const express = require('express');
const http = require('http');
const { Server } = require('socket.io');

const app = express();
const server = http.createServer(app);
const io = new Server(server, { maxHttpBufferSize: 1e5 });

const TTL_MS = 300000;
const MAX_NAME = 30;
const MAX_TITLE = 40;
const MAX_BODY = 500;
const MAX_POSTS_PER_THREAD = 500;
const MAX_THREADS_PER_BOARD = 30;
const COOLDOWN_MS = 1000;
const THREAD_COOLDOWN_MS = 5000;
const TRUSTED_PROXY_HOPS = Math.max(1, Number(process.env.TRUSTED_PROXY_HOPS) || 3);
const MAX_CONNECTIONS = 300;
const MAX_CONN_PER_IP = 20;
const CONN_ATTEMPTS_PER_MIN = 600;
const CONN_ATTEMPTS_PER_MIN_PER_IP = 60;
const EVENTS_PER_10S = 40;
const IP_POSTS_PER_MIN = 90;
const IP_THREADS_PER_MIN = 20;
const IP_JOINS_PER_MIN = 120;
const IP_SEARCHES_PER_MIN = 30;
const GLOBAL_SEARCHES_PER_MIN = 200;
const MAX_QUERY = 40;
const MAX_RESULTS = 30;
const DEFAULT_NAME = "名無しさん＠５分で消滅";
const ADMIN_NAME = "管理人 ★";

const BOARDS = [
    { id: 'nandemo', name: 'なんでも' },
    { id: 'game', name: 'ゲーム' },
    { id: 'anime', name: 'アニメ' },
    { id: 'zatsu', name: '雑談' },
    { id: 'kuro', name: '黒歴史' }
];
const BOARD_IDS = new Set(BOARDS.map(b => b.id));

let threads = [];
let nextThreadId = 1;

function createLimiter(windowMs, max) {
    const hits = new Map();
    return {
        take(key, now) {
            const list = (hits.get(key) || []).filter(t => now - t < windowMs);
            if (list.length >= max) {
                hits.set(key, list);
                return false;
            }
            list.push(now);
            hits.set(key, list);
            return true;
        },
        purge(now) {
            hits.forEach((list, key) => {
                const alive = list.filter(t => now - t < windowMs);
                if (alive.length) {
                    hits.set(key, alive);
                } else {
                    hits.delete(key);
                }
            });
        }
    };
}

const globalAttempts = createLimiter(60000, CONN_ATTEMPTS_PER_MIN);
const ipAttempts = createLimiter(60000, CONN_ATTEMPTS_PER_MIN_PER_IP);
const ipPosts = createLimiter(60000, IP_POSTS_PER_MIN);
const ipThreads = createLimiter(60000, IP_THREADS_PER_MIN);
const ipJoins = createLimiter(60000, IP_JOINS_PER_MIN);
const ipSearches = createLimiter(60000, IP_SEARCHES_PER_MIN);
const globalSearches = createLimiter(60000, GLOBAL_SEARCHES_PER_MIN);
const allLimiters = [globalAttempts, ipAttempts, ipPosts, ipThreads, ipJoins, ipSearches, globalSearches];
const connPerIp = new Map();
let connectionCount = 0;

function clientIp(socket) {
    const header = socket.handshake.headers['x-forwarded-for'];
    if (typeof header === 'string' && header.length > 0 && header.length < 1000) {
        const chain = header.split(',').map(s => s.trim()).filter(Boolean);
        if (chain.length > 0) {
            return chain[Math.max(0, chain.length - TRUSTED_PROXY_HOPS)].slice(0, 64);
        }
    }
    return String(socket.handshake.address || 'unknown').slice(0, 64);
}

const HTML = String.raw`<!DOCTYPE html>
<html lang="ja">
<head>
    <meta charset="UTF-8">
    <meta name="viewport" content="width=device-width, initial-scale=1.0">
    <title>5分限定・暴言強制キモ告白変換掲示板</title>
    <style>
        body { background-color: #efefef; color: #000; font-family: "MS PGothic", sans-serif; padding: 10px; font-size: 16px; margin: 0; }
        .wrap { max-width: 600px; margin: 0 auto; padding: 10px; }
        h1 { color: #ff0000; font-size: 22px; text-align: center; margin: 10px 0; }
        h2 { font-size: 17px; margin: 8px 0; word-break: break-all; }
        .desc { font-size: 12px; text-align: center; color: #555; margin-bottom: 20px; }
        .rules { background: #fffbe6; border: 1px solid #e0c97a; padding: 8px 12px; border-radius: 5px; font-size: 13px; margin-bottom: 15px; }
        .rules ul { margin: 6px 0 0; padding-left: 18px; }
        .toast { display: none; position: fixed; left: 10px; right: 10px; bottom: 10px; background: #333; color: #fff; padding: 10px; border-radius: 5px; font-size: 14px; text-align: center; z-index: 10; }
        .form-box { background: #fbfbfb; border: 1px solid #aaa; padding: 10px; margin-bottom: 15px; border-radius: 5px; }
        .form-group { margin-bottom: 8px; }
        input[type="text"], textarea { width: 100%; box-sizing: border-box; padding: 6px; border: 1px solid #ccc; font-size: 16px; }
        textarea { height: 80px; }
        .submit-btn { background-color: #e1e1e1; border: 1px solid #777; padding: 8px 18px; cursor: pointer; font-size: 15px; }
        .panel { background: #fff; border: 1px solid #ccc; padding: 5px 15px; min-height: 40px; border-radius: 5px; margin-bottom: 15px; }
        .back { display: inline-block; margin: 4px 0 8px; font-size: 14px; }
        .board-link, .thread-link { display: flex; justify-content: space-between; align-items: center; gap: 8px; padding: 12px 4px; border-bottom: 1px dashed #ccc; text-decoration: none; color: #0000ee; }
        .board-name { font-weight: bold; }
        .board-count, .thread-meta { color: #555; font-size: 13px; white-space: nowrap; }
        .thread-title { flex: 1; word-break: break-all; }
        .thread-timer { color: #cc0000; font-size: 11px; white-space: nowrap; }
        .empty { color: #777; padding: 12px 4px; font-size: 14px; }
        .notice { background: #ffecec; border: 1px solid #e0a0a0; padding: 8px 12px; border-radius: 5px; margin-bottom: 10px; font-size: 14px; }
        .post { margin: 15px 0; border-bottom: 1px dashed #ccc; padding-bottom: 10px; position: relative; }
        .post-header { font-size: 13px; color: #222; padding-right: 70px; }
        .post-num { color: #0000ff; font-weight: bold; margin-right: 5px; cursor: pointer; }
        .post-name { color: #228b22; font-weight: bold; margin-right: 5px; }
        .post-body { font-size: 15px; white-space: pre-wrap; word-break: break-all; padding-left: 10px; margin-top: 5px; }
        .timer-badge { position: absolute; top: 0; right: 0; background: #ff0000; color: #fff; font-size: 10px; padding: 2px 6px; border-radius: 10px; }
        .converted-mark { color: #ff007f; font-size: 11px; font-weight: bold; margin-left: 5px; }
        .anchor { color: #0000ee; text-decoration: underline; cursor: pointer; }
        .anchor-preview { margin: 6px 0 0 10px; padding: 6px 8px; border: 1px solid #aab; background: #f4f4ff; font-size: 13px; word-break: break-all; white-space: pre-wrap; }
        .search-row { display: flex; gap: 6px; }
        .search-row input[type="text"] { flex: 1; width: auto; }
        .result-link { display: block; padding: 10px 4px; border-bottom: 1px dashed #ccc; text-decoration: none; color: #0000ee; }
        .result-snippet { color: #444; font-size: 13px; margin-top: 2px; word-break: break-all; }
    </style>
    <script src="/socket.io/socket.io.js"></script>
</head>
<body>
<div class="wrap">

    <h1>■ 5分限定・暴言強制浄化掲示板 ■</h1>
    <div class="desc">リアルタイム同期サーバー版。5分で本当に消えます。<br>俺は警察のお縄になりたくないので仕方なく告白に変えてます。<br>アングラのネット民！すまねぇな！</div>

    <div class="rules">
        <b>__ADMIN__ からのルール</b>
        <ul>
            <li>「殺す」「死ね」などの暴言は「究極の愛」に強制変換されます（名前やスレ題名も）</li>
            <li>アニメやゲームのセリフも容赦なく変換されます</li>
            <li>書き込みは5分（300秒）で消滅します。スレは最後の書き込みが消えると一緒に消えます</li>
            <li>名前は__MAX_NAME__字まで（記号は使えません）、スレ題名は__MAX_TITLE__字まで、本文は__MAX_BODY__字まで</li>
            <li>連投は__POST_CD__秒に1回、スレ立ては__THREAD_CD__秒に1回まで</li>
            <li>サーバーの再起動などで、5分たつ前でも全部消えることがあります</li>
            <li>「&gt;&gt;1」と書くと返信になります。レス番号をタップすると、入力欄に入ります</li>
            <li>検索できるのは、まだ消えてないスレ題名と書き込みだけです</li>
        </ul>
    </div>

    <div id="toast" class="toast"></div>

    <div id="nameBox" class="form-box" style="display: none;">
        <label>名前:</label><input type="text" id="nameInput" maxlength="__MAX_NAME__" value="名無しさん＠５分で消滅">
    </div>

    <div id="searchBox" class="form-box">
        <form id="searchForm" class="search-row">
            <input type="text" id="searchInput" maxlength="__MAX_QUERY__" placeholder="スレ題名・書き込みを検索">
            <button type="submit" class="submit-btn">検索</button>
        </form>
        <div class="panel" id="searchResults" style="display: none; margin: 10px 0 0;"></div>
    </div>

    <div id="boardsView">
        <h2>板一覧</h2>
        <div class="panel" id="boardList"></div>
    </div>

    <div id="threadsView" style="display: none;">
        <a class="back" href="#/">← 板一覧</a>
        <h2 id="boardTitle"></h2>
        <div class="form-box">
            <form id="threadForm">
                <div class="form-group">
                    <label>スレ題名:</label><input type="text" id="titleInput" maxlength="__MAX_TITLE__" required>
                </div>
                <div class="form-group">
                    <label>最初の書き込み:</label>
                    <textarea id="threadBodyInput" maxlength="__MAX_BODY__" placeholder="ここに暴言を吐くと、どうなるかな？ウヒヒ。" required></textarea>
                </div>
                <button type="submit" class="submit-btn">スレを立てる</button>
            </form>
        </div>
        <div class="panel" id="threadList"></div>
    </div>

    <div id="threadView" style="display: none;">
        <a class="back" id="backToBoard" href="#/">← 板に戻る</a>
        <h2 id="threadTitle"></h2>
        <div class="notice" id="threadNotice" style="display: none;"></div>
        <div class="panel" id="postList"></div>
        <div class="form-box">
            <form id="postForm">
                <div class="form-group">
                    <label>内容:</label>
                    <textarea id="bodyInput" maxlength="__MAX_BODY__" placeholder="ここに暴言を吐くと、どうなるかな？ウヒヒ。" required></textarea>
                </div>
                <button type="submit" class="submit-btn">書き込む</button>
            </form>
        </div>
    </div>

</div>

    <script>
        var socket = io();
        var offset = 0;
        var boards = [];
        var counts = {};
        var currentBoard = null;
        var currentThread = null;
        var postNodes = {};
        var postData = {};
        var listItems = [];
        var toastTimer = null;

        function el(id) {
            return document.getElementById(id);
        }

        function make(tag, className, text) {
            var e = document.createElement(tag);
            if (className) e.className = className;
            if (text !== undefined) e.textContent = text;
            return e;
        }

        function clear(node) {
            while (node.firstChild) node.removeChild(node.firstChild);
        }

        function syncTime(serverTime) {
            offset = serverTime - performance.now();
        }

        function secondsLeft(expireAt) {
            return Math.max(0, Math.round((expireAt - (performance.now() + offset)) / 1000));
        }

        function findBoard(id) {
            for (var i = 0; i < boards.length; i++) {
                if (boards[i].id === id) return boards[i];
            }
            return null;
        }

        function showToast(text) {
            var t = el('toast');
            t.textContent = text;
            t.style.display = 'block';
            clearTimeout(toastTimer);
            toastTimer = setTimeout(function () { t.style.display = 'none'; }, 3000);
        }

        function showView(name) {
            el('boardsView').style.display = name === 'boards' ? 'block' : 'none';
            el('threadsView').style.display = name === 'threads' ? 'block' : 'none';
            el('threadView').style.display = name === 'thread' ? 'block' : 'none';
            el('nameBox').style.display = name === 'boards' ? 'none' : 'block';
            el('searchBox').style.display = name === 'thread' ? 'none' : 'block';
        }

        function renderBoards() {
            var box = el('boardList');
            clear(box);
            boards.forEach(function (b) {
                var a = make('a', 'board-link');
                a.href = '#/b/' + b.id;
                a.appendChild(make('span', 'board-name', b.name));
                a.appendChild(make('span', 'board-count', (counts[b.id] || 0) + 'スレ'));
                box.appendChild(a);
            });
        }

        function renderThreads(list) {
            var box = el('threadList');
            clear(box);
            listItems = [];
            if (!list.length) {
                box.appendChild(make('div', 'empty', 'スレがありません。最初のスレを立ててみよう'));
                return;
            }
            list.forEach(function (t, i) {
                var a = make('a', 'thread-link');
                a.href = '#/t/' + t.id;
                a.appendChild(make('span', 'thread-title', (i + 1) + ': ' + t.title));
                a.appendChild(make('span', 'thread-meta', '(' + t.count + ')'));
                var timer = make('span', 'thread-timer');
                a.appendChild(timer);
                box.appendChild(a);
                listItems.push({ timer: timer, expireAt: t.expireAt });
            });
            updateBadges();
        }

        function toHalfNumber(text) {
            return Number(text.replace(/[０-９]/g, function (c) {
                return String.fromCharCode(c.charCodeAt(0) - 65248);
            }));
        }

        function replyTo(id) {
            var box = el('bodyInput');
            box.value = box.value + '>>' + id + '\n';
            if (box.focus) box.focus();
        }

        function toggleAnchor(span, num, host) {
            if (span.previewNode) {
                host.removeChild(span.previewNode);
                span.previewNode = null;
                return;
            }
            var target = postData[num];
            var box = make('div', 'anchor-preview');
            if (target) {
                box.appendChild(make('div', 'post-header', target.id + ' ' + target.name + ' ' + target.date));
                box.appendChild(make('div', 'post-body', target.body));
            } else {
                box.appendChild(make('div', '', '>>' + num + ' は消滅したか、存在しません'));
            }
            host.appendChild(box);
            span.previewNode = box;
        }

        function fillBody(container, text, host) {
            text.split(/([>＞]{2}[0-9０-９]{1,4})/).forEach(function (part, i) {
                if (!part) return;
                if (i % 2 === 1) {
                    var num = toHalfNumber(part.slice(2));
                    var span = make('span', 'anchor', part);
                    span.addEventListener('click', function () { toggleAnchor(span, num, host); });
                    container.appendChild(span);
                } else {
                    container.appendChild(make('span', '', part));
                }
            });
        }

        function addPostNode(p) {
            if (postNodes[p.id]) return;
            var node = make('div', 'post');
            var head = make('div', 'post-header');
            var numSpan = make('span', 'post-num', String(p.id));
            numSpan.addEventListener('click', function () { replyTo(p.id); });
            head.appendChild(numSpan);
            head.appendChild(make('span', 'post-name', p.name));
            if (p.converted) head.appendChild(make('span', 'converted-mark', '【★強制浄化完了★】'));
            head.appendChild(make('span', 'post-date', p.date + ' '));
            head.appendChild(make('span', 'post-id', p.uid));
            node.appendChild(head);
            var body = make('div', 'post-body');
            fillBody(body, p.body, node);
            node.appendChild(body);
            var badge = make('span', 'timer-badge', '残り ' + secondsLeft(p.expireAt) + '秒');
            node.appendChild(badge);
            el('postList').appendChild(node);
            postNodes[p.id] = { node: node, badge: badge, expireAt: p.expireAt };
            postData[p.id] = p;
        }

        function removePostNode(id) {
            var p = postNodes[id];
            if (!p) return;
            if (p.node.parentNode) p.node.parentNode.removeChild(p.node);
            delete postNodes[id];
            delete postData[id];
        }

        function updateBadges() {
            listItems.forEach(function (it) {
                it.timer.textContent = 'あと' + secondsLeft(it.expireAt) + '秒';
            });
            Object.keys(postNodes).forEach(function (id) {
                var p = postNodes[id];
                var left = secondsLeft(p.expireAt);
                if (left <= 0) {
                    removePostNode(id);
                } else {
                    p.badge.textContent = '残り ' + left + '秒';
                }
            });
        }

        function showGone() {
            var n = el('threadNotice');
            clear(n);
            n.appendChild(make('span', '', 'このスレは消滅しました。'));
            var a = make('a', '', '板に戻る');
            a.href = currentBoard ? '#/b/' + currentBoard : '#/';
            n.appendChild(a);
            n.style.display = 'block';
            el('threadTitle').textContent = '';
            el('postForm').style.display = 'none';
        }

        function openHome() {
            currentBoard = null;
            currentThread = null;
            socket.emit('leave');
            showView('boards');
            renderBoards();
        }

        function openBoard(id) {
            currentBoard = id;
            currentThread = null;
            el('boardTitle').textContent = findBoard(id).name;
            clear(el('threadList'));
            listItems = [];
            showView('threads');
            socket.emit('joinBoard', id);
        }

        function openThread(id) {
            currentThread = null;
            postNodes = {};
            postData = {};
            clear(el('postList'));
            el('threadTitle').textContent = '読み込み中...';
            el('threadNotice').style.display = 'none';
            el('postForm').style.display = 'block';
            el('backToBoard').href = currentBoard ? '#/b/' + currentBoard : '#/';
            showView('thread');
            socket.emit('joinThread', id);
        }

        function route() {
            hideResults();
            var parts = (location.hash || '#/').split('/');
            var kind = parts[1];
            var id = parts[2];
            if (kind === 'b' && findBoard(id)) {
                openBoard(id);
            } else if (kind === 't' && id) {
                openThread(Number(id));
            } else {
                openHome();
            }
        }

        socket.on('init', function (d) {
            syncTime(d.serverTime);
            boards = d.boards;
            counts = d.counts;
            renderBoards();
            route();
        });

        socket.on('counts', function (c) {
            counts = c;
            renderBoards();
        });

        socket.on('threadList', function (d) {
            syncTime(d.serverTime);
            if (d.boardId !== currentBoard) return;
            renderThreads(d.threads);
        });

        socket.on('threadData', function (d) {
            syncTime(d.serverTime);
            currentThread = d.thread;
            currentBoard = d.thread.boardId;
            el('threadTitle').textContent = d.thread.title;
            el('backToBoard').href = '#/b/' + d.thread.boardId;
            clear(el('postList'));
            postNodes = {};
            postData = {};
            d.posts.forEach(function (p) { addPostNode(p); });
        });

        socket.on('newPost', function (d) {
            if (currentThread && d.threadId === currentThread.id) addPostNode(d.post);
        });

        socket.on('deletePost', function (d) {
            if (currentThread && d.threadId === currentThread.id) removePostNode(d.postId);
        });

        socket.on('threadGone', function (d) {
            if (currentThread && d.threadId === currentThread.id) showGone();
        });

        socket.on('threadMissing', function () {
            showGone();
        });

        el('threadForm').addEventListener('submit', function (e) {
         e.preventDefault();
            if (!currentBoard) return;
            socket.emit('createThread', {
                boardId: currentBoard,
                title: el('titleInput').value,
                name: el('nameInput').value,
                body: el('threadBodyInput').value
            }, function (res) {
                if (res && res.ok) {
                    el('titleInput').value = '';
                    el('threadBodyInput').value = '';
                    location.hash = '#/t/' + res.threadId;
                } else {
                    showToast(res && res.error ? res.error : '失敗しました');
                }
            });
        });

        el('postForm').addEventListener('submit', function (e) {
            e.preventDefault();
            if (!currentThread) return;
            socket.emit('submitPost', {
                threadId: currentThread.id,
                name: el('nameInput').value,
                body: el('bodyInput').value
            }, function (res) {
                if (res && res.ok) {
                    el('bodyInput').value = '';
                } else {
                    showToast(res && res.error ? res.error : '失敗しました');
                }
            });
        });

        function boardNameOf(id) {
            var b = findBoard(id);
            return b ? b.name : id;
        }

        function hideResults() {
            var box = el('searchResults');
            clear(box);
            box.style.display = 'none';
        }

        function renderResults(list, q) {
            var box = el('searchResults');
            clear(box);
            box.appendChild(make('div', 'empty', '「' + q.trim() + '」の検索結果：' + list.length + 'スレ'));
            list.forEach(function (r) {
                var a = make('a', 'result-link');
                a.href = '#/t/' + r.threadId;
                a.appendChild(make('div', 'thread-title', '[' + boardNameOf(r.boardId) + '] ' + r.title));
                if (r.postId !== null) {
                    var more = r.count > 1 ? '（ほか' + (r.count - 1) + '件）' : '';
                    a.appendChild(make('div', 'result-snippet', '>>' + r.postId + ' ' + r.snippet + more));
                }
                box.appendChild(a);
            });
            box.style.display = 'block';
        }

        el('searchForm').addEventListener('submit', function (e) {
            e.preventDefault();
            var q = el('searchInput').value;
            if (!q.trim()) return;
            socket.emit('search', { q: q, boardId: currentBoard }, function (res) {
                if (res && res.ok) {
                    renderResults(res.results, q);
                } else {
                    showToast(res && res.error ? res.error : '検索に失敗しました');
                }
            });
        });

        socket.on('notice', function (text) {
            showToast(text);
        });

        socket.on('connect_error', function () {
            showToast('接続できません。アクセスが多すぎるようです。少し待ってからもう一度');
        });

        socket.on('disconnect', function (reason) {
            if (reason === 'io server disconnect') {
                showToast('アクセスが多すぎて切断されました。少し待ってから再読み込みしてください');
            }
        });

        window.addEventListener('hashchange', route);
        setInterval(updateBadges, 1000);
    </script>
</body>
</html>
`;

const PAGE = HTML
    .split('__ADMIN__').join(ADMIN_NAME)
    .split('__MAX_NAME__').join(String(MAX_NAME))
    .split('__MAX_TITLE__').join(String(MAX_TITLE))
    .split('__MAX_BODY__').join(String(MAX_BODY))
    .split('__MAX_QUERY__').join(String(MAX_QUERY))
    .split('__POST_CD__').join(String(COOLDOWN_MS / 1000))
    .split('__THREAD_CD__').join(String(THREAD_COOLDOWN_MS / 1000));

app.get('/', (req, res) => {
    res.type('html').send(PAGE);
});

function sanitizeName(raw) {
    const trimmed = raw.trim();
    if (trimmed === DEFAULT_NAME) return DEFAULT_NAME;
    const cleaned = trimmed
        .replace(/[^\p{L}\p{N}\s]/gu, '')
        .replace(/\s+/g, ' ')
        .trim()
        .slice(0, MAX_NAME);
    if (!cleaned || cleaned.replace(/\s/g, '').includes('管理人')) return DEFAULT_NAME;
    return cleaned;
}

function toHiragana(str) {
    return str.replace(/[ァ-ヶ]/g, c => String.fromCharCode(c.charCodeAt(0) - 0x60));
}

function prepareWords(words) {
    return words.map(w => toHiragana(w.normalize('NFKC').toLowerCase()));
}

const RULES = [
    {
        target: 'letters',
        reply: "おいらと交際を前提に結婚してください(逆でうんち)",
        words: prepareWords(['殺す', 'ころす', '殺せ', 'ころせ'])
    },
    {
        target: 'letters',
        reply: "愛してるぜ…",
        words: prepareWords(['氏ね', 'くたばれ', '消えろ', 'きえろ']),
        patterns: [
            /死[^\p{L}\p{N}]*ね(?!ない|なかっ|る)/u,
            /(^|[^ぁ-ゖ])し[^\p{L}\p{N}]*ね/u,
            /シ[^\p{L}\p{N}]*ネ(?![マコ])/u,
            /(おまえ|てめえ|てめぇ|きさま|あんた)し[^\p{L}\p{N}]*ね/u
        ]
    },
    {
        target: 'compact',
        reply: "（おいらのハートがハッキングされちゃったみたいだ…キュン♡）",
        words: prepareWords(['.exe', 'javascript:'])
    }
];

function findReply(text) {
    const normalized = text.normalize('NFKC').toLowerCase();
    const forms = {
        raw: normalized,
        compact: normalized.replace(/\s+/g, ''),
        letters: toHiragana(normalized).replace(/[^\p{L}\p{N}]/gu, '')
    };
    for (const rule of RULES) {
        const wordHit = rule.words.some(w => forms[rule.target].includes(w));
        const patternHit = (rule.patterns || []).some(p => p.test(forms.raw));
        if (wordHit || patternHit) return rule.reply;
    }
    return null;
}

const searchKeys = new WeakMap();

function normalizeForSearch(s) {
    return toHiragana(s.normalize('NFKC').toLowerCase());
}

function searchKey(obj, text) {
    let key = searchKeys.get(obj);
    if (key === undefined) {
        key = normalizeForSearch(text);
        searchKeys.set(obj, key);
    }
    return key;
}

function makeSnippet(body, q) {
    const key = normalizeForSearch(body);
    const idx = key.length === body.length ? Math.max(0, key.indexOf(q)) : 0;
    const start = Math.max(0, idx - 10);
    const piece = body.slice(start, start + 40).replace(/\s+/g, ' ');
    return (start > 0 ? '…' : '') + piece + (start + 40 < body.length ? '…' : '');
}

function searchThreads(q, boardId, now) {
    const results = [];
    const list = threads
        .filter(t => !boardId || t.boardId === boardId)
        .sort((a, b) => b.lastPostAt - a.lastPostAt);
    for (const t of list) {
        const posts = livePosts(t, now);
        if (posts.length === 0) continue;
        const titleHit = searchKey(t, t.title).includes(q);
        let count = 0;
        let first = null;
        for (const p of posts) {
            if (searchKey(p, p.body).includes(q)) {
                count++;
                if (!first) first = p;
            }
        }
        if (!titleHit && count === 0) continue;
        results.push({
            threadId: t.id,
            boardId: t.boardId,
            title: t.title,
            postId: first ? first.id : null,
            snippet: first ? makeSnippet(first.body, q) : '',
            count: count
        });
        if (results.length >= MAX_RESULTS) break;
    }
    return results;
}

function formatDate(ms) {
    return new Date(ms).toLocaleString('sv-SE', { timeZone: 'Asia/Tokyo' }).replace(/-/g, '/');
}

function findThread(id) {
    return threads.find(t => t.id === id);
}

function livePosts(t, now) {
    return t.posts.filter(p => p.expireAt > now);
}

function boardThreads(boardId) {
    const now = Date.now();
    return threads
        .filter(t => t.boardId === boardId && livePosts(t, now).length > 0)
        .sort((a, b) => b.lastPostAt - a.lastPostAt);
}

function threadSummary(t) {
    const posts = livePosts(t, Date.now());
    return {
        id: t.id,
        title: t.title,
        count: posts.length,
        expireAt: posts[posts.length - 1].expireAt
    };
}

function countsOf() {
    const now = Date.now();
    const c = {};
    BOARDS.forEach(b => { c[b.id] = 0; });
    threads.forEach(t => {
        if (livePosts(t, now).length > 0) c[t.boardId]++;
    });
    return c;
}

function emitBoard(boardId) {
    io.to('board:' + boardId).emit('threadList', {
        boardId: boardId,
        threads: boardThreads(boardId).map(threadSummary),
        serverTime: Date.now()
    });
}

function emitCounts() {
    io.emit('counts', countsOf());
}

function removeThread(t) {
    threads = threads.filter(x => x !== t);
    io.to('thread:' + t.id).emit('threadGone', { threadId: t.id });
}

function trimBoard(boardId) {
    const list = boardThreads(boardId);
    while (list.length > MAX_THREADS_PER_BOARD) {
        removeThread(list.pop());
    }
}

function makePost(thread, socket, rawName, rawBody) {
    const cleanName = sanitizeName(rawName);
    const name = findReply(cleanName) ? DEFAULT_NAME : cleanName;
    const hit = findReply(rawBody);
    const now = Date.now();
    thread.postCount++;
    const post = {
        id: thread.postCount,
        name: name,
        body: hit || rawBody,
        date: formatDate(now),
        uid: 'ID:' + socket.id.substring(0, 8).toUpperCase(),
        converted: !!hit,
        expireAt: now + TTL_MS
    };
    thread.posts.push(post);
    thread.lastPostAt = now;
    return post;
}

function reply(ack, result) {
    if (typeof ack === 'function') ack(result);
}

io.use((socket, next) => {
    const now = Date.now();
    const ip = clientIp(socket);
    socket.data.ip = ip;
    if (!globalAttempts.take('all', now) || !ipAttempts.take(ip, now)) {
        return next(new Error('too many attempts'));
    }
    if (connectionCount >= MAX_CONNECTIONS || (connPerIp.get(ip) || 0) >= MAX_CONN_PER_IP) {
        return next(new Error('server busy'));
    }
    next();
});

function joinAllowed(socket) {
    if (ipJoins.take(socket.data.ip, Date.now())) return true;
    socket.emit('notice', 'アクセスが多すぎます。少し待ってください');
    return false;
}

io.on('connection', (socket) => {
    const ip = socket.data.ip;
    connectionCount++;
    connPerIp.set(ip, (connPerIp.get(ip) || 0) + 1);
    socket.on('disconnect', () => {
        connectionCount--;
        const n = (connPerIp.get(ip) || 1) - 1;
        if (n > 0) {
            connPerIp.set(ip, n);
        } else {
            connPerIp.delete(ip);
        }
    });

    let recentEvents = [];
    socket.use((packet, next) => {
        const now = Date.now();
        recentEvents = recentEvents.filter(t => now - t < 10000);
        recentEvents.push(now);
        if (recentEvents.length > EVENTS_PER_10S) {
            socket.disconnect(true);
            return;
        }
        next();
    });

    socket.emit('init', { boards: BOARDS, counts: countsOf(), serverTime: Date.now() });

    let lastPostAt = 0;
    let lastThreadAt = 0;

    function leaveRooms() {
        Array.from(socket.rooms).forEach(r => {
            if (r !== socket.id) socket.leave(r);
        });
    }

    socket.on('leave', () => {
        leaveRooms();
    });

    socket.on('joinBoard', (boardId) => {
        if (!joinAllowed(socket)) return;
        if (typeof boardId !== 'string' || !BOARD_IDS.has(boardId)) return;
        leaveRooms();
        socket.join('board:' + boardId);
        socket.emit('threadList', {
            boardId: boardId,
            threads: boardThreads(boardId).map(threadSummary),
            serverTime: Date.now()
        });
    });

    socket.on('joinThread', (threadId) => {
        if (!joinAllowed(socket)) return;
        const thread = Number.isInteger(threadId) ? findThread(threadId) : null;
        const posts = thread ? livePosts(thread, Date.now()) : [];
        if (!thread || posts.length === 0) {
            socket.emit('threadMissing');
            return;
        }
        leaveRooms();
        socket.join('thread:' + thread.id);
        socket.emit('threadData', {
            thread: { id: thread.id, boardId: thread.boardId, title: thread.title },
            posts: posts,
            serverTime: Date.now()
        });
    });

    socket.on('search', (data, ack) => {
        if (!data || typeof data.q !== 'string') {
            return reply(ack, { ok: false, error: '検索ワードが正しくありません' });
        }
        const now = Date.now();
        if (!ipSearches.take(ip, now) || !globalSearches.take('all', now)) {
            return reply(ack, { ok: false, error: '検索が多すぎます。少し待ってください' });
        }
        const q = normalizeForSearch(data.q.trim().slice(0, MAX_QUERY));
        if (!q) {
            return reply(ack, { ok: false, error: '検索ワードを入力してください' });
        }
        const boardId = typeof data.boardId === 'string' && BOARD_IDS.has(data.boardId) ? data.boardId : null;
        reply(ack, { ok: true, results: searchThreads(q, boardId, now) });
    });

    socket.on('createThread', (data, ack) => {
        if (!data || typeof data.boardId !== 'string' || typeof data.title !== 'string' ||
            typeof data.name !== 'string' || typeof data.body !== 'string') {
            return reply(ack, { ok: false, error: '入力が正しくありません' });
        }
        if (!BOARD_IDS.has(data.boardId)) {
            return reply(ack, { ok: false, error: 'その板は存在しません' });
        }
        const now = Date.now();
        if (now - lastThreadAt < THREAD_COOLDOWN_MS) {
            return reply(ack, { ok: false, error: 'スレ立ては' + (THREAD_COOLDOWN_MS / 1000) + '秒に1回までです' });
        }
        const rawTitle = data.title.trim().slice(0, MAX_TITLE);
        const rawBody = data.body.trim().slice(0, MAX_BODY);
        if (!rawTitle || !rawBody) {
            return reply(ack, { ok: false, error: '題名と本文を入力してください' });
        }
        if (!ipThreads.take(ip, now)) {
            return reply(ack, { ok: false, error: 'このIPからのスレ立てが多すぎます。少し待ってください' });
        }
        lastThreadAt = now;

        const thread = {
            id: nextThreadId++,
            boardId: data.boardId,
            title: findReply(rawTitle) || rawTitle,
            posts: [],
            postCount: 0,
            lastPostAt: now
        };
        threads.push(thread);
        makePost(thread, socket, data.name, rawBody);
        trimBoard(thread.boardId);
        emitBoard(thread.boardId);
        emitCounts();
        reply(ack, { ok: true, threadId: thread.id });
    });

    socket.on('submitPost', (data, ack) => {
        if (!data || typeof data.name !== 'string' || typeof data.body !== 'string') {
            return reply(ack, { ok: false, error: '入力が正しくありません' });
        }
        const thread = findThread(data.threadId);
        if (!thread) {
            return reply(ack, { ok: false, error: 'このスレは消滅しました' });
        }
        const now = Date.now();
        if (now - lastPostAt < COOLDOWN_MS) {
            return reply(ack, { ok: false, error: '連投は' + (COOLDOWN_MS / 1000) + '秒に1回までです' });
        }
        const rawBody = data.body.trim().slice(0, MAX_BODY);
        if (!rawBody) {
            return reply(ack, { ok: false, error: '本文を入力してください' });
        }
        if (thread.posts.length >= MAX_POSTS_PER_THREAD) {
            return reply(ack, { ok: false, error: 'このスレは満杯です。次スレ立ててね（古い書き込みが消えるまで待ってもOK）' });
        }
        if (!ipPosts.take(ip, now)) {
            return reply(ack, { ok: false, error: 'このIPからの書き込みが多すぎます。少し待ってください' });
        }
        lastPostAt = now;

        const post = makePost(thread, socket, data.name, rawBody);
        io.to('thread:' + thread.id).emit('newPost', { threadId: thread.id, post: post });
        emitBoard(thread.boardId);
        reply(ack, { ok: true });
    });
});

let sweepTicks = 0;

setInterval(() => {
    const now = Date.now();
    const dirtyBoards = new Set();
    sweepTicks++;
    if (sweepTicks % 60 === 0) allLimiters.forEach(l => l.purge(now));
    let countsChanged = false;

    threads = threads.filter(t => {
        const alive = [];
        t.posts.forEach(p => {
            if (p.expireAt <= now) {
                io.to('thread:' + t.id).emit('deletePost', { threadId: t.id, postId: p.id });
            } else {
                alive.push(p);
            }
        });
        if (alive.length !== t.posts.length) dirtyBoards.add(t.boardId);
        t.posts = alive;
        if (alive.length === 0) {
            io.to('thread:' + t.id).emit('threadGone', { threadId: t.id });
            countsChanged = true;
            return false;
        }
        return true;
    });

    dirtyBoards.forEach(emitBoard);
    if (countsChanged) emitCounts();
}, 1000);

const PORT = process.env.PORT || 3000;
server.listen(PORT, () => {
    console.log('Server is running on port ' + PORT);
}); 
