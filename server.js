const express = require('express');
const http = require('http');
const { Server } = require('socket.io');
const crypto = require('crypto');
const { findReply, toHiragana } = require('./filter');

let sharp = null;
try {
    sharp = require('sharp');
    sharp.cache({ memory: 50, files: 0, items: 20 });
    sharp.concurrency(1);
} catch (e) {
    sharp = null;
}

const app = express();
const server = http.createServer(app);
server.requestTimeout = 60000;
server.headersTimeout = 15000;
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
const ADMIN_PASSWORD = String(process.env.ADMIN_PASSWORD || '').normalize('NFKC').trim();
const ADMIN_ENABLED = ADMIN_PASSWORD.length >= 8;
const MAX_NAME_INPUT = 80;
const ADMIN_FAILS_PER_10MIN = 8;
const REPORT_HIDE_COUNT = 3;
const IP_REPORTS_PER_MIN = 10;
const MAX_REPORT_ENTRIES = 1000;
const HIDDEN_BODY = '【通報が集まったので非表示にしました】';
const IMAGES_REQUESTED = ['off', 'admin', 'all'].includes(process.env.IMAGES_MODE) ? process.env.IMAGES_MODE : 'admin';
const IMAGES_MODE = sharp ? IMAGES_REQUESTED : 'off';
const MAX_UPLOAD_BYTES = 6 * 1024 * 1024;
const MAX_IMAGE_SIDE = 1280;
const MAX_INPUT_PIXELS = 40000000;
const MAX_IMAGE_TOTAL_BYTES = 60 * 1024 * 1024;
const ORPHAN_IMAGE_MS = 60000;
const TOKEN_TTL_MS = 60000;
const MAX_PENDING_TOKENS = 3;
const IP_UPLOADS_PER_MIN = 6;
const IP_IMAGE_VIEWS_PER_MIN = 600;
const MAX_CONCURRENT_UPLOADS = 1;
const HTTP_PER_SEC = 50;
const HTTP_PER_MIN = 500;
const BAN_STRIKES = 6;
const BAN_STRIKE_WINDOW_MS = 300000;
const BAN_BASE_MS = 300000;
const BAN_MAX_MS = 21600000;
const BAN_MAX_ENTRIES = 20000;
const MAX_LIMITER_KEYS = 20000;
const ADMIN_FAILS_GLOBAL_PER_10MIN = 60;
const IP_ALLOWLIST = new Set(String(process.env.IP_ALLOWLIST || '').split(',').map(s => normalizeIp(s.trim())).filter(Boolean));
const DEBUG_IP = process.env.DEBUG_IP === '1';
const IMAGE_RULES = {
    off: '',
    admin: '<li>画像を貼れるのは管理人だけです</li>',
    all: '<li>画像（JPEG・PNG・GIF・WebP）を貼れます。最初はぼかして表示され、タップで見られます。サーバーで変換するのでGIFは止まった絵になります。通報されると画像だけすぐ消えます</li>'
};

const BOARDS = [
    { id: 'nandemo', name: 'なんでも' },
    { id: 'game', name: 'ゲーム' },
    { id: 'anime', name: 'アニメ' },
    { id: 'zatsu', name: '雑談' },
    { id: 'kuro', name: '黒歴史' },
    { id: 'music', name: '音楽' },
    { id: 'sports', name: 'スポーツ' },
    { id: 'eiga', name: '映画・ドラマ' },
    { id: 'renai', name: '恋愛・告白' },
    { id: 'shigoto', name: '仕事・学校' },
    { id: 'gohan', name: '食べ物' },
    { id: 'sousaku', name: '創作・AA' },
    { id: 'unchi', name: 'うんち' }
];
const BOARD_IDS = new Set(BOARDS.map(b => b.id));

let threads = [];
let nextThreadId = 1;
const reports = new Map();
const images = new Map();
const uploadTokens = new Map();
let imageBytes = 0;
let activeUploads = 0;

function createLimiter(windowMs, max) {
    const hits = new Map();
    let lastPurge = 0;
    return {
        take(key, now) {
            if (hits.size >= MAX_LIMITER_KEYS && !hits.has(key)) {
                if (now - lastPurge >= 1000) {
                    lastPurge = now;
                    this.purge(now);
                }
                if (hits.size >= MAX_LIMITER_KEYS) return false;
            }
            const list = (hits.get(key) || []).filter(t => now - t < windowMs);
            if (list.length >= max) {
                hits.set(key, list);
                return false;
            }
            list.push(now);
            hits.set(key, list);
            return true;
        },
        count(key, now) {
            return (hits.get(key) || []).filter(t => now - t < windowMs).length;
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
const ipReports = createLimiter(60000, IP_REPORTS_PER_MIN);
const adminFails = createLimiter(600000, ADMIN_FAILS_PER_10MIN);
const ipUploads = createLimiter(60000, IP_UPLOADS_PER_MIN);
const ipImageViews = createLimiter(60000, IP_IMAGE_VIEWS_PER_MIN);
const httpPerSec = createLimiter(1000, HTTP_PER_SEC);
const httpPerMin = createLimiter(60000, HTTP_PER_MIN);
const adminFailsGlobal = createLimiter(600000, ADMIN_FAILS_GLOBAL_PER_10MIN);
const allLimiters = [globalAttempts, ipAttempts, ipPosts, ipThreads, ipJoins, ipSearches, globalSearches, ipReports, adminFails, ipUploads, ipImageViews, httpPerSec, httpPerMin, adminFailsGlobal];
const connPerIp = new Map();
let connectionCount = 0;

class BanList {
    constructor(options) {
        this.strikesToBan = Math.max(1, options.strikesToBan);
        this.strikeWindowMs = options.strikeWindowMs;
        this.banBaseMs = options.banBaseMs;
        this.banMaxMs = options.banMaxMs;
        this.maxEntries = Math.max(1, options.maxEntries);
        this.now = options.now || Date.now;
        this.entries = new Map();
        this.lastSweep = 0;
    }

    get size() {
        return this.entries.size;
    }

    remainingMs(ip) {
        const entry = this.entries.get(ip);
        if (!entry) {
            return 0;
        }
        const remaining = entry.bannedUntil - this.now();
        return remaining > 0 ? remaining : 0;
    }

    isBanned(ip) {
        return this.remainingMs(ip) > 0;
    }

    strike(ip, minGapMs = 0) {
        const now = this.now();
        let entry = this.entries.get(ip);
        if (!entry) {
            this.makeRoom();
            entry = { count: 0, windowStart: now, bannedUntil: 0, level: 0, touched: now, lastStrikeAt: 0 };
            this.entries.set(ip, entry);
        }
        entry.touched = now;
        if (entry.bannedUntil > now) {
            return false;
        }
        if (minGapMs > 0 && entry.lastStrikeAt > 0 && now - entry.lastStrikeAt < minGapMs) {
            return false;
        }
        entry.lastStrikeAt = now;
        if (now - entry.windowStart > this.strikeWindowMs) {
            entry.count = 0;
            entry.windowStart = now;
        }
        entry.count += 1;
        if (entry.count < this.strikesToBan) {
            return false;
        }
        entry.level += 1;
        entry.count = 0;
        entry.windowStart = now;
        const duration = Math.min(this.banBaseMs * 2 ** (entry.level - 1), this.banMaxMs);
        entry.bannedUntil = now + duration;
        return true;
    }

    isExpired(entry, now) {
        if (entry.bannedUntil > now) {
            return false;
        }
        const memory = entry.level > 0 ? this.banMaxMs : this.strikeWindowMs;
        return now - entry.touched > memory;
    }

    sweep() {
        const now = this.now();
        for (const [ip, entry] of this.entries) {
            if (this.isExpired(entry, now)) {
                this.entries.delete(ip);
            }
        }
    }

    makeRoom() {
        if (this.entries.size < this.maxEntries) {
            return;
        }
        const now = this.now();
        if (now - this.lastSweep >= 1000) {
            this.lastSweep = now;
            this.sweep();
            if (this.entries.size < this.maxEntries) {
                return;
            }
        }
        let toRemove = Math.ceil(this.maxEntries * 0.1);
        for (const [ip, entry] of this.entries) {
            if (toRemove <= 0) {
                break;
            }
            if (entry.bannedUntil <= now) {
                this.entries.delete(ip);
                toRemove -= 1;
            }
        }
        while (this.entries.size >= this.maxEntries) {
            this.entries.delete(this.entries.keys().next().value);
        }
    }
}

const banList = new BanList({
    strikesToBan: BAN_STRIKES,
    strikeWindowMs: BAN_STRIKE_WINDOW_MS,
    banBaseMs: BAN_BASE_MS,
    banMaxMs: BAN_MAX_MS,
    maxEntries: BAN_MAX_ENTRIES
});
const guardStats = { blocked: 0, banned: 0, lastBanned: null, logged: 0 };
let debugIpCount = 0;

function normalizeIp(ip) {
    const text = String(ip || '');
    return text.startsWith('::ffff:') ? text.slice(7) : text;
}

function isBannedIp(ip) {
    const key = normalizeIp(ip);
    return !IP_ALLOWLIST.has(key) && banList.isBanned(key);
}

function strikeIp(ip, minGapMs) {
    const key = normalizeIp(ip);
    if (IP_ALLOWLIST.has(key)) return false;
    if (!banList.strike(key, minGapMs)) return false;
    guardStats.banned++;
    guardStats.lastBanned = key;
    if (guardStats.logged < 5) {
        guardStats.logged++;
        console.log('[防御壁] BAN: ' + key);
    }
    return true;
}

function debugIp(headers, address, picked) {
    if (!DEBUG_IP || debugIpCount >= 10) return;
    debugIpCount++;
    console.log('[IP確認] x-forwarded-for=' + headers['x-forwarded-for'] + ' / address=' + address + ' / 採用=' + picked + ' / hops=' + TRUSTED_PROXY_HOPS);
}

function clientIp(socket) {
    return ipFromHeaders(socket.handshake.headers, socket.handshake.address);
}

function ipFromHeaders(headers, address) {
    const header = headers['x-forwarded-for'];
    let picked = null;
    if (typeof header === 'string' && header.length > 0 && header.length < 1000) {
        const chain = header.split(',').map(s => s.trim()).filter(Boolean);
        if (chain.length > 0) {
            picked = chain[Math.max(0, chain.length - TRUSTED_PROXY_HOPS)].slice(0, 64);
        }
    }
    if (picked === null) {
        picked = String(address || 'unknown').slice(0, 64);
    }
    debugIp(headers, address, picked);
    return picked;
}

const HTML = String.raw`<!DOCTYPE html>
<html lang="ja">
<head>
    <meta charset="UTF-8">
    <meta name="viewport" content="width=device-width, initial-scale=1.0">
    <title>5分限定・暴言強制キモ告白変換掲示板</title>
    <style>
        .img-host { margin-left: 10px; overflow: hidden; }
        .post-img { max-width: 100%; max-height: 320px; display: block; margin-top: 6px; cursor: pointer; }
        .blurred { filter: blur(24px); }
        .img-hint { font-size: 11px; color: #777; margin-top: 2px; }
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
        .report-btn { color: #888; font-size: 11px; margin-left: 6px; text-decoration: underline; cursor: pointer; }
        .admin-del { color: #cc0000; font-size: 11px; margin-left: 6px; text-decoration: underline; cursor: pointer; }
        .post-admin .post-name { color: #cc0000; }
        .report-row { padding: 8px 4px; border-bottom: 1px dashed #ccc; font-size: 13px; word-break: break-all; }
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
            __IMAGE_RULE__
            <li>ひどい書き込みは「通報」を押してください。__REPORT_N__人が通報すると自動で非表示になります</li>
        </ul>
    </div>

    <div id="toast" class="toast"></div>

    <div id="nameBox" class="form-box" style="display: none;">
        <label>名前:</label><input type="text" id="nameInput" maxlength="__MAX_NAME_INPUT__" value="名無しさん＠５分で消滅">
    </div>

    <div id="searchBox" class="form-box">
        <form id="searchForm" class="search-row">
            <input type="text" id="searchInput" maxlength="__MAX_QUERY__" placeholder="スレ題名・書き込みを検索">
            <button type="submit" class="submit-btn">検索</button>
        </form>
        <div class="panel" id="searchResults" style="display: none; margin: 10px 0 0;"></div>
    </div>

    <div id="adminBox" class="form-box" style="display: none;">
        <b>管理人モード</b>
        <button type="button" class="submit-btn" id="reportsBtn">通報一覧を見る</button>
        <div id="reportsList"></div>
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
                <div class="form-group" id="threadImageRow" style="display: none;">
                    <label>画像:</label><input type="file" id="threadImageInput" accept="image/jpeg,image/png,image/gif,image/webp">
                </div>
                <button type="submit" class="submit-btn">スレを立てる</button>
            </form>
        </div>
        <div class="panel" id="threadList"></div>
    </div>

    <div id="threadView" style="display: none;">
        <a class="back" id="backToBoard" href="#/">← 板に戻る</a>
        <h2 id="threadTitle"></h2>
        <button type="button" class="submit-btn" id="adminThreadDel" style="display: none;">このスレを削除</button>
        <div class="notice" id="threadNotice" style="display: none;"></div>
        <div class="panel" id="postList"></div>
        <div class="form-box">
            <form id="postForm">
                <div class="form-group">
                    <label>内容:</label>
                    <textarea id="bodyInput" maxlength="__MAX_BODY__" placeholder="ここに暴言を吐くと、どうなるかな？ウヒヒ。" required></textarea>
                </div>
                <div class="form-group" id="postImageRow" style="display: none;">
                    <label>画像:</label><input type="file" id="postImageInput" accept="image/jpeg,image/png,image/gif,image/webp">
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
        var isAdmin = false;
        var viewName = 'boards';
        var imagesMode = 'off';
        var uploading = false;
        var MAX_UPLOAD = __MAX_UPLOAD_BYTES__;

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
            viewName = name;
            refreshAdminUi();
        }

        function refreshAdminUi() {
            el('adminBox').style.display = isAdmin && viewName !== 'thread' ? 'block' : 'none';
            el('adminThreadDel').style.display = isAdmin && viewName === 'thread' && currentThread ? 'inline-block' : 'none';
            refreshImageUi();
        }

        function refreshImageUi() {
            var show = imagesMode === 'all' || (imagesMode === 'admin' && isAdmin);
            el('threadImageRow').style.display = show ? 'block' : 'none';
            el('postImageRow').style.display = show ? 'block' : 'none';
        }

        function uploadImage(file, cb) {
            socket.emit('imageToken', function (res) {
                if (!res || !res.ok) {
                    cb(null, res && res.error ? res.error : '画像を送れません');
                    return;
                }
                var xhr = new XMLHttpRequest();
                xhr.open('POST', '/upload?token=' + encodeURIComponent(res.token));
                xhr.setRequestHeader('Content-Type', 'application/octet-stream');
                xhr.onload = function () {
                    var data = null;
                    try { data = JSON.parse(xhr.responseText); } catch (err) { data = null; }
                    if (xhr.status === 200 && data && data.ok) {
                        cb(data.id, null);
                    } else {
                        cb(null, data && data.error ? data.error : '画像のアップロードに失敗しました');
                    }
                };
                xhr.onerror = function () { cb(null, '画像のアップロードに失敗しました'); };
                xhr.send(file);
            });
        }

        function withImage(inputId, cb) {
            var input = el(inputId);
            var file = input.files && input.files[0];
            if (!file) {
                cb(null);
                return;
            }
            if (uploading) return;
            if (file.size > MAX_UPLOAD) {
                showToast('画像が大きすぎます（6MBまで）');
                return;
            }
            uploading = true;
            showToast('画像を送っています...');
            uploadImage(file, function (id, err) {
                uploading = false;
                if (err) {
                    showToast(err);
                    return;
                }
                cb(id);
            });
        }

        function fillImage(host, p) {
            clear(host);
            if (p.image) {
                var img = make('img', 'post-img blurred');
                img.src = '/img/' + p.image;
                img.alt = '';
                var hint = make('div', 'img-hint', '画像（ぼかし中。タップで表示、もう一度タップでぼかします）');
                img.addEventListener('click', function () {
                    var blurred = img.className.indexOf('blurred') >= 0;
                    img.className = blurred ? 'post-img' : 'post-img blurred';
                    hint.style.display = blurred ? 'none' : 'block';
                });
                host.appendChild(img);
                host.appendChild(hint);
            } else if (p.imageHidden) {
                host.appendChild(make('div', 'img-hint', '【画像は通報により削除されました】'));
            }
        }

        function setAdmin(flag) {
            var was = isAdmin;
            isAdmin = flag;
            refreshAdminUi();
            if (flag && !was) {
                showToast('管理人として認証されました');
                route();
            }
        }

        function tryAdminLogin() {
            var v = el('nameInput').value;
            if (!/[#＃]/.test(v)) return;
            socket.emit('adminLogin', v, function (res) {
                if (res && res.ok) setAdmin(true);
            });
        }

        function askConfirm(text) {
            return typeof confirm !== 'function' || confirm(text);
        }

        function reportPost(postId) {
            if (!currentThread) return;
            if (!askConfirm('この書き込みを通報しますか？')) return;
            socket.emit('report', { threadId: currentThread.id, postId: postId }, function (res) {
                if (res && res.ok) {
                    showToast(res.already ? 'もう通報済みです' : '通報しました。ありがとうございます');
                } else {
                    showToast(res && res.error ? res.error : '通報に失敗しました');
                }
            });
        }

        function adminDelete(threadId, postId, row) {
            if (!askConfirm('この書き込みを削除しますか？')) return;
            socket.emit('adminDeletePost', { threadId: threadId, postId: postId }, function (res) {
                if (res && res.ok) {
                    if (row && row.parentNode) row.parentNode.removeChild(row);
                    showToast('削除しました');
                } else {
                    showToast(res && res.error ? res.error : '削除に失敗しました');
                }
            });
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
            var node = make('div', p.admin ? 'post post-admin' : 'post');
            var head = make('div', 'post-header');
            var numSpan = make('span', 'post-num', String(p.id));
            numSpan.addEventListener('click', function () { replyTo(p.id); });
            head.appendChild(numSpan);
            head.appendChild(make('span', 'post-name', p.name));
            if (p.converted) head.appendChild(make('span', 'converted-mark', '【★強制浄化完了★】'));
            head.appendChild(make('span', 'post-date', p.date + ' '));
            head.appendChild(make('span', 'post-id', p.uid));
            if (!p.admin) {
                var rep = make('span', 'report-btn', '通報');
                rep.addEventListener('click', function () { reportPost(p.id); });
                head.appendChild(rep);
            }
            if (isAdmin) {
                var del = make('span', 'admin-del', '削除');
                del.addEventListener('click', function () { adminDelete(currentThread.id, p.id, null); });
                head.appendChild(del);
            }
            node.appendChild(head);
            var body = make('div', 'post-body');
            fillBody(body, p.body, node);
            node.appendChild(body);
            var imgHost = make('div', 'img-host');
            fillImage(imgHost, p);
            node.appendChild(imgHost);
            var badge = make('span', 'timer-badge', '残り ' + secondsLeft(p.expireAt) + '秒');
            node.appendChild(badge);
            el('postList').appendChild(node);
            postNodes[p.id] = { node: node, badge: badge, body: body, img: imgHost, expireAt: p.expireAt };
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
            currentThread = null;
            refreshAdminUi();
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
            imagesMode = d.images || 'off';
            renderBoards();
            route();
            refreshImageUi();
            tryAdminLogin();
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
            refreshAdminUi();
            clear(el('postList'));
            postNodes = {};
            postData = {};
            d.posts.forEach(function (p) { addPostNode(p); });
        });

        socket.on('newPost', function (d) {
            if (currentThread && d.threadId === currentThread.id) addPostNode(d.post);
        });

        socket.on('updatePost', function (d) {
            if (!currentThread || d.threadId !== currentThread.id) return;
            var n = postNodes[d.post.id];
            if (!n) return;
            postData[d.post.id] = d.post;
            clear(n.body);
            fillBody(n.body, d.post.body, n.node);
            fillImage(n.img, d.post);
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
            withImage('threadImageInput', function (imageId) {
                var data = {
                    boardId: currentBoard,
                    title: el('titleInput').value,
                    name: el('nameInput').value,
                    body: el('threadBodyInput').value
                };
                if (imageId) data.image = imageId;
                socket.emit('createThread', data, function (res) {
                    if (res && res.admin) setAdmin(true);
                    if (res && res.ok) {
                        el('titleInput').value = '';
                        el('threadBodyInput').value = '';
                        el('threadImageInput').value = '';
                        location.hash = '#/t/' + res.threadId;
                    } else {
                        showToast(res && res.error ? res.error : '失敗しました');
                    }
                });
            });
        });

        el('postForm').addEventListener('submit', function (e) {
            e.preventDefault();
            if (!currentThread) return;
            var threadId = currentThread.id;
            withImage('postImageInput', function (imageId) {
                var data = {
                    threadId: threadId,
                    name: el('nameInput').value,
                    body: el('bodyInput').value
                };
                if (imageId) data.image = imageId;
                socket.emit('submitPost', data, function (res) {
                    if (res && res.admin) setAdmin(true);
                    if (res && res.ok) {
                        el('bodyInput').value = '';
                        el('postImageInput').value = '';
                    } else {
                        showToast(res && res.error ? res.error : '失敗しました');
                    }
                });
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

        el('nameInput').addEventListener('change', tryAdminLogin);

        el('reportsBtn').addEventListener('click', function () {
            socket.emit('adminReports', function (res) {
                var box = el('reportsList');
                clear(box);
                if (!res || !res.ok) {
                    showToast(res && res.error ? res.error : '取得に失敗しました');
                    return;
                }
                if (!res.reports.length) box.appendChild(make('div', 'empty', '通報はありません'));
                res.reports.forEach(function (r) {
                    var row = make('div', 'report-row');
                    var a = make('a', '', '[' + boardNameOf(r.boardId) + '] ' + r.title + ' >>' + r.postId + '（通報' + r.count + '件' + (r.hidden ? '・非表示中' : '') + '）');
                    a.href = '#/t/' + r.threadId;
                    row.appendChild(a);
                    row.appendChild(make('div', 'result-snippet', r.body));
                    var del = make('button', 'submit-btn', '削除');
                    del.type = 'button';
                    del.addEventListener('click', function () { adminDelete(r.threadId, r.postId, row); });
                    row.appendChild(del);
                    box.appendChild(row);
                });
            });
        });

        el('adminThreadDel').addEventListener('click', function () {
            if (!currentThread) return;
            if (!askConfirm('このスレを丸ごと削除しますか？')) return;
            socket.emit('adminDeleteThread', { threadId: currentThread.id }, function (res) {
                if (!res || !res.ok) showToast(res && res.error ? res.error : '削除に失敗しました');
            });
        });

        socket.on('notice', function (text) {
            showToast(text);
        });

        socket.on('connect_error', function () {
            showToast('接続できません。アクセスが多すぎるようです。少し待ってからもう一度');
        });

        socket.on('disconnect', function (reason) {
            setAdmin(false);
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
    .split('__MAX_NAME_INPUT__').join(String(MAX_NAME_INPUT))
    .split('__MAX_NAME__').join(String(MAX_NAME))
    .split('__REPORT_N__').join(String(REPORT_HIDE_COUNT))
    .split('__IMAGE_RULE__').join(IMAGE_RULES[IMAGES_MODE])
    .split('__MAX_UPLOAD_BYTES__').join(String(MAX_UPLOAD_BYTES))
    .split('__MAX_TITLE__').join(String(MAX_TITLE))
    .split('__MAX_BODY__').join(String(MAX_BODY))
    .split('__MAX_QUERY__').join(String(MAX_QUERY))
    .split('__POST_CD__').join(String(COOLDOWN_MS / 1000))
    .split('__THREAD_CD__').join(String(THREAD_COOLDOWN_MS / 1000));

app.disable('x-powered-by');

app.use((req, res, next) => {
    res.set({
        'X-Content-Type-Options': 'nosniff',
        'X-Frame-Options': 'DENY',
        'Referrer-Policy': 'no-referrer'
    });
    const now = Date.now();
    const ip = ipFromHeaders(req.headers, req.socket && req.socket.remoteAddress);
    if (IP_ALLOWLIST.has(normalizeIp(ip))) return next();
    if (isBannedIp(ip)) {
        guardStats.blocked++;
        res.set('Retry-After', String(Math.ceil(banList.remainingMs(normalizeIp(ip)) / 1000)));
        return res.status(429).type('text/plain').send('アクセスが制限されています。しばらく時間をおいてください。');
    }
    if (req.path.startsWith('/img/')) return next();
    if (!httpPerSec.take(ip, now) || !httpPerMin.take(ip, now)) {
        guardStats.blocked++;
        strikeIp(ip, 1000);
        res.set('Retry-After', '10');
        return res.status(429).type('text/plain').send('リクエストが多すぎます。しばらく時間をおいてください。');
    }
    next();
});

app.get('/', (req, res) => {
    res.type('html').send(PAGE);
});

function dropImage(id) {
    if (!id) return;
    const img = images.get(id);
    if (!img) return;
    imageBytes -= img.buf.length;
    images.delete(id);
}

function isImageFile(buf) {
    if (buf.length < 12) return false;
    if (buf[0] === 0xff && buf[1] === 0xd8 && buf[2] === 0xff) return true;
    if (buf[0] === 0x89 && buf[1] === 0x50 && buf[2] === 0x4e && buf[3] === 0x47) return true;
    const head = buf.toString('latin1', 0, 4);
    if (head === 'GIF8') return true;
    return head === 'RIFF' && buf.toString('latin1', 8, 12) === 'WEBP';
}

async function convertImage(buf) {
    const meta = await sharp(buf, { limitInputPixels: MAX_INPUT_PIXELS }).metadata();
    if (!['jpeg', 'png', 'gif', 'webp'].includes(meta.format)) throw new Error('format');
    return sharp(buf, { limitInputPixels: MAX_INPUT_PIXELS })
        .rotate()
        .resize({ width: MAX_IMAGE_SIDE, height: MAX_IMAGE_SIDE, fit: 'inside', withoutEnlargement: true })
        .flatten({ background: '#ffffff' })
        .jpeg({ quality: 80 })
        .toBuffer();
}

function imagesAllowed(socket) {
    return IMAGES_MODE === 'all' || (IMAGES_MODE === 'admin' && !!socket.data.admin);
}

function takeImage(socket, id) {
    if (id === undefined || id === null) return { ok: true, id: null, image: null };
    if (typeof id !== 'string' || !/^[0-9a-f]{24}$/.test(id)) return { ok: false };
    const img = images.get(id);
    if (!img || img.attached || img.owner !== socket.id || img.expireAt <= Date.now()) return { ok: false };
    if (!imagesAllowed(socket)) return { ok: false };
    return { ok: true, id: id, image: img };
}

function attachImage(post, taken) {
    if (!taken.image) return;
    taken.image.attached = true;
    taken.image.expireAt = post.expireAt;
    post.image = taken.id;
}

const IMAGE_GONE = '画像の期限が切れました。もう一度選んでください';

function uploadGuard(req, res, next) {
    if (IMAGES_MODE === 'off') {
        return res.status(403).json({ ok: false, error: '画像は今は使えません' });
    }
    const token = typeof req.query.token === 'string' ? req.query.token : '';
    const entry = uploadTokens.get(token);
    uploadTokens.delete(token);
    if (!entry || entry.expireAt <= Date.now()) {
        return res.status(403).json({ ok: false, error: 'もう一度試してください' });
    }
    if (activeUploads >= MAX_CONCURRENT_UPLOADS) {
        return res.status(503).json({ ok: false, error: '混み合っています。少し待ってからもう一度' });
    }
    activeUploads++;
    let released = false;
    res.on('close', () => {
        if (!released) {
            released = true;
            activeUploads--;
        }
    });
    req.uploadEntry = entry;
    next();
}

app.post('/upload', uploadGuard, express.raw({ type: '*/*', limit: MAX_UPLOAD_BYTES, inflate: false }), async (req, res) => {
    const entry = req.uploadEntry;
    const buf = req.body;
    if (!Buffer.isBuffer(buf) || !isImageFile(buf)) {
        return res.status(400).json({ ok: false, error: '対応していない画像です（JPEG・PNG・GIF・WebPだけ）' });
    }
    let out;
    try {
        out = await convertImage(buf);
    } catch (e) {
        return res.status(400).json({ ok: false, error: '画像を読み込めませんでした。大きすぎるか、壊れています' });
    }
    if (imageBytes + out.length > MAX_IMAGE_TOTAL_BYTES) {
        return res.status(503).json({ ok: false, error: 'いま画像がいっぱいです。少し待ってください' });
    }
    const id = crypto.randomBytes(12).toString('hex');
    images.set(id, { buf: out, owner: entry.owner, attached: false, expireAt: Date.now() + ORPHAN_IMAGE_MS });
    imageBytes += out.length;
    res.json({ ok: true, id: id });
});

app.get('/img/:id', (req, res) => {
    const now = Date.now();
    const ip = ipFromHeaders(req.headers, req.socket && req.socket.remoteAddress);
    if (!ipImageViews.take(ip, now)) return res.status(429).end();
    const id = String(req.params.id);
    const img = /^[0-9a-f]{24}$/.test(id) ? images.get(id) : null;
    if (!img || !img.attached || img.expireAt <= now) return res.status(404).end();
    res.set({
        'Content-Type': 'image/jpeg',
        'X-Content-Type-Options': 'nosniff',
        'Cache-Control': 'no-store',
        'Content-Security-Policy': "default-src 'none'; sandbox",
        'Cross-Origin-Resource-Policy': 'same-origin'
    });
    res.send(img.buf);
});

app.use((err, req, res, next) => {
    if (res.headersSent) return next(err);
    const tooBig = err && err.status === 413;
    res.status(tooBig ? 413 : 400).json({ ok: false, error: tooBig ? '画像が大きすぎます（6MBまで）' : '送信に失敗しました' });
});

function sanitizeName(raw) {
    const trimmed = raw.trim();
    if (trimmed === DEFAULT_NAME) return DEFAULT_NAME;
    const cleaned = trimmed
        .replace(/[^\p{L}\p{N}\s]/gu, '')
        .replace(/\s+/g, ' ')
        .trim()
        .slice(0, MAX_NAME);
    const flat = cleaned.normalize('NFKC').replace(/\s/g, '');
    if (!cleaned || flat.includes('管理人') || flat.includes('管理者')) return DEFAULT_NAME;
    return cleaned;
}

function splitName(raw) {
    const text = raw.slice(0, MAX_NAME_INPUT);
    const at = text.search(/[#＃]/);
    if (at < 0) return { name: text, secret: null };
    return { name: text.slice(0, at), secret: text.slice(at + 1) };
}

function secretMatches(secret) {
    const a = crypto.createHash('sha256').update(secret.normalize('NFKC').trim()).digest();
    const b = crypto.createHash('sha256').update(ADMIN_PASSWORD).digest();
    return crypto.timingSafeEqual(a, b);
}

function checkAdmin(socket, secret) {
    if (secret === null || !ADMIN_ENABLED) return false;
    const now = Date.now();
    const ip = socket.data.ip;
    if (adminFails.count(ip, now) >= ADMIN_FAILS_PER_10MIN) {
        strikeIp(ip, 10000);
        return false;
    }
    if (adminFailsGlobal.count('all', now) >= ADMIN_FAILS_GLOBAL_PER_10MIN) return false;
    if (secretMatches(secret)) {
        socket.data.admin = true;
        return true;
    }
    adminFails.take(ip, now);
    adminFailsGlobal.take('all', now);
    return false;
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

function dropReports(threadId) {
    reports.forEach((e, key) => {
        if (e.threadId === threadId) reports.delete(key);
    });
}

function purgeReports(now) {
    reports.forEach((e, key) => {
        const t = findThread(e.threadId);
        const alive = t && t.posts.some(p => p.id === e.postId && p.expireAt > now);
        if (!alive) reports.delete(key);
    });
}

function hideImage(thread, post) {
    dropImage(post.image);
    post.image = null;
    post.imageHidden = true;
    io.to('thread:' + thread.id).emit('updatePost', { threadId: thread.id, post: post });
}

function hidePost(thread, post) {
    if (post.image) {
        dropImage(post.image);
        post.image = null;
        post.imageHidden = true;
    }
    post.body = HIDDEN_BODY;
    post.hidden = true;
    post.converted = false;
    searchKeys.delete(post);
    io.to('thread:' + thread.id).emit('updatePost', { threadId: thread.id, post: post });
}

function removeThread(t) {
    threads = threads.filter(x => x !== t);
    t.posts.forEach(p => dropImage(p.image));
    dropReports(t.id);
    io.to('thread:' + t.id).emit('threadGone', { threadId: t.id });
}

function trimBoard(boardId) {
    const list = boardThreads(boardId);
    while (list.length > MAX_THREADS_PER_BOARD) {
        removeThread(list.pop());
    }
}

function makePost(thread, socket, rawName, rawBody) {
    const parts = splitName(rawName);
    const admin = checkAdmin(socket, parts.secret);
    const cleanName = admin ? ADMIN_NAME : sanitizeName(parts.name);
    const name = findReply(cleanName) ? DEFAULT_NAME : cleanName;
    const hit = findReply(rawBody);
    const now = Date.now();
    thread.postCount++;
    const post = {
        id: thread.postCount,
        name: name,
        body: hit || rawBody,
        date: formatDate(now),
        uid: admin ? 'ID:★★★' : 'ID:' + socket.id.substring(0, 8).toUpperCase(),
        converted: !!hit,
        admin: admin,
        hidden: false,
        image: null,
        imageHidden: false,
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
    if (isBannedIp(ip)) {
        guardStats.blocked++;
        return next(new Error('banned'));
    }
    if (!globalAttempts.take('all', now)) {
        guardStats.blocked++;
        return next(new Error('too many attempts'));
    }
    if (!ipAttempts.take(ip, now)) {
        guardStats.blocked++;
        strikeIp(ip, 1000);
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
            guardStats.blocked++;
            strikeIp(ip, 1000);
            socket.disconnect(true);
            return;
        }
        next();
    });

    socket.emit('init', { boards: BOARDS, counts: countsOf(), images: IMAGES_MODE, serverTime: Date.now() });

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
        const taken = takeImage(socket, data.image);
        if (!taken.ok) {
            return reply(ack, { ok: false, error: IMAGE_GONE });
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
        const first = makePost(thread, socket, data.name, rawBody);
        attachImage(first, taken);
        trimBoard(thread.boardId);
        emitBoard(thread.boardId);
        emitCounts();
        reply(ack, { ok: true, threadId: thread.id, admin: first.admin });
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
        const taken = takeImage(socket, data.image);
        if (!taken.ok) {
            return reply(ack, { ok: false, error: IMAGE_GONE });
        }
        if (!ipPosts.take(ip, now)) {
            return reply(ack, { ok: false, error: 'このIPからの書き込みが多すぎます。少し待ってください' });
        }
        lastPostAt = now;

        const post = makePost(thread, socket, data.name, rawBody);
        attachImage(post, taken);
        io.to('thread:' + thread.id).emit('newPost', { threadId: thread.id, post: post });
        emitBoard(thread.boardId);
        reply(ack, { ok: true, admin: post.admin });
    });

    socket.on('report', (data, ack) => {
        if (!data || !Number.isInteger(data.threadId) || !Number.isInteger(data.postId)) {
            return reply(ack, { ok: false, error: '入力が正しくありません' });
        }
        const now = Date.now();
        if (!ipReports.take(ip, now)) {
            return reply(ack, { ok: false, error: '通報が多すぎます。少し待ってください' });
        }
        const thread = findThread(data.threadId);
        const post = thread ? livePosts(thread, now).find(p => p.id === data.postId) : null;
        if (!post) {
            return reply(ack, { ok: false, error: 'その書き込みはもう消えています' });
        }
        if (post.admin) {
            return reply(ack, { ok: false, error: 'この書き込みは通報できません' });
        }
        if (post.hidden) {
            return reply(ack, { ok: true, already: true });
        }
        const key = thread.id + ':' + post.id;
        let entry = reports.get(key);
        if (!entry) {
            if (reports.size >= MAX_REPORT_ENTRIES) {
                return reply(ack, { ok: false, error: '通報が混み合っています。少し待ってください' });
            }
            entry = { threadId: thread.id, postId: post.id, ips: new Set(), orig: post.body };
            reports.set(key, entry);
        }
        if (entry.ips.has(ip)) {
            return reply(ack, { ok: true, already: true });
        }
        entry.ips.add(ip);
        if (post.image) hideImage(thread, post);
        if (entry.ips.size >= REPORT_HIDE_COUNT) hidePost(thread, post);
        reply(ack, { ok: true });
    });

    socket.on('imageToken', (ack) => {
        if (IMAGES_MODE === 'off') return reply(ack, { ok: false, error: '画像は今は使えません' });
        if (!imagesAllowed(socket)) return reply(ack, { ok: false, error: '画像は管理人だけが使えます' });
        const now = Date.now();
        let pending = 0;
        uploadTokens.forEach((t) => {
            if (t.owner === socket.id && t.expireAt > now) pending++;
        });
        if (pending >= MAX_PENDING_TOKENS) {
            return reply(ack, { ok: false, error: '少し待ってからもう一度送ってください' });
        }
        if (!ipUploads.take(ip, now)) {
            return reply(ack, { ok: false, error: '画像の投稿が多すぎます。少し待ってください' });
        }
        const token = crypto.randomBytes(18).toString('hex');
        uploadTokens.set(token, { owner: socket.id, expireAt: now + TOKEN_TTL_MS });
        reply(ack, { ok: true, token: token });
    });

    socket.on('adminLogin', (text, ack) => {
        if (typeof text !== 'string') return reply(ack, { ok: false });
        const parts = splitName(text);
        reply(ack, { ok: checkAdmin(socket, parts.secret) });
    });

    socket.on('adminReports', (ack) => {
        if (!socket.data.admin) return reply(ack, { ok: false, error: '権限がありません' });
        const now = Date.now();
        const list = [];
        reports.forEach((e) => {
            const t = findThread(e.threadId);
            const p = t ? livePosts(t, now).find(x => x.id === e.postId) : null;
            if (!p) return;
            list.push({
                threadId: t.id,
                boardId: t.boardId,
                title: t.title,
                postId: p.id,
                count: e.ips.size,
                hidden: !!p.hidden,
                body: e.orig
            });
        });
        list.sort((a, b) => b.count - a.count);
        reply(ack, { ok: true, reports: list.slice(0, 50) });
    });

    socket.on('adminDeletePost', (data, ack) => {
        if (!socket.data.admin) return reply(ack, { ok: false, error: '権限がありません' });
        if (!data || !Number.isInteger(data.threadId) || !Number.isInteger(data.postId)) {
            return reply(ack, { ok: false, error: '入力が正しくありません' });
        }
        const t = findThread(data.threadId);
        if (!t || !t.posts.some(p => p.id === data.postId)) {
            return reply(ack, { ok: false, error: 'もう消えています' });
        }
        t.posts.forEach(p => {
            if (p.id === data.postId) dropImage(p.image);
        });
        t.posts = t.posts.filter(p => p.id !== data.postId);
        reports.delete(t.id + ':' + data.postId);
        io.to('thread:' + t.id).emit('deletePost', { threadId: t.id, postId: data.postId });
        if (livePosts(t, Date.now()).length === 0) {
            removeThread(t);
            emitCounts();
        }
        emitBoard(t.boardId);
        reply(ack, { ok: true });
    });

    socket.on('adminDeleteThread', (data, ack) => {
        if (!socket.data.admin) return reply(ack, { ok: false, error: '権限がありません' });
        if (!data || !Number.isInteger(data.threadId)) {
            return reply(ack, { ok: false, error: '入力が正しくありません' });
        }
        const t = findThread(data.threadId);
        if (!t) return reply(ack, { ok: false, error: 'もう消えています' });
        removeThread(t);
        emitBoard(t.boardId);
        emitCounts();
        reply(ack, { ok: true });
    });
});

let sweepTicks = 0;

setInterval(() => {
    const now = Date.now();
    const dirtyBoards = new Set();
    sweepTicks++;
    if (sweepTicks % 60 === 0) {
        allLimiters.forEach(l => l.purge(now));
        banList.sweep();
    }
    if (sweepTicks % 10 === 0) purgeReports(now);
    images.forEach((img, id) => {
        if (img.expireAt <= now) dropImage(id);
    });
    uploadTokens.forEach((t, key) => {
        if (t.expireAt <= now) uploadTokens.delete(key);
    });
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

setInterval(() => {
    if (guardStats.blocked > 0 || guardStats.banned > 0) {
        console.log('[防御壁] 直近10秒: 遮断 ' + guardStats.blocked + '件 / 新規BAN ' + guardStats.banned + '件 / 管理中IP ' + banList.size + '件' + (guardStats.lastBanned ? ' / 最後にBANしたIP ' + guardStats.lastBanned : ''));
    }
    guardStats.blocked = 0;
    guardStats.banned = 0;
    guardStats.logged = 0;
}, 10000).unref();

const PORT = process.env.PORT || 3000;
server.listen(PORT, () => {
    console.log('Server is running on port ' + PORT);
    console.log('Images: ' + IMAGES_MODE + (sharp ? '' : ' (sharp is not installed)'));
    console.log(ADMIN_ENABLED ? 'Admin mode: enabled' : 'Admin mode: disabled (set ADMIN_PASSWORD with 8+ characters)');
});
