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
        words: prepareWords([
            '殺す', 'ころす', '殺せ', 'ころせ',
            '殺してやる', '殺してやろ', '殺しに行', '殺しにい', '殺したい', '殺しちゃ', '殺しちま', '殺そう',
            'ころしてやる', 'ころしてやろ', 'ころしにいく', 'ころしたい',
            'ぶち殺', 'ぶっ殺', 'ぶちころ', 'ぶっころ'
        ])
    },
    {
        target: 'letters',
        reply: "愛してるぜ…",
        words: prepareWords([
            '氏ね', 'くたばれ', '消えろ', 'きえろ',
            '死にやがれ', 'しにやがれ', '死んでしまえ', 'しんでしまえ', '死んじまえ', 'しんじまえ',
            '死んでくれ', '死んでこい', '死に晒せ', 'しにさらせ',
            'くたばっちまえ', 'くたばりやがれ', 'くたばってしまえ', 'くたばってくれ'
        ]),
        patterns: [
            /死[^\p{L}\p{N}]*ね(?!ない|なかっ|る)/u,
            /(^|[^ぁ-ゖ])し[^\p{L}\p{N}]*ね/u,
            /シ[^\p{L}\p{N}]*ネ(?![マコ])/u,
            /(おまえ|てめえ|てめぇ|きさま|あんた)し[^\p{L}\p{N}]*ね/u
        ]
    },
    {
        target: 'letters',
        reply: "愛してるぜ…",
        words: prepareWords(['きちがい', '気違い', '気ちがい']),
        lettersPatterns: [
            /がいじ(?![んゃゅょ])/u
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
        const lettersHit = (rule.lettersPatterns || []).some(p => p.test(forms.letters));
        if (wordHit || patternHit || lettersHit) return rule.reply;
    }
    return null;
}

module.exports = { toHiragana, findReply };
