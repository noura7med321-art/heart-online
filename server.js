'use strict';
/*
 * هارت أونلاين — standalone public server for Nour's "Heart" card game.
 * Zero dependencies: Node built-in http only. All room/match state lives in
 * memory here (single source of truth). Player XP/coins persist to players.json.
 * Rules: ~/workspace/heart-game/rules.md (Nour's custom rules, NOT standard Hearts).
 */
const http = require('http');
const fs = require('fs');
const path = require('path');
const crypto = require('crypto');

const PORT = process.env.PORT ? parseInt(process.env.PORT, 10) : 8377;
const ROOT = __dirname;
const PLAYERS_FILE = path.join(ROOT, 'players.json');
const INDEX_FILE = path.join(ROOT, 'public', 'index.html');

/* ---------------- players (persistent XP / coins) ---------------- */
let players = {};
try { players = JSON.parse(fs.readFileSync(PLAYERS_FILE, 'utf8')) || {}; } catch (e) { players = {}; }
function savePlayers() {
  try {
    const tmp = PLAYERS_FILE + '.tmp';
    fs.writeFileSync(tmp, JSON.stringify(players, null, 1));
    fs.renameSync(tmp, PLAYERS_FILE);
  } catch (e) { /* non-fatal */ }
}
const LEVEL_XP = [0, 100, 250, 450, 700, 1000];
function levelOf(xp) { let l = 1; for (let i = 0; i < LEVEL_XP.length; i++) if (xp >= LEVEL_XP[i]) l = i + 1; return l; }
function getPlayer(token) { return token && players[token] ? players[token] : null; }

/* ---------------- cards ---------------- */
const SUITS = ['S', 'H', 'D', 'C']; // spades, hearts, diamonds, clubs
function cardCode(s, r) { return s + r; } // e.g. "S12" = Queen of Spades, "H5"
function parseCard(c) { return { s: c[0], r: parseInt(c.slice(1), 10) }; }
function cardPoints(c) { const p = parseCard(c); if (p.s === 'H') return 1; if (p.s === 'S' && p.r === 12) return 7; return 0; }
function fullDeck() { const d = []; for (const s of SUITS) for (let r = 2; r <= 14; r++) d.push(cardCode(s, r)); return d; }
function shuffle(a) { for (let i = a.length - 1; i > 0; i--) { const j = crypto.randomInt(i + 1); [a[i], a[j]] = [a[j], a[i]]; } return a; }
function sortHand(h) { const so = { S: 0, H: 1, D: 2, C: 3 }; return h.slice().sort((a, b) => { const x = parseCard(a), y = parseCard(b); return so[x.s] - so[y.s] || x.r - y.r; }); }

/* ---------------- rooms ---------------- */
const rooms = new Map();
const CODE_ALPHABET = 'ABCDEFGHJKMNPQRSTUVWXYZ23456789';
function newCode() { let c; do { c = ''; for (let i = 0; i < 5; i++) c += CODE_ALPHABET[crypto.randomInt(CODE_ALPHABET.length)]; } while (rooms.has(c)); return c; }
const BOT_NAMES = ['الصقر', 'النمر', 'الذئب', 'الفهد', 'العقاب', 'الثعلب'];
const BOT_AVATARS = ['🦅', '🐅', '🐺', '🐆', '🦇', '🦊'];
const BOT_EMOJIS = ['😄', '😎', '🔥', '👏', '😮', '💪', '🎉', '😉'];

function humanSeat(room, token) { return room.seats.find(s => s.token && s.token === token) || null; }
function seatIndex(room, token) { return room.seats.findIndex(s => s.token && s.token === token); }
function bump(room) { room.version++; room.updatedAt = Date.now(); }
function makeSeat() { return { token: null, bot: false, botControlled: false, name: '', avatar: '👤', lastSeen: 0 }; }

/* ---------------- game engine ---------------- */
function legalCards(hand, trick, isFirstLeadOfRound) {
  if (!trick || trick.length === 0) {
    if (isFirstLeadOfRound) { const nh = hand.filter(c => parseCard(c).s !== 'H'); return nh.length ? nh : hand.slice(); }
    return hand.slice();
  }
  const led = parseCard(trick[0].card).s;
  const follow = hand.filter(c => parseCard(c).s === led);
  return follow.length ? follow : hand.slice();
}
function lowestLegal(hand, trick, firstLead) {
  const legal = legalCards(hand, trick, firstLead);
  return legal.slice().sort((a, b) => parseCard(a).r - parseCard(b).r || SUITS.indexOf(parseCard(a).s) - SUITS.indexOf(parseCard(b).s))[0];
}
function scoreRound(taken) {
  const t0 = taken[0] + taken[2], t1 = taken[1] + taken[3];
  const e = taken.map(x => x > 0);
  const solo = taken.findIndex(x => x === 20);
  if (solo >= 0) { const team = solo % 2, other = 1 - team; const s = [0, 0]; s[other] = 12; s[team] = -12; return { score: s, special: 'solo20' }; }
  const be0 = e[0] && e[2], be1 = e[1] && e[3];
  if (be0 !== be1) { const beTeam = be0 ? 0 : 1, other = 1 - beTeam, tot = beTeam === 0 ? t0 : t1; const s = [0, 0]; s[other] = tot; s[beTeam] = -tot; return { score: s, special: 'bothEntered' }; }
  const s0 = 10 - t0; return { score: [s0, -s0], special: null };
}

/* ---- bot brains (sensible, legal) ---- */
function botPass(hand) {
  const picks = [];
  const has = c => hand.includes(c) && !picks.includes(c);
  const spades = hand.filter(c => parseCard(c).s === 'S');
  if (has('S12') && spades.length <= 3) picks.push('S12');
  if (!has('S12')) { if (has('S14') && spades.length <= 4) picks.push('S14'); if (has('S13') && spades.length <= 4 && picks.length < 4) picks.push('S13'); }
  // short-suit yourself: dump highest cards of shortest suits
  const suits = SUITS.map(s => ({ s, cards: hand.filter(c => parseCard(c).s === s && !picks.includes(c)).sort((a, b) => parseCard(b).r - parseCard(a).r) }))
    .sort((a, b) => a.cards.length - b.cards.length);
  for (const su of suits) { for (const c of su.cards) { if (picks.length >= 4) break; if (su.cards.length <= 2 || parseCard(c).r >= 12) picks.push(c); } if (picks.length >= 4) break; }
  // then highest hearts, then highest anything
  const rest = hand.filter(c => !picks.includes(c)).sort((a, b) => (parseCard(b).s === 'H') - (parseCard(a).s === 'H') || parseCard(b).r - parseCard(a).r);
  for (const c of rest) { if (picks.length >= 4) break; picks.push(c); }
  return picks.slice(0, 4);
}
function botPlay(hand, trick, firstLead) {
  const legal = legalCards(hand, trick, firstLead);
  const byRank = legal.slice().sort((a, b) => parseCard(a).r - parseCard(b).r);
  if (!trick || trick.length === 0) {
    // lead: lowest card of the longest suit (hearts already excluded on first lead by legal)
    const counts = {}; for (const c of legal) counts[parseCard(c).s] = (counts[parseCard(c).s] || 0) + 1;
    const bestSuit = Object.keys(counts).sort((a, b) => counts[b] - counts[a])[0];
    const inSuit = byRank.filter(c => parseCard(c).s === bestSuit);
    return inSuit[0] || byRank[0];
  }
  const led = parseCard(trick[0].card).s;
  const follow = byRank.filter(c => parseCard(c).s === led);
  if (follow.length) {
    // shed the Queen safely if Ace/King of spades already on the table
    if (led === 'S' && follow.some(c => c === 'S12') && trick.some(t => t.card === 'S14' || t.card === 'S13')) return 'S12';
    const winRank = Math.max(...trick.filter(t => parseCard(t.card).s === led).map(t => parseCard(t.card).r));
    const nonQ = follow.filter(c => c !== 'S12');
    if (trick.length === 3) { const duck = nonQ.filter(c => parseCard(c).r < winRank); if (duck.length) return duck[duck.length - 1]; }
    if (nonQ.length && trick.length < 3) return nonQ[0];
    return follow[0];
  }
  // void: shed Queen, then A/K spades, then highest heart, then highest card
  if (legal.includes('S12')) return 'S12';
  if (legal.includes('S14')) return 'S14';
  if (legal.includes('S13')) return 'S13';
  const hearts = byRank.filter(c => parseCard(c).s === 'H');
  if (hearts.length) return hearts[hearts.length - 1];
  return byRank[byRank.length - 1];
}

/* ---- match lifecycle ---- */
function startMatch(room) {
  const humans = room.seats.filter(s => s.token && !s.bot);
  if (room.fillBots) {
    let bi = 0;
    room.seats = room.seats.map(s => {
      if (s.token && !s.bot) return s;
      const b = makeSeat(); b.bot = true; b.name = BOT_NAMES[bi % BOT_NAMES.length]; b.avatar = BOT_AVATARS[bi % BOT_AVATARS.length]; bi++; return b;
    });
  } else if (humans.length < 4) {
    return { error: 'لازم 4 لاعيبة أو تفعّل ملء المقاعد بالبوتات' };
  }
  const dealer = crypto.randomInt(4);
  room.match = {
    round: 1, dealer, starter: dealer, phase: 'passing',
    cum: [0, 0], history: [], coinsRound: [0, 0, 0, 0],
    settlement: null, lastRound: null
  };
  startRound(room, dealer);
  bump(room);
  return { ok: true };
}
function startRound(room, starter) {
  const m = room.match;
  const deck = shuffle(fullDeck());
  m.hands = [[], [], [], []];
  for (let i = 0; i < 52; i++) m.hands[i % 4].push(deck[i]);
  m.hands = m.hands.map(sortHand);
  m.passCards = [null, null, null, null];
  m.passedFrom = [[], [], [], []];
  m.taken = [0, 0, 0, 0];
  m.heartsTaken = 0; m.queenTaken = false; m.queenTaker = -1;
  m.trick = []; m.trickLeader = starter; m.current = -1; m.trickIndex = 0;
  m.lastTrick = null; m.trickHoldUntil = 0;
  m.snapUsed = [false, false, false, false];
  m.snaps = []; m.queenHint = {}; // partnerSeat -> queenWithSeat
  m.phase = 'passing';
  m.turnDeadline = room.timer ? Date.now() + room.timer * 1000 : 0;
  m.botAt = Date.now() + 900;
  m.roundEndAt = 0;
}
function applyPasses(room) {
  const m = room.match;
  for (let s = 0; s < 4; s++) {
    const cards = m.passCards[s];
    m.passedFrom[s] = cards.slice();
    m.hands[s] = m.hands[s].filter(c => !cards.includes(c));
  }
  for (let s = 0; s < 4; s++) { const to = (s + 1) % 4; m.hands[to] = sortHand(m.hands[to].concat(m.passCards[s])); }
  m.phase = 'playing';
  m.current = m.trickLeader;
  m.turnDeadline = room.timer ? Date.now() + room.timer * 1000 : 0;
  m.botAt = Date.now() + 800;
}
function doPlay(room, seat, card, snap) {
  const m = room.match;
  if (m.phase !== 'playing' || m.current !== seat) return { error: 'مش دورك' };
  if (m.trickHoldUntil && Date.now() < m.trickHoldUntil) return { error: 'استنى' };
  const hand = m.hands[seat];
  if (!hand.includes(card)) return { error: 'الكارت مش في إيدك' };
  const firstLead = m.trickIndex === 0 && m.trick.length === 0;
  const legal = legalCards(hand, m.trick, firstLead);
  if (!legal.includes(card)) {
    if (firstLead && parseCard(card).s === 'H') return { error: 'مينفعش تفتح هارت أول فتحة' };
    return { error: 'لازم تلعب من نفس القطوع' };
  }
  // snap registration (only on a lead, once per round)
  if (snap && m.trick.length === 0 && !m.snapUsed[seat]) {
    m.snapUsed[seat] = true;
    m.snaps.push({ seat, at: Date.now() });
    if (m.passedFrom[seat].includes('S12')) m.queenHint[(seat + 2) % 4] = (seat + 1) % 4;
  }
  m.hands[seat] = hand.filter(c => c !== card);
  m.trick.push({ seat, card });
  if (m.trick.length < 4) {
    m.current = (seat + 1) % 4;
    m.turnDeadline = room.timer ? Date.now() + room.timer * 1000 : 0;
    m.botAt = Date.now() + 750;
  } else {
    resolveTrick(room);
  }
  bump(room);
  return { ok: true };
}
function resolveTrick(room) {
  const m = room.match;
  const led = parseCard(m.trick[0].card).s;
  let win = m.trick[0];
  for (const t of m.trick) { const p = parseCard(t.card); if (p.s === led && p.r > parseCard(win.card).r) win = t; }
  const pts = m.trick.reduce((a, t) => a + cardPoints(t.card), 0);
  m.taken[win.seat] += pts;
  for (const t of m.trick) { const p = parseCard(t.card); if (p.s === 'H') m.heartsTaken++; if (t.card === 'S12') { m.queenTaken = true; m.queenTaker = win.seat; } }
  m.lastTrick = { plays: m.trick.slice(), winner: win.seat };
  // occasional bot reaction
  if (crypto.randomInt(4) === 0) { const bs = room.seats.findIndex(s => s.bot || s.botControlled); if (bs >= 0) room.emojis[bs] = { e: BOT_EMOJIS[crypto.randomInt(BOT_EMOJIS.length)], at: Date.now() }; }
  const roundOver = (m.heartsTaken >= 13 && m.queenTaken) || m.hands.every(h => h.length === 0);
  if (roundOver) { endRound(room); return; }
  m.trickHoldUntil = Date.now() + 1200;
  m.nextLeader = win.seat;
  m.current = -1;
}
function endRound(room) {
  const m = room.match;
  const res = scoreRound(m.taken);
  m.cum[0] += res.score[0]; m.cum[1] += res.score[1];
  const winTeam = res.score[0] > 0 ? 0 : 1;
  for (let s = 0; s < 4; s++) if (s % 2 === winTeam) { m.coinsRound[s] += 2 + (res.special ? 5 : 0); }
  const summary = { round: m.round, taken: m.taken.slice(), teamTaken: [m.taken[0] + m.taken[2], m.taken[1] + m.taken[3]], score: res.score.slice(), special: res.special, cum: m.cum.slice() };
  m.history.push(summary);
  m.lastRound = summary;
  m.trick = [];
  const matchOver = m.round >= 7 && m.cum[0] !== m.cum[1];
  if (matchOver) { settleMatch(room); m.phase = 'matchEnd'; }
  else { m.phase = 'roundEnd'; m.roundEndAt = Date.now() + 4000; m.nextStarter = m.queenTaker >= 0 ? m.queenTaker : m.trickLeader; }
}
function settleMatch(room) {
  const m = room.match;
  m.settlement = {};
  for (let s = 0; s < 4; s++) {
    const seat = room.seats[s];
    if (!seat.token || seat.bot) continue;
    const p = getPlayer(seat.token); if (!p) continue;
    const team = s % 2, won = m.cum[team] > m.cum[1 - team];
    const margin = Math.abs(m.cum[0] - m.cum[1]);
    const xpDelta = won ? 50 + Math.min(30, margin) : -25;
    const coinsDelta = 10 + (won ? 25 : 0) + m.coinsRound[s];
    p.xp = Math.max(0, p.xp + xpDelta);
    p.coins += coinsDelta;
    m.settlement[seat.token] = { xpDelta, coinsDelta, xp: p.xp, coins: p.coins, won };
  }
  savePlayers();
}

/* ---- server tick: bots, timers, phase advances, disconnect takeover ---- */
function roomTick(room) {
  const m = room.match;
  const now = Date.now();
  // disconnect takeover (mid-match): human seat silent > 9s -> bot drives it
  if (m && (m.phase === 'passing' || m.phase === 'playing')) {
    for (const s of room.seats) {
      if (s.token && !s.bot && !s.botControlled && s.lastSeen && now - s.lastSeen > 9000) { s.botControlled = true; bump(room); }
    }
  }
  if (!m) return;
  if (m.phase === 'passing') {
    if (now >= m.botAt) {
      let changed = false;
      for (let s = 0; s < 4; s++) {
        const seat = room.seats[s];
        if ((seat.bot || seat.botControlled) && !m.passCards[s]) { m.passCards[s] = botPass(m.hands[s]); changed = true; }
      }
      if (changed) { bump(room); m.botAt = now + 600; }
    }
    if (room.timer && m.turnDeadline && now > m.turnDeadline) {
      for (let s = 0; s < 4; s++) if (!m.passCards[s]) m.passCards[s] = botPass(m.hands[s]);
    }
    if (m.passCards.every(c => c)) applyPasses(room), bump(room);
  } else if (m.phase === 'playing') {
    if (m.trickHoldUntil && now >= m.trickHoldUntil) {
      m.trick = []; m.trickIndex++; m.trickLeader = m.nextLeader; m.current = m.nextLeader; m.trickHoldUntil = 0;
      m.turnDeadline = room.timer ? now + room.timer * 1000 : 0; m.botAt = now + 750; bump(room); return;
    }
    if (m.current < 0) return;
    const seat = room.seats[m.current];
    const isBot = seat.bot || seat.botControlled;
    const oneCard = m.hands[m.current].length === 1;
    if (isBot && now >= m.botAt) {
      const c = botPlay(m.hands[m.current], m.trick, m.trickIndex === 0 && m.trick.length === 0);
      doPlay(room, m.current, c, false);
    } else if (!isBot && oneCard && now >= m.botAt) {
      doPlay(room, m.current, m.hands[m.current][0], false); // last card auto-plays
    } else if (!isBot && room.timer && m.turnDeadline && now > m.turnDeadline) {
      const c = lowestLegal(m.hands[m.current], m.trick, m.trickIndex === 0 && m.trick.length === 0);
      doPlay(room, m.current, c, false);
      m.botAt = now + 800;
    }
  } else if (m.phase === 'roundEnd') {
    if (now >= m.roundEndAt) { m.round++; startRound(room, m.nextStarter); bump(room); }
  }
}
setInterval(() => { for (const room of rooms.values()) { try { roomTick(room); } catch (e) { console.error('tick', e); } } }, 400);
// sweep stale empty rooms hourly-ish (30 min idle, lobby only)
setInterval(() => { const now = Date.now(); for (const [code, room] of rooms) { if (room.phase === 'lobby' && now - room.updatedAt > 30 * 60 * 1000) rooms.delete(code); } }, 60000);

/* ---------------- state view (per player — own hand only) ---------------- */
function stateFor(room, token) {
  const mySeat = seatIndex(room, token);
  const m = room.match;
  const st = {
    ok: true, version: room.version, phase: m ? m.phase : 'lobby',
    room: { code: room.code, isHost: room.hostToken === token, timer: room.timer, fillBots: room.fillBots, hasPassword: !!room.password },
    seats: room.seats.map((s, i) => ({
      seat: i, name: s.bot ? s.name : (s.token ? s.name : ''), avatar: s.avatar,
      bot: !!s.bot, botControlled: !!s.botControlled, empty: !s.token && !s.bot,
      isMe: i === mySeat, connected: s.bot ? true : (Date.now() - (s.lastSeen || 0) < 12000),
      cardCount: m ? m.hands[i].length : 0, takenPts: m ? m.taken[i] : 0,
      snapped: m ? !!m.snapUsed[i] : false, passed: m ? !!m.passCards[i] : false
    })),
    emojis: room.emojis || {},
    me: null, play: null, scores: null, matchInfo: null
  };
  if (mySeat >= 0 && m) {
    st.me = {
      seat: mySeat, hand: m.hands[mySeat].slice(),
      passSubmitted: !!m.passCards[mySeat], snapUsed: m.snapUsed[mySeat],
      queenHintSeat: (m.queenHint && m.queenHint[mySeat] !== undefined) ? m.queenHint[mySeat] : null,
      settlement: m.phase === 'matchEnd' && m.settlement ? (m.settlement[token] || null) : null
    };
    st.play = {
      trick: m.trick.map(t => ({ seat: t.seat, card: t.card })),
      current: m.current, leader: m.trickLeader,
      lastTrick: m.lastTrick ? { plays: m.lastTrick.plays.map(t => ({ seat: t.seat, card: t.card })), winner: m.lastTrick.winner } : null,
      turnDeadline: m.turnDeadline || 0, timerSec: room.timer || 0
    };
    st.scores = { cum: m.cum.slice(), history: m.history, lastRound: m.lastRound };
    st.matchInfo = { round: m.round, tiebreak: m.round > 7 };
  }
  return st;
}

/* ---------------- HTTP ---------------- */
function send(res, code, obj) { const body = JSON.stringify(obj); res.writeHead(code, { 'Content-Type': 'application/json; charset=utf-8', 'Cache-Control': 'no-store' }); res.end(body); }
function readBody(req) { return new Promise((resolve, reject) => { let d = ''; req.on('data', c => { d += c; if (d.length > 100000) req.destroy(); }); req.on('end', () => { try { resolve(d ? JSON.parse(d) : {}); } catch (e) { resolve({}); } }); req.on('error', reject); }); }

const server = http.createServer(async (req, res) => {
  const url = new URL(req.url, 'http://x');
  const p = url.pathname;
  try {
    if (req.method === 'GET' && (p === '/' || p === '/index.html')) {
      const html = fs.readFileSync(INDEX_FILE);
      res.writeHead(200, { 'Content-Type': 'text/html; charset=utf-8', 'Cache-Control': 'no-store' }); res.end(html); return;
    }
    if (p === '/favicon.ico') { res.writeHead(204); res.end(); return; }
    if (req.method === 'GET' && p === '/api/state') {
      const token = url.searchParams.get('token') || ''; const code = (url.searchParams.get('code') || '').toUpperCase();
      const room = rooms.get(code); const pl = getPlayer(token);
      if (!pl) return send(res, 401, { error: 'اعمل بروفايل الأول' });
      if (!room) return send(res, 404, { error: 'الغرفة مش موجودة' });
      const si = seatIndex(room, token);
      if (si < 0) return send(res, 403, { error: 'انت مش في الغرفة دي' });
      room.seats[si].lastSeen = Date.now();
      if (room.seats[si].botControlled) { room.seats[si].botControlled = false; bump(room); } // reclaim on poll
      return send(res, 200, stateFor(room, token));
    }
    if (req.method !== 'POST' || !p.startsWith('/api/')) { res.writeHead(404); res.end('not found'); return; }
    const b = await readBody(req);
    const token = b.token || '';

    if (p === '/api/profile') {
      let t = token;
      if (!t || !players[t]) { t = crypto.randomBytes(16).toString('hex'); players[t] = { name: '', avatar: '🦊', xp: 0, coins: 0 }; }
      const pl = players[t];
      if (typeof b.name === 'string' && b.name.trim()) pl.name = b.name.trim().slice(0, 24);
      if (typeof b.avatar === 'string' && b.avatar) pl.avatar = b.avatar.slice(0, 8);
      savePlayers();
      return send(res, 200, { ok: true, token: t, profile: { name: pl.name, avatar: pl.avatar, xp: pl.xp, coins: pl.coins, level: levelOf(pl.xp) } });
    }
    const pl = getPlayer(token);
    if (!pl) return send(res, 401, { error: 'اعمل بروفايل الأول' });
    if (!pl.name) return send(res, 400, { error: 'اكتب اسمك الأول' });

    if (p === '/api/create-room') {
      const code = newCode();
      const room = {
        code, hostToken: token, password: (b.password || '').toString().slice(0, 32),
        timer: [0, 10, 15, 20, 30].includes(+b.timer) ? +b.timer : 30,
        fillBots: b.fillBots !== false,
        seats: [makeSeat(), makeSeat(), makeSeat(), makeSeat()],
        match: null, phase: 'lobby', version: 1, updatedAt: Date.now(), emojis: {}
      };
      room.seats[0].token = token; room.seats[0].name = pl.name; room.seats[0].avatar = pl.avatar; room.seats[0].lastSeen = Date.now();
      rooms.set(code, room);
      return send(res, 200, { ok: true, code });
    }
    const code = (b.code || '').toString().toUpperCase();
    const room = rooms.get(code);
    if (!room) return send(res, 404, { error: 'الغرفة مش موجودة — اتأكد من الكود' });

    if (p === '/api/join-room') {
      const existing = seatIndex(room, token);
      if (existing >= 0) { room.seats[existing].lastSeen = Date.now(); return send(res, 200, { ok: true, seat: existing }); }
      if (room.match) return send(res, 400, { error: 'الماتش بدأ خلاص في الغرفة دي' });
      if (room.password && room.password !== (b.password || '')) return send(res, 403, { error: 'كلمة السر غلط' });
      const free = room.seats.findIndex(s => !s.token && !s.bot);
      if (free < 0) return send(res, 400, { error: 'الغرفة مليانة' });
      room.seats[free].token = token; room.seats[free].name = pl.name; room.seats[free].avatar = pl.avatar; room.seats[free].lastSeen = Date.now();
      bump(room);
      return send(res, 200, { ok: true, seat: free });
    }
    const si = seatIndex(room, token);
    if (si < 0) return send(res, 403, { error: 'انت مش في الغرفة دي' });
    room.seats[si].lastSeen = Date.now();

    if (p === '/api/leave-room') {
      if (room.match && room.match.phase !== 'matchEnd') {
        room.seats[si].botControlled = true; // bot finishes the match for him; token kept for reclaim
      } else {
        room.seats[si] = makeSeat();
        if (room.hostToken === token) { const next = room.seats.find(s => s.token); room.hostToken = next ? next.token : token; }
        if (!room.seats.some(s => s.token)) rooms.delete(code);
      }
      bump(room);
      return send(res, 200, { ok: true });
    }
    if (p === '/api/start-match') {
      if (room.hostToken !== token) return send(res, 403, { error: 'صاحب الغرفة بس يقدر يبدأ' });
      if (room.match && room.match.phase !== 'matchEnd') return send(res, 400, { error: 'الماتش شغال' });
      const r = startMatch(room);
      if (r.error) return send(res, 400, { error: r.error });
      return send(res, 200, { ok: true });
    }
    if (p === '/api/pass') {
      const m = room.match; if (!m || m.phase !== 'passing') return send(res, 400, { error: 'مش وقت التبديل' });
      if (m.passCards[si]) return send(res, 400, { error: 'بدّلت خلاص' });
      const cards = Array.isArray(b.cards) ? b.cards : [];
      if (cards.length !== 4 || new Set(cards).size !== 4) return send(res, 400, { error: 'اختار 4 كروت' });
      if (!cards.every(c => m.hands[si].includes(c))) return send(res, 400, { error: 'في كارت مش في إيدك' });
      m.passCards[si] = cards.slice();
      if (m.passCards.every(c => c)) applyPasses(room);
      bump(room);
      return send(res, 200, { ok: true });
    }
    if (p === '/api/play') {
      const r = doPlay(room, si, (b.card || '').toString(), !!b.snap);
      if (r.error) return send(res, 400, { error: r.error });
      return send(res, 200, { ok: true });
    }
    if (p === '/api/emoji') {
      const e = (b.emoji || '').toString().slice(0, 8);
      if (e) { room.emojis[si] = { e, at: Date.now() }; bump(room); }
      return send(res, 200, { ok: true });
    }
    return send(res, 404, { error: 'not found' });
  } catch (err) { console.error(err); return send(res, 500, { error: 'حصلت مشكلة في السيرفر' }); }
});
server.listen(PORT, '0.0.0.0', () => console.log('Heart online server on port ' + PORT));
