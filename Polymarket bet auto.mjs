#!/usr/bin/env node
/**
 * ============================================================
 *  Polymarket Auto-Betting Daemon (Production Grade)
 * ============================================================
 *  Runs continuously, checking Firebase every 10 minutes.
 *  Only processes NEW predictions not yet bet on.
 *
 *  Confidence-based bet sizing:
 *    75-79% -> 10% of available balance
 *    80-84% -> 15% of available balance
 *    >=85%  -> 25% of available balance
 *
 *  Safety & Rules:
 *    - Max 5 bets per cycle
 *    - Max 60% of starting balance per day
 *    - Min reserve of MIN_RESERVE_USDC (default: 0 or env configured)
 *    - Correct orderbook ask parsing: minimum price (best ask) across asks array
 *    - Strict handicap / spreads resolution: matches team on outcomes and line
 *    - Explicit tickSize and negRisk passed to createAndPostOrder
 *    - Running balance update inside cycle to prevent overspending across matches
 *    - Isolated in-memory tracking in DRY_RUN (zero MongoDB pollution)
 *    - Trailing odds peak tracker: monitors odds until peak reverses by >= 0.01
 *    - Mandatory kickoff cutoff: <= 30 mins before match start
 *    - Minimum odds floor (< 1.15): rejected at cutoff unless confidence >= 85%
 *    - Pre-match protection: odds < 1.15 far from match are NOT killed; kept for retries
 *    - In-play protection: matches started > 15 mins ago are skipped
 *    - Proxy rotation via Webshare for bypassing regional IP restrictions
 *    - MongoDB state persistence (polymarket_bot_state collection)
 *
 *  Usage:
 *    node "Polymarket bet auto.mjs"                 <- run daemon (real bets)
 *    node "Polymarket bet auto.mjs" --dry-run       <- run daemon (simulation mode)
 *    node "Polymarket bet auto.mjs" --once          <- run once and exit
 *    node "Polymarket bet auto.mjs" --once --dry-run
 * ============================================================
 */

import 'dotenv/config';
import dns from 'dns';
dns.setServers(['8.8.8.8', '1.1.1.1']);
import { initializeApp, cert } from 'firebase-admin/app';
import { getFirestore } from 'firebase-admin/firestore';
import { MongoClient } from 'mongodb';
import { Wallet, Interface } from 'ethers';
import { readFileSync, writeFileSync, existsSync } from 'fs';
import { join, dirname } from 'path';
import { fileURLToPath } from 'url';
import nodeFetch from 'node-fetch';
import { HttpsProxyAgent } from 'https-proxy-agent';
import axios from 'axios';
import { ClobClient, Side, OrderType, AssetType, SignatureTypeV2 } from '@polymarket/clob-client-v2';

const __dirname = dirname(fileURLToPath(import.meta.url));

// ═══════════════════════════════════════════════
//  CONFIGURATION
// ═══════════════════════════════════════════════
const DRY_RUN = process.argv.includes('--dry-run');
const RUN_ONCE = process.argv.includes('--once');
const CHECK_INTERVAL_MS = 10 * 60 * 1000; // 10 minutes
const MAX_BETS_PER_CYCLE = 5;
const POLYMARKET_CLOB_HOST = 'https://clob.polymarket.com';
const GAMMA_API_BASE = 'https://gamma-api.polymarket.com';
const DATA_API_BASE = 'https://data-api.polymarket.com';
const RELAYER_URL = 'https://relayer-v2.polymarket.com';
const CTF_ADDRESS = '0x4D97DCd97eC945f40cF65F87097ACe5EA0476045';
const USDC_E_ADDRESS = '0x2791Bca1f2de4661ED88A30C99A7a9449Aa84174';
const PUSD_ADDRESS = '0xc011a7e12a19f7b1f670d46f03b03f3342e82dfb'; // Polymarket V2 collateral
const PARENT_COLLECTION_ID = '0x0000000000000000000000000000000000000000000000000000000000000000';
const POLYGON_RPCS = [
    'https://polygon-bor-rpc.publicnode.com',
    'https://polygon.llamarpc.com',
    'https://1rpc.io/matic',
    'https://rpc.ankr.com/polygon'
];
const CHAIN_ID = 137; // Polygon Mainnet
const FETCH_TIMEOUT_MS = 15_000;
const MAX_SEARCH_RETRIES = 72; // 72 cycles x 10 mins = 12 hours coverage
const BET_LOG_FILE = join(__dirname, 'polymarket-bet-history.json');

function cleanEnv(val) {
    if (!val) return '';
    let s = String(val).trim();
    if ((s.startsWith('"') && s.endsWith('"')) || (s.startsWith("'") && s.endsWith("'"))) {
        s = s.slice(1, -1);
    }
    return s.trim();
}

let rawPk = cleanEnv(
    process.env.polymarket_PRIVATE_KEY ||
    process.env.POLYMARKET_PRIVATE_KEY ||
    process.env.PRIVATE_KEY
);
if (rawPk && !rawPk.startsWith('0x')) {
    rawPk = '0x' + rawPk;
}
const WALLET_PRIVATE_KEY = rawPk;

const FUNDER_ADDRESS = cleanEnv(
    process.env.polymarket_Address ||
    process.env.POLYMARKET_ADDRESS ||
    process.env.POLYMARKET_FUNDER_ADDRESS
);

const POLYMARKET_API_KEY = cleanEnv(
    process.env.polymarket_API ||
    process.env.POLYMARKET_API ||
    process.env.POLYMARKET_API_KEY
);

const MIN_RESERVE_USDC = parseFloat(cleanEnv(process.env.MIN_RESERVE_USDC || '0'));

// In-memory sets for DRY RUN to prevent polluting MongoDB bet history
const dryRunBets = new Set();
const dryRunEvents = new Set();

// ═══════════════════════════════════════════════
//  PROXY ROTATION FOR ORDER EXECUTION & GAMMA API
// ═══════════════════════════════════════════════
const DEFAULT_PROXIES = [
    'http://bivwqmnj:6pssg3eaa1rx@64.137.96.74:6641',  // Spain (Madrid) - 🟢 Verified Allowed
    'http://bivwqmnj:6pssg3eaa1rx@84.247.60.125:6095', // Poland (Warsaw) - 🟢 Verified Allowed
];

// Verified allowed countries on Polymarket CLOB (Spain, Poland). Excludes geoblocked US, UK, Germany.
const POLYMARKET_ALLOWED_IPS = ['64.137.96.74', '84.247.60.125'];

let proxiesList = [];
let currentProxyIndex = 0;
let activeProxyAgent = null;

function getProxies() {
    const custom = cleanEnv(process.env.PROXY_URL || process.env.WEBSHARE_PROXY);
    if (custom) return [custom];
    const file = join(__dirname, 'Webshare 10 proxies.txt');
    if (existsSync(file)) {
        try {
            const lines = readFileSync(file, 'utf-8').split('\n').map(l => l.trim()).filter(Boolean);
            const parsed = lines.map(line => {
                const parts = line.split(':');
                if (parts.length === 4) {
                    const [ip, port, user, pass] = parts;
                    return `http://${user}:${pass}@${ip}:${port}`;
                }
                return line.startsWith('http') ? line : `http://${line}`;
            });
            // Strictly filter for Polymarket-compliant jurisdictions only
            const compliant = parsed.filter(p => POLYMARKET_ALLOWED_IPS.some(ip => p.includes(ip)));
            if (compliant.length) return compliant;
        } catch { }
    }
    return DEFAULT_PROXIES;
}

function initProxies() {
    proxiesList = getProxies();
    currentProxyIndex = 0;
    applyProxy(proxiesList[0]);
}

function applyProxy(proxyUrl) {
    activeProxyAgent = new HttpsProxyAgent(proxyUrl);
    axios.defaults.httpsAgent = activeProxyAgent;
    axios.defaults.httpAgent = activeProxyAgent;
}

function rotateProxy() {
    if (!proxiesList.length) proxiesList = getProxies();
    currentProxyIndex = (currentProxyIndex + 1) % proxiesList.length;
    const nextProxy = proxiesList[currentProxyIndex];
    const host = nextProxy.split('@')[1] || nextProxy;
    log('🔄', `Rotating proxy -> #${currentProxyIndex + 1} (${host})`);
    applyProxy(nextProxy);
    return activeProxyAgent;
}

// ═══════════════════════════════════════════════
//  LOGGER
// ═══════════════════════════════════════════════
function log(emoji, ...args) {
    const time = new Date().toLocaleTimeString('en-US', { hour12: false });
    console.log(`[${time}] ${emoji}`, ...args);
}

// ═══════════════════════════════════════════════
//  MONGODB (Polymarket State Persistence)
// ═══════════════════════════════════════════════
let mongoCol = null;

async function initMongo() {
    if (mongoCol) return mongoCol;
    const uri = cleanEnv(process.env.MONGODB_URI);
    if (!uri) throw new Error('Missing MONGODB_URI in .env');
    const client = new MongoClient(uri);
    await client.connect();
    const db = client.db('water_football');
    mongoCol = db.collection('polymarket_bot_state');

    try {
        const existing = await mongoCol.findOne({ _id: 'polymarket_state' });
        if (!existing && existsSync(BET_LOG_FILE)) {
            const data = JSON.parse(readFileSync(BET_LOG_FILE, 'utf-8'));
            await mongoCol.updateOne(
                { _id: 'polymarket_state' },
                {
                    $set: {
                        bets: data.bets || [],
                        dailySpend: data.dailySpend || {},
                        searchRetries: data.searchRetries || {},
                        oddsTracker: data.oddsTracker || {},
                        events: data.events || [],
                        lastCleanup: data.lastCleanup || '',
                        migratedAt: new Date()
                    }
                },
                { upsert: true }
            );
            log('📦', 'Migrated polymarket-bet-history.json to MongoDB successfully!');
        }
    } catch (e) {
        log('⚠️', `Mongo init check: ${e.message}`);
    }
    return mongoCol;
}

async function loadBetHistory(col) {
    try {
        if (col) {
            const doc = await col.findOne({ _id: 'polymarket_state' });
            if (doc) {
                return {
                    bets: doc.bets || [],
                    dailySpend: doc.dailySpend || {},
                    searchRetries: doc.searchRetries || {},
                    oddsTracker: doc.oddsTracker || {},
                    events: doc.events || [],
                    lastCleanup: doc.lastCleanup || '',
                };
            }
        }
    } catch (e) {
        log('⚠️', `Failed to load state from Mongo: ${e.message}`);
    }

    if (existsSync(BET_LOG_FILE)) {
        try {
            return JSON.parse(readFileSync(BET_LOG_FILE, 'utf-8'));
        } catch { }
    }
    return { bets: [], dailySpend: {}, searchRetries: {}, oddsTracker: {}, events: [], lastCleanup: '' };
}

async function saveBetHistory(col, history) {
    if (DRY_RUN) return; // Do not persist simulated bets in Dry Run

    try {
        writeFileSync(BET_LOG_FILE, JSON.stringify(history, null, 2));
    } catch (e) {
        log('⚠️', `Failed to save local history file: ${e.message}`);
    }

    try {
        if (col) {
            await col.updateOne(
                { _id: 'polymarket_state' },
                {
                    $set: {
                        bets: history.bets,
                        dailySpend: history.dailySpend,
                        searchRetries: history.searchRetries,
                        oddsTracker: history.oddsTracker,
                        events: history.events || [],
                        lastCleanup: history.lastCleanup,
                        updatedAt: new Date()
                    }
                },
                { upsert: true }
            );
        }
    } catch (e) {
        log('⚠️', `Failed to save state to MongoDB: ${e.message}`);
    }
}

function wasBetPlaced(history, key) {
    if (DRY_RUN && dryRunBets.has(key)) return true;
    return history.bets.includes(key);
}

function getBetKey(today, matchIndex, prediction) {
    return `${today}_${matchIndex}_${prediction}`;
}

async function recordBet(col, history, key, amount, eventId = null) {
    if (DRY_RUN) {
        if (key) dryRunBets.add(key);
        if (eventId) dryRunEvents.add(eventId);
        log('📝', `[DRY RUN] In-memory record: ${key} ($${amount.toFixed(2)}) -- not saved to DB`);
        return;
    }

    if (key && !history.bets.includes(key)) {
        history.bets.push(key);
    }
    if (!history.events) history.events = [];
    if (eventId && !history.events.includes(eventId)) {
        history.events.push(eventId);
        log('📌', `Recorded Polymarket Event ID ${eventId} to prevent duplicate bets`);
    }
    const today = new Date().toISOString().split('T')[0];
    history.dailySpend[today] = (history.dailySpend[today] || 0) + amount;

    // Cleanup old entries (keep last 7 days)
    if (history.lastCleanup !== today) {
        const cutoff = new Date();
        cutoff.setDate(cutoff.getDate() - 7);
        const cutoffStr = cutoff.toISOString().split('T')[0];
        history.bets = history.bets.filter(b => b >= cutoffStr);
        for (const d of Object.keys(history.dailySpend)) {
            if (d < cutoffStr) delete history.dailySpend[d];
        }
        if (history.events.length > 200) {
            history.events = history.events.slice(-100);
        }
        history.lastCleanup = today;
    }
    await saveBetHistory(col, history);
}

function getDailySpend(history) {
    const today = new Date().toISOString().split('T')[0];
    return history.dailySpend[today] || 0;
}

// ═══════════════════════════════════════════════
//  FIREBASE PREDICTIONS
// ═══════════════════════════════════════════════
let firebaseInitialized = false;

function initFirebase() {
    if (firebaseInitialized) return getFirestore();
    let raw = cleanEnv(process.env.FIREBASE_SERVICE_ACCOUNT);
    const sa = JSON.parse(raw);
    sa.private_key = sa.private_key.replace(/\\n/g, '\n');
    initializeApp({ credential: cert(sa) });
    firebaseInitialized = true;
    return getFirestore();
}

async function fetchTodayPredictions(db) {
    const today = new Date().toISOString().split('T')[0];
    log('📅', `Checking predictions for: ${today}`);

    const snap = await db.collection('ai_best_predictions')
        .where('apiDate', '==', today)
        .get();

    if (snap.empty) {
        log('💤', 'No predictions for today');
        return { today, preds: [] };
    }

    const preds = [];
    snap.forEach(doc => {
        const d = doc.data();
        if (Array.isArray(d.allAnalyses)) {
            for (const a of d.allAnalyses) preds.push(a);
        }
    });

    const deduped = new Map();
    for (const p of preds) {
        const lines = p.match.split('\n');
        const matchKey = lines[0].trim();
        const conf = extractConfidence(p.analysis);
        const existing = deduped.get(matchKey);
        if (!existing || conf > existing.conf) {
            deduped.set(matchKey, { pred: p, conf });
        }
    }
    const uniquePreds = [...deduped.values()].map(v => v.pred);
    log('📊', `Found ${preds.length} total predictions (${uniquePreds.length} unique matches)`);
    return { today, preds: uniquePreds };
}

// ═══════════════════════════════════════════════
//  PREDICTION PARSING & CLASSIFICATION
// ═══════════════════════════════════════════════
function extractConfidence(analysis) {
    if (!analysis) return 0;
    const matches = [...analysis.matchAll(/\[(\d+)%\]/g)];
    if (!matches.length) return 0;
    return parseInt(matches[matches.length - 1][1]);
}

function parsePrediction(pred) {
    const lines = pred.match.split('\n');
    const [team1, team2] = lines[0].split(' vs ').map(s => s.trim());
    const league = (lines.find(l => l.startsWith('League:')) || '').replace('League:', '').trim();
    const predLine = (lines.find(l => l.startsWith('Prediction:')) || '').replace('Prediction:', '').trim();
    const parts = predLine.split('|').map(s => s.trim());
    const prediction = parts[0] || '';
    const odds = parseFloat((parts[1] || '').replace('Odds:', '').trim()) || 0;
    const confidence = extractConfidence(pred.analysis) || parseInt(pred.successRate || 0) || 0;

    return { matchIndex: pred.matchIndex, team1, team2, league, prediction, odds, confidence };
}

function classifyPrediction(prediction) {
    const p = prediction.trim();

    // Handicap: "Telekom -4.5 Wins" or "Barcelona +2.5 Win"
    const handicapRe = /^(.+?)\s+([+-]\d+\.?\d*)\s+Wins?$/i;
    const hm = p.match(handicapRe);
    if (hm) return { type: 'handicap', team: hm[1].trim(), line: parseFloat(hm[2]) };

    // Double Chance: "Ferencvaros Wins Or Draw" -> 1X
    const dcRe = /^(.+?)\s+(?:Wins?\s+Or\s+Draw|Draw\s+Or\s+Wins?)$/i;
    const dc = p.match(dcRe);
    if (dc) return { type: 'double_chance', team: dc[1].trim() };

    // Straight Win / Moneyline: "Barcelona Wins" or "Barcelona Win"
    const mlRe = /^(.+?)\s+Wins?$/i;
    const ml = p.match(mlRe);
    if (ml) return { type: 'moneyline', team: ml[1].trim() };

    // Totals: "Over 2.5 Goals" or "Under 2.5 Goals"
    const totalRe = /^(Over|Under) (\d+\.?\d*)\s*(?:Goals?|Points?)?$/i;
    const tm = p.match(totalRe);
    if (tm) return { type: 'over_under', line: parseFloat(tm[2]), side: tm[1].toLowerCase() };

    // Both Teams To Score (Polymarket supports both Yes and No!)
    if (/(?:both\s*teams?\s*(?:to\s*)?score|btts)/i.test(p)) {
        if (/\bno\b/i.test(p)) {
            return { type: 'btts_no' };
        }
        if (/\byes\b/i.test(p)) {
            return { type: 'btts_yes' };
        }
        return { type: 'btts_yes' };
    }

    // Team Totals: "Leverkusen Over 1.5 Goals"
    const teamOURe = /^(.+?)\s+(Over|Under)\s+(\d+\.?\d*)\s*Goals?$/i;
    const to = p.match(teamOURe);
    if (to) return { type: 'team_over', team: to[1].trim(), side: to[2].toLowerCase(), line: parseFloat(to[3]) };

    return { type: 'unknown', raw: p };
}

// ═══════════════════════════════════════════════
//  SAFE FUZZY TEAM MATCHING & GENDER FILTERS
// ═══════════════════════════════════════════════
const GENERIC_WORDS = new Set([
    'fc', 'cf', 'sc', 'bc', 'fk', 'sk', 'as', 'ac', 'cd', 'cs', 'cp', 'clube', 'club', 'de',
    'city', 'town', 'united', 'utd', 'athletic', 'atlético', 'atletico', 'inter', 'real',
    'sporting', 'racing', 'dynamo', 'dinamo', 'lokomotiv', 'lokomotiva', 'red', 'star',
    'rovers', 'wanderers', 'albion', 'hotspur', 'borussia', 'olympiacos', 'panathinaikos',
    'telekom', 'baskets', 'ratiopharm'
]);

function normalise(str) {
    return (str || '')
        .toLowerCase()
        .normalize('NFD').replace(/[\u0300-\u036f]/g, '')
        .replace(/[^a-z0-9\s]/g, ' ')
        .replace(/\s+/g, ' ')
        .trim();
}

function extractCategory(name) {
    const raw = (name || '').toLowerCase();
    const categories = [];
    if (/\b(women|woman|femme|femenino|femminile|damer|damen|w)\b/i.test(raw)) categories.push('women');
    if (/\b(u17|u18|u19|u20|u21|u23|youth|academy|sub\s*\d+|under\s*\d+)\b/i.test(raw)) categories.push('youth');
    if (/\b(b\s+team|ii|reserves?)\b/i.test(raw)) categories.push('b_team');
    return categories.sort().join('_') || 'standard';
}

function getSignificantWords(name) {
    const norm = normalise(name);
    return norm.split(' ').filter(w => w.length >= 3 && !GENERIC_WORDS.has(w));
}

function teamsMatch(nameA, nameB) {
    if (!nameA || !nameB) return false;

    // Strict gender & youth category match
    const catA = extractCategory(nameA);
    const catB = extractCategory(nameB);
    if (catA !== catB) return false;

    const normA = normalise(nameA);
    const normB = normalise(nameB);
    if (normA === normB) return true;

    const sigA = getSignificantWords(nameA);
    const sigB = getSignificantWords(nameB);

    if (sigA.length === 0 || sigB.length === 0) {
        return normA.includes(normB) || normB.includes(normA);
    }

    for (const wa of sigA) {
        for (const wb of sigB) {
            if (wa === wb) return true;
            if (wa.length >= 4 && wb.length >= 4 && (wa.includes(wb) || wb.includes(wa))) {
                return true;
            }
        }
    }
    return false;
}

// ═══════════════════════════════════════════════
//  GAMMA API CLIENT (Search & Markets)
// ═══════════════════════════════════════════════
async function gammaGet(endpoint, params = {}, retries = 2) {
    const url = new URL(endpoint, GAMMA_API_BASE);
    for (const [k, v] of Object.entries(params)) {
        if (v != null) url.searchParams.set(k, String(v));
    }

    for (let attempt = 0; attempt <= retries; attempt++) {
        try {
            const controller = new AbortController();
            const timer = setTimeout(() => controller.abort(), FETCH_TIMEOUT_MS);
            const res = await nodeFetch(url.toString(), {
                agent: activeProxyAgent,
                signal: controller.signal,
                headers: { 'Accept': 'application/json' },
            }).finally(() => clearTimeout(timer));

            if (!res.ok) {
                const text = await res.text();
                throw new Error(`Gamma GET ${endpoint} -> ${res.status}: ${text}`);
            }
            return await res.json();
        } catch (e) {
            if (attempt < retries) {
                log('🔄', `Gamma request retry (${attempt + 1}/${retries}) for ${endpoint}: ${e.message}`);
                rotateProxy();
                await new Promise(r => setTimeout(r, 1500));
            } else {
                throw e;
            }
        }
    }
}

// ═══════════════════════════════════════════════
//  DATA API CLIENT (Positions & Valuations)
// ═══════════════════════════════════════════════
async function dataApiGet(endpoint, params = {}, retries = 2) {
    const url = new URL(endpoint, DATA_API_BASE);
    for (const [k, v] of Object.entries(params)) {
        if (v != null) url.searchParams.set(k, String(v));
    }

    for (let attempt = 0; attempt <= retries; attempt++) {
        try {
            const controller = new AbortController();
            const timer = setTimeout(() => controller.abort(), FETCH_TIMEOUT_MS);
            const res = await nodeFetch(url.toString(), {
                agent: activeProxyAgent,
                signal: controller.signal,
                headers: { 'Accept': 'application/json' },
            }).finally(() => clearTimeout(timer));

            if (!res.ok) {
                const text = await res.text();
                throw new Error(`Data API GET ${endpoint} -> ${res.status}: ${text}`);
            }
            return await res.json();
        } catch (e) {
            if (attempt < retries) {
                log('🔄', `Data API retry (${attempt + 1}/${retries}) for ${endpoint}: ${e.message}`);
                rotateProxy();
                await new Promise(r => setTimeout(r, 1500));
            } else {
                throw e;
            }
        }
    }
}

async function searchFixture(team1, team2) {
    const terms = new Set();
    if (team1.length >= 3) terms.add(team1);
    if (team2.length >= 3) terms.add(team2);

    for (const w of getSignificantWords(team1)) terms.add(w);
    for (const w of getSignificantWords(team2)) terms.add(w);

    for (const q of terms) {
        try {
            log('🔍', `Searching Polymarket for: "${q}"`);
            const res = await gammaGet('/public-search', { q });
            const events = res.events || [];
            if (!events.length) continue;

            for (const ev of events) {
                if (ev.closed) continue;

                let t1Found = false;
                let t2Found = false;

                if (Array.isArray(ev.teams) && ev.teams.length >= 2) {
                    const home = ev.teams[0]?.name || '';
                    const away = ev.teams[1]?.name || '';
                    t1Found = teamsMatch(home, team1) || teamsMatch(away, team1);
                    t2Found = teamsMatch(home, team2) || teamsMatch(away, team2);
                }

                if (!t1Found || !t2Found) {
                    const parts = (ev.title || '').split(/\s+vs\.?\s+/i);
                    if (parts.length >= 2) {
                        const m1 = teamsMatch(parts[0], team1) && teamsMatch(parts[1], team2);
                        const m2 = teamsMatch(parts[0], team2) && teamsMatch(parts[1], team1);
                        if (m1 || m2) {
                            t1Found = true;
                            t2Found = true;
                        }
                    }
                }

                if (t1Found && t2Found) {
                    log('✅', `Polymarket event found: "${ev.title}" (slug: ${ev.slug})`);
                    return ev;
                }
            }
        } catch (e) {
            log('⚠️', `Search error for "${q}": ${e.message}`);
        }
    }
    return null;
}

async function getEventMarkets(event, neededType) {
    let markets = Array.isArray(event.markets) ? [...event.markets] : [];
    const hasMoreMarketsType = ['over_under', 'team_over', 'btts_yes', 'btts_no', 'handicap'].includes(neededType);

    if (hasMoreMarketsType) {
        const hasTotals = markets.some(m => m.sportsMarketType === 'totals');
        const hasBTTS = markets.some(m => m.sportsMarketType === 'both_teams_to_score');
        const hasSpreads = markets.some(m => m.sportsMarketType === 'spreads');

        const needsExtra = (neededType === 'over_under' && !hasTotals) ||
            ((neededType === 'btts_yes' || neededType === 'btts_no') && !hasBTTS) ||
            (neededType === 'handicap' && !hasSpreads);

        if (needsExtra && event.slug) {
            try {
                const moreSlug = event.slug.endsWith('-more-markets') ? event.slug : `${event.slug}-more-markets`;
                log('🔍', `Fetching additional markets from slug: ${moreSlug}`);
                const extraEvents = await gammaGet('/events', { slug: moreSlug });
                if (extraEvents && extraEvents[0]?.markets?.length) {
                    markets = markets.concat(extraEvents[0].markets);
                    log('✅', `Added ${extraEvents[0].markets.length} additional markets`);
                }
            } catch { }
        }
    }
    return markets;
}

// ═══════════════════════════════════════════════
//  MARKET & TOKEN RESOLUTION
// ═══════════════════════════════════════════════
function parseJsonArray(str) {
    if (!str) return [];
    if (Array.isArray(str)) return str;
    try {
        return JSON.parse(str);
    } catch {
        return [];
    }
}

async function findMarketAndOutcome(event, classification, team1, team2) {
    const markets = await getEventMarkets(event, classification.type);
    if (!markets.length) {
        log('⚠️', 'No markets available for this event');
        return null;
    }

    switch (classification.type) {
        case 'moneyline': {
            const targetTeam = classification.team;
            // 1) Check 3-way moneyline market (common in soccer)
            for (const m of markets) {
                if (m.sportsMarketType === 'moneyline' && m.groupItemTitle) {
                    if (teamsMatch(m.groupItemTitle, targetTeam)) {
                        const tokenIds = parseJsonArray(m.clobTokenIds);
                        const outcomes = parseJsonArray(m.outcomes);
                        const yesIndex = outcomes.findIndex(o => o.toLowerCase() === 'yes');
                        const idx = yesIndex !== -1 ? yesIndex : 0;
                        return {
                            market: m,
                            tokenID: tokenIds[idx],
                            outcomeName: `${m.groupItemTitle} (Yes)`,
                            outcomeIndex: idx
                        };
                    }
                }
            }
            // 2) Check 2-way moneyline market (common in basketball, tennis)
            for (const m of markets) {
                if (m.sportsMarketType === 'moneyline' || !m.sportsMarketType) {
                    const outcomes = parseJsonArray(m.outcomes);
                    const tokenIds = parseJsonArray(m.clobTokenIds);
                    for (let i = 0; i < outcomes.length; i++) {
                        if (teamsMatch(outcomes[i], targetTeam)) {
                            return {
                                market: m,
                                tokenID: tokenIds[i],
                                outcomeName: outcomes[i],
                                outcomeIndex: i
                            };
                        }
                    }
                }
            }
            log('⚠️', `Could not find moneyline market for team "${targetTeam}"`);
            return null;
        }

        case 'double_chance': {
            // "Team1 Wins Or Draw" -> In 3-way soccer, bet "No" on opponent win!
            const myTeam = classification.team;
            const oppTeam = teamsMatch(team1, myTeam) ? team2 : team1;

            for (const m of markets) {
                if (m.sportsMarketType === 'moneyline' && m.groupItemTitle) {
                    if (teamsMatch(m.groupItemTitle, oppTeam)) {
                        const tokenIds = parseJsonArray(m.clobTokenIds);
                        const outcomes = parseJsonArray(m.outcomes);
                        const noIndex = outcomes.findIndex(o => o.toLowerCase() === 'no');
                        const idx = noIndex !== -1 ? noIndex : 1;
                        return {
                            market: m,
                            tokenID: tokenIds[idx],
                            outcomeName: `${myTeam} Win or Draw (No on ${m.groupItemTitle})`,
                            outcomeIndex: idx
                        };
                    }
                }
            }
            log('⚠️', `Could not find opponent market for Double Chance against "${oppTeam}"`);
            return null;
        }

        case 'over_under':
        case 'team_over': {
            const targetLine = classification.line;
            const wantOver = classification.side === 'over';

            for (const m of markets) {
                if (m.sportsMarketType === 'totals') {
                    const marketLine = parseFloat(m.line || m.groupItemThreshold || 0);
                    const questionHasLine = (m.question || '').includes(String(targetLine));
                    const groupHasLine = (m.groupItemTitle || '').includes(String(targetLine));

                    if (marketLine === targetLine || questionHasLine || groupHasLine) {
                        const tokenIds = parseJsonArray(m.clobTokenIds);
                        const outcomes = parseJsonArray(m.outcomes);
                        const targetWord = wantOver ? 'over' : 'under';
                        let idx = outcomes.findIndex(o => o.toLowerCase().includes(targetWord));
                        if (idx === -1) idx = wantOver ? 0 : 1;

                        return {
                            market: m,
                            tokenID: tokenIds[idx],
                            outcomeName: `${wantOver ? 'Over' : 'Under'} ${targetLine}`,
                            outcomeIndex: idx
                        };
                    }
                }
            }
            log('⚠️', `Exact line ${targetLine} totals market not found`);
            return null;
        }

        case 'btts_yes':
        case 'btts_no': {
            const wantYes = classification.type === 'btts_yes';
            for (const m of markets) {
                if (m.sportsMarketType === 'both_teams_to_score' || /both teams to score/i.test(m.question || '')) {
                    const tokenIds = parseJsonArray(m.clobTokenIds);
                    const outcomes = parseJsonArray(m.outcomes);
                    const targetWord = wantYes ? 'yes' : 'no';
                    let idx = outcomes.findIndex(o => o.toLowerCase() === targetWord);
                    if (idx === -1) idx = wantYes ? 0 : 1;

                    return {
                        market: m,
                        tokenID: tokenIds[idx],
                        outcomeName: `BTTS ${wantYes ? 'Yes' : 'No'}`,
                        outcomeIndex: idx
                    };
                }
            }
            log('⚠️', 'Both Teams to Score market not found');
            return null;
        }

        case 'handicap': {
            const targetTeam = classification.team;
            const targetLine = classification.line;
            const signStr = targetLine > 0 ? `+${targetLine}` : `${targetLine}`;

            for (const m of markets) {
                if (m.sportsMarketType === 'spreads') {
                    const outcomes = parseJsonArray(m.outcomes);
                    const tokenIds = parseJsonArray(m.clobTokenIds);
                    const marketLine = parseFloat(m.line || 0);
                    const q = `${m.question || ''} ${m.groupItemTitle || ''}`;

                    // Check if market line matches target line
                    const lineMatches = Math.abs(marketLine - targetLine) < 0.01 ||
                        q.includes(signStr) ||
                        q.includes(String(targetLine));

                    if (lineMatches) {
                        for (let i = 0; i < outcomes.length; i++) {
                            if (teamsMatch(outcomes[i], targetTeam)) {
                                return {
                                    market: m,
                                    tokenID: tokenIds[i],
                                    outcomeName: `${outcomes[i]} (${signStr})`,
                                    outcomeIndex: i
                                };
                            }
                        }
                    }
                }
            }
            log('⚠️', `Spread line ${targetLine} for team "${targetTeam}" not found`);
            return null;
        }

        default:
            return null;
    }
}

// ═══════════════════════════════════════════════
//  POLYMARKET CLOB CLIENT & RELAY SERVICES
// ═══════════════════════════════════════════════
let clobClientInstance = null;
let relayClientInstance = null;
let viemWalletClient = null;

async function initRelayClient(privateKey) {
    if (relayClientInstance) return { relayClient: relayClientInstance, walletClient: viemWalletClient };
    try {
        const { createWalletClient, http } = await import('viem');
        const { privateKeyToAccount } = await import('viem/accounts');
        const { polygon } = await import('viem/chains');
        const { RelayClient, RelayerTxType } = await import('@polymarket/builder-relayer-client');

        const account = privateKeyToAccount(privateKey);
        viemWalletClient = createWalletClient({
            account,
            chain: polygon,
            transport: http(POLYGON_RPCS[0])
        });

        log('⚡', 'Initializing Polymarket Relayer client (gasless claims)...');
        relayClientInstance = new RelayClient(RELAYER_URL, CHAIN_ID, viemWalletClient, undefined, RelayerTxType.PROXY);
        return { relayClient: relayClientInstance, walletClient: viemWalletClient };
    } catch (e) {
        log('ℹ️', `Relayer/Viem dynamic check (${e.message}) -- install viem & @polymarket/builder-relayer-client for gasless claims.`);
        return { relayClient: null, walletClient: null };
    }
}

async function resolveFunderAndType(walletAddress, relayClient) {
    if (FUNDER_ADDRESS && FUNDER_ADDRESS.toLowerCase() !== walletAddress.toLowerCase()) {
        log('👤', `Using configured funder address: ${FUNDER_ADDRESS}`);
        return { funder: FUNDER_ADDRESS, isDepositWallet: true };
    }

    // 1) Try Polymarket profile API
    try {
        const res = await nodeFetch(`https://polymarket.com/api/profile/userData?address=${walletAddress}`, {
            agent: activeProxyAgent,
            headers: { 'Accept': 'application/json' },
            timeout: 8000
        });
        if (res.ok) {
            const data = await res.json();
            if (data?.proxyWallet) {
                log('🎯', `Detected Polymarket proxy wallet from profile: ${data.proxyWallet} (${data.name || 'User'})`);
                return { funder: data.proxyWallet, isDepositWallet: true };
            }
        }
    } catch { }

    // 2) Derive deposit wallet via relayClient
    if (relayClient) {
        try {
            const derived = await relayClient.deriveDepositWalletAddress(walletAddress);
            if (derived) {
                const isDeployed = await relayClient.isContractDeployed(derived);
                if (isDeployed) {
                    log('🎯', `Detected deployed Polymarket deposit wallet: ${derived}`);
                    return { funder: derived, isDepositWallet: true };
                }
            }
        } catch { }
    }

    log('ℹ️', `Operating with direct EOA: ${walletAddress}`);
    return { funder: walletAddress, isDepositWallet: false };
}

// ═══════════════════════════════════════════════
//  AUTO-CLAIM & REDEMPTIONS (Gasless / CTF)
// ═══════════════════════════════════════════════
async function checkAndRedeemPositions(funder, walletClient, clobClient, relayClient, isDepositWallet) {
    try {
        log('🔍', `Checking for redeemable (Claim) positions for ${funder}...`);
        const res = await dataApiGet('/v2/positions', { user: funder, status: 'REDEEMABLE' });
        const redeemable = (res && Array.isArray(res.data)) ? res.data : [];

        if (!redeemable.length) {
            log('✨', 'No redeemable positions waiting to be claimed.');
            return 0;
        }

        log('🎁', `Found ${redeemable.length} winning position(s) ready to CLAIM!`);
        if (!relayClient) {
            log('ℹ️', `Automated Claim relayer not loaded -- skipping on-chain auto-redemption for ${redeemable.length} positions.`);
            return 0;
        }
        let claimedCount = 0;

        for (const pos of redeemable) {
            const title = pos.title || pos.slug || 'Unknown Market';
            const value = pos.current_value || 0;
            const condId = pos.condition_id;

            log('⚡', `Executing automated Claim for "${title}" (~$${value.toFixed(2)} USDC)...`);

            if (DRY_RUN) {
                log('🧪', `[DRY RUN] Would submit redemption for condition ${condId} via Relayer`);
                claimedCount++;
                continue;
            }

            try {
                const ctfInterface = new Interface([
                    'function redeemPositions(address collateralToken, bytes32 parentCollectionId, bytes32 conditionId, uint256[] indexSets)'
                ]);
                const data = ctfInterface.encodeFunctionData('redeemPositions', [
                    PUSD_ADDRESS,
                    PARENT_COLLECTION_ID,
                    condId,
                    [1, 2]
                ]);

                if (isDepositWallet) {
                    const call = {
                        target: CTF_ADDRESS,
                        value: '0',
                        data
                    };
                    const txRes = await relayClient.executeDepositWalletBatch([call], funder);
                    log('⏳', `Redemption submitted via Relayer (TxID: ${txRes.transactionID}) -- waiting for confirmation...`);
                    const receipt = await txRes.wait();
                    log('🎉', `Redemption confirmed! TxHash: ${receipt?.transactionHash || txRes.transactionHash}`);
                } else {
                    const tx = {
                        to: CTF_ADDRESS,
                        data,
                        value: '0'
                    };
                    const txRes = await relayClient.execute([tx], funder);
                    const receipt = await txRes.wait();
                    log('🎉', `Redemption confirmed! TxHash: ${receipt?.transactionHash || txRes.transactionHash}`);
                }

                claimedCount++;
            } catch (err) {
                log('❌', `Failed to redeem position for ${title}: ${err.message}`);
            }
        }

        if (claimedCount > 0 && clobClient) {
            try {
                await clobClient.updateBalanceAllowance({ asset_type: AssetType.COLLATERAL });
                log('🔄', 'CLOB balance allowance updated successfully after redemptions.');
            } catch (e) {
                log('⚠️', `Failed to update CLOB balance after redemption: ${e.message}`);
            }
        }

        return claimedCount;
    } catch (e) {
        log('⚠️', `Error in checkAndRedeemPositions: ${e.message}`);
        return 0;
    }
}

async function getPendingClaimsStatus(funder) {
    try {
        const res = await dataApiGet('/v2/positions', { user: funder });
        const positions = (res && Array.isArray(res.data)) ? res.data : [];

        let totalPendingValue = 0;
        const pendingPositions = [];

        for (const pos of positions) {
            // 1) Explicitly marked redeemable by Polymarket
            if (pos.redeemable || pos.status === 'REDEEMABLE') {
                totalPendingValue += (pos.current_value || 0);
                pendingPositions.push({ ...pos, reason: 'Ready for Claim' });
            }
            // 2) Won market waiting for oracle settlement (price ~ 100¢ / >= 0.95)
            else if (pos.status === 'OPEN' && ((pos.current_price || pos.cur_price || 0) >= 0.95)) {
                totalPendingValue += (pos.current_value || 0);
                pendingPositions.push({ ...pos, reason: 'Won match waiting for Claim resolution' });
            }
        }

        return {
            hasPending: pendingPositions.length > 0,
            count: pendingPositions.length,
            totalPendingValue,
            pendingPositions
        };
    } catch (e) {
        return { hasPending: false, count: 0, totalPendingValue: 0, pendingPositions: [] };
    }
}

async function initClobClient(wallet, resolvedFunder = null) {
    if (clobClientInstance) return clobClientInstance;

    // Ethers v6 compatibility shim for Polymarket SDK
    wallet._signTypedData = (domain, types, value) => {
        delete types.EIP712Domain;
        return wallet.signTypedData(domain, types, value);
    };

    const funder = resolvedFunder || FUNDER_ADDRESS || wallet.address;
    const isProxy = funder.toLowerCase() !== wallet.address.toLowerCase();
    const sigType = isProxy ? SignatureTypeV2.POLY_1271 : SignatureTypeV2.EOA;

    log('🔐', `Initializing Polymarket CLOB client (Signer: ${wallet.address}, Funder: ${funder}, SigType: ${sigType})...`);
    const initClient = new ClobClient({
        host: POLYMARKET_CLOB_HOST,
        chain: CHAIN_ID,
        signer: wallet,
        signatureType: sigType,
        funderAddress: funder
    });

    let creds;
    try {
        creds = await initClient.createOrDeriveApiKey();
        log('🔑', 'Derived Polymarket L2 API credentials successfully');
    } catch (e) {
        log('⚠️', `Failed to derive API key: ${e.message}`);
        throw e;
    }

    clobClientInstance = new ClobClient({
        host: POLYMARKET_CLOB_HOST,
        chain: CHAIN_ID,
        signer: wallet,
        creds,
        signatureType: sigType,
        funderAddress: funder
    });

    // Refresh CLOB internal allowance cache from Polygon
    try {
        await clobClientInstance.updateBalanceAllowance({ asset_type: AssetType.COLLATERAL });
    } catch { }

    return clobClientInstance;
}

async function getOrderbookTop(client, tokenID) {
    try {
        const book = await client.getOrderBook(tokenID);
        if (!book || !Array.isArray(book.asks) || book.asks.length === 0) {
            return null;
        }

        // Bug 1 Fix: book.asks is NOT guaranteed ascending! Find the MINIMUM price (best ask for buyer)
        const validAsks = book.asks.filter(a => {
            const p = parseFloat(a.price);
            const s = parseFloat(a.size);
            return !isNaN(p) && !isNaN(s) && p > 0 && p < 1 && s > 0;
        });

        if (!validAsks.length) return null;

        const bestAsk = validAsks.reduce((min, cur) =>
            parseFloat(cur.price) < parseFloat(min.price) ? cur : min
        );

        const price = parseFloat(bestAsk.price);
        const decimalOdds = 1.0 / price;
        const availableShares = parseFloat(bestAsk.size);
        const availableUsdc = price * availableShares;
        const minOrderSize = parseFloat(book.min_order_size || 5);
        const tickSize = book.tick_size || '0.001';
        const negRisk = book.neg_risk ?? false;

        return {
            price,
            decimalOdds,
            availableShares,
            availableUsdc,
            minOrderSize,
            tickSize,
            negRisk,
        };
    } catch (e) {
        log('⚠️', `Orderbook snapshot error: ${e.message}`);
        return null;
    }
}

// ═══════════════════════════════════════════════
//  SINGLE CYCLE
// ═══════════════════════════════════════════════
async function runCycle(db, wallet, col, client, relayClient, funder, isDepositWallet, walletClient) {
    // 1) First: Run automated Claim / Redemption for any won positions ready to claim!
    await checkAndRedeemPositions(funder, walletClient, client, relayClient, isDepositWallet);

    const history = await loadBetHistory(col);
    const { today, preds } = await fetchTodayPredictions(db);
    if (!preds.length) return;

    const newPreds = preds.filter(raw => {
        const p = parsePrediction(raw);
        const key = getBetKey(today, p.matchIndex, p.prediction);
        return !wasBetPlaced(history, key);
    });

    if (!newPreds.length) {
        log('💤', 'No new predictions to process');
        return;
    }

    log('🆕', `${newPreds.length} new predictions (${preds.length - newPreds.length} already processed)`);

    // Check Polymarket balance (CLOB v2 with POLY_1271 reads pUSD correctly)
    let currentBalance = 0;
    try {
        const balRes = await client.getBalanceAllowance({ asset_type: AssetType.COLLATERAL });
        currentBalance = Number(BigInt(balRes.balance || 0)) / 1e6;
    } catch (e) {
        log('⚠️', `Error fetching balance: ${e.message}`);
        if (DRY_RUN) currentBalance = 100.0; // Simulated balance for dry run
    }

    log('💰', `Polymarket USDC balance: $${currentBalance.toFixed(2)} (Min Reserve: $${MIN_RESERVE_USDC.toFixed(2)})`);

    // Check pending claims status for smart bet delaying
    const pendingClaims = await getPendingClaimsStatus(funder);
    if (pendingClaims.hasPending) {
        log('⏳', `Found ${pendingClaims.count} pending winning position(s) totaling ~$${pendingClaims.totalPendingValue.toFixed(2)} USDC awaiting Claim settlement.`);
    }

    let betsPlaced = 0;
    const results = [];

    for (const raw of newPreds) {
        if (betsPlaced >= MAX_BETS_PER_CYCLE) {
            log('🛑', `Max bets per cycle reached (${MAX_BETS_PER_CYCLE}) -- stopping`);
            break;
        }

        console.log('\n' + '-'.repeat(55));
        const p = parsePrediction(raw);
        const betKey = getBetKey(today, p.matchIndex, p.prediction);

        log('⚽', `#${p.matchIndex}  ${p.team1}  vs  ${p.team2}`);
        log('📋', `Prediction: ${p.prediction}`);
        log('📊', `Confidence: ${p.confidence}% | League: ${p.league}`);

        // 1) Filter confidence below 75%
        if (p.confidence < 75) {
            log('⏭️', `Skip -- confidence ${p.confidence}% below 75%`);
            await recordBet(col, history, betKey, 0, null);
            results.push({ ...p, status: 'SKIP', reason: `Confidence ${p.confidence}% < 75%` });
            continue;
        }

        // 2) Classify prediction
        const cls = classifyPrediction(p.prediction);
        if (cls.type === 'unknown') {
            log('⚠️', `Cannot classify prediction: "${p.prediction}"`);
            await recordBet(col, history, betKey, 0, null);
            results.push({ ...p, status: 'SKIP', reason: 'Unknown prediction type' });
            continue;
        }

        // 3) Search fixture on Polymarket
        const event = await searchFixture(p.team1, p.team2);
        if (!event) {
            const retries = (history.searchRetries[betKey] || 0) + 1;
            history.searchRetries[betKey] = retries;
            if (retries >= MAX_SEARCH_RETRIES) {
                log('🛑', `Match not found after ${retries} cycles -- permanently skipping`);
                await recordBet(col, history, betKey, 0, null);
                results.push({ ...p, status: 'SKIP', reason: `Match not found (${retries} cycles)` });
            } else {
                log('⏳', `Match not found on Polymarket (attempt ${retries}/${MAX_SEARCH_RETRIES}) -- will retry next cycle`);
                await saveBetHistory(col, history);
                results.push({ ...p, status: 'RETRY', reason: `Match not found (attempt ${retries})` });
            }
            continue;
        }

        // 4) Check duplicate event ID
        if ((history.events && history.events.includes(event.id)) || (DRY_RUN && dryRunEvents.has(event.id))) {
            log('⏭️', `Skip -- event ID ${event.id} already has a placed bet`);
            await recordBet(col, history, betKey, 0, event.id);
            results.push({ ...p, status: 'SKIP', reason: 'Duplicate event bet' });
            continue;
        }

        // 5) Find market and outcome token
        const target = await findMarketAndOutcome(event, cls, p.team1, p.team2);
        if (!target) {
            log('⏭️', `Target market not found on Polymarket for ${p.prediction}`);
            await recordBet(col, history, betKey, 0, event.id);
            results.push({ ...p, status: 'SKIP', reason: 'Market not found on Polymarket' });
            continue;
        }

        log('🎯', `Selected outcome: "${target.outcomeName}" (Token ID: ${target.tokenID.slice(0, 10)}...)`);

        // 6) Live Orderbook & Odds
        const ob = await getOrderbookTop(client, target.tokenID);
        if (!ob) {
            log('⚠️', 'No liquidity currently available on the orderbook -- will retry next cycle');
            continue;
        }

        const currentOdds = ob.decimalOdds;
        log('📊', `Current Odds: ${currentOdds.toFixed(2)} (Best Price: $${ob.price.toFixed(3)}) | Available Liquidity: $${ob.availableUsdc.toFixed(2)} (${ob.availableShares} shares)`);

        // 7) Time to Kickoff Check
        const startTimeStr = event.startTime || target.market.gameStartTime;
        const kickoffMs = startTimeStr ? new Date(startTimeStr).getTime() : 0;
        const nowMs = Date.now();
        const minutesLeft = kickoffMs ? (kickoffMs - nowMs) / (60 * 1000) : 999;

        // In-Play Protection: If match started more than 15 minutes ago, skip
        if (minutesLeft < -15) {
            log('⏭️', `Match already started/finished (${Math.round(minutesLeft)} mins ago) -- skipping`);
            await recordBet(col, history, betKey, 0, event.id);
            results.push({ ...p, status: 'SKIP', reason: 'Match already in-play' });
            continue;
        }

        // ═══════════════════════════════════════════════
        //  RULE: SMART BET DELAY FOR PENDING CLAIMS
        // ═══════════════════════════════════════════════
        // If there are pending winning bets / claims awaiting settlement into cash:
        // - If kickoff is far (> 30 mins): DELAY the bet so cash from claims is available!
        // - If kickoff is urgent (<= 30 mins): BET IMMEDIATELY with available cash!
        if (pendingClaims.hasPending) {
            if (minutesLeft > 30) {
                log('⏳', `[DELAY] Match "${p.team1} vs ${p.team2}" (starts in ${Math.round(minutesLeft)}m). Postponing bet to wait for pending winning claims ($${pendingClaims.totalPendingValue.toFixed(2)}) to settle into cash first...`);
                results.push({ ...p, status: 'DELAYED', reason: `Waiting for pending claims to settle ($${pendingClaims.totalPendingValue.toFixed(2)})` });
                continue;
            } else {
                log('🚨', `[URGENCY CUTOFF] Match kickoff is imminent (${Math.round(minutesLeft)}m <= 30m) -- placing bet NOW with current available cash without waiting!`);
            }
        }

        if (!history.oddsTracker) history.oddsTracker = {};
        const tracker = history.oddsTracker[betKey] || { peakOdds: currentOdds, lastOdds: currentOdds };

        // ═══════════════════════════════════════════════
        //  RULE: MINIMUM ODDS FLOOR (Odds < 1.15)
        // ═══════════════════════════════════════════════
        if (currentOdds < 1.15) {
            if (p.confidence < 85) {
                if (minutesLeft <= 30) {
                    // Kickoff window reached and odds are still < 1.15 with conf < 85% -> REJECT
                    log('🛑', `Odds ${currentOdds.toFixed(2)} < 1.15 and confidence ${p.confidence}% < 85% at kickoff window (${Math.round(minutesLeft)}m) -> REJECTED`);
                    await recordBet(col, history, betKey, 0, event.id);
                    results.push({ ...p, status: 'SKIP', reason: `Odds ${currentOdds.toFixed(2)} < 1.15 with conf < 85%` });
                    continue;
                } else {
                    // Match is still far (> 30 mins) -> do NOT kill; wait to see if odds rise!
                    log('⏳', `Odds ${currentOdds.toFixed(2)} < 1.15 (conf ${p.confidence}%) but kickoff in ${Math.round(minutesLeft)} mins -> Waiting for odds to rise`);
                    continue;
                }
            } else {
                log('⚡', `Odds ${currentOdds.toFixed(2)} < 1.15 ALLOWED because confidence ${p.confidence}% >= 85%`);
            }
        }

        // Kickoff Urgency: <= 30 minutes to match start
        let shouldPlaceNow = false;
        if (minutesLeft <= 30) {
            log('🚨', `Kickoff urgency window reached (remaining: ${Math.round(minutesLeft)} mins) -> Placed immediately`);
            shouldPlaceNow = true;
        } else {
            // Trailing Peak Logic
            if (currentOdds > tracker.peakOdds) {
                tracker.peakOdds = currentOdds;
                tracker.lastOdds = currentOdds;
                history.oddsTracker[betKey] = tracker;
                await saveBetHistory(col, history);
                log('📈', `Odds rising: new peak ${currentOdds.toFixed(2)} (kickoff in ${Math.round(minutesLeft)} mins) -> Waiting for peak reversal`);
                continue;
            } else if (currentOdds <= tracker.peakOdds - 0.01) {
                log('🎯', `Odds peaked at ${tracker.peakOdds.toFixed(2)} and dropped to ${currentOdds.toFixed(2)} (>= 0.01 drop) -> TRIGGERING BET!`);
                shouldPlaceNow = true;
            } else {
                tracker.lastOdds = currentOdds;
                history.oddsTracker[betKey] = tracker;
                await saveBetHistory(col, history);
                log('⏳', `Odds holding at ${currentOdds.toFixed(2)} (peak: ${tracker.peakOdds.toFixed(2)}, kickoff in ${Math.round(minutesLeft)} mins) -> Waiting`);
                continue;
            }
        }

        // 8) Bet Sizing & Safety Caps
        const availableBalance = Math.max(0, currentBalance - MIN_RESERVE_USDC);
        if (availableBalance <= 0 && !DRY_RUN) {
            log('🛑', `Available balance ($${currentBalance.toFixed(2)}) is below reserve ($${MIN_RESERVE_USDC.toFixed(2)}) -- skipping order`);
            continue;
        }

        let pct = 0.10;
        if (p.confidence >= 85) pct = 0.25;
        else if (p.confidence >= 80) pct = 0.15;

        let targetUsdc = availableBalance * pct;
        if (DRY_RUN && targetUsdc <= 0) targetUsdc = 10.0; // Simulate $10 in dry run

        const dailySpend = getDailySpend(history);
        const dailyCap = (currentBalance + dailySpend) * 0.60;
        const dailyRemaining = Math.max(0, dailyCap - dailySpend);
        targetUsdc = Math.min(targetUsdc, dailyRemaining);

        // Check if book liquidity is too shallow (< $1.00 or < 30% of target bet)
        if (ob.availableUsdc < 1.0) {
            log('⏳', `Orderbook liquidity ($${ob.availableUsdc.toFixed(2)}) is below $1.00 minimum -- waiting`);
            continue;
        }
        if (ob.availableUsdc < targetUsdc * 0.3 && targetUsdc >= 5.0) {
            log('⏳', `Orderbook liquidity ($${ob.availableUsdc.toFixed(2)}) is too shallow for target bet ($${targetUsdc.toFixed(2)}) -- waiting`);
            continue;
        }

        targetUsdc = Math.min(targetUsdc, ob.availableUsdc);

        let sharesToBuy = Math.floor(targetUsdc / ob.price);
        if (sharesToBuy < ob.minOrderSize) {
            const minCost = ob.minOrderSize * ob.price;
            // Only bump if within balance and within 1.5x of target
            if (minCost <= availableBalance && minCost <= targetUsdc * 1.5 && ob.availableShares >= ob.minOrderSize) {
                sharesToBuy = Math.ceil(ob.minOrderSize);
            } else {
                log('⚠️', `Calculated shares (${sharesToBuy}) below minimum order size (${ob.minOrderSize}) -- skipping`);
                continue;
            }
        }

        const totalCostUsdc = sharesToBuy * ob.price;
        if (totalCostUsdc > availableBalance && !DRY_RUN) {
            log('🛑', `Order cost ($${totalCostUsdc.toFixed(2)}) exceeds available balance ($${availableBalance.toFixed(2)})`);
            continue;
        }

        log('💵', `Target Bet: $${targetUsdc.toFixed(2)} USDC -> Buying ${sharesToBuy} shares @ $${ob.price.toFixed(3)} (~$${totalCostUsdc.toFixed(2)} USDC)`);

        // 9) Submit Order
        if (DRY_RUN) {
            log('🧪', `[DRY RUN] Would place order: BUY ${sharesToBuy} shares of token ${target.tokenID.slice(0, 8)}... at price $${ob.price.toFixed(3)} (Odds: ${currentOdds.toFixed(2)})`);
            await recordBet(col, history, betKey, totalCostUsdc, event.id);
            currentBalance -= totalCostUsdc; // Update running balance for next matches in loop
            betsPlaced++;
            results.push({ ...p, status: 'BET_PLACED (DRY RUN)', amount: totalCostUsdc, odds: currentOdds });
        } else {
            try {
                const userOrder = {
                    tokenID: target.tokenID,
                    price: ob.price,
                    size: sharesToBuy,
                    side: Side.BUY,
                };
                const orderOptions = {
                    tickSize: ob.tickSize,
                    negRisk: ob.negRisk,
                };
                log('🚀', `Submitting FOK order to Polymarket CLOB (tickSize: ${ob.tickSize}, negRisk: ${ob.negRisk})...`);
                const orderRes = await client.createAndPostOrder(userOrder, orderOptions, OrderType.FOK);
                log('🎉', `Order submitted successfully:`, orderRes);
                await recordBet(col, history, betKey, totalCostUsdc, event.id);
                currentBalance -= totalCostUsdc; // Update running balance for next matches in loop
                betsPlaced++;
                results.push({ ...p, status: 'BET_PLACED', amount: totalCostUsdc, odds: currentOdds, orderRes });
            } catch (err) {
                log('❌', `Order placement error: ${err.message}`);
                results.push({ ...p, status: 'ERROR', error: err.message });
            }
        }
    }

    log('🏁', `Cycle completed. Bets placed: ${betsPlaced}`);
}

// ═══════════════════════════════════════════════
//  MAIN DAEMON LOOP
// ═══════════════════════════════════════════════
async function main() {
    console.log('='.repeat(60));
    console.log('  POLYMARKET AUTO-BETTING DAEMON');
    console.log(`  Mode: ${DRY_RUN ? 'SIMULATION (DRY RUN)' : 'LIVE BETTING'}`);
    console.log(`  Loop: ${RUN_ONCE ? 'RUN ONCE' : `EVERY ${CHECK_INTERVAL_MS / 60000} MINUTES`}`);
    console.log(`  Min Reserve: $${MIN_RESERVE_USDC.toFixed(2)} USDC`);
    console.log('='.repeat(60));

    if (!WALLET_PRIVATE_KEY) {
        throw new Error('Missing PRIVATE_KEY in .env');
    }

    initProxies();
    const db = initFirebase();
    const col = await initMongo();

    const wallet = new Wallet(WALLET_PRIVATE_KEY);
    const { relayClient, walletClient } = await initRelayClient(WALLET_PRIVATE_KEY);
    const { funder, isDepositWallet } = await resolveFunderAndType(wallet.address, relayClient);
    const client = await initClobClient(wallet, funder);

    let isRunning = false;
    const run = async () => {
        if (isRunning) return;
        isRunning = true;
        try {
            await runCycle(db, wallet, col, client, relayClient, funder, isDepositWallet, walletClient);
        } catch (e) {
            log('💥', `Cycle exception: ${e.message}`);
        } finally {
            isRunning = false;
        }
    };

    await run();
    if (RUN_ONCE) {
        log('👋', 'Run once completed -- exiting');
        process.exit(0);
    }

    const interval = setInterval(run, CHECK_INTERVAL_MS);
    const cleanup = () => {
        log('🛑', 'Shutting down daemon...');
        clearInterval(interval);
        process.exit(0);
    };

    process.on('SIGINT', cleanup);
    process.on('SIGTERM', cleanup);
}

main().catch(e => {
    console.error('Fatal error:', e);
    process.exit(1);
});
