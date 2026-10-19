#!/usr/bin/env python3
"""
Collect public ssh-rsa keys from https://github.com/<user>.keys for usernames taken from
the follower pages of a few seed accounts.  Stores ONLY anonymised records
(salted hash of the username, exponent, modulus); no usernames are written to disk.

Usage:
    CRAWLER_CONTACT="you@example.org" KEY_SALT="long-random-string" \
        python3 corpus_collect.py --seeds torvalds,gaearon --pages 40 --out keys.json [--max-users 5000]

Please respect GitHub's terms of use and rate limits; the defaults are deliberately polite
(0.4 s pause between follower pages, 8 concurrent key downloads, back-off on HTTP 429).
"""
import argparse, base64, hashlib, json, os, random, re, sys, threading, time
import urllib.error, urllib.request
from concurrent.futures import ThreadPoolExecutor


def get(url, headers, tries=3):
    for i in range(tries):
        try:
            with urllib.request.urlopen(urllib.request.Request(url, headers=headers), timeout=20) as r:
                return r.read().decode('utf-8', 'replace')
        except urllib.error.HTTPError as e:
            if e.code == 429:
                time.sleep(5 * (i + 1)); continue
            if e.code in (403, 404):
                return ''
        except Exception:
            time.sleep(1)
    return ''


def parse_ssh_rsa(line):
    parts = line.split()
    if len(parts) < 2 or parts[0] != 'ssh-rsa':
        return None
    try:
        blob = base64.b64decode(parts[1])
        def rd(b, i):
            L = int.from_bytes(b[i:i + 4], 'big'); return b[i + 4:i + 4 + L], i + 4 + L
        t, i = rd(blob, 0); e, i = rd(blob, i); n, i = rd(blob, i)
        if t != b'ssh-rsa':
            return None
        return int.from_bytes(e, 'big'), int.from_bytes(n, 'big')
    except Exception:
        return None


def main():
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument('--seeds', required=True, help='comma-separated seed accounts whose follower pages are read')
    ap.add_argument('--pages', type=int, default=40, help='follower pages per seed (about 50 users each)')
    ap.add_argument('--max-users', type=int, default=0, help='examine only a random subset of this many usernames (0 = all)')
    ap.add_argument('--out', default='keys.json')
    ap.add_argument('--shuffle-seed', type=int, default=1)
    a = ap.parse_args()
    contact = os.environ.get('CRAWLER_CONTACT', '')
    salt = os.environ.get('KEY_SALT', '')
    if not salt:
        sys.exit('Set KEY_SALT (any long random string, kept private) so that identifiers cannot be reversed.')
    headers = {'User-Agent': 'research-crawler' + (f' (contact: {contact})' if contact else '')}

    users, seen = [], set()
    for seed in a.seeds.split(','):
        got = 0
        for pg in range(1, a.pages + 1):
            html = get(f'https://github.com/{seed}?tab=followers&page={pg}', headers)
            names = re.findall(r'data-hovercard-url="/users/([A-Za-z0-9-]+)/hovercard"', html)
            if not names:
                break
            for u in dict.fromkeys(names):
                if u not in seen:
                    seen.add(u); users.append(u); got += 1
            time.sleep(0.4)
        print(f'seed {seed}: +{got} usernames (total {len(users)})', flush=True)
    random.Random(a.shuffle_seed).shuffle(users)
    if a.max_users:
        users = users[:a.max_users]

    lock = threading.Lock(); out = []; stats = dict(users=0, with_keys=0, lines=0, rsa=0)

    def work(u):
        txt = get(f'https://github.com/{u}.keys', headers)
        recs = [r for r in map(parse_ssh_rsa, txt.splitlines()) if r]
        with lock:
            stats['users'] += 1; stats['lines'] += len(txt.splitlines())
            stats['with_keys'] += bool(txt.strip()); stats['rsa'] += len(recs)
            for e, n in recs:
                out.append(dict(id=hashlib.sha256((salt + u).encode()).hexdigest()[:10], e=e, n=hex(n)))
            if stats['users'] % 500 == 0:
                print(stats, flush=True); json.dump(out, open(a.out, 'w'))

    with ThreadPoolExecutor(8) as ex:
        list(ex.map(work, users))
    json.dump(out, open(a.out, 'w'))
    print('DONE', stats, flush=True)


if __name__ == '__main__':
    main()
