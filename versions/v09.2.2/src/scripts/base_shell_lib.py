#!/usr/bin/env python3
"""
Base-Shell Diagnostic Framework: shared utilities for academic computational tests.

This module is intentionally conservative:
- Public-mode functions never require the factorization of N.
- Validation-mode functions require p and q and are clearly marked.
- No function claims to factor RSA-class moduli; nontrivial gcd events are reported
  as Kraitchik-style certificates when they occur.

Author: A. A. Khachatryan / SibarS Labs companion scripts
Version: v9.2.0-pre / academic test package
"""
from __future__ import annotations

import csv
import hashlib
import json
import math
import os
import platform
import random
import statistics
import sys
import time
from dataclasses import dataclass, asdict
from pathlib import Path
from typing import Dict, Iterable, Iterator, List, Optional, Sequence, Tuple

try:
    import sympy as sp  # type: ignore
except Exception as exc:  # pragma: no cover
    raise RuntimeError(
        "sympy is required. Install dependencies with: pip install -r requirements.txt"
    ) from exc

SignPair = Tuple[int, int]
CRTClass = str

SIGN_PAIRS: List[SignPair] = [(1, 1), (-1, -1), (1, -1), (-1, 1)]
SIGN_LABELS: Dict[SignPair, str] = {
    (1, 1): "++",
    (-1, -1): "--",
    (1, -1): "+-",
    (-1, 1): "-+",
}
HOMOGENEOUS_LABELS = {"++", "--"}
MIXED_LABELS = {"+-", "-+"}


@dataclass(frozen=True)
class ExperimentConfig:
    seed: int = 20260628
    bit_lengths: Tuple[int, ...] = (64, 96, 128, 192, 256)
    bases: Tuple[int, ...] = (2, 3, 5, 7, 11)
    theta_bands: Tuple[Tuple[float, float], ...] = ((0.15, 0.35), (0.25, 0.50))
    population_size_small: int = 200
    population_size_main: int = 1000
    output_dir: str = "results"
    figure_dir: str = "figures"
    data_dir: str = "data"
    logs_dir: str = "logs"
    # brute-force threshold for sanity checks; keep small by design
    max_bruteforce_A: int = 1_000_000


def ensure_dirs(root: Path | str, subdirs: Sequence[str] = ("data", "results", "figures", "logs")) -> None:
    root = Path(root)
    for sub in subdirs:
        (root / sub).mkdir(parents=True, exist_ok=True)


def write_json(path: Path | str, obj: object) -> None:
    p = Path(path)
    p.parent.mkdir(parents=True, exist_ok=True)
    with p.open("w", encoding="utf-8") as f:
        json.dump(obj, f, indent=2, ensure_ascii=False, sort_keys=True)


def read_json(path: Path | str) -> object:
    with Path(path).open("r", encoding="utf-8") as f:
        return json.load(f)


def write_csv(path: Path | str, rows: Sequence[Dict[str, object]], fieldnames: Optional[Sequence[str]] = None) -> None:
    p = Path(path)
    p.parent.mkdir(parents=True, exist_ok=True)
    if fieldnames is None:
        fieldnames = sorted({k for row in rows for k in row.keys()}) if rows else []
    with p.open("w", newline="", encoding="utf-8") as f:
        writer = csv.DictWriter(f, fieldnames=list(fieldnames))
        writer.writeheader()
        for row in rows:
            writer.writerow(row)


def read_csv(path: Path | str) -> List[Dict[str, str]]:
    with Path(path).open("r", newline="", encoding="utf-8") as f:
        return list(csv.DictReader(f))


def sha256_file(path: Path | str) -> str:
    h = hashlib.sha256()
    with Path(path).open("rb") as f:
        for chunk in iter(lambda: f.read(1024 * 1024), b""):
            h.update(chunk)
    return h.hexdigest()


def manifest(root: Path | str, config: Optional[ExperimentConfig] = None, extra: Optional[Dict[str, object]] = None) -> Dict[str, object]:
    root = Path(root)
    files = []
    for sub in ("scripts", "data", "results", "figures"):
        d = root / sub
        if d.exists():
            for path in sorted(d.rglob("*")):
                if path.is_file():
                    files.append({
                        "path": str(path.relative_to(root)),
                        "sha256": sha256_file(path),
                        "bytes": path.stat().st_size,
                    })
    return {
        "created_utc": time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime()),
        "python": sys.version,
        "platform": platform.platform(),
        "config": asdict(config) if config else None,
        "extra": extra or {},
        "files": files,
    }


def gcd(a: int, b: int) -> int:
    return math.gcd(int(a), int(b))


def inv_mod(a: int, m: int) -> int:
    return pow(int(a) % int(m), -1, int(m))


def crt_two(a_p: int, p: int, a_q: int, q: int) -> int:
    """Return x modulo N=pq with x=a_p mod p, x=a_q mod q."""
    p = int(p); q = int(q)
    n = p * q
    # x = a_p + p * t, p*t = a_q-a_p mod q -> t = (a_q-a_p)*p^-1 mod q
    t = ((int(a_q) - int(a_p)) * inv_mod(p, q)) % q
    return (int(a_p) + p * t) % n


def e_representatives(p: int, q: int) -> List[Dict[str, object]]:
    """Validation-mode E_N representatives with CRT labels."""
    reps: List[Dict[str, object]] = []
    n = int(p) * int(q)
    for eps_p, eps_q in SIGN_PAIRS:
        rep = crt_two(eps_p % p, p, eps_q % q, q)
        reps.append({
            "label": SIGN_LABELS[(eps_p, eps_q)],
            "eps_p": eps_p,
            "eps_q": eps_q,
            "e": rep % n,
            "is_mixed": SIGN_LABELS[(eps_p, eps_q)] in MIXED_LABELS,
            "is_homogeneous": SIGN_LABELS[(eps_p, eps_q)] in HOMOGENEOUS_LABELS,
        })
    return reps


def class_label_from_u(u: int, p: int, q: int) -> str:
    """Validation-mode label for a root of unity u modulo N."""
    up = int(u) % int(p)
    uq = int(u) % int(q)
    eps_p = 1 if up == 1 % p else -1 if up == (-1) % p else 0
    eps_q = 1 if uq == 1 % q else -1 if uq == (-1) % q else 0
    if eps_p == 0 or eps_q == 0:
        return "not_E_N"
    return SIGN_LABELS[(eps_p, eps_q)]


def exact_window_count_for_class(n: int, a: int, e: int) -> int:
    """
    Count s with 0 <= s < A and s == A*e (mod N).
    Valid for arbitrary A; O(1) formula.
    """
    n = int(n); a = int(a); e = int(e)
    c = (a * e) % n
    if c >= a:
        return 0
    return 1 + ((a - 1 - c) // n)


def exact_window_representatives_for_class(n: int, a: int, e: int, max_emit: Optional[int] = None) -> List[int]:
    """Emit representatives s in [0,A) with s == A*e mod N; validation helper."""
    n = int(n); a = int(a); e = int(e)
    c = (a * e) % n
    if c >= a:
        return []
    count = 1 + ((a - 1 - c) // n)
    if max_emit is not None:
        count = min(count, max_emit)
    return [c + k * n for k in range(count)]


def brute_force_window_count(n: int, a: int, max_a: int = 1_000_000) -> Optional[int]:
    """Brute-force count s in [0,A), only for small A; returns None when skipped."""
    n = int(n); a = int(a)
    if a > max_a:
        return None
    target = (a * a) % n
    cnt = 0
    for s in range(a):
        if (s * s) % n == target:
            cnt += 1
    return cnt


def public_global_indicator(n: int, b: int, r: int) -> int:
    """
    Public global-window indicator for global classes (+,+), (-,-).
    Uses low-height disjoint formula; if A>=N/2, the sum can be 2 and is still a valid count
    of the two global representatives satisfying s<A.
    """
    n = int(n); b = int(b); r = int(r)
    a = pow(b, r)
    x = pow(b, r, n)
    cnt = 0
    if x < a:
        cnt += 1
    if x > n - a:  # N-x < A
        cnt += 1
    return cnt


def theta_height_range(n: int, b: int, theta0: float, theta1: float, min_r: int = 1) -> List[int]:
    """Return r such that N^theta0 <= b^r <= N^theta1, using floating logs for ranges."""
    if not (0 < theta0 <= theta1):
        raise ValueError("Require 0 < theta0 <= theta1")
    if b <= 1:
        raise ValueError("Base b must be >= 2")
    logn = math.log(int(n))
    logb = math.log(int(b))
    r0 = max(min_r, math.ceil(theta0 * logn / logb))
    r1 = max(r0, math.floor(theta1 * logn / logb))
    return list(range(r0, r1 + 1))


def compute_zglob_for_n(n: int, bases: Sequence[int], theta0: float, theta1: float) -> Dict[str, object]:
    """Compute public Cglob, null mean, null variance proxy, and Zglob."""
    n = int(n)
    cglob = 0
    mu = 0.0
    var = 0.0
    num_heights = 0
    base_details = []
    for b in bases:
        if math.gcd(b, n) != 1:
            continue
        r_values = theta_height_range(n, b, theta0, theta1)
        b_c = 0
        b_mu = 0.0
        for r in r_values:
            a = pow(b, r)
            ind = public_global_indicator(n, b, r)
            p_hit = min(1.0, 2.0 * float(a) / float(n))  # public global first-order baseline
            cglob += ind
            b_c += ind
            mu += p_hit
            b_mu += p_hit
            var += p_hit * max(0.0, 1.0 - p_hit)
            num_heights += 1
        base_details.append({"base": b, "r_min": min(r_values) if r_values else None, "r_max": max(r_values) if r_values else None, "count": b_c, "mu": b_mu, "heights": len(r_values)})
    sigma = math.sqrt(max(0.0, var))
    z = (cglob - mu) / max(1.0, sigma)
    return {
        "Cglob": cglob,
        "mu": mu,
        "sigma": sigma,
        "Zglob": z,
        "num_heights": num_heights,
        "theta0": theta0,
        "theta1": theta1,
        "bases": ",".join(map(str, bases)),
        "base_details_json": json.dumps(base_details, sort_keys=True),
    }


def random_odd_with_bits(bits: int, rng: random.Random) -> int:
    if bits < 2:
        raise ValueError("bits must be >= 2")
    x = rng.getrandbits(bits)
    x |= (1 << (bits - 1))
    x |= 1
    return x


def random_prime_bits(bits: int, rng: random.Random) -> int:
    """Reproducible prime generation using sympy.isprime."""
    while True:
        x = random_odd_with_bits(bits, rng)
        if sp.isprime(x):
            return int(x)


def random_prime_residue_bits(bits: int, modulus: int, residue: int, rng: random.Random, max_tries: int = 200_000) -> int:
    """Generate a prime p of exact bit length with p == residue mod modulus."""
    modulus = int(modulus); residue = int(residue) % modulus
    if math.gcd(residue, modulus) != 1:
        raise ValueError("Residue must be coprime to modulus")
    low = 1 << (bits - 1)
    high = (1 << bits) - 1
    k_min = (low - residue + modulus - 1) // modulus
    k_max = (high - residue) // modulus
    if k_min > k_max:
        raise ValueError("No candidate in bit range for this residue/modulus")
    for _ in range(max_tries):
        k = rng.randint(k_min, k_max)
        x = residue + modulus * k
        if x % 2 == 0:
            continue
        if x.bit_length() == bits and sp.isprime(x):
            return int(x)
    # Deterministic fallback sweep around random start
    start = rng.randint(k_min, k_max)
    span = k_max - k_min + 1
    for j in range(min(span, max_tries)):
        k = k_min + ((start - k_min + j) % span)
        x = residue + modulus * k
        if x % 2 and x.bit_length() == bits and sp.isprime(x):
            return int(x)
    raise RuntimeError(f"Failed to generate residue prime after {max_tries} tries")


def generate_balanced_semiprime(bits: int, rng: random.Random) -> Tuple[int, int, int]:
    """Return N,p,q with p,q around half bit length."""
    p_bits = bits // 2
    q_bits = bits - p_bits
    while True:
        p = random_prime_bits(p_bits, rng)
        q = random_prime_bits(q_bits, rng)
        if p != q:
            n = p * q
            # Accept near target bit length; exact bit length may vary by one.
            if n.bit_length() in {bits - 1, bits, bits + 1}:
                return int(n), int(p), int(q)


def generate_residue_biased_semiprime(bits: int, modulus: int, residue_p: int, residue_q: int, rng: random.Random) -> Tuple[int, int, int]:
    p_bits = bits // 2
    q_bits = bits - p_bits
    while True:
        p = random_prime_residue_bits(p_bits, modulus, residue_p, rng)
        q = random_prime_residue_bits(q_bits, modulus, residue_q, rng)
        if p != q:
            n = p * q
            if n.bit_length() in {bits - 1, bits, bits + 1}:
                return int(n), int(p), int(q)


def weyl_sum_profile(n: int, b: int, h_values: Sequence[int], hmax_values: Sequence[int]) -> List[Dict[str, object]]:
    """Compute |sum_{r<=H} exp(2pi i h b^r/N)| / H for selected h,H."""
    import cmath
    rows: List[Dict[str, object]] = []
    n = int(n); b = int(b)
    max_hmax = max(hmax_values) if hmax_values else 0
    # Precompute residues b^r mod N
    residues = [pow(b, r, n) for r in range(1, max_hmax + 1)]
    for h in h_values:
        partial: List[complex] = []
        total = 0j
        for x in residues:
            total += cmath.exp(2j * math.pi * ((int(h) * x) / n))
            partial.append(total)
        for H in hmax_values:
            if H <= 0 or H > len(partial):
                continue
            mag = abs(partial[H - 1]) / H
            rows.append({"N": str(n), "base": b, "h": int(h), "H": int(H), "normalized_magnitude": mag})
    return rows


def manual_auc(y_true: Sequence[int], scores: Sequence[float]) -> Optional[float]:
    """Compute ROC AUC via rank statistic. Returns None if degenerate."""
    pairs = sorted(zip(scores, y_true), key=lambda x: x[0])
    n_pos = sum(y_true)
    n_neg = len(y_true) - n_pos
    if n_pos == 0 or n_neg == 0:
        return None
    # average ranks for ties
    ranks = [0.0] * len(pairs)
    i = 0
    while i < len(pairs):
        j = i + 1
        while j < len(pairs) and pairs[j][0] == pairs[i][0]:
            j += 1
        avg_rank = (i + 1 + j) / 2.0
        for k in range(i, j):
            ranks[k] = avg_rank
        i = j
    rank_sum_pos = sum(rank for rank, (_, y) in zip(ranks, pairs) if y == 1)
    auc = (rank_sum_pos - n_pos * (n_pos + 1) / 2.0) / (n_pos * n_neg)
    return auc


def ks_statistic(x: Sequence[float], y: Sequence[float]) -> float:
    """Two-sample KS statistic (no p-value); pure Python fallback."""
    xs = sorted(x); ys = sorted(y)
    i = j = 0
    n = len(xs); m = len(ys)
    d = 0.0
    values = sorted(set(xs + ys))
    for v in values:
        while i < n and xs[i] <= v:
            i += 1
        while j < m and ys[j] <= v:
            j += 1
        d = max(d, abs(i / n - j / m))
    return d


def summarize_numeric(values: Sequence[float]) -> Dict[str, Optional[float]]:
    vals = [float(v) for v in values if v is not None and math.isfinite(float(v))]
    if not vals:
        return {"n": 0, "mean": None, "std": None, "median": None, "min": None, "max": None, "q25": None, "q75": None}
    vals_sorted = sorted(vals)
    def quantile(q: float) -> float:
        if len(vals_sorted) == 1:
            return vals_sorted[0]
        pos = q * (len(vals_sorted) - 1)
        lo = math.floor(pos); hi = math.ceil(pos)
        if lo == hi:
            return vals_sorted[lo]
        return vals_sorted[lo] * (hi - pos) + vals_sorted[hi] * (pos - lo)
    return {
        "n": len(vals),
        "mean": statistics.mean(vals),
        "std": statistics.stdev(vals) if len(vals) > 1 else 0.0,
        "median": statistics.median(vals),
        "min": vals_sorted[0],
        "max": vals_sorted[-1],
        "q25": quantile(0.25),
        "q75": quantile(0.75),
    }


def parse_int_maybe(value: object) -> Optional[int]:
    if value in (None, "", "null"):
        return None
    return int(str(value).strip())
