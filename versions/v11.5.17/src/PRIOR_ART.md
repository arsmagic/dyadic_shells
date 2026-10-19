# Prior-art check for FP-MITM (search done on 2026-10-08; abstracts and excerpts only)

Sources: SciSpace paper search (4 queries), Firecrawl web search (3 queries). Elicit was unavailable (plan without API access).
Full texts of the Meng papers were NOT accessible (paywall / abstract-only results); every statement about their technique is therefore
inferred from abstracts and must be checked against the full papers. Bibliographic details below come from search excerpts and are unverified.

| Topic | Closest works found | Relation to FP-MITM | Confidence |
|---|---|---|---|
| Meet in the middle for sparse / fixed-weight unknowns | Stinson (baby-step giant-step for low Hamming weight discrete logarithms); Coppersmith (low-weight DLP); Kacsmar, Plosker, Henry (2017, computing low-weight discrete logarithms) | The inner join over the U zone is exactly a fixed-weight subset-sum meet in the middle, here in the group R/Z. Not new. | high (several excerpts agree) |
| Subset-sum algorithms | Horowitz-Sahni; Schroeppel-Shamir (low memory); Howgrave-Graham-Joux (representation technique, about 2^0.337n); Becker-Coron-Joux (about 2^0.291n); later improvements (about 2^0.283n) | Possible speed-ups of the inner join (a >= 6): representation technique, Schroeppel-Shamir. Not tried. | medium |
| Square-root (BSGS / rho) attacks on RSA beyond the Coppersmith N^(1/4) range | Meng (2010), Cryptanalysis of RSA with small prime combination: |rho*q - p| = N^(1/4+gamma) factored in time O(N^(gamma+eps)) by square-root attacks (baby-step giant-step and a more sophisticated one). Meng and Zheng (ACISP 2012), Cryptanalysis of RSA with a small parameter: BSGS and Pollard rho for a small parameter k; a later paper gives a birthday variant | Same family of ideas for a DENSE unknown beyond N^(1/4): a smooth approximation plus a collision search replaces lattice reduction. Whether their linearisation and integrality test coincide with ours (fractional parts modulo 1, coupling zone) cannot be decided from abstracts. | medium-low on the technical overlap |
| Structured primes in the wild | Bernstein et al. (2013); Nitaj and Rachidi (ePrint 2015/398, weak primes a*p = u0 + M1*u1 + ...); a 2024 paper by Anwar, Ismail and Bahig on prime factors of the form a^m + r (exact title not recorded) | These concern structure of the primes themselves (lattice / divisibility), not of the centre; the a^m + r work is the closest to the b^r anchors tried in the audit. | medium |
| Number-theoretic context | Shparlinski and others: distribution of RSA moduli with prescribed bit patterns or Hamming weight | Existence / counting results, not attacks. | low relevance |

## Assessment
* The meet-in-the-middle core is classical (low-weight DLP / subset sum). It should be cited, not claimed.
* The idea "smooth approximation of a prime + integrality becomes an additive equality + collision search beyond N^(1/4)" is probably related to
  Meng's and Meng-Zheng's square-root attacks (dense case). This must be checked in the full texts before any claim of novelty.
* What I could not find (in abstracts): sparse (low Hamming weight) centres or offsets combined with the zone analysis (U zone uncoupled by the
  second-order term c2 ~ 2^-(r-7), M zone enumerated), with explicit coverage accounting. This combination may be new but is a modest, incremental
  contribution built from known tools; it is unverified.
* Reasonable framing: "application and analysis of known meet-in-the-middle techniques to a new structured class (sparse centres), with
  measured crossovers against lattice and enumeration".


## Update 2026-10-08 (full texts received)
See `LITERATURE_FINDINGS.md`: the inner join of FP-MITM coincides with Coppersmith's Las Vegas algorithm for low Hamming weight discrete logarithms as described by Stinson (2002). Meng (2010) and Meng-Zheng (2012) are still unread.
