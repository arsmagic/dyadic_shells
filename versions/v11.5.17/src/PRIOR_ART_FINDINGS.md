# Prior-art findings for FP-MITM (full-text reading, English summary)

This note summarises what the full texts that were available established about the novelty of the
fractional-part meet-in-the-middle (FP-MITM) of Section 9 of the preprint. It accompanies the shorter
pre-reading check in `PRIOR_ART.md` and the reading plan in `READING_LIST.md`.

**Read in full or in part:** Stinson (Math. Comp. 71, 2002); slides of Kacsmar--Plosker--Henry (talk, not
the paper); slides of Coppersmith (ASIACRYPT 2003); Coppersmith (EUROCRYPT 1996, bivariate equation);
Sarkar--Maitra (Bull. Korean Math. Soc. 2009); Herrmann--May (ASIACRYPT 2008); Heninger--Shacham
(CRYPTO 2009); Howgrave-Graham--Joux (ePrint 2010/189); Becker--Coron--Joux (ePrint 2011/474);
Bonnetain--Bricout--Schrottenloher--Shen (ePrint 2020/168); Schroeppel--Shamir (MIT technical report, scan).
**Not available, therefore NOT read:** Meng (ICISC 2010), Meng--Zheng (ACISP 2012) and their follow-ups;
the Kacsmar--Plosker--Henry paper (only slides). Depth of reading: abstracts, introductions and the main
algorithms; proofs were not verified.

## Main conclusion on novelty
The inner stage of FP-MITM (random split of the U-zone positions into halves, repeated until the weight
divides evenly, then sorting and lookup over subset lists of weight k and a-k) **coincides with
Coppersmith's Las Vegas-type algorithm for the low-Hamming-weight discrete logarithm**, as presented by
Stinson (2002): complexity of order C(m/2, t/2) with a factor of order sqrt(t) from the repetitions
(Heiman--Odlyzko: C(m, t/2); deterministic Coppersmith: order m * C(m/2, t/2); Stinson's deterministic
variant via "splitting systems"). Hence the meet-in-the-middle core is classical and must be cited as such.

What remains non-classical, among the texts read:
1. the reduction "sparse centre -> integrality of a fractional part modulo 1" with the U and M zones split
   by the second-order coupling threshold c2 ~ 2^-(r-7);
2. the third list (subsets of the M zone) and the choice of cost-optimal **unbalanced** weight splits
   (new in this code; not seen in the papers read);
3. the coverage accounting and the comparison against lattices and enumeration.
All of this is a modest, incremental combination of known tools.

## Work by work
| Work | What was established | Consequence for us |
|---|---|---|
| Stinson 2002 | Heiman--Odlyzko and Coppersmith algorithms (deterministic and Las Vegas) for weight t in length m; a new deterministic version via "splitting systems" | our inner join = Coppersmith's algorithm; mandatory citation. Approximate equality (tolerance eps) is not treated in the text I read (not specifically searched) |
| Kacsmar--Plosker--Henry (slides) | improvements: interleaving of computations, a Pascal-rule reuse in the deterministic Coppersmith algorithm, generalisation to an arbitrary base | a possible replacement of our R random partitions by a deterministic cover; needs the paper itself |
| Coppersmith 1996 (EUROCRYPT, bivariate) | N^{1/4} high bits; condition (XY)^{3/2} < D; the equation (P0+x)(Q0+y)-N has a coupling term xy | analogue of our coupling term c2 * 2^{e+e'}; confirms that the N^{1/4} bound is tied to the quadratic term |
| Coppersmith 2003 (slides) | general survey of lattice methods | nothing on sparse or meet-in-the-middle (keyword search) |
| Sarkar--Maitra 2009 | trading "guessed bits" for "revealed bits" in partial key exposure | matches our cost estimate for the hybrid (number of guesses x lattice cost); not about a sparse centre |
| Herrmann--May 2008 | factoring with bits known in blocks at KNOWN positions (linear equations modulo a divisor) | contrast: our positions of ones are unknown, only their number is known to be small |
| Heninger--Shacham 2009 | branch-and-prune on bits when random bits of p, q, d, dp, dq are known | confirms bitwise lifting works for KNOWN bits; for a sparse unknown there is no pruning (cf. two-adic saturation) |
| Howgrave-Graham--Joux 2010; Becker--Coron--Joux 2011; Bonnetain et al. 2020 | representation technique for "hard knapsacks" of density ~1 (weight ~n/2), time ~2^{0.337n}, 2^{0.291n}, 2^{0.283n} | our regime is different: weight 3-8 out of 85-170 positions, approximate equality and an extra M list; no direct applicability seen, but not disproved |
| Schroeppel--Shamir | time 2^{n/2} at memory 2^{n/4} for four lists | saves memory, not time; our bottleneck is time |

## Improvement made along the way (ours, not from the papers)
The inner U-zone problem is really three-list: a list of M-subsets (|M_j|), a small list U1 and a large
sorted list U2. The cost of a balanced split (k, k) is |M_j| * C(h/2, k); an unbalanced split (k1, a-k1)
with small k1 is markedly cheaper at a comparable per-partition coverage. The planner `plan_y` in
`fpmitm.py` chooses the set of splits and the repetition count R by the cost model.
Measured (1024-bit, w = 300, jmax = 4, the same planned modulus for comparison):
* h = 6: 39.9 s -> 9.8 s (coverage 0.934, factor found);
* h = 7: 97.6 s -> 91.6 s (coverage 0.856, factor found);
* h = 8: stages j = 0,1,2 took 29.5 + 76.6 + 232 s (previously stage j = 2 did not finish in >10 min);
  stages j = 3,4 could not be completed. The full h = 8 run was NOT achieved.
Cost model with the new planner: predicted/measured = 0.93 (h=6), 0.85 (h=7), 0.40 (h=8, stages j<=2).
The constants were fitted with the previous planner, so the first two numbers are not an independent check;
for large lists the model underestimates the time.

## What is still missing for a final novelty decision
1. Meng (2010) and Meng--Zheng (2012): whether their linearisation and integrality test coincide with ours,
   and whether they have an analogue of the U and M zones.
2. The Kacsmar--Plosker--Henry paper (SAC 2017), to use deterministic covers.
3. A citation search on Stinson 2002 and Meng 2010 for RSA applications.
