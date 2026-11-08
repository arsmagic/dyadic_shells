# Textbook companion scripts

This folder holds the runnable teaching scripts printed in the "Practice &
Reproducibility Laboratory" sections of the forthcoming textbook built on
this preprint series. Each chapter's companion script is the exact code
printed in that chapter, committed here as a standalone file so that the
chapter's citation and QR code resolve to a real, runnable file.

**Provenance note.** These scripts are pedagogical: each chapter explicitly
states that its printed laboratory code is self-contained teaching code and
*not* presented as a byte-for-byte reproduction of a file inside a specific
archived Zenodo source package. They are committed here, outside the
`versions/` tree, precisely to keep that distinction intact — the
`versions/*/src/` folders remain exact, byte-for-byte mirrors of their
respective Zenodo records (see the top-level [README](../README.md)).

| Chapter | Script | Illustrates |
|---|---|---|
| 1 — *From Pierre de Fermat to Maurice Kraitchik* | [`chapter01/dyadic_triple_to_factors.py`](./chapter01/dyadic_triple_to_factors.py) | Verifying a dyadic triple `(r, s, alpha)` against `n` and extracting a non-trivial factor via `gcd(2^r - s, n)` when one exists. |
| 2 — *The Binary "Passport" of a Number* | [`chapter02/dyadic_diagnostic.py`](./chapter02/dyadic_diagnostic.py) | The two-adic valuation `nu2`, the valence identity `nu2(alpha) == 2*nu2(s)`, and why identity validity, valence, and non-trivial factor recovery are three distinct conditions. |

Run either file directly to execute its chapter's laboratory assertions:

```bash
python3 textbook/chapter01/dyadic_triple_to_factors.py
python3 textbook/chapter02/dyadic_diagnostic.py
```

---
*Part of the dyadic-shell preprint series. Index: [../README.md](../README.md). License: CC BY-NC 4.0.*
