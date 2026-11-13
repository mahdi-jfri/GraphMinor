# A uniform bound for complete graph minors

This folder holds the note "A uniform bound for complete graph minors" by MohammadTaghi
Hajiaghayi and Mahdi JafariRaviz, the programs and certificates that check its computer-assisted
part, and the scripts that write the certificate tables of the Lean formalization.

## The theorem

Graph Minors XIII (5.5), page 83, states, as a result of Thomason, that for every integer $p \ge 1$
every non-null simple graph $G$ with $|E(G)| \ge 2.68\, p \sqrt{\log_2 p}\, |V(G)|$ has a $K_p$
minor. Thomason's paper (A. Thomason, *An extremal function for contractions of graphs*, Math. Proc.
Cambridge Philos. Soc. 95 (1984), 261–265) gives the constant $2.68$ only for all sufficiently
large $p$. The note proves that for every integer $p \ge 51$, every non-null simple graph $G$ with
$|E(G)| \ge (16/5)\, p \sqrt{\ln p}\, |V(G)|$ has a $K_p$ minor. Since
$(16/5)\sqrt{\ln 2} = 2.6641\ldots < 2.68$, this gives (5.5) for every $p \ge 51$. The proof uses
Thomason's density reduction (his Lemma 1, page 262) and a random partition of the vertex set into
small blocks. Two certificates, checked with exact rational arithmetic, cover
$51 \le p \le 10^{44}$, and an analytic argument covers $\ln p \ge 100$. The note does not cover
$p \le 50$. In the Lean formalization, (5.5) is proved for every $p \ge 1$ as
`GraphMinor.Thomason.thomason84`, and Section 8 of the note explains which parts of that proof
follow the note.

## Files

| File | Contents |
| --- | --- |
| `uniform_minor_bound.pdf`, `uniform_minor_bound.tex` | The note and its LaTeX source. |
| `global_finite_checker.py` | Checker (and optional generator) for the certificate of Section 4 of the note, $51 \le p \le 109$. |
| `global_finite_certificate.jsonl` | That certificate: one row for each $p$, with one choice of blocks for each order of a reduced graph. |
| `global_medium_checker.py` | Checker (and optional generator) for the interval certificate of Section 5 of the note, $110 \le p \le 10^{44}$. |
| `global_medium_certificate.jsonl` | That certificate: 88 intervals of $p$ and 508 cells. |
| `verify_all.py` | Runs both checkers. |
| `medium_log2_certificate.py` | Checker and generator for the base-2 interval certificate used by the Lean proof for $110 \le p \le 10^{44}$. |
| `medium_log2_certificate.jsonl` | That certificate: 69 intervals of $p$ and 261 cells. |
| `gen_lean_finite.py` | Writes the Lean tables for $51 \le p \le 109$. |
| `gen_lean_medium.py` | Writes the Lean tables for $110 \le p \le 10^{44}$. |

## Running the checkers

The checkers need Python 3.8 or later and no other package. From this folder, run

```
python3 verify_all.py
```

or the two checks one at a time:

```
python3 global_finite_checker.py check global_finite_certificate.jsonl
python3 global_medium_checker.py check global_medium_certificate.jsonl
```

`verify_all.py` prints the following (the running times vary).

```
PASS: all integers 51 <= p <= 109; 19873 cases (p, n), 313 of them with pairs and triples.
Minimum B-(p-3) > 1/10 (approximately 0.100642159415); elapsed 1.00s.
PASS: 88 p intervals; 508 cells; all integers 110 <= p <= 100000000000000000000000000000000000000000000.
Minimum certified margin for B/p-(1-3/U): 9.98234667206e-07; elapsed 0.6s.
PASS: both exact certificates verified.
Together they cover all integers 51 <= p <= 10^44.
Section 6 of the note covers ln(p) >= 100, which includes every p > 10^44.
```

A checker stops with an error at the first failed test. Every test that accepts a certificate
uses integer or `fractions.Fraction` arithmetic, including the bounds on logarithms and square
roots. The decimal numbers in the output are for information only. The `check` commands only read
the certificates. The `gen` commands write a new certificate: they use floating point to propose
witnesses and then check each one exactly. In our runs, `gen` with the default options reproduced
the three certificate files of this folder exactly.

## The Lean tables

The Lean proof checks its certificates with Lean's kernel (`decide +kernel`), so it does not rely
on these scripts. The scripts only write the data. Each one first runs the same tests as the Lean
check and stops if a row fails.

| Script | Reads | Writes (in `GraphMinor/Thomason/`) |
| --- | --- | --- |
| `gen_lean_finite.py` | `global_finite_certificate.jsonl` | `UniformFinite51.lean` to `UniformFinite109.lean` |
| `gen_lean_medium.py` | `medium_log2_certificate.jsonl` (checked with `medium_log2_certificate.py`) | `UniformMedium0.lean` to `UniformMedium6.lean`, `UniformMediumRange.lean` |
| `medium_log2_certificate.py gen FILE` | nothing | `medium_log2_certificate.jsonl` |

To write the Lean files into a folder `OUTDIR`, run

```
python3 gen_lean_finite.py OUTDIR
python3 gen_lean_medium.py OUTDIR
```

With `OUTDIR` equal to `GraphMinor/Thomason`, the scripts reproduce the files of the formalization
exactly.

For $51 \le p \le 109$ the Lean proof uses the certificate of the note, with the same density $c$
and the same choices of blocks. It checks $c \le 2.68\, p \sqrt{\log_2 p}$ directly, in place of
$c < (16/5)\, p\sqrt{\ln p}$. For $110 \le p \le 10^{44}$ it uses the base-2 certificate
`medium_log2_certificate.jsonl` for the density $2.68\, p \sqrt{\log_2 p}$, not
`global_medium_certificate.jsonl`. For $p > 10^{44}$ it uses its own argument in base 2, in
`GraphMinor/Thomason/UniformTail.lean` and `GraphMinor/Thomason/UniformLarge.lean`.

## References

- N. Robertson and P. D. Seymour, *Graph Minors. XIII. The disjoint paths problem*, J. Combin.
  Theory Ser. B 63 (1995), 65–110, https://doi.org/10.1006/jctb.1995.1006. The statement (5.5) is
  on page 83.
- A. Thomason, *An extremal function for contractions of graphs*, Math. Proc. Cambridge Philos.
  Soc. 95 (1984), 261–265, https://doi.org/10.1017/S0305004100061521. Lemma 1 is on page 262.
- D. R. Wood, *An explicit bound on the extremal function for complete graph minors*,
  arXiv:2610.41060v1, 29 October 2026, https://arxiv.org/abs/2610.41060v1.
