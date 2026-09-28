# Area certificates for the far-commutator bound in Houghton's group H_3

## Current sharper bound

`build107.py` reconstructs the auxiliary-relator proof of
`A*(M) <= 135 M^(log2 107)` without consuming any external certificate package.
`verify107.py` is independent of the builder and checks all 25 distributed
certificates over the original five relators, as well as the auxiliary lists,
matrix counts, rule costs, weight inequality and characteristic polynomial.
The auxiliary relation is a nine-cell consequence, not a free sixth relator.
Its expansion is delayed until after recursive substitution. No image of r2 is
needed for this restricted recursion; the original five-image endomorphism
certificate below remains available independently.

    python build107.py
    python verify107.py

The deterministic output is `out/certificates107.json.gz`. Its current 7,366
original cells include normal-form certificates through k=8. The all-k area
theorem uses the written recurrence; its scalar induction and eight short
finite inputs have the Lean coverage detailed in `../README.md`.

## Original fallback archive

These files make the polynomial far-commutator area bound (the paper's polynomial-area theorem, A*(M) <= M^11)
checkable by machine at every finite step.

A certificate for a null word w is a list of cells (z, r, s), r one of the five relators of Johnson's
presentation (Lee, arXiv:1212.0257, Theorem 2.8), s = +1 or -1, with

    w  ==  prod_k  z_k r_k^{s_k} z_k^{-1}      in the free group on a, b, x (x = alpha).

The number of cells bounds the area of w.

## Files

- `vk.py`: free-group routines and the derivation engine. A derivation rewrites a token list; each
  step replaces one run u by v where u v^-1 is conjugate to an already certified relation (or a relator),
  and the relation's cells are conjugated into place. The finished list of cells is re-verified by free
  reduction before a lemma is accepted.
- `lemmas_small.py`: the transfer and halving lemmas at the parameters used: A(2..6), E(0..3), U(1..3),
  B(2..3), B0.
- `lemmas_psi.py`: the doubling endomorphism psi(a) = a^2, psi(b) = b^2, psi(x) = [a^2, b^2]; the relation
  rho^b = R' (14 cells); [x, rho] (5); psi(x) = s_1 s_2 s_0 s_1 (6); the braid move (4); the images
  psi(r1), psi(r2), psi(r3), psi(r5) (17, 359, 864, 182; psi(r4) is freely trivial); psi(rho) = R (84).
  psi(r2) is produced by an implementation of a coset rewriting procedure; like every other certificate, its cell list is re-verified by free reduction.
- `recursion.py`: the recursion executed: certificates of X_n = W_n obtained by transporting earlier
  certificates through psi cell by cell (each psi(r_i) replaced by its certificate) or by conjugating by b;
  then [x, X_n] and A(m) via the halving lemma at k = 2.
- `build_all.py`: builds everything, checks each count against the claimed bound, and exports
  `out/certificates.json.gz` (recursion instances n <= 5).
- `verify.py`: independent verifier. It shares no code with the builder: it recomputes each target word
  from the definitions (including W_n by its own recursion), multiplies out the cells and freely reduces.

## Reproduce

    python build_all.py        # build, compare with claimed counts, export
    python verify.py           # independent check of the exported certificates
    python recursion.py 9      # the executed recursion up to n = 9 (about two minutes)

## Certificate contents

Every claimed count is met exactly:

| relation | cells |
|---|---|
| A(2), A(3), A(4), A(5), A(6) | 1, 21, 47, 79, 157 |
| E(0), E(1), E(2), E(3) | 1, 4, 27, 76 |
| U(1), U(2), U(3) | 1, 5, 32 |
| B0, B(2), B(3) | 5, 9, 12 |
| rho^b = R' | 14 |
| [x, rho] | 5 |
| psi(x) = s_1 s_2 s_0 s_1 | 6 |
| braid move | 4 |
| psi(r1), psi(r2), psi(r3), psi(r4), psi(r5) | 17, 359, 864, 0, 182 |
| psi(rho) = R | 84 |

Executed recursion (cells of the certificate of X_n = W_n, against the recursion bound
Rw(2n) <= 864 Rw(n) + 84 #rho(W_n), Rw(2n+1) <= Rw(2n) + 14 #rho(W_2n)):

| n | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 | 9 |
|---|---|---|---|---|---|---|---|---|---|
| cells | 0 | 0 | 14 | 84 | 392 | 995 | 2493 | 5298 | 11878 |
| bound | 0 | 0 | 14 | 84 | 392 | 12516 | 14014 | 74424 | 81004 |
| [x, X_n] | 1 | 7 | 60 | 308 | 1383 | 2669 | 7884 | 13578 | 36479 |

Far commutators via the halving lemma at k = 2: A(3..11) <= 21, 51, 175, 689, 2857, 5447, 15895, 27301,
73121 (the direct small-lemma route gives the sharper 21, 47, 79, 157 for m <= 6). The bound m^11 is
not close to binding at these sizes; the executed certificates are far smaller than the recursion bound
because psi(r4) is freely trivial and most cells are r4-cells.

## What this does and does not certify

Checked by the independent verifier on the distributed file: every finite relation the proof uses, and the recursion's
instances for n <= 5. The instances 6 <= n <= 9 were executed by `python recursion.py 9` (cell counts in the table above) but
are not in the distributed file; `python build_all.py 9` exports them, after which `python verify.py` checks them.
The full area theorem is not formalized in Lean. The release's Lean arithmetic file
checks a conditional all-depth induction for the reweighted recurrence, while
FreeReduction.lean proves certificate-checker soundness and Certificates.lean
checks the 15 core finite inputs with at most 21 cells. All 40 distributed
certificates are checked in Python. See ../README.md for the precise boundary.
