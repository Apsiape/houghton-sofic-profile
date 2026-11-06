# Houghton's group H3 has superpolynomial sofic profile: Lean core

This directory proves selected results of the paper in Lean 4. It is the Lean core of the paper, not a formalization of the whole paper.

## What is checked

`Statements.lean` freezes the selected propositions, `Proofs.lean` proves them, and `Audit.lean` checks that they match the original declarations below and prints their axioms. A row credits only the form stated in it.

| Printed result | Lean name | Checked form |
|---|---|---|
| Theorem 1.1 | `Houghton.theorem_1_1_final` | The printed lower bounds, with the stronger explicit upper bound 2^(7000√r·log₂r) for E_H. |
| Corollary 1.2 | `Houghton.corollary_1_2_final` | Partial: the finite, superpolynomial profile conclusion only; not the structural extension or elementary-amenability clause. |
| Corollary 1.3 | `Houghton.cremona_finAlt3` | Conditional and partial: only the H₃, finitary-three-cycle-kernel conclusion, with the explicit premise `hS : PermSectorBound`, which this root does not discharge; not the general H_m statement or the commutator-order, nilpotency-class and abelian-index conclusions. |
| Theorem 3.1 | `Houghton.astar_le_pow` | The printed bound A*(M) ≤ M¹¹ for M ≥ 2. |
| Theorem 3.2 | `Houghton.astar_le_weighted_rpow` | The stronger range M ≥ 1: a natural area witness ≤ 135·M^(log₂107). |
| Theorem 3.3 | `Houghton.dehn_bound` | The printed bound in the equivalent pointwise form over all null words: area ≤ 400n⁴(1+A) for n ≥ 1, where A bounds A*(4n+2). |
| Theorem 3.3, polynomial consequence | `Houghton.dehn_poly_weighted` | The printed consequence: one real C bounds every null word by ⌊C·n^(log₂107+4)⌋. |
| Lemma 2.1, embedding | `Houghton.embeds_of_profile_lt` | The printed threshold profile(E,r) < 2r for r > 1. |
| Lemma 2.1, dichotomy | `Houghton.profile_bounded_or_ge` | The printed bounded-or-linear dichotomy; infinite profile uses the ENat convention. |
| Proposition 5.1 | `Houghton.dimension_perm` | The printed permutation dimension bound. |
| Johnson's presentation (unnumbered) | `Houghton.null_iff_areaLE` | The printed equivalence of a trivial ray action and finite relator area. |

The numbered wrappers are `PaperProofs.<suffix>`, with frozen types `PaperStatements.<suffix>`, for the suffixes `theorem_1_1`, `corollary_1_2`, `corollary_1_3`, `theorem_3_1`, `theorem_3_2`, `theorem_3_3`, `theorem_3_3_polynomial`, `lemma_2_1_embedding`, `lemma_2_1_dichotomy`, `proposition_5_1`, `johnson_presentation`.

**Conditional premise.** `PermSectorBound` can be proved inside the package, as `Houghton.permSectorBound_of_SSA Houghton.qit_commutingPinchingSSA`, but the selected Corollary 1.3 root and its wrapper keep it as a hypothesis. No named literature hypothesis is assumed: strong subadditivity is proved, as `Houghton.qit_commutingPinchingSSA`, and every row except Corollary 1.3 discharges it. `AXIOMS.txt` also lists the `_SSA` roots, which keep `hQ : QIT_CommutingPinchingSSA` as an explicit hypothesis. Historical comments in some source files (for example `Houghton/Final.lean`) describe earlier intermediate steps; they do not change the table.

**Conventions:** H₃ is realized in `(Perm Y)ᵐᵒᵖ` for the paper's right action, and models use Mathlib's product (`Houghton.modelSizesPaper_eq` proves that the model sizes agree). Approximate S₃ pairs are rounded as permutations by cycle truncation. The entropy results are finite dimensional, use natural logarithms and keep the positive-definiteness hypotheses shown in their types; no infinite-dimensional operator-entropy bridge is claimed.

**Not formalized:** the H_m (m > 3) and sharp image-structure clauses of Corollary 1.3; the structural clause of Corollary 1.2; Proposition 2.3, Lemma 2.4 and Proposition 2.5; Remark 2.2's representation description; Proposition 3.4; the general unitary statements of Theorem 1.4, Lemmas 4.2–4.3, Theorem 4.4 and Propositions 4.5–4.6 beyond their permutation specializations; Proposition 6.1 in full arbitrary-colour form; Proposition 6.2 for chunks other than E_H; Lemmas 6.3–6.4, Propositions 6.5–6.6 and Corollary 6.7; Proposition 7.1; the results of Section 8 (Theorems 8.1, 8.3 and 8.6, Corollary 8.2, Propositions 8.4–8.5) and their introductory restatements, Theorems 1.5–1.6; the spectral-radius refinement of Appendix A; Lemma 4.1 and Lemmas A.1–A.2 as numbered statements (only supporting source results exist); Remark 8.7.

The `verification/` package at the repository root is separate: it uses Lean 4.30.0 and checks finite certificate transcriptions and scalar recurrences (see `verification/README.md`).

## Trust base

- Lean 4.35.0 and Mathlib commit `56a005855ea17e0b0958f73ec801ae140b0a1679`. The pins are in `lean-toolchain`, `lake-manifest.json` and `UPSTREAM-PINS.json`; `LIBRARY-MODULES.txt` lists the vendored shared-library modules.
- Every declaration in the table and every numbered wrapper depends only on Lean's three standard axioms, `propext`, `Classical.choice` and `Quot.sound`. `AXIOMS.txt` is the exact axiom output.
- The proofs pass two independent kernel checkers, `leanchecker` and `nanoda`.
- `evidence/KERNEL-REPLAY.json` records the kernel replay (export digest, checker binaries, exits) and the run of the reproduce commands on 6 November 2026. `evidence/replay.sh` runs leanchecker over the vendored library modules only; it is not the two-checker replay recorded in `KERNEL-REPLAY.json`.

## Reproduce

With the pinned Lean toolchain on PATH, Git available for fetching the pinned dependencies, one compiler at a time and at least 4 GiB of free memory, run from `lean/`:

```sh
export LEAN_NUM_THREADS=1
lake exe cache get
lake build
lake env lean -j1 -M6144 Audit.lean
```

On Windows set `LEAN_NUM_THREADS` to `1` before the commands. `lake exe cache get` fetches the Mathlib build cache and `lake build` builds the core. `Audit.lean` prints the type of each checked declaration followed by its axioms; the axiom lines match `AXIOMS.txt`.

For the earlier certificate package, with Lean 4.30.0 on PATH, run from the repository root:

```sh
python build.py
python verification/check.py
```
