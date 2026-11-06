# FiniteLean source subset

This directory contains exactly the shared-library Lean modules listed in `../../LIBRARY-MODULES.txt`, with their certified bytes retained. It is an import closure for this paper rather than the full shared library. Build it through the enclosing `lean/` package with Lean 4.35.0 and the pinned Mathlib revision recorded there.

The entropy results in this snapshot are finite dimensional. `QIT.mlog`, `QIT.relEnt` and `Houghton.vN` use natural logarithms (nats). The relative-entropy conjugation, joint-convexity and partial-trace theorems have the positive-definiteness assumptions shown by their types; extended-valued relative entropy for arbitrary singular states is outside this snapshot. Strong subadditivity is proved for all finite Hermitian positive-semidefinite trace-one density matrices. `QIT.integralRep` proves the `IntegralRep` interface; `relEnt_jointlyConvex_of` retains that interface as an explicit, internally dischargeable premise. The two compatibility bridges preserve the retained finite-matrix definitions exactly. No infinite-dimensional operator-entropy bridge is claimed.

From the enclosing `lean/` directory:

```sh
export LEAN_NUM_THREADS=1
lake exe cache get
lake build
lake env lean -j1 -M6144 Audit.lean
```

The same serial compiler and memory limits described in `../../README.md` apply. Licensing follows `../../RIGHTS.md` and its referenced licence texts. This subset contains no project objects.
