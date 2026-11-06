import Houghton.Final
import Houghton.Analysis.SectorGen

/-!
# Theorem 1.1 and Corollary 1.2 of "Houghton's group H3 has superpolynomial sofic profile"

Douglas–Mghirbi, v1.2.0.  Everything is proved in Lean except one textbook theorem of
finite-dimensional quantum information, taken as the explicit hypothesis
`hQ : QIT_CommutingPinchingSSA` (`Houghton/Analysis/SectorQIT.lean`): for pairwise commuting
complete families of orthogonal projections `P₀, …, P_{m-1}` on `ℂ^ι` and every density matrix `ρ`,
`S(Π₀ ⋯ Π_{m-1} ρ) - S(ρ) ≤ ∑ₖ (S(Πₖ ρ) - S(ρ))`, where `Πₖ X = ∑ₐ Pₖₐ X Pₖₐ` and `S` is von
Neumann entropy in nats (`vN`, computed from `Matrix.IsHermitian.eigenvalues`; it is `0` on
non-Hermitian matrices, but it is only applied to density matrices and their pinchings).  This is
strong subadditivity in its commuting-conditional-expectation form (Lieb–Ruskai 1973; it follows
from Lindblad–Uhlmann monotonicity of relative entropy).  The upper bound does not use `hQ`.

`permSectorBound_of_SSA` shows that the earlier interface `PermSectorBound`, used by
`Houghton/Final.lean`, is itself a consequence of `hQ`; the theorems below supersede
`Final.theorem_1_1` and `Final.corollary_1_2`.

The profile `σ_{E_H}(r)` is `ℕ∞`-valued (`⊤` if no model exists); the statements below include
that it is finite for every `r ≥ 2`, so none of them is vacuous.
-/

namespace Houghton

/-- Proposition `prop:dimension-perm`, from strong subadditivity. -/
theorem dimensionPermStatement_of_SSA (hQ : QIT_CommutingPinchingSSA.{0}) :
    DimensionPermStatement :=
  fun φ δ h1 h2 N A h3 h4 h5 => dimension_perm_of_SSA hQ φ δ h1 h2 N A h3 h4 h5

/-- The sector bound `PermSectorBound` (the permutation form of Theorem `thm:phase-robust`),
from strong subadditivity. -/
theorem permSectorBound_of_SSA (hQ : QIT_CommutingPinchingSSA.{0}) : PermSectorBound.{0} :=
  permSectorBound_of_entropy
    (permSectorEntropy_of_QIT hQ subStateEntropy (subTwirlEntropy_of_gen genTwirlBound)
      subSectorEntropy)

/-- For `r ≥ 2` the profile `σ_{E_H}(r)` is finite (by the upper bound). -/
theorem profile_finite (r : ℝ) (hr : 2 ≤ r) :
    ∃ m : ℕ, profile E_H r = m ∧ (m : ℝ) ≤ 2 ^ (7000 * √r * Real.logb 2 r) := by
  obtain ⟨n, hn, hnle⟩ := profile_upper r hr
  have hfin : profile E_H r ≠ ⊤ := ne_top_of_le_ne_top (ENat.natCast_ne_top n) hn
  refine ⟨(profile E_H r).toNat, (ENat.coe_toNat hfin).symm, ?_⟩
  have hmn : (profile E_H r).toNat ≤ n := by
    have h := hn
    rw [← ENat.coe_toNat hfin] at h
    exact_mod_cast h
  exact le_trans (by exact_mod_cast hmn) hnle

/-- **Theorem 1.1.** For every `r ≥ 2`, `σ_{E_H}(r)` is a natural number `m` with
`2^{r^{1/(log₂107+1)}/1280 - 1/16} ≤ m`, `2^{r^{1/12}/270 - 1/16} ≤ m` (the unweighted bound from
certified finite fillings) and `m ≤ 2^{7000 √r log₂ r}`. -/
theorem theorem_1_1_SSA (hQ : QIT_CommutingPinchingSSA.{0}) (r : ℝ) (hr : 2 ≤ r) :
    ∃ m : ℕ, profile E_H r = m ∧
      (2:ℝ) ^ (r ^ (1 / (Real.logb 2 107 + 1)) / 1280 - 1 / 16) ≤ m ∧
      (2:ℝ) ^ (r ^ ((1:ℝ) / 12) / 270 - 1 / 16) ≤ m ∧
      (m : ℝ) ≤ 2 ^ (7000 * √r * Real.logb 2 r) := by
  obtain ⟨m, hm, hup⟩ := profile_finite r hr
  exact ⟨m, hm,
    profile_lower_weighted (dimensionPermStatement_of_SSA hQ) weightedAreaStatement hr m hm,
    profile_lower_unweighted (dimensionPermStatement_of_SSA hQ) areaStatement hr m hm, hup⟩

/-- **Theorem 1.1, upper bound** (unconditional). -/
theorem theorem_1_1_upper (r : ℝ) (hr : 2 ≤ r) :
    ∃ m : ℕ, profile E_H r = m ∧ (m : ℝ) ≤ 2 ^ (7000 * √r * Real.logb 2 r) :=
  profile_finite r hr

/-- **Corollary 1.2.** The (finite) profile of the chunk `E_H` of `H₃` is not bounded by any
polynomial: for all `k, C` there is `r ≥ 2` with `σ_{E_H}(r) > C r^k`. -/
theorem corollary_1_2_SSA (hQ : QIT_CommutingPinchingSSA.{0}) :
    ∀ k C : ℝ, ∃ r : ℝ, 2 ≤ r ∧ ∃ m : ℕ, profile E_H r = m ∧ C * r ^ k < m := by
  intro k C
  obtain ⟨r, hr, h⟩ := not_polynomially_bounded (dimensionPermStatement_of_SSA hQ) areaStatement k C
  obtain ⟨m, hm, -⟩ := profile_finite r hr
  exact ⟨r, hr, m, hm, h m hm⟩

end Houghton
