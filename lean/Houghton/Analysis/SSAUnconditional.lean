import FiniteLean.QIT.Entropy.SSAUnconditional
import FiniteLean.QIT.Entropy.SSAGain
import Houghton.Analysis.SectorGen
import Houghton.Headline
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog

/-!
# Step (6): extension to all density matrices, and the final statements

`vN((1-ε)X + (ε/d)·1) = ∑ᵢ η((1-ε)λᵢ(X) + ε/d)` (functional calculus), pinchings are affine and
fix `1`, and `ε ↦ η(...)` is continuous; the SSA inequality for the positive definite states
`ρ_ε = (1-ε)ρ + (ε/d)·1` passes to `ε = 0`.

Final statements: `theorem_1_1` and `corollary_1_2` with only the joint convexity and unitary invariance of relative entropy
(`QIT_RelEntJointlyConvex`, `QIT_RelEntUnitaryInvariant`) as hypotheses.
-/

namespace Houghton

/-- **Theorem 1.1** of Douglas–Mghirbi, assuming only `QIT.relEnt_jointlyConvex_of QIT.integralRep` and `QIT.relEnt_unitary_conj`. -/
theorem theorem_1_1_relEnt (hJ : QIT_RelEntJointlyConvex) (hU : QIT_RelEntUnitaryInvariant)
    (r : ℝ) (hr : 2 ≤ r) :
    ∃ m : ℕ, profile E_H r = m ∧
      (2:ℝ) ^ (r ^ (1 / (Real.logb 2 107 + 1)) / 1280 - 1 / 16) ≤ m ∧
      (2:ℝ) ^ (r ^ ((1:ℝ) / 12) / 270 - 1 / 16) ≤ m ∧
      (m : ℝ) ≤ 2 ^ (7000 * √r * Real.logb 2 r) :=
  theorem_1_1_SSA (qit_commutingPinchingSSA_of hJ hU) r hr

/-- **Corollary 1.2** of Douglas–Mghirbi, assuming only `QIT.relEnt_jointlyConvex_of QIT.integralRep` and `QIT.relEnt_unitary_conj`. -/
theorem corollary_1_2_relEnt (hJ : QIT_RelEntJointlyConvex) (hU : QIT_RelEntUnitaryInvariant) :
    ∀ k C : ℝ, ∃ r : ℝ, 2 ≤ r ∧ ∃ m : ℕ, profile E_H r = m ∧ C * r ^ k < m :=
  corollary_1_2_SSA (qit_commutingPinchingSSA_of hJ hU)

/-- `prop:dimension-perm` with exactly the target signature, assuming only `QIT.relEnt_jointlyConvex_of QIT.integralRep` and `QIT.relEnt_unitary_conj`. -/
theorem dimension_perm_of_relEnt (hJ : QIT_RelEntJointlyConvex) (hU : QIT_RelEntUnitaryInvariant)
    {Ω : Type} [Fintype Ω] [DecidableEq Ω] (φ : F →* Equiv.Perm Ω) (δ : ℝ)
    (hrel : ∀ i, dH (φ (rel i)) 1 ≤ δ) (hγ : 1/2 ≤ dH (φ γ) 1) (N A : ℕ) (hN : 1 ≤ N)
    (hA : AstarLE (3 * N) A) (hδ : (10:ℝ)^8 * N * max 1 A * δ ≤ 1) :
    (N : ℝ) / 16 ≤ Real.logb 2 (Fintype.card Ω) :=
  dimension_perm_of_SSA (qit_commutingPinchingSSA_of hJ hU) φ δ hrel hγ N A hN hA hδ

end Houghton
