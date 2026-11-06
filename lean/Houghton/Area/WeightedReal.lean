import Houghton.Area.Weighted
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Base

/-! Theorem `thm:area-weighted` in the paper's form `A*(M) ≤ 135 · M^{log₂ 107}`. -/

namespace Houghton

lemma pow_log_le_rpow (M : ℕ) (hM : 1 ≤ M) :
    (107 : ℝ) ^ Nat.log 2 M ≤ (M : ℝ) ^ Real.logb 2 107 := by
  have h1 : (2 : ℝ) ^ Nat.log 2 M ≤ M := by exact_mod_cast Nat.pow_log_le_self 2 (by omega)
  have h2 : (2 : ℝ) ^ Real.logb 2 107 = 107 :=
    Real.rpow_logb (by norm_num) (by norm_num) (by norm_num)
  calc (107 : ℝ) ^ Nat.log 2 M = ((2 : ℝ) ^ Real.logb 2 107) ^ Nat.log 2 M := by rw [h2]
    _ = ((2 : ℝ) ^ Nat.log 2 M) ^ Real.logb 2 107 := by
      rw [← Real.rpow_natCast, ← Real.rpow_natCast, ← Real.rpow_mul (by norm_num),
        ← Real.rpow_mul (by norm_num)]
      congr 1
      ring
    _ ≤ (M : ℝ) ^ Real.logb 2 107 :=
      Real.rpow_le_rpow (by positivity) h1 (Real.logb_nonneg (by norm_num) (by norm_num))

/-- **Theorem `thm:area-weighted`**: `A*(M) ≤ 135 · M^{log₂ 107}` for every `M ≥ 1`. -/
theorem astar_le_weighted_rpow (M : ℕ) (hM : 1 ≤ M) :
    ∃ n : ℕ, AstarLE M n ∧ (n : ℝ) ≤ 135 * (M : ℝ) ^ Real.logb 2 107 :=
  ⟨135 * 107 ^ Nat.log 2 M, astar_le_weighted_log M, by
    push_cast
    exact mul_le_mul_of_nonneg_left (pow_log_le_rpow M hM) (by norm_num)⟩

end Houghton
