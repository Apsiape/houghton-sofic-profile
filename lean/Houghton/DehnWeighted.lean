import Houghton.DehnFinal
import Houghton.Area.WeightedReal

/-! Theorem `thm:dehn` with Theorem `thm:area-weighted`: `δ_P(n) = O(n^{log₂107 + 4})`. -/

namespace Houghton

/-- **Corollary** (`thm:area-weighted` + `thm:dehn`): `δ_P(n) ≤ C n^{log₂ 107 + 4}`, with
`C = 400 + 54000 · 6^{log₂ 107}`. -/
theorem dehn_poly_weighted : ∃ C : ℝ, ∀ n : ℕ, 1 ≤ n → ∀ w : F, w.toWord.length ≤ n → ρH w = 1 →
    AreaLE w ⌊C * (n : ℝ) ^ (Real.logb 2 107 + 4)⌋₊ := by
  set p := Real.logb 2 107 with hp
  have hp0 : 0 ≤ p := Real.logb_nonneg (by norm_num) (by norm_num)
  refine ⟨400 + 400 * 135 * (6 : ℝ) ^ p, fun n hn w hw h1 => ?_⟩
  obtain ⟨m, hm, hmle⟩ := astar_le_weighted_rpow (4 * n + 2) (by omega)
  refine (dehn_bound n hn w hw h1 m hm).mono (Nat.le_floor ?_)
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := by linarith
  have hM : ((4 * n + 2 : ℕ) : ℝ) ≤ 6 * n := by push_cast; linarith
  have hMp : ((4 * n + 2 : ℕ) : ℝ) ^ p ≤ (6 : ℝ) ^ p * (n : ℝ) ^ p := by
    rw [← Real.mul_rpow (by norm_num) hn0.le]
    exact Real.rpow_le_rpow (by positivity) hM hp0
  have hnp : (1 : ℝ) ≤ (n : ℝ) ^ p := Real.one_le_rpow hn' hp0
  have hsplit : (n : ℝ) ^ (p + 4) = (n : ℝ) ^ p * (n : ℝ) ^ 4 := by
    rw [Real.rpow_add hn0, show (4 : ℝ) = ((4 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  have hm' : (m : ℝ) ≤ 135 * ((6 : ℝ) ^ p * (n : ℝ) ^ p) := le_trans hmle (by gcongr)
  have hn4 : (0 : ℝ) ≤ (n : ℝ) ^ 4 := by positivity
  push_cast
  rw [hsplit]
  have h6 : (0 : ℝ) ≤ (6 : ℝ) ^ p := by positivity
  nlinarith [mul_le_mul_of_nonneg_left hm' hn4, mul_le_mul_of_nonneg_left hnp hn4]

end Houghton
