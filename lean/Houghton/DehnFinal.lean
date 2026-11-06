import Houghton.DehnCoxeter
import Mathlib.Tactic.Ring

/-! Theorem `thm:dehn`: `δ_P(n) ≤ 400 n⁴ (1 + A*(4n+2))`, and the unweighted corollary
`δ_P(n) = O(n¹⁵)`. -/

namespace Houghton

lemma astarLE_mono_M {M M' A : ℕ} (h : AstarLE M A) (hM : M' ≤ M) : AstarLE M' A :=
  fun p q hp hq hpq e₁ e₂ => h p q (by omega) (by omega) hpq e₁ e₂

/-- **Theorem `thm:dehn`** (Douglas–Mghirbi): a null word of reduced length `≤ n` has area at most
`400 n⁴ (1 + A)` whenever `A*(4n+2) ≤ A`. -/
theorem dehn_bound (n : ℕ) (hn : 1 ≤ n) (w : F) (hw : w.toWord.length ≤ n) (h1 : ρH w = 1)
    (A : ℕ) (hA : AstarLE (4 * n + 2) A) : AreaLE w (400 * n ^ 4 * (1 + A)) := by
  have h := dehn_bound_of_coxeter n w hw h1 A _ (astarLE_mono_M hA (by omega))
    (coxeterFill (astarLE_mono_M hA (show 4 * n ≤ 4 * n + 2 by omega)))
  refine h.mono ?_
  have key : n * (2 * n + 2 * n * ((1 + A) * (2 * n) ^ 2)) +
      n * (2 * n + 1) * (1 + (4 * n + 1) * ((4 * n + 1) * A + 4)) =
      8 * n ^ 4 + 32 * n ^ 3 + 28 * n ^ 2 + 5 * n +
        (40 * (n ^ 4 * A) + 32 * (n ^ 3 * A) + 10 * (n ^ 2 * A) + n * A) := by ring
  have e : 400 * n ^ 4 * (1 + A) = 400 * n ^ 4 + 400 * (n ^ 4 * A) := by ring
  have p1 : n ≤ n ^ 2 := by simpa using Nat.pow_le_pow_right hn (show 1 ≤ 2 by omega)
  have p2 : n ^ 2 ≤ n ^ 3 := Nat.pow_le_pow_right hn (by omega)
  have p3 : n ^ 3 ≤ n ^ 4 := Nat.pow_le_pow_right hn (by omega)
  have q1 : n * A ≤ n ^ 2 * A := Nat.mul_le_mul_right _ p1
  have q2 : n ^ 2 * A ≤ n ^ 3 * A := Nat.mul_le_mul_right _ p2
  have q3 : n ^ 3 * A ≤ n ^ 4 * A := Nat.mul_le_mul_right _ p3
  rw [key, e]
  omega

/-- **Corollary** (`thm:area` + `thm:dehn`): `δ_P(n) ≤ C n¹⁵`, with `C = 400 (1 + 6¹¹)`. -/
theorem dehn_poly15 : ∃ C : ℕ, ∀ n : ℕ, 1 ≤ n → ∀ w : F, w.toWord.length ≤ n → ρH w = 1 →
    AreaLE w (C * n ^ 15) := by
  refine ⟨400 * (1 + 6 ^ 11), fun n hn w hw h1 => ?_⟩
  have h := dehn_bound n hn w hw h1 _ (astar_le_pow (4 * n + 2) (by omega))
  refine h.mono ?_
  have h6 : (4 * n + 2) ^ 11 ≤ 6 ^ 11 * n ^ 11 := by
    rw [← mul_pow]; exact Nat.pow_le_pow_left (by omega) 11
  have hn11 : 1 ≤ n ^ 11 := Nat.one_le_pow _ _ (by omega)
  have e1 : 400 * n ^ 4 * (1 + (4 * n + 2) ^ 11) = 400 * n ^ 4 + 400 * (n ^ 4 * (4 * n + 2) ^ 11) := by
    ring
  have e2 : 400 * (1 + 6 ^ 11) * n ^ 15 = 400 * (n ^ 4 * n ^ 11) + 400 * 6 ^ 11 * (n ^ 4 * n ^ 11) := by
    ring
  have b1 : n ^ 4 ≤ n ^ 4 * n ^ 11 := Nat.le_mul_of_pos_right _ hn11
  have b2 : n ^ 4 * (4 * n + 2) ^ 11 ≤ 6 ^ 11 * (n ^ 4 * n ^ 11) := by
    calc n ^ 4 * (4 * n + 2) ^ 11 ≤ n ^ 4 * (6 ^ 11 * n ^ 11) := Nat.mul_le_mul_left _ h6
      _ = 6 ^ 11 * (n ^ 4 * n ^ 11) := by ring
  rw [e1, e2]
  omega

/-- **Johnson's presentation** (a by-product): a word is trivial in `H₃` iff it is a product of
conjugates of `r₁, …, r₅`, i.e. `⟨a, b, α | r₁, …, r₅⟩` presents `H₃`. -/
theorem null_iff_areaLE (w : F) : ρH w = 1 ↔ ∃ n, AreaLE w n := by
  constructor
  · intro h1
    obtain ⟨C, hC⟩ := dehn_poly15
    exact ⟨_, hC (max 1 w.toWord.length) (le_max_left _ _) w (le_max_right _ _) h1⟩
  · rintro ⟨n, h⟩
    exact rho_of_areaLE h

end Houghton
