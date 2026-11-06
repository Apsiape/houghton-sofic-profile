import Houghton.Area.Main

/-! The paper's constants: `|W_n| ≤ 323^s`, `541·Rw(n) ≤ 728·(864^s - 323^s)` for `n < 2^{s+1}`. -/

namespace Houghton

open Word

/-- **The paper's bound for the doubling recursion** (`Rw(n) ≤ 728/541 · 864^s`, `|W_n| ≤ 323^s`). -/
theorem rec_bound_sharp (s : ℕ) : ∀ n, 1 ≤ n → n < 2 ^ (s + 1) →
    ∃ W : List ℕ, ∃ r : ℕ, Syms W ∧ 1 ≤ W.length ∧ AreaEq (X n) (evS W) r ∧
      W.length ≤ 323 ^ s ∧ 541 * r ≤ 728 * (864 ^ s - 323 ^ s) := by
  induction s with
  | zero =>
    intro n h1 h2
    obtain rfl : n = 1 := by simp at h2; omega
    refine ⟨[0], 0, by decide, by simp, ?_, by simp, by simp⟩
    rw [evS_0]
    exact AreaEq.of_eq (by simp [X, t])
  | succ s ih =>
    intro n h1 h2
    have hP : 864 ^ (s + 1) = 864 * 864 ^ s := pow_succ' 864 s
    have hQ : 323 ^ (s + 1) = 323 * 323 ^ s := pow_succ' 323 s
    have hQP : 323 ^ s ≤ 864 ^ s := Nat.pow_le_pow_left (by decide) s
    have hQ1 : 1 ≤ 323 ^ s := Nat.one_le_pow _ _ (by decide)
    have h2' : 2 ^ (s + 1 + 1) = 2 * 2 ^ (s + 1) := pow_succ' 2 (s + 1)
    rcases Nat.lt_or_ge n (2 ^ (s + 1)) with h3 | h3
    · obtain ⟨W, r, hW, hl, hX, hlb, hb⟩ := ih n h1 h3
      exact ⟨W, r, hW, hl, hX, by omega, by omega⟩
    · have hpos : 1 ≤ 2 ^ (s + 1) := Nat.one_le_two_pow
      obtain ⟨W, r, hW, hl, hX, hlb, hb⟩ := ih (n / 2) (by omega) (by omega)
      set m := n / 2 with hm
      set W' := substS [0, 2, 0] RS W with hW'
      have hX' := even_step hW hX
      have hl'u : W'.length ≤ 46 * W.length := length_substS_le (by decide) (by decide) W
      have hl'l : 1 ≤ W'.length := one_le_length_substS (by decide) (by decide) hl
      have hW'S : Syms W' := Syms.substS (by decide) syms_RS W
      rcases Nat.mod_two_eq_zero_or_one n with hk | hk
      · have hn' : n = 2 * m := by omega
        refine ⟨W', 864 * r + 84 * W.length, hW'S, hl'l, ?_, by omega, by omega⟩
        rw [hn']; exact hX'
      · have hn' : n = 2 * m + 1 := by omega
        set W'' := substS [0, 2] RpS W' ++ [0] with hW''
        have hX'' := odd_step hW'S hX'
        have hl''u : W''.length ≤ 7 * W'.length + 1 := by
          have := length_substS_le (u := [0, 2]) (v := RpS) (L := 7) (by decide) (by decide) W'
          simp only [hW'', List.length_append, List.length_singleton]
          omega
        refine ⟨W'', 864 * r + 84 * W.length + 14 * W'.length,
          (Syms.substS (by decide) syms_RpS W').append (by decide), by simp [hW''], ?_, by omega,
          by omega⟩
        rw [hn']; exact hX''

/-- `U(n) = Area[α, X_n] ≤ 2 Rw(n) + 5 |W_n|` with the sharp bounds on `Rw(n)` and `|W_n|`. -/
theorem area_comm_α_X_sharp (s n : ℕ) (hn : 1 ≤ n) (hns : n < 2 ^ (s + 1)) :
    ∃ r : ℕ, 541 * r ≤ 728 * 864 ^ s ∧ AreaLE (comm α (X n)) (2 * r + 5 * 323 ^ s) := by
  obtain ⟨W, r, hW, -, hX, hlb, hb⟩ := rec_bound_sharp s n hn hns
  refine ⟨r, by omega, ?_⟩
  have h1 : AreaEq (comm α (X n)) (comm α (evS W)) (0 + r + 0 + r) := (AreaEq.refl α).comm hX
  exact (AreaLE.of_areaEq h1 (comm_α_evS W hW)).mono (by omega)

/-- `A(j+2) ≤ 2U(j) + 18 j + 1 ≤ 4 Rw(j) + 10 · 323^s + 18 j + 1` with `541 Rw(j) ≤ 728 · 864^s`
(the paper: `A(m) ≤ 5.39 m^{log₂ 864} + 10 m^{log₂ 323} + 18 m`). -/
theorem area_A_sharp (s j : ℕ) (hj : 1 ≤ j) (hjs : j < 2 ^ (s + 1)) :
    ∃ r : ℕ, 541 * r ≤ 728 * 864 ^ s ∧
      AreaLE (comm (σ 0) (σ (j + 2))) (4 * r + 10 * 323 ^ s + 18 * j + 1) := by
  obtain ⟨r, hr, h⟩ := area_comm_α_X_sharp s j hj hjs
  refine ⟨r, hr, ?_⟩
  have hU : AreaEq (σ j) (τ j) (2 * r + 5 * 323 ^ s) := by
    have h2 := h.conj (b ^ j)
    rw [← τ_σ_eq] at h2
    exact h2.inv.of_eq (by simp [mul_inv_rev])
  exact (transfer hU).mono (by omega)

end Houghton
