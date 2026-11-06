import Houghton.Area.Main
import Houghton.Area.WeightedAlgebra
import Mathlib.Data.Nat.Log

/-! Theorem `thm:area-weighted`. Formal words in `t, q` (`0,1,2,3 = t,t⁻¹,q,q⁻¹`), value `evQ`.
Rules `d(t),d(q),o(t),o(q)` (cost `≤ 2315`, lengths `3,10,7,26`); `W_{2m} = d(W_m)`,
`W_{2m+1} = o(W_m)t`; `A_k + 29n_k ≤ 29·107^s` for `k < 2^{s+1}`. -/

namespace Houghton

open Word

/-- The value of a formal word in `t, q`. -/
abbrev evQ (w : List ℕ) : F := evF qW w

lemma evQ_0 : evQ [0] = t := evF_0 qW
lemma evQ_1 : evQ [1] = t⁻¹ := evF_1 qW
lemma evQ_2 : evQ [2] = σneg 2 := (evF_2 qW).trans ev_qW
lemma evQ_3 : evQ [3] = (σneg 2)⁻¹ := (evF_3 qW).trans (by rw [ev_qW])
lemma evQ_append (w₁ w₂ : List ℕ) : evQ (w₁ ++ w₂) = evQ w₁ * evQ w₂ := evF_append qW w₁ w₂
lemma evQ_cons (x : ℕ) (w : List ℕ) : evQ (x :: w) = evQ [x] * evQ w := evF_cons qW x w

theorem subst_wareaEq (f : F →* F) {u v : List ℕ} {c : ℕ} (hu : Syms u) (hv : Syms v)
    (ht : WAreaEq (f t) (evQ u) c) (hq : WAreaEq (f (σneg 2)) (evQ v) c) :
    ∀ W : List ℕ, Syms W → WAreaEq (f (evQ W)) (evQ (substS u v W)) (c * W.length) :=
  subst_gen WAreaEq (WAreaEq.refl 1) WAreaEq.mul WAreaEq.inv f hu hv ht (by rw [ev_qW]; exact hq)

/-! ### The four rules -/

lemma rule_dt : WAreaEq (ψ t) (evQ DTq) 2315 :=
  areaW_of_check chk_wdt (by rw [ev_append, ev_invW, ← ψ_ev tW (by decide), ev_tW, evQ, evF, symQ])
    wsum_rules.1

lemma rule_dq : WAreaEq (ψ (σneg 2)) (evQ DQq) 2315 :=
  areaW_of_check chk_wdq (by rw [ev_append, ev_invW, ← ψ_ev qW (by decide), ev_qW, evQ, evF, symQ])
    wsum_rules.2.1

lemma rule_ot : WAreaEq (conjB (ψ t)) (evQ OTq) 2315 :=
  areaW_of_check chk_wot
    (by rw [ev_append, ev_append, ev_append, ev_invW, ← ψ_ev tW (by decide), ev_tW,
      ev_singleton, ev_singleton, ltr_3, ltr_2, conjB_apply, evQ, evF, symQ])
    wsum_rules.2.2.1

lemma rule_oq : WAreaEq (conjB (ψ (σneg 2))) (evQ OQq) 2315 :=
  areaW_of_check chk_woq
    (by rw [ev_append, ev_append, ev_append, ev_invW, ← ψ_ev qW (by decide), ev_qW,
      ev_singleton, ev_singleton, ltr_3, ltr_2, conjB_apply, evQ, evF, symQ])
    wsum_rules.2.2.2

/-! ### The recursion -/

theorem even_stepW {m A : ℕ} {W : List ℕ} (hW : Syms W) (h : WAreaEq (X m) (evQ W) A) :
    WAreaEq (X (2 * m)) (evQ (substS DTq DQq W)) (107 * A + 2315 * W.length) := by
  have h1 : WAreaEq (X (2 * m)) (ψ (evQ W)) (107 * A) := by
    have := WAreaLE.psi h
    rw [map_mul, map_inv, ψ_X] at this
    exact this
  exact h1.trans (subst_wareaEq ψ (by decide) (by decide) rule_dt rule_dq W hW)

theorem odd_stepW {m A : ℕ} {W : List ℕ} (hW : Syms W) (h : WAreaEq (X m) (evQ W) A) :
    WAreaEq (X (2 * m + 1)) (evQ (substS OTq OQq W ++ [0])) (107 * A + 2315 * W.length) := by
  have h0 : WAreaEq (ψ (X m)) (ψ (evQ W)) (107 * A) := by
    have := WAreaLE.psi h
    rw [map_mul, map_inv] at this
    exact this
  have h1 : WAreaEq (conjB (ψ (X m))) (conjB (ψ (evQ W))) (107 * A) := by
    have := h0.conj b⁻¹
    rw [inv_inv] at this
    exact this
  have h2 := subst_wareaEq (conjB.comp ψ) (by decide) (by decide) rule_ot rule_oq W hW
  have h3 := (h1.trans h2).mul (WAreaEq.refl t)
  rw [X_odd, ← ψ_X, evQ_append, evQ_0]
  simpa using h3

/-- **The weighted doubling recursion**: for `1 ≤ n < 2^{s+1}`, `X_n = W_n` with
`A_n + 29 |W_n| ≤ 29 · 107^s`. -/
theorem rec_boundW (s : ℕ) : ∀ n, 1 ≤ n → n < 2 ^ (s + 1) →
    ∃ W : List ℕ, ∃ A : ℕ, Syms W ∧ 1 ≤ W.length ∧ WAreaEq (X n) (evQ W) A ∧
      A + 29 * W.length ≤ 29 * 107 ^ s := by
  induction s with
  | zero =>
    intro n h1 h2
    obtain rfl : n = 1 := by simp at h2; omega
    refine ⟨[0], 0, by decide, by simp, ?_, by simp⟩
    rw [evQ_0]
    exact WAreaEq.of_eq (by simp [X, t])
  | succ s ih =>
    intro n h1 h2
    have h107 : 107 ^ (s + 1) = 107 * 107 ^ s := pow_succ' 107 s
    have h2' : 2 ^ (s + 1 + 1) = 2 * 2 ^ (s + 1) := pow_succ' 2 (s + 1)
    rcases Nat.lt_or_ge n (2 ^ (s + 1)) with h3 | h3
    · obtain ⟨W, A, hW, hl, hX, hb⟩ := ih n h1 h3
      exact ⟨W, A, hW, hl, hX, by omega⟩
    · have hpos : 1 ≤ 2 ^ (s + 1) := Nat.one_le_two_pow
      obtain ⟨W, A, hW, hl, hX, hb⟩ := ih (n / 2) (by omega) (by omega)
      rcases Nat.mod_two_eq_zero_or_one n with hk | hk
      · have hn' : n = 2 * (n / 2) := by omega
        have hlu : (substS DTq DQq W).length ≤ 10 * W.length :=
          length_substS_le (by decide) (by decide) W
        refine ⟨substS DTq DQq W, 107 * A + 2315 * W.length, Syms.substS (by decide) (by decide) W,
          one_le_length_substS (by decide) (by decide) hl, ?_, by omega⟩
        rw [hn']; exact even_stepW hW hX
      · have hn' : n = 2 * (n / 2) + 1 := by omega
        have hlu : (substS OTq OQq W).length ≤ 26 * W.length :=
          length_substS_le (by decide) (by decide) W
        refine ⟨substS OTq OQq W ++ [0], 107 * A + 2315 * W.length,
          (Syms.substS (by decide) (by decide) W).append (by decide), by simp, ?_, ?_⟩
        · rw [hn']; exact odd_stepW hW hX
        · simp only [List.length_append, List.length_singleton]
          omega

/-! ### From `h_k` to far commutators -/

/-- `[α, W]` for a formal word `W` in `t, q` costs one original cell per letter. -/
theorem comm_α_evQ : ∀ W : List ℕ, Syms W → AreaLE (comm α (evQ W)) W.length
  | [], _ => by simpa using AreaLE.of_eq_one (show comm α (evQ []) = 1 by simp [comm])
  | x :: W, hW => by
    have hx : x < 4 := hW x (by simp)
    have ih := comm_α_evQ W (fun y hy => hW y (by simp [hy]))
    have hlet : AreaLE (comm α (evQ [x])) 1 := by
      rcases x with _ | _ | _ | _ | x
      · rw [evQ_0]; exact area_comm_α_t
      · rw [evQ_1]; exact area_comm_α_t.comm_inv_right
      · rw [evQ_2]; exact comm_σneg2_α.comm_symm
      · rw [evQ_3]; exact comm_σneg2_α.comm_symm.comm_inv_right
      · omega
    rw [evQ_cons, List.length_cons, Nat.add_comm]
    exact hlet.comm_mul_right ih

/-- `U(n) ≤ 2 A_n + n_n ≤ 58 · 107^s` for `1 ≤ n < 2^{s+1}`. -/
theorem area_U_weighted (s j : ℕ) (hj : 1 ≤ j) (hjs : j < 2 ^ (s + 1)) :
    AreaEq (σ j) (τ j) (58 * 107 ^ s) := by
  obtain ⟨W, A, hW, -, hX, hb⟩ := rec_boundW s j hj hjs
  have h1 : AreaEq (comm α (X j)) (comm α (evQ W)) (0 + A + 0 + A) :=
    (AreaEq.refl α).comm hX.toAreaEq
  have h2 := (AreaLE.of_areaEq h1 (comm_α_evQ W hW)).conj (b ^ j)
  rw [← τ_σ_eq] at h2
  exact (h2.inv.of_eq (by simp [mul_inv_rev])).mono (by omega)

/-- `A(j+2) ≤ 116 · 107^s + 18 j + 1 ≤ 135 · 107^s` for `1 ≤ j < 2^{s+1}`. -/
theorem area_A_weighted (s j : ℕ) (hj : 1 ≤ j) (hjs : j < 2 ^ (s + 1)) :
    AreaLE (comm (σ 0) (σ (j + 2))) (135 * 107 ^ s) := by
  refine (transfer (area_U_weighted s j hj hjs)).mono ?_
  rcases s with _ | s
  · simp at hjs; omega
  · have h107 : 107 ^ (s + 1) = 107 * 107 ^ s := pow_succ' 107 s
    have h2 : 2 ^ (s + 1 + 1) = 4 * 2 ^ s := by rw [pow_succ', pow_succ']; omega
    have h3 : 2 ^ s ≤ 107 ^ s := Nat.pow_le_pow_left (by decide) s
    omega

/-- **Theorem `thm:area-weighted`** (integer form): if `M < 2^{s+1}` (e.g. `s = ⌊log₂ M⌋`),
then `A*(M) ≤ 135 · 107^s`.  Since `107^{⌊log₂ M⌋} ≤ M^{log₂ 107}`, this gives the paper's
`A*(M) ≤ 135 · M^{log₂ 107}`.  (No hypothesis `M ≥ 2` is needed: for `M < 2` there is no far pair.) -/
theorem astar_le_weighted (M s : ℕ) (hs : M < 2 ^ (s + 1)) :
    AstarLE M (135 * 107 ^ s) := by
  apply astar_of_A
  intro d hd hdM
  rcases Nat.lt_or_ge d 3 with h | h
  · obtain rfl : d = 2 := by omega
    exact area_A2.mono (by have := Nat.one_le_pow s 107 (by decide); omega)
  · obtain ⟨j, rfl⟩ : ∃ j, d = j + 2 := ⟨d - 2, by omega⟩
    exact area_A_weighted s j (by omega) (by omega)

/-- **Theorem `thm:area-weighted`** with `s = ⌊log₂ M⌋`: `A*(M) ≤ 135 · 107^{⌊log₂ M⌋}`. -/
theorem astar_le_weighted_log (M : ℕ) : AstarLE M (135 * 107 ^ Nat.log 2 M) :=
  astar_le_weighted M (Nat.log 2 M) (Nat.lt_pow_succ_log_self (by decide) M)

end Houghton
