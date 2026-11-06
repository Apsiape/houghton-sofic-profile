import Houghton.Area.Recursion

/-! Theorem `thm:area`. Step (4): `U(n) = Area[α,X_n] ≤ 2Rw(n) + 5|W_n| ≤ 5n^{10}`; Lemma
`lem:transfer` (iv), `k = 2`: `A(j+2) ≤ 1 + 18j + 2U(j) ≤ (j+2)^{11}`. -/

namespace Houghton

open Word

/-! ### Step (4) -/

/-- `[α, W]` for a formal word `W` costs at most `5` cells per letter. -/
theorem comm_α_evS : ∀ W : List ℕ, Syms W → AreaLE (comm α (evS W)) (5 * W.length)
  | [], _ => by simpa using AreaLE.of_eq_one (show comm α (evS []) = 1 by simp [comm])
  | x :: W, hW => by
    have hx : x < 4 := hW x (by simp)
    have ih := comm_α_evS W (fun y hy => hW y (by simp [hy]))
    have hlet : AreaLE (comm α (evS [x])) 5 := by
      rcases x with _ | _ | _ | _ | x
      · rw [evS_0]; exact area_comm_α_t.mono (by decide)
      · rw [evS_1]; exact area_comm_α_t.comm_inv_right.mono (by decide)
      · rw [evS_2]; exact area_comm_α_ρ
      · rw [evS_3]; exact area_comm_α_ρ.comm_inv_right
      · omega
    rw [evS_cons, List.length_cons, Nat.mul_succ, Nat.add_comm]
    exact hlet.comm_mul_right ih

/-- `U(n) = Area[α, X_n] ≤ 2 Rw(n) + 5 |W_n| ≤ 5 n^{10}` for `n ≥ 1`. -/
theorem area_comm_α_X (n : ℕ) (hn : 1 ≤ n) : AreaLE (comm α (X n)) (5 * n ^ 10) := by
  obtain ⟨W, r, hW, -, hX, hb⟩ := rec_bound n hn
  have h1 : AreaEq (comm α (X n)) (comm α (evS W)) (0 + r + 0 + r) := (AreaEq.refl α).comm hX
  exact (AreaLE.of_areaEq h1 (comm_α_evS W hW)).mono (by omega)

/-! ### Lemma `lem:transfer` (iv) with `k = 2` -/

lemma τ_σ_eq (j : ℕ) : τ j * (σ j)⁻¹ = b ^ j * comm α (X j) * (b ^ j)⁻¹ := by
  simp [τ, σ, X, comm, mul_assoc, inv_pow]

/-- `σ_j = τ_j` modulo `U(j) ≤ 5 j^{10}` cells, since `b^{-j}(τ_j σ_j⁻¹)b^j = [α, X_j]` freely. -/
theorem area_U (j : ℕ) (hj : 1 ≤ j) : AreaEq (σ j) (τ j) (5 * j ^ 10) := by
  have h := (area_comm_α_X j hj).conj (b ^ j)
  rw [← τ_σ_eq] at h
  exact h.inv.of_eq (by simp [mul_inv_rev])

/-- `[σ_{-2}, α]` is a conjugate of `r₃`. -/
theorem comm_σneg2_α : AreaLE (comm (σneg 2) α) 1 := by
  have e : comm (σneg 2) α = a⁻¹ ^ 2 * rel 2 * (a⁻¹ ^ 2)⁻¹ := by
    simp [rel, r₃, comm, σneg, mul_assoc, pow_two]
  rw [e]
  exact (AreaLE.rel 2).conj _

/-- Moving `σ_{-2}` across the `2j` letters `b^{±1}` of `τ_j` (cost `B(2) ≤ 9` each) and across `α`. -/
theorem area_comm_σneg2_τ (j : ℕ) : AreaLE (comm (σneg 2) (τ j)) (18 * j + 1) := by
  have h1 := area_B2.comm_pow_right j
  have h2 := area_B2.comm_inv_right.comm_pow_right j
  have h := (h1.comm_mul_right comm_σneg2_α).comm_mul_right h2
  unfold τ
  exact h.mono (by omega)

lemma comm_conj (g x y : F) : comm (g * x * g⁻¹) (g * y * g⁻¹) = g * comm x y * g⁻¹ := by
  simp [comm, mul_assoc, mul_inv_rev]

lemma σ_add (p d : ℕ) : σ (p + d) = a ^ p * σ d * (a ^ p)⁻¹ := by
  rw [σ, σ, pow_add, Nat.add_comm p d, pow_add]
  simp [inv_pow, mul_assoc]

/-- **Lemma `lem:transfer` (iv) with `k = 2`**: `A(j+2) ≤ A(2) + 2j B(2) + 2U(j)`, where `U` bounds
the cost of `σ_j = τ_j`. -/
theorem transfer {j U : ℕ} (hU : AreaEq (σ j) (τ j) U) :
    AreaLE (comm (σ 0) (σ (j + 2))) (2 * U + 18 * j + 1) := by
  have h1 : AreaEq (comm (σneg 2) (σ j)) (comm (σneg 2) (τ j)) (0 + U + 0 + U) :=
    (AreaEq.refl _).comm hU
  have h2 := (AreaLE.of_areaEq h1 (area_comm_σneg2_τ j)).conj (a ^ 2)
  have e0 : σ 0 = a ^ 2 * σneg 2 * (a ^ 2)⁻¹ := by
    simp [σ, σneg, mul_assoc, inv_pow]
  have e : a ^ 2 * comm (σneg 2) (σ j) * (a ^ 2)⁻¹ = comm (σ 0) (σ (j + 2)) := by
    rw [e0, Nat.add_comm j 2, σ_add, comm_conj]
  rw [e] at h2
  exact h2.mono (by omega)

/-- `A(j+2) ≤ A(2) + 2j B(2) + 2U(j) ≤ 10 j^{10} + 18 j + 1`. -/
theorem area_A_succ_succ (j : ℕ) (hj : 1 ≤ j) :
    AreaLE (comm (σ 0) (σ (j + 2))) (10 * j ^ 10 + 18 * j + 1) :=
  (transfer (area_U j hj)).mono (by omega)

/-! ### The numerical bound -/

lemma key_ineq (j : ℕ) : 10 * j ^ 10 + 18 * j + 1 ≤ (j + 2) ^ 11 := by
  rcases Nat.lt_or_ge j 11 with h | h
  · have hs : ∀ k < 11, 10 * k ^ 10 + 18 * k + 1 ≤ (k + 2) ^ 11 := by decide +kernel
    exact hs j h
  · have h1 : j ^ 10 ≤ (j + 2) ^ 10 := Nat.pow_le_pow_left (by omega) 10
    have h2 : (j + 2) ^ 11 = j * (j + 2) ^ 10 + 2 * (j + 2) ^ 10 := by
      rw [pow_succ', Nat.add_mul]
    have h3 : j ^ 2 ≤ j ^ 10 := Nat.pow_le_pow_right (by omega) (by decide)
    have h4 : 11 * j ^ 10 ≤ j * j ^ 10 := Nat.mul_le_mul_right _ h
    have h5 : j * j ^ 10 ≤ j * (j + 2) ^ 10 := Nat.mul_le_mul_left _ h1
    have h6 : 11 * j ≤ j ^ 2 := by rw [pow_two]; exact Nat.mul_le_mul_right _ h
    omega

/-- `A(d) ≤ d^{11}` for every `d ≥ 2`. -/
theorem area_A (d : ℕ) (hd : 2 ≤ d) : AreaLE (comm (σ 0) (σ d)) (d ^ 11) := by
  rcases Nat.lt_or_ge d 3 with h | h
  · obtain rfl : d = 2 := by omega
    exact area_A2.mono (by decide)
  · obtain ⟨j, rfl⟩ : ∃ j, d = j + 2 := ⟨d - 2, by omega⟩
    exact (area_A_succ_succ j (by omega)).mono (key_ineq j)

lemma AreaLE.comm_signs {x y : F} {n : ℕ} (h : AreaLE (comm x y) n) (e₁ e₂ : Bool) :
    AreaLE (comm (if e₁ then x else x⁻¹) (if e₂ then y else y⁻¹)) n := by
  cases e₁ <;> cases e₂ <;> simp only [Bool.false_eq_true, ↓reduceIte]
  · exact h.comm_inv_right.comm_inv_left
  · exact h.comm_inv_left
  · exact h.comm_inv_right
  · exact h

/-- Reduction of `A*(M)` to the commutators `[σ₀, σ_d]`, `2 ≤ d ≤ M` (conjugation by `a^p`,
`[x,y]⁻¹ = [y,x]`, and the sign changes `[x⁻¹,y] = x⁻¹[y,x]x`, `[x,y⁻¹] = y⁻¹[y,x]y`). -/
theorem astar_of_A {M n : ℕ} (hA : ∀ d, 2 ≤ d → d ≤ M → AreaLE (comm (σ 0) (σ d)) n) :
    AstarLE M n := by
  intro p q hp hq hpq e₁ e₂
  have key : ∀ p q, q ≤ M → p + 2 ≤ q → AreaLE (comm (σ p) (σ q)) n := by
    intro p q hq h
    obtain ⟨d, rfl⟩ : ∃ d, q = p + d := ⟨q - p, by omega⟩
    have h1 := (hA d (by omega) (by omega)).conj (a ^ p)
    have e0 : σ p = a ^ p * σ 0 * (a ^ p)⁻¹ := by
      have := σ_add p 0
      simpa using this
    rw [← comm_conj, ← e0, ← σ_add] at h1
    exact h1
  rcases hpq with h | h
  · exact (key p q hq h).comm_signs e₁ e₂
  · exact (key q p hp h).comm_symm.comm_signs e₁ e₂

set_option linter.unusedVariables false in
/-- **Theorem `thm:area`** (Douglas–Mghirbi): `A*(M) ≤ M¹¹` for every `M ≥ 2` (`hM` is not
needed: for `M < 2` there is no far pair). -/
theorem astar_le_pow (M : ℕ) (hM : 2 ≤ M) : AstarLE M (M ^ 11) :=
  astar_of_A fun d hd hdM => (area_A d hd).mono (Nat.pow_le_pow_left hdM 11)

end Houghton
