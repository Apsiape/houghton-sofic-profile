import Houghton.Basic
import Mathlib.Tactic.SplitIfs
import Mathlib.Data.ZMod.Basic

/-!
# Section 6 (partial): corner models

Formalized here: the cycle identities from the proof of Proposition `prop:corner`, the recursion
for the top-row permutations `D_i`, and the corner-model action of `a, b, α` on states
`(i, j, x)` (clocks in `ℤ/M`, colourings `x : ℕ → S` of the coordinates), with the exactness of
`r₁, r₂, r₃, r₅` at every clock and of `r₄` at every clock except `(M - 1, M - 1)`.
**Not** formalized: the restriction to the finite set `Ω_{M,s}` and the resulting Hamming
estimates, the computation of `R_M` at the corner, the far-commutator and short-word estimates, and
Proposition `prop:sofic-upper`.

Coordinates are the paper's `1, …, L`, embedded in `ℕ` (points outside are fixed). Products are
read from left to right as in the paper, so `t · (π₁ π₂) = π₂ (π₁ t)` for these functions.
* `cyc r` is the reverse cycle `c_r = (1 r r-1 ⋯ 2)`: `1 ↦ r`, `k ↦ k - 1` for `2 ≤ k ≤ r`;
* `cycInv r` is `c_r⁻¹`; `swp a b` is the transposition `(a b)`, and `τ = swp 1 2`.
-/

namespace Houghton.Corner

/-- The reverse cycle `c_r = (1 r r-1 ⋯ 2)`. -/
def cyc (r k : ℕ) : ℕ := if k = 1 then r else if 2 ≤ k ∧ k ≤ r then k - 1 else k

/-- `c_r⁻¹`. -/
def cycInv (r k : ℕ) : ℕ := if k = r then 1 else if 1 ≤ k ∧ k < r then k + 1 else k

/-- The transposition `(a b)`. -/
def swp (a b k : ℕ) : ℕ := if k = a then b else if k = b then a else k

theorem cycInv_cyc (r k : ℕ) (hr : 2 ≤ r) : cycInv r (cyc r k) = k := by
  unfold cyc cycInv; split_ifs <;> omega

theorem cyc_cycInv (r k : ℕ) (hr : 2 ≤ r) : cyc r (cycInv r k) = k := by
  unfold cyc cycInv; split_ifs <;> omega

/-- `c_r τ c_r⁻¹ = (2 3)` for `r ≥ 4`. -/
theorem conj_tau (r k : ℕ) (hr : 4 ≤ r) : cycInv r (swp 1 2 (cyc r k)) = swp 2 3 k := by
  unfold cyc cycInv swp; split_ifs <;> omega

/-- `c_r (2 3) c_r⁻¹ = (3 4)` for `r ≥ 4`. -/
theorem conj_23 (r k : ℕ) (hr : 4 ≤ r) : cycInv r (swp 2 3 (cyc r k)) = swp 3 4 k := by
  unfold cyc cycInv swp; split_ifs <;> omega

/-- Equation `eq:corner-id`: `c_r c_t c_{r-1}⁻¹ c_t⁻¹ = τ` for `3 ≤ r < t`. -/
theorem corner_id (r t k : ℕ) (hr : 3 ≤ r) (hrt : r < t) :
    cycInv t (cycInv (r - 1) (cyc t (cyc r k))) = swp 1 2 k := by
  unfold cyc cycInv swp; split_ifs <;> omega

/-- The top-row colour permutations `D_i` of `eq:corner-rec` (with `ℓ = 2M + 2`):
`D_0 = c_{2ℓ-M+1}`, `D_{i+1} = c_{ℓ-i-(M-1)}⁻¹ τ D_i c_{ℓ-i}` (left to right). -/
def D (M : ℕ) : ℕ → ℕ → ℕ
  | 0 => cyc (2 * (2 * M + 2) - M + 1)
  | i + 1 => fun k => cyc (2 * M + 2 - i) (D M i (swp 1 2 (cycInv (2 * M + 2 - i - (M - 1)) k)))

/-- `D_i(t) = t - 1` for `2 ≤ t ≤ M + 3 - i` (proof of Proposition `prop:corner`). -/
theorem D_apply (M : ℕ) (hM : 2 ≤ M) :
    ∀ i, i ≤ M - 1 → ∀ t, 2 ≤ t → t ≤ M + 3 - i → D M i t = t - 1 := by
  intro i
  induction i with
  | zero =>
    intro _ t ht1 ht2
    simp only [D, cyc]
    split_ifs <;> omega
  | succ i ih =>
    intro hi t ht1 ht2
    simp only [D]
    have h1 : cycInv (2 * M + 2 - i - (M - 1)) t = t + 1 := by
      unfold cycInv; split_ifs <;> omega
    have h2 : swp 1 2 (t + 1) = t + 1 := by
      unfold swp; split_ifs <;> omega
    rw [h1, h2, ih (by omega) (t + 1) (by omega) (by omega)]
    unfold cyc; split_ifs <;> omega

/-- Hence `D_i⁻¹(1) = 2` and `D_i⁻¹(2) = 3`, i.e. `D_i τ D_i⁻¹ = (2 3)` on the top row. -/
theorem D_two_three (M : ℕ) (hM : 2 ≤ M) (i : ℕ) (hi : i ≤ M - 1) :
    D M i 2 = 1 ∧ D M i 3 = 2 :=
  ⟨D_apply M hM i hi 2 le_rfl (by omega), D_apply M hM i hi 3 (by omega) (by omega)⟩

/-- The inverse of `D_i`. -/
def Dinv (M : ℕ) : ℕ → ℕ → ℕ
  | 0 => cycInv (2 * (2 * M + 2) - M + 1)
  | i + 1 => fun k => cyc (2 * M + 2 - i - (M - 1)) (swp 1 2 (Dinv M i (cycInv (2 * M + 2 - i) k)))

theorem swp12_swp12 (t : ℕ) : swp 1 2 (swp 1 2 t) = t := by
  unfold swp; split_ifs <;> omega

theorem Dinv_D (M : ℕ) (hM : 2 ≤ M) : ∀ i, i ≤ M - 1 → ∀ t, Dinv M i (D M i t) = t := by
  intro i
  induction i with
  | zero => intro _ t; exact cycInv_cyc _ _ (by omega)
  | succ i ih =>
    intro hi t
    simp only [D, Dinv]
    rw [cycInv_cyc _ _ (by omega), ih (by omega), swp12_swp12, cyc_cycInv _ _ (by omega)]

theorem D_Dinv (M : ℕ) (hM : 2 ≤ M) : ∀ i, i ≤ M - 1 → ∀ t, D M i (Dinv M i t) = t := by
  intro i
  induction i with
  | zero => intro _ t; exact cyc_cycInv _ _ (by omega)
  | succ i ih =>
    intro hi t
    simp only [D, Dinv]
    rw [cycInv_cyc _ _ (by omega), swp12_swp12, ih (by omega), cyc_cycInv _ _ (by omega)]

/-- `D_i τ D_i⁻¹ = (2 3)` (left to right). -/
theorem D_conj (M : ℕ) (hM : 2 ≤ M) (i : ℕ) (hi : i ≤ M - 1) (u : ℕ) :
    Dinv M i (swp 1 2 (D M i u)) = swp 2 3 u := by
  obtain ⟨h2, h3⟩ := D_two_three M hM i hi
  have hinv := Dinv_D M hM i hi
  have hi1 : Dinv M i 1 = 2 := by rw [← h2, hinv]
  have hi2 : Dinv M i 2 = 3 := by rw [← h3, hinv]
  by_cases hu1 : D M i u = 1
  · have hu : u = 2 := by rw [← hinv u, hu1, hi1]
    subst hu
    rw [hu1]; simp [swp, hi2]
  · by_cases hu2 : D M i u = 2
    · have hu : u = 3 := by rw [← hinv u, hu2, hi2]
      subst hu
      rw [hu2]; simp [swp, hi1]
    · have hs : swp 1 2 (D M i u) = D M i u := by unfold swp; split_ifs; omega
      rw [hs, hinv]
      have hne2 : u ≠ 2 := fun h => hu1 (h ▸ h2)
      have hne3 : u ≠ 3 := fun h => hu2 (h ▸ h3)
      unfold swp; split_ifs <;> omega

end Houghton.Corner

/-! ### Corner models: the action of `a, b, α` and the relators -/

namespace Houghton.Corner

variable (M : ℕ) [NeZero M] {S : Type*}

/-- `ℓ = 2M + 2`. -/
def ell : ℕ := 2 * M + 2

/-- A state `(i, j, x)`: clocks `i, j ∈ ℤ/M` and a colouring `x` of the coordinates (only
`1, …, L` matter). -/
abbrev CState (S : Type*) := ZMod M × ZMod M × (ℕ → S)

/-- `(i, j, x) · a = (i + 1, j, x · A_{i,j})` with `A_{i,j} = c_{ℓ-i-j}` and `x · π = x ∘ π⁻¹`. -/
def actA (s : CState M S) : CState M S :=
  (s.1 + 1, s.2.1, fun t => s.2.2 (cycInv (ell M - s.1.val - s.2.1.val) t))

/-- The inverse of `actA`. -/
def actAinv (s : CState M S) : CState M S :=
  (s.1 - 1, s.2.1, fun t => s.2.2 (cyc (ell M - (s.1 - 1).val - s.2.1.val) t))

/-- `(i, j, x) · α = (i, j, x · τ)`. -/
def actα (s : CState M S) : CState M S := (s.1, s.2.1, fun t => s.2.2 (swp 1 2 t))

theorem swp34_swp34 (t : ℕ) : swp 3 4 (swp 3 4 t) = t := by
  unfold swp; split_ifs <;> omega

/-- `(τ (2 3))³ = 1`. -/
theorem three_cycle_cube (t : ℕ) :
    swp 1 2 (swp 2 3 (swp 1 2 (swp 2 3 (swp 1 2 (swp 2 3 t))))) = t := by
  rcases (by omega : t = 1 ∨ t = 2 ∨ t = 3 ∨ (t ≠ 1 ∧ t ≠ 2 ∧ t ≠ 3)) with h | h | h | ⟨h1, h2, h3⟩
  · subst h; rfl
  · subst h; rfl
  · subst h; rfl
  · simp [swp, h1, h2, h3]

/-- `τ` and `(3 4)` commute. -/
theorem tau_comm_34 (t : ℕ) : swp 1 2 (swp 3 4 t) = swp 3 4 (swp 1 2 t) := by
  unfold swp; split_ifs <;> omega

theorem ell_sub_ge (i j : ZMod M) : 4 ≤ ell M - i.val - j.val := by
  have := ZMod.val_lt i; have := ZMod.val_lt j; unfold ell; omega

omit [NeZero M] in
/-- `r₁ = α²` acts trivially. -/
theorem r1_trivial (s : CState M S) : actα M (actα M s) = s := by
  obtain ⟨i, j, x⟩ := s
  simp only [actα, swp12_swp12]

/-- `r₂ = (α a α a⁻¹)³` acts trivially. -/
theorem r2_trivial (s : CState M S) :
    actAinv M (actα M (actA M (actα M (actAinv M (actα M (actA M (actα M
      (actAinv M (actα M (actA M (actα M s))))))))))) = s := by
  obtain ⟨i, j, x⟩ := s
  have hr := ell_sub_ge M i j
  simp only [actα, actA, actAinv, add_sub_cancel_right, Prod.mk.injEq, true_and]
  funext t
  simp only [conj_tau _ _ hr, three_cycle_cube]

/-- `r₃ = [α, a² α a⁻²]` acts trivially. -/
theorem r3_trivial (s : CState M S) :
    actAinv M (actAinv M (actα M (actA M (actA M (actα M (actAinv M (actAinv M (actα M
      (actA M (actA M (actα M s))))))))))) = s := by
  obtain ⟨i, j, x⟩ := s
  have hr := ell_sub_ge M i j
  have hr' := ell_sub_ge M (i + 1) j
  simp only [actα, actA, actAinv, add_sub_cancel_right, Prod.mk.injEq, true_and]
  funext t
  simp only [conj_tau _ _ hr', conj_23 _ _ hr, tau_comm_34, swp12_swp12, swp34_swp34]

/-- The colour permutation of `b` at clock `(i, j)` as a function (`B_{i,j}`): `c_{2ℓ-j}` off the top
row, `D_i` on the top row `j = M - 1`. -/
def Bfwd (i j : ZMod M) : ℕ → ℕ :=
  if j.val < M - 1 then cyc (2 * ell M - j.val) else D M i.val

/-- `B_{i,j}⁻¹`. -/
def Binv (i j : ZMod M) : ℕ → ℕ :=
  if j.val < M - 1 then cycInv (2 * ell M - j.val) else Dinv M i.val

/-- `(i, j, x) · b = (i, j + 1, x · B_{i,j})`. -/
def actB (s : CState M S) : CState M S :=
  (s.1, s.2.1 + 1, fun t => s.2.2 (Binv M s.1 s.2.1 t))

/-- The inverse of `actB`. -/
def actBinv (s : CState M S) : CState M S :=
  (s.1, s.2.1 - 1, fun t => s.2.2 (Bfwd M s.1 (s.2.1 - 1) t))

/-- `B_{i,j} τ B_{i,j}⁻¹ = (2 3)` at every clock. -/
theorem B_conj (hM : 2 ≤ M) (i j : ZMod M) (u : ℕ) :
    Binv M i j (swp 1 2 (Bfwd M i j u)) = swp 2 3 u := by
  unfold Binv Bfwd
  split_ifs with h
  · exact conj_tau _ _ (by unfold ell; omega)
  · exact D_conj M hM i.val (by have := ZMod.val_lt i; omega) u

theorem swp23_swp23 (t : ℕ) : swp 2 3 (swp 2 3 t) = t := by
  unfold swp; split_ifs <;> omega

/-- `r₅ = a α a⁻¹ b α⁻¹ b⁻¹` acts trivially (for `M ≥ 2`). -/
theorem r5_trivial (hM : 2 ≤ M) (s : CState M S) :
    actBinv M (actα M (actB M (actAinv M (actα M (actA M s))))) = s := by
  obtain ⟨i, j, x⟩ := s
  have hr := ell_sub_ge M i j
  simp only [actα, actA, actAinv, actB, actBinv, add_sub_cancel_right, Prod.mk.injEq, true_and]
  funext t
  simp only [B_conj M hM, conj_tau _ _ hr, swp23_swp23]

theorem val_add_one (hM : 2 ≤ M) (j : ZMod M) :
    (j + 1).val = if j.val + 1 < M then j.val + 1 else 0 := by
  rw [ZMod.val_add, ZMod.val_one_eq_one_mod, Nat.mod_eq_of_lt (by omega : 1 < M)]
  have := ZMod.val_lt j
  split_ifs with h
  · exact Nat.mod_eq_of_lt h
  · have h' : j.val + 1 = M := by omega
    rw [h', Nat.mod_self]

/-- The inverse form of `eq:corner-id`. -/
theorem corner_id' (r t k : ℕ) (hr : 3 ≤ r) (hrt : r < t) :
    cycInv r (cycInv t (cyc (r - 1) (cyc t (swp 1 2 k)))) = k := by
  have h := corner_id r t (cycInv r (cycInv t (cyc (r - 1) (cyc t (swp 1 2 k))))) hr hrt
  rw [cyc_cycInv _ _ (by omega), cyc_cycInv _ _ (by omega), cycInv_cyc _ _ (by omega),
    cycInv_cyc _ _ (by omega)] at h
  have := congrArg (swp 1 2) h
  rw [swp12_swp12, swp12_swp12] at this
  exact this.symm

/-- `r₄ = a b a⁻¹ b⁻¹ α⁻¹` acts trivially at every clock except the corner `(M - 1, M - 1)`. -/
theorem r4_trivial_off_corner (hM : 2 ≤ M) (s : CState M S)
    (hcorner : ¬ (s.1.val = M - 1 ∧ s.2.1.val = M - 1)) :
    actα M (actBinv M (actAinv M (actB M (actA M s)))) = s := by
  obtain ⟨i, j, x⟩ := s
  simp only at hcorner
  have hiM := ZMod.val_lt i
  have hjM := ZMod.val_lt j
  simp only [actα, actA, actAinv, actB, actBinv, add_sub_cancel_right, Prod.mk.injEq, true_and]
  funext t
  congr 1
  by_cases h : j.val < M - 1
  · have hj1 : (j + 1).val = j.val + 1 := by
      rw [val_add_one M hM]; simp [show j.val + 1 < M by omega]
    simp only [Binv, Bfwd, h, ↓reduceIte, hj1]
    rw [show ell M - i.val - (j.val + 1) = ell M - i.val - j.val - 1 by omega]
    exact corner_id' _ _ _ (by have := ell_sub_ge M i j; omega) (by unfold ell; omega)
  · have hj : j.val = M - 1 := by omega
    have hi : i.val < M - 1 := by
      by_contra hc; exact hcorner ⟨by omega, hj⟩
    have hj0 : (j + 1).val = 0 := by
      rw [val_add_one M hM]; simp [show ¬ (j.val + 1 < M) by omega]
    have hi1 : (i + 1).val = i.val + 1 := by
      rw [val_add_one M hM]; simp [show i.val + 1 < M by omega]
    simp only [Binv, Bfwd, h, ↓reduceIte, hj0, hi1, Dinv]
    rw [show ell M - i.val - j.val = 2 * M + 2 - i.val - (M - 1) by unfold ell; omega,
      show ell M - i.val - 0 = 2 * M + 2 - i.val by unfold ell; omega,
      cycInv_cyc _ _ (by omega), cycInv_cyc _ _ (by omega), Dinv_D M hM _ (by omega),
      swp12_swp12]

end Houghton.Corner
