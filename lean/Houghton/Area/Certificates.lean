import Houghton.Area.Psi
import Houghton.Area.ChecksSmall
import Houghton.Area.ChecksPsiR2
import Houghton.Area.ChecksPsiR3
import Houghton.Area.ChecksPsiR5

/-! The certified finite relations as `AreaLE` statements: kernel-checked runs of the checker on
the cells of `certificates.json.gz`, plus `checkPacked_sound`. Cell counts as in the paper. -/

namespace Houghton

open Word

/-- `t = b⁻¹ a`. -/
def t : F := b⁻¹ * a
/-- `ρ = a⁻¹ b⁻¹ a b`. -/
def ρ : F := a⁻¹ * b⁻¹ * a * b
/-- `τ_j = b^j α b^{-j}`. -/
def τ (j : ℕ) : F := b ^ j * α * b⁻¹ ^ j
/-- `σ_{-j} = a^{-j} α a^j`. -/
def σneg (j : ℕ) : F := a⁻¹ ^ j * α * a ^ j

lemma ev_replicate (x k : ℕ) : ev (List.replicate k x) = ltr x ^ k := by
  induction k with
  | zero => simp
  | succ k ih => rw [List.replicate_succ, ev_cons, ih, pow_succ']

lemma ev_sigmaW (j : ℕ) : ev (sigmaW j) = σ j := by
  simp [sigmaW, ev_replicate, σ, mul_assoc]

lemma ev_sigmaNegW (j : ℕ) : ev (sigmaNegW j) = σneg j := by
  simp [sigmaNegW, ev_replicate, σneg, mul_assoc]

lemma ev_tauW (j : ℕ) : ev (tauW j) = τ j := by
  simp [tauW, ev_replicate, τ, mul_assoc]

lemma ev_tW : ev tW = t := by simp [tW, t]

lemma ev_rhoW : ev rhoW = ρ := by simp [rhoW, ρ, mul_assoc]

lemma ev_commW (u v : List ℕ) : ev (commW u v) = comm (ev u) (ev v) := by
  simp [commW, comm, ev_invW, mul_assoc]

/-- The value of a formal word in `t` and a second letter with word `v0` (symbols `0,1,2,3`). -/
def evF (v0 w : List ℕ) : F := ev (substS tW v0 w)

/-- The value of a formal word in `t, ρ`. -/
abbrev evS (w : List ℕ) : F := evF rhoW w

/-- Turning a successful check into an area bound. -/
lemma areaLE_of_check {D target : List ℕ} {w : F} {n : ℕ} (h : checkPacked relW D target = true)
    (hw : ev target = w) (hn : D.length ≤ n) : AreaLE w n :=
  ((checkPacked_sound D target h).mono hn).of_eq hw

/-! ### Base relations and the transfer lemma inputs -/

theorem area_A2 : AreaLE (comm (σ 0) (σ 2)) 1 :=
  areaLE_of_check chk_A2 (by simp [ev_commW, ev_sigmaW]) (by decide +kernel)

theorem area_E0 : AreaLE (comm (σ 0) t) 1 :=
  areaLE_of_check chk_E0 (by simp [ev_commW, ev_sigmaW, ev_tW]) (by decide +kernel)

theorem area_E1 : AreaLE (comm (σ 1) t) 4 :=
  areaLE_of_check chk_E1 (by simp [ev_commW, ev_sigmaW, ev_tW]) (by decide +kernel)

theorem area_E2 : AreaLE (comm (σ 2) t) 27 :=
  areaLE_of_check chk_E2 (by simp [ev_commW, ev_sigmaW, ev_tW]) (by decide +kernel)

theorem area_E3 : AreaLE (comm (σ 3) t) 76 :=
  areaLE_of_check chk_E3 (by simp [ev_commW, ev_sigmaW, ev_tW]) (by decide +kernel)

theorem area_U1 : AreaLE (τ 1 * (σ 1)⁻¹) 1 :=
  areaLE_of_check chk_U1 (by simp [ev_tauW, ev_sigmaW, ev_invW]) (by decide +kernel)

theorem area_U2 : AreaLE (τ 2 * (σ 2)⁻¹) 5 :=
  areaLE_of_check chk_U2 (by simp [ev_tauW, ev_sigmaW, ev_invW]) (by decide +kernel)

theorem area_U3 : AreaLE (τ 3 * (σ 3)⁻¹) 32 :=
  areaLE_of_check chk_U3 (by simp [ev_tauW, ev_sigmaW, ev_invW]) (by decide +kernel)

theorem area_B0 : AreaLE (comm α (σ 1 * σ 0 * b)) 5 :=
  areaLE_of_check chk_B0 (by simp [ev_commW, ev_sigmaW, mul_assoc]) (by decide +kernel)

theorem area_B2 : AreaLE (comm (σneg 2) b) 9 :=
  areaLE_of_check chk_B2 (by simp [ev_commW, ev_sigmaNegW]) (by decide +kernel)

theorem area_B3 : AreaLE (comm (σneg 3) b) 12 :=
  areaLE_of_check chk_B3 (by simp [ev_commW, ev_sigmaNegW]) (by decide +kernel)

theorem area_A3 : AreaLE (comm (σ 0) (σ 3)) 21 :=
  areaLE_of_check chk_A3 (by simp [ev_commW, ev_sigmaW]) (by decide +kernel)

theorem area_A4 : AreaLE (comm (σ 0) (σ 4)) 47 :=
  areaLE_of_check chk_A4 (by simp [ev_commW, ev_sigmaW]) (by decide +kernel)

theorem area_A5 : AreaLE (comm (σ 0) (σ 5)) 79 :=
  areaLE_of_check chk_A5 (by simp [ev_commW, ev_sigmaW]) (by decide +kernel)

theorem area_A6 : AreaLE (comm (σ 0) (σ 6)) 157 :=
  areaLE_of_check chk_A6 (by simp [ev_commW, ev_sigmaW]) (by decide +kernel)

/-! ### The cheap letters (step (2)) -/

/-- `[α, t]` has area 1 (it is `E(0)`). -/
theorem area_comm_α_t : AreaLE (comm α t) 1 := by
  have h := area_E0
  simpa [σ] using h

/-- `[α, ρ]` has area at most 5. -/
theorem area_comm_α_ρ : AreaLE (comm α ρ) 5 :=
  areaLE_of_check chk_commXRho (by simp [ev_commW, ev_rhoW]) (by decide +kernel)

/-- The relation of step (2): `ρ^b = R' = tρt⁻¹·ρ·tρt⁻¹`, with 14 cells. -/
theorem area_N4 : AreaEq (b⁻¹ * ρ * b) (evS RpS) 14 :=
  areaLE_of_check chk_N4 (by simp [evF, symW, ev_rhoW, ev_invW, mul_assoc]) (by decide +kernel)

/-- `ψ(ρ) = R` as a word in `t, ρ`, with 84 cells. -/
theorem area_psi_ρ : AreaEq (ψ ρ) (evS RS) 84 :=
  areaLE_of_check chk_psiRho
    (by rw [ev_append, ev_invW, ← ψ_ev rhoW (by decide), ev_rhoW, evS, evF, symW]) (by decide +kernel)

/-! ### The doubling lifts (Lemma `lem:psi`) -/

/-- `ψ(α) = Π = σ₁σ₂σ₀σ₁` with 6 cells. -/
theorem area_CONV : AreaEq (ψ α) (σ 1 * σ 2 * σ 0 * σ 1) 6 :=
  areaLE_of_check chk_CONV
    (by rw [ev_append, ev_invW, ← ψ_ev [4] (by decide)]; simp [PiW, ev_sigmaW, mul_assoc])
    (by decide +kernel)

/-- The braid relation `σ₁σ₀σ₁ = σ₀σ₁σ₀` with 4 cells. -/
theorem area_BRAID : AreaEq (σ 1 * σ 0 * σ 1) (σ 0 * σ 1 * σ 0) 4 :=
  areaLE_of_check chk_BRAID (by simp [ev_sigmaW, ev_invW, mul_assoc]) (by decide +kernel)

lemma psi_rel_eq (k : ℕ) : ψ (rel (idx k)) = ev (psiW (relW k)) := by
  rw [← ev_relW]
  exact ψ_ev _ (by
    intro x hx
    rcases k with _ | _ | _ | _ | k <;> simp [relW] at hx <;> omega)

theorem area_psi_r1 : AreaLE (ψ r₁) 17 :=
  areaLE_of_check chk_psiR1 (psi_rel_eq 0).symm (by decide +kernel)

theorem area_psi_r2 : AreaLE (ψ r₂) 359 :=
  areaLE_of_check chk_psiR2 (psi_rel_eq 1).symm (by decide +kernel)

theorem area_psi_r3 : AreaLE (ψ r₃) 864 :=
  areaLE_of_check chk_psiR3 (psi_rel_eq 2).symm (by decide +kernel)

theorem area_psi_r4 : AreaLE (ψ r₄) 0 :=
  areaLE_of_check chk_psiR4 (psi_rel_eq 3).symm (by decide +kernel)

theorem area_psi_r5 : AreaLE (ψ r₅) 182 :=
  areaLE_of_check chk_psiR5 (psi_rel_eq 4).symm (by decide +kernel)

theorem area_psi_rel (i : Fin 5) : AreaLE (ψ (rel i)) 864 := by
  rcases i with ⟨_ | _ | _ | _ | _ | k, hk⟩
  · exact area_psi_r1.mono (by decide)
  · exact area_psi_r2.mono (by decide)
  · exact area_psi_r3
  · exact area_psi_r4.mono (by decide)
  · exact area_psi_r5.mono (by decide)
  · omega

/-- **Lemma `lem:psi`**: `Area ψ(w) ≤ 864 Area(w)`. -/
theorem AreaLE.psi {w : F} {n : ℕ} (h : AreaLE w n) : AreaLE (ψ w) (864 * n) := by
  obtain ⟨cs, hl, rfl⟩ := h
  have key : ∀ cs : List (F × Fin 5 × Bool),
      AreaLE (ψ (cs.map Houghton.cell).prod) (864 * cs.length) := by
    intro cs
    induction cs with
    | nil => simpa using AreaLE.one
    | cons c cs ih =>
      have hc : AreaLE (ψ (Houghton.cell c)) 864 := by
        rcases c with ⟨z, i, s⟩
        cases s
        · simpa [Houghton.cell, map_mul, map_inv] using (area_psi_rel i).inv.conj (ψ z)
        · simpa [Houghton.cell, map_mul, map_inv] using (area_psi_rel i).conj (ψ z)
      simp only [List.map_cons, List.prod_cons, map_mul, List.length_cons]
      exact (hc.mul ih).mono (by rw [Nat.mul_succ]; omega)
  exact (key cs).mono (Nat.mul_le_mul_left _ hl)

end Houghton
