import Houghton.Area.Checker
import Houghton.Area.Algebra

/-! The endomorphism `ψ`: `a ↦ a²`, `b ↦ b²`, `α ↦ [a², b²]`. -/

namespace Houghton

open Word

/-- The endomorphism `ψ` of the free group. -/
def ψ : F →* F := FreeGroup.lift ![a ^ 2, b ^ 2, comm (a ^ 2) (b ^ 2)]

@[simp] lemma ψ_a : ψ a = a ^ 2 := by simp [ψ, a, FreeGroup.lift_apply_of]
@[simp] lemma ψ_b : ψ b = b ^ 2 := by simp [ψ, b, FreeGroup.lift_apply_of]
@[simp] lemma ψ_α : ψ α = comm (a ^ 2) (b ^ 2) := by simp [ψ, α, FreeGroup.lift_apply_of]

lemma ψ_ltr (x : ℕ) (hx : x < 6) : ψ (ltr x) = ev (psiLetter x) := by
  rcases x with _ | _ | _ | _ | _ | _ | x
  · simp [psiLetter, pow_two]
  · simp [psiLetter, pow_two]
  · simp [psiLetter, pow_two]
  · simp [psiLetter, pow_two]
  · simp [psiLetter, pow_two, comm, mul_assoc]
  · simp [psiLetter, pow_two, comm, mul_assoc, mul_inv_rev]
  · omega

lemma ψ_ev (w : List ℕ) (hw : ∀ x ∈ w, x < 6) : ψ (ev w) = ev (psiW w) := by
  induction w with
  | nil => simp [psiW]
  | cons x w ih =>
    rw [ev_cons, map_mul, ψ_ltr x (hw x (by simp)), ih (fun y hy => hw y (by simp [hy]))]
    simp [psiW]

end Houghton
