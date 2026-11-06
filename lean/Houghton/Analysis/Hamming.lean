import Houghton.Basic
import FiniteLean.GroupTheory.Permutations.Hamming

namespace Houghton
open Finset Equiv
variable {Ω : Type*} [Fintype Ω] [DecidableEq Ω]
section Transport

variable (φ : F →* Perm Ω) (δ : ℝ)

lemma dH_cell_le (hrel : ∀ i, dH (φ (rel i)) 1 ≤ δ) (c : F × Fin 5 × Bool) :
    dH (φ (cell c)) 1 ≤ δ := by
  rcases c with ⟨z, i, e⟩
  have key : ∀ g : Perm Ω, dH (φ z * g * (φ z)⁻¹) 1 = dH g 1 := fun g => dH_conj _ _
  simp only [cell, map_mul, map_inv, key]
  cases e
  · simp only [Bool.false_eq_true, ite_false, map_inv, dH_inv_one]
    exact hrel i
  · simp only [ite_true]
    exact hrel i

lemma dH_prod_cells_le (hrel : ∀ i, dH (φ (rel i)) 1 ≤ δ) (cs : List (F × Fin 5 × Bool)) :
    dH (φ (cs.map cell).prod) 1 ≤ cs.length * δ := by
  induction cs with
  | nil => simp [dH_self]
  | cons c cs ih =>
    rw [List.map_cons, List.prod_cons, map_mul, List.length_cons]
    calc dH (φ (cell c) * φ (cs.map cell).prod) 1
        ≤ dH (φ (cell c) * φ (cs.map cell).prod) (φ (cell c)) + dH (φ (cell c)) 1 :=
          dH_triangle _ _ _
      _ = dH (φ (cs.map cell).prod) 1 + dH (φ (cell c)) 1 := by rw [dH_mul_self_left]
      _ ≤ cs.length * δ + δ := add_le_add ih (dH_cell_le φ δ hrel c)
      _ = ((cs.length + 1 : ℕ) : ℝ) * δ := by rw [Nat.cast_succ, add_mul, one_mul]

/-- Transport in measure: a null word of area at most `n` has defect at most `n δ`. -/
lemma dH_le_of_areaLE (hrel : ∀ i, dH (φ (rel i)) 1 ≤ δ) (hδ : 0 ≤ δ) {w : F} {n : ℕ}
    (h : AreaLE w n) : dH (φ w) 1 ≤ n * δ := by
  obtain ⟨cs, hlen, rfl⟩ := h
  calc dH (φ (cs.map cell).prod) 1 ≤ cs.length * δ := dH_prod_cells_le φ δ hrel cs
    _ ≤ n * δ := mul_le_mul_of_nonneg_right (by exact_mod_cast hlen) hδ

end Transport
end Houghton
