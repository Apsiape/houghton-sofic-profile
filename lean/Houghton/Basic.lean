import FiniteLean.GroupTheory.Permutations.Basic
import Mathlib.GroupTheory.FreeGroup.Basic
import Mathlib.GroupTheory.Perm.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fin.VecNotation

namespace Houghton
abbrev F := FreeGroup (Fin 3)
def a : F := FreeGroup.of 0
def b : F := FreeGroup.of 1
def α : F := FreeGroup.of 2
def comm (x y : F) : F := x * y * x⁻¹ * y⁻¹
def r₁ : F := α ^ 2
def r₂ : F := (α * a * α * a⁻¹) ^ 3
def r₃ : F := comm α (a ^ 2 * α * a⁻¹ ^ 2)
def r₄ : F := a * b * a⁻¹ * b⁻¹ * α⁻¹
def r₅ : F := a * α * a⁻¹ * b * α⁻¹ * b⁻¹
def rel : Fin 5 → F := ![r₁, r₂, r₃, r₄, r₅]
def σ (j : ℕ) : F := a ^ j * α * a⁻¹ ^ j
def γ : F := α * (a * α * a⁻¹)
def cell (c : F × Fin 5 × Bool) : F :=
  c.1 * (if c.2.2 then rel c.2.1 else (rel c.2.1)⁻¹) * c.1⁻¹
def AreaLE (w : F) (n : ℕ) : Prop :=
  ∃ cs : List (F × Fin 5 × Bool), cs.length ≤ n ∧ (cs.map cell).prod = w
def AstarLE (M n : ℕ) : Prop :=
  ∀ p q : ℕ, p ≤ M → q ≤ M → (p + 2 ≤ q ∨ q + 2 ≤ p) →
    ∀ e₁ e₂ : Bool,
      AreaLE (comm (if e₁ then σ p else (σ p)⁻¹) (if e₂ then σ q else (σ q)⁻¹)) n
end Houghton
