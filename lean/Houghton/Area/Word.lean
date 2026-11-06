import FiniteLean.GroupTheory.Area.Word

namespace Houghton.Word
/-- The relator words `r₁,…,r₅` (indices `0,…,4`; every index `≥ 4` means `r₅`). -/
def relW : Nat → List Nat
  | 0 => [4, 4]
  | 1 => [4, 0, 4, 1, 4, 0, 4, 1, 4, 0, 4, 1]
  | 2 => [4, 0, 0, 4, 1, 1, 5, 0, 0, 5, 1, 1]
  | 3 => [0, 2, 1, 3, 5]
  | _ => [0, 4, 1, 2, 5, 3]

/-- `σ_j = a^j α a^{-j}`. -/
def sigmaW (j : Nat) : List Nat := List.replicate j 0 ++ [4] ++ List.replicate j 1

/-- `σ_{-j} = a^{-j} α a^j`. -/
def sigmaNegW (j : Nat) : List Nat := List.replicate j 1 ++ [4] ++ List.replicate j 0

/-- `τ_j = b^j α b^{-j}`. -/
def tauW (j : Nat) : List Nat := List.replicate j 2 ++ [4] ++ List.replicate j 3

/-- `t = b⁻¹ a`. -/
def tW : List Nat := [3, 0]

/-- `ρ = a⁻¹ b⁻¹ a b`. -/
def rhoW : List Nat := [1, 3, 0, 2]

/-- `ψ` on letters: `a ↦ a², b ↦ b², α ↦ [a², b²]`. -/
def psiLetter : Nat → List Nat
  | 0 => [0, 0]
  | 1 => [1, 1]
  | 2 => [2, 2]
  | 3 => [3, 3]
  | 4 => [0, 0, 2, 2, 1, 1, 3, 3]
  | _ => [2, 2, 0, 0, 3, 3, 1, 1]

/-- `ψ` on words. -/
def psiW : List Nat → List Nat
  | [] => []
  | x :: w => psiLetter x ++ psiW w

/-! Formal words in `t, ρ`: symbols `0 = t, 1 = t⁻¹, 2 = ρ, 3 = ρ⁻¹`. -/

/-- Expand a formal word in `t, ρ` to a word in `a, b, α`. -/
def symW (w : List Nat) : List Nat := substS tW rhoW w

/-- `R' = t ρ t⁻¹ ρ t ρ t⁻¹` (formal). -/
def RpS : List Nat := [0, 2, 1, 2, 0, 2, 1]

/-- `R = t⁻¹ R' R'(tρ, R') t ρ R'` (formal, length 46). -/
def RS : List Nat := [1] ++ RpS ++ substS [0, 2] RpS RpS ++ [0, 2] ++ RpS

/-- `Π = σ₁ σ₂ σ₀ σ₁`. -/
def PiW : List Nat := sigmaW 1 ++ sigmaW 2 ++ sigmaW 0 ++ sigmaW 1

end Houghton.Word
