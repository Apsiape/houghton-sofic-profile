import Houghton.Area.Word

/-! The checker for the auxiliary presentation of `thm:area-weighted` (core Lean only). Types
`0,1,2,3,≥4` are `r₁,r₃,r₄,r₅,r₆` with `r₆ = [q,b]`, `q = σ_{-2}`; weights `(25,616,1,133,78)`. -/

namespace Houghton.Word

/-- `q = σ_{-2} = a⁻² α a²`. -/
def qW : List Nat := [1, 1, 4, 0, 0]

/-- `r₆ = [q, b]`. -/
def r6W : List Nat := commW qW [2]

/-- The auxiliary relator words. -/
def relWA : Nat → List Nat
  | 0 => relW 0
  | 1 => relW 2
  | 2 => relW 3
  | 3 => relW 4
  | _ => r6W

/-- The weights. -/
def wtA : Nat → Nat
  | 0 => 25
  | 1 => 616
  | 2 => 1
  | 3 => 133
  | _ => 78

/-- Total weight of packed auxiliary data. -/
def wsumA : List Nat → Nat
  | [] => 0
  | c :: cs => wtA ((c / 65536) % 8) + wsumA cs

/-! Formal words in `t, q`: symbols `0 = t, 1 = t⁻¹, 2 = q, 3 = q⁻¹`. -/

/-- Expand a formal word in `t, q` to a word in `a, b, α`. -/
def symQ (w : List Nat) : List Nat := substS tW qW w

/-- `d(t) = t² q`. -/
def DTq : List Nat := [0, 0, 2]
/-- `d(q) = u₁ u₂ q u₁⁻¹` with `u_i = t^{-i} q t^i`, i.e. `t⁻¹qt⁻¹qt²qt⁻¹q⁻¹t`. -/
def DQq : List Nat := [1, 2, 1, 2, 0, 0, 2, 1, 3, 0]
/-- `o(t) = E(d(t))`, freely reduced (length 7). -/
def OTq : List Nat := [0, 0, 2, 0, 2, 1, 2]
/-- `o(q) = E(d(q))`, freely reduced (length 26). -/
def OQq : List Nat :=
  [0, 3, 1, 1, 2, 0, 3, 1, 1, 2, 0, 0, 2, 0, 2, 1, 2, 0, 3, 1, 1, 3, 0, 0, 2, 1]

end Houghton.Word
