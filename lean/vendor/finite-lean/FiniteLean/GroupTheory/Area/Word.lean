/-! Words and the Bool-valued certificate checker (core Lean only, so the kernel checks do not
depend on Mathlib). Letters: `0,1,2,3,4,5 = a,a⁻¹,b,b⁻¹,α,α⁻¹`. A cell `(z,i,s)` stands for
`z r_{i+1}^{±1} z⁻¹`; the checker multiplies the cells out with free reduction on a stack and
compares with the reduced target. Soundness: `Houghton.Area.Checker`. -/

namespace Houghton.Word

/-- Inverse letter. -/
def inv (x : Nat) : Nat := cond (Nat.beq (x % 2) 0) (x + 1) (x - 1)

/-- Push one letter onto a reduced stack (the stack is the reversed word). -/
def push : List Nat → Nat → List Nat
  | [], x => [x]
  | y :: s, x => cond (Nat.beq y (inv x)) s (x :: y :: s)

/-- Push a word, letter by letter.  The `match` forces the new stack at every step, so that the
kernel does not build a deep chain of suspended `push` applications. -/
def pushW : List Nat → List Nat → List Nat
  | stk, [] => stk
  | stk, x :: w =>
    match push stk x with
    | [] => pushW [] w
    | y :: s => pushW (y :: s) w

/-- Formal inverse of a word. -/
def invW (w : List Nat) : List Nat := (w.map inv).reverse

/-- Push a relator `R i` or its inverse (`R` = the relator words of the presentation). -/
def pushRel (R : Nat → List Nat) (stk : List Nat) (i : Nat) (s : Bool) : List Nat :=
  cond s (pushW stk (R i)) (pushW stk (invW (R i)))

/-- A cell: conjugator word, relator index, sign. -/
abbrev Cell := List Nat × Nat × Bool

/-- Push the word `z r^{±1} z⁻¹` of a cell. -/
def runCell (R : Nat → List Nat) (stk : List Nat) (c : Cell) : List Nat :=
  pushW (pushRel R (pushW stk c.1) c.2.1 c.2.2) (invW c.1)

/-- Push all cells. -/
def run (R : Nat → List Nat) : List Nat → List Cell → List Nat
  | stk, [] => stk
  | stk, c :: cs =>
    match runCell R stk c with
    | [] => run R [] cs
    | y :: s => run R (y :: s) cs

/-- Boolean equality of words. -/
def beqL : List Nat → List Nat → Bool
  | [], [] => true
  | x :: xs, y :: ys => cond (Nat.beq x y) (beqL xs ys) false
  | _, _ => false

/-- The checker: the product of the cells and the target have the same free reduction. -/
def check (R : Nat → List Nat) (cs : List Cell) (target : List Nat) : Bool :=
  beqL (run R [] cs) (pushW [] target)

/-! Packed cell: `k + 65536 * (i + 8 * ([s] + 2 * ∑ⱼ (z[j] + 1) 8^j))`; the salt `k < 65536` is
ignored (distinct salts avoid kernel cache collisions; ~10x faster). -/

/-- Decode a packed word (with fuel). -/
def decW : Nat → Nat → List Nat
  | 0, _ => []
  | f + 1, n => cond (Nat.beq n 0) [] ((n % 8 - 1) :: decW f (n / 8))

/-- Decode a packed cell. -/
def decodeCell (c : Nat) : Cell :=
  (decW 1000 (c / 1048576), (c / 65536) % 8, Nat.beq ((c / 524288) % 2) 1)

/-- The checker on packed data. -/
def checkPacked (R : Nat → List Nat) (data : List Nat) (target : List Nat) : Bool :=
  check R (data.map decodeCell) target

/-! ### Word builders for targets -/

/-- `[u, v] = u v u⁻¹ v⁻¹`. -/
def commW (u v : List Nat) : List Nat := u ++ v ++ invW u ++ invW v

/-- The image of one formal symbol under `t ↦ u`, `ρ ↦ v` (the result is a word in the alphabet of
`u, v`, using `inv` for inverses). -/
def img (u v : List Nat) : Nat → List Nat
  | 0 => u
  | 1 => invW u
  | 2 => v
  | _ => invW v

/-- Substitute `t ↦ u`, `ρ ↦ v` in a formal word. -/
def substS (u v : List Nat) : List Nat → List Nat
  | [] => []
  | x :: w => img u v x ++ substS u v w


end Houghton.Word
