import Houghton.UpperData
import Houghton.Area.Checker
import Houghton.Chunk

/-!
# Kernel-checked finite facts about `E_H` for the upper bound

Canonical words `cwi k` (`k < 40`) for the distinct elements of `E_H`; every chunk word and its
inverse equals some canonical word in `H₃` (by a filling); every chunk relation `c_i c_j = c_k`
has a filling of `c_i c_j c_k⁻¹` with at most `4` cells. A fingerprint (the action on six points)
shows that no other triple `(i, j, k)` is a chunk relation.
-/

namespace Houghton

open Word UpperData

/-- The letter with code `c` (`0..5 = a,a⁻¹,b,b⁻¹,α,α⁻¹`). -/
def codeLetter (c : ℕ) : Letter := (⟨(c / 2) % 3, Nat.mod_lt _ (by decide)⟩, c % 2 == 0)

/-- The code of a letter. -/
def letterCode (l : Letter) : ℕ := 2 * l.1.val + (if l.2 then 0 else 1)

/-- The paper's right action of a coded word on `Y`. -/
def wActC (w : List ℕ) (y : Y) : Y := wordAct (w.map codeLetter) y

def mkY (p : ℕ × ℕ) : Y := (⟨p.1 % 3, Nat.mod_lt _ (by decide)⟩, p.2)
def encY (y : Y) : ℕ := 3 * y.2 + y.1.val

/-- Fingerprint of a coded word. -/
def fpW (w : List ℕ) : List ℕ := fpPts.map fun p => encY (wActC w (mkY p))

def cwi (k : ℕ) : List ℕ := cw.getD k []
def fpd (k : ℕ) : List ℕ := fpData.getD k []
def lookupK (f : List ℕ) : Option ℕ := (List.range 40).find? fun k => fpd k == f
def tblE (i j : ℕ) : List ℕ := (fillTbl.getD i []).getD j []

def chkFp : Bool := (List.range 40).all fun k => fpd k == fpW (cwi k)
def chkInj : Bool :=
  (List.range 40).all fun k => (List.range 40).all fun k' => !(fpd k == fpd k') || k == k'
def chkFill : Bool := (List.range 40).all fun i => (List.range 40).all fun j =>
  match lookupK (fpW (cwi i ++ cwi j)) with
  | none => true
  | some k => checkPacked relW (tblE i j) (cwi i ++ cwi j ++ invW (cwi k)) &&
      Nat.ble (tblE i j).length 4
def chkLen : Bool := (List.range 40).all fun k => Nat.ble (cwi k).length 10
def chkCov : Bool := covData.all fun e =>
  Nat.blt e.2.1 40 && checkPacked relW e.2.2.1 (e.1 ++ invW (cwi e.2.1)) &&
  Nat.blt e.2.2.2.1 40 && checkPacked relW e.2.2.2.2 (invW e.1 ++ invW (cwi e.2.2.2.1))
def chkCovWords : Bool := chunkWords.all fun w => (covData.map Prod.fst).contains (w.map letterCode)

theorem chkFp_eq : chkFp = true := by decide +kernel
theorem chkInj_eq : chkInj = true := by decide +kernel
theorem chkLen_eq : chkLen = true := by decide +kernel
theorem chkCov_eq : chkCov = true := by decide +kernel
theorem chkCovWords_eq : chkCovWords = true := by decide +kernel
theorem chkFill_eq : chkFill = true := by decide +kernel

end Houghton
