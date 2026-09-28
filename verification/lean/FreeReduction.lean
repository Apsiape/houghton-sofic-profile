import Std.Tactic

/-! Soundness of free reduction and relator-cell certificates.
The conclusion is universal in a multiplicative interpretation of six letters.
The cancellation and associativity hypotheses hold for every group interpretation.
No claim about the presentation of H_3 is built into the checker.
-/
namespace WordCertificate

inductive Letter where
  | a | A | b | B | x | X
  deriving DecidableEq, Repr

open Letter
abbrev Word := List Letter

def inverse : Letter → Letter
  | a => A | A => a | b => B | B => b | x => X | X => x

def invWord (w : Word) : Word := w.reverse.map inverse

def push (c : Letter) : Word → Word
  | [] => [c]
  | d :: w => if inverse c = d then w else c :: d :: w

def reduce : Word → Word
  | [] => []
  | c :: w => push c (reduce w)

structure Model (G : Type u) where
  one : G
  mul : G → G → G
  val : Letter → G
  assoc : ∀ x y z, mul (mul x y) z = mul x (mul y z)
  one_mul : ∀ x, mul one x = x
  mul_one : ∀ x, mul x one = x
  cancel : ∀ c, mul (val c) (val (inverse c)) = one

def eval (M : Model G) : Word → G
  | [] => M.one
  | c :: w => M.mul (M.val c) (eval M w)

theorem eval_append (M : Model G) (u v : Word) :
    eval M (u ++ v) = M.mul (eval M u) (eval M v) := by
  induction u with
  | nil => simp [eval, M.one_mul]
  | cons c u ih => simp [eval, ih, M.assoc]

theorem eval_push (M : Model G) (c : Letter) (w : Word) :
    eval M (push c w) = M.mul (M.val c) (eval M w) := by
  cases w with
  | nil => rfl
  | cons d w =>
      by_cases h : inverse c = d
      · subst d
        simp only [push, ite_true, eval]
        rw [← M.assoc, M.cancel, M.one_mul]
      · simp [push, h, eval]

theorem reduce_sound (M : Model G) (w : Word) :
    eval M (reduce w) = eval M w := by
  induction w with
  | nil => rfl
  | cons c w ih => simp only [reduce, eval_push, eval, ih]

theorem reduction_equality_sound (M : Model G) (u v : Word)
    (h : reduce u = reduce v) : eval M u = eval M v := by
  rw [← reduce_sound M u, ← reduce_sound M v, h]

theorem word_cancel (M : Model G) (w : Word) :
    M.mul (eval M w) (eval M (invWord w)) = M.one := by
  induction w with
  | nil => simp [invWord, eval, M.one_mul]
  | cons c w ih =>
      simp only [invWord, List.reverse_cons, List.map_append, List.map_cons,
        List.map_nil, eval_append, eval]
      rw [M.mul_one]
      rw [M.assoc, ← M.assoc (eval M w)]
      change M.mul (M.val c)
        (M.mul (M.mul (eval M w) (eval M (invWord w))) (M.val (inverse c))) = _
      rw [ih, M.one_mul, M.cancel]

def relator : Fin 5 → Word
  | 0 => [x,x]
  | 1 => [x,a,x,A,x,a,x,A,x,a,x,A]
  | 2 => [x,a,a,x,A,A,X,a,a,X,A,A]
  | 3 => [a,b,A,B,X]
  | 4 => [a,x,A,b,X,B]

structure Cell where
  conjugator : Word
  rel : Fin 5
  negative : Bool

def signedRelator (c : Cell) : Word :=
  if c.negative then invWord (relator c.rel) else relator c.rel

def cellWord (c : Cell) : Word := c.conjugator ++ signedRelator c ++ invWord c.conjugator

def certificateWord (cs : List Cell) : Word := cs.flatMap cellWord

theorem signed_relator_sound (M : Model G) (h : ∀ i, eval M (relator i) = M.one)
    (c : Cell) : eval M (signedRelator c) = M.one := by
  unfold signedRelator
  split
  · have hc := word_cancel M (relator c.rel)
    rw [h, M.one_mul] at hc
    exact hc
  · exact h c.rel

theorem cell_sound (M : Model G) (h : ∀ i, eval M (relator i) = M.one)
    (c : Cell) : eval M (cellWord c) = M.one := by
  simp only [cellWord, eval_append, signed_relator_sound M h, M.mul_one]
  exact word_cancel M c.conjugator

theorem certificate_sound (M : Model G) (h : ∀ i, eval M (relator i) = M.one)
    (cs : List Cell) : eval M (certificateWord cs) = M.one := by
  induction cs with
  | nil => rfl
  | cons c cs ih =>
      simp only [certificateWord, List.flatMap_cons, eval_append, cell_sound M h]
      change M.mul M.one (eval M (certificateWord cs)) = _
      rw [ih, M.one_mul]

theorem accepted_certificate_sound (M : Model G)
    (h : ∀ i, eval M (relator i) = M.one) (target : Word) (cs : List Cell)
    (accepted : reduce target = reduce (certificateWord cs)) :
    eval M target = M.one := by
  rw [reduction_equality_sound M target (certificateWord cs) accepted]
  exact certificate_sound M h cs

-- Reduce after every cell to keep the executable check's intermediate words small.
def certificateNF : List Cell → Word
  | [] => []
  | c :: cs => reduce (cellWord c ++ certificateNF cs)

theorem certificateNF_sound (M : Model G) (cs : List Cell) :
    eval M (certificateNF cs) = eval M (certificateWord cs) := by
  induction cs with
  | nil => rfl
  | cons c cs ih =>
      simp only [certificateNF, reduce_sound, eval_append,
        certificateWord, List.flatMap_cons, eval_append] at *
      rw [ih]

theorem accepted_nf_sound (M : Model G)
    (h : ∀ i, eval M (relator i) = M.one) (target : Word) (cs : List Cell)
    (accepted : reduce target = certificateNF cs) :
    eval M target = M.one := by
  rw [← reduce_sound M target, accepted, certificateNF_sound]
  exact certificate_sound M h cs

-- A bounded-size kernel check per cell avoids evaluating a whole certificate
-- as one enormous reduction expression.
theorem checked_step (M : Model G)
    (h : ∀ i, eval M (relator i) = M.one) (c : Cell) (tail current : Word)
    (step : reduce (cellWord c ++ tail) = reduce current)
    (tail_valid : eval M tail = M.one) : eval M current = M.one := by
  rw [← reduction_equality_sound M _ current step]
  rw [eval_append, cell_sound M h, tail_valid, M.one_mul]

#print axioms accepted_certificate_sound
#print axioms accepted_nf_sound
#print axioms checked_step
end WordCertificate
