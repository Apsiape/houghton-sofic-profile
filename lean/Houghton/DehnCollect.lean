import Houghton.Dehn
import Houghton.DehnQuot

/-! Theorem `thm:dehn`, part 3: buffered collection of a word into a word in the `σ_j^{±1}`. -/

namespace Houghton

/-- Words in the `σ_j^{±1}`. -/
abbrev SW := List (ℕ × Bool)

def σl (x : ℕ × Bool) : F := if x.2 then σ x.1 else (σ x.1)⁻¹

def σw (V : SW) : F := (V.map σl).prod

lemma σw_append (U V : SW) : σw (U ++ V) = σw U * σw V := by simp [σw, List.prod_append]

lemma σw_cons (x : ℕ × Bool) (V : SW) : σw (x :: V) = σl x * σw V := by simp [σw]

/-- `σ_{m+q-1}^{-1} ⋯ σ_m^{-1}`. -/
def negRun (m : ℕ) : ℕ → SW
  | 0 => []
  | q + 1 => (m + q, false) :: negRun m q

def invSW (V : SW) : SW := (V.map fun x => (x.1, !x.2)).reverse

lemma σw_invSW : ∀ V : SW, σw (invSW V) = (σw V)⁻¹
  | [] => by simp [invSW, σw]
  | x :: V => by
    have ih := σw_invSW V
    simp only [invSW, List.map_cons, List.reverse_cons, σw_append] at ih ⊢
    rw [ih, σw_cons]
    rcases x with ⟨j, _ | _⟩ <;> simp [σw, σl]

lemma σw_negRun (m : ℕ) : ∀ q : ℕ, σw (negRun m q) = a ^ m * Pσ q * (a ^ m)⁻¹
  | 0 => by simp [negRun, σw, Pσ]
  | q + 1 => by
    rw [negRun, σw_cons, σw_negRun m q]
    simp only [σl, Bool.false_eq_true, ↓reduceIte, Pσ, σ_add]
    group

/-- `s(m, q) = a^m b^q`. -/
def sv (m q : ℕ) : F := a ^ m * b ^ q

/-- One collection step. -/
def step (st : ℕ × ℕ × SW) (l : Letter) : ℕ × ℕ × SW :=
  match l.1.val, l.2 with
  | 0, true => (st.1 + 1, st.2.1, st.2.2 ++ negRun st.1 st.2.1)
  | 0, false => (st.1 - 1, st.2.1, st.2.2 ++ invSW (negRun (st.1 - 1) st.2.1))
  | 1, true => (st.1, st.2.1 + 1, st.2.2)
  | 1, false => (st.1, st.2.1 - 1, st.2.2)
  | _, e => (st.1, st.2.1, st.2.2 ++ [(st.1 + st.2.1, e)])

lemma hcDehn {A : ℕ} (q : ℕ) : (1 + A) * q ^ 2 ≤ q + q * ((1 + A) * q ^ 2) := by
  rcases q with _ | q
  · simp
  · exact le_add_left (Nat.le_mul_of_pos_left _ (by omega))

/-- **One step of buffered collection**, at cost `q + q (1+A) q²`. -/
theorem step_areaEq {M A : ℕ} (hA : AstarLE M A) (m q : ℕ) (V : SW) (l : Letter) (hq : q ≤ M)
    (hm : l = (0, false) → 1 ≤ m) (hq1 : l = (1, false) → 1 ≤ q) :
    AreaEq (σw V * sv m q * letterF l)
      (σw (step (m, q, V) l).2.2 * sv (step (m, q, V) l).1 (step (m, q, V) l).2.1)
      (q + q * ((1 + A) * q ^ 2)) := by
  rcases l with ⟨⟨_ | _ | _ | i, hi⟩, _ | _⟩
  · -- a⁻¹
    obtain ⟨m, rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by have := hm rfl; omega⟩
    have h := (AreaEq.refl (σw V)).mul (collect_rule_a_inv hA m q hq)
    refine areaEq_congr h ?_ ?_ (by omega)
    · simp [sv, letterF, mul_assoc]; rfl
    · simp only [step, Nat.add_sub_cancel, σw_append, σw_invSW, σw_negRun, sv, mul_assoc]
  · -- a
    have h := (AreaEq.refl (σw V)).mul (collect_rule_a hA m q hq)
    refine areaEq_congr h ?_ ?_ (by omega)
    · simp [sv, letterF, mul_assoc]; rfl
    · simp only [step, σw_append, σw_negRun, sv, mul_assoc]
  · -- b⁻¹
    obtain ⟨q, rfl⟩ : ∃ q', q = q' + 1 := ⟨q - 1, by have := hq1 rfl; omega⟩
    refine (AreaEq.of_eq ?_).mono (Nat.zero_le _)
    simp only [step, Nat.add_sub_cancel, sv, letterF, pow_succ]
    simp [mul_assoc, b]
  · -- b
    refine (AreaEq.of_eq ?_).mono (Nat.zero_le _)
    simp only [step, sv, letterF, pow_succ]
    simp [mul_assoc, b]
  · -- α⁻¹
    have h := (((AreaEq.refl (σw V * (σ (m + q))⁻¹)).mul (collect_rule_α hA m q hq).symm).mul
      (AreaEq.refl α⁻¹))
    refine areaEq_congr h ?_ ?_ (by have := hcDehn (A := A) q; omega)
    · simp [sv, letterF, mul_assoc, α]
    · simp only [step, σw, sv]
      simp [mul_assoc, α, σl]
  · -- α
    have h := (AreaEq.refl (σw V)).mul (collect_rule_α hA m q hq)
    refine areaEq_congr h ?_ ?_ (by have := hcDehn (A := A) q; omega)
    · simp [sv, letterF, mul_assoc, α]
    · simp only [step, σw, sv]
      simp [mul_assoc, σl]
  · omega
  · omega

lemma step_bounds (m q : ℕ) (V : SW) (l : Letter) :
    m - 1 ≤ (step (m, q, V) l).1 ∧ (step (m, q, V) l).1 ≤ m + 1 ∧
      q - 1 ≤ (step (m, q, V) l).2.1 ∧ (step (m, q, V) l).2.1 ≤ q + 1 := by
  rcases l with ⟨⟨_ | _ | _ | i, hi⟩, _ | _⟩ <;> simp [step] <;> omega

lemma step_len (m q : ℕ) (V : SW) (l : Letter) :
    (step (m, q, V) l).2.2.length ≤ V.length + q + 1 := by
  have h1 : ∀ m q, (negRun m q).length = q := by
    intro m q; induction q with
    | zero => rfl
    | succ q ih => simp [negRun, ih]
  rcases l with ⟨⟨_ | _ | _ | i, hi⟩, _ | _⟩ <;> simp [step, invSW, h1] <;> omega

lemma step_idx (m q : ℕ) (V : SW) (l : Letter) (B : ℕ) (hV : ∀ x ∈ V, x.1 ≤ B)
    (hB : m + q ≤ B) : ∀ x ∈ (step (m, q, V) l).2.2, x.1 ≤ B := by
  have h1 : ∀ m q, ∀ x ∈ negRun m q, x.1 + 1 ≤ m + q := by
    intro m q; induction q with
    | zero => simp [negRun]
    | succ q ih =>
      intro x hx; simp only [negRun, List.mem_cons] at hx
      rcases hx with rfl | hx
      · simp; omega
      · have := ih x hx; omega
  rcases l with ⟨⟨_ | _ | _ | i, hi⟩, _ | _⟩ <;>
    simp only [step, List.mem_append, invSW, List.mem_reverse, List.mem_map, List.mem_singleton] <;>
    intro x hx
  · rcases hx with hx | ⟨y, hy, rfl⟩
    · exact hV x hx
    · have := h1 _ _ y hy; simp; omega
  · rcases hx with hx | hx
    · exact hV x hx
    · have := h1 _ _ x hx; omega
  · exact hV x hx
  · exact hV x hx
  · rcases hx with hx | rfl
    · exact hV x hx
    · simpa using hB
  · rcases hx with hx | rfl
    · exact hV x hx
    · simpa using hB
  · omega
  · omega

lemma cost_mono {A q M : ℕ} (h : q ≤ M) :
    q + q * ((1 + A) * q ^ 2) ≤ M + M * ((1 + A) * M ^ 2) := by
  have h2 : q ^ 2 ≤ M ^ 2 := Nat.pow_le_pow_left h 2
  have h3 : (1 + A) * q ^ 2 ≤ (1 + A) * M ^ 2 := Nat.mul_le_mul_left _ h2
  have h4 : q * ((1 + A) * q ^ 2) ≤ M * ((1 + A) * M ^ 2) := Nat.mul_le_mul h h3
  omega

/-- **Buffered collection of a word**: if `|L| ≤ m`, `|L| ≤ q` and `q + |L| ≤ M`, then
`σw V · s(m,q) · L` is rewritten into `σw V' · s(m', q')` at cost `|L| (M + M(1+A)M²)`. -/
theorem collect_list {M A : ℕ} (hA : AstarLE M A) : ∀ (L : List Letter) (m q : ℕ) (V : SW),
    L.length ≤ m → L.length ≤ q → q + L.length ≤ M →
    AreaEq (σw V * sv m q * wordF L)
      (σw (L.foldl step (m, q, V)).2.2 * sv (L.foldl step (m, q, V)).1 (L.foldl step (m, q, V)).2.1)
      (L.length * (M + M * ((1 + A) * M ^ 2)))
  | [], m, q, V, _, _, _ => by
    show AreaEq (σw V * sv m q * wordF []) (σw V * sv m q) _
    exact (AreaEq.of_eq (by rw [show wordF [] = 1 from rfl, mul_one])).mono (Nat.zero_le _)
  | l :: L, m, q, V, hm, hq, hM => by
    simp only [List.length_cons] at hm hq hM
    have h1 := step_areaEq hA m q V l (by omega) (fun _ => by omega) (fun _ => by omega)
    obtain ⟨b1, b2, b3, b4⟩ := step_bounds m q V l
    rw [List.foldl_cons]
    generalize hs : step (m, q, V) l = st at h1 b1 b2 b3 b4 ⊢
    obtain ⟨m', q', V'⟩ := st
    have ih := collect_list hA L m' q' V' (by simp at b1; omega) (by simp at b3; omega)
      (by simp at b4; omega)
    have h2 := (h1.mul (AreaEq.refl (wordF L))).trans ih
    refine areaEq_congr h2 ?_ ?_ ?_
    · simp [wordF, mul_assoc]
    · rfl
    · have := cost_mono (A := A) (show q ≤ M by omega)
      simp only [List.length_cons, Nat.succ_mul]; omega

end Houghton
