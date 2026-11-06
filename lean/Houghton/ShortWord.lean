import Houghton.CornerFin

/-!
# The short-word estimate of Proposition `prop:corner`

At a clock `(i, j)` with `m ≤ i, j ≤ M - 1 - m` the coordinates `1, …, L` of the corner model are
identified (`ew`) with the window `S_{i,j}` of `Y` (the first `ℓ-i-j`, `ℓ+i`, `ℓ+j` points of
rays 1, 2, 3); a word of length `≤ m` then moves colours exactly as its element of `H₃` moves points.
Consequence (`fixed_card_le`): a word of length `≤ m` representing a nonidentity element of `H₃`
fixes at most a fraction `(4m + 1)/M` of `Ω` (the paper's `s⁻¹ + 4t/M` with `s = M`).
-/

namespace Houghton.Corner

open Finset

/-! ### Translations -/

def dIL (l : Letter) : ℤ := if l.1 = 0 then (if l.2 then 1 else -1) else 0
def dJL (l : Letter) : ℤ := if l.1 = 1 then (if l.2 then 1 else -1) else 0
def tauL (l : Letter) (r : Fin 3) : ℤ := if r = 0 then -dIL l - dJL l else if r = 1 then dIL l else dJL l

def dI (u : List ℕ) : ℤ := (u.map fun c => dIL (codeLetter c)).sum
def dJ (u : List ℕ) : ℤ := (u.map fun c => dJL (codeLetter c)).sum

def trW (u : List ℕ) (r : Fin 3) : ℤ := if r = 0 then -dI u - dJ u else if r = 1 then dI u else dJ u

theorem dIL_abs (l : Letter) : -1 ≤ dIL l ∧ dIL l ≤ 1 := by
  unfold dIL; split_ifs <;> omega
theorem dJL_abs (l : Letter) : -1 ≤ dJL l ∧ dJL l ≤ 1 := by
  unfold dJL; split_ifs <;> omega
theorem dIL_dJL (l : Letter) : -1 ≤ dIL l + dJL l ∧ dIL l + dJL l ≤ 1 := by
  unfold dIL dJL; split_ifs <;> simp_all

theorem trW_cons (c : ℕ) (u : List ℕ) (r : Fin 3) :
    trW (c :: u) r = tauL (codeLetter c) r + trW u r := by
  simp only [trW, tauL, dI, dJ, List.map_cons, List.sum_cons]
  split_ifs <;> ring

theorem dI_abs (u : List ℕ) : |dI u| ≤ u.length := by
  induction u with
  | nil => simp [dI]
  | cons c u ih =>
    simp only [dI, List.map_cons, List.sum_cons, List.length_cons] at ih ⊢
    have := dIL_abs (codeLetter c); rw [abs_le] at ih ⊢; push_cast; constructor <;> linarith
theorem dJ_abs (u : List ℕ) : |dJ u| ≤ u.length := by
  induction u with
  | nil => simp [dJ]
  | cons c u ih =>
    simp only [dJ, List.map_cons, List.sum_cons, List.length_cons] at ih ⊢
    have := dJL_abs (codeLetter c); rw [abs_le] at ih ⊢; push_cast; constructor <;> linarith

theorem letterAct_far (l : Letter) (r : Fin 3) (n : ℕ) (hn : 2 ≤ n) :
    ∃ n', letterAct l (r, n) = (r, n') ∧ (n' : ℤ) = n + tauL l r := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
  obtain ⟨⟨_ | _ | _ | i, hi⟩, _ | _⟩ := l <;> obtain ⟨_ | _ | _ | r', hr⟩ := r <;>
    first
    | omega
    | exact ⟨_, rfl, by simp [tauL, dIL, dJL]; omega⟩
    | exact ⟨_, rfl, by simp [tauL, dIL, dJL]⟩

theorem wordAct_append (A B : List Letter) (y : Y) :
    wordAct (A ++ B) y = wordAct B (wordAct A y) := by
  induction A generalizing y with
  | nil => rfl
  | cons l A ih => exact ih _

theorem wActC_cons (c : ℕ) (u : List ℕ) (y : Y) :
    wActC (c :: u) y = wActC u (letterAct (codeLetter c) y) := rfl

/-- Far points are translated. -/
theorem wActC_far (u : List ℕ) (r : Fin 3) (n : ℕ) (hn : u.length + 1 ≤ n) :
    ∃ n', wActC u (r, n) = (r, n') ∧ (n' : ℤ) = n + trW u r := by
  induction u generalizing n with
  | nil =>
    refine ⟨n, rfl, ?_⟩
    simp only [trW, dI, dJ, List.map_nil, List.sum_nil]; split_ifs <;> simp
  | cons c u ih =>
    obtain ⟨n1, h1, h1'⟩ := letterAct_far (codeLetter c) r n (by simp at hn; omega)
    have hb : -1 ≤ tauL (codeLetter c) r ∧ tauL (codeLetter c) r ≤ 1 := by
      have := dIL_abs (codeLetter c); have := dJL_abs (codeLetter c)
      have := dIL_dJL (codeLetter c)
      unfold tauL; split_ifs <;> omega
    obtain ⟨n2, h2, h2'⟩ := ih n1 (by simp at hn; omega)
    refine ⟨n2, by rw [wActC_cons, h1, h2], ?_⟩
    rw [h2', h1', trW_cons]; ring

theorem wActC_far_fix (u : List ℕ) (h0 : dI u = 0) (h1 : dJ u = 0) (r : Fin 3) (n : ℕ)
    (hn : u.length + 1 ≤ n) : wActC u (r, n) = (r, n) := by
  obtain ⟨n', h, h'⟩ := wActC_far u r n hn
  have : trW u r = 0 := by
    simp only [trW, h0, h1]; split_ifs <;> simp
  rw [h]; congr 1; omega

variable (M : ℕ) [NeZero M]

/-! ### Clocks -/

theorem natActL_clock (l : Letter) (s : CState M (Fin M)) :
    (natActL M l s).1 = s.1 + (dIL l : ZMod M) ∧ (natActL M l s).2.1 = s.2.1 + (dJL l : ZMod M) := by
  obtain ⟨⟨_ | _ | _ | i, hi⟩, _ | _⟩ := l
  · show (actAinv M s).1 = _ ∧ (actAinv M s).2.1 = _
    simp [actAinv, dIL, dJL, sub_eq_add_neg]
  · show (actA M s).1 = _ ∧ (actA M s).2.1 = _
    simp [actA, dIL, dJL]
  · show (actBinv M s).1 = _ ∧ (actBinv M s).2.1 = _
    simp [actBinv, dIL, dJL, sub_eq_add_neg]
  · show (actB M s).1 = _ ∧ (actB M s).2.1 = _
    simp [actB, dIL, dJL]
  · show (actα M s).1 = _ ∧ (actα M s).2.1 = _
    simp [actα, dIL, dJL]
  · show (actα M s).1 = _ ∧ (actα M s).2.1 = _
    simp [actα, dIL, dJL]
  · omega
  · omega

theorem natNest_clock (u : List ℕ) (s : CState M (Fin M)) :
    (natNest M u s).1 = s.1 + (dI u : ZMod M) ∧ (natNest M u s).2.1 = s.2.1 + (dJ u : ZMod M) := by
  induction u generalizing s with
  | nil => simp [natNest, dI, dJ]
  | cons c u ih =>
    obtain ⟨h1, h2⟩ := ih (natActL M (codeLetter c) s)
    obtain ⟨h3, h4⟩ := natActL_clock M (codeLetter c) s
    simp only [natNest, dI, dJ, List.map_cons, List.sum_cons] at h1 h2 ⊢
    rw [h1, h2, h3, h4]; push_cast; constructor <;> ring

theorem val_sub_one' (hM : 2 ≤ M) (i : ZMod M) (h : 1 ≤ i.val) : (i - 1).val = i.val - 1 := by
  have h1 : (1 : ZMod M).val = 1 := by
    rw [ZMod.val_one_eq_one_mod, Nat.mod_eq_of_lt (by omega)]
  rw [ZMod.val_sub (by rw [h1]; exact h), h1]

theorem val_add_one' (hM : 2 ≤ M) (i : ZMod M) (h : i.val + 1 < M) : (i + 1).val = i.val + 1 := by
  rw [val_add_one M hM]; simp [h]

/-! ### Windows -/

/-- Coordinate `k` at clock `(i, j)` is the point `ew i j k` of the window `S_{i,j}`. -/
def ew (i j k : ℕ) : Y :=
  if k ≤ ell M - i - j then (0, k - 1)
  else if k ≤ 2 * ell M - j then (1, k - (ell M - i - j) - 1)
  else (2, k - (2 * ell M - j) - 1)

/-- The coordinate of a point of the window. -/
def winv (i j : ℕ) (q : Y) : ℕ :=
  if q.1.val = 0 then q.2 + 1 else if q.1.val = 1 then ell M - i - j + q.2 + 1
  else 2 * ell M - j + q.2 + 1

theorem aFun_0 (n : ℕ) : aFun (0, n) = if n = 0 then (1, 0) else (0, n - 1) := by
  cases n <;> rfl
theorem aFun_1 (n : ℕ) : aFun (1, n) = (1, n + 1) := rfl
theorem aFun_2 (n : ℕ) : aFun (2, n) = (2, n) := rfl
theorem bFun_0 (n : ℕ) : bFun (0, n) = if n = 0 then (2, 0) else (0, n - 1) := by
  cases n <;> rfl
theorem bFun_1 (n : ℕ) : bFun (1, n) = (1, n) := rfl
theorem bFun_2 (n : ℕ) : bFun (2, n) = (2, n + 1) := rfl
theorem alFun_0 (n : ℕ) : alFun (0, n) = if n = 0 then (0, 1) else if n = 1 then (0, 0) else (0, n) := by
  rcases n with _ | _ | n <;> rfl
theorem alFun_1 (n : ℕ) : alFun (1, n) = (1, n) := rfl
theorem alFun_2 (n : ℕ) : alFun (2, n) = (2, n) := rfl

theorem win_a (i j k : ℕ) (hi : i + 1 ≤ M - 1) (hj : j ≤ M - 1) (hk1 : 1 ≤ k)
    (hk2 : k ≤ 3 * ell M) : aFun (ew M i j k) = ew M (i + 1) j (cyc (ell M - i - j) k) := by
  have hl : ell M = 2 * M + 2 := rfl
  unfold ew cyc
  split_ifs <;> simp only [aFun_0, aFun_1, aFun_2] <;> (try split_ifs) <;>
    first | (exfalso; omega) | exact Prod.ext rfl (by simp only; omega) | rfl

theorem win_b (i j k : ℕ) (hi : i ≤ M - 1) (hj : j + 1 ≤ M - 1) (hk1 : 1 ≤ k)
    (hk2 : k ≤ 3 * ell M) : bFun (ew M i j k) = ew M i (j + 1) (cyc (2 * ell M - j) k) := by
  have hl : ell M = 2 * M + 2 := rfl
  unfold ew cyc
  split_ifs <;> simp only [bFun_0, bFun_1, bFun_2] <;> (try split_ifs) <;>
    first | (exfalso; omega) | exact Prod.ext rfl (by simp only; omega) | rfl

theorem win_α (i j k : ℕ) (hi : i ≤ M - 1) (hj : j ≤ M - 1) (hk1 : 1 ≤ k)
    (hk2 : k ≤ 3 * ell M) : alFun (ew M i j k) = ew M i j (swp 1 2 k) := by
  have hl : ell M = 2 * M + 2 := rfl
  unfold ew swp
  split_ifs <;> simp only [alFun_0, alFun_1, alFun_2] <;> (try split_ifs) <;>
    first | (exfalso; omega) | rfl

theorem ew_winv (m i j : ℕ) (hi : i + m ≤ M - 1) (hj : j + m ≤ M - 1) (q : Y) (hq : q.2 ≤ m) :
    ew M i j (winv M i j q) = q ∧ 1 ≤ winv M i j q ∧ winv M i j q ≤ 3 * ell M := by
  have hl : ell M = 2 * M + 2 := rfl
  obtain ⟨⟨_ | _ | _ | r, hr⟩, n⟩ := q
  · simp only at hq
    have hw : winv M i j (⟨0, hr⟩, n) = n + 1 := by simp [winv]
    rw [hw]; refine ⟨?_, by omega, by omega⟩
    simp only [ew]; rw [if_pos (by omega)]; exact Prod.ext rfl (by simp)
  · simp only at hq
    have hw : winv M i j (⟨1, hr⟩, n) = ell M - i - j + n + 1 := by simp [winv]
    rw [hw]; refine ⟨?_, by omega, by omega⟩
    simp only [ew]; rw [if_neg (by omega), if_pos (by omega)]
    exact Prod.ext rfl (by simp only; omega)
  · simp only at hq
    have hw : winv M i j (⟨2, hr⟩, n) = 2 * ell M - j + n + 1 := by simp [winv]
    rw [hw]; refine ⟨?_, by omega, by omega⟩
    simp only [ew]; rw [if_neg (by omega), if_neg (by omega)]
    exact Prod.ext rfl (by simp only; omega)
  · omega

theorem winv_inj (i j : ℕ) {p q : Y} (h : winv M i j p = winv M i j q) (hp : ew M i j (winv M i j p) = p)
    (hq : ew M i j (winv M i j q) = q) : p = q := by
  rw [← hp, ← hq, h]

/-! ### Colours follow points -/

/-- The colouring of state `s` is `c` on the window. -/
def Rel (s : CState M (Fin M)) (c : Y → Fin M) : Prop :=
  ∀ k, 1 ≤ k → k ≤ 3 * ell M → s.2.2 k = c (ew M s.1.val s.2.1.val k)

theorem cyc_mem (r k L : ℕ) (hr1 : 1 ≤ r) (hr : r ≤ L) (hk1 : 1 ≤ k) (hk2 : k ≤ L) :
    1 ≤ cyc r k ∧ cyc r k ≤ L := by
  unfold cyc; split_ifs <;> omega
theorem cycInv_mem (r k L : ℕ) (hr : r ≤ L) (hk1 : 1 ≤ k) (hk2 : k ≤ L) :
    1 ≤ cycInv r k ∧ cycInv r k ≤ L := by
  unfold cycInv; split_ifs <;> constructor <;> omega
theorem swp_mem (k L : ℕ) (hL : 2 ≤ L) (hk1 : 1 ≤ k) (hk2 : k ≤ L) :
    1 ≤ swp 1 2 k ∧ swp 1 2 k ≤ L := by
  unfold swp; split_ifs <;> constructor <;> omega

theorem rel_step (hM : 2 ≤ M) (l : Letter) (s : CState M (Fin M)) (c : Y → Fin M)
    (hi1 : 1 ≤ s.1.val) (hi2 : s.1.val + 1 ≤ M - 1) (hj1 : 1 ≤ s.2.1.val)
    (hj2 : s.2.1.val + 1 ≤ M - 1) (h : Rel M s c) :
    Rel M (natActL M l s) (fun q => c (letterAct (l.1, !l.2) q)) := by
  obtain ⟨i, j, X⟩ := s
  simp only at hi1 hi2 hj1 hj2
  have hl : ell M = 2 * M + 2 := rfl
  obtain ⟨⟨_ | _ | _ | n, hn⟩, _ | _⟩ := l
  · -- a⁻¹
    intro k hk1 hk2
    have hv : (i - 1).val = i.val - 1 := val_sub_one' M hM i hi1
    simp only [natActL, actAinv, Bool.not_false]
    rw [hv]
    obtain ⟨hm1, hm2⟩ := cyc_mem (ell M - (i.val - 1) - j.val) k (3 * ell M) (by omega) (by omega) hk1 hk2
    have hh := h _ hm1 hm2; dsimp only at hh; rw [hh]
    have := win_a M (i.val - 1) j.val k (by omega) (by omega) hk1 hk2
    have e : i.val - 1 + 1 = i.val := by omega
    rw [e] at this
    show _ = c (aFun _)
    rw [this]
  · -- a
    intro k hk1 hk2
    have hv : (i + 1).val = i.val + 1 := val_add_one' M hM i (by omega)
    simp only [natActL, actA, Bool.not_true]
    rw [hv]
    obtain ⟨hm1, hm2⟩ := cycInv_mem (ell M - i.val - j.val) k (3 * ell M) (by omega) hk1 hk2
    have hh := h _ hm1 hm2; dsimp only at hh; rw [hh]
    have := win_a M i.val j.val _ (by omega) (by omega) hm1 hm2
    rw [cyc_cycInv _ _ (by omega)] at this
    show _ = c (aInv _)
    rw [← this, aInv_aFun]
  · -- b⁻¹
    intro k hk1 hk2
    have hv : (j - 1).val = j.val - 1 := val_sub_one' M hM j hj1
    simp only [natActL, actBinv, Bool.not_false, Bfwd]
    rw [hv, if_pos (by omega)]
    obtain ⟨hm1, hm2⟩ := cyc_mem (2 * ell M - (j.val - 1)) k (3 * ell M) (by omega) (by omega) hk1 hk2
    have hh := h _ hm1 hm2; dsimp only at hh; rw [hh]
    have := win_b M i.val (j.val - 1) k (by omega) (by omega) hk1 hk2
    have e : j.val - 1 + 1 = j.val := by omega
    rw [e] at this
    show _ = c (bFun _)
    rw [this]
  · -- b
    intro k hk1 hk2
    have hv : (j + 1).val = j.val + 1 := val_add_one' M hM j (by omega)
    simp only [natActL, actB, Bool.not_true, Binv]
    rw [hv, if_pos (by omega)]
    obtain ⟨hm1, hm2⟩ := cycInv_mem (2 * ell M - j.val) k (3 * ell M) (by omega) hk1 hk2
    have hh := h _ hm1 hm2; dsimp only at hh; rw [hh]
    have := win_b M i.val j.val _ (by omega) (by omega) hm1 hm2
    rw [cyc_cycInv _ _ (by omega)] at this
    show _ = c (bInv _)
    rw [← this, bInv_bFun]
  · -- α⁻¹
    intro k hk1 hk2
    simp only [natActL, actα]
    obtain ⟨hm1, hm2⟩ := swp_mem k (3 * ell M) (by omega) hk1 hk2
    have hh := h _ hm1 hm2; dsimp only at hh; rw [hh]
    show _ = c (alFun _)
    rw [win_α M i.val j.val k (by omega) (by omega) hk1 hk2]
  · -- α
    intro k hk1 hk2
    simp only [natActL, actα]
    obtain ⟨hm1, hm2⟩ := swp_mem k (3 * ell M) (by omega) hk1 hk2
    have hh := h _ hm1 hm2; dsimp only at hh; rw [hh]
    show _ = c (alFun _)
    rw [win_α M i.val j.val k (by omega) (by omega) hk1 hk2]
  · omega
  · omega

theorem natActL_val (hM : 2 ≤ M) (l : Letter) (s : CState M (Fin M))
    (hi1 : 1 ≤ s.1.val) (hi2 : s.1.val + 1 ≤ M - 1) (hj1 : 1 ≤ s.2.1.val)
    (hj2 : s.2.1.val + 1 ≤ M - 1) :
    s.1.val ≤ (natActL M l s).1.val + 1 ∧ (natActL M l s).1.val ≤ s.1.val + 1 ∧
      s.2.1.val ≤ (natActL M l s).2.1.val + 1 ∧ (natActL M l s).2.1.val ≤ s.2.1.val + 1 := by
  obtain ⟨i, j, X⟩ := s
  simp only at hi1 hi2 hj1 hj2
  obtain ⟨⟨_ | _ | _ | n, hn⟩, _ | _⟩ := l
  · simp only [natActL, actAinv]; rw [val_sub_one' M hM i hi1]; omega
  · simp only [natActL, actA]; rw [val_add_one' M hM i (by omega)]; omega
  · simp only [natActL, actBinv]; rw [val_sub_one' M hM j hj1]; omega
  · simp only [natActL, actB]; rw [val_add_one' M hM j (by omega)]; omega
  · simp only [natActL, actα]; omega
  · simp only [natActL, actα]; omega
  · omega
  · omega

theorem codeLetter_inv (c : ℕ) : codeLetter (Word.inv c) = ((codeLetter c).1, !(codeLetter c).2) := by
  unfold codeLetter Word.inv
  rcases Nat.mod_two_eq_zero_or_one c with h | h
  · have hb : Nat.beq (c % 2) 0 = true := by rw [h]; rfl
    rw [hb]; simp only [cond_true]
    refine Prod.ext (Fin.ext ?_) ?_
    · simp only; omega
    · simp only [h]; simp; omega
  · have hb : Nat.beq (c % 2) 0 = false := by rw [h]; rfl
    rw [hb]; simp only [cond_false]
    refine Prod.ext (Fin.ext ?_) ?_
    · simp only; omega
    · simp only [h]; simp; omega

theorem wActC_invW_cons (c : ℕ) (u : List ℕ) (q : Y) :
    wActC (Word.invW (c :: u)) q = letterAct ((codeLetter c).1, !(codeLetter c).2) (wActC (Word.invW u) q) := by
  simp only [wActC, Word.invW, List.map_cons, List.reverse_cons, List.map_append, wordAct_append,
    List.map_nil]
  rw [← codeLetter_inv]; rfl

/-- **Colours follow points** along a word, away from the wrap lines. -/
theorem rel_word (hM : 2 ≤ M) (u : List ℕ) (s : CState M (Fin M)) (c : Y → Fin M)
    (hi1 : u.length ≤ s.1.val) (hi2 : s.1.val + u.length ≤ M - 1) (hj1 : u.length ≤ s.2.1.val)
    (hj2 : s.2.1.val + u.length ≤ M - 1) (h : Rel M s c) :
    Rel M (natNest M u s) (fun q => c (wActC (Word.invW u) q)) := by
  induction u generalizing s c with
  | nil => exact h
  | cons x u ih =>
    simp only [List.length_cons] at hi1 hi2 hj1 hj2
    have hs := rel_step M hM (codeLetter x) s c (by omega) (by omega) (by omega) (by omega) h
    obtain ⟨v1, v2, v3, v4⟩ := natActL_val M hM (codeLetter x) s (by omega) (by omega) (by omega)
      (by omega)
    have := ih (natActL M (codeLetter x) s) _ (by omega) (by omega) (by omega) (by omega) hs
    simp only [natNest]
    intro k hk1 hk2
    rw [this k hk1 hk2]
    dsimp only
    rw [wActC_invW_cons]


/-! ### The fixed-point estimate -/

theorem ltr_eq (c : ℕ) : ltr c = letterF (codeLetter c) := by
  unfold ltr genN letterF codeLetter
  by_cases h : c % 2 = 0
  · have h' : (c % 2 == 0) = true := by simpa using h
    simp [h, h']
  · have h' : (c % 2 == 0) = false := by simpa using h
    simp [h, h']

theorem ev_eq_wordF (w : List ℕ) : ev w = wordF (w.map codeLetter) := by
  simp only [ev, wordF, List.map_map]
  congr 1; apply List.map_congr_left; intro c _; exact ltr_eq c

theorem wActC_eq (w : List ℕ) (y : Y) : wActC w y = (ρH (ev w)).unop y := by
  rw [ev_eq_wordF, rho_word_apply]; rfl

theorem wActC_inv_cancel (u : List ℕ) (y : Y) : wActC (Word.invW u) (wActC u y) = y := by
  rw [wActC_eq, wActC_eq, ev_invW, map_inv, MulOpposite.unop_inv]
  exact (ρH (ev u)).unop.symm_apply_apply y

theorem winv_ew (i j k : ℕ) (hi : i ≤ M - 1) (hj : j ≤ M - 1) (hk1 : 1 ≤ k) (hk2 : k ≤ 3 * ell M) :
    winv M i j (ew M i j k) = k := by
  have hl : ell M = 2 * M + 2 := rfl
  unfold ew; split_ifs <;> simp [winv] <;> omega

theorem rel_iota (ω : Ω M) :
    Rel M (iota M ω) (fun q => ω.2.2 (clampF M (winv M ω.1.val ω.2.1.val q))) := by
  intro k hk1 hk2
  simp only [iota]
  rw [winv_ew M _ _ k (by have := ZMod.val_lt ω.1; omega) (by have := ZMod.val_lt ω.2.1; omega)
    hk1 hk2]

/-- At a good clock, a state fixed by `u` has equal colours at the coordinates of `y` and of its
image under `u`. -/
theorem fixed_colours (hM : 2 ≤ M) (u : List ℕ) (m : ℕ) (hlen : u.length ≤ m) (ω : Ω M)
    (hi1 : m ≤ ω.1.val) (hi2 : ω.1.val + m ≤ M - 1) (hj1 : m ≤ ω.2.1.val)
    (hj2 : ω.2.1.val + m ≤ M - 1) (hfix : finNest M u ω = ω) (y : Y) :
    ω.2.2 (clampF M (winv M ω.1.val ω.2.1.val (wActC u y))) =
      ω.2.2 (clampF M (winv M ω.1.val ω.2.1.val y)) ∨ (wActC u y).2 > m ∨ y.2 > m := by
  by_cases hp : (wActC u y).2 ≤ m
  · by_cases hy : y.2 ≤ m
    · left
      have hs : natNest M u (iota M ω) = iota M ω := by rw [← iota_finNest M hM, hfix]
      have hr := rel_word M hM u (iota M ω) _ (by simp [iota]; omega) (by simp [iota]; omega)
        (by simp [iota]; omega) (by simp [iota]; omega) (rel_iota M ω)
      rw [hs] at hr
      obtain ⟨e1, k1, k2⟩ := ew_winv M m ω.1.val ω.2.1.val (by omega) (by omega) _ hp
      have h1 := hr _ k1 k2
      have h2 := rel_iota M ω _ k1 k2
      simp only [iota] at h1 h2
      rw [e1, wActC_inv_cancel] at h1
      rw [e1] at h2
      rw [← h2, h1]
    · right; right; omega
  · right; left; omega

theorem card_eq_le (N : ℕ) (a b : Fin N) (hab : a ≠ b) :
    (univ.filter fun x : Fin N → Fin M => x a = x b).card ≤ M ^ (N - 1) := by
  have hc : Fintype.card ({t // t ≠ b} → Fin M) = M ^ (N - 1) := by
    rw [Fintype.card_fun, Fintype.card_fin]
    congr 1
    rw [Fintype.card_subtype_compl, Fintype.card_fin, Fintype.card_subtype_eq]
  rw [← hc, ← card_univ]
  apply card_le_card_of_injOn (fun x t => x t.val) (fun _ _ => mem_univ _)
  intro x hx x' hx' hxx
  simp only [coe_filter, Set.mem_setOf_eq, mem_univ, true_and] at hx hx'
  funext t
  by_cases ht : t = b
  · subst ht
    rw [← hx, ← hx']
    exact congrFun hxx ⟨a, hab⟩
  · exact congrFun hxx ⟨t, ht⟩

/-- Bad clock values. -/
def badV (m : ℕ) : Finset (ZMod M) := univ.filter fun i => ¬ (m ≤ i.val ∧ i.val + m ≤ M - 1)

theorem card_badV (m : ℕ) : (badV M m).card ≤ 2 * m := by
  have hsub : (badV M m).map ⟨ZMod.val, ZMod.val_injective M⟩ ⊆ range m ∪ Ico (M - m) M := by
    intro n hn
    simp only [mem_map, badV, mem_filter, mem_univ, true_and, Function.Embedding.coeFn_mk] at hn
    obtain ⟨i, hi, rfl⟩ := hn
    have := ZMod.val_lt i
    simp only [mem_union, mem_range, mem_Ico]; omega
  have := (card_le_card hsub).trans (card_union_le _ _)
  simp only [card_map, card_range, Nat.card_Ico] at this
  omega

theorem natNest_fix_clock (hM : 2 ≤ M) (u : List ℕ) (hlen : u.length < M) (ω : Ω M)
    (hfix : finNest M u ω = ω) : dI u = 0 ∧ dJ u = 0 := by
  have hs : natNest M u (iota M ω) = iota M ω := by rw [← iota_finNest M hM, hfix]
  obtain ⟨h1, h2⟩ := natNest_clock M u (iota M ω)
  rw [hs] at h1 h2
  simp only [iota, left_eq_add] at h1 h2
  rw [ZMod.intCast_zmod_eq_zero_iff_dvd] at h1 h2
  have a1 := dI_abs u; have a2 := dJ_abs u
  rw [abs_le] at a1 a2
  constructor
  · obtain ⟨q, hq⟩ := h1
    have : q = 0 := by
      by_contra hq0
      rcases lt_or_gt_of_ne hq0 with h | h
      · nlinarith
      · nlinarith
    rw [hq, this, mul_zero]
  · obtain ⟨q, hq⟩ := h2
    have : q = 0 := by
      by_contra hq0
      rcases lt_or_gt_of_ne hq0 with h | h
      · nlinarith
      · nlinarith
    rw [hq, this, mul_zero]

/-- **Short-word estimate** (Proposition `prop:corner`, with `s = M`): a word of length `≤ m`
representing a nonidentity element of `H₃` fixes at most a fraction `(4m + 1)/M` of `Ω`. -/
theorem fixed_card_le (hM : 2 ≤ M) (u : List ℕ) (m : ℕ) (hlen : u.length ≤ m) (h2m : 2 * m < M)
    (hne : ρH (ev u) ≠ 1) :
    ((univ.filter fun ω => finNest M u ω = ω).card : ℝ) ≤
      (4 * m + 1) / M * Fintype.card (Ω M) := by
  classical
  have hMpos : (0 : ℝ) < M := by exact_mod_cast (show 0 < M by omega)
  obtain ⟨y, hy⟩ : ∃ y, wActC u y ≠ y := by
    by_contra hc; push Not at hc; apply hne
    apply MulOpposite.unop_injective; ext z : 1
    rw [← wActC_eq, hc]; rfl
  by_cases h0 : dI u = 0 ∧ dJ u = 0
  swap
  · have : (univ.filter fun ω => finNest M u ω = ω) = ∅ := by
      ext ω; simp only [mem_filter, mem_univ, true_and, Finset.notMem_empty, iff_false]
      intro hf; exact h0 (natNest_fix_clock M hM u (by omega) ω hf)
    rw [this, card_empty, Nat.cast_zero]; positivity
  obtain ⟨d0, e0⟩ := h0
  set p := wActC u y with hpdef
  have hyn : y.2 ≤ m := by
    by_contra h; exact hy (wActC_far_fix u d0 e0 y.1 y.2 (by omega))
  have hpy : p ≠ y := hy
  have hpn : p.2 ≤ m := by
    by_contra h
    have hfar : wActC u p = p := wActC_far_fix u d0 e0 p.1 p.2 (by omega)
    apply hpy
    rw [wActC_eq] at hfar
    have h2 : (ρH (ev u)).unop p = (ρH (ev u)).unop y := by rw [hfar, hpdef, wActC_eq]
    exact (ρH (ev u)).unop.injective h2
  set N := NN M
  let good : ZMod M × ZMod M → Prop := fun ij =>
    m ≤ ij.1.val ∧ ij.1.val + m ≤ M - 1 ∧ m ≤ ij.2.val ∧ ij.2.val + m ≤ M - 1
  let A : ZMod M × ZMod M → Fin N := fun ij => clampF M (winv M ij.1.val ij.2.val p)
  let B : ZMod M × ZMod M → Fin N := fun ij => clampF M (winv M ij.1.val ij.2.val y)
  have hsub : (univ.filter fun ω => finNest M u ω = ω) ⊆
      ((badV M m) ×ˢ (univ : Finset (ZMod M × (Fin N → Fin M)))) ∪
      ((univ : Finset (ZMod M)) ×ˢ ((badV M m) ×ˢ (univ : Finset (Fin N → Fin M)))) ∪
      ((univ.filter good).biUnion fun ij =>
        (univ.filter fun x : Fin N → Fin M => x (A ij) = x (B ij)).image
          fun x => (ij.1, ij.2, x)) := by
    intro ω hω
    simp only [mem_filter, mem_univ, true_and] at hω
    obtain ⟨i, j, x⟩ := ω
    by_cases hg : good (i, j)
    · apply mem_union_right
      simp only [mem_biUnion, mem_filter, mem_univ, true_and, mem_image]
      refine ⟨(i, j), hg, x, ?_, rfl⟩
      obtain ⟨g1, g2, g3, g4⟩ := hg
      rcases fixed_colours M hM u m hlen (i, j, x) g1 g2 g3 g4 hω y with h | h | h
      · exact h
      · exfalso; simp only [← hpdef] at h; omega
      · exfalso; omega
    · apply mem_union_left
      simp only [good, not_and_or] at hg
      by_cases hi : i ∈ badV M m
      · exact mem_union_left _ (mem_product.mpr ⟨hi, mem_univ _⟩)
      · apply mem_union_right
        refine mem_product.mpr ⟨mem_univ _, mem_product.mpr ⟨?_, mem_univ _⟩⟩
        simp only [badV, mem_filter, mem_univ, true_and, not_and_or, not_not] at hi ⊢
        omega
  have hEq : ((univ.filter good).biUnion fun ij =>
      (univ.filter fun x : Fin N → Fin M => x (A ij) = x (B ij)).image
        fun x => (ij.1, ij.2, x)).card ≤ M * M * M ^ (N - 1) := by
    refine (card_biUnion_le).trans ?_
    calc ∑ ij ∈ univ.filter good, ((univ.filter fun x : Fin N → Fin M => x (A ij) = x (B ij)).image
          fun x => (ij.1, ij.2, x)).card
        ≤ ∑ _ij ∈ (univ : Finset (ZMod M × ZMod M)), M ^ (N - 1) := by
          refine (sum_le_sum fun ij hij => ?_).trans (sum_le_sum_of_subset (filter_subset _ _))
          refine card_image_le.trans (card_eq_le M N _ _ ?_)
          simp only [mem_filter, mem_univ, true_and] at hij
          obtain ⟨g1, g2, g3, g4⟩ := hij
          intro hAB
          simp only [A, B, clampF, Fin.mk.injEq] at hAB
          obtain ⟨e1, k1, k2⟩ := ew_winv M m ij.1.val ij.2.val (by omega) (by omega) p hpn
          obtain ⟨e2, k3, k4⟩ := ew_winv M m ij.1.val ij.2.val (by omega) (by omega) y hyn
          have hl : ell M = 2 * M + 2 := rfl
          have hw : winv M ij.1.val ij.2.val p = winv M ij.1.val ij.2.val y := by omega
          exact hpy (by rw [← e1, ← e2, hw])
      _ = M * M * M ^ (N - 1) := by
          rw [sum_const, card_univ, Fintype.card_prod, ZMod.card, smul_eq_mul]
  have hb1 : ((badV M m) ×ˢ (univ : Finset (ZMod M × (Fin N → Fin M)))).card ≤
      2 * m * (M * M ^ N) := by
    rw [card_product, card_univ, Fintype.card_prod, ZMod.card, Fintype.card_fun]
    simp only [Fintype.card_fin]
    exact Nat.mul_le_mul_right _ (card_badV M m)
  have hb2 : ((univ : Finset (ZMod M)) ×ˢ ((badV M m) ×ˢ (univ : Finset (Fin N → Fin M)))).card ≤
      M * (2 * m * M ^ N) := by
    rw [card_product, card_product, card_univ, card_univ, ZMod.card, Fintype.card_fun]
    simp only [Fintype.card_fin]
    exact Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _ (card_badV M m))
  have htot := (card_le_card hsub).trans ((card_union_le _ _).trans
    (add_le_add ((card_union_le _ _).trans (add_le_add hb1 hb2)) hEq))
  have hP : M ^ N = M * M ^ (N - 1) := by
    rw [← pow_succ']; congr 1
  have key : (univ.filter fun ω => finNest M u ω = ω).card * M ≤ (4 * m + 1) * (M * (M * M ^ N)) := by
    calc _ ≤ (2 * m * (M * M ^ N) + M * (2 * m * M ^ N) + M * M * M ^ (N - 1)) * M :=
          Nat.mul_le_mul_right _ htot
      _ = (4 * m + 1) * (M * (M * M ^ N)) := by rw [hP]; ring
  rw [card_Ω, div_mul_eq_mul_div, le_div_iff₀ hMpos]
  exact_mod_cast key

end Houghton.Corner
