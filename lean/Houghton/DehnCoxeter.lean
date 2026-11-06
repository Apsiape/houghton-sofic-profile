import Houghton.DehnMain

/-! Theorem `thm:dehn`, part 5: Coxeter insertion in `S_{d+1}` (generators `σ_0, …, σ_{d-1}`). -/

namespace Houghton

/-- `Dn lo len = σ_{lo+len-1} ⋯ σ_lo`. -/
def Dn (lo : ℕ) : ℕ → F
  | 0 => 1
  | len + 1 => σ (lo + len) * Dn lo len

lemma Dn_split (lo b : ℕ) : ∀ a' : ℕ, Dn lo (a' + b) = Dn (lo + b) a' * Dn lo b
  | 0 => by simp [Dn]
  | a' + 1 => by
    rw [show a' + 1 + b = (a' + b) + 1 by omega, Dn, Dn, Dn_split lo b a', Nat.add_assoc,
      Nat.add_comm b a', mul_assoc]

lemma Dn_succ_bot (lo len : ℕ) : Dn lo (len + 1) = Dn (lo + 1) len * σ lo := by
  rw [Dn_split lo 1 len]; simp [Dn]

/-- `[σ_i, σ_l]` for far `i, l ≤ M`. -/
lemma far_comm {M A : ℕ} (hA : AstarLE M A) {i l : ℕ} (hi : i ≤ M) (hl : l ≤ M)
    (h : i + 2 ≤ l ∨ l + 2 ≤ i) : AreaLE (comm (σ i) (σ l)) A := by
  simpa using hA i l hi hl h true true

lemma comm_σ_Dn {M A : ℕ} (hA : AstarLE M A) (i lo : ℕ) (hi : i ≤ M) :
    ∀ len : ℕ, lo + len ≤ M + 1 → (∀ t < len, i + 2 ≤ lo + t ∨ lo + t + 2 ≤ i) →
      AreaLE (comm (σ i) (Dn lo len)) (len * A)
  | 0, _, _ => by simpa [Dn, comm] using AreaLE.one
  | len + 1, hlen, hfar => by
    have h1 := far_comm hA hi (l := lo + len) (by omega) (hfar len (by omega))
    have h2 := comm_σ_Dn hA i lo hi len (by omega) (fun t ht => hfar t (by omega))
    exact (h1.comm_mul_right h2).mono (by rw [Nat.succ_mul]; omega)

/-- Moving `σ_i` from the right of `Dn lo len` to its left. -/
lemma move_left {M A : ℕ} (hA : AstarLE M A) (i lo len : ℕ) (hi : i ≤ M) (hlen : lo + len ≤ M + 1)
    (hfar : ∀ t < len, i + 2 ≤ lo + t ∨ lo + t + 2 ≤ i) :
    AreaEq (Dn lo len * σ i) (σ i * Dn lo len) (len * A) := by
  refine ((comm_σ_Dn hA i lo hi len hlen hfar).inv).of_eq ?_
  simp [comm, mul_inv_rev, mul_assoc]

/-- `σ_k² = 1` (one `r₁` cell). -/
lemma σ_sq (k : ℕ) : AreaEq (σ k * σ k) 1 1 := by
  refine ((AreaLE.rel 0).conj (a ^ k)).of_eq ?_
  simp [rel, r₁, σ, pow_two, mul_assoc]

/-- The braid relation `σ_{i}σ_{i-1}σ_{i} = σ_{i-1}σ_iσ_{i-1}` (4 cells). -/
lemma braid (i : ℕ) : AreaEq (σ (i + 1) * σ i * σ (i + 1)) (σ i * σ (i + 1) * σ i) 4 := by
  have h := area_BRAID.conj (a ^ i)
  have e1 : σ (i + 1) = a ^ i * σ 1 * (a ^ i)⁻¹ := σ_add i 1
  have e0 : σ i = a ^ i * σ 0 * (a ^ i)⁻¹ := by simpa using σ_add i 0
  refine areaEq_congr h ?_ ?_ le_rfl
  · rw [e1, e0]; group
  · rw [e1, e0]; group

/-! ### Normal forms and insertion -/

/-- Normal form, top level first: `nfDehn (k :: ks) = nfDehn ks · σ_{j-1} ⋯ σ_k` with `j = |ks| + 1`. -/
def nfDehn : List ℕ → F
  | [] => 1
  | k :: ks => nfDehn ks * Dn k (ks.length + 1 - k)

/-- Each level `j` carries `k ≤ j`. -/
def Valid : List ℕ → Prop
  | [] => True
  | k :: ks => k ≤ ks.length + 1 ∧ Valid ks

/-- Insert `σ_i` on the right of a normal form. -/
def ins : List ℕ → ℕ → List ℕ
  | [], _ => []
  | k :: ks, i =>
    if i + 2 ≤ k then k :: ins ks i
    else if i + 1 = k then (k - 1) :: ks
    else if i = k then (k + 1) :: ks
    else k :: ins ks (i - 1)

lemma ins_length : ∀ (ks : List ℕ) (i : ℕ), (ins ks i).length = ks.length
  | [], _ => rfl
  | k :: ks, i => by
    unfold ins
    split_ifs <;> simp [ins_length ks]

lemma ins_valid : ∀ (ks : List ℕ) (i : ℕ), Valid ks → i < ks.length → Valid (ins ks i)
  | [], _, _, _ => trivial
  | k :: ks, i, ⟨hk, hv⟩, hi => by
    simp only [List.length_cons] at hi
    unfold ins
    split_ifs with h1 h2 h3
    · exact ⟨by rw [ins_length]; exact hk, ins_valid ks i hv (by omega)⟩
    · exact ⟨by omega, hv⟩
    · exact ⟨by omega, hv⟩
    · exact ⟨by rw [ins_length]; exact hk, ins_valid ks (i - 1) hv (by omega)⟩

lemma cost_step (L A c : ℕ) (hcDehn : c ≤ (L + 1) * A + 4) :
    L * (L * A + 4) + c ≤ (L + 1) * ((L + 1) * A + 4) := by
  have h1 : L * A ≤ (L + 1) * A := Nat.mul_le_mul_right _ (by omega)
  have h2 : L * (L * A + 4) ≤ L * ((L + 1) * A + 4) := Nat.mul_le_mul_left _ (by omega)
  rw [Nat.succ_mul (L) ((L + 1) * A + 4)]
  omega

/-- **Coxeter insertion**: `nfDehn ks · σ_i = nfDehn (ins ks i)` at cost `j (jA + 4)`, `j = |ks|`. -/
theorem ins_areaEq {M A : ℕ} (hA : AstarLE M A) : ∀ (ks : List ℕ) (i : ℕ), Valid ks →
    i < ks.length → ks.length ≤ M + 1 →
    AreaEq (nfDehn ks * σ i) (nfDehn (ins ks i)) (ks.length * (ks.length * A + 4))
  | [], _, _, hi, _ => by simp at hi
  | k :: ks, i, ⟨hk, hv⟩, hi, hM => by
    simp only [List.length_cons] at hi hM ⊢
    unfold ins
    split_ifs with h1 h2 h3
    · -- far: move `σ_i` left across the top block
      have hm := move_left hA i k (ks.length + 1 - k) (by omega) (by omega)
        (fun t _ => Or.inl (by omega))
      have ih := ins_areaEq hA ks i hv (by omega) (by omega)
      have h := ((AreaEq.refl (nfDehn ks)).mul hm).trans
        (areaEq_congr (ih.mul (AreaEq.refl (Dn k (ks.length + 1 - k)))) (mul_assoc _ _ _) rfl le_rfl)
      refine areaEq_congr h ?_ ?_ ?_
      · simp [nfDehn, mul_assoc]
      · simp [nfDehn, ins_length]
      · have : (ks.length + 1 - k) * A ≤ (ks.length + 1) * A := Nat.mul_le_mul_right _ (by omega)
        have := cost_step ks.length A ((ks.length + 1 - k) * A) (by omega); omega
    · -- `c_k σ_{k-1} = c_{k-1}`
      refine (AreaEq.of_eq ?_).mono (Nat.zero_le _)
      obtain ⟨k, rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
      have e : ks.length + 1 - k = (ks.length + 1 - (k + 1)) + 1 := by omega
      obtain rfl : i = k := by omega
      simp only [nfDehn, Nat.add_sub_cancel]
      rw [e, Dn_succ_bot, mul_assoc]
    · -- `c_k σ_k = c_{k+1}` (one `r₁` cell)
      subst h3
      have e : ks.length + 1 - i = (ks.length + 1 - (i + 1)) + 1 := by omega
      have h := (AreaEq.refl (nfDehn ks * Dn (i + 1) (ks.length + 1 - (i + 1)))).mul (σ_sq i)
      refine areaEq_congr h ?_ ?_ ?_
      · simp only [nfDehn]; rw [e, Dn_succ_bot]; simp [mul_assoc]
      · simp [nfDehn]
      · have := cost_step ks.length A 1 (by omega); omega
    · -- braid case: `c_k σ_{i+1} = σ_i c_k`
      obtain ⟨i, rfl⟩ : ∃ i', i = i' + 1 := ⟨i - 1, by omega⟩
      have hsplit : Dn k (ks.length + 1 - k) =
          Dn (i + 2) (ks.length - (i + 1)) * (σ (i + 1) * (σ i * Dn k (i - k))) := by
        have e : ks.length + 1 - k = (ks.length - (i + 1)) + ((i - k) + 2) := by omega
        rw [e, Dn_split, show k + (i - k + 2) = i + 2 by omega]
        simp only [Dn, show k + (i - k + 1) = i + 1 by omega, show k + (i - k) = i by omega]
      have hY' := move_left hA (i + 1) k (i - k) (by omega) (by omega)
        (fun t _ => Or.inr (by omega))
      have hX' := move_left hA i (i + 2) (ks.length - (i + 1)) (by omega) (by omega)
        (fun t _ => Or.inl (by omega))
      have ih := ins_areaEq hA ks i hv (by omega) (by omega)
      have hb := braid i
      simp only [nfDehn, ins_length]
      rw [hsplit]
      have s1 := (AreaEq.refl (nfDehn ks * Dn (i + 2) (ks.length - (i + 1)) * σ (i + 1) * σ i)).mul hY'
      have s2 := ((AreaEq.refl (nfDehn ks * Dn (i + 2) (ks.length - (i + 1)))).mul hb).mul
        (AreaEq.refl (Dn k (i - k)))
      have s3 := ((AreaEq.refl (nfDehn ks)).mul hX').mul (AreaEq.refl (σ (i + 1) * σ i * Dn k (i - k)))
      have s4 := ih.mul (AreaEq.refl (Dn (i + 2) (ks.length - (i + 1)) * (σ (i + 1) * σ i * Dn k (i - k))))
      have h := ((s1.trans (areaEq_congr s2 (by simp only [mul_assoc]) rfl le_rfl)).trans
        (areaEq_congr s3 (by simp only [mul_assoc]) rfl le_rfl)).trans
        (areaEq_congr s4 (by simp only [mul_assoc]) rfl le_rfl)
      refine areaEq_congr h (by simp only [mul_assoc]) (by simp only [mul_assoc, Nat.add_sub_cancel]) ?_
      have hc1 : (i - k) * A + (ks.length - (i + 1)) * A ≤ (ks.length + 1) * A := by
        rw [← Nat.add_mul]; exact Nat.mul_le_mul_right _ (by omega)
      have := cost_step ks.length A ((i - k) * A + 4 + (ks.length - (i + 1)) * A) (by omega)
      omega
/-! ### Semantics: a trivial normal form is empty -/

lemma rho_mul_apply (x y : F) (p : Y) : (ρH (x * y)).unop p = (ρH y).unop ((ρH x).unop p) := by
  simp [map_mul]

lemma rho_σ_apply (j p : ℕ) : (ρH (σ j)).unop ((0 : Fin 3), p) =
    if p = j then ((0 : Fin 3), j + 1) else if p = j + 1 then ((0 : Fin 3), j) else ((0 : Fin 3), p) := by
  rw [rho_σ_unop]
  by_cases h1 : p = j
  · subst h1; simp
  · by_cases h2 : p = j + 1
    · subst h2; simp
    · rw [Equiv.swap_apply_of_ne_of_ne] <;> simp [h1, h2]

lemma Dn_fix (k : ℕ) : ∀ len p, k + len < p → (ρH (Dn k len)).unop ((0 : Fin 3), p) = (0, p)
  | 0, p, _ => by simp [Dn]
  | len + 1, p, h => by
    rw [Dn, rho_mul_apply, rho_σ_apply, if_neg (show ¬ _ by omega), if_neg (show ¬ _ by omega)]
    exact Dn_fix k len p (by omega)

lemma Dn_top (k : ℕ) : ∀ len, (ρH (Dn k len)).unop ((0 : Fin 3), k + len) = (0, k)
  | 0 => by simp [Dn]
  | len + 1 => by
    rw [Dn, rho_mul_apply, rho_σ_apply, if_neg (show ¬ _ by omega), if_pos (show _ by omega)]
    exact Dn_top k len

lemma nf_fix : ∀ ks : List ℕ, Valid ks → ∀ p, ks.length < p →
    (ρH (nfDehn ks)).unop ((0 : Fin 3), p) = (0, p)
  | [], _, p, _ => by simp [nfDehn]
  | k :: ks, ⟨hk, hv⟩, p, hp => by
    simp only [List.length_cons] at hp
    rw [nfDehn, rho_mul_apply, nf_fix ks hv p (by omega), Dn_fix k _ p (by omega)]

lemma nf_eq_one : ∀ ks : List ℕ, Valid ks → ρH (nfDehn ks) = 1 → nfDehn ks = 1
  | [], _, _ => rfl
  | k :: ks, ⟨hk, hv⟩, h => by
    have hpt := congrArg (fun g : (Equiv.Perm Y)ᵐᵒᵖ => g.unop ((0 : Fin 3), ks.length + 1)) h
    rw [nfDehn, rho_mul_apply, nf_fix ks hv _ (by omega)] at hpt
    have hD := Dn_top k (ks.length + 1 - k)
    rw [show k + (ks.length + 1 - k) = ks.length + 1 by omega] at hD
    rw [hD] at hpt
    simp only [MulOpposite.unop_one, Equiv.Perm.coe_one, id, Prod.mk.injEq, true_and] at hpt
    have hk' : ks.length + 1 - k = 0 := by omega
    have hD : Dn k (ks.length + 1 - k) = 1 := by rw [hk']; rfl
    have h' : ρH (nfDehn ks) = 1 := by rw [nfDehn, hD, mul_one] at h; exact h
    rw [nfDehn, hD, mul_one, nf_eq_one ks hv h']

/-- The identity normal form at level `j`. -/
def idd : ℕ → List ℕ
  | 0 => []
  | j + 1 => (j + 1) :: idd j

lemma idd_length : ∀ j, (idd j).length = j
  | 0 => rfl
  | j + 1 => by simp [idd, idd_length j]

lemma idd_valid : ∀ j, Valid (idd j)
  | 0 => trivial
  | j + 1 => ⟨by simp [idd_length], idd_valid j⟩

lemma nf_idd : ∀ j, nfDehn (idd j) = 1
  | 0 => rfl
  | j + 1 => by simp [idd, nfDehn, idd_length, nf_idd j, Dn]

/-! ### Filling a positive word -/

lemma fold_ins_valid : ∀ (P ks : List ℕ), Valid ks → (∀ i ∈ P, i < ks.length) →
    Valid (P.foldl ins ks)
  | [], _, hv, _ => hv
  | i :: P, ks, hv, hP => by
    rw [List.foldl_cons]
    exact fold_ins_valid P _ (ins_valid ks i hv (hP i (by simp)))
      (fun j hj => by rw [ins_length]; exact hP j (by simp [hj]))

theorem fill_pos {M A : ℕ} (hA : AstarLE M A) (d : ℕ) (hd : d ≤ M + 1) :
    ∀ (P : List ℕ) (ks : List ℕ), Valid ks → ks.length = d → (∀ i ∈ P, i < d) →
      AreaEq (nfDehn ks * (P.map σ).prod) (nfDehn (P.foldl ins ks)) (P.length * (d * (d * A + 4)))
  | [], ks, _, _, _ => by simpa using AreaEq.refl (nfDehn ks)
  | i :: P, ks, hv, hl, hP => by
    have h1 := ins_areaEq hA ks i hv (by rw [hl]; exact hP i (by simp)) (by omega)
    have h2 := fill_pos hA d hd P (ins ks i) (ins_valid ks i hv (by rw [hl]; exact hP i (by simp)))
      (by rw [ins_length, hl]) (fun j hj => hP j (by simp [hj]))
    have h := (h1.mul (AreaEq.refl (P.map σ).prod)).trans h2
    rw [hl] at h
    refine areaEq_congr h (by simp [mul_assoc]) rfl ?_
    simp only [List.length_cons, Nat.succ_mul]; omega

/-- `σ_j^{±1} = σ_j` (one `r₁` cell). -/
lemma σl_pos (x : ℕ × Bool) : AreaEq (σl x) (σ x.1) 1 := by
  rcases x with ⟨j, _ | _⟩
  · exact (AreaLE.inv (σ_sq j)).of_eq (by simp [σl, mul_inv_rev])
  · exact (AreaEq.refl _).mono (Nat.zero_le _)

lemma σw_pos : ∀ V : SW, AreaEq (σw V) ((V.map fun x => σ x.1).prod) V.length
  | [] => AreaEq.refl _
  | x :: V => by
    have h := (σl_pos x).mul (σw_pos V)
    refine areaEq_congr h (by simp [σw]) (by simp) (by simp; omega)

/-- **Coxeter filling** (`CoxeterFill`): with `A ≥ A*(B)`, every null word in `σ_0, …, σ_B`
has area at most `1 + (B+1)((B+1)A + 4)` per letter. -/
theorem coxeterFill {B A : ℕ} (hA : AstarLE B A) :
    CoxeterFill B (1 + (B + 1) * ((B + 1) * A + 4)) := by
  intro V hV h1
  set P := V.map (·.1) with hP
  have hpos := σw_pos V
  have hPσ : (V.map fun x => σ x.1) = P.map σ := by simp [hP, Function.comp_def]
  rw [hPσ] at hpos
  have hfill := fill_pos hA (B + 1) le_rfl P (idd (B + 1)) (idd_valid _) (idd_length _)
    (fun i hi => by
      simp only [hP, List.mem_map] at hi
      obtain ⟨x, hx, rfl⟩ := hi
      have := hV x hx; omega)
  rw [nf_idd, one_mul] at hfill
  have hnull : ρH (P.map σ).prod = 1 := by rw [← rho_eq_of_areaEq hpos, h1]
  have hfin : nfDehn (P.foldl ins (idd (B + 1))) = 1 := by
    apply nf_eq_one
    · exact fold_ins_valid P _ (idd_valid _) (fun i hi => by
        rw [idd_length]; simp only [hP, List.mem_map] at hi
        obtain ⟨x, hx, rfl⟩ := hi; have := hV x hx; omega)
    · rw [← rho_eq_of_areaEq hfill, hnull]
  rw [hfin] at hfill
  have h := hpos.trans hfill
  refine (AreaLE.of_eq h (by simp)).mono ?_
  simp only [hP, List.length_map, Nat.mul_add, Nat.mul_one]
  omega

end Houghton
