import Houghton.Main

/-!
# Images of `H₃` (the first step of Corollary `cor:cremona`)

For a homomorphism `h : H₃ → Γ` with `h(γ) ≠ 1`, the image chunk `h(E_H)` keeps every product
relation of `E_H` and separates `h(γ)` from `1`, which is all the lower bound uses. Hence its
profile is superpolynomial, and a homomorphism from `H₃` to a group all of whose chunks have
polynomially bounded profile kills `γ` (`kills_γ`). (The paper then concludes, by conjugation, that the
finitary alternating subgroup is killed, and treats `H_m`, `m ≥ 3`; that part is not formalized.)
-/

namespace Houghton

open Finset

variable {Γ : Type*} [Group Γ]

open Classical in
/-- The image chunk `h(E_H) ⊆ Γ`. -/
noncomputable def imageChunk (h : H3 →* Γ) : Finset Γ := E_H.image h

theorem mem_imageChunk {h : H3 →* Γ} {x : H3} (hx : x ∈ E_H) : h x ∈ imageChunk h := by
  classical
  unfold imageChunk
  exact mem_image.mpr ⟨x, hx, rfl⟩

theorem one_mem_imageChunk (h : H3 →* Γ) : (1 : Γ) ∈ imageChunk h := by
  have := mem_imageChunk (h := h) one_mem_E_H
  rwa [map_one] at this

/-- A model of the image chunk pulls back to an `r⁻¹`-morphism of `E_H` separating `γ` from `1`. -/
theorem goodSize_of_image {h : H3 →* Γ} (hγ : h (ρH' γ) ≠ 1) {r : ℝ} {n : ℕ}
    (hn : n ∈ modelSizes (imageChunk h) r) : GoodSize r n := by
  obtain ⟨hn0, f, ⟨hf1, hfm⟩, hfe⟩ := hn
  refine ⟨hn0, fun x => f (h x), ⟨by simp [hf1], fun x hx y hy hxy => ?_⟩, ?_⟩
  · have hxy' : h x * h y ∈ imageChunk h := by rw [← map_mul]; exact mem_imageChunk hxy
    have := hfm (h x) (mem_imageChunk hx) (h y) (mem_imageChunk hy) hxy'
    simpa [map_mul] using this
  · have := hfe (h (ρH' γ)) (mem_imageChunk rho'_γ_mem_E_H) 1 (one_mem_imageChunk h) hγ
    simpa using this

/-- The unweighted lower bound for the image chunk of any homomorphism not killing `γ`. -/
theorem image_lower_bound_unweighted (hdim : DimensionPermStatement) (harea : AreaStatement)
    {h : H3 →* Γ} (hγ : h (ρH' γ) ≠ 1) {r : ℝ} (hr : 2 ≤ r) {n : ℕ}
    (hn : n ∈ modelSizes (imageChunk h) r) :
    (2:ℝ) ^ (r ^ ((1:ℝ) / 12) / 270 - 1 / 16) ≤ n :=
  lower_bound_unweighted_of_good hdim harea hr (goodSize_of_image hγ hn)

/-- The weighted lower bound for the image chunk of any homomorphism not killing `γ`. -/
theorem image_lower_bound_weighted (hdim : DimensionPermStatement)
    (harea : WeightedAreaStatement) {h : H3 →* Γ} (hγ : h (ρH' γ) ≠ 1) {r : ℝ} (hr : 2 ≤ r)
    {n : ℕ} (hn : n ∈ modelSizes (imageChunk h) r) :
    (2:ℝ) ^ (r ^ (1 / (Real.logb 2 107 + 1)) / 1280 - 1 / 16) ≤ n :=
  lower_bound_weighted_of_good hdim harea hr (goodSize_of_image hγ hn)

/-- The image chunk has superpolynomial profile. -/
theorem image_not_polynomially_bounded (hdim : DimensionPermStatement) (harea : AreaStatement)
    {h : H3 →* Γ} (hγ : h (ρH' γ) ≠ 1) :
    ∀ k C R : ℝ, ∃ r : ℝ, R ≤ r ∧ 2 ≤ r ∧
      ∀ m : ℕ, profile (imageChunk h) r = m → C * r ^ k < m := by
  intro k C R
  obtain ⟨r, hR, hr, hlt⟩ := exists_two_rpow_gt (1 / 270) (1 / 16) (1 / 12) C k R
    (by norm_num) (by norm_num) (by norm_num)
  refine ⟨r, hR, hr, fun m hm => ?_⟩
  have := le_profile_of_forall (fun _ hn => image_lower_bound_unweighted hdim harea hγ hr hn) m hm
  have e : (1:ℝ) / 270 * r ^ ((1:ℝ) / 12) - 1 / 16 = r ^ ((1:ℝ) / 12) / 270 - 1 / 16 := by ring
  rw [e] at hlt
  linarith

/-- **Corollary `cor:cremona`, first step** (for `H₃`): if every chunk of `Γ` has profile bounded
by a polynomial for all large `r`, every homomorphism `H₃ → Γ` kills the three-cycle `γ`. -/
theorem kills_γ (hdim : DimensionPermStatement) (harea : AreaStatement) (h : H3 →* Γ)
    (hpoly : ∀ E : Finset Γ, (1 : Γ) ∈ E → ∃ k C R : ℝ, ∀ r : ℝ, R ≤ r →
      ∃ m : ℕ, profile E r = m ∧ (m : ℝ) ≤ C * r ^ k) :
    h (ρH' γ) = 1 := by
  by_contra hγ
  obtain ⟨k, C, R, hb⟩ := hpoly (imageChunk h) (one_mem_imageChunk h)
  obtain ⟨r, hR, -, hlt⟩ := image_not_polynomially_bounded hdim harea hγ k C R
  obtain ⟨m, hm, hle⟩ := hb r hR
  have := hlt m hm
  linarith

end Houghton
