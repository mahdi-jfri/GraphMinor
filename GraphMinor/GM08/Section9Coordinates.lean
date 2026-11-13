module

public import GraphMinor.Surface.SphereDisc

/-!
# Plane coordinates for a ring with a fixed exterior point

For the finite-crossing replacement in the foundation step of VIII (9.1),
we put the old ring on the unit circle. A chosen point outside the ambient
disc goes to infinity, so the drawing stays in the plane. This is the
Schoenflies construction of `Surface.exists_homeomorph_model`, with the
point sent to infinity retained as part of the conclusion.
-/

public section

namespace GraphMinor.GM08

open Set Surface Topology OnePoint Metric

universe u

/-- Send a ring on a sphere to the unit circle while sending a prescribed
point off the ring to infinity. This fixes which side is the bounded side
when rings are approximated in the proof of VIII (9.1). -/
theorem exists_homeomorph_ring_model_at {S : Type u} [TopologicalSpace S]
    (hS : IsSphere S) {F : Set S} (hF : IsOArc F) {x : S} (hx : x ∉ F) :
    ∃ T : S ≃ₜ OnePoint EuclideanPlane,
      T '' F = sph '' sphere (0 : ℂ) 1 ∧ T x = ∞ := by
  obtain ⟨e⟩ := hS
  obtain ⟨φ⟩ := id hF
  obtain ⟨h, hh⟩ := exists_homeomorph_onePoint (e x)
  let E : S ≃ₜ OnePoint EuclideanPlane := e.trans h
  have hxE : E x = ∞ := hh
  have hinf : (∞ : OnePoint EuclideanPlane) ∉ E '' F := by
    rintro ⟨y, hy, hyE⟩
    have hyx : y = x := E.injective (hyE.trans hxE.symm)
    exact hx (hyx ▸ hy)
  have hsub : E '' F ⊆ range sph := fun p hp => by
    rcases eq_infty_or_sph p with rfl | ⟨z, rfl⟩
    · exact absurd hp hinf
    · exact ⟨z, rfl⟩
  have himg : sph '' (sph ⁻¹' (E '' F)) = E '' F := image_preimage_eq_of_subset hsub
  have hG : IsOArc (sph ⁻¹' (E '' F)) := by
    have h1 := isOpenEmbedding_sph.isEmbedding.homeomorphImage (sph ⁻¹' (E '' F))
    have h2 : (E '' F : Set _) ≃ₜ (sph '' (sph ⁻¹' (E '' F)) : Set _) :=
      Homeomorph.setCongr himg.symm
    exact ⟨(φ.trans (E.image F)).trans (h2.trans h1.symm)⟩
  obtain ⟨φ₀⟩ := oArc_sphere
  obtain ⟨φ'⟩ := id hG
  obtain ⟨h₀, k₀, m, _⟩ := exists_bdMatch (φ₀.symm.trans φ')
  obtain ⟨G, hGe⟩ := exists_homeomorph_of_bdMatch hG m
  let g : EuclideanPlane ≃ₜ EuclideanPlane :=
    complexPlane.symm.toHomeomorph.trans (G.trans complexPlane.toHomeomorph)
  let C : OnePoint EuclideanPlane ≃ₜ OnePoint EuclideanPlane := g.onePointCongr
  have hC : ∀ z, C (sph z) = sph (G z) := fun z => by
    show ((g (complexPlane z) : EuclideanPlane) : OnePoint EuclideanPlane) = sph (G z)
    simp [g, sph]
  refine ⟨E.trans C.symm, ?_, ?_⟩
  · have h3 : C '' (sph '' sphere (0 : ℂ) 1) = E '' F := by
      rw [image_image]
      simp only [hC]
      rw [← image_image (g := sph) (f := G), hGe.image_eq, m.image_eq, himg]
    have h4 : (E.trans C.symm) '' F = C.symm '' (E '' F) := by
      rw [image_image]
      rfl
    rw [h4, ← h3, image_image]
    simp
  · change C.symm (E x) = ∞
    rw [hxE]
    rfl

/-- In ring coordinates, a chosen point of the ring can also be sent to `1`.
Choosing this point off the other ring gives the free gap required by the
round finite-crossing replacement in the foundation step of VIII (9.1). -/
theorem exists_homeomorph_ring_model_at_points {S : Type u} [TopologicalSpace S]
    (hS : IsSphere S) {F : Set S} (hF : IsOArc F) {x y : S} (hx : x ∉ F) (hy : y ∈ F) :
    ∃ T : S ≃ₜ OnePoint EuclideanPlane,
      T '' F = sph '' sphere (0 : ℂ) 1 ∧ T x = ∞ ∧ T y = sph 1 := by
  obtain ⟨T, hTF, hTx⟩ := exists_homeomorph_ring_model_at hS hF hx
  obtain ⟨z, hz, hTy⟩ : T y ∈ sph '' sphere (0 : ℂ) 1 := hTF ▸ mem_image_of_mem T hy
  have hzNorm : ‖z‖ = 1 := mem_sphere_zero_iff_norm.mp hz
  have hz0 : z ≠ 0 := norm_ne_zero_iff.mp (hzNorm ▸ one_ne_zero)
  let R : ℂ ≃ₜ ℂ := Homeomorph.mulLeft₀ z⁻¹ (inv_ne_zero hz0)
  have hRnorm : ∀ w, ‖R w‖ = ‖w‖ := by
    intro w
    simp only [R, Homeomorph.coe_mulLeft₀, norm_mul, norm_inv, hzNorm, inv_one, one_mul]
  have hRsphere : R '' sphere (0 : ℂ) 1 = sphere (0 : ℂ) 1 := by
    apply subset_antisymm
    · rintro _ ⟨w, hw, rfl⟩
      exact mem_sphere_zero_iff_norm.mpr ((hRnorm w).trans (mem_sphere_zero_iff_norm.mp hw))
    · intro w hw
      refine ⟨R.symm w, ?_, R.apply_symm_apply w⟩
      apply mem_sphere_zero_iff_norm.mpr
      have hn := hRnorm (R.symm w)
      rw [R.apply_symm_apply] at hn
      exact hn.symm.trans (mem_sphere_zero_iff_norm.mp hw)
  let g : EuclideanPlane ≃ₜ EuclideanPlane :=
    complexPlane.symm.toHomeomorph.trans (R.trans complexPlane.toHomeomorph)
  let C : OnePoint EuclideanPlane ≃ₜ OnePoint EuclideanPlane := g.onePointCongr
  have hC : ∀ w, C (sph w) = sph (R w) := by
    intro w
    simp [C, g, sph]
  refine ⟨T.trans C, ?_, ?_, ?_⟩
  · calc
      (T.trans C) '' F = C '' (T '' F) := by rw [image_image]; rfl
      _ = C '' (sph '' sphere (0 : ℂ) 1) := by rw [hTF]
      _ = sph '' (R '' sphere (0 : ℂ) 1) := by
        rw [image_image, image_image]
        apply image_congr
        intro w _
        exact hC w
      _ = sph '' sphere (0 : ℂ) 1 := by rw [hRsphere]
  · change C (T x) = ∞
    rw [hTx]
    rfl
  · change C (T y) = sph 1
    rw [← hTy, hC]
    congr 1
    exact inv_mul_cancel₀ hz0

/-- Plane coordinates for a ring as an open embedding into the sphere.
The complement of its range is the chosen exterior point. A chosen point
of the ring is the image of `1`, so a gap there becomes a gap at `1` in the plane. -/
theorem exists_plane_embedding_for_ring {S : Type u} [TopologicalSpace S]
    (hS : IsSphere S) {F : Set S} (hF : IsOArc F) {x y : S} (hx : x ∉ F) (hy : y ∈ F) :
    ∃ g : ℂ → S, IsOpenEmbedding g ∧ g '' sphere (0 : ℂ) 1 = F ∧
      g 1 = y ∧ range g = ({x} : Set S)ᶜ := by
  obtain ⟨T, hTF, hTx, hTy⟩ := exists_homeomorph_ring_model_at_points hS hF hx hy
  let g : ℂ → S := fun z => T.symm (sph z)
  have hg : IsOpenEmbedding g := T.symm.isOpenEmbedding.comp isOpenEmbedding_sph
  refine ⟨g, hg, ?_, ?_, ?_⟩
  · calc
      g '' sphere (0 : ℂ) 1 = T.symm '' (sph '' sphere (0 : ℂ) 1) := by
        rw [image_image]
      _ = T.symm '' (T '' F) := by rw [hTF]
      _ = F := by rw [image_image]; simp
  · apply T.injective
    change T (T.symm (sph 1)) = T y
    rw [T.apply_symm_apply, hTy]
  · apply subset_antisymm
    · rintro _ ⟨z, rfl⟩ hxg
      have heq : T.symm (sph z) = x := hxg
      have heq' := congrArg T heq
      rw [T.apply_symm_apply, hTx] at heq'
      exact sph_ne_infty z heq'
    · intro z hz
      rcases eq_infty_or_sph (T z) with h | ⟨w, hw⟩
      · exact False.elim (hz (T.injective (h.trans hTx.symm)))
      · exact ⟨w, by dsimp only [g]; rw [← hw, T.symm_apply_apply]⟩

/-- Two closed discs on a sphere with the same boundary coincide if both
miss the same point. This identifies the bounded side in ring coordinates. -/
theorem closed_discs_eq_of_boundary_and_missing_point {S : Type u} [TopologicalSpace S]
    (hS : IsSphere S) {A B F : Set S} (hA : IsClosedDisc A) (hB : IsClosedDisc B)
    (hAb : discBd A = F) (hBb : discBd B = F) {x : S} (hxA : x ∉ A) (hxB : x ∉ B) :
    A = B := by
  have hF : IsOArc F := hAb ▸ hA.isOArc_discBd
  obtain ⟨K, L, _, hK, hL, hKb, hLb, hKL, _, _, huniq⟩ := sphere_disc S hS F hF
  rcases huniq A hA hAb with hAK | hAL
  · rcases huniq B hB hBb with hBK | hBL
    · exact hAK.trans hBK.symm
    · have hx : x ∈ K ∪ L := hKL.symm ▸ mem_univ x
      exact False.elim (hx.elim (fun h => hxA (hAK.symm ▸ h))
        (fun h => hxB (hBL.symm ▸ h)))
  · rcases huniq B hB hBb with hBK | hBL
    · have hx : x ∈ K ∪ L := hKL.symm ▸ mem_univ x
      exact False.elim (hx.elim (fun h => hxB (hBK.symm ▸ h))
        (fun h => hxA (hAL.symm ▸ h)))
    · exact hAL.trans hBL.symm

end GraphMinor.GM08
