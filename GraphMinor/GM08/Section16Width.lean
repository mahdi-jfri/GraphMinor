module

public import GraphMinor.GM08.Section15Tube
import GraphMinor.GM08.Section15

/-!
# Width after moving a boundary hoop

Moving the first hoop inside a tube and restricting the drawing does not
lower its width. This supplies the width assertion after the inward hoop
step in Case 2 of Graph Minors VIII (16.2), page 283.
-/

public section

namespace GraphMinor.GM08

open Set GraphMinor.Surface GraphMinor.GM11

universe w

private theorem cylinderBetween_overlap {S : Type w} [TopologicalSpace S]
    (cap : CylinderSphereCap S) (hS : IsCylinder S)
    {A B C D : Set S} (hA : IsHoop A) (hB : IsHoop B) (hC : IsHoop C) (hD : IsHoop D)
    (hAB : cap.disc₁ hS.1 hA ⊆ cap.disc₁ hS.1 hB)
    (hBC : cap.disc₁ hS.1 hB ⊆ cap.disc₁ hS.1 hC)
    (hCD : cap.disc₁ hS.1 hC ⊆ cap.disc₁ hS.1 hD) :
    cylinderBetween A C ∩ cylinderBetween B D = cylinderBetween B C := by
  rw [cap.cylinderBetween_eq_of_disc₁_subset hS hA hC (hAB.trans hBC),
    cap.cylinderBetween_eq_of_disc₁_subset hS hB hD (hBC.trans hCD),
    cap.cylinderBetween_eq_of_disc₁_subset hS hB hC hBC]
  have hBA := (cap.disc₂_subset_iff_disc₁_subset hS.1 hA hB).mpr hAB
  ext x
  exact ⟨fun ⟨⟨hxC, _⟩, ⟨_, hxB⟩⟩ => ⟨hxC, hxB⟩,
    fun ⟨hxC, hxB⟩ => ⟨⟨hxC, hBA hxB⟩, ⟨hCD hxC, hxB⟩⟩⟩

/-- The width does not decrease when the first boundary moves inward and the
drawing is restricted, as used in Case 2 of VIII (16.2), page 283. -/
theorem Tube.width_le_subTube_right {S : Type w} [TopologicalSpace S]
    (τ : Tube S) {K : Set S} (hK : IsHoop K) (hNK : τ.Γ.IsNormal K)
    (hKsub : K ⊆ cylinderBetween τ.F₁ τ.F₂) :
    τ.width ≤ (τ.subTube
      (areLaminarHoops_of_subset_cylinderBetween τ.laminar hK hKsub).2 hNK τ.isNormal_F₂).width := by
  have : T2Space S := τ.t2Space
  let hlam := (areLaminarHoops_of_subset_cylinderBetween τ.laminar hK hKsub).2
  let σ := τ.subTube hlam hNK τ.isNormal_F₂
  obtain ⟨cap, hle⟩ := CylinderSphereCap.exists_oriented τ.isCylinder
    τ.isHoop_F₁ τ.isHoop_F₂ τ.laminar
  have hKpos := (cap.hoop_subset_cylinderBetween_iff τ.isCylinder
    τ.isHoop_F₁ τ.isHoop_F₂ hK hle).mp hKsub
  have hV : σ.Γ.V = τ.Γ.V ∩ cylinderBetween K τ.F₂ :=
    interSet_V_of_isClosed τ.Γ (isClosed_cylinderBetween hlam)
  have hU : σ.Γ.U = τ.Γ.U ∩ cylinderBetween K τ.F₂ :=
    interSet_U_eq_of_laminar_normal τ.Γ hlam hNK τ.isNormal_F₂
  apply (σ.le_width_iff).mpr
  intro H hH hNH hHsub
  have hHpos := (cap.hoop_subset_cylinderBetween_iff τ.isCylinder
    hK τ.isHoop_F₂ hH hKpos.2).mp hHsub
  have hNH' : τ.Γ.IsNormal H :=
    (τ.subTube_isNormal_iff hlam hNK τ.isNormal_F₂ hHsub).mp hNH
  have hHsub' : H ⊆ cylinderBetween τ.F₁ τ.F₂ := hHsub.trans
    (cylinderBetween_subset_cylinderBetween τ.laminar hlam hKsub
      (subset_cylinderBetween_right τ.laminar))
  have hHV : H ∩ σ.Γ.V = H ∩ τ.Γ.V := by
    rw [hV]
    ext x
    exact ⟨fun ⟨hxH, hxV, _⟩ => ⟨hxH, hxV⟩,
      fun ⟨hxH, hxV⟩ => ⟨hxH, hxV, hHsub hxH⟩⟩
  rcases (τ.le_width_iff.mp le_rfl) H hH hNH' hHsub' with htriv | hcard
  · left
    rcases htriv with ⟨hcut, heq⟩ | ⟨hcut, heq⟩
    · refine Or.inl ⟨?_, ?_⟩
      · intro x hx
        exact hcut (hU.subset hx).1
      · change H ∩ σ.Γ.V = K ∩ σ.Γ.V
        ext x
        constructor
        · rintro ⟨hxH, hxV⟩
          have hxV' := (hV.subset hxV).1
          have hxF₁ := (heq.subset ⟨hxH, hxV'⟩).1
          have h₁K : AreLaminarHoops τ.F₁ K :=
            (areLaminarHoops_of_subset_cylinderBetween τ.laminar hK hKsub).1
          have hKH : AreLaminarHoops K H :=
            (cap.areLaminarHoops_iff τ.isCylinder hK hH).mpr (Or.inl hHpos.1)
          have hxK : x ∈ K := by
            rw [← cap.cylinderBetween_inter τ.isCylinder τ.isHoop_F₁ hK hH hKpos.1 hHpos.1]
            exact ⟨subset_cylinderBetween_left h₁K hxF₁,
              subset_cylinderBetween_right hKH hxH⟩
          exact ⟨hxK, hxV⟩
        · rintro ⟨hxK, hxV⟩
          have hxV' := (hV.subset hxV).1
          have hKsubH : K ⊆ cylinderBetween τ.F₁ H :=
            (cap.hoop_subset_cylinderBetween_iff τ.isCylinder τ.isHoop_F₁ hH hK
              (hKpos.1.trans hHpos.1)).mpr ⟨hKpos.1, hHpos.1⟩
          have hxH : x ∈ H := by
            rw [← cap.cylinderBetween_inter τ.isCylinder τ.isHoop_F₁ hH τ.isHoop_F₂
              (hKpos.1.trans hHpos.1) hHpos.2]
            exact ⟨hKsubH hxK, hcut (τ.Γ.V_subset_U hxV')⟩
          exact ⟨hxH, hxV⟩
    · refine Or.inr ⟨?_, ?_⟩
      · intro x hx
        have hx' := hU.subset hx
        change x ∈ cylinderBetween K H
        rw [← cylinderBetween_overlap cap τ.isCylinder τ.isHoop_F₁ hK hH τ.isHoop_F₂
          hKpos.1 hHpos.1 hHpos.2]
        exact ⟨hcut hx'.1, hx'.2⟩
      · change H ∩ σ.Γ.V = τ.F₂ ∩ σ.Γ.V
        rw [hV]
        ext x
        exact ⟨fun ⟨hxH, hxV, hxC⟩ => ⟨(heq.subset ⟨hxH, hxV⟩).1, hxV, hxC⟩,
          fun ⟨hxF, hxV, hxC⟩ => ⟨(heq.symm.subset ⟨hxF, hxV⟩).1, hxV, hxC⟩⟩
  · right
    rwa [hHV]

end GraphMinor.GM08
