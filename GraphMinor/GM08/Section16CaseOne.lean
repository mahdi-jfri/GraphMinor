module

public import GraphMinor.GM08.Section16Defs
import GraphMinor.GM08.Section16Step

/-!
# The equal boundary sizes case of Graph Minors VIII (16.2)

If both boundary hoops have the minimum possible number of vertices, Menger's
theorem joins them to any pair of inner hoops. Thus a framing which is not
boundary-linked has no inner tube of the required width and length.
-/

public section

namespace GraphMinor.GM08

open Set GraphMinor.Surface GraphMinor.GM11

universe w

private theorem subTube_swap {S : Type w} [TopologicalSpace S] (τ : Tube S)
    {H₁ H₂ : Set S} (hlam : AreLaminarHoops H₁ H₂)
    (hN₁ : τ.Γ.IsNormal H₁) (hN₂ : τ.Γ.IsNormal H₂) :
    τ.subTube hlam.symm hN₂ hN₁ = (τ.subTube hlam hN₁ hN₂).symm := by
  have : T2Space S := τ.t2Space
  apply Tube.ext
  · change τ.Γ.interSet (cylinderBetween H₂ H₁) =
      τ.Γ.interSet (cylinderBetween H₁ H₂)
    rw [cylinderBetween_comm]
  · rfl
  · rfl

private theorem boundaryLinked_of_ordered_hoops {S : Type w} [TopologicalSpace S]
    (τ : Tube S) {r s m : ℕ}
    (h₁ : (τ.Γ.V ∩ τ.F₁).ncard = m) (h₂ : (τ.Γ.V ∩ τ.F₂).ncard = m)
    (hmin : ∀ H : Set S, IsHoop H → τ.Γ.IsNormal H →
      H ⊆ cylinderBetween τ.F₁ τ.F₂ → m ≤ (τ.Γ.V ∩ H).ncard)
    {H₁ H₂ : Set S} (hlam : AreLaminarHoops H₁ H₂)
    (hsub₁ : H₁ ⊆ cylinderBetween τ.F₁ τ.F₂)
    (hsub₂ : H₂ ⊆ cylinderBetween τ.F₁ τ.F₂)
    (hN₁ : τ.Γ.IsNormal H₁) (hN₂ : τ.Γ.IsNormal H₂)
    (horder₁ : H₂ ⊆ cylinderBetween τ.F₁ H₁)
    (horder₂ : H₁ ⊆ cylinderBetween τ.F₂ H₂)
    (hw : (r : ℕ∞) ≤ (τ.subTube hlam hN₁ hN₂).width)
    (hl : s ≤ (τ.subTube hlam hN₁ hN₂).length) : τ.IsBoundaryLinked r s := by
  have hleft := (areLaminarHoops_of_subset_cylinderBetween τ.laminar hlam.2.1 hsub₁).1
  have hright := (areLaminarHoops_of_subset_cylinderBetween τ.laminar hlam.2.2.1 hsub₂).2.symm
  refine ⟨H₁, H₂, hlam, hsub₁, hsub₂, hN₁, hN₂, horder₁, horder₂, hw, hl, ?_, ?_⟩
  · rw [h₁]
    apply τ.hasDisjointPaths_skeleton_of_forall_hoop_ncard_ge hleft τ.isNormal_F₁ hN₁
    intro H hH hNH hsub
    exact hmin H hH hNH (hsub.trans (cylinderBetween_subset_cylinderBetween τ.laminar
      hleft (subset_cylinderBetween_left τ.laminar) hsub₁))
  · rw [h₂]
    apply τ.hasDisjointPaths_skeleton_of_forall_hoop_ncard_ge hright τ.isNormal_F₂ hN₂
    intro H hH hNH hsub
    exact hmin H hH hNH (hsub.trans (cylinderBetween_subset_cylinderBetween τ.laminar
      hright (subset_cylinderBetween_right τ.laminar) hsub₂))

/-- Case 1 of Graph Minors VIII (16.2), page 283. If the two boundary hoops
attain the minimum vertex count, a framing which is not boundary-linked has no
inner tube of width at least `r` and length at least `s`. -/
theorem Tube.hasNoSubTubeOf_of_minimum_boundaries {S : Type w} [TopologicalSpace S]
    (τ : Tube S) {r s m : ℕ}
    (h₁ : (τ.Γ.V ∩ τ.F₁).ncard = m) (h₂ : (τ.Γ.V ∩ τ.F₂).ncard = m)
    (hmin : ∀ H : Set S, IsHoop H → τ.Γ.IsNormal H →
      H ⊆ cylinderBetween τ.F₁ τ.F₂ → m ≤ (τ.Γ.V ∩ H).ncard)
    (hnot : ¬ τ.IsBoundaryLinked r s) : τ.HasNoSubTubeOf r s := by
  rintro ⟨H₁, H₂, hlam, hsub₁, hsub₂, hN₁, hN₂, hw, hl⟩
  obtain ⟨cap, hle⟩ := CylinderSphereCap.exists_oriented τ.isCylinder
    τ.isHoop_F₁ τ.isHoop_F₂ τ.laminar
  have ha := (cap.hoop_subset_cylinderBetween_iff τ.isCylinder
    τ.isHoop_F₁ τ.isHoop_F₂ hlam.2.1 hle).mp hsub₁
  have hb := (cap.hoop_subset_cylinderBetween_iff τ.isCylinder
    τ.isHoop_F₁ τ.isHoop_F₂ hlam.2.2.1 hle).mp hsub₂
  rcases (cap.areLaminarHoops_iff τ.isCylinder hlam.2.1 hlam.2.2.1).mp hlam with hab | hba
  · have ho₁ : H₁ ⊆ cylinderBetween τ.F₁ H₂ :=
      (cap.hoop_subset_cylinderBetween_iff τ.isCylinder τ.isHoop_F₁
        hlam.2.2.1 hlam.2.1 hb.1).mpr ⟨ha.1, hab⟩
    have ho₂ : H₂ ⊆ cylinderBetween τ.F₂ H₁ := by
      rw [cylinderBetween_comm]
      exact (cap.hoop_subset_cylinderBetween_iff τ.isCylinder hlam.2.1
        τ.isHoop_F₂ hlam.2.2.1 ha.2).mpr ⟨hab, hb.2⟩
    have hw' : (r : ℕ∞) ≤ (τ.subTube hlam.symm hN₂ hN₁).width := by
      rw [subTube_swap, Tube.width_symm]
      exact hw
    have hl' : s ≤ (τ.subTube hlam.symm hN₂ hN₁).length := by
      rw [subTube_swap, Tube.length_symm]
      exact hl
    exact hnot (boundaryLinked_of_ordered_hoops τ h₁ h₂ hmin hlam.symm
      hsub₂ hsub₁ hN₂ hN₁ ho₁ ho₂ hw' hl')
  · have ho₁ : H₂ ⊆ cylinderBetween τ.F₁ H₁ :=
      (cap.hoop_subset_cylinderBetween_iff τ.isCylinder τ.isHoop_F₁
        hlam.2.1 hlam.2.2.1 ha.1).mpr ⟨hb.1, hba⟩
    have ho₂ : H₁ ⊆ cylinderBetween τ.F₂ H₂ := by
      rw [cylinderBetween_comm]
      exact (cap.hoop_subset_cylinderBetween_iff τ.isCylinder hlam.2.2.1
        τ.isHoop_F₂ hlam.2.1 hb.2).mpr ⟨hba, ha.2⟩
    exact hnot (boundaryLinked_of_ordered_hoops τ h₁ h₂ hmin hlam
      hsub₁ hsub₂ hN₁ hN₂ ho₁ ho₂ hw hl)

end GraphMinor.GM08
