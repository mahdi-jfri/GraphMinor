module

public import GraphMinor.GM08.Section15Tube
import GraphMinor.GM08.Section15Menger

/-!
# A tube drawing is proper

The part between two framing hoops meets the ambient cylinder boundary
only on those hoops. The normality of both hoops therefore makes the
drawing proper in the ambient cylinder. This allows the arc pullback
construction in the short-tube proof of VIII (15.4).
-/

public section

namespace GraphMinor.GM08

open Set GraphMinor.Surface

universe w

/-- The region between laminar hoops meets the cylinder boundary only
on the hoops. This supplies properness for the cut in VIII (15.4),
page 282. -/
theorem cylinderBetween_inter_bd_subset {S : Type w} [TopologicalSpace S]
    {F₁ F₂ : Set S} (hlam : AreLaminarHoops F₁ F₂) :
    cylinderBetween F₁ F₂ ∩ bd S ⊆ F₁ ∪ F₂ := by
  obtain ⟨hS, hF₁, hF₂, _⟩ := id hlam
  obtain ⟨cap, hle⟩ := CylinderSphereCap.exists_oriented hS hF₁ hF₂ hlam
  obtain ⟨_, _, _, _, _, hcap₁, hD₁, _⟩ := cap.disc₁_disc₂_spec hS.1 hF₁
  obtain ⟨_, _, _, _, _, hcap₂, _, hD₂⟩ := cap.disc₁_disc₂_spec hS.1 hF₂
  intro x hx
  rw [cap.cylinderBetween_eq_of_disc₁_subset hS hF₁ hF₂ hle] at hx
  rw [cap.bd_eq] at hx
  rcases hx.2 with hC₁ | hC₂
  · have hjD : cap.j x ∈ cap.D₁ :=
      Surface.discBd_subset _ (cap.discBd_D₁ ▸ mem_image_of_mem cap.j hC₁)
    have hjF : cap.j x ∈ cap.j '' F₁ := hcap₁ ▸ ⟨hD₁ hjD, hx.1.2⟩
    obtain ⟨y, hy, heq⟩ := hjF
    exact .inl (cap.inj heq ▸ hy)
  · have hjD : cap.j x ∈ cap.D₂ :=
      Surface.discBd_subset _ (cap.discBd_D₂ ▸ mem_image_of_mem cap.j hC₂)
    have hjF : cap.j x ∈ cap.j '' F₂ := hcap₂ ▸ ⟨hx.1.1, hD₂ hjD⟩
    obtain ⟨y, hy, heq⟩ := hjF
    exact .inr (cap.inj heq ▸ hy)

/-- Every tube drawing is proper in its ambient cylinder. The normality
of the framing hoops covers all its boundary contacts, as used in
VIII (15.4), page 282. -/
theorem Tube.isProper {S : Type w} [TopologicalSpace S] (τ : Tube S) :
    τ.Γ.IsProper := by
  intro x hx
  rcases cylinderBetween_inter_bd_subset τ.laminar ⟨τ.U_subset hx.2, hx.1⟩ with h | h
  · exact τ.isNormal_F₁ ⟨h, hx.2⟩
  · exact τ.isNormal_F₂ ⟨h, hx.2⟩

end GraphMinor.GM08
