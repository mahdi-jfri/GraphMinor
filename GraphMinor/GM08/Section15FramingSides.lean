module

public import GraphMinor.GM08.Section15Tube
import GraphMinor.GM08.Section15SeparateSides

/-!
# Disjoint empty discs carrying the framing roots

In the capped cylinder the two outer sides of a tube are closed discs.
They can touch where the framing hoops touch. Shrink the second side
while retaining its exclusive roots. The resulting discs are disjoint,
miss the drawing in their interiors, and their boundary union carries
exactly the original framing roots. Their complement is the cylinder
used to open the short tube in VIII (15.4).
-/

public section

namespace GraphMinor.GM08

open Set GraphMinor.Surface

universe w

/-- Separate the two outer discs of a capped framing while retaining
exactly its root set on their boundary union. This is the framing
adjustment in the short-tube proof of VIII (15.4), page 282. -/
theorem Tube.exists_separated_framing_sides {S : Type w} [TopologicalSpace S]
    (τ : Tube S) (cap : CylinderSphereCap S)
    (hle : cap.disc₁ τ.isCylinder.1 τ.isHoop_F₁ ⊆ cap.disc₁ τ.isCylinder.1 τ.isHoop_F₂)
    (G : Drawing cap.Z) (hGU : G.U = cap.j '' τ.Γ.U) (hGV : G.V = cap.j '' τ.Γ.V) :
    ∃ E : Set cap.Z, IsClosedDisc E ∧ E ⊆ cap.disc₂ τ.isCylinder.1 τ.isHoop_F₂ ∧
      Disjoint (cap.disc₁ τ.isCylinder.1 τ.isHoop_F₁) E ∧
      Disjoint (discInt (cap.disc₁ τ.isCylinder.1 τ.isHoop_F₁)) G.U ∧
      Disjoint (discInt E) G.U ∧ G.IsNormal E ∧
      G.V ∩ (discBd (cap.disc₁ τ.isCylinder.1 τ.isHoop_F₁) ∪ discBd E) =
        cap.j '' (τ.Γ.V ∩ (τ.F₁ ∪ τ.F₂)) := by
  have : T2Space cap.Z := cap.t2Space_Z
  obtain ⟨_, _, hb₁, _, _, hcap₁, _, _⟩ := cap.disc₁_disc₂_spec τ.isCylinder.1 τ.isHoop_F₁
  obtain ⟨_, hD₂, _, hb₂, _, hcap₂, _, _⟩ := cap.disc₁_disc₂_spec τ.isCylinder.1 τ.isHoop_F₂
  have hGUsub : G.U ⊆ cap.disc₁ τ.isCylinder.1 τ.isHoop_F₂ ∩
      cap.disc₂ τ.isCylinder.1 τ.isHoop_F₁ := by
    rw [hGU]
    rintro _ ⟨x, hx, rfl⟩
    have h := τ.U_subset hx
    rwa [cap.cylinderBetween_eq_of_disc₁_subset τ.isCylinder τ.isHoop_F₁ τ.isHoop_F₂ hle] at h
  have hoff₁ : Disjoint (discInt (cap.disc₁ τ.isCylinder.1 τ.isHoop_F₁)) G.U := by
    refine disjoint_left.mpr ?_
    intro x hx hxG
    exact hx.2 (hb₁.symm ▸ (hcap₁ ▸ ⟨hx.1, (hGUsub hxG).2⟩))
  have hoff₂ : Disjoint (discInt (cap.disc₂ τ.isCylinder.1 τ.isHoop_F₂)) G.U := by
    refine disjoint_left.mpr ?_
    intro x hx hxG
    exact hx.2 (hb₂.symm ▸ (hcap₂ ▸ ⟨(hGUsub hxG).1, hx.1⟩))
  have hinter : cap.disc₁ τ.isCylinder.1 τ.isHoop_F₁ ∩
      cap.disc₂ τ.isCylinder.1 τ.isHoop_F₂ ⊆
      discBd (cap.disc₁ τ.isCylinder.1 τ.isHoop_F₁) ∩
        discBd (cap.disc₂ τ.isCylinder.1 τ.isHoop_F₂) := by
    rw [cap.disc₁_inter_disc₂_eq_image_inter τ.isCylinder.1 τ.isHoop_F₁ τ.isHoop_F₂ hle,
      hb₁, hb₂, ← image_inter cap.inj]
  obtain ⟨E, hE, hsub, hdis, hoff, hnE, hroots⟩ := exists_separated_empty_sides G hD₂ hinter hoff₂
  refine ⟨E, hE, hsub, hdis, hoff₁, hoff, hnE, ?_⟩
  rw [hroots, hGV, hb₁, hb₂, ← image_union, ← image_inter cap.inj]

end GraphMinor.GM08
