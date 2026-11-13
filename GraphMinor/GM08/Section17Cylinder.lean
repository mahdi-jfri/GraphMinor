module

public import GraphMinor.GM08.Section15Tube
import GraphMinor.GM08.Section15ShortFraming
import GraphMinor.GM08.Section15CuffLength
import GraphMinor.GM08.Section18Map
import GraphMinor.GM08.Section9GraftDrawing

/-!
# Tubular grafts and cylinder drawings

The framing adjustment from (15.4) puts every tubular graft in a
cylinder with all roots on its cuffs. Transport it to any fixed
cylinder. Conversely, the two cuffs frame any proper graft drawing
in a cylinder. The cuff vertex counts add to its index. These are the
facts behind VIII (17.1), page 284.
-/

public section

namespace GraphMinor.GM08

open Set GraphMinor.Surface Graph

universe u v

/-- Every tubular graft embeds in any fixed cylinder, as asserted
before Graph Minors VIII (17.1), page 284. The framing adjustment also
covers touching hoops. -/
theorem embedsGraft_cylinder_of_isTubularGraft {S : Type} [TopologicalSpace S]
    (hS : IsCylinder S) {α : Type u} {β : Type v} {X : Graft α β}
    (hX : IsTubularGraft X) : EmbedsGraft S X := by
  obtain ⟨T, tT, τ, ⟨fr⟩⟩ := hX
  obtain ⟨Y, tY, hY, gd, _⟩ := fr.exists_short_cylinder_drawing (Nat.lt_succ_self τ.length)
  obtain ⟨eY⟩ := hY.2
  obtain ⟨eS⟩ := hS.2
  exact ⟨mapGraftDrawing (eY.trans eS.symm) gd⟩

/-- Choose the cylinder cap with its cuffs in a prescribed order.
This fixes the order of the two linking families in VIII (17.2). -/
theorem CylinderSphereCap.exists_with_cuffs {S : Type} [TopologicalSpace S]
    (hS : IsCylinder S) {C D : Set S} (hC : C ∈ cuffs S) (hD : D ∈ cuffs S)
    (hCD : C ≠ D) :
    ∃ cap : CylinderSphereCap S, cap.C₁ = C ∧ cap.C₂ = D := by
  obtain ⟨cap⟩ := CylinderSphereCap.exists_of_isCylinder hS
  rw [cap.cuffs_eq] at hC hD
  rcases hC with rfl | rfl <;> rcases hD with rfl | rfl
  · exact (hCD rfl).elim
  · exact ⟨cap, rfl, rfl⟩
  · exact ⟨cap.swap, rfl, rfl⟩
  · exact (hCD rfl).elim

/-- A graft drawing gives a framing whose hoops are the prescribed
ordered cylinder cuffs and whose drawing is unchanged. This is the
framing to which boundary linking is applied in VIII (17.2). -/
theorem exists_tube_framing_with_cuffs {S : Type} [TopologicalSpace S]
    (hS : IsCylinder S) {C D : Set S} (hC : C ∈ cuffs S) (hD : D ∈ cuffs S)
    (hCD : C ≠ D) {α : Type u} {β : Type v} {X : Graft α β}
    (gd : GraftDrawing X.G X.T S) :
    ∃ τ : Tube S, τ.Γ = gd.drawing ∧ τ.F₁ = C ∧ τ.F₂ = D ∧ τ.IsFraming X := by
  obtain ⟨cap, rfl, rfl⟩ := CylinderSphereCap.exists_with_cuffs hS hC hD hCD
  have hC₁ := cap.isHoop_C₁ hS.1
  have hC₂ := cap.isHoop_C₂ hS.1
  have hlam : AreLaminarHoops cap.C₁ cap.C₂ :=
    ⟨hS, hC₁, hC₂, cap.side₁ hS.1 hC₁, cap.side₂ hS.1 hC₁,
      cap.isHoopSidePair hS hC₁, .inr (cap.C₂_diff_subset_side₂ hS.1 hC₁)⟩
  let τ : Tube S := {
    Γ := gd.drawing
    F₁ := cap.C₁
    F₂ := cap.C₂
    isCylinder := hS
    laminar := hlam
    isNormal_F₁ := fun x hx => gd.isProper ⟨cap.bd_eq.symm ▸ (.inl hx.1), hx.2⟩
    isNormal_F₂ := fun x hx => gd.isProper ⟨cap.bd_eq.symm ▸ (.inr hx.1), hx.2⟩
    U_subset := by rw [cap.cylinderBetween_cuffs hS]; exact subset_univ _ }
  refine ⟨τ, rfl, rfl, rfl, ⟨gd.iso, ?_⟩⟩
  intro v
  change (gd.iso.vertexEquiv v).1 ∈ cap.C₁ ∪ cap.C₂ ↔ v.1 ∈ X.T
  rw [← cap.bd_eq]
  exact gd.mem_bd_iff v.1 v.2

/-- The two cuffs frame every graft drawn in a cylinder, as used in
Graph Minors VIII (17.1), page 284. -/
theorem isTubularGraft_of_embedsGraft_cylinder {S : Type} [TopologicalSpace S]
    (hS : IsCylinder S) {α : Type u} {β : Type v} {X : Graft α β}
    (hX : EmbedsGraft S X) : IsTubularGraft X := by
  obtain ⟨gd⟩ := hX
  obtain ⟨cap⟩ := CylinderSphereCap.exists_of_isCylinder hS
  have hC₁ := cap.isHoop_C₁ hS.1
  have hC₂ := cap.isHoop_C₂ hS.1
  have hlam : AreLaminarHoops cap.C₁ cap.C₂ :=
    ⟨hS, hC₁, hC₂, cap.side₁ hS.1 hC₁, cap.side₂ hS.1 hC₁,
      cap.isHoopSidePair hS hC₁, .inr (cap.C₂_diff_subset_side₂ hS.1 hC₁)⟩
  let τ : Tube S := {
    Γ := gd.drawing
    F₁ := cap.C₁
    F₂ := cap.C₂
    isCylinder := hS
    laminar := hlam
    isNormal_F₁ := fun x hx => gd.isProper ⟨cap.bd_eq.symm ▸ (.inl hx.1), hx.2⟩
    isNormal_F₂ := fun x hx => gd.isProper ⟨cap.bd_eq.symm ▸ (.inr hx.1), hx.2⟩
    U_subset := by rw [cap.cylinderBetween_cuffs hS]; exact subset_univ _ }
  refine ⟨S, inferInstance, τ, ⟨gd.iso, ?_⟩⟩
  intro v
  change (gd.iso.vertexEquiv v).1 ∈ cap.C₁ ∪ cap.C₂ ↔ v.1 ∈ X.T
  rw [← cap.bd_eq]
  exact gd.mem_bd_iff v.1 v.2

/-- On a cylinder, the counts of drawing vertices on its two distinct
cuffs add to the graft index. This is the count in VIII (17.1), page 284. -/
theorem graftDrawing_index_eq_cuff_counts {S : Type} [TopologicalSpace S]
    (hS : IsCylinder S) {C D : Set S} (hC : C ∈ cuffs S) (hD : D ∈ cuffs S)
    (hCD : C ≠ D) {α : Type u} {β : Type v} {X : Graft α β}
    (gd : GraftDrawing X.G X.T S) :
    X.index = (gd.drawing.V ∩ C).ncard + (gd.drawing.V ∩ D).ncard := by
  have : Nonempty S := hS.nonempty
  have hbd := graftDrawing_boundary_ncard gd
  rw [hS.bd_eq_union_of_cuffs hC hD hCD, inter_union_distrib_left,
    ncard_union_eq (disjoint_of_subset_left inter_subset_right
      (disjoint_of_subset_right inter_subset_right (cuffs_disjoint hC hD hCD)))
      (gd.drawing.finite_V.subset inter_subset_left) (gd.drawing.finite_V.subset inter_subset_left)] at hbd
  exact hbd.symm

end GraphMinor.GM08
