module

public import GraphMinor.GM08.Section17Defs
public import GraphMinor.GM08.Section16PrintedDefs
import GraphMinor.GM08.Section17Cylinder
import GraphMinor.GM08.Section17FreeCylinder
import GraphMinor.GM08.Section17Crossing
import GraphMinor.GM08.Section15FramingDrawing
import GraphMinor.GM11.PaintingRegions

/-!
# The empty-cuff case of VIII (17.2)

Cap the cylinder and retain the disc on the cuff containing the roots.
The other cuff has no drawing vertices. Choose a new free hole next
to the retained disc. The resulting cylinder drawing has precisely
the same graft roots and a free cuff-joining arc. Its cuff framing is
not `(r,2)`-boundary-linked. Thus the unlinked alternative of (17.2)
always holds when either fixed cuff count is zero.
-/

public section

namespace GraphMinor.GM08

open Set Topology GraphMinor.Surface

universe u v

/-- If one cuff is empty of drawing vertices, the graft has a cylinder
drawing with a free cuff-joining arc. This is the framing choice for
the empty-cuff case of VIII (17.2), page 284. -/
theorem exists_free_cuff_arc_drawing_of_empty_cuff {S : Type}
    [TopologicalSpace S] (hS : IsCylinder S)
    {C D : Set S} (hC : C ∈ cuffs S) (hD : D ∈ cuffs S) (hCD : C ≠ D)
    {α : Type u} {β : Type v} {X : Graft α β}
    (gd : GraftDrawing X.G X.T S) (hempty : gd.drawing.V ∩ C = ∅) :
    ∃ (Q : Type) (_ : TopologicalSpace Q), IsCylinder Q ∧
      ∃ (gdQ : GraftDrawing X.G X.T Q) (C₁ C₂ I : Set Q) (a b : Q),
        C₁ ∈ cuffs Q ∧ C₂ ∈ cuffs Q ∧ C₁ ≠ C₂ ∧
        IsLineWithEnds I a b ∧ a ∈ C₁ ∧ b ∈ C₂ ∧ Disjoint I gdQ.drawing.U := by
  have : T2Space S := hS.1.2.1
  have : CompactSpace S := hS.1.1
  have : Nonempty S := hS.nonempty
  obtain ⟨cap, rfl, rfl⟩ := CylinderSphereCap.exists_with_cuffs hS hC hD hCD
  have : T2Space cap.Z := cap.t2Space_Z
  obtain ⟨τ, hτΓ, hτC, hτD, ⟨fr⟩⟩ := exists_tube_framing_with_cuffs hS hC hD hCD gd
  obtain ⟨G, hm⟩ := GM07.exists_image_matched cap.isClosedEmbedding τ.Γ
  have hGU : G.U = cap.j '' τ.Γ.U := by simpa using hm.image_U.symm
  have hGV : G.V = cap.j '' τ.Γ.V := by simpa using hm.image_V.symm
  have hnormal : G.IsNormal (discBd cap.D₂) := by
    rw [cap.discBd_D₂]
    rintro z ⟨⟨x, hxD, rfl⟩, hzU⟩
    obtain ⟨y, hyU, heq⟩ := hGU ▸ hzU
    have hxU : x ∈ τ.Γ.U := cap.inj heq ▸ hyU
    have hxV : x ∈ τ.Γ.V := τ.isNormal_F₂ ⟨hτD.symm ▸ hxD, hxU⟩
    rw [hGV]
    exact mem_image_of_mem cap.j hxV
  have hoff : Disjoint (discInt cap.D₂) G.U := by
    apply disjoint_left.mpr
    intro z hzD hzG
    obtain ⟨x, _, rfl⟩ := hGU ▸ hzG
    exact disjoint_left.mp cap.disjoint_range_discInt_D₂ ⟨x, rfl⟩ hzD
  obtain ⟨p, hp, hpV⟩ :=
    ((GM11.infinite_of_isOArc cap.isClosedDisc_D₂.isOArc_discBd).sdiff G.finite_V).nonempty
  have hpoff : p ∉ G.U := fun hpU => hpV (hnormal ⟨hp, hpU⟩)
  obtain ⟨E, _, _, H, hQ, hH, hroots, ⟨i, hiv⟩,
    C₁, C₂, I, a, b, hC₁, hC₂, hne, hI, ha, hb, hIG⟩ :=
    exists_free_cylinder_drawing cap.isClosedSurface cap.isSphere G
      cap.isClosedDisc_D₂ hoff hnormal hp hpoff
  let Q := GM12.discComplement (![cap.D₂, E] : Fin 2 → Set cap.Z)
  have hroot_image : G.V ∩ discBd cap.D₂ =
      cap.j '' (τ.Γ.V ∩ (τ.F₁ ∪ τ.F₂)) := by
    rw [hGV, cap.discBd_D₂, ← image_inter cap.inj, hτC, hτD,
      inter_union_distrib_left]
    have hz : τ.Γ.V ∩ cap.C₁ = ∅ := by rw [hτΓ]; exact hempty
    rw [hz, empty_union]
  obtain ⟨gdQ, hgd⟩ := exists_graftDrawing_of_framing_image fr
    cap.isClosedEmbedding.isEmbedding hm H hH i Subtype.val_injective hiv
    (hroots.trans hroot_image)
  refine ⟨Q, inferInstance, hQ, gdQ, C₁, C₂, I, a, b,
    hC₁, hC₂, hne, hI, ha, hb, ?_⟩
  simpa only [hgd] using hIG

/-- The unlinked alternative of VIII (17.2), page 284, holds for every
graft in the fixed-cuff class when its first count is zero. -/
theorem mem_printedClassBUnlinked_of_zero_first_cuff {S : Type}
    [TopologicalSpace S] (hS : IsCylinder S)
    {C D : Set S} (hC : C ∈ cuffs S) (hD : D ∈ cuffs S) (hCD : C ≠ D)
    {α : Type u} {β : Type v} {X : Graft α β} {k r : ℕ}
    (hX : X ∈ classBCuffCounts S C D 0 k) : X ∈ printedClassBUnlinked k r 2 := by
  obtain ⟨gd, hzero, hk⟩ := hX
  have hindex := graftDrawing_index_eq_cuff_counts hS hC hD hCD gd
  rw [hzero, hk, zero_add] at hindex
  have hempty := (ncard_eq_zero (gd.drawing.finite_V.inter_of_left C)).mp hzero
  obtain ⟨Q, tQ, hQ, gdQ, C₁, C₂, I, a, b, hC₁, hC₂, hne, hI, ha, hb, hIG⟩ :=
    exists_free_cuff_arc_drawing_of_empty_cuff hS hC hD hCD gd hempty
  obtain ⟨τ, hτΓ, hτC, hτD, hfr⟩ := exists_tube_framing_with_cuffs hQ hC₁ hC₂ hne gdQ
  refine ⟨hindex.le, Q, tQ, τ, hfr, ?_⟩
  apply τ.not_printedBoundaryLinked_of_free_cuff_arc
    (hτC.symm ▸ hC₁) (hτD.symm ▸ hC₂)
    (by simpa only [hτC, hτD] using hne) hI
    (hτC.symm ▸ ha) (hτD.symm ▸ hb)
  simpa only [hτΓ] using hIG

/-- The empty second cuff gives the same unlinked alternative of
VIII (17.2), page 284, after reversing the cuff order. -/
theorem mem_printedClassBUnlinked_of_zero_second_cuff {S : Type}
    [TopologicalSpace S] (hS : IsCylinder S)
    {C D : Set S} (hC : C ∈ cuffs S) (hD : D ∈ cuffs S) (hCD : C ≠ D)
    {α : Type u} {β : Type v} {X : Graft α β} {k r : ℕ}
    (hX : X ∈ classBCuffCounts S C D k 0) : X ∈ printedClassBUnlinked k r 2 := by
  obtain ⟨gd, hk, hzero⟩ := hX
  exact mem_printedClassBUnlinked_of_zero_first_cuff hS hD hC hCD.symm ⟨gd, hzero, hk⟩

end GraphMinor.GM08
