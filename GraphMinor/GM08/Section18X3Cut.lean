module

public import GraphMinor.GM08.Section18SurroundSides
public import GraphMinor.GM08.Section18CutCompose
public import GraphMinor.GM08.Section18LineCut
import GraphMinor.GM08.Section18SurroundFarSide
import GraphMinor.GM08.Section18DiscPiece
import GraphMinor.GM08.Section18LineLift
import GraphMinor.GM08.Section18Theorem182
import GraphMinor.GM12.Section3ThetaCircles
import GraphMinor.GM07.Section5a
import GraphMinor.GM07.Section8
import GraphMinor.Surface.ChartCells

/-!
# The cut along an `X₃`-arc

A schism of type (v) (VIII (18.2), page 286) is an `X₃`-arc: three lines
`P₁, P₂, P₃` with the same ends `u, v`, such that the circles `P₁ ∪ P₂`,
`P₁ ∪ P₃` and `P₂ ∪ P₃` surround three different cuffs. We cut in two steps.

1. Cut along the circle `A = P₁ ∪ P₂`, which surrounds a cuff `C`
   (`exists_surround_sides`). One side is a cylinder `W` around `C`.
2. The inside of `P₃` lifts to the far side `Wᶜ`. Otherwise `P₁ ∪ P₃` would
   lie in the image of `W`, so it would be planar after capping `C`, while it
   surrounds another cuff (`preimage_subset_compl_of_planar`). So the lift of
   `P₃` is a line in `Wᶜ` between two boundary points, and we cut `Wᶜ` along it
   (`exists_line_cut_piece`).

The second cut lowers the measure of `Wᶜ`, unless it has a disc piece. A disc
piece would give a planar circle in the arc (`exists_planar_oArc_of_disc_piece`),
and no circle of the arc is planar. The cylinder `W` has measure `2 < g(Σ)`.
Each point of the arc has at least two lifts, and the lift counts add up to at
most `2 |B| + 2` for a finite set `B` of the arc (`lifts_comp`), since the two
cut sets `A` and `P₃` share only `u` and `v`.
-/

@[expose] public section

namespace GraphMinor.GM08

open Set Topology GraphMinor.Surface GraphMinor.GM11

universe w

/-- The conclusion of (18.2) with lift counts, for a set `F` in `Σ`: a cut
along `F` with a smaller measure, at least two lifts over each point of `F`,
and at most `2 |B| + 2` lifts over a finite set `B ⊆ F`. -/
def HasCountedCut (S : Type w) [TopologicalSpace S] (F : Set S) : Prop :=
  ∃ (T : Type w) (_ : TopologicalSpace T) (ψ : T → S),
    GM07.IsCutAlongSet F ψ ∧ GM19.IsCutMap ψ F ∧
    surfaceComplexity T < surfaceComplexity S ∧
    (∀ x ∈ F, 1 < (ψ ⁻¹' {x}).ncard) ∧
    ∀ B ⊆ F, B.Finite → (ψ ⁻¹' B).ncard ≤ 2 * B.ncard + 2

variable {S T : Type w} [TopologicalSpace S] [TopologicalSpace T]

/-- Under a cut along a circle `A` with sides `W` and `Wᶜ`, every point of
`A` has a lift in `W`, since the map is one to one on `Wᶜ`. -/
theorem subset_image_of_surroundSides {A C : Set S} {ψ : T → S} {W : Set T}
    (hcut : IsCutting ψ A) (hs : SurroundSides ψ A C W) : A ⊆ ψ '' W := by
  intro a ha
  obtain ⟨z₁, z₂, hne, hpair⟩ := ncard_eq_two.mp (hcut.2.2.2.1 a ha)
  have h₁ : z₁ ∈ ψ ⁻¹' {a} := hpair ▸ Or.inl rfl
  have h₂ : z₂ ∈ ψ ⁻¹' {a} := hpair ▸ Or.inr rfl
  by_contra hno
  have hz₁ : z₁ ∈ Wᶜ := fun h => hno ⟨z₁, h, h₁⟩
  have hz₂ : z₂ ∈ Wᶜ := fun h => hno ⟨z₂, h, h₂⟩
  exact hne (hs.injOn_compl hz₁ hz₂ (h₁.trans h₂.symm))

/-- **A connected set lifts to the far side when it closes a circle that
surrounds another cuff.** Let `B` be connected and miss `A`, and let `A'` be a
circle in `A ∪ closure B` that surrounds a cuff other than `C`. Then `B` lifts
to the far side `Wᶜ`. -/
theorem preimage_subset_compl_of_planar [ConnectedSpace S] (hS : IsSurface S) (hT : IsSurface T)
    (hncyl : ¬ Nonempty (S ≃ₜ SurfaceModel 0 0 2)) {A C A' C' : Set S} {ψ : T → S}
    {W : Set T} (hcut : IsCutting ψ A) (hs : SurroundSides ψ A C W) (hC : C ∈ cuffs S)
    (hA' : IsOArc A') (hsur' : GM07.SurroundsCuff A' C') (hCC : C ≠ C') {B : Set S}
    (hB : IsPreconnected B) (hBA : Disjoint B A) (hA'B : A' ⊆ A ∪ closure B) :
    ψ ⁻¹' B ⊆ Wᶜ := by
  have : CompactSpace T := hT.1
  have : T2Space S := hS.2.1
  have hpre := isPreconnected_preimage_of_isCutMap (GM19.IsCutting.isCutMap hcut) hB hBA
  have hcov : ψ ⁻¹' B ⊆ W ∪ Wᶜ := fun z _ => (em (z ∈ W)).elim Or.inl Or.inr
  rcases hpre.subset_or_subset hs.isClopen.isOpen hs.isClopen.compl.isOpen disjoint_compl_right
      hcov with h | h
  · exfalso
    have hWc : IsClosed (ψ '' W) := (hs.isClopen.isClosed.isCompact.image hcut.1).isClosed
    have hBW : B ⊆ ψ '' W := by
      intro b hb
      obtain ⟨z, rfl⟩ := hcut.2.1 b
      exact ⟨z, h hb, rfl⟩
    have hsub : A' ⊆ ψ '' W := hA'B.trans (union_subset (subset_image_of_surroundSides hcut hs)
      (closure_minimal hBW hWc))
    have hp : GM07.IsPlanarInCappedCuff C A' := (hs.planar W subset_rfl).mono hsub
    exact hncyl (GM07.surroundsCuff_and_planarInCappedCuff_imp_cylinder hS hsur'.1 hC
      (Ne.symm hCC) hA' hsur' hp)
  · exact h

/-- The cylinder side `W` of a surrounding circle has components of measure two. -/
theorem connectedSurfaceComplexity_component_of_mem_cylinder {A C : Set S} {ψ : T → S}
    {W : Set T} (hs : SurroundSides ψ A C W) {z : T} (hz : z ∈ W) :
    connectedSurfaceComplexity (connectedComponent z) = 2 := by
  have := hs.connected
  obtain ⟨e⟩ := hs.cylinder
  rw [← connectedSurfaceComplexity_component_subtype hs.isClopen ⟨z, hz⟩]
  have hu : connectedComponent (⟨z, hz⟩ : W) = univ :=
    PreconnectedSpace.connectedComponent_eq_univ _
  exact connectedSurfaceComplexity_component_model
    (((Homeomorph.setCongr hu).trans (Homeomorph.Set.univ W)).trans e)

/-- **(18.2) with lift counts for an `X₃`-arc.** -/
theorem hasCountedCut_X3 [ConnectedSpace S] (hS : IsSurface S)
    (hncyl : ¬ Nonempty (S ≃ₜ SurfaceModel 0 0 2)) (h3 : 3 ≤ surfaceComplexity S)
    {P₁ P₂ P₃ : Set S} {u v : S} (huv : u ≠ v) (hP₁ : IsLineWithEnds P₁ u v)
    (hP₂ : IsLineWithEnds P₂ u v) (hP₃ : IsLineWithEnds P₃ u v)
    (h12 : P₁ ∩ P₂ = {u, v}) (h13 : P₁ ∩ P₃ = {u, v}) (h23 : P₂ ∩ P₃ = {u, v})
    (hoff : Disjoint (P₁ ∪ P₂ ∪ P₃) (bd S)) {C C' : Set S}
    (hsur : GM07.SurroundsCuff (P₁ ∪ P₂) C) (hsur' : GM07.SurroundsCuff (P₁ ∪ P₃) C')
    (hCC : C ≠ C') (hnp : ∀ Z ⊆ P₁ ∪ P₂ ∪ P₃, IsOArc Z → ¬ IsPlanar Z) :
    HasCountedCut S (P₁ ∪ P₂ ∪ P₃) := by
  have : T2Space S := hS.2.1
  set A := P₁ ∪ P₂ with hAdef
  have hA : IsOArc A := GM12.isOArc_union_of_lines_inter_eq_ends hP₁ hP₂ h12
  have hAc : IsClosed A := hA.isCompact.isClosed
  have hAoff : Disjoint A (bd S) := hoff.mono_left subset_union_left
  obtain ⟨T₁, t₁, ψ₁, W, hT₁, hcut₁, hs, hgR⟩ := exists_surround_sides hS hncyl h3 hA hAoff hsur
  have : CompactSpace T₁ := hT₁.1
  have : T2Space T₁ := hT₁.2.1
  have huA : u ∈ A := Or.inl hP₁.left_mem
  have hvA : v ∈ A := Or.inl hP₁.right_mem
  have hP₃A : Disjoint (P₃ \ {u, v}) A := by
    refine disjoint_left.mpr fun z hz hzA => hz.2 ?_
    rcases hzA with h | h
    · exact h13 ▸ ⟨h, hz.1⟩
    · exact h23 ▸ ⟨h, hz.1⟩
  obtain ⟨x, y, hx, hy, hL, hbij, hdiff⟩ :=
    exists_line_closure_lift_of_cutMap (GM19.IsCutting.isCutMap hcut₁) hAc hP₃ hP₃A
  set L := closure (ψ₁ ⁻¹' (P₃ \ {u, v}))
  have hfar : ψ₁ ⁻¹' (P₃ \ {u, v}) ⊆ Wᶜ :=
    preimage_subset_compl_of_planar hS hT₁ hncyl hcut₁ hs hsur.1
      (GM12.isOArc_union_of_lines_inter_eq_ends hP₁ hP₃ h13) hsur' hCC
      (GM11.IsLineWithEnds.isPreconnected_sdiff_pair hP₃) hP₃A
      (union_subset (subset_union_left.trans subset_union_left)
        (hP₃.subset_closure_diff.trans subset_union_right))
  have hLR : L ⊆ Wᶜ := closure_minimal hfar hs.isClopen.compl.isClosed
  have hxy : x ≠ y := fun h => huv (hx ▸ hy ▸ congrArg ψ₁ h)
  have hbdT : ψ₁ ⁻¹' (bd S ∪ A) = bd T₁ :=
    (isCutAlongSet_of_isCutting hS hT₁ hAc hcut₁).preimage_bd
  have hLbd : L ∩ bd T₁ = {x, y} := by
    ext z
    constructor
    · rintro ⟨hzL, hzb⟩
      by_contra hz
      have hz' : z ∈ ψ₁ ⁻¹' (P₃ \ {u, v}) := hdiff ▸ ⟨hzL, hz⟩
      rcases (hbdT ▸ hzb : z ∈ ψ₁ ⁻¹' (bd S ∪ A)) with h | h
      · exact disjoint_left.mp hoff (Or.inr hz'.1) h
      · exact disjoint_left.mp hP₃A hz' h
    · rintro (rfl | rfl)
      · exact ⟨hL.left_mem, hcut₁.2.2.2.2 (show ψ₁ z ∈ A by rw [hx]; exact huA)⟩
      · exact ⟨hL.right_mem, hcut₁.2.2.2.2 (show ψ₁ z ∈ A by rw [hy]; exact hvA)⟩
  have := hs.connected_compl
  obtain ⟨T₂, t₂, ψ₂, hT₂, hcut₂, hcase⟩ :=
    exists_line_cut_piece hT₁ hs.isClopen.compl hLR hL hxy hLbd
  have hLc : IsClosed L := isClosed_closure
  have hG₂H : L ⊆ ψ₁ ⁻¹' P₃ := fun z hz => hbij.mapsTo hz
  have hH : ψ₁ ⁻¹' P₃ ⊆ L ∪ bd T₁ := by
    intro z hz
    by_cases huvz : ψ₁ z ∈ ({u, v} : Set S)
    · refine Or.inr (hcut₁.2.2.2.2 ?_)
      rcases huvz with h | h
      · exact (show ψ₁ z ∈ A by rw [h]; exact huA)
      · exact (show ψ₁ z ∈ A by rw [mem_singleton_iff.mp h]; exact hvA)
    · exact Or.inl (subset_closure ⟨hz, huvz⟩)
  have hHG₂ : ψ₁ ⁻¹' (P₃ \ A) ⊆ L := by
    intro z hz
    refine subset_closure ⟨hz.1, fun h => hz.2 ?_⟩
    rcases h with h | h
    · rw [h]; exact huA
    · rw [mem_singleton_iff.mp h]; exact hvA
  have hFc : IsClosed (A ∪ P₃) := hAc.union hP₃.isCompact.isClosed
  have hcutF := isCutAlongSet_comp hS hT₁ hT₂ hcut₁ hAc hcut₂ hLc hG₂H hH
  have hmapF := isCutMap_comp hT₁ hT₂ hcut₁ hcut₂ hLc hG₂H hH
  obtain ⟨hlift, hcount⟩ := lifts_comp hcut₁ hcut₂ hbij.injOn hG₂H hHG₂
  have hAP : A ∩ P₃ = {u, v} := by rw [hAdef, union_inter_distrib_right, h13, h23, union_self]
  refine ⟨T₂, t₂, ψ₁ ∘ ψ₂, hcutF, hmapF, ?_, hlift, fun B _ hB =>
    (hcount B hB).trans (ncard_bound_of_inter hB (hAP ▸ toFinite _) ?_)⟩
  rotate_left
  · rw [hAP]
    exact (ncard_insert_le _ _).trans (by rw [ncard_singleton])
  rcases hcase with hle | ⟨D, hDo, hD, hinj, hDQ, hmeet⟩
  · have := hle (surfaceComplexity S - 1) (by omega) fun z hz => by
      rw [connectedSurfaceComplexity_component_of_mem_cylinder hs (not_not.mp hz)]
      omega
    omega
  · exfalso
    have hinj' : InjOn (ψ₁ ∘ ψ₂) D := fun a ha b hb hab =>
      hinj ha hb (hs.injOn_compl (hDQ ha) (hDQ hb) hab)
    obtain ⟨z, hzD, hzL⟩ := hmeet
    obtain ⟨Z, hZF, hZ, hZp⟩ := exists_planar_oArc_of_disc_piece hS hFc
      hoff hcutF hDo hD hinj'
      ⟨z, hzD, Or.inr (hG₂H hzL)⟩
    exact hnp Z hZF hZ hZp

end GraphMinor.GM08
