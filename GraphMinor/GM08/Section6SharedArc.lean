module

public import GraphMinor.Surface.DiscGrow
import GraphMinor.Surface.EdgeLens
import GraphMinor.GM08.Section6SharedSide

/-!
# Enclosure from a retained arc and the common exterior

The boundary glued in VIII (6.2), page 264, shares a retained arc with the
old boundary. A thin lens around that arc avoids the two complementary
arcs. Its connected sides, together with access from the common exterior,
put the two discs on the same side. Separation then proves enclosure.
-/

public section

namespace GraphMinor.GM08

open Set Topology Surface

local notation "𝕀" => unitInterval

/-- Two discs sharing an embedded boundary arc choose the same interior
side when an interior point of that arc is approached from outside both.
If the old interior misses the new boundary, the old disc is enclosed.
This is the enclosure step for the excursion construction of VIII (6.2). -/
theorem disc_subset_of_shared_arc_and_common_exterior
    {S : Type} [TopologicalSpace S] (hS : IsClosedSurface S)
    {D E : Set S} (hD : IsClosedDisc D) (hE : IsClosedDisc E)
    {q f g : 𝕀 → S} (hqf : IsTwoArcs q f) (hqg : IsTwoArcs q g)
    (hDb : discBd D = range q ∪ range f) (hEb : discBd E = range q ∪ range g)
    {p : S} (hp : p ∈ q '' Ioo (0 : 𝕀) 1)
    (hpcl : p ∈ closure ((D ∪ E)ᶜ))
    (hdis : Disjoint (discInt D) (discBd E)) : D ⊆ E := by
  have : T2Space S := hS.2.1
  have hman : ∀ x : S, IsManifoldPoint x := fun x => (hS.2.2 x).isManifoldPoint
  let L := range q
  let Z := range f ∪ range g
  have hZ : IsClosed Z :=
    (isCompact_range hqf.2.1).isClosed.union (isCompact_range hqg.2.1).isClosed
  have hLZ : L ∩ Z ⊆ {q 0, q 1} := by
    rintro x ⟨⟨s, rfl⟩, (⟨t, ht⟩ | ⟨t, ht⟩)⟩
    · rcases hqf.5 s t ht.symm with h | h
      · exact Or.inl (congrArg q h.1)
      · exact Or.inr (congrArg q h.1)
    · rcases hqg.5 s t ht.symm with h | h
      · exact Or.inl (congrArg q h.1)
      · exact Or.inr (congrArg q h.1)
  have hne : q 0 ≠ q 1 := fun he => zero_ne_one (hqf.1.2 he)
  obtain ⟨T, A, B, hT, hLT, hTZ, _, _, hTL, hcover, hA, hB, _, _, hAL, hBL,
    _, _, _, _⟩ := exists_edge_lens hS hqf.1.isLineWithEnds hne hZ hLZ
  have hlocal : ∀ R : Set S, R ⊆ Z → T ∩ (L ∪ R) = L := by
    intro R hR
    apply subset_antisymm
    · rintro x ⟨hxT, hxL | hxR⟩
      · exact hxL
      · rcases hTZ ⟨hxT, hR hxR⟩ with hx0 | hx1
        · exact ⟨0, hx0.symm⟩
        · exact ⟨1, hx1.symm⟩
    · intro x hxL
      exact ⟨hLT hxL, Or.inl hxL⟩
  have hDL : T ∩ discBd D = L := by
    rw [hDb]
    exact hlocal (range f) subset_union_left
  have hEL : T ∩ discBd E = L := by
    rw [hEb]
    exact hlocal (range g) subset_union_right
  have hpL : p ∈ L := (image_subset_range _ _) hp
  have hpends : p ∉ ({q 0, q 1} : Set S) := by
    obtain ⟨r, hr, he⟩ := hp
    rintro (hp0 | hp1)
    · exact (ne_of_gt hr.1) (hqf.1.2 (he.trans hp0))
    · exact (ne_of_lt hr.2) (hqf.1.2 (he.trans hp1))
  have hpT : p ∈ discInt T := ⟨hLT hpL, fun h => hpends (hTL ⟨h, hpL⟩)⟩
  have hmeet := interiors_meet_of_shared_lens_and_common_exterior hman hD hE hT
    hcover hA hB hAL hBL hDL hEL hpL hpT hpcl
  exact disc_subset_of_interior_meets_and_boundary_disjoint hman hD hE hdis hmeet

end GraphMinor.GM08
