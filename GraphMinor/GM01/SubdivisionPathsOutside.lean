module

public import GraphMinor.GM01.SubdivisionSides

/-!
# Replacing paths outside a later region

The two-cell comb in the skipped block of Graph Minors I, (4.1), page 55,
must stay outside the next tail region. A selected source edge with no
end on the later source side cannot contribute a vertex of that region.
If its replacing path meets a path incident with that side, they meet at
a source centre. Away from the deleted centre, that centre belongs to
the later source side, contradicting the selected edge's ends.
-/

public section

namespace GraphMinor.GM01

open Set Graph SimpleGraph

/-- A replacing path whose source edge has no end on a source side is
disjoint from the corresponding avoidance region in the subdivision.
The cut centre itself is excluded by deletion. -/
theorem subdivision_path_disjoint_region {α β ν : Type*} {S : SimpleGraph ν}
    {N : Graph α β} {c : ν → α} (hc : Function.Injective c)
    {P : S.edgeSet → Graph α β} (hPN : ∀ e, P e ≤ N)
    (hE : E(N) = ⋃ e, E(P e))
    (hPaths : ∀ e : S.edgeSet, ∃ a b, e.val = s(a,b) ∧
      V(P e) ∩ range c = {c a,c b})
    (hInter : ∀ e f : S.edgeSet, e ≠ f → V(P e) ∩ V(P f) ⊆ range c)
    (D : Set ν) (r : ν)
    (hD : ∀ {a b}, S.Adj a b → a ∈ D → b ≠ r → b ∈ D)
    (t : ν) (ht : t ∈ D) (e : S.edgeSet) (heD : ∀ v ∈ e.val, v ∉ D) :
    Disjoint V(P e) (vertexAvoidanceRegion N (c t) (c r)) := by
  apply Set.disjoint_left.mpr
  intro x hxP hxR
  have hxSide := vertexAvoidanceRegion_subdivision_subset_side hc hPN hE hPaths hInter D r hD t ht hxR
  have hxAll := hxSide
  rcases hxSide with ⟨v, hvD, rfl⟩ | hxSide
  · exact heD v ((subdivision_centre_mem_path_iff hc hPaths e v).mp hxP) hvD
  · obtain ⟨f, hxSide⟩ := mem_iUnion.mp hxSide
    obtain ⟨hselect, hxf⟩ := mem_iUnion.mp hxSide
    have hef : e ≠ f := by
      intro heq
      obtain ⟨v, hvD, hvf⟩ := hselect
      exact heD v (heq.symm ▸ hvf) hvD
    obtain ⟨v, rfl⟩ := hInter e f hef ⟨hxP, hxf⟩
    have hvne : v ≠ r := by
      intro h
      exact (vertexAvoidanceRegion_subset N (c t) (c r) hxR).2 (congrArg c h)
    have hvD := (subdivision_centre_mem_side_iff hc hPaths D r hD hvne).mp hxAll
    exact heD v ((subdivision_centre_mem_path_iff hc hPaths e v).mp hxP) hvD

/-- A centre outside the source side is outside the corresponding
avoidance region, including when it is the deleted centre itself. -/
theorem subdivision_centre_not_mem_region {α β ν : Type*} {S : SimpleGraph ν}
    {N : Graph α β} {c : ν → α} (hc : Function.Injective c)
    {P : S.edgeSet → Graph α β} (hPN : ∀ e, P e ≤ N)
    (hE : E(N) = ⋃ e, E(P e))
    (hPaths : ∀ e : S.edgeSet, ∃ a b, e.val = s(a,b) ∧
      V(P e) ∩ range c = {c a,c b})
    (hInter : ∀ e f : S.edgeSet, e ≠ f → V(P e) ∩ V(P f) ⊆ range c)
    (D : Set ν) (r : ν)
    (hD : ∀ {a b}, S.Adj a b → a ∈ D → b ≠ r → b ∈ D)
    (t : ν) (ht : t ∈ D) (v : ν) (hv : v ∉ D) :
    c v ∉ vertexAvoidanceRegion N (c t) (c r) := by
  intro hmem
  by_cases hvr : v = r
  · exact (vertexAvoidanceRegion_subset N (c t) (c r) hmem).2 (congrArg c hvr)
  · have hside := vertexAvoidanceRegion_subdivision_subset_side
      hc hPN hE hPaths hInter D r hD t ht hmem
    exact hv ((subdivision_centre_mem_side_iff hc hPaths D r hD hvr).mp hside)

end GraphMinor.GM01
