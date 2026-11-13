module

public import GraphMinor.GM01.RootedSubcubicPaths
import GraphMinor.GM16.SubdivisionPathDisjoint
import GraphMinor.GM09.Basic

/-!
# The rooted subdivision subgraph

For the positive-height proof used in Graph Minors I, (1.1), page 55,
join the replacing paths into a subgraph and retain the branch centres.
Distinct replacing paths are edge disjoint and meet only at centres.
The separate path from the target root meets this subgraph only at the
source-root centre. The centre map and replacing paths give the explicit
isomorphism with the source subdivision.
-/

public section

namespace GraphMinor.GM01

open Set Graph SimpleGraph Function GraphMinor.GM09 GraphMinor.GM16

universe u v w

/-- The rooted subdivision assertion used on page 55 of the proof of
Graph Minors I, (1.1). The map `c` specifies the source vertices in the
subdivision, and `P` specifies its replacing edge paths. The path `R`
from the distinguished target root meets the subdivision only at `c r`.
The union retains an ordinary source minor model with `c r` in its root
branch. -/
theorem exists_rooted_subcubic_subdivision {α : Type u} {β : Type v} {ν : Type w} [Finite ν]
    {H : SimpleGraph ν} {G : Graph α β} {ηv : ν → Set α} {ηe : Sym2 ν → β}
    (h : IsMinorModel (Graph.ofSimpleGraph H) G ηv ηe)
    (hDeg : ∀ v, (H.neighborSet v).ncard ≤ 3) (r : ν)
    (hRootDeg : (H.neighborSet r).ncard ≤ 2) (hNonempty : (H.neighborSet r).Nonempty)
    (root : α) (hroot : root ∈ ηv r) :
    ∃ (N : Graph α β) (c : ν → α) (P : H.edgeSet → Graph α β) (R : Graph α β),
      N ≤ G ∧ Injective c ∧ (∀ v, c v ∈ ηv v) ∧
      V(N) = range c ∪ ⋃ e, V(P e) ∧ E(N) = ⋃ e, E(P e) ∧
      (∀ e : H.edgeSet, ∃ a b, e.val = s(a,b) ∧ H.Adj a b ∧
        IsGraphPathWithEnds N (P e) (c a) (c b) ∧ ηe e.val ∈ E(P e) ∧
        V(P e) ∩ range c = {c a,c b}) ∧
      (∀ e f : H.edgeSet, e ≠ f → Disjoint E(P e) E(P f) ∧
        V(P e) ∩ V(P f) ⊆ range c) ∧
      IsGraphPathWithEnds G R root (c r) ∧ V(R) ∩ V(N) = {c r} ∧
      ∃ ηv' : ν → Set α, IsMinorModel (Graph.ofSimpleGraph H) N ηv' ηe ∧ c r ∈ ηv' r := by
  obtain ⟨c, P, R, hcInj, hc, hPaths, hInter, hR, hRRange, hRPaths, ηv', hModelN, hcRoot⟩ :=
    exists_rooted_subcubic_edge_paths h hDeg r hRootDeg hNonempty root hroot
  have hP : ∀ e, P e ≤ G := by
    intro e
    obtain ⟨_, _, _, _, hPath, _, _⟩ := hPaths e
    exact hPath.le
  have hC : range c ⊆ V(G) := by
    rintro x ⟨v, rfl⟩
    exact h.vertex_subset v (mem_univ _) (hc v)
  have hDisj := subdivision_paths_edge_disjoint c hcInj P
    (fun e ↦ by
      obtain ⟨a, b, he, _, hPath, _, hRange⟩ := hPaths e
      exact ⟨a, b, he, hPath, hRange⟩) hInter
  let N := pathSystemGraph G (range c) P
  have hRMeet : V(R) ∩ V(N) = {c r} := by
    apply Subset.antisymm
    · rintro x ⟨hxR, hxN⟩
      change x ∈ range c ∪ ⋃ e, V(P e) at hxN
      rcases hxN with hxC | hxP
      · exact hRRange ▸ ⟨hxR, hxC⟩
      · obtain ⟨e, hxe⟩ := mem_iUnion.mp hxP
        exact hRPaths e ⟨hxR, hxe⟩
    · rintro x rfl
      exact ⟨hR.right_mem, Or.inl (mem_range_self r)⟩
  refine ⟨N, c, P, R, pathSystemGraph_le hC hP, hcInj, hc,
    pathSystemGraph_vertexSet G (range c) P, pathSystemGraph_edgeSet hP,
    ?_, ?_, hR, hRMeet, ηv', hModelN, hcRoot⟩
  · intro e
    obtain ⟨a, b, he, hAdj, hPath, hChosen, hRange⟩ := hPaths e
    exact ⟨a, b, he, hAdj, hPath.of_le (le_pathSystemGraph hP e), hChosen, hRange⟩
  · intro e f hne
    exact ⟨hDisj e f hne, hInter e f hne⟩

end GraphMinor.GM01
