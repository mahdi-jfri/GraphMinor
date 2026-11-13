module

public import GraphMinor.GM02.InducedPathIntersections
import GraphMinor.GM02.CrossingPathLists
import GraphMinor.GM02.JoinPairPaths

/-!
# Gluing feasible corrected induced graphs

For the reverse implication of corrected II (2.9), choose a path for each
edge of the crossing-scheme graph from whichever induced family contains
that pair. Paths selected from the same family are disjoint. Paths from
opposite families meet only at shared endpoints, by the corrected induced
vertex intersection. Joining these replacements proves original feasibility.
-/

public section
namespace GraphMinor.GM02
open Graph SimpleGraph Set Classical
universe u v

/-- Reverse implication of II (2.9), page 315, with the corrected induced
graphs that also delete original terminals assigned only to the other side.
The printed induced graphs do not satisfy this implication. -/
theorem feasible_of_corrected_induced_feasible {α : Type u} {β : Type v}
    {G H H' : Graph α β} {A₀ : Termination V(G)} (hsep : IsSeparation G H H')
    (C : CrossingScheme G H H' A₀) (hL : C.left.Feasible C.inducedLeft)
    (hR : C.right.Feasible C.inducedRight) : A₀.Feasible G := by
  obtain ⟨P, hP⟩ := hL
  obtain ⟨Q, hQ⟩ := hR
  have hmem : ∀ e : C.pairGraph.edgeSet, e.val ∈ C.left.pairs ∨ e.val ∈ C.right.pairs := by
    intro e
    have he := e.property
    change e.val ∈ (SimpleGraph.fromEdgeSet (C.left.pairs ∪ C.right.pairs : Finset (Sym2 α))).edgeSet at he
    simp only [SimpleGraph.edgeSet_fromEdgeSet] at he
    exact Finset.mem_union.1 he.1
  let R : ∀ e : C.pairGraph.edgeSet, PairPath (pathGraph G) e.val := fun e =>
    if he : e.val ∈ C.left.pairs then
      (P ⟨e.val, he⟩).mapLe (C.inducedLeft_le hsep)
    else (Q ⟨e.val, (hmem e).resolve_left he⟩).mapLe (C.inducedRight_le hsep)
  have hInt : ∀ e f, e ≠ f → (R e).vertices ∩ (R f).vertices ⊆
      {a | a ∈ e.val ∧ a ∈ f.val} := by
    intro e f hef a ha
    by_cases he : e.val ∈ C.left.pairs <;> by_cases hf : f.val ∈ C.left.pairs
    · have hae : a ∈ (P ⟨e.val, he⟩).vertices := by
        simpa only [R, dite_eq_left he, PairPath.vertices_mapLe] using ha.1
      have haf : a ∈ (P ⟨f.val, hf⟩).vertices := by
        simpa only [R, dite_eq_left hf, PairPath.vertices_mapLe] using ha.2
      have hne : (⟨e.val, he⟩ : {p // p ∈ C.left.pairs}) ≠ ⟨f.val, hf⟩ := by
        intro h
        have hv : e.val = f.val := congrArg (fun p : {p // p ∈ C.left.pairs} => p.val) h
        exact hef (Subtype.ext hv)
      exact (Set.disjoint_left.1 (hP _ _ hne) hae haf).elim
    · have hae : a ∈ (P ⟨e.val, he⟩).vertices := by
        simpa only [R, dite_eq_left he, PairPath.vertices_mapLe] using ha.1
      have haf : a ∈ (Q ⟨f.val, (hmem f).resolve_left hf⟩).vertices := by
        simpa only [R, dite_eq_right hf, PairPath.vertices_mapLe] using ha.2
      exact C.induced_paths_inter_subset P Q hP hQ _ _ ⟨hae, haf⟩
    · have hae : a ∈ (Q ⟨e.val, (hmem e).resolve_left he⟩).vertices := by
        simpa only [R, dite_eq_right he, PairPath.vertices_mapLe] using ha.1
      have haf : a ∈ (P ⟨f.val, hf⟩).vertices := by
        simpa only [R, dite_eq_left hf, PairPath.vertices_mapLe] using ha.2
      exact (C.induced_paths_inter_subset P Q hP hQ _ _ ⟨haf, hae⟩).symm
    · have hae : a ∈ (Q ⟨e.val, (hmem e).resolve_left he⟩).vertices := by
        simpa only [R, dite_eq_right he, PairPath.vertices_mapLe] using ha.1
      have haf : a ∈ (Q ⟨f.val, (hmem f).resolve_left hf⟩).vertices := by
        simpa only [R, dite_eq_right hf, PairPath.vertices_mapLe] using ha.2
      have hne : (⟨e.val, (hmem e).resolve_left he⟩ : {p // p ∈ C.right.pairs}) ≠
          ⟨f.val, (hmem f).resolve_left hf⟩ := by
        intro h
        have hv : e.val = f.val := congrArg (fun p : {p // p ∈ C.right.pairs} => p.val) h
        exact hef (Subtype.ext hv)
      exact (Set.disjoint_left.1 (hQ _ _ hne) hae haf).elim
  exact feasible_of_pairPathUnion_replacements A₀ G C.pairGraph C.path_union R hInt

end GraphMinor.GM02
