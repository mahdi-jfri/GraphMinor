module

public import GraphMinor.GM02.PortInnerVertices

/-!
# Geometry of the projected host routes

The feasible split paths supply routes for every pattern edge. Their
interiors avoid the branch vertices and are pairwise disjoint. Their
edge lists have no repetitions and are pairwise disjoint as well. The
proof transfers both kinds of disjointness through the exact split-vertex
correspondences, so it also applies to loops and parallel pattern edges.
-/

public section
namespace GraphMinor.GM02
open Graph Set Classical
universe u v

/-- Simultaneously project a feasible family, retaining its disjoint interiors and edge sets. -/
theorem exists_portGeometric_family {α : Type u} {β : Type v} {k : ℕ} (G H : Graph α β)
    {ends : Fin k → α × α} (choice : PortChoice G ends)
    (hVH : V(H) ⊆ V(G)) (hends : ∀ i, (ends i).1 ∈ V(H) ∧ (ends i).2 ∈ V(H))
    (hfeas : (portTermination G H choice).Feasible (portGraph G H choice)) :
    ∃ (inner : Fin k → List α) (W : ∀ i, Surface.GraphWalk G (ends i).1 (ends i).2),
      (∀ i, (W i).support = (ends i).1 :: (inner i ++ [(ends i).2]) ∧
        (inner i).Nodup ∧ (∀ y ∈ inner i, y ∈ V(G) \ V(H)) ∧
        (W i).edges.Nodup ∧ (W i).edges ≠ []) ∧
      ∀ i j, i ≠ j →
        Disjoint {y | y ∈ inner i} {y | y ∈ inner j} ∧
        Disjoint {e | e ∈ (W i).edges} {e | e ∈ (W j).edges} := by
  obtain ⟨P, hP⟩ := hfeas
  choose inner W hW using (fun i => exists_portRoute_inner G H choice hVH hends P hP i)
  refine ⟨inner, W, ?_, ?_⟩
  · intro i
    refine ⟨(hW i).1, (hW i).2.1, (hW i).2.2.1, (hW i).2.2.2.2.1, ?_⟩
    have hm := portPath_chosenEdge_mem G H choice i (P (portPair G H choice i)) false
    have he := ((hW i).2.2.2.2.2 _).2 hm
    intro hn
    rw [hn] at he
    exact List.not_mem_nil he
  · intro i j hij
    have hd := hP (portPair G H choice i) (portPair G H choice j)
      (fun h => hij (portPair_injective G H choice h))
    constructor
    · rw [Set.disjoint_left]
      intro y hyi hyj
      exact Set.disjoint_left.1 hd (((hW i).2.2.2.1 y).1 hyi) (((hW j).2.2.2.1 y).1 hyj)
    · rw [Set.disjoint_left]
      intro e hei hej
      exact Set.disjoint_left.1 hd (((hW i).2.2.2.2.2 e).1 hei) (((hW j).2.2.2.2.2 e).1 hej)

end GraphMinor.GM02
