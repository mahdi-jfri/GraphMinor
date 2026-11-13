module

public import GraphMinor.GM02.PortRoutes

/-!
# Edge-disjoint projected route families

Project every member of a feasible split family. Its chosen first edge
ensures the projected walk has positive length, including for a pattern
loop. Disjointness of split paths gives disjointness of their host-edge
sets, even when pattern edges have the same ends.
-/

public section
namespace GraphMinor.GM02
open Graph Set Classical
universe u v

/-- A feasible split family supplies nonempty host walks with disjoint edge sets. -/
theorem exists_portRoute_family {α : Type u} {β : Type v} {k : ℕ} (G H : Graph α β)
    {ends : Fin k → α × α} (choice : PortChoice G ends)
    (hVH : V(H) ⊆ V(G)) (hends : ∀ i, (ends i).1 ∈ V(H) ∧ (ends i).2 ∈ V(H))
    (hfeas : (portTermination G H choice).Feasible (portGraph G H choice)) :
    ∃ W : ∀ i, Surface.GraphWalk G (ends i).1 (ends i).2,
      (∀ i, (W i).edges.Nodup ∧ (W i).edges ≠ []) ∧
      ∀ i j, i ≠ j → Disjoint {e | e ∈ (W i).edges} {e | e ∈ (W j).edges} := by
  obtain ⟨P, hP⟩ := hfeas
  choose W hW using (fun i => exists_portRoute G H choice hVH hends P hP i)
  refine ⟨W, ?_, ?_⟩
  · intro i
    refine ⟨(hW i).1, ?_⟩
    have hm := portPath_chosenEdge_mem G H choice i (P (portPair G H choice i)) false
    have he := ((hW i).2 _).2 hm
    intro hn
    rw [hn] at he
    exact List.not_mem_nil he
  · intro i j hij
    rw [Set.disjoint_left]
    intro e hei hej
    exact Set.disjoint_left.1 (hP (portPair G H choice i) (portPair G H choice j)
      (fun h => hij (portPair_injective G H choice h)))
      (((hW i).2 e).1 hei) (((hW j).2 e).1 hej)

end GraphMinor.GM02
