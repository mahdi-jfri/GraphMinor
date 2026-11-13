module

public import GraphMinor.GM02.EdgeRouteTraces
import GraphMinor.GM02.Section4Suppression
import GraphMinor.GM11.Walks

/-!
# Host routes of a topologically contained pattern

Use the edge-labelled traces of the suppression sequence. The final
isomorphism identifies each pattern edge with one of the final edges
and fixes its endpoints. Orient that trace by the prescribed pattern
endpoints, then transfer it from the witnessing subgraph to the host.
The edge bijection preserves disjointness between different routes.
-/

public section
namespace GraphMinor.GM02
open Graph Set Classical Surface
universe u v

/-- Topological containment supplies edge-disjoint host routes with disjoint non-branch interiors. -/
theorem exists_edgeRoutes_of_topologicallyContains {α : Type u} {β : Type v} {k : ℕ}
    (G H : Graph α β) (edge : Fin k ≃ E(H)) (ends : Fin k → α × α)
    (hH : ∀ i, H.IsLink (edge i).val (ends i).1 (ends i).2)
    (hTopo : TopologicallyContains G H) :
    ∃ (inner : Fin k → List α) (W : ∀ i, GraphWalk G (ends i).1 (ends i).2),
      (∀ i, (W i).support = (ends i).1 :: (inner i ++ [(ends i).2]) ∧
        (inner i).Nodup ∧ (∀ y ∈ inner i, y ∈ V(G) \ V(H)) ∧
        (W i).edges.Nodup ∧ (W i).edges ≠ []) ∧
      ∀ i j, i ≠ j →
        Disjoint {y | y ∈ inner i} {y | y ∈ inner j} ∧
        Disjoint {e | e ∈ (W i).edges} {e | e ∈ (W j).edges} := by
  obtain ⟨K, hKG, L, hKL, σ, hVL, hσ, hLinks⟩ := topologicallyContains_iff_isoFix.1 hTopo
  obtain ⟨R, hR, hDis⟩ := exists_edgeRoute_traces hKL
  let fL : Fin k → E(L) := fun i => ⟨σ (edge i).val, hσ.mapsTo (edge i).property⟩
  have hfL : Function.Injective fL := by
    intro i j hij
    have heq : (edge i).val = (edge j).val :=
      hσ.injOn (edge i).property (edge j).property (congrArg Subtype.val hij)
    exact edge.injective (Subtype.ext heq)
  have hex : ∀ i, ∃ (inner : List α) (W : GraphWalk G (ends i).1 (ends i).2),
      W.support = (ends i).1 :: (inner ++ [(ends i).2]) ∧ inner.Nodup ∧
      (∀ y ∈ inner, y ∈ V(G) \ V(H)) ∧ W.edges.Nodup ∧ W.edges ≠ [] ∧
      (∀ y, y ∈ inner ↔ y ∈ (R (fL i)).inner) ∧
      (∀ e, e ∈ W.edges ↔ e ∈ (R (fL i)).walk.edges) := by
    intro i
    have hl : L.IsLink (fL i).val (ends i).1 (ends i).2 :=
      (hLinks (edge i).val (edge i).property _ _).1 (hH i)
    obtain ⟨inner, WK, hs, hn, ho, heN, heNon, hmV, hmE⟩ :=
      exists_oriented_edgeRoute_properties (hR (fL i)).1 hl
        (R (fL i)).inner (R (fL i)).walk (V(K) \ V(L))
        (hR (fL i)).2.1 (hR (fL i)).2.2.1 (hR (fL i)).2.2.2.1
        (hR (fL i)).2.2.2.2.1 (hR (fL i)).2.2.2.2.2
    obtain ⟨WG, hsG, heG⟩ := WK.exists_transfer
      (fun _ _ _ _ hab => hKG.isLink_mono hab)
      (fun _ hy => hKG.vertexSet_mono (WK.mem_vertexSet_of_mem_support hy))
    refine ⟨inner, WG, hsG.trans hs, hn, ?_, heG.symm ▸ heN, heG.symm ▸ heNon, hmV, ?_⟩
    · intro y hy
      refine ⟨hKG.vertexSet_mono (ho y hy).1, ?_⟩
      rw [hVL]
      exact (ho y hy).2
    · intro e
      rw [heG]
      exact hmE e
  choose inner W hW using hex
  refine ⟨inner, W, ?_, ?_⟩
  · intro i
    exact ⟨(hW i).1, (hW i).2.1, (hW i).2.2.1, (hW i).2.2.2.1, (hW i).2.2.2.2.1⟩
  · intro i j hij
    have hd := hDis (fL i) (fL j) (fun h => hij (hfL h))
    constructor
    · rw [Set.disjoint_left]
      intro y hyi hyj
      exact Set.disjoint_left.1 hd.1 (((hW i).2.2.2.2.2.1 y).1 hyi) (((hW j).2.2.2.2.2.1 y).1 hyj)
    · rw [Set.disjoint_left]
      intro e hei hej
      exact Set.disjoint_left.1 hd.2 (((hW i).2.2.2.2.2.2 e).1 hei) (((hW j).2.2.2.2.2.2 e).1 hej)

end GraphMinor.GM02
