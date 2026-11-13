module

public import GraphMinor.GM02.EdgeRouteInduction
import GraphMinor.GM11.Walks

/-!
# Topological containment from disjoint edge-labelled routes

Take the union of the route edges and all pattern vertices. Its vertex
set consists of the pattern vertices and the route interiors. Transfer
the walks to this subgraph and apply the suppression induction. Isolated
pattern vertices are retained even when there are no route edges.
-/

public section
namespace GraphMinor.GM02
open Graph Set Classical Surface Relation
universe u v

/-- Disjoint host routes for all pattern edges certify topological containment. -/
theorem topologicallyContains_of_edgeRoutes {α : Type u} {β : Type v} {k : ℕ}
    (G H : Graph α β) (hV : V(G).Finite) (hVH : V(H) ⊆ V(G))
    (edge : Fin k ≃ E(H)) (ends : Fin k → α × α)
    (hH : ∀ i, H.IsLink (edge i).val (ends i).1 (ends i).2)
    (inner : Fin k → List α) (W : ∀ i, GraphWalk G (ends i).1 (ends i).2)
    (hs : ∀ i, (W i).support = (ends i).1 :: (inner i ++ [(ends i).2]))
    (hn : ∀ i, (inner i).Nodup)
    (hinner : ∀ i y, y ∈ inner i → y ∈ V(G) \ V(H))
    (hdis : ∀ i j, i ≠ j → Disjoint {y | y ∈ inner i} {y | y ∈ inner j})
    (heN : ∀ i, (W i).edges.Nodup) (heNon : ∀ i, (W i).edges ≠ [])
    (heDis : ∀ i j, i ≠ j → Disjoint {e | e ∈ (W i).edges} {e | e ∈ (W j).edges}) :
    TopologicallyContains G H := by
  let X : Set α := V(H) ∪ {y | ∃ i, y ∈ inner i}
  let E₀ : Set β := {e | ∃ i, e ∈ (W i).edges}
  let K := (G.restrict E₀).induce X
  have hX : X ⊆ V(G) := by
    rintro y (hy | ⟨i, hi⟩)
    · exact hVH hy
    · exact (hinner i y hi).1
  have hKG : K ≤ G := ((G.restrict E₀).induce_le hX).trans Graph.restrict_le
  have hsupport : ∀ i y, y ∈ (W i).support → y ∈ X := by
    intro i y hy
    rw [hs i] at hy
    simp only [List.mem_cons, List.mem_append, List.not_mem_nil, or_false] at hy
    rcases hy with hy | hy | hy
    · exact Or.inl (hy ▸ (hH i).left_mem)
    · exact Or.inr ⟨i, hy⟩
    · exact Or.inl (hy ▸ (hH i).right_mem)
  have htransfer : ∀ i, ∃ w : GraphWalk K (ends i).1 (ends i).2,
      w.support = (W i).support ∧ w.edges = (W i).edges := by
    intro i
    apply (W i).exists_transfer
    · intro e a b he hab
      exact ⟨⟨⟨i, he⟩, hab⟩,
        hsupport i a ((W i).left_mem_support_of_mem_edges he hab),
        hsupport i b ((W i).left_mem_support_of_mem_edges he hab.symm)⟩
    · exact hsupport i
  choose WK hKS hKE using htransfer
  have hsK : ∀ i, (WK i).support = (ends i).1 :: (inner i ++ [(ends i).2]) :=
    fun i => (hKS i).trans (hs i)
  have heNK : ∀ i, (WK i).edges.Nodup := fun i => (hKE i).symm ▸ heN i
  have heNonK : ∀ i, (WK i).edges ≠ [] := fun i => (hKE i).symm ▸ heNon i
  have heDisK : ∀ i j, i ≠ j → Disjoint {e | e ∈ (WK i).edges} {e | e ∈ (WK j).edges} := by
    intro i j hij
    simpa only [hKE] using heDis i j hij
  have hVHK : V(H) ⊆ V(K) := fun _ hy => Or.inl hy
  have hVC : ∀ y ∈ V(K), y ∈ V(H) ∨ ∃ i, y ∈ inner i := fun _ hy => hy
  have hEC : ∀ e ∈ E(K), ∃ i, e ∈ (WK i).edges := by
    intro e he
    obtain ⟨a, b, hab⟩ := K.exists_isLink_of_mem_edgeSet he
    have he₀ : e ∈ E₀ := hab.1.1
    obtain ⟨i, hi⟩ := he₀
    exact ⟨i, (hKE i).symm ▸ hi⟩
  obtain ⟨L, hL, hIso⟩ := edgeRoutes_suppress K H edge ends hH inner WK hsK hn
    (fun i y hy => (hinner i y hy).2) hdis heNK heNonK heDisK hVHK hVC hEC
      ((hV.subset hKG.vertexSet_mono).sdiff)
  exact topologicallyContains_iff_isoFix.2 ⟨K, hKG, L, hL, hIso⟩

end GraphMinor.GM02
