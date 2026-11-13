module

public import GraphMinor.GM02.MinorModelEnds

/-!
# Keeping only the branch trees and representing edges

In II (4.8), replace each branch of a minor model by a connected subgraph
that keeps its attachment vertices. Retain exactly these subgraphs and the
representing edges in the source graph. The resulting source is a subgraph
of the original graph and still models the target. No edge outside those
chosen subgraphs and representing edges is retained.
-/

public section

namespace GraphMinor.GM02

open Graph Set

universe u v u' v'

/-- Connected subgraphs of the branches that keep every representing-edge
end give a smaller source for the same minor model. Its vertex and edge
sets are exactly the unions specified in the conclusion. -/
theorem IsMinorModel.restrict_to_branch_subgraphs
    {α : Type u} {β : Type v} {α' : Type u'} {β' : Type v'}
    {G : Graph α β} {H : Graph α' β'} {ηv : α' → Set α} {ηe : β' → β}
    (hm : IsMinorModel H G ηv ηe) (K : α' → Graph α β)
    (hK : ∀ u ∈ V(H), K u ≤ G.deleteEdges (ηe '' E(H)))
    (hconn : ∀ u ∈ V(H), GraphConnected (K u))
    (hsub : ∀ u ∈ V(H), V(K u) ⊆ ηv u)
    (hkeep : ∀ u ∈ V(H), ∀ e ∈ E(H), ∀ x ∈ ηv u,
      G.Inc (ηe e) x → x ∈ V(K u)) :
    ∃ P ≤ G,
      IsMinorModel H P (fun u => V(K u)) ηe ∧
      V(P) = ⋃ u ∈ V(H), V(K u) ∧
      E(P) = ηe '' E(H) ∪ ⋃ u ∈ V(H), E(K u) := by
  classical
  let U := ⋃ u ∈ V(H), V(K u)
  let F := ηe '' E(H) ∪ ⋃ u ∈ V(H), E(K u)
  let P := (G.restrict F).induce U
  have hU : U ⊆ V(G) := by
    intro x hx
    obtain ⟨u, hu'⟩ := Set.mem_iUnion.1 hx
    obtain ⟨hu, hxu⟩ := Set.mem_iUnion.1 hu'
    exact hm.vertex_subset u hu (hsub u hu hxu)
  have hPG : P ≤ G := (Graph.induce_le (G := G.restrict F) hU).trans Graph.restrict_le
  have hU_mem : ∀ u ∈ V(H), ∀ x ∈ V(K u), x ∈ U := by
    intro u hu x hx
    exact Set.mem_iUnion.2 ⟨u, Set.mem_iUnion.2 ⟨hu, hx⟩⟩
  have hGend : ∀ e ∈ E(H), ∀ x, G.Inc (ηe e) x → x ∈ U := by
    intro e he x hx
    obtain ⟨u, hu, hxu⟩ := GraphMinor.GM02.IsMinorModel.edge_ends_covered hm he hx
    exact hU_mem u hu x (hkeep u hu e he x hxu hx)
  have hFlink : ∀ e ∈ F, ∃ a b, G.IsLink e a b ∧ a ∈ U ∧ b ∈ U := by
    intro e he
    rcases he with ⟨e', he', rfl⟩ | he
    · obtain ⟨a, b, hab⟩ := Graph.exists_isLink_of_mem_edgeSet (hm.edge_mem e' he')
      exact ⟨a, b, hab, hGend e' he' a hab.inc_left, hGend e' he' b hab.inc_right⟩
    · obtain ⟨u, hu⟩ := Set.mem_iUnion.1 he
      obtain ⟨hu, he⟩ := Set.mem_iUnion.1 hu
      obtain ⟨a, b, hab⟩ := Graph.exists_isLink_of_mem_edgeSet he
      exact ⟨a, b, (hK u hu).isLink_mono hab |>.1,
        hU_mem u hu a hab.left_mem, hU_mem u hu b hab.right_mem⟩
  have hPE : E(P) = F := by
    ext e
    constructor
    · intro he
      obtain ⟨a, b, hab⟩ := Graph.exists_isLink_of_mem_edgeSet he
      exact hab.1.1
    · intro he
      obtain ⟨a, b, hab, ha, hb⟩ := hFlink e he
      exact (show P.IsLink e a b from ⟨⟨he, hab⟩, ha, hb⟩).edge_mem
  have hrepr : ∀ e ∈ E(H), ηe e ∈ E(P) := by
    intro e he
    rw [hPE]
    exact Or.inl ⟨e, he, rfl⟩
  have hinc : ∀ e ∈ E(H), ∀ x, P.Inc (ηe e) x ↔ G.Inc (ηe e) x :=
    fun e he _ => hPG.inc_congr (hrepr e he)
  have hbranch : ∀ u ∈ V(H), K u ≤ P.deleteEdges (ηe '' E(H)) := by
    intro u hu
    constructor
    · exact hU_mem u hu
    · intro e a b hab
      have hKG := (hK u hu).isLink_mono hab
      have heF : e ∈ F := Or.inr
        (Set.mem_iUnion.2 ⟨u, Set.mem_iUnion.2 ⟨hu, hab.edge_mem⟩⟩)
      exact ⟨⟨⟨heF, hKG.1⟩, hU_mem u hu a hab.left_mem,
        hU_mem u hu b hab.right_mem⟩, hKG.2⟩
  refine ⟨P, hPG, ?_, rfl, hPE⟩
  refine ⟨?_, ?_, hrepr, ?_, hm.edge_injOn, ?_, ?_, ?_⟩
  · intro u hu
    exact (hconn u hu).1
  · intro u hu
    exact hU_mem u hu
  · intro a ha b hb hab
    exact (hm.vertex_disjoint a ha b hb hab).mono (hsub a ha) (hsub b hb)
  · intro u hu e he
    rw [hm.inc_iff u hu e he]
    constructor
    · rintro ⟨x, hx, hxe⟩
      exact ⟨x, hkeep u hu e he x hx hxe, (hinc e he x).2 hxe⟩
    · rintro ⟨x, hx, hxe⟩
      exact ⟨x, hsub u hu hx, (hinc e he x).1 hxe⟩
  · intro u hu e he
    rw [hm.isLoopAt_iff u hu e he]
    constructor
    · intro hall x hx
      have hxG := (hinc e he x).1 hx
      exact hkeep u hu e he x (hall x hxG) hxG
    · intro hall x hx
      exact hsub u hu (hall x ((hinc e he x).2 hx))
  · intro u hu
    exact ⟨K u, hbranch u hu, rfl, hconn u hu⟩

end GraphMinor.GM02
