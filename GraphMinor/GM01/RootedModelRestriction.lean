module

public import GraphMinor.GM01.RootedModelSets

/-!
# Restricting a rooted model to a selected source support

In Graph Minors I, (5.2), page 61, the disjoint sets packed in the
fork are transferred to its model in the component. Restrict the
source to one selected vertex set and the target to the union of
its model branches. All represented edges and all branch paths
remain inside these induced graphs. Any chosen vertex of a chosen
root branch can be distinguished as target root.
-/

public section

namespace GraphMinor.GM01

open Set Graph Function

/-- Restrict a model to an induced source support and its lifted target
support, retaining the actual branches and represented edges for the
packing in GM01 (5.2), page 61. -/
noncomputable def RootedMinorModel.restrictSource {α β γ δ : Type*}
    {H : RootedGraph α β} {G : RootedGraph γ δ} (M : RootedMinorModel H G)
    (S : Set α) (hS : S ⊆ V(H.graph)) (r : V(H.graph.induce S))
    (x : V(G.graph.induce (M.liftSet S)))
    (hx : x.val ∈ M.branch ⟨r.val,hS r.property⟩) :
    RootedMinorModel (⟨H.graph.induce S,r⟩ : RootedGraph α β)
      (⟨G.graph.induce (M.liftSet S),x⟩ : RootedGraph γ δ) := by
  let sourceVertex : V(H.graph.induce S) → V(H.graph) := fun v ↦ ⟨v.val,hS v.property⟩
  have hVertexInjective : Injective sourceVertex := fun _ _ h ↦ Subtype.ext (congrArg (fun v : V(H.graph) ↦ v.val) h)
  have hSH := H.graph.induce_le hS
  let sourceEdge : E(H.graph.induce S) ↪ E(H.graph) :=
    ⟨fun e ↦ ⟨e.val,hSH.edgeSet_mono e.property⟩,
      fun _ _ h ↦ Subtype.ext (congrArg (fun e : E(H.graph) ↦ e.val) h)⟩
  have hLift : ∀ v : V(H.graph.induce S), M.branch (sourceVertex v) ⊆ M.liftSet S := by
    intro v y hy
    exact (M.mem_liftSet_iff S y).mpr ⟨sourceVertex v,v.property,hy⟩
  have hEdgeMem : ∀ e : E(H.graph.induce S),
      (M.edgeMap (sourceEdge e)).val ∈ E(G.graph.induce (M.liftSet S)) := by
    intro e
    obtain ⟨a,b,he⟩ := (H.graph.induce S).exists_isLink_of_mem_edgeSet e.property
    let a' : V(H.graph.induce S) := ⟨a,he.left_mem⟩
    let b' : V(H.graph.induce S) := ⟨b,he.right_mem⟩
    obtain ⟨p,hp,q,hq,hpq⟩ := M.edge_links (sourceEdge e) (sourceVertex a') (sourceVertex b') he.1
    exact (show (G.graph.induce (M.liftSet S)).IsLink (M.edgeMap (sourceEdge e)).val p q from
      ⟨hpq,hLift a' hp,hLift b' hq⟩).edge_mem
  let targetEdge : E(H.graph.induce S) ↪ E(G.graph.induce (M.liftSet S)) :=
    ⟨fun e ↦ ⟨(M.edgeMap (sourceEdge e)).val,hEdgeMem e⟩, by
      intro e f hef
      apply sourceEdge.injective
      apply M.edgeMap.injective
      exact Subtype.ext (congrArg (fun e : E(G.graph.induce (M.liftSet S)) ↦ e.val) hef)⟩
  refine {
    branch := fun v ↦ M.branch (sourceVertex v)
    branch_subset := hLift
    branch_disjoint := fun _ _ hne ↦ M.branch_disjoint (hVertexInjective.ne hne)
    branch_connected := ?_
    edgeMap := targetEdge
    edge_links := ?_
    root_mem := hx }
  · intro v
    refine ⟨(M.branch_connected (sourceVertex v)).1,?_⟩
    intro a ha b hb
    apply Relation.ReflTransGen.mono ?_ a b ((M.branch_connected (sourceVertex v)).2 a ha b hb)
    intro p q hpq
    obtain ⟨e,he⟩ := hpq
    exact ⟨e,⟨he.1,hLift v he.2.1,hLift v he.2.2⟩,he.2.1,he.2.2⟩
  · intro e a b he
    obtain ⟨p,hp,q,hq,hpq⟩ := M.edge_links (sourceEdge e) (sourceVertex a) (sourceVertex b) he.1
    exact ⟨p,hp,q,hq,hpq,hLift a hp,hLift b hq⟩

end GraphMinor.GM01
