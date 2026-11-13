module

public import GraphMinor.GM05.BranchEdgeModel
public import GraphMinor.Surface.Defs
import GraphMinor.GM16.DrawingGraphPaths
import GraphMinor.GM11.Walks

/-!
# The model supplied by the star subdrawings

For GM V, (8.14), the connected branch drawings lie in the star
drawing. The chosen middle edges are outside its edge set. Thus
each branch graph is a subgraph of the host with all representing
edges deleted. Apply the branch-and-edge model construction.
-/

public section
namespace GraphMinor.GM05
open Set Surface Graph

/-- The abstract minor model from the connected star subdrawings
and the single middle edges in GM V, (8.14), page 113. -/
theorem exists_minor_model_of_branch_subdrawings {S : Type*} [TopologicalSpace S]
    (D T H : Drawing S) (u v : D.E → S)
    (hsrc : ∀ e, D.toGraph.IsLink e.val (u e) (v e)) (hne : ∀ e, u e ≠ v e)
    (K : D.V → Drawing S) (hKT : ∀ w, (K w).IsSubdrawing T) (hTH : T.IsSubdrawing H)
    (hc : ∀ w, GraphConnected (K w).toGraph)
    (hdis : Pairwise (fun w z ↦ Disjoint (K w).V (K z).V))
    (ε : D.E → Set S) (hε : Function.Injective ε) (p q : D.E → S)
    (hl : ∀ e, H.toGraph.IsLink (ε e) (p e) (q e))
    (hp : ∀ e, p e ∈ (K ⟨u e,(hsrc e).left_mem⟩).V)
    (hq : ∀ e, q e ∈ (K ⟨v e,(hsrc e).right_mem⟩).V)
    (havoid : Disjoint T.E (range ε)) :
    ∃ ηv ηe, IsMinorModel D.toGraph H.toGraph ηv ηe ∧
      (∀ w (hw : w ∈ D.V), ηv w = (K ⟨w,hw⟩).V) ∧
      ∀ e (he : e ∈ D.E), ηe e = ε ⟨e,he⟩ := by
  have hKdelete : ∀ w, (K w).toGraph ≤ H.toGraph.deleteEdges (range ε) := by
    intro w
    have hKG := GM16.toGraph_le_of_isSubdrawing ((hKT w).trans hTH)
    refine ⟨hKG.vertexSet_mono,?_⟩
    intro e x y he
    refine ⟨hKG.isLink_mono he,?_⟩
    intro herange
    exact disjoint_left.mp havoid ((hKT w).2 he.edge_mem) herange
  exact exists_minor_model_of_branches_and_edges D.toGraph H.toGraph
    (fun e ↦ ⟨u e,(hsrc e).left_mem⟩) (fun e ↦ ⟨v e,(hsrc e).right_mem⟩) hsrc
    (fun e he ↦ hne e (congrArg Subtype.val he)) (fun w ↦ (K w).toGraph)
    ε p q hKdelete hc hdis hε hl hp hq

end GraphMinor.GM05
