module

public import GraphMinor.GM01.ForestTrees
public import GraphMinor.GM01.ForestGraphs
import GraphMinor.GM01.Basic

/-!
# The branching trees are forests over the multigraph definitions

Graph Minors I uses the trees `Y` as the forests in the reformulation
(1.2). Their unordered-pair edge labels give simplicity. The identity
map on their vertex subtype sends the underlying simple graph to
the word-labelled tree, whose acyclicity was proved by parent steps.
-/

public section

namespace GraphMinor.GM01

/-- The trees used in observation (b) on page 40 are forests under the
same multigraph definition as the statement of GM01 (1.1). -/
theorem forestTreeGraph_isForest (lam : ℕ) : IsForest (forestTreeGraph lam) := by
  refine ⟨?_, ?_⟩
  · exact
      { not_isLoopAt := not_isLoopAt_toGraph (forestTree lam)
        eq_of_isLink := fun _ _ _ _ he hf ↦ he.1.trans hf.1.symm }
  · let f : (forestTreeGraph lam).toSimpleGraph →g (forestTree lam).coe :=
      { toFun := fun x ↦ x
        map_rel' := fun h ↦ (adj_toGraph (forestTree lam) _ _).mp h.2 }
    exact (forestTree_isAcyclic lam).comap f Function.injective_id

end GraphMinor.GM01
