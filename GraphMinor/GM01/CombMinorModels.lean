module

public import GraphMinor.GM01.CombDegree
public import GraphMinor.GM01.RootedModelMinor
import GraphMinor.GM01.RootedEmbeddings
import GraphMinor.GM01.Basic

/-!
# Ordinary models of the rooted comb configurations

The positive-height proof used for Graph Minors I, (1.1), starts with a
rooted model of a long `P(γ,δ)` configuration and extracts a subdivision.
We construct the ordinary model needed for that extraction while keeping
the target root inside the branch of the comb root. When `δ ≥ 2`, a spine
edge supplies a target edge label, so there is no extra nonemptiness
assumption on the target label type.
-/

public section

namespace GraphMinor.GM01

open Graph SimpleGraph

universe u v

/-- The represented first spine edge supplies an actual target edge label. -/
theorem RootedMinorModel.pathComb_nonempty_edge_labels {γ δ : ℕ} (hδ : 2 ≤ δ)
    {α : Type u} {β : Type v} (G : RootedGraph α β)
    (M : RootedMinorModel (rootedPathComb γ δ (by omega)) G) : Nonempty β := by
  let a : PathCombVertex δ := Sum.inl ⟨0, by omega⟩
  let b : PathCombVertex δ := Sum.inl ⟨1, by omega⟩
  have hab : (pathComb γ δ).Adj a b := pathComb_spine_adj
    (pathGraph_adj.mpr (Or.inl rfl))
  let edge : E(toGraph (pathComb γ δ)) := ⟨s(a, b), hab⟩
  exact ⟨(M.edgeMap edge).val⟩

/-- Forget the root of a long comb model without losing the root's branch.
The root condition is derived from (M4), and the ordinary model is
constructed from the printed rooted-model conditions. -/
theorem RootedMinorModel.pathComb_minor_model {γ δ : ℕ} (hδ : 2 ≤ δ)
    {α : Type u} {β : Type v} (G : RootedGraph α β)
    (M : RootedMinorModel (rootedPathComb γ δ (by omega)) G) :
    ∃ (ηv : (pathComb γ δ).verts → Set α)
      (ηe : Sym2 (pathComb γ δ).verts → β),
      IsMinorModel (Graph.ofSimpleGraph (pathComb γ δ).coe) G.graph ηv ηe ∧
      G.root.val ∈ ηv (rootedPathComb γ δ (by omega)).root := by
  let : Nonempty β := M.pathComb_nonempty_edge_labels hδ G
  let root : (pathComb γ δ).verts := (rootedPathComb γ δ (by omega)).root
  let M' : RootedMinorModel
      (⟨Graph.ofSimpleGraph (pathComb γ δ).coe, ⟨root, Set.mem_univ _⟩⟩ :
        RootedGraph (pathComb γ δ).verts (Sym2 (pathComb γ δ).verts)) G :=
    M.comapSource (subgraphSimpleGraphIso (pathComb γ δ)) rfl
  obtain ⟨ηv, ηe, hbranches, _, hm⟩ :=
    M'.exists_isMinorModel_of_simple_with_branches (pathComb γ δ).coe root G
  refine ⟨ηv, ηe, hm, ?_⟩
  rw [hbranches root]
  exact M'.root_mem

end GraphMinor.GM01
