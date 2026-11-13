module

public import GraphMinor.GM01.ForestCombMinor
public import GraphMinor.GM01.CombMinorModels
import GraphMinor.GM01.Basic
import GraphMinor.GM01.SubgraphIso

/-!
# From forest exclusion to rooted comb exclusion

The proof of Graph Minors I, (3.1), page 54, applies the rooted bound to
a graph excluding `Y_ℓ`. A rooted comb model gives an ordinary comb minor,
and the spine contraction gives the forbidden forest minor. Thus the
rooted exclusion follows from the original exclusion, with no added
model hypothesis in the final implication.
-/

public section

namespace GraphMinor.GM01

open Set Graph SimpleGraph

universe u v

/-- A rooted comb model in a finite graph supplies an ordinary minor of
that graph. The ordinary model is obtained from (M1)–(M3); the root
condition need not be used for this conclusion. -/
theorem RootedMinorModel.pathComb_isIsoMinor {γ δ : ℕ} (hδ : 2 ≤ δ)
    {α : Type u} {β : Type v} (G : RootedGraph α β)
    (hV : V(G.graph).Finite) (hE : E(G.graph).Finite)
    (M : RootedMinorModel (rootedPathComb γ δ (by omega)) G) :
    IsIsoMinor (toGraph (pathComb γ δ)) G.graph := by
  let : Finite (pathComb γ δ).verts := (pathComb_vertices_finite γ δ).to_subtype
  obtain ⟨ηv, ηe, hModel, _⟩ := M.pathComb_minor_model hδ G
  have hminor := isIsoMinor_of_isMinorModel
    (Graph.ofSimpleGraph (pathComb γ δ).coe) G.graph
    (by exact Set.finite_univ) (Set.toFinite _) hV hE ηv ηe hModel
  exact (subgraphSimpleGraphIso (pathComb γ δ)).symm.isIsoMinor_left hminor

/-- The rooted exclusion implication used in the proof of Graph Minors I,
(3.1), page 54. A hypothetical rooted comb model would give the excluded
forest minor by contraction of its spine. -/
theorem not_rootedPathComb_of_not_forestTree {α : Type u} {β : Type v}
    (G : RootedGraph α β) (hV : V(G.graph).Finite) (hE : E(G.graph).Finite)
    (ℓ : ℕ) (hno : ¬ IsIsoMinor (forestTreeGraph ℓ) G.graph) :
    ¬ HasRootedMinor (rootedPathComb ℓ 3 (by decide)) G := by
  rintro ⟨M⟩
  exact hno ((forestTree_isIsoMinor_pathComb ℓ).trans
    (M.pathComb_isIsoMinor (by decide) G hV hE))

end GraphMinor.GM01
