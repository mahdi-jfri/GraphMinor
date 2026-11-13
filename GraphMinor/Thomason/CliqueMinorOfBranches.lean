module
public import GraphMinor.Statement
public import Mathlib.Combinatorics.Graph.Simple
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Subgraph
import GraphMinor.GM01.Basic

/-!
# Clique minors from connected branches

Disjoint nonempty connected vertex sets with edges between every pair
form a clique-minor model. We use the connected-subgraph construction
of the minor witness, retaining explicit adjacent endpoints.
-/

public section
namespace GraphMinor.Thomason
open SimpleGraph Finset
universe u
variable {V : Type u} [Fintype V]
variable (G : SimpleGraph V)

/-- Connected disjoint branch sets with pairwise adjacent endpoints give
a complete-graph minor. This is the contraction step at the end of the
branch construction in Thomason (1984), p. 264. -/
theorem clique_isIsoMinor_of_branches {q : ℕ} (T : Fin q → Finset V)
    (hconn : ∀ i, (G.induce (T i : Set V)).Connected)
    (hdis : Pairwise fun i j => Disjoint (T i) (T j))
    (hadj : ∀ i j, i ≠ j → ∃ v ∈ T i, ∃ w ∈ T j, G.Adj v w) :
    IsIsoMinor (Graph.ofSimpleGraph (⊤ : SimpleGraph (Fin q))) (Graph.ofSimpleGraph G) := by
  let Γ := SimpleGraph.toSubgraph G le_top
  let K : Fin q → (⊤ : SimpleGraph V).Subgraph := fun i => Γ.induce (T i : Set V)
  rw [GM01.ofSimpleGraph_eq_toGraph G]
  apply GM01.isIsoMinor_ofSimpleGraph_of_connected_subgraphs ⊤ (Set.toFinite Γ.verts) K
  · intro i
    exact ⟨fun _ _ => trivial, fun _ _ h => h.2.2⟩
  · intro i
    let f : (G.induce (T i : Set V)) →g (K i).coe :=
      { toFun := id
        map_rel' := fun {x y} h => ⟨x.property, y.property, h⟩ }
    exact SimpleGraph.Subgraph.Connected.mk ((hconn i).map f Function.surjective_id)
  · intro i j hij
    exact Set.disjoint_left.mpr (fun v hv hw => (Finset.disjoint_left.mp (hdis hij)) hv hw)
  · intro i j hij
    exact hadj i j hij

end GraphMinor.Thomason
