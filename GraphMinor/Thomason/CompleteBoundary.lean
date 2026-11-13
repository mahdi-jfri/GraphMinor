module

public import GraphMinor.Thomason.CliqueMinorOfBranches
public import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Data.Fintype.EquivFin
import Lean.Elab.Tactic.Omega

/-!
# The complete-graph boundary of the surplus condition

Lemma 5 of Thomason (1984), p. 263, requires the surplus to be at most
three less than the order. If that condition fails but twice every
degree exceeds the order by the surplus, the graph is complete.
Singleton branches then provide every clique of at most its order.
-/

public section
namespace GraphMinor.Thomason
open SimpleGraph Finset
universe u

/-- A complete graph contains a clique minor of every order at most
its own, with singleton branches given by an explicit vertex injection. -/
theorem clique_isIsoMinor_of_complete {V : Type u} [Fintype V]
    (G : SimpleGraph V) (hc : ∀ u v, u ≠ v → G.Adj u v)
    (q : ℕ) (hq : q ≤ Fintype.card V) :
    IsIsoMinor (Graph.ofSimpleGraph (⊤ : SimpleGraph (Fin q))) (Graph.ofSimpleGraph G) := by
  classical
  let e : Fin q → V := fun i => (Fintype.equivFin V).symm (Fin.castLE hq i)
  have he : Function.Injective e :=
    (Fintype.equivFin V).symm.injective.comp (Fin.castLE_injective hq)
  apply clique_isIsoMinor_of_branches G (fun i => {e i})
  · intro i
    have heq : (({e i} : Finset V) : Set V) = {e i} := by ext x; simp
    rw [heq]
    exact (SimpleGraph.Subgraph.singletonSubgraph_connected (G := G) (v := e i)).induce_verts
  · intro i j hij
    exact Finset.disjoint_singleton.mpr (fun h => hij (he h))
  · intro i j hij
    exact ⟨e i, mem_singleton_self _, e j, mem_singleton_self _, hc _ _ (fun h => hij (he h))⟩

/-- If the degree surplus is too large for the order condition of
Thomason's Lemma 5, every vertex is universal. -/
theorem complete_of_large_degree_surplus {V : Type u} [Fintype V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (d : ℕ)
    (hN : Fintype.card V ≤ d + 2)
    (hdeg : ∀ v, Fintype.card V + d ≤ 2 * G.degree v) :
    ∀ u v, u ≠ v → G.Adj u v := by
  intro u v huv
  have hlt := G.degree_lt_card_verts u
  have hd := hdeg u
  have heq : G.degree u = Fintype.card V - 1 := by omega
  exact ((G.degree_eq_card_sub_one u).mp heq) huv

end GraphMinor.Thomason
