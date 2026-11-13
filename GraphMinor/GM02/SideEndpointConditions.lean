module

public import GraphMinor.GM02.SidePairPathUnion
public import GraphMinor.GM02.SidePiecePairInjective
public import GraphMinor.GM02.SideTerminationFeasible
public import GraphMinor.GM02.PairUnionLocation
import GraphMinor.GM02.FeasiblePathSupport

/-!
# Endpoint conditions for the extracted crossing scheme

The graph of contracted pieces is the union of the two termination
matchings. Its disjoint paths give parity by counting degrees. The paths
on each side stay in that side's graph, so outside the separator their
endpoints are exactly the original terminals on that side.
-/

public section
namespace GraphMinor.GM02
open Graph SimpleGraph Set Classical
universe u v
variable {α : Type u} {β : Type v} {S : Set α} (A : Termination S) (G H : Graph α β)
variable (P : ∀ p : {p // p ∈ A.pairs}, PairPath (pathGraph G) p.val)
variable (hP : ∀ p q, p ≠ q → Disjoint (P p).vertices (P q).vertices)

/-- Feasibility forces every termination endpoint to belong to the graph. -/
theorem Termination.Feasible.support_subset {T : Set α} {B : Termination T}
    {K : Graph α β} (hB : B.Feasible K) : B.support ⊆ V(K) := by
  obtain ⟨Q, _⟩ := hB
  intro a ha
  obtain ⟨p, hp⟩ := Set.mem_iUnion.1 ha
  obtain ⟨hp, hap⟩ := Set.mem_iUnion.1 hp
  exact (Q ⟨p, hp⟩).vertices_subset (B.not_diag p hp) ((Q ⟨p, hp⟩).endpoint_mem hap)

/-- The contracted graph is the union of the two side matchings. -/
theorem sidePairGraph_eq_sup : sidePairGraph A G H P hP =
    (sideTermination A G H P hP true).pairGraph ⊔
      (sideTermination A G H P hP false).pairGraph := by
  ext a b
  simp only [sidePairGraph, SimpleGraph.fromEdgeSet_adj, Finset.mem_coe,
    Finset.mem_union, SimpleGraph.sup_adj]
  tauto

/-- The contracted paths may be viewed in the union of the side matchings. -/
theorem sideTermination_isPairPathUnion : IsPairPathUnion A
    ((sideTermination A G H P hP true).pairGraph ⊔
      (sideTermination A G H P hP false).pairGraph)
    ((sideTermination A G H P hP true).support ∪
      (sideTermination A G H P hP false).support) := by
  rw [← sidePairGraph_eq_sup A G H P hP]
  exact sidePairGraph_isPairPathUnion A G H P hP

/-- The original and two side terminations have even endpoint multiplicity. -/
theorem sideTermination_even_support (a : α) :
    Even ((if a ∈ A.support then 1 else 0) +
      (if a ∈ (sideTermination A G H P hP true).support then 1 else 0) +
      (if a ∈ (sideTermination A G H P hP false).support then 1 else 0)) :=
  @IsPairPathUnion.even_support α S (V(G)) (V(G)) A
    (sideTermination A G H P hP true) (sideTermination A G H P hP false)
    (sideTermination_isPairPathUnion A G H P hP)
    (sideTermination_pairs_disjoint A G H P hP) a

/-- Outside the separator, the first side's endpoints are exactly its original terminals. -/
theorem sideTermination_left_support {H' : Graph α β} (hsep : IsSeparation G H H') :
    (sideTermination A G H P hP true).support \ (V(H) ∩ V(H')) =
      A.support ∩ (V(H) \ V(H')) :=
  @IsPairPathUnion.support_diff_inter α S (V(G)) (V(G)) (V(H)) (V(H')) A
    (sideTermination A G H P hP true) (sideTermination A G H P hP false)
    (sideTermination_isPairPathUnion A G H P hP)
    (sideTermination_pairs_disjoint A G H P hP)
    (sideTermination_left_feasible A G H P hP).support_subset
    (sideTermination_right_feasible A G H P hP hsep).support_subset

/-- Outside the separator, the second side's endpoints are exactly its original terminals. -/
theorem sideTermination_right_support {H' : Graph α β} (hsep : IsSeparation G H H') :
    (sideTermination A G H P hP false).support \ (V(H) ∩ V(H')) =
      A.support ∩ (V(H') \ V(H)) := by
  have hU := sideTermination_isPairPathUnion A G H P hP
  have hswap : IsPairPathUnion A
      ((sideTermination A G H P hP false).pairGraph ⊔
        (sideTermination A G H P hP true).pairGraph)
      ((sideTermination A G H P hP false).support ∪
        (sideTermination A G H P hP true).support) := by
    rw [sup_comm, Set.union_comm]
    exact hU
  have he := @IsPairPathUnion.support_diff_inter α S (V(G)) (V(G)) (V(H')) (V(H)) A
    (sideTermination A G H P hP false) (sideTermination A G H P hP true)
    hswap (sideTermination_pairs_disjoint A G H P hP).symm
    (sideTermination_right_feasible A G H P hP hsep).support_subset
    (sideTermination_left_feasible A G H P hP).support_subset
  rw [Set.inter_comm (V(H')) (V(H))] at he
  exact he

end GraphMinor.GM02
