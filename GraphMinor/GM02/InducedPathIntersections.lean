module

public import GraphMinor.GM02.InducedTerminatedGraphs
public import GraphMinor.GM02.FeasiblePathSupport

/-!
# Intersections of the two induced path families

For the corrected version of II (2.9), both induced graphs are subgraphs
of the original graph. Their common vertices are common termination
endpoints. A feasible family can use such an endpoint only on its own
pair's path. Thus paths from opposite sides meet only at endpoints shared
by their two pairs, as needed to join the pieces along a crossing scheme.
-/

public section
namespace GraphMinor.GM02
open Graph Set Classical
universe u v

/-- The first corrected induced graph is a subgraph of the original graph. -/
theorem CrossingScheme.inducedLeft_le {α : Type u} {β : Type v}
    {G H H' : Graph α β} {A₀ : Termination V(G)} (C : CrossingScheme G H H' A₀)
    (hsep : IsSeparation G H H') : C.inducedLeft ≤ G :=
  Graph.deleteVerts_le.trans hsep.1

/-- The second corrected induced graph is a subgraph of the original graph. -/
theorem CrossingScheme.inducedRight_le {α : Type u} {β : Type v}
    {G H H' : Graph α β} {A₀ : Termination V(G)} (C : CrossingScheme G H H' A₀)
    (hsep : IsSeparation G H H') : C.inducedRight ≤ G :=
  Graph.deleteVerts_le.trans hsep.2.1

/-- Paths in the two feasible induced families can meet only at endpoints
shared by their prescribed pairs. -/
theorem CrossingScheme.induced_paths_inter_subset {α : Type u} {β : Type v}
    {G H H' : Graph α β} {A₀ : Termination V(G)} (C : CrossingScheme G H H' A₀)
    (P : ∀ p : {p // p ∈ C.left.pairs}, PairPath (pathGraph C.inducedLeft) p.val)
    (Q : ∀ q : {q // q ∈ C.right.pairs}, PairPath (pathGraph C.inducedRight) q.val)
    (hP : ∀ p q, p ≠ q → Disjoint (P p).vertices (P q).vertices)
    (hQ : ∀ p q, p ≠ q → Disjoint (Q p).vertices (Q q).vertices)
    (p : {p // p ∈ C.left.pairs}) (q : {q // q ∈ C.right.pairs}) :
    (P p).vertices ∩ (Q q).vertices ⊆ {a | a ∈ p.val ∧ a ∈ q.val} := by
  intro a ha
  have haL := (P p).vertices_subset (C.left.not_diag p.val p.property) ha.1
  have haR := (Q q).vertices_subset (C.right.not_diag q.val q.property) ha.2
  have haBoth : a ∈ C.left.support ∩ C.right.support := by
    rw [← C.induced_vertex_inter]
    exact ⟨haL, haR⟩
  exact ⟨mem_pair_of_mem_support_of_mem_family C.left P hP ha.1 haBoth.1,
    mem_pair_of_mem_support_of_mem_family C.right Q hQ ha.2 haBoth.2⟩

end GraphMinor.GM02
