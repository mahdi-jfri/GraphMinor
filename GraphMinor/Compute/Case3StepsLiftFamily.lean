module

public import GraphMinor.Compute.Case3StepsLoopOwner

/-!
# Edge coverage and disjointness of lifted members

The division conditions of Graph Minors XIII, Section 8, pages 95--96, say that
the members cover the graph and have disjoint edge sets. Restoring every copy
of a simple edge preserves these two properties. A loop is covered by its
chosen owner and cannot belong to two members.
-/

@[expose] public section

namespace GraphMinor.Compute

open Graph Classical
open scoped Sym2

/-- Every edge of the multigraph belongs to a lifted member of the simple
division. Loops use the chosen owner and non-loops use simple edge coverage. -/
theorem case3LiftFamily_edge_covered {n : ℕ} (D : MultiDigraph n)
    (omega : List (Fin n)) (homega : omega.Nodup)
    (F : Set (Alg86Subgraph D.toSimpleGraph))
    (hdiv : GM13.IsSocietyDivision (case3SimpleSocietyInput D omega homega).toSociety
      (Alg86Subgraph.toGMGraph '' F))
    {e : ℕ × ℕ × ℕ} (he : e ∈ E(D.toGMDigraph.toGraph))
    (assignment : Case3LoopAssignment (case3SimpleSocietyInput D omega homega) F :=
      case3DefaultLoopAssignment (case3SimpleSocietyInput D omega homega) F hdiv) :
    ∃ A ∈ F, e ∈ E(case3LiftMember D A
      (case3AssignedLoops assignment A)) := by
  let x := case3SimpleSocietyInput D omega homega
  have hu : e.1 < n := he.choose
  have hv : e.2.1 < n := he.choose_spec.choose
  let u : Fin n := ⟨e.1, hu⟩
  let v : Fin n := ⟨e.2.1, hv⟩
  have hk : e.2.2 < D.edgeMult u v := he.choose_spec.choose_spec
  by_cases huv : u = v
  · let A := (assignment.member u).1
    have hA : A ∈ F ∧ u ∈ A.verts := ⟨(assignment.member u).2, assignment.contains_vertex u⟩
    refine ⟨A, hA.1, ?_⟩
    rw [case3LiftMember_edgeSet]
    apply (case3MemberMultiDigraph_mem_edgeSet D A (case3AssignedLoops assignment A) u v e.2.2).mpr
    exact ⟨hk, Or.inr ⟨huv, (mem_case3AssignedLoops assignment A u).mpr rfl, hA.2⟩⟩
  · have hadj : D.toSimpleGraph.Adj u v :=
      (MultiDigraph.toSimpleGraph_adj D u v).mpr ⟨huv, Or.inl (Nat.zero_lt_of_lt hk)⟩
    have hs : s(u, v) ∈ E(x.toSociety.G) := by
      rw [Alg81Input.toSociety_G]
      exact D.toSimpleGraph.mem_edgeSet.mpr hadj
    rw [← hdiv.sUnion_eq, GM09.edgeSet_subgraphSUnion
      (fun _ h => hdiv.sub_of_mem h)] at hs
    obtain ⟨B, hB, hsB⟩ := Set.mem_iUnion₂.mp hs
    obtain ⟨A, hA, rfl⟩ := hB
    obtain ⟨a, b, hab, hadjA⟩ := A.mem_edgeSet_toGMGraph_iff.mp hsB
    have hAuv : A.graph.Adj u v := A.graph.mem_edgeSet.mp
      (hab ▸ A.graph.mem_edgeSet.mpr hadjA)
    refine ⟨A, hA, ?_⟩
    rw [case3LiftMember_edgeSet]
    exact (case3MemberMultiDigraph_mem_edgeSet D A _ u v e.2.2).mpr ⟨hk, Or.inl hAuv⟩

/-- Different simple members lift to disjoint multigraph edge sets. -/
theorem case3LiftFamily_edge_disjoint {n : ℕ} (D : MultiDigraph n)
    (omega : List (Fin n)) (homega : omega.Nodup)
    (F : Set (Alg86Subgraph D.toSimpleGraph))
    (hdiv : GM13.IsSocietyDivision (case3SimpleSocietyInput D omega homega).toSociety
      (Alg86Subgraph.toGMGraph '' F))
    {A B : Alg86Subgraph D.toSimpleGraph} (hA : A ∈ F) (hB : B ∈ F) (hne : A ≠ B)
    (assignment : Case3LoopAssignment (case3SimpleSocietyInput D omega homega) F :=
      case3DefaultLoopAssignment (case3SimpleSocietyInput D omega homega) F hdiv) :
    Disjoint
      E(case3LiftMember D A (case3AssignedLoops assignment A))
      E(case3LiftMember D B (case3AssignedLoops assignment B)) := by
  let x := case3SimpleSocietyInput D omega homega
  apply Set.disjoint_left.mpr
  intro e heA heB
  have heD := (case3LiftMember_le D A (case3AssignedLoops assignment A)).edgeSet_mono heA
  have hu : e.1 < n := heD.choose
  have hv : e.2.1 < n := heD.choose_spec.choose
  let u : Fin n := ⟨e.1, hu⟩
  let v : Fin n := ⟨e.2.1, hv⟩
  rw [case3LiftMember_edgeSet] at heA heB
  have hselA := ((case3MemberMultiDigraph_mem_edgeSet D A _ u v e.2.2).mp heA).2
  have hselB := ((case3MemberMultiDigraph_mem_edgeSet D B _ u v e.2.2).mp heB).2
  by_cases huv : u = v
  · have hloopA : u ∈ case3AssignedLoops assignment A := by
      rcases hselA with h | h
      · exact False.elim ((A.graph.ne_of_adj h) huv)
      · exact h.2.1
    have hloopB : u ∈ case3AssignedLoops assignment B := by
      rcases hselB with h | h
      · exact False.elim ((B.graph.ne_of_adj h) huv)
      · exact h.2.1
    exact hne (((mem_case3AssignedLoops assignment A u).mp hloopA).symm.trans
      ((mem_case3AssignedLoops assignment B u).mp hloopB))
  · have hadjA : A.graph.Adj u v := hselA.resolve_right (fun h => huv h.1)
    have hadjB : B.graph.Adj u v := hselB.resolve_right (fun h => huv h.1)
    have hneq : A.toGMGraph ≠ B.toGMGraph :=
      fun h => hne (Alg86Subgraph.toGMGraph_injective h)
    have hdis := hdiv.edge_disjoint ⟨A, hA, rfl⟩ ⟨B, hB, rfl⟩ hneq
    exact Set.disjoint_left.mp hdis
      ((A.isLink_toGMGraph_iff.mpr ⟨rfl, hadjA⟩).edge_mem)
      ((B.isLink_toGMGraph_iff.mpr ⟨rfl, hadjB⟩).edge_mem)

end GraphMinor.Compute
