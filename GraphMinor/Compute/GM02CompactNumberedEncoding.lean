module

public import GraphMinor.Compute.GM02CompactNumberedInstance
public import GraphMinor.Compute.GM02CompactTermination

/-!
# Exact plain encodings of compact child instances

Every edge and terminal endpoint of an actual child belongs to its
vertex set. Compacting its complement therefore filters out no edge or
pair. The numbered instance encoding is precisely the three computed
headers followed by rank-rewritten graph and matching words.
-/

public section
namespace GraphMinor.Compute
open Graph Set Classical GraphMinor.GM02

/-- Restricting to the actual vertices removes no path-shadow edge. -/
theorem gm02ActualGraph_filter_edges {n : ℕ} {β : Type*}
    (G : Graph (Fin n) β) (Z : Finset (Fin n))
    (hV : V(G) = {v : Fin n | v ∉ Z}) :
    (edgeListOf (pathGraph G)).filter
      (fun p => decide (p.1 ∉ Z) && decide (p.2 ∉ Z)) = edgeListOf (pathGraph G) := by
  apply List.filter_eq_self.2
  intro p hp
  have hadj := ((mem_edgeListOf _ p).1 hp).2
  have h₁ := hadj.1.left_mem
  have h₂ := hadj.1.right_mem
  rw [hV] at h₁ h₂
  simp only [Bool.and_eq_true, decide_eq_true_eq]
  exact ⟨h₁, h₂⟩

/-- Restricting to the actual vertices removes no prescribed pair. -/
theorem gm02ActualGraph_filter_pairs {n : ℕ} {β : Type*}
    (G : Graph (Fin n) β) (A : Termination V(G)) (Z : Finset (Fin n))
    (hV : V(G) = {v : Fin n | v ∉ Z}) :
    (edgeListOf A.pairGraph).filter
      (fun p => decide (p.1 ∉ Z) && decide (p.2 ∉ Z)) = edgeListOf A.pairGraph := by
  apply List.filter_eq_self.2
  intro p hp
  have hpair := A.pairGraph_adj_iff.mp ((mem_edgeListOf _ p).mp hp).2
  have h₁ := A.vertex_mem _ hpair p.1 (Sym2.mem_mk_left _ _)
  have h₂ := A.vertex_mem _ hpair p.2 (Sym2.mem_mk_right _ _)
  rw [hV] at h₁ h₂
  simp only [Bool.and_eq_true, decide_eq_true_eq]
  exact ⟨h₁, h₂⟩

/-- Compact numbering does not change the number of actual path-shadow edges. -/
theorem gm02CompactNumberedInstance_edgeCount {n : ℕ} {β : Type*}
    (G : Graph (Fin n) β) (A : Termination V(G)) (Z : Finset (Fin n))
    (hV : V(G) = {v : Fin n | v ∉ Z}) :
    (edgeListOf (gm02CompactNumberedInstance G A Z hV).G).length =
      (edgeListOf (pathGraph G)).length := by
  have he := congrArg List.length (gm02CompactEdgeList_map (pathGraph G) Z)
  simp only [List.length_map, gm02ActualGraph_filter_edges G Z hV] at he
  simp only [gm02CompactNumberedInstance_graph]
  convert he using 1; rfl

/-- The exact compact child encoding uses rank-rewritten original words. -/
theorem gm02CompactNumberedInstance_enc {n : ℕ} {β : Type*}
    (G : Graph (Fin n) β) (A : Termination V(G)) (Z : Finset (Fin n))
    (hV : V(G) = {v : Fin n | v ∉ Z}) :
    (gm02CompactNumberedInstance G A Z hV).enc =
      [Zᶜ.card, (edgeListOf (pathGraph G)).length] ++
        (flatEdges (edgeListOf (pathGraph G))).map (compactRank Z) ++
        [A.index] ++ (flatEdges (edgeListOf A.pairGraph)).map (compactRank Z) := by
  have hEG : flatEdges (edgeListOf (gm02CompactNumberedInstance G A Z hV).G) =
      (flatEdges (edgeListOf (pathGraph G))).map (compactRank Z) := by
    simp only [gm02CompactNumberedInstance_graph]
    have he := gm02CompactEdgeWords (pathGraph G) Z
    simp only [gm02ActualGraph_filter_edges G Z hV] at he
    convert he using 1; rfl
  have hPA : flatEdges (edgeListOf (gm02CompactNumberedInstance G A Z hV).A.pairGraph) =
      (flatEdges (edgeListOf A.pairGraph)).map (compactRank Z) := by
    simp only [gm02CompactNumberedInstance_pairGraph]
    have he := gm02CompactEdgeWords A.pairGraph Z
    simp only [gm02ActualGraph_filter_pairs G A Z hV] at he
    convert he using 1
    congr 2
  simp only [GM02SimpleTerminatedInput.enc, encGraph, hEG, hPA,
    gm02CompactNumberedInstance_index, gm02CompactNumberedInstance_edgeCount]
  rfl

end GraphMinor.Compute
