module

public import GraphMinor.Compute.GM02CompactEdges
public import GraphMinor.GM02.TerminationGraphMaps

/-!
# Compact terminal-pair encodings

All terminal endpoints of a child survive its vertex deletion. Restrict
the pairs to the surviving subtype and rename by increasing vertex rank.
The resulting matching is the original matching pulled back along the
increasing enumeration. Hence the same rank-word rewrite used for graph
edges also gives the canonical terminal-pair suffix of the child input.
-/

@[expose] public section
namespace GraphMinor.Compute
open Classical GraphMinor.GM02

/-- Rename a child termination by the increasing numbering of survivors. -/
noncomputable def gm02CompactTermination {n : ℕ} (Z : Finset (Fin n))
    (A : Termination {v : Fin n | v ∉ Z}) : Termination (Set.univ : Set (Fin Zᶜ.card)) :=
  (A.onVertices.mapEmbedding (gm02CompactEquiv Z).toEmbedding).rebase (Set.subset_univ _)

/-- Compact numbering preserves the prescribed number of pairs. -/
theorem gm02CompactTermination_index {n : ℕ} (Z : Finset (Fin n))
    (A : Termination {v : Fin n | v ∉ Z}) : (gm02CompactTermination Z A).index = A.index := by
  simp only [gm02CompactTermination, Termination.rebase_index,
    Termination.mapEmbedding_index, Termination.onVertices_index]

/-- The numbered matching is the original matching pulled back along the
increasing surviving-vertex enumeration. -/
theorem gm02CompactTermination_pairGraph {n : ℕ} (Z : Finset (Fin n))
    (A : Termination {v : Fin n | v ∉ Z}) :
    (gm02CompactTermination Z A).pairGraph = A.pairGraph.comap (compactEmb Z) := by
  rw [gm02CompactTermination, Termination.rebase_pairGraph, Termination.mapEquiv_pairGraph,
    Termination.onVertices_pairGraph]
  ext a b
  change A.pairGraph.Adj ((gm02CompactEquiv Z).symm a).val
    ((gm02CompactEquiv Z).symm b).val ↔ A.pairGraph.Adj (compactEmb Z a) (compactEmb Z b)
  rw [gm02CompactEquiv_symm_val, gm02CompactEquiv_symm_val]

/-- Every original pair survives, so filtering the matching removes no edge. -/
theorem gm02CompactTermination_filter_pairs {n : ℕ} (Z : Finset (Fin n))
    (A : Termination {v : Fin n | v ∉ Z}) :
    (edgeListOf A.pairGraph).filter
      (fun p => decide (p.1 ∉ Z) && decide (p.2 ∉ Z)) = edgeListOf A.pairGraph := by
  apply List.filter_eq_self.2
  intro p hp
  have hadj := (mem_edgeListOf A.pairGraph p).1 hp
  have hpair := A.pairGraph_adj_iff.1 hadj.2
  have h₁ := A.vertex_mem _ hpair p.1 (Sym2.mem_mk_left _ _)
  have h₂ := A.vertex_mem _ hpair p.2 (Sym2.mem_mk_right _ _)
  simp only [Bool.and_eq_true, decide_eq_true_eq]
  exact ⟨h₁, h₂⟩

/-- The compact endpoint suffix is exactly the old endpoint words with
ranks substituted, in canonical order. -/
theorem gm02CompactTermination_pairWords {n : ℕ} (Z : Finset (Fin n))
    (A : Termination {v : Fin n | v ∉ Z}) :
    flatEdges (edgeListOf (gm02CompactTermination Z A).pairGraph) =
      (flatEdges (edgeListOf A.pairGraph)).map (compactRank Z) := by
  simpa only [gm02CompactTermination_pairGraph, gm02CompactTermination_filter_pairs] using
    (gm02CompactEdgeWords A.pairGraph Z)

end GraphMinor.Compute
