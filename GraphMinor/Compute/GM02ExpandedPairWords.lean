module

public import GraphMinor.Compute.GM02CompactEdges
public import GraphMinor.GM02.TerminationGraphMaps

/-!
# Canonical pair order under expansion of boundary names

Compact boundary names are increasing in the original vertex order.
Consequently expanding a matching maps its canonical edge list without
reordering it. This identifies the endpoint array emitted by a fixed
catalogue branch with the canonical pair words of its parent scheme.
-/

public section
namespace GraphMinor.Compute
open Classical GraphMinor.GM02

/-- An expanded graph has no endpoint outside the retained boundary. -/
theorem gm02CompactMapped_filter {n : ℕ} (Z : Finset (Fin n))
    (F : SimpleGraph (Fin Zᶜ.card)) [DecidableRel F.Adj] :
    (edgeListOf (F.map (compactEmb Z).toEmbedding)).filter
      (fun p => decide (p.1 ∉ Z) && decide (p.2 ∉ Z)) =
        edgeListOf (F.map (compactEmb Z).toEmbedding) := by
  apply List.filter_eq_self.2
  intro p hp
  have hadj := ((mem_edgeListOf _ p).1 hp).2
  obtain ⟨u, v, _, hu, hv⟩ := (SimpleGraph.map_adj _ _ _ _).mp hadj
  simp only [Bool.and_eq_true, decide_eq_true_eq]
  exact ⟨hu ▸ compactEmb_not_mem Z u, hv ▸ compactEmb_not_mem Z v⟩

/-- Expanding increasing boundary names preserves the canonical edge order. -/
theorem gm02CompactMapped_edgeList {n : ℕ} (Z : Finset (Fin n))
    (F : SimpleGraph (Fin Zᶜ.card)) [DecidableRel F.Adj] :
    (edgeListOf F).map (Prod.map (compactEmb Z) (compactEmb Z)) =
      edgeListOf (F.map (compactEmb Z).toEmbedding) := by
  have he := gm02CompactEdgeList_map (F.map (compactEmb Z).toEmbedding) Z
  rw [gm02CompactMapped_filter] at he
  have hc : (F.map (compactEmb Z).toEmbedding).comap (compactEmb Z) = F :=
    SimpleGraph.comap_map_eq (compactEmb Z).toEmbedding F
  simpa only [hc] using he

/-- The parent matching words are the boundary matching endpoints in old names. -/
theorem gm02ExpandedTermination_pairWords {n : ℕ} (Z : Finset (Fin n))
    (A : Termination (Set.univ : Set (Fin Zᶜ.card))) :
    flatEdges (edgeListOf (A.mapEmbedding (compactEmb Z).toEmbedding).pairGraph) =
      (edgeListOf A.pairGraph).flatMap
        (fun p => [(compactEmb Z p.1).val, (compactEmb Z p.2).val]) := by
  simp only [Termination.mapEmbedding_pairGraph]
  rw [← gm02CompactMapped_edgeList, gm02FlatEdges_map]

end GraphMinor.Compute
