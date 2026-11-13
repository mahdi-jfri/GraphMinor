module

public import GraphMinor.Compute.Parse
public import GraphMinor.Compute.Algorithm99Relabel

/-!
# Canonical edge lists after compacting a child graph

The increasing numbering of surviving vertices preserves the canonical
edge order. Thus compacting a simple graph amounts to filtering out edges
with a deleted endpoint and replacing each surviving endpoint by its
rank. The rank program already computes these numbers in one pass. This
supplies the edge-list identity needed for II's recursive child encodings.
-/

public section
namespace GraphMinor.Compute
open Classical

/-- Increasing numbering identifies the surviving vertex subtype with its
compact range. -/
def gm02CompactEquiv {n : ℕ} (Z : Finset (Fin n)) :
    {v : Fin n // v ∉ Z} ≃ Fin Zᶜ.card where
  toFun v := ⟨compactRank Z v.val.val, compactRank_lt_card Z v.property⟩
  invFun i := ⟨compactEmb Z i, compactEmb_not_mem Z i⟩
  left_inv v := Subtype.ext (compactEmb_compactRank Z v.property)
  right_inv i := Fin.ext (compactRank_compactEmb Z i)

/-- The inverse compact numbering gives the old surviving vertex name. -/
theorem gm02CompactEquiv_symm_val {n : ℕ} (Z : Finset (Fin n)) (i : Fin Zᶜ.card) :
    ((gm02CompactEquiv Z).symm i).val = compactEmb Z i := by
  unfold gm02CompactEquiv
  rfl

/-- The forward compact numbering is the computed rank. -/
theorem gm02CompactEquiv_apply_val {n : ℕ} (Z : Finset (Fin n))
    (v : {v : Fin n // v ∉ Z}) : (gm02CompactEquiv Z v).val = compactRank Z v.val.val := by
  unfold gm02CompactEquiv
  rfl

/-- Mapping the compact canonical edge list back to old names gives exactly
the surviving edges, in the original canonical order. -/
theorem gm02CompactEdgeList_map {n : ℕ} (F : SimpleGraph (Fin n)) [DecidableRel F.Adj]
    (Z : Finset (Fin n)) :
    (edgeListOf (F.comap (compactEmb Z))).map (Prod.map (compactEmb Z) (compactEmb Z)) =
      (edgeListOf F).filter (fun p => decide (p.1 ∉ Z) && decide (p.2 ∉ Z)) := by
  have hp : edgeListOf (F.comap (compactEmb Z)) =
      (allPairs Zᶜ.card).filter
        ((fun p : Fin n × Fin n => decide (p.1.val < p.2.val ∧ F.Adj p.1 p.2)) ∘
          Prod.map (compactEmb Z) (compactEmb Z)) := by
    unfold edgeListOf
    congr 1
    funext p
    simp only [Function.comp_apply, Prod.map, SimpleGraph.comap_adj, decide_eq_decide]
    exact and_congr (compactEmb Z).lt_iff_lt.symm Iff.rfl
  rw [hp, ← List.filter_map, map_compactEmb_allPairs Z, List.filter_comm]
  rfl

/-- Flattening commutes with mapping both endpoints of every edge. -/
theorem gm02FlatEdges_map {n m : ℕ} (edges : List (Fin n × Fin n)) (f : Fin n → Fin m) :
    flatEdges (edges.map (Prod.map f f)) =
      edges.flatMap (fun p => [((f p.1).val), ((f p.2).val)]) := by
  simp only [flatEdges, List.flatMap_map, Prod.map]

/-- The compact edge words are obtained by rank substitution in the
surviving original edge words. -/
theorem gm02CompactEdgeWords {n : ℕ} (F : SimpleGraph (Fin n)) [DecidableRel F.Adj]
    (Z : Finset (Fin n)) :
    flatEdges (edgeListOf (F.comap (compactEmb Z))) =
      (flatEdges ((edgeListOf F).filter
        (fun p => decide (p.1 ∉ Z) && decide (p.2 ∉ Z)))).map (compactRank Z) := by
  rw [← gm02CompactEdgeList_map F Z, gm02FlatEdges_map]
  simp only [List.map_flatMap, List.map_cons, List.map_nil, compactRank_compactEmb]
  rfl

end GraphMinor.Compute
