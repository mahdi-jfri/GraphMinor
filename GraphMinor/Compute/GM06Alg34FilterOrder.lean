module

public import GraphMinor.Compute.GM06Alg34LabelList
import Mathlib.Data.List.NodupEquivFin

/-!
# Relative order of surviving cuff labels

A filtered cuff list is a sublist of the original list. Its positions
embed in the original positions by a strictly increasing map. Distinct
surviving labels therefore keep their relative index order. This is the
order fact needed to preserve the cyclic crossing test after deletion.
-/

public section
namespace GraphMinor.Compute

/-- A sublist of a list without repetitions preserves the index order
of any two labels retained in the sublist. -/
theorem gm06_idxOf_lt_idxOf_sublist {α : Type*} [DecidableEq α]
    {L' L : List α} (hsub : List.Sublist L' L) (hL : L.Nodup)
    {a b : α} (ha : a ∈ L') (hb : b ∈ L') :
    L'.idxOf a < L'.idxOf b ↔ L.idxOf a < L.idxOf b := by
  obtain ⟨f, hf⟩ := List.sublist_iff_exists_fin_orderEmbedding_get_eq.mp hsub
  let ia := gm06ListIndex L' a ha
  let ib := gm06ListIndex L' b hb
  have hia : gm06ListIndex L a (hsub.subset ha) = f ia := by
    apply hL.get_inj_iff.mp
    exact (gm06ListIndex_get L a _).trans ((hf ia).symm.trans (gm06ListIndex_get L' a ha)).symm
  have hib : gm06ListIndex L b (hsub.subset hb) = f ib := by
    apply hL.get_inj_iff.mp
    exact (gm06ListIndex_get L b _).trans ((hf ib).symm.trans (gm06ListIndex_get L' b hb)).symm
  change ia < ib ↔ gm06ListIndex L a (hsub.subset ha) < gm06ListIndex L b (hsub.subset hb)
  rw [hia, hib]
  exact f.lt_iff_lt.symm

/-- In particular, filtering a cuff list preserves all comparisons
between the indices of retained labels. -/
theorem gm06_idxOf_lt_idxOf_filter {α : Type*} [DecidableEq α] (L : List α)
    (hL : L.Nodup) (p : α → Bool) {a b : α} (ha : a ∈ L.filter p) (hb : b ∈ L.filter p) :
    (L.filter p).idxOf a < (L.filter p).idxOf b ↔ L.idxOf a < L.idxOf b :=
  gm06_idxOf_lt_idxOf_sublist (List.filter_sublist) hL ha hb

end GraphMinor.Compute
