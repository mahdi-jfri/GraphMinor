module

public import GraphMinor.Compute.GM06Alg34GapRestriction
public import GraphMinor.Compute.GM06Alg34GapListPositions
public import GraphMinor.Compute.GM06Alg34FilterOrder

/-!
# Retained cuff positions and their following gaps

The index of a retained vertex in the old cuff list gives an increasing
selection of old positions. Pair the surviving vertex with the gap at
that same old index. The alternating-position restriction theorem then
preserves exactly the primal-versus-gap crossing comparisons.
-/

@[expose] public section
namespace GraphMinor.Compute

/-- The old position of a vertex read at a filtered cuff position. -/
def gm06FilterPosition {α : Type*} [DecidableEq α] (L : List α) (p : α → Bool)
    (i : Fin (L.filter p).length) : Fin L.length :=
  gm06ListIndex L ((L.filter p).get i) (List.mem_of_mem_filter ((L.filter p).get_mem i))

/-- Reading a retained vertex through its old position recovers that vertex. -/
theorem gm06FilterPosition_get {α : Type*} [DecidableEq α] (L : List α) (p : α → Bool)
    (i : Fin (L.filter p).length) : L.get (gm06FilterPosition L p i) = (L.filter p).get i :=
  gm06ListIndex_get _ _ _

private theorem idxOf_get {α : Type*} [DecidableEq α] {L : List α} (hL : L.Nodup)
    (i : Fin L.length) : L.idxOf (L.get i) = i.val := by
  have hh := congrArg (fun j : Fin L.length => j.val) (gm06ListIndex_get_index L hL i)
  exact hh

/-- Retained cuff positions occur in increasing old-index order. -/
theorem gm06FilterPosition_strictMono {α : Type*} [DecidableEq α]
    (L : List α) (hL : L.Nodup) (p : α → Bool) : StrictMono (gm06FilterPosition L p) := by
  intro i j hij
  change L.idxOf ((L.filter p).get i) < L.idxOf ((L.filter p).get j)
  apply (gm06_idxOf_lt_idxOf_filter L hL p ((L.filter p).get_mem i) ((L.filter p).get_mem j)).mp
  rw [idxOf_get (hL.filter p) i, idxOf_get (hL.filter p) j]
  exact hij

/-- Keeping a cuff vertex and its following gap preserves their crossing
comparisons against every retained primal pair. -/
theorem gm06PairCrossesGaps_filter {n : ℕ} (L : List (Fin n)) (hL : L.Nodup)
    (p : Fin n → Bool) (a b i j : Fin (L.filter p).length) :
    GM06DrawingData.pairCrossesGaps (L.filter p) ((L.filter p).get a) ((L.filter p).get b) i j =
      GM06DrawingData.pairCrossesGaps L (L.get (gm06FilterPosition L p a))
        (L.get (gm06FilterPosition L p b)) (gm06FilterPosition L p i) (gm06FilterPosition L p j) := by
  rw [gm06PairCrossesGaps_get (hL.filter p), gm06PairCrossesGaps_get hL]
  exact gm06PairCrossesGaps_fin_mono (gm06FilterPosition L p) (gm06FilterPosition_strictMono L hL p)
    a b i j

end GraphMinor.Compute
