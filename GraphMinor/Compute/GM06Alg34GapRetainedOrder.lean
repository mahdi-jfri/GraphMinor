module

public import GraphMinor.Compute.GM06Alg34GapRetainedPositions
import GraphMinor.Compute.GM06Alg34InducedOrder

/-!
# Crossing tests at retained gap positions

The old positions of the surviving vertices form an increasing map.
Applying the finite alternating-order theorem to this map preserves
primal-versus-gap crossings. Applying the ordinary cyclic-order theorem
preserves crossings between four gap points.
-/

public section
namespace GraphMinor.Compute

open GM06DrawingData

/-- Crossing tests for listed surviving vertices agree with the old
vertices and gaps at their selected old positions. -/
theorem gm06PairCrossesGaps_relabel_get (x : GM06DrawingData)
    (vs L : List (Fin x.n)) (hL : L.Nodup)
    (a b i j : Fin (x.relabelVertexList vs L).length) :
    pairCrossesGaps (x.relabelVertexList vs L)
      ((x.relabelVertexList vs L).get a) ((x.relabelVertexList vs L).get b) i j =
    pairCrossesGaps L (L.get (gm06InducedGapPosition x vs L a))
      (L.get (gm06InducedGapPosition x vs L b))
      (gm06InducedGapPosition x vs L i) (gm06InducedGapPosition x vs L j) := by
  rw [gm06PairCrossesGaps_get (x.relabelVertexList_nodup vs L hL),
    gm06PairCrossesGaps_get hL]
  exact gm06PairCrossesGaps_fin_mono (gm06InducedGapPosition x vs L)
    (gm06InducedGapPosition_strictMono x vs L hL) a b i j

/-- The retained gap positions have exactly their old cyclic order. -/
theorem gm06GapCrosses_relabel (x : GM06DrawingData)
    (vs L : List (Fin x.n)) (hL : L.Nodup)
    (a b i j : Fin (x.relabelVertexList vs L).length) :
    crossesOnList (List.finRange (x.relabelVertexList vs L).length) a b i j =
    crossesOnList (List.finRange L.length)
      (gm06InducedGapPosition x vs L a) (gm06InducedGapPosition x vs L b)
      (gm06InducedGapPosition x vs L i) (gm06InducedGapPosition x vs L j) :=
  (gm06CrossesFinRange_map (gm06InducedGapPosition x vs L)
    (gm06InducedGapPosition_strictMono x vs L hL) a b i j).symm

end GraphMinor.Compute
