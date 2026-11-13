module

public import GraphMinor.GM06.Alg34GapInterleave
public import GraphMinor.Compute.GM06Alg34GapPositionOrder

/-!
# Circle crossing order of following gap points

Choose one point in each following segment of an increasing vertex
sequence. Their coordinates interleave, so the numeric alternating test
is the geometric crossing test. The gap points also have exactly the
cyclic order of their own indices.
-/

public section
namespace GraphMinor.GM06

open Set Surface Compute

/-- Following gap points have the cyclic crossing order of their starting vertices. -/
theorem alg34_gap_circle_order {V : Set Circle} {c : Circle} (hc : c ∈ V)
    {n : ℕ} (v p : Fin n → Circle) (hv : ∀ i, v i ∈ V)
    (horder : StrictMono (fun i => c.angleDiff (v i)))
    (hp : ∀ i, p i ∈ nextSegment V (v i)) (a b i j : Fin n) :
    GM06DrawingData.crossesOnList (List.finRange n) a b i j = true ↔
      CrossesOn (univ : Set Circle) (p a) (p b) (p i) (p j) := by
  have hm := alg34_gap_angles_strictMono hc v p hv horder hp
  exact (alg34_gap_coordinate_order (circleCoordFrom c) p hm a b i j).trans
    (crossesOn_univ_iff_circleCoordFrom c).symm

/-- Primal pairs and following gap pairs have exactly the finite alternating
crossing relation used by the supplied gap input. -/
theorem alg34_primal_gap_circle_order {V : Set Circle} {c : Circle} (hc : c ∈ V)
    {n : ℕ} (v p : Fin n → Circle) (hv : ∀ i, v i ∈ V)
    (horder : StrictMono (fun i => c.angleDiff (v i)))
    (hp : ∀ i, p i ∈ nextSegment V (v i)) (a b i j : Fin n) :
    GM06DrawingData.pairCrossesGaps (List.finRange n) a b
      (Fin.cast List.length_finRange.symm i) (Fin.cast List.length_finRange.symm j) = true ↔
        CrossesOn (univ : Set Circle) (v a) (v b) (p i) (p j) := by
  have hm := alg34_gap_interleaved_strictMono hc v p hv horder hp
  have he := (alg34_gap_coordinate_order (circleCoordFrom c) (alg34_interleavedPoint v p)
    hm (gm06EvenIndex a) (gm06EvenIndex b) (gm06OddIndex i) (gm06OddIndex j)).trans
      (crossesOn_univ_iff_circleCoordFrom c).symm
  rw [gm06EvenOdd_crosses] at he
  simpa only [gm06EvenIndex, gm06OddIndex, alg34_interleavedPoint_even,
    alg34_interleavedPoint_odd] using he

end GraphMinor.GM06
