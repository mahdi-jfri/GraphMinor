module

public import GraphMinor.GM06.Alg34GapCoordinateOrder

/-!
# Coordinates of points in the following boundary segment

Cut the circular coordinate at a vertex of the finite set. A point in
the segment following a vertex has a larger coordinate than that vertex
and a smaller coordinate than every later vertex. Thus the chosen gap
points interleave with the increasing vertex list without crossing the
coordinate cut.
-/

public section
namespace GraphMinor.GM06

open Set Surface

/-- With the coordinate cut at a supplied vertex, its following gap
always has a larger coordinate than its starting vertex. -/
theorem alg34_gap_angle_lower {V : Set Circle} {c v p : Circle}
    (hc : c ∈ V) (hp : p ∈ nextSegment V v) :
    c.angleDiff v < c.angleDiff p := by
  have hz : c.angleDiff c = 0 := by simp [Circle.angleDiff]
  by_cases hvc : v = c
  · rw [hvc, hz]
    exact Circle.angleDiff_pos (fun he => hp.1 (hvc.trans he).symm)
  · have hcv : c ≠ v := Ne.symm hvc
    have ht := hp.2 c ⟨hc, by simpa only [mem_singleton_iff] using hcv⟩
    have hvpos := Circle.angleDiff_pos hcv
    by_contra hn
    have hle : c.angleDiff p ≤ c.angleDiff v := le_of_not_gt hn
    have hne : c.angleDiff p ≠ c.angleDiff v := (circleCoordFrom c).injective.ne hp.1
    have hlt : c.angleDiff p < c.angleDiff v := lt_of_le_of_ne hle hne
    rw [angleDiff_eq_of_angleDiff (x := c) (a := v) (b := p),
      angleDiff_eq_of_angleDiff (x := c) (a := v) (b := c)] at ht
    simp only [hz, if_neg (not_le.mpr hlt), if_neg (not_le.mpr hvpos)] at ht
    have hnonneg := Circle.angleDiff_nonneg c p
    linarith only [ht, hnonneg]

/-- A point in the following segment precedes every vertex with larger
coordinate, since the segment ends before the first such vertex. -/
theorem alg34_gap_angle_upper {V : Set Circle} {c v w p : Circle}
    (hc : c ∈ V) (hw : w ∈ V) (hp : p ∈ nextSegment V v)
    (hvw : c.angleDiff v < c.angleDiff w) :
    c.angleDiff p < c.angleDiff w := by
  have hwv : w ≠ v := by
    intro he
    rw [he] at hvw
    exact lt_irrefl _ hvw
  have ht := hp.2 w ⟨hw, by simpa only [mem_singleton_iff] using hwv⟩
  have hvp := alg34_gap_angle_lower hc hp
  rw [angleDiff_eq_of_angleDiff (x := c) (a := v) (b := p),
    angleDiff_eq_of_angleDiff (x := c) (a := v) (b := w)] at ht
  simp only [if_pos hvp.le, if_pos hvw.le] at ht
  linarith only [ht]

/-- Points selected in successive following segments have increasing
coordinates in the same order as their starting vertices. -/
theorem alg34_gap_angles_strictMono {V : Set Circle} {c : Circle} (hc : c ∈ V)
    {n : ℕ} (v p : Fin n → Circle) (hv : ∀ i, v i ∈ V)
    (horder : StrictMono (fun i => c.angleDiff (v i)))
    (hp : ∀ i, p i ∈ nextSegment V (v i)) :
    StrictMono (fun i => c.angleDiff (p i)) := by
  intro i j hij
  exact (alg34_gap_angle_upper hc (hv j) (hp i) (horder hij)).trans
    (alg34_gap_angle_lower hc (hp j))

end GraphMinor.GM06
