module

public import GraphMinor.Compute.GM06Alg34Input
public import GraphMinor.GM06.Section2Dual

/-!
# Crossing order in an increasing circular coordinate

For points whose coordinates increase with their finite labels, open
coordinate arcs agree with numeric intervals. The numeric crossing test
therefore agrees with the circle crossing relation. This applies both
to cuff vertices and to the points inserted in the intervening gaps.
-/

public section
namespace GraphMinor.GM06

open Set Surface Compute

private theorem gap_bne_true (a b : Bool) :
    (a != b) = true ↔ ((a = true) ↔ ¬ b = true) := by
  cases a <;> cases b <;> decide

private theorem gap_between_xor (p q s t : ℕ)
    (hps : p ≠ s) (hpt : p ≠ t) (hqs : q ≠ s) (hqt : q ≠ t) :
    (GM06DrawingData.cyclicBetween p q s != GM06DrawingData.cyclicBetween p q t) = true ↔
      ((min p q < s ∧ s < max p q) ↔ ¬ (min p q < t ∧ t < max p q)) := by
  rw [gap_bne_true]
  simp only [GM06DrawingData.cyclicBetween]
  split_ifs <;> simp only [decide_eq_true_eq] <;> omega

/-- Increasing circular coordinates give the finite cyclic crossing order
of VI Section 2, page 117, for every choice of four finite labels. -/
theorem alg34_gap_coordinate_order {n : ℕ} (coord : CircleCoord Circle)
    (z : Fin n → Circle) (hz : StrictMono (fun i => coord.angle (z i)))
    (a c b d : Fin n) :
    GM06DrawingData.crossesOnList (List.finRange n) a c b d = true ↔
      circleCrosses coord (z a) (z c) (z b) (z d) := by
  have hinj : Function.Injective z := by
    intro i j hij
    exact hz.injective (congrArg coord.angle hij)
  have heq (i j : Fin n) : z i = z j ↔ i.val = j.val :=
    hinj.eq_iff.trans Fin.ext_iff
  have harc (t : Fin n) : onOpenArc coord (z a) (z c) (z t) ↔
      min a.val c.val < t.val ∧ t.val < max a.val c.val := by
    simp only [onOpenArc, min_lt_iff, lt_max_iff, hz.lt_iff_lt, Fin.lt_def]
  simp only [GM06DrawingData.crossesOnList, Bool.and_eq_true, decide_eq_true_eq,
    List.mem_finRange, true_and, List.idxOf_finRange, circleCrosses,
    ne_eq, heq, Fin.ext_iff, harc, gap_bne_true]
  by_cases hn : a.val ≠ c.val ∧ b.val ≠ d.val ∧ a.val ≠ b.val ∧
      a.val ≠ d.val ∧ c.val ≠ b.val ∧ c.val ≠ d.val
  · simp only [hn.1, hn.2.1, hn.2.2.1, hn.2.2.2.1, hn.2.2.2.2.1,
      hn.2.2.2.2.2, not_false_eq_true, true_and]
    simpa only [gap_bne_true] using gap_between_xor a.val c.val b.val d.val
      hn.2.2.1 hn.2.2.2.1 hn.2.2.2.2.1 hn.2.2.2.2.2
  · tauto

end GraphMinor.GM06
