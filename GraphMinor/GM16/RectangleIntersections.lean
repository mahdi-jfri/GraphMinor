module

public import GraphMinor.GM16.RectangularLines
import Mathlib.Tactic.Linarith

/-!
# Intersections of adjacent rectangles

Two bricks in one row share a vertical side. Bricks in successive
rows have their ends shifted by one, so their intersection is a
horizontal line of length one. The interval calculations here keep
these common sides explicit for the two-face rigidity case in
XVI (4.2).
-/

public section
namespace GraphMinor.GM16
open Set Surface

/-- Rectangles placed side by side meet in their common vertical side. -/
theorem adjacent_rectangles_inter {a b c d e : ℝ} (hab : a ≤ b) (hbc : b ≤ c) :
    (Icc a b ×ˢ Icc d e) ∩ (Icc b c ×ˢ Icc d e) = {b} ×ˢ Icc d e := by
  rw [prod_inter_prod,inter_self,Icc_inter_Icc,max_eq_right hab,min_eq_left hbc,Icc_self]

/-- Staggered rectangles in successive rows meet in the overlap of the
horizontal sides at their common height. -/
theorem staggered_rectangles_inter {a b c d e f g : ℝ}
    (hab : a ≤ b) (hcd : c ≤ d) (hef : e ≤ f) (hfg : f ≤ g) :
    (Icc a c ×ˢ Icc e f) ∩ (Icc b d ×ˢ Icc f g) = Icc b c ×ˢ {f} := by
  rw [prod_inter_prod,Icc_inter_Icc,Icc_inter_Icc,max_eq_right hab,min_eq_left hcd,
    max_eq_right hef,min_eq_left hfg,Icc_self]

/-- The common side of two bricks in the same row is a line. -/
theorem adjacent_rectangles_inter_isLine {a b c d e : ℝ}
    (hab : a ≤ b) (hbc : b ≤ c) (hde : d < e) :
    IsLineWithEnds ((Icc a b ×ˢ Icc d e) ∩ (Icc b c ×ˢ Icc d e)) (b,d) (b,e) := by
  rw [adjacent_rectangles_inter hab hbc]
  exact vertical_interval_isLine b hde

/-- The common side of overlapping bricks in successive rows is a line. -/
theorem staggered_rectangles_inter_isLine {a b c d e f g : ℝ}
    (hab : a ≤ b) (hbc : b < c) (hcd : c ≤ d) (hef : e ≤ f) (hfg : f ≤ g) :
    IsLineWithEnds ((Icc a c ×ˢ Icc e f) ∩ (Icc b d ×ˢ Icc f g)) (b,f) (c,f) := by
  rw [staggered_rectangles_inter hab hcd hef hfg]
  exact horizontal_interval_isLine hbc f

end GraphMinor.GM16
