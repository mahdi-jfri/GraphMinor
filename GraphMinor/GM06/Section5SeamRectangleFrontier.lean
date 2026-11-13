module

public import GraphMinor.GM06.Section5SeamRectangle
import Mathlib.Analysis.Complex.CoveringMap
import Mathlib.Tactic

/-!
# The frontier of the seam chart

In the rectangular chart used for VI Reduction 3, page 129, every
point with horizontal coordinate strictly between the two sides
has an open angular band in the chart image. The relative frontier
of the chart image can therefore occur only at a vertical side.
The rectangle contraction fixes both such sides.
-/

public section

namespace GraphMinor.GM06

open Set Real GraphMinor.Surface

/-- Only the vertical sides of the seam rectangle can map to the
frontier of its image in the cylinder. -/
theorem section5SeamRectangle_frontier_sides {ε : ℝ} (hε : 0 < ε)
    (p : Section5CollapseRectangle)
    (hp : section5SeamRectangle ε p ∈ frontier (range (section5SeamRectangle ε))) :
    p.1.1 = -1 ∨ p.1.1 = 1 := by
  by_contra hn
  obtain ⟨hnL, hnR⟩ := not_or.mp hn
  have hxL : -1 < p.1.1 := lt_of_le_of_ne p.1.2.1 (fun h => hnL h.symm)
  have hxR : p.1.1 < 1 := lt_of_le_of_ne p.1.2.2 hnR
  let U : Set ClosedCylinder := {z | z.1.2 ∈ Circle.exp '' Ioo (-ε) ε}
  have hU : IsOpen U :=
    (Circle.isCoveringMap_exp.isOpenMap _ isOpen_Ioo).preimage
      (continuous_snd.comp continuous_subtype_val)
  have hpU : section5SeamRectangle ε p ∈ U :=
    ⟨ε * p.1.1, ⟨by nlinarith only [hε, hxL], by nlinarith only [hε, hxR]⟩, rfl⟩
  have hsub : U ⊆ range (section5SeamRectangle ε) := by
    rintro z ⟨a, ha, he⟩
    let q : Section5CollapseRectangle :=
      (⟨a / ε, ⟨(le_div_iff₀ hε).mpr (by linarith only [ha.1]),
        (div_le_iff₀ hε).mpr (by linarith only [ha.2])⟩⟩,
        ⟨2 * (z.1.1 - 1), ⟨by linarith only [z.2.1.1], by linarith only [z.2.1.2]⟩⟩)
    refine ⟨q, ?_⟩
    apply Subtype.ext
    apply Prod.ext
    · change 1 + 2 * (z.1.1 - 1) / 2 = z.1.1
      ring
    · change Circle.exp (ε * (a / ε)) = z.1.2
      rw [show ε * (a / ε) = a by field_simp]
      exact he
  have hi : section5SeamRectangle ε p ∈ interior (range (section5SeamRectangle ε)) :=
    mem_interior.mpr ⟨U, hsub, hU, hpU⟩
  exact hp.2 hi

end GraphMinor.GM06
