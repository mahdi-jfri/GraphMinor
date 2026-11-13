module

public import GraphMinor.GM06.Section5CollapseRectangle
public import GraphMinor.GM06.Section5CylinderProduct
import GraphMinor.GM06.Section4
import Mathlib.Tactic

/-!
# A rectangular chart around the radial seam

For Reduction 3 of VI, page 129, the rectangle coordinates send
horizontal coordinate x to angle εx and height y to radius 1+y/2.
For 0<ε<π this map is injective. The central half-segment is exactly
the first half of the radial seam, and the top and bottom sides lie
on the two cuffs.
-/

public section

namespace GraphMinor.GM06

open Set Real GraphMinor.Surface

/-- The rectangular seam chart, with angular half-width ε. -/
@[expose] noncomputable def section5SeamRectangle (ε : ℝ) :
    C(Section5CollapseRectangle, ClosedCylinder) where
  toFun p := ⟨(1 + p.2.1 / 2, Circle.exp (ε * p.1.1)),
    ⟨⟨by linarith only [p.2.2.1], by linarith only [p.2.2.2]⟩, trivial⟩⟩
  continuous_toFun := by fun_prop

/-- A seam chart narrower than a full angular period is injective. -/
theorem section5SeamRectangle_injective {ε : ℝ} (hε : 0 < ε) (hεπ : ε < π) :
    Function.Injective (section5SeamRectangle ε) := by
  intro p q he
  have hr : 1 + p.2.1 / 2 = 1 + q.2.1 / 2 := congrArg (fun x : ClosedCylinder => x.1.1) he
  have ha : Circle.exp (ε * p.1.1) = Circle.exp (ε * q.1.1) :=
    congrArg (fun x : ClosedCylinder => x.1.2) he
  have hangle (t : Icc (-1 : ℝ) 1) : ε * t.1 ∈ Icc (-ε) ε := by
    constructor <;> nlinarith only [hε, t.2.1, t.2.2]
  have hx := Circle.exp_injOn_Icc (by linarith only [hεπ] : ε - -ε < 2 * π)
    (hangle p.1) (hangle q.1) ha
  apply Prod.ext
  · apply Subtype.ext
    exact (mul_left_cancel₀ hε.ne' hx)
  · apply Subtype.ext
    linarith only [hr]

/-- A point of the rectangular chart lies on the cylinder boundary
exactly when its height is zero or two. -/
theorem section5SeamRectangle_mem_boundary_iff (ε : ℝ) (p : Section5CollapseRectangle) :
    section5SeamRectangle ε p ∈ bd ClosedCylinder ↔ p.2.1 = 0 ∨ p.2.1 = 2 := by
  rw [bd_closedCylinder]
  change (1 + p.2.1 / 2 = 1 ∨ 1 + p.2.1 / 2 = 2) ↔ _
  constructor
  · rintro (h | h)
    · exact Or.inl (by linarith only [h])
    · exact Or.inr (by linarith only [h])
  · rintro (h | h)
    · exact Or.inl (by rw [h]; norm_num)
    · exact Or.inr (by rw [h]; norm_num)

/-- The chart sends its distinguished bottom point to the beginning
of the standard radial seam. -/
theorem section5SeamRectangle_origin (ε : ℝ) :
    section5SeamRectangle ε section5RectangleOrigin = section5CylinderProduct.symm (1, 0) := by
  apply Subtype.ext
  apply Prod.ext
  · change 1 + (0 : ℝ) / 2 = 1 + 0
    ring
  · change Circle.exp (ε * 0) = 1
    simp

/-- The segment collapsed in the model rectangle is exactly the first
half of the radial seam in the cylinder. -/
theorem image_section5SeamRectangle_segment (ε : ℝ) :
    section5SeamRectangle ε '' {p | p.1.1 = 0 ∧ p.2.1 ≤ 1} =
      (fun u : unitInterval => section5CylinderProduct.symm (1, u)) ''
        Icc 0 (⟨1 / 2, by constructor <;> norm_num⟩ : unitInterval) := by
  ext x
  constructor
  · rintro ⟨p, ⟨hp0, hp1⟩, rfl⟩
    let u : unitInterval := ⟨p.2.1 / 2, ⟨by linarith only [p.2.2.1], by linarith only [p.2.2.2]⟩⟩
    refine ⟨u, ⟨bot_le, ?_⟩, ?_⟩
    · change p.2.1 / 2 ≤ 1 / 2
      linarith only [hp1]
    · apply Subtype.ext
      apply Prod.ext
      · rfl
      · change (1 : Circle) = Circle.exp (ε * p.1.1)
        rw [hp0, mul_zero, Circle.exp_zero]
  · rintro ⟨u, hu, rfl⟩
    let p : Section5CollapseRectangle :=
      (⟨0, by constructor <;> norm_num⟩,
        ⟨2 * u.1, ⟨by linarith only [u.2.1], by linarith only [u.2.2]⟩⟩)
    refine ⟨p, ⟨rfl, ?_⟩, ?_⟩
    · change 2 * u.1 ≤ 1
      have hh : u.1 ≤ 1 / 2 := hu.2
      linarith only [hh]
    · apply Subtype.ext
      apply Prod.ext
      · change 1 + 2 * u.1 / 2 = 1 + u.1
        ring
      · change Circle.exp (ε * 0) = 1
        simp

end GraphMinor.GM06
