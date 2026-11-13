module

public import GraphMinor.GM06.Section5CollapseCoordinates
public import Mathlib.Topology.ContinuousMap.Basic
public import Mathlib.Topology.UnitInterval

/-!
# A boundary-fixing contraction of a rectangle

For Reduction 3 of VI, page 129, the coordinate contraction defines a
continuous surjection of a closed rectangle. Its only nontrivial fiber
is the segment from (0,0) to (0,1). Linear interpolation gives a
homotopy to the identity that fixes the boundary throughout.
-/

public section

namespace GraphMinor.GM06

open Set

/-- The rectangular chart used for the local contraction in Reduction 3. -/
abbrev Section5CollapseRectangle := Icc (-1 : ℝ) 1 × Icc (0 : ℝ) 2

/-- The endpoint on the bottom side of the segment being contracted. -/
@[expose] def section5RectangleOrigin : Section5CollapseRectangle :=
  (⟨0, by norm_num⟩, ⟨0, by norm_num⟩)

/-- Contract the distinguished vertical segment in the rectangle. -/
noncomputable def section5RectangleCollapse :
    C(Section5CollapseRectangle, Section5CollapseRectangle) where
  toFun p := (p.1, ⟨section5CollapseHeight p.1.1 p.2.1,
    section5CollapseHeight_mem p.1.2 p.2.2⟩)
  continuous_toFun := continuous_fst.prodMk
    ((continuous_section5CollapseHeight.comp
      ((continuous_subtype_val.comp continuous_fst).prodMk
        (continuous_subtype_val.comp continuous_snd))).subtype_mk _)

/-- The contraction fixes the four sides of the rectangle. -/
theorem section5RectangleCollapse_boundary (p : Section5CollapseRectangle)
    (hb : p.1.1 = -1 ∨ p.1.1 = 1 ∨ p.2.1 = 0 ∨ p.2.1 = 2) :
    section5RectangleCollapse p = p := by
  refine Prod.ext ?_ ?_
  · rfl
  apply Subtype.ext
  exact section5CollapseHeight_boundary p.1.2 p.2.2 hb

/-- The contraction maps onto the rectangle. -/
theorem section5RectangleCollapse_surjective :
    Function.Surjective section5RectangleCollapse := by
  intro p
  obtain ⟨y, hy, he⟩ := section5CollapseHeight_surjOn p.1.2 p.2.2
  exact ⟨(p.1, ⟨y, hy⟩), Prod.ext rfl (Subtype.ext he)⟩

/-- Outside the distinguished segment the contraction is injective. -/
theorem section5RectangleCollapse_injOn :
    InjOn section5RectangleCollapse {p | p.1.1 ≠ 0 ∨ 1 < p.2.1} := by
  intro p hp q hq he
  have hx := congrArg (fun r : Section5CollapseRectangle => r.1) he
  change p.1 = q.1 at hx
  apply Prod.ext hx
  apply Subtype.ext
  have hh : section5CollapseHeight p.1.1 p.2.1 =
      section5CollapseHeight q.1.1 q.2.1 := congrArg (fun r => r.2.1) he
  change q.1.1 ≠ 0 ∨ 1 < q.2.1 at hq
  rw [← hx] at hh hq
  exact section5CollapseHeight_injective_off_segment hp hq hh

/-- The sole collapsed fiber is the distinguished segment. -/
theorem section5RectangleCollapse_eq_origin_iff (p : Section5CollapseRectangle) :
    (section5RectangleCollapse p).1.1 = 0 ∧ (section5RectangleCollapse p).2.1 = 0 ↔
      p.1.1 = 0 ∧ p.2.1 ≤ 1 := by
  change p.1.1 = 0 ∧ section5CollapseHeight p.1.1 p.2.1 = 0 ↔ _
  rw [section5CollapseHeight_eq_zero_iff p.2.2.1]
  constructor
  · rintro ⟨hx, hy | ⟨_, hy⟩⟩
    · exact ⟨hx, by rw [hy]; norm_num⟩
    · exact ⟨hx, hy⟩
  · rintro ⟨hx, hy⟩
    exact ⟨hx, Or.inr ⟨hx, hy⟩⟩

/-- The fiber over the bottom endpoint is the vertical segment. -/
theorem section5RectangleCollapse_fiber (p : Section5CollapseRectangle) :
    section5RectangleCollapse p = section5RectangleOrigin ↔ p.1.1 = 0 ∧ p.2.1 ≤ 1 := by
  rw [← section5RectangleCollapse_eq_origin_iff]
  constructor
  · intro he
    exact ⟨congrArg (fun q : Section5CollapseRectangle => q.1.1) he,
      congrArg (fun q : Section5CollapseRectangle => q.2.1) he⟩
  · rintro ⟨hx, hy⟩
    exact Prod.ext (Subtype.ext hx) (Subtype.ext hy)

/-- The straight homotopy from the identity to the contraction. -/
noncomputable def section5RectangleCollapseHomotopy :
    C(unitInterval × Section5CollapseRectangle, Section5CollapseRectangle) where
  toFun p := (p.2.1, ⟨(1 - p.1.1) * p.2.2.1 +
    p.1.1 * section5CollapseHeight p.2.1.1 p.2.2.1, by
      have h := section5CollapseHeight_mem p.2.1.2 p.2.2.2
      constructor
      · exact add_nonneg (mul_nonneg (sub_nonneg.mpr p.1.2.2) p.2.2.2.1)
          (mul_nonneg p.1.2.1 h.1)
      · nlinarith [mul_nonneg (sub_nonneg.mpr p.1.2.2) (sub_nonneg.mpr p.2.2.2.2),
          mul_nonneg p.1.2.1 (sub_nonneg.mpr h.2)]⟩)
  continuous_toFun := by
    apply (continuous_fst.comp continuous_snd).prodMk
    apply Continuous.subtype_mk
    have ht : Continuous (fun p : unitInterval × Section5CollapseRectangle => p.1.1) :=
      continuous_subtype_val.comp continuous_fst
    have hx : Continuous (fun p : unitInterval × Section5CollapseRectangle => p.2.1.1) :=
      continuous_subtype_val.comp (continuous_fst.comp continuous_snd)
    have hy : Continuous (fun p : unitInterval × Section5CollapseRectangle => p.2.2.1) :=
      continuous_subtype_val.comp (continuous_snd.comp continuous_snd)
    exact ((continuous_const.sub ht).mul hy).add
      (ht.mul (continuous_section5CollapseHeight.comp (hx.prodMk hy)))

/-- The straight homotopy starts at the identity. -/
theorem section5RectangleCollapseHomotopy_zero (p : Section5CollapseRectangle) :
    section5RectangleCollapseHomotopy (0, p) = p := by
  refine Prod.ext ?_ ?_
  · rfl
  apply Subtype.ext
  simp [section5RectangleCollapseHomotopy]

/-- The straight homotopy ends at the contraction. -/
theorem section5RectangleCollapseHomotopy_one (p : Section5CollapseRectangle) :
    section5RectangleCollapseHomotopy (1, p) = section5RectangleCollapse p := by
  refine Prod.ext ?_ ?_
  · rfl
  apply Subtype.ext
  simp [section5RectangleCollapseHomotopy, section5RectangleCollapse]

/-- Every stage of the homotopy fixes all four boundary sides. -/
theorem section5RectangleCollapseHomotopy_boundary (p : Section5CollapseRectangle)
    (hb : p.1.1 = -1 ∨ p.1.1 = 1 ∨ p.2.1 = 0 ∨ p.2.1 = 2) (t : unitInterval) :
    section5RectangleCollapseHomotopy (t, p) = p := by
  refine Prod.ext ?_ ?_
  · rfl
  apply Subtype.ext
  change (1 - t.1) * p.2.1 + t.1 * section5CollapseHeight p.1.1 p.2.1 = p.2.1
  rw [section5CollapseHeight_boundary p.1.2 p.2.2 hb]
  ring

private theorem collapseHeight_monotone (x : ℝ) : Monotone (section5CollapseHeight x) := by
  intro y z hyz
  unfold section5CollapseHeight
  apply max_le_max
  · exact div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_left hyz (mul_nonneg (by norm_num) (abs_nonneg x)))
      (by positivity)
  · linarith only [hyz]

/-- Before the final instant, the rectangular collapse homotopy
is injective. Its height has a strictly positive identity term and
a nondecreasing collapse term. -/
theorem section5RectangleCollapseHomotopy_injective (t : unitInterval) (ht : t < 1) :
    Function.Injective (fun p => section5RectangleCollapseHomotopy (t, p)) := by
  intro p q heq
  have hx₀ := congrArg (fun r : Section5CollapseRectangle => r.1) heq
  have hx : p.1 = q.1 := hx₀
  apply Prod.ext hx
  apply Subtype.ext
  have hh := congrArg (fun r : Section5CollapseRectangle => r.2.1) heq
  change (1 - t.val) * p.2.val + t.val * section5CollapseHeight p.1.val p.2.val =
    (1 - t.val) * q.2.val + t.val * section5CollapseHeight q.1.val q.2.val at hh
  rw [← hx] at hh
  have htime : 0 < 1 - t.val := sub_pos.mpr ht
  have hmono := collapseHeight_monotone p.1.val
  rcases lt_trichotomy p.2.val q.2.val with hlt | he | hgt
  · have hinc := mul_lt_mul_of_pos_left hlt htime
    have hnondec := mul_le_mul_of_nonneg_left (hmono hlt.le) t.2.1
    linarith only [hh, hinc, hnondec]
  · exact he
  · have hinc := mul_lt_mul_of_pos_left hgt htime
    have hnondec := mul_le_mul_of_nonneg_left (hmono hgt.le) t.2.1
    linarith only [hh, hinc, hnondec]

/-- At every instant the rectangular homotopy is injective away
from the distinguished segment. At the last instant this is the
previously proved exceptional-fibre calculation. -/
theorem section5RectangleCollapseHomotopy_injOn (t : unitInterval) :
    InjOn (fun p => section5RectangleCollapseHomotopy (t, p))
      {p | p.1.1 ≠ 0 ∨ 1 < p.2.1} := by
  rcases eq_or_lt_of_le t.2.2 with ht | ht
  · have ht' : t = 1 := Subtype.ext ht
    simp only [ht', section5RectangleCollapseHomotopy_one]
    exact section5RectangleCollapse_injOn
  · exact (section5RectangleCollapseHomotopy_injective t ht).injOn

/-- Every stage maps onto the rectangle. Each vertical interval
has its endpoints fixed, so the intermediate value theorem supplies
all its heights, including at the final collapsed stage. -/
theorem section5RectangleCollapseHomotopy_surjective (t : unitInterval) :
    Function.Surjective (fun p => section5RectangleCollapseHomotopy (t, p)) := by
  intro p
  let f : ℝ → ℝ := fun y => (1 - t.val) * y + t.val * section5CollapseHeight p.1.val y
  have hc : Continuous f := by
    have hheight : Continuous (section5CollapseHeight p.1.val) :=
      continuous_section5CollapseHeight.comp (continuous_const.prodMk continuous_id)
    exact (continuous_const.mul continuous_id).add (continuous_const.mul hheight)
  have h0 : f 0 = 0 := by
    rw [show f 0 = (1 - t.val) * 0 + t.val * section5CollapseHeight p.1.val 0 from rfl,
      section5CollapseHeight_boundary p.1.2 (by norm_num) (Or.inr (Or.inr (Or.inl rfl)))]
    ring
  have h2 : f 2 = 2 := by
    rw [show f 2 = (1 - t.val) * 2 + t.val * section5CollapseHeight p.1.val 2 from rfl,
      section5CollapseHeight_boundary p.1.2 (by norm_num) (Or.inr (Or.inr (Or.inr rfl)))]
    ring
  obtain ⟨y, hy, he⟩ := intermediate_value_Icc (by norm_num : (0 : ℝ) ≤ 2)
    hc.continuousOn (show p.2.val ∈ Icc (f 0) (f 2) by rw [h0, h2]; exact p.2.2)
  exact ⟨(p.1, ⟨y, hy⟩), Prod.ext rfl (Subtype.ext he)⟩

end GraphMinor.GM06
