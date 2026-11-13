module

public import GraphMinor.GM06.Section5CollapseGlue
import Mathlib.Tactic

/-!
# Transferring the contraction through a chart

In Reduction 3 of VI, page 129, the local rectangle contraction is
extended by the identity outside its chart. The whole homotopy is
pasted at once. Hence it starts at the identity and fixes every
specified point whose chart coordinates lie on a boundary side.
-/

public section

namespace GraphMinor.GM06

open Set

/-- A rectangular chart transfers the contraction and its homotopy to
the ambient space. Points outside the chart and specified boundary
points stay fixed throughout. -/
theorem exists_rectangle_contraction_in_chart
    {S : Type*} [TopologicalSpace S] {D B : Set S} (hD : IsClosed D)
    (e : Section5CollapseRectangle ≃ₜ D)
    (hfront : ∀ z, (e z).1 ∈ frontier D →
      z.1.1 = -1 ∨ z.1.1 = 1 ∨ z.2.1 = 0 ∨ z.2.1 = 2)
    (hB : ∀ z, (e z).1 ∈ B →
      z.1.1 = -1 ∨ z.1.1 = 1 ∨ z.2.1 = 0 ∨ z.2.1 = 2) :
    ∃ (π : C(S, S)) (H : C(unitInterval × S, S)),
      (∀ x, H (0, x) = x) ∧
      (∀ x, H (1, x) = π x) ∧
      (∀ x ∈ B, ∀ t, H (t, x) = x) ∧
      (∀ z, π (e z).1 = (e (section5RectangleCollapse z)).1) ∧
      (∀ x ∉ D, ∀ t, H (t, x) = x) ∧
      (∀ t z, H (t, (e z).1) = (e (section5RectangleCollapseHomotopy (t, z))).1) := by
  obtain ⟨H, hHchart, hHout⟩ := exists_continuous_glue_of_closed_rectangle hD e
    section5RectangleCollapseHomotopy (fun t z hz =>
      section5RectangleCollapseHomotopy_boundary z (hfront z hz) t)
  let π : C(S, S) := ⟨fun x => H (1, x),
    H.continuous.comp (continuous_const.prodMk continuous_id)⟩
  have hpoint (x : S) (hx : x ∈ D) : ∃ z, (e z).1 = x :=
    ⟨e.symm ⟨x, hx⟩, congrArg Subtype.val (e.apply_symm_apply ⟨x, hx⟩)⟩
  refine ⟨π, H, ?_, fun _ => rfl, ?_, ?_, ?_, hHchart⟩
  · intro x
    by_cases hx : x ∈ D
    · obtain ⟨z, rfl⟩ := hpoint x hx
      rw [hHchart, section5RectangleCollapseHomotopy_zero]
    · exact hHout 0 x hx
  · intro x hx t
    by_cases hxD : x ∈ D
    · obtain ⟨z, rfl⟩ := hpoint x hxD
      rw [hHchart, section5RectangleCollapseHomotopy_boundary z (hB z hx) t]
    · exact hHout t x hxD
  · intro z
    change H (1, (e z).1) = _
    rw [hHchart, section5RectangleCollapseHomotopy_one]
  · intro x hx t
    exact hHout t x hx

end GraphMinor.GM06
