module

public import GraphMinor.GM06.Section5CollapseInChart
import GraphMinor.GM06.Section5CollapseComplement
import Mathlib.Topology.LocalAtTarget
import Mathlib.Topology.Homeomorph.Lemmas
import Mathlib.Tactic

/-!
# Fibers of the contraction in a chart

The local contraction in Reduction 3 of VI, page 129, maps its chart
onto itself and is the identity outside. Thus the ambient map is
surjective. Two points off the collapsed segment have distinct images:
inside the chart this is the coordinate injectivity theorem, and a
point outside cannot have the same image as a point inside.
-/

public section

namespace GraphMinor.GM06

open Set

/-- Extending the rectangular contraction by the identity preserves
surjectivity. -/
theorem surjective_of_rectangle_collapse_in_chart
    {S : Type*} [TopologicalSpace S] {D : Set S}
    (e : Section5CollapseRectangle ≃ₜ D) (π : S → S)
    (hchart : ∀ z, π (e z).1 = (e (section5RectangleCollapse z)).1)
    (hout : ∀ x ∉ D, π x = x) : Function.Surjective π := by
  intro y
  by_cases hy : y ∈ D
  · let z := e.symm ⟨y, hy⟩
    obtain ⟨w, hw⟩ := section5RectangleCollapse_surjective z
    refine ⟨(e w).1, ?_⟩
    rw [hchart, hw]
    exact congrArg Subtype.val (e.apply_symm_apply ⟨y, hy⟩)
  · exact ⟨y, hout y hy⟩

/-- The ambient contraction is injective outside the image of the
vertical segment in its rectangular chart. -/
theorem injOn_of_rectangle_collapse_in_chart
    {S : Type*} [TopologicalSpace S] {D : Set S}
    (e : Section5CollapseRectangle ≃ₜ D) (π : S → S)
    (hchart : ∀ z, π (e z).1 = (e (section5RectangleCollapse z)).1)
    (hout : ∀ x ∉ D, π x = x) :
    InjOn π ((fun z => (e z).1) '' {z | z.1.1 = 0 ∧ z.2.1 ≤ 1})ᶜ := by
  have hpoint (x : S) (hx : x ∈ D) : ∃ z, (e z).1 = x :=
    ⟨e.symm ⟨x, hx⟩, congrArg Subtype.val (e.apply_symm_apply ⟨x, hx⟩)⟩
  intro x hx y hy he
  by_cases hxD : x ∈ D
  · obtain ⟨z, rfl⟩ := hpoint x hxD
    by_cases hyD : y ∈ D
    · obtain ⟨w, rfl⟩ := hpoint y hyD
      rw [hchart, hchart] at he
      have hzw : section5RectangleCollapse z = section5RectangleCollapse w :=
        e.injective (Subtype.ext he)
      have hz : z.1.1 ≠ 0 ∨ 1 < z.2.1 := by
        by_contra hn
        have hh : z.1.1 = 0 ∧ z.2.1 ≤ 1 := by
          simpa only [not_or, not_not, not_lt] using hn
        exact hx ⟨z, hh, rfl⟩
      have hw : w.1.1 ≠ 0 ∨ 1 < w.2.1 := by
        by_contra hn
        have hh : w.1.1 = 0 ∧ w.2.1 ≤ 1 := by
          simpa only [not_or, not_not, not_lt] using hn
        exact hy ⟨w, hh, rfl⟩
      exact congrArg (fun q => (e q).1) (section5RectangleCollapse_injOn hz hw hzw)
    · rw [hchart, hout y hyD] at he
      exact False.elim (hyD (he ▸ (e (section5RectangleCollapse z)).2))
  · rw [hout x hxD] at he
    by_cases hyD : y ∈ D
    · obtain ⟨w, rfl⟩ := hpoint y hyD
      rw [hchart] at he
      exact False.elim (hxD (he.symm ▸ (e (section5RectangleCollapse w)).2))
    · rwa [hout y hyD] at he

/-- The fiber of the pasted contraction over the distinguished
boundary endpoint is exactly the drawn segment in the chart. -/
theorem fiber_of_rectangle_collapse_in_chart
    {S : Type*} [TopologicalSpace S] {D : Set S}
    (e : Section5CollapseRectangle ≃ₜ D) (π : S → S)
    (hchart : ∀ z, π (e z).1 = (e (section5RectangleCollapse z)).1)
    (hout : ∀ x ∉ D, π x = x) :
    π ⁻¹' {(e section5RectangleOrigin).1} =
      (fun z => (e z).1) '' {z | z.1.1 = 0 ∧ z.2.1 ≤ 1} := by
  ext x
  constructor
  · intro hx
    have heq : π x = (e section5RectangleOrigin).1 := hx
    have hxD : x ∈ D := by
      by_contra hn
      rw [hout x hn] at heq
      exact hn (heq.symm ▸ (e section5RectangleOrigin).2)
    let z := e.symm ⟨x, hxD⟩
    have hz : (e z).1 = x := congrArg Subtype.val (e.apply_symm_apply ⟨x, hxD⟩)
    have hπ : (e (section5RectangleCollapse z)).1 = (e section5RectangleOrigin).1 := by
      rw [← hchart, hz]
      exact heq
    have hz0 := (section5RectangleCollapse_fiber z).mp (e.injective (Subtype.ext hπ))
    exact ⟨z, hz0, hz⟩
  · rintro ⟨z, hz, rfl⟩
    change π (e z).1 = (e section5RectangleOrigin).1
    rw [hchart, (section5RectangleCollapse_fiber z).mpr hz]

/-- On a compact Hausdorff ambient space the pasted contraction is a
homeomorphism off the segment. The restricted map is closed and
bijective, as in the local rectangle calculation. -/
theorem homeomorph_off_segment_of_rectangle_collapse_in_chart
    {S : Type*} [TopologicalSpace S] [CompactSpace S] [T2Space S] {D : Set S}
    (e : Section5CollapseRectangle ≃ₜ D) (π : C(S, S))
    (hchart : ∀ z, π (e z).1 = (e (section5RectangleCollapse z)).1)
    (hout : ∀ x ∉ D, π x = x) :
    Nonempty ({x : S // x ∉ (fun z => (e z).1) '' {z | z.1.1 = 0 ∧ z.2.1 ≤ 1}} ≃ₜ
      {y : S // y ≠ (e section5RectangleOrigin).1}) := by
  classical
  let B : Set S := {(e section5RectangleOrigin).1}ᶜ
  let E := (fun z => (e z).1) '' {z | z.1.1 = 0 ∧ z.2.1 ≤ 1}
  have hpre : π ⁻¹' B = Eᶜ := by
    rw [preimage_compl, fiber_of_rectangle_collapse_in_chart e π hchart hout]
  let f := B.restrictPreimage π
  have hf : Function.Bijective f := by
    constructor
    · intro x y he
      apply Subtype.ext
      apply injOn_of_rectangle_collapse_in_chart e π hchart hout
      · change x.1 ∈ Eᶜ
        rw [← hpre]
        exact x.2
      · change y.1 ∈ Eᶜ
        rw [← hpre]
        exact y.2
      · exact congrArg Subtype.val he
    · intro y
      obtain ⟨x, hx⟩ := surjective_of_rectangle_collapse_in_chart e π hchart hout y.1
      refine ⟨⟨x, ?_⟩, Subtype.ext hx⟩
      change π x ∈ B
      rw [hx]
      exact y.2
  let eqv := Equiv.ofBijective f hf
  have hc : Continuous f := π.continuous.restrictPreimage
  have hcl : IsClosedMap f := π.continuous.isClosedMap.restrictPreimage B
  exact ⟨(Homeomorph.setCongr hpre.symm).trans (eqv.toHomeomorphOfContinuousClosed hc hcl)⟩

/-- Every stage of the pasted rectangular homotopy is surjective.
Inside the chart this is the vertical interval calculation. Outside
it every point remains fixed. -/
theorem surjective_of_rectangle_homotopy_in_chart
    {S : Type*} [TopologicalSpace S] {D : Set S}
    (e : Section5CollapseRectangle ≃ₜ D)
    (H : unitInterval × S → S)
    (hchart : ∀ t z, H (t, (e z).val) = (e (section5RectangleCollapseHomotopy (t, z))).val)
    (hout : ∀ x ∉ D, ∀ t, H (t, x) = x) (t : unitInterval) :
    Function.Surjective (fun x => H (t, x)) := by
  intro y
  by_cases hy : y ∈ D
  · obtain ⟨z, hz⟩ := section5RectangleCollapseHomotopy_surjective t (e.symm ⟨y, hy⟩)
    change section5RectangleCollapseHomotopy (t, z) = e.symm ⟨y, hy⟩ at hz
    refine ⟨(e z).val, ?_⟩
    change H (t, (e z).val) = y
    rw [hchart, hz]
    exact congrArg Subtype.val (e.apply_symm_apply ⟨y, hy⟩)
  · exact ⟨y, hout y hy t⟩

/-- Before the final instant the pasted rectangular homotopy is
injective on the whole surface. A point inside the chart stays
inside it and cannot meet any fixed point outside. -/
theorem injective_of_rectangle_homotopy_in_chart
    {S : Type*} [TopologicalSpace S] {D : Set S}
    (e : Section5CollapseRectangle ≃ₜ D)
    (H : unitInterval × S → S)
    (hchart : ∀ t z, H (t, (e z).val) = (e (section5RectangleCollapseHomotopy (t, z))).val)
    (hout : ∀ x ∉ D, ∀ t, H (t, x) = x) (t : unitInterval) (ht : t < 1) :
    Function.Injective (fun x => H (t, x)) := by
  have hpoint (x : S) (hx : x ∈ D) : ∃ z, (e z).val = x :=
    ⟨e.symm ⟨x, hx⟩, congrArg Subtype.val (e.apply_symm_apply ⟨x, hx⟩)⟩
  intro x y heq
  change H (t, x) = H (t, y) at heq
  by_cases hx : x ∈ D
  · obtain ⟨z, rfl⟩ := hpoint x hx
    by_cases hy : y ∈ D
    · obtain ⟨q, rfl⟩ := hpoint y hy
      rw [hchart, hchart] at heq
      have hlocal := e.injective (Subtype.ext heq)
      exact congrArg (fun z => (e z).val)
        (section5RectangleCollapseHomotopy_injective t ht hlocal)
    · rw [hchart, hout y hy t] at heq
      exact False.elim (hy (heq ▸ (e (section5RectangleCollapseHomotopy (t, z))).property))
  · by_cases hy : y ∈ D
    · obtain ⟨q, rfl⟩ := hpoint y hy
      rw [hout x hx t, hchart] at heq
      exact False.elim (hx (heq.symm ▸ (e (section5RectangleCollapseHomotopy (t, q))).property))
    · rwa [hout x hx t, hout y hy t] at heq

/-- A point outside the closed contracted segment has a singleton
fibre throughout the pasted homotopy, even at its final instant.
This gives the separation of a retained chart's centre from its rim. -/
theorem rectangle_homotopy_eq_iff_of_off_segment
    {S : Type*} [TopologicalSpace S] {D : Set S}
    (e : Section5CollapseRectangle ≃ₜ D)
    (H : unitInterval × S → S)
    (hchart : ∀ t z, H (t, (e z).val) = (e (section5RectangleCollapseHomotopy (t, z))).val)
    (hout : ∀ x ∉ D, ∀ t, H (t, x) = x)
    {w : S} (hw : w ∉ (fun z => (e z).val) '' {z | z.1.1 = 0 ∧ z.2.1 ≤ 1})
    (t : unitInterval) (x : S) : H (t, x) = H (t, w) ↔ x = w := by
  constructor
  · intro heq
    rcases eq_or_lt_of_le t.2.2 with ht | ht
    · have ht' : t = 1 := Subtype.ext ht
      subst t
      have hlast : ∀ z, H (1, (e z).val) = (e (section5RectangleCollapse z)).val := by
        intro z
        rw [hchart, section5RectangleCollapseHomotopy_one]
      have hlastOut : ∀ x ∉ D, H (1, x) = x := fun x hx => hout x hx 1
      have hfibre := fiber_of_rectangle_collapse_in_chart e (fun x => H (1, x)) hlast hlastOut
      have hx : x ∉ (fun z => (e z).val) '' {z | z.1.1 = 0 ∧ z.2.1 ≤ 1} := by
        intro hx
        have hx' : H (1, x) = (e section5RectangleOrigin).val :=
          show x ∈ (fun x => H (1, x)) ⁻¹' {(e section5RectangleOrigin).val} from hfibre.symm ▸ hx
        have hw' : w ∈ (fun z => (e z).val) '' {z | z.1.1 = 0 ∧ z.2.1 ≤ 1} := by
          rw [← hfibre]
          exact heq.symm.trans hx'
        exact hw hw'
      exact injOn_of_rectangle_collapse_in_chart e _ hlast hlastOut hx hw heq
    · exact injective_of_rectangle_homotopy_in_chart e H hchart hout t ht heq
  · rintro rfl
    rfl

end GraphMinor.GM06
