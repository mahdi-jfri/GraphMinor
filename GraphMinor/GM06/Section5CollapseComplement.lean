module

public import GraphMinor.GM06.Section5CollapseRectangle
public import Mathlib.Topology.Homeomorph.Defs
import Mathlib.Topology.Homeomorph.Lemmas
import Mathlib.Topology.LocalAtTarget
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Tactic

/-!
# The contraction off its collapsed segment

The rectangle contraction used for Reduction 3 of VI, page 129, is a
homeomorphism from the complement of the distinguished segment onto
the punctured rectangle. Its restriction is continuous, closed, and
bijective: closedness follows by restricting the continuous map of
the compact rectangle.
-/

public section

namespace GraphMinor.GM06

open Set

/-- The coordinate contraction restricts to a homeomorphism off its
collapsed segment, as required by Reduction 3. -/
theorem section5RectangleCollapse_homeomorph_off_segment :
    Nonempty ({p : Section5CollapseRectangle // p.1.1 ≠ 0 ∨ 1 < p.2.1} ≃ₜ
      {p : Section5CollapseRectangle // ¬ (p.1.1 = 0 ∧ p.2.1 = 0)}) := by
  classical
  let B : Set Section5CollapseRectangle := {p | ¬ (p.1.1 = 0 ∧ p.2.1 = 0)}
  let A : Set Section5CollapseRectangle := {p | p.1.1 ≠ 0 ∨ 1 < p.2.1}
  have hpre : section5RectangleCollapse ⁻¹' B = A := by
    ext p
    change ¬ ((section5RectangleCollapse p).1.1 = 0 ∧
      (section5RectangleCollapse p).2.1 = 0) ↔ _
    rw [section5RectangleCollapse_eq_origin_iff]
    simp only [not_and_or, not_le]
    rfl
  let f := B.restrictPreimage section5RectangleCollapse
  have hf : Function.Bijective f := by
    constructor
    · intro p q he
      apply Subtype.ext
      apply section5RectangleCollapse_injOn
      · change p.1 ∈ A
        rw [← hpre]
        exact p.2
      · change q.1 ∈ A
        rw [← hpre]
        exact q.2
      · exact congrArg Subtype.val he
    · intro y
      obtain ⟨p, hp⟩ := section5RectangleCollapse_surjective y.1
      refine ⟨⟨p, ?_⟩, Subtype.ext hp⟩
      change section5RectangleCollapse p ∈ B
      rw [hp]
      exact y.2
  let e := Equiv.ofBijective f hf
  have hc : Continuous f := section5RectangleCollapse.continuous.restrictPreimage
  have hcl : IsClosedMap f := section5RectangleCollapse.continuous.isClosedMap.restrictPreimage B
  exact ⟨(Homeomorph.setCongr hpre.symm).trans (e.toHomeomorphOfContinuousClosed hc hcl)⟩

/-- A point off the collapsed segment has exactly one preimage. -/
theorem section5RectangleCollapse_unique_preimage
    {p q : Section5CollapseRectangle} (hq : q.1.1 ≠ 0 ∨ 1 < q.2.1)
    (he : section5RectangleCollapse p = section5RectangleCollapse q) : p = q := by
  have hp : p.1.1 ≠ 0 ∨ 1 < p.2.1 := by
    by_contra hn
    have hp0 : p.1.1 = 0 ∧ p.2.1 ≤ 1 := by
      simpa only [not_or, not_not, not_lt] using hn
    have hpz := (section5RectangleCollapse_eq_origin_iff p).mpr hp0
    rw [he] at hpz
    have hq0 := (section5RectangleCollapse_eq_origin_iff q).mp hpz
    exact hq.elim (fun h => h hq0.1) (fun h => (not_lt_of_ge hq0.2) h)
  exact section5RectangleCollapse_injOn hp hq he

/-- An open set missing the collapsed segment has open image. This is
the local openness condition in Reduction 3. -/
theorem section5RectangleCollapse_isOpen_image
    {U : Set Section5CollapseRectangle} (hU : IsOpen U)
    (hUA : ∀ p ∈ U, p.1.1 ≠ 0 ∨ 1 < p.2.1) :
    IsOpen (section5RectangleCollapse '' U) := by
  have hq := section5RectangleCollapse.continuous.isClosedMap.isQuotientMap
    section5RectangleCollapse.continuous section5RectangleCollapse_surjective
  rw [← hq.isCoinducing.isOpen_preimage]
  have hsat : section5RectangleCollapse ⁻¹' (section5RectangleCollapse '' U) = U := by
    ext p
    constructor
    · rintro ⟨q, hqU, he⟩
      have hpq := section5RectangleCollapse_unique_preimage (hUA q hqU) he.symm
      exact hpq.symm ▸ hqU
    · exact fun hp => ⟨p, hp, rfl⟩
  rw [hsat]
  exact hU

end GraphMinor.GM06
