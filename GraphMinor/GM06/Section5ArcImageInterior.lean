module

public import GraphMinor.GM06.Defs
import GraphMinor.GM06.Section5RegionInterior
import GraphMinor.Surface.DiscRemove
import GraphMinor.GM11.Ties
import GraphMinor.GM11.PerimeterPull
import Mathlib.Topology.Homeomorph.Lemmas

/-!
# Compact injective curve pieces have no surface interior

The Reduction 2 avoidance argument in VI (5.5), page 130, chooses
points outside a simplified curve. A compact part on which a curve
is injective cannot contain an O-arc, since its inverse embeds that
O-arc in the unit interval. Every nonempty open part of the cylinder
contains a closed disc and hence an O-arc. Thus such a curve piece
has empty interior in the cylinder.
-/

public section
namespace GraphMinor.GM06
open Set Topology GraphMinor.Surface

/-- A compact injective part of an interval curve contains no O-arc. -/
theorem not_isOArc_subset_image_compact_injOn
    {S : Type*} [TopologicalSpace S] [T2Space S]
    (f : C(unitInterval, S)) {K : Set unitInterval} (hK : IsCompact K)
    (hi : InjOn f K) {J : Set S} (hJ : IsOArc J) (hJK : J ⊆ f '' K) : False := by
  let : CompactSpace K := isCompact_iff_compactSpace.mp hK
  let F : K → S := fun x => f x.1
  have hFc : Continuous F := f.continuous.comp continuous_subtype_val
  have hFi : Function.Injective F := fun x y h => Subtype.ext (hi x.2 y.2 h)
  let e : K ≃ₜ range F := Continuous.homeoOfEquivCompactToT2
    (f := Equiv.ofInjective F hFi) hFc.rangeFactorization
  obtain ⟨c⟩ := hJ
  have hcR (z : Circle) : (c z).1 ∈ range F := by
    obtain ⟨t, htK, htf⟩ := hJK (c z).2
    exact ⟨⟨t, htK⟩, htf⟩
  let j : Circle → unitInterval := fun z => (e.symm ⟨(c z).1, hcR z⟩).1
  have hjc : Continuous j := by fun_prop
  have hjf (z) : f (j z) = (c z).1 :=
    congrArg Subtype.val (e.apply_symm_apply ⟨(c z).1, hcR z⟩)
  have hji : Function.Injective j := by
    intro z w he
    apply c.injective
    apply Subtype.ext
    exact (hjf z).symm.trans ((congrArg f he).trans (hjf w))
  have hJ' : IsOArc (range j) :=
    ⟨Continuous.homeoOfEquivCompactToT2 (f := Equiv.ofInjective j hji) hjc.rangeFactorization⟩
  have hI : IsLine (univ : Set unitInterval) := ⟨(Homeomorph.Set.univ unitInterval).symm⟩
  exact GraphMinor.GM11.not_isOArc_of_subset_line hI hJ' (subset_univ _)

/-- A subset of the cylinder containing no O-arc has empty interior. -/
theorem interior_eq_empty_of_no_oArc_subset
    {K : Set ClosedCylinder} (hK : ∀ J : Set ClosedCylinder, IsOArc J → J ⊆ K → False) :
    interior K = ∅ := by
  apply eq_empty_iff_forall_notMem.mpr
  intro x hx
  have hcl : x ∈ closure (interior K \ bd ClosedCylinder) :=
    (closure_sdiff_boundary_of_isOpen isSurface_closedCylinder isOpen_interior).symm ▸ subset_closure hx
  obtain ⟨y, _, hyK, hybd⟩ := mem_closure_iff.mp hcl univ isOpen_univ (mem_univ x)
  have hy : IsInteriorPoint y := by by_contra h; exact hybd h
  obtain ⟨U, h, g, c, hU, _⟩ := hy.exists_ballChart isOpen_interior hyK (R := 2) (by norm_num)
  have hsub : Metric.closedBall (0 : ℂ) 1 ⊆ Metric.ball 0 2 := Metric.closedBall_subset_ball (by norm_num)
  have hsmall : IsClosedDisc (Metric.closedBall (0 : ℂ) 1) :=
    (isClosedDisc_of_convex (convex_closedBall 0 1) (by
      rw [interior_closedBall _ one_ne_zero]
      exact ⟨0, by simp⟩) Metric.isBounded_closedBall Metric.isClosed_closedBall).1
  let D := g '' Metric.closedBall (0 : ℂ) 1
  have hD : IsClosedDisc D := (c.image_disc hsmall hsub).1
  have hDK : D ⊆ interior K := by
    rintro _ ⟨z, hz, rfl⟩
    exact hU (c.gm (hsub hz))
  exact hK (discBd D) hD.isOArc_discBd ((discBd_subset D).trans (hDK.trans interior_subset))

/-- A compact injective part of a cylinder curve has empty interior. -/
theorem interior_image_compact_injOn_curve_eq_empty
    (f : Curve ClosedCylinder) {K : Set unitInterval} (hK : IsCompact K) (hi : InjOn f K) :
    interior (f '' K) = ∅ :=
  interior_eq_empty_of_no_oArc_subset (fun _ hJ hsub => not_isOArc_subset_image_compact_injOn f hK hi hJ hsub)

end GraphMinor.GM06
