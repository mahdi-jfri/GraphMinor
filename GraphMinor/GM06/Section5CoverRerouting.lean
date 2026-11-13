module

public import GraphMinor.GM06.Defs
import GraphMinor.GM06.Section5CoverCurve
import GraphMinor.GM06.Section5HelixConcatenation
import GraphMinor.GM06.Section4Winding
import GraphMinor.GM07.ForestFlat
import GraphMinor.GM07.Section3
import GraphMinor.GM07.CuffForest
import GraphMinor.GM11.Ties

/-!
# Winding of a rerouting with its lifted contact fixed

For the one-path correction of VI Reduction 4, the new prefix must reach
the same lift of its contact vertex as the old prefix. Both prefixes
can be joined to the same old tail. Curves in a path drawing with
the same ends are homotopic, so the two concatenations compute the
old and new winding. The fixed lifted contact makes those windings
equal, without assuming a winding identity in the reduction data.
-/

public section
namespace GraphMinor.GM06
open Set Real GraphMinor.Surface

private theorem path_point_set_flat {P : Drawing ClosedCylinder} {s t : ClosedCylinder}
    (hP : IsPathDrawing P s t) : GM11.IsFlat P.U := by
  obtain ⟨f, hf⟩ := hP.2
  let e : unitInterval ≃ₜ range f := Continuous.homeoOfEquivCompactToT2
    (f := Equiv.ofInjective f hf.1) f.continuous.rangeFactorization
  have hline : IsLine P.U := ⟨e.trans (Homeomorph.setCongr hf.2.1)⟩
  apply GM07.isFlat_forest (G := P)
  exact GM07.isForest_of_noOArc fun F hF hFP => GM11.not_isOArc_of_subset_line hline hF hFP

private theorem windingNumber_eq_add_in_path
    {P : Drawing ClosedCylinder} {s v t : ClosedCylinder}
    (hP : IsPathDrawing P s t) (f : Curve ClosedCylinder)
    (hf : range f ⊆ P.U) (hf0 : f 0 = s) (hf1 : f 1 = t)
    (q : Path s v) (r : Path v t) (hq : range q ⊆ P.U) (hr : range r ⊆ P.U) :
    windingNumber f = windingNumber q.toContinuousMap + windingNumber r.toContinuousMap := by
  have hqr : range (q.trans r).toContinuousMap ⊆ P.U := by
    change range (q.trans r) ⊆ P.U
    rw [Path.trans_range]
    exact union_subset hq hr
  have hhom := GM07.IsFlat.curvesHomotopic (path_point_set_flat hP) hf hqr
    (hf0.trans (Path.source _).symm) (hf1.trans (Path.target _).symm)
  exact (windingNumber_eq_of_homotopic hhom).trans (windingNumber_path_trans q r)

/-- Rerouting a prefix to a lifted contact shifted by d full turns
changes winding by d. The old and new full curves are path drawings
with the same tail. This gives the winding increment in VI (5.1),
page 129, as well as preservation for corrected Reduction 4. -/
theorem windingNumber_eq_add_of_rerouting_lifted_contact
    {P R : Drawing ClosedCylinder} {s v t : ClosedCylinder}
    (hP : IsPathDrawing P s t) (hR : IsPathDrawing R s t)
    (f g : Curve ClosedCylinder)
    (hf : ParametrizesSet f P.U s t) (hg : ParametrizesSet g R.U s t)
    (q : Path s v) (r : Path v t)
    (hqR : range q ⊆ R.U) (hrR : range r ⊆ R.U) (hrP : range r ⊆ P.U)
    (u : unitInterval) (hu : f u = v) (a : ℝ) (ha : Circle.exp a = s.1.2) (d : ℝ)
    (hend : (cylinderCurveLiftAt q.toContinuousMap a 1).2 =
      (cylinderCurveLiftAt f a u).2 + 2 * π * d) :
    windingNumber g = windingNumber f + d := by
  let p : Path s v := ⟨GM07.subPathSeg f 0 u,
    (GM07.subPathSeg_zero f 0 u).trans hf.2.2.1,
    (GM07.subPathSeg_one f 0 u).trans hu⟩
  have hpP : range p ⊆ P.U := by
    exact (GM07.range_subPathSeg_subset f 0 u).trans (hf.2.1 ▸ Subset.rfl)
  have hold := windingNumber_eq_add_in_path hP f (hf.2.1 ▸ Subset.rfl)
    hf.2.2.1 hf.2.2.2 p r hpP hrP
  have hnew := windingNumber_eq_add_in_path hR g (hg.2.1 ▸ Subset.rfl)
    hg.2.2.1 hg.2.2.2 q r hqR hrR
  have haq : Circle.exp a = (q 0).1.2 := by rw [Path.source]; exact ha
  have haf : Circle.exp a = (f 0).1.2 := by rw [hf.2.2.1]; exact ha
  let α : C(unitInterval, ℝ) :=
    ⟨fun x => (cylinderCurveLiftAt f a x).2,
      continuous_snd.comp (cylinderCurveLiftAt f a).continuous⟩
  have hα (x : unitInterval) : Circle.exp (α x) = (f x).1.2 :=
    congrArg (fun z : ClosedCylinder => z.1.2) (cylinderCoverProjection_curveLiftAt f a haf x)
  have hpq : windingNumber q.toContinuousMap = windingNumber p.toContinuousMap + d := by
    rw [windingNumber_eq_curveLiftAt q.toContinuousMap a haq]
    change _ = windingNumber (GM07.subPathSeg f 0 u) + d
    rw [windingNumber_subPathSeg_of_exp_lift α hα]
    change _ = ((cylinderCurveLiftAt f a u).2 - (cylinderCurveLiftAt f a 0).2) / (2 * π) + d
    rw [cylinderCurveLiftAt_zero, hend]
    field_simp [pi_ne_zero]
    ring
  rw [hnew, hold, hpq]
  ring


/-- Rerouting a prefix to the same lifted contact preserves winding.
The old and new full curves lie in path drawings, and the same tail
joins the contact to their common terminal vertex. These are the
geometric data used in the side correction of VI Reduction 4, page 129. -/
theorem windingNumber_eq_of_rerouting_lifted_contact
    {P R : Drawing ClosedCylinder} {s v t : ClosedCylinder}
    (hP : IsPathDrawing P s t) (hR : IsPathDrawing R s t)
    (f g : Curve ClosedCylinder)
    (hf : ParametrizesSet f P.U s t) (hg : ParametrizesSet g R.U s t)
    (q : Path s v) (r : Path v t)
    (hqR : range q ⊆ R.U) (hrR : range r ⊆ R.U) (hrP : range r ⊆ P.U)
    (u : unitInterval) (hu : f u = v) (a : ℝ) (ha : Circle.exp a = s.1.2)
    (hend : (cylinderCurveLiftAt q.toContinuousMap a 1).2 =
      (cylinderCurveLiftAt f a u).2) :
    windingNumber g = windingNumber f := by
  have hend' : (cylinderCurveLiftAt q.toContinuousMap a 1).2 =
      (cylinderCurveLiftAt f a u).2 + 2 * π * (0 : ℝ) := by simpa using hend
  have h := windingNumber_eq_add_of_rerouting_lifted_contact hP hR f g hf hg q r hqR hrR hrP u hu a ha 0 hend'
  simpa using h

end GraphMinor.GM06
