module

public import GraphMinor.GM06.Defs
import GraphMinor.GM06.Section5CoverCurve
import GraphMinor.GM06.Section5CoverSides
import GraphMinor.GM06.Section4Winding
import GraphMinor.GM06.Section4
import GraphMinor.Surface.ArcInPath

/-!
# Simplifying a lifted helix

For the discarded-side avoidance in VI (5.5), page 130, a helix
can be replaced by one whose angular-cover lift is injective. The
arc-in-path theorem keeps the two lifted endpoints and stays in the
old lifted range. Normality and winding are therefore preserved.
Injectivity bounds new vertex times by the finite old vertex visits.
-/

public section
namespace GraphMinor.GM06
open Set GraphMinor.Surface

/-- A helix has a representative with an injective angular-cover
lift, the same winding, and no larger vertex count. -/
theorem exists_helix_with_injective_cover_lift
    {k : ℕ} {G : Drawing ClosedCylinder} (f : Curve ClosedCylinder) (hf : IsHelix k G f) :
    ∃ g : Curve ClosedCylinder, ∃ q : C(unitInterval, CylinderCover),
      Function.Injective q ∧ (∀ t, cylinderCoverProjection (q t) = g t) ∧
      IsHelix k G g ∧ windingNumber g = windingNumber f ∧ curveL G g ≤ curveL G f ∧ range g ⊆ range f := by
  let A := cylinderCurveLiftAt f (cylinderAngleLift f 0)
  have hA (t) : cylinderCoverProjection (A t) = f t :=
    cylinderCoverProjection_curveLiftAt f _ (exp_cylinderAngleLift f 0) t
  have hf0r : (f 0).1.1 = 1 := by obtain ⟨j, hj⟩ := hf.2.1; rw [← hj]; rfl
  have hf1r : (f 1).1.1 = 2 := by obtain ⟨j, hj⟩ := hf.2.2.1; rw [← hj]; rfl
  have hAne : A 0 ≠ A 1 := by
    intro he
    have hr := congrArg (fun x : CylinderCover => x.1.1) he
    change (f 0).1.1 = (f 1).1.1 at hr
    rw [hf0r, hf1r] at hr
    norm_num at hr
  obtain ⟨q₀, hqc, hqi, hq0, hq1, hqrange⟩ := exists_arc_of_path A.continuous hAne
  let q : C(unitInterval, CylinderCover) := ⟨q₀, hqc⟩
  have hqinj : Function.Injective q := hqi
  let g : Curve ClosedCylinder := ⟨fun t => cylinderCoverProjection (q t),
    continuous_cylinderCoverProjection.comp q.continuous⟩
  have hproj (t) : cylinderCoverProjection (q t) = g t := rfl
  have hg0 : g 0 = f 0 := (congrArg cylinderCoverProjection hq0).trans (hA 0)
  have hg1 : g 1 = f 1 := (congrArg cylinderCoverProjection hq1).trans (hA 1)
  have hgRange : range g ⊆ range f := by
    rintro _ ⟨t, rfl⟩
    obtain ⟨u, hu⟩ := hqrange (mem_range_self t)
    exact ⟨u, (hA u).symm.trans (congrArg cylinderCoverProjection hu)⟩
  have hnormal : IsNormalCurve G g := fun x hx => hf.1 ⟨hgRange hx.1, hx.2⟩
  have hsub : q '' curveVertexHits G g ⊆ A '' curveVertexHits G f := by
    rintro _ ⟨t, ht, rfl⟩
    obtain ⟨u, hu⟩ := hqrange (mem_range_self t)
    refine ⟨u, ?_, hu⟩
    change f u ∈ G.V
    have he : f u = g t := (hA u).symm.trans (congrArg cylinderCoverProjection hu)
    exact he.symm ▸ ht
  have hnewfin : (curveVertexHits G g).Finite := by
    have himfin := (hf.2.2.2.image A).subset hsub
    have hpre : (q ⁻¹' (q '' curveVertexHits G g)).Finite := himfin.preimage hqinj.injOn
    exact hpre.subset (subset_preimage_image q _)
  have hcard := ncard_le_ncard hsub (hf.2.2.2.image A)
  rw [ncard_image_of_injective _ hqinj] at hcard
  have hcount : curveL G g ≤ curveL G f := hcard.trans (ncard_image_le hf.2.2.2)
  let α : C(unitInterval, ℝ) := ⟨fun t => (q t).2, continuous_snd.comp q.continuous⟩
  let β : C(unitInterval, ℝ) := ⟨fun t => (A t).2, continuous_snd.comp A.continuous⟩
  have hwind : windingNumber g = windingNumber f := by
    rw [windingNumber_eq_of_exp_lift α (fun _ => rfl),
      windingNumber_eq_of_exp_lift β (fun t => congrArg (fun x : ClosedCylinder => x.1.2) (hA t))]
    change ((q 1).2 - (q 0).2) / (2 * Real.pi) = ((A 1).2 - (A 0).2) / (2 * Real.pi)
    have he0 : q 0 = A 0 := hq0
    have he1 : q 1 = A 1 := hq1
    rw [he0, he1]
  exact ⟨g, q, hqi, hproj, ⟨hnormal, hg0 ▸ hf.2.1, hg1 ▸ hf.2.2.1, hnewfin⟩, hwind, hcount, hgRange⟩

end GraphMinor.GM06
