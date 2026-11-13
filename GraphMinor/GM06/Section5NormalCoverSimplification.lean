module

public import GraphMinor.GM06.Defs
public import GraphMinor.GM06.Section5CoverSides
import GraphMinor.GM06.Section5FiniteLiftedVertices
import GraphMinor.GM06.Section4Winding
import GraphMinor.Surface.ArcInPath

/-!
# Simplifying normal curves after an attachment detour

For VI (5.5), page 130, a raw normal detour may have infinitely
many visits to its attachment. Replace its angular lift by an arc
with the same endpoints inside the same image. The compact lifted
image contains only finitely many lifted vertices. Injectivity of
the new arc bounds vertex times by that finite set, without assuming
that the original detour already has finitely many vertex times.
-/

public section
namespace GraphMinor.GM06
open Set GraphMinor.Surface

/-- A normal curve between the two prescribed cuff sets has a
helix representative with the same lifted endpoints and winding.
Its vertex count is bounded by the number of distinct lifted
vertices in the original lifted image. -/
theorem exists_helix_from_normal_cover_curve
    {k : ℕ} {G : Drawing ClosedCylinder} (f : Curve ClosedCylinder)
    (hf : IsNormalCurve G f) (hf0 : f 0 ∈ cylinderN1 k) (hf1 : f 1 ∈ cylinderN2 k)
    (A : C(unitInterval, CylinderCover)) (hA : ∀ t, cylinderCoverProjection (A t) = f t) :
    ∃ g : Curve ClosedCylinder, ∃ q : C(unitInterval, CylinderCover),
      Function.Injective q ∧ (∀ t, cylinderCoverProjection (q t) = g t) ∧
      IsHelix k G g ∧ windingNumber g = windingNumber f ∧
      curveL G g ≤ (range A ∩ cylinderCoverProjection ⁻¹' G.V).ncard ∧
      range g ⊆ range f ∧ q 0 = A 0 ∧ q 1 = A 1 := by
  have hf0r : (f 0).1.1 = 1 := by obtain ⟨j, hj⟩ := hf0; rw [← hj]; rfl
  have hf1r : (f 1).1.1 = 2 := by obtain ⟨j, hj⟩ := hf1; rw [← hj]; rfl
  have hAne : A 0 ≠ A 1 := by
    intro he
    have hends : f 0 = f 1 := (hA 0).symm.trans
      ((congrArg cylinderCoverProjection he).trans (hA 1))
    have hr := congrArg (fun x : ClosedCylinder => x.1.1) hends
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
  have hnormal : IsNormalCurve G g := fun x hx => hf ⟨hgRange hx.1, hx.2⟩
  have hsub : q '' curveVertexHits G g ⊆ range A ∩ cylinderCoverProjection ⁻¹' G.V := by
    rintro _ ⟨t, ht, rfl⟩
    exact ⟨hqrange (mem_range_self t), ht⟩
  have hfinite := finite_lifted_vertices_on_curve G A
  have hnewfin : (curveVertexHits G g).Finite := by
    have himfin := hfinite.subset hsub
    have hpre : (q ⁻¹' (q '' curveVertexHits G g)).Finite := himfin.preimage hqinj.injOn
    exact hpre.subset (subset_preimage_image q _)
  have hcard := ncard_le_ncard hsub hfinite
  rw [ncard_image_of_injective _ hqinj] at hcard
  let α : C(unitInterval, ℝ) := ⟨fun t => (q t).2, continuous_snd.comp q.continuous⟩
  let β : C(unitInterval, ℝ) := ⟨fun t => (A t).2, continuous_snd.comp A.continuous⟩
  have hwind : windingNumber g = windingNumber f := by
    rw [windingNumber_eq_of_exp_lift α (fun _ => rfl),
      windingNumber_eq_of_exp_lift β (fun t => congrArg (fun x : ClosedCylinder => x.1.2) (hA t))]
    change ((q 1).2 - (q 0).2) / (2 * Real.pi) = ((A 1).2 - (A 0).2) / (2 * Real.pi)
    have he0 : q 0 = A 0 := hq0
    have he1 : q 1 = A 1 := hq1
    rw [he0, he1]
  exact ⟨g, q, hqi, hproj, ⟨hnormal, hg0 ▸ hf0, hg1 ▸ hf1, hnewfin⟩, hwind, hcard, hgRange, hq0, hq1⟩

end GraphMinor.GM06
