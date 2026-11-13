module

public import GraphMinor.GM06.Defs
import GraphMinor.GM06.Section5CurveCount
import GraphMinor.GM06.Section5HelixConcatenation
import GraphMinor.GM06.Section4Winding

/-!
# The identities for the auxiliary curve in helix surgery

In VI (5.5), pages 131–132, the old and new helices share a suffix.
The auxiliary curve follows the old prefix and reverses the new
prefix. Winding therefore adds to that of the new helix. For vertex
counts, each join at a vertex is counted once rather than twice.
Keeping this correction gives the paper's three values of l after
the replacement-prefix counts are substituted.
-/

public section
namespace GraphMinor.GM06
open Set GraphMinor.Surface

/-- Reversing a cylinder path negates its winding. -/
theorem windingNumber_path_symm {x y : ClosedCylinder} (p : Path x y) :
    windingNumber p.symm.toContinuousMap = -windingNumber p.toContinuousMap := by
  let a := cylinderAngleLift p.toContinuousMap
  let b : C(unitInterval, ℝ) := ⟨fun t => a (unitInterval.symm t),
    a.continuous.comp (by fun_prop)⟩
  have hb (t : unitInterval) : Circle.exp (b t) = (p.symm t).1.2 :=
    exp_cylinderAngleLift p.toContinuousMap (unitInterval.symm t)
  rw [windingNumber_eq_of_exp_lift b hb]
  change (a (unitInterval.symm 1) - a (unitInterval.symm 0)) / (2 * Real.pi) = _
  simp only [unitInterval.symm_one, unitInterval.symm_zero]
  rw [windingNumber_eq_of_exp_lift a (exp_cylinderAngleLift p.toContinuousMap)]
  ring

/-- Reversing a path preserves the finite number of its vertex times. -/
theorem curveL_path_symm
    {S : Type*} [TopologicalSpace S] {G : Drawing S} {x y : S}
    (p : Path x y) (hp : (curveVertexHits G p.toContinuousMap).Finite) :
    (curveVertexHits G p.symm.toContinuousMap).Finite ∧
      curveL G p.symm.toContinuousMap = curveL G p.toContinuousMap := by
  have hi : Function.Injective unitInterval.symm := by
    intro s t h
    simpa using congrArg unitInterval.symm h
  have hfin : (curveVertexHits G p.symm.toContinuousMap).Finite := by
    change (unitInterval.symm ⁻¹' curveVertexHits G p.toContinuousMap).Finite
    exact Set.Finite.preimage hi.injOn hp
  have him : unitInterval.symm '' curveVertexHits G p.symm.toContinuousMap =
      curveVertexHits G p.toContinuousMap := by
    ext t
    constructor
    · rintro ⟨s, hs, rfl⟩
      exact hs
    · intro ht
      refine ⟨unitInterval.symm t, ?_, by simp⟩
      change p (unitInterval.symm (unitInterval.symm t)) ∈ G.V
      change p t ∈ G.V at ht
      simpa using ht
  refine ⟨hfin, ?_⟩
  rw [curveL, curveL, ← him]
  exact (ncard_image_of_injective _ hi).symm

/-- The winding identity for the auxiliary curve f'' in VI (5.5),
page 131, expressed using the two prefixes and their shared suffix. -/
theorem helix_surgery_winding_identity
    {x y v z : ClosedCylinder} (p : Path x v) (q : Path y v) (r : Path v z) :
    windingNumber (p.trans r).toContinuousMap =
      windingNumber (q.trans r).toContinuousMap + windingNumber (p.trans q.symm).toContinuousMap := by
  rw [windingNumber_path_trans, windingNumber_path_trans,
    windingNumber_path_trans, windingNumber_path_symm]
  ring

open Classical in
/-- The vertex-count identity for f'' in VI (5.5), pages 131–132.
The correction l is twice the new-prefix count minus the joining
vertex indicator. Thus its three values are 1, 2 and 3. -/
theorem helix_surgery_count_identity
    {S : Type*} [TopologicalSpace S] {G : Drawing S} {x y v z : S}
    (p : Path x v) (q : Path y v) (r : Path v z)
    (hp : (curveVertexHits G p.toContinuousMap).Finite)
    (hq : (curveVertexHits G q.toContinuousMap).Finite)
    (hr : (curveVertexHits G r.toContinuousMap).Finite) :
    (curveVertexHits G (p.trans q.symm).toContinuousMap).Finite ∧
      curveL G (p.trans r).toContinuousMap + 2 * curveL G q.toContinuousMap =
        curveL G (q.trans r).toContinuousMap + curveL G (p.trans q.symm).toContinuousMap +
          (if v ∈ G.V then 1 else 0) := by
  classical
  have hrev := curveL_path_symm q hq
  have hOld := (curveL_path_trans_add p r hp hr).2
  have hNew := (curveL_path_trans_add q r hq hr).2
  have hLoop := curveL_path_trans_add p q.symm hp hrev.1
  have hLoopL := hLoop.2
  rw [hrev.2] at hLoopL
  exact ⟨hLoop.1, by omega⟩

end GraphMinor.GM06
