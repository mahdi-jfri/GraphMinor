module

public import GraphMinor.GM06.Alg511FlowPaths
public import GraphMinor.GM06.Alg511FlowReindex
import Mathlib.Tactic

/-!
# A cylinder linkage from the initial flow paths

For the initial maximum-flow step of VI (5.11), page 134, order the
returned paths by their prescribed inner cuff vertices. Lift them
to disjoint path subdrawings and take injective parametrizations.
The supplied cuff interpretation puts their ends at the required
points. This constructs an actual cylinder linkage from the finite
path output, without assuming a linkage as part of the input.
-/

public section
namespace GraphMinor.GM06
open GraphMinor.Compute GraphMinor.Surface

/-- The paths returned by the finite initial flow search yield an
actual cylinder linkage under the supplied cuff interpretation. -/
theorem alg511_exists_linkage_of_flowPaths (x : GM06Alg511Input)
    {G : Drawing ClosedCylinder}
    (rep : GM06SuccessorGraphRep (x.withLinkage []) G.toGraph)
    (source : Fin x.pathCount → Fin x.vertexCount)
    (hsource : ∀ a ∈ x.flowInput.A, ∃ i, source i = a)
    (hpoints : ∀ i, (rep.vertex (source i)).val = cylinderM1Point x.pathCount i)
    (htarget : ∀ b ∈ x.flowInput.B, (rep.vertex b).val ∈ cylinderM2 x.pathCount)
    (P : Fin x.pathCount → ABWalk x.flowGraph x.flowInput.A x.flowInput.B)
    (hdisj : PairwiseVertexDisjoint P) (hsimple : ∀ i, (P i).walk.IsPath) :
    Nonempty (CylinderLinkage x.pathCount G) := by
  classical
  obtain ⟨Q, hstart, hQdisj, hQsimple⟩ :=
    alg511_exists_source_ordered_flowPaths source hsource P hdisj hsimple
  have hQpoints : ∀ i, (rep.vertex (Q i).start).val = cylinderM1Point x.pathCount i := by
    intro i
    rw [hstart i, hpoints i]
  have hQtarget : ∀ i, (rep.vertex (Q i).finish).val ∈ cylinderM2 x.pathCount :=
    fun i => htarget _ (Q i).finish_mem
  have hne : ∀ i, (Q i).start ≠ (Q i).finish := by
    intro i heq
    obtain ⟨j, hj⟩ := hQtarget i
    have hp : cylinderM1Point x.pathCount i = cylinderM2Point x.pathCount j := by
      rw [← hQpoints i, heq, ← hj]
    have hr := congrArg cylinderRadius hp
    norm_num [cylinderM1Point, cylinderM2Point] at hr
  obtain ⟨D, hD, hDdisj⟩ := alg511_exists_disjoint_pathDrawings x rep
    (fun i => (Q i).start) (fun i => (Q i).finish) (fun i => (Q i).walk)
    hQsimple hne hQdisj
  have hpaths : ∀ i, IsPathDrawing (D i) (cylinderM1Point x.pathCount i)
      (rep.vertex (Q i).finish).val := by
    intro i
    rw [← hQpoints i]
    exact (hD i).2.1
  choose f hf using fun i => (hpaths i).2
  refine ⟨{
    pathDrawing := D
    curve := f
    isSubdrawing := fun i => ⟨(hD i).1, (hD i).1.U_subset⟩
    isPath := ?_
    curve_parametrizes := ?_
    curve_one_mem := ?_
    pairwise_disjoint := hDdisj }⟩
  · intro i
    rw [(hf i).2.2.2]
    exact hpaths i
  · intro i
    rw [(hf i).2.2.2]
    exact hf i
  · intro i
    rw [(hf i).2.2.2]
    exact hQtarget i

end GraphMinor.GM06
