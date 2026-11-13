module

public import GraphMinor.Compute.GM06Alg511FiniteFeasible
public import GraphMinor.GM06.Alg511LabelTransfer
public import GraphMinor.GM06.Alg511WalkWinding
import GraphMinor.GM06.Alg511FlowPaths
import GraphMinor.GM06.Section5Red
import Mathlib.Tactic

/-!
# Soundness of finite winding witnesses

For the input determination required by VI (5.11), lift each finite
edge-labelled path through the supplied bijections. The actual paths
are simple and disjoint because their vertex supports are. Normalize
their curve parametrizations and use the proved edge-turn winding
formula. This constructs an actual cylinder linkage with the prescribed
winding from every finite witness, without a geometric linkage in the
input data.
-/

public section
namespace GraphMinor.GM06
open GraphMinor.Compute GraphMinor.Surface GraphMinor.GM11 Set

/-- Finite labelled feasibility implies actual cylinder feasibility
under the supplied graph, cuff and normalized turn interpretations. -/
theorem alg511_feasible_of_finite {x : GM06Alg511Input} {G : Drawing ClosedCylinder}
    (hk : 0 < x.pathCount)
    (rep : GM06SuccessorGraphRep (x.withLinkage []) G.toGraph)
    (turns : List ℤ) (hrep : Alg511NormalizedTurnsRep rep turns)
    (source target : Fin x.pathCount → Fin x.vertexCount)
    (hsource : ∀ i, (rep.vertex (source i)).val = cylinderM1Point x.pathCount i)
    (htarget : ∀ i, (rep.vertex (target i)).val = cylinderM2Point x.pathCount i)
    (theta : ℝ) (hfinite : GM06Alg511FiniteFeasible rep.pairs turns source target theta) :
    IsThetaFeasible x.pathCount G theta := by
  classical
  obtain ⟨finish, walks, hsimple, hdisj, hvalues⟩ := hfinite
  choose W hsupport hturn using fun i => alg511_exists_actual_walk_of_labelWalk rep turns (walks i)
  have hinj : Function.Injective (fun j => (rep.vertex j).val) :=
    Subtype.val_injective.comp rep.vertex.injective
  have hWsimple : ∀ i, (W i).IsSimple := by
    intro i
    change (W i).support.Nodup
    rw [hsupport i]
    exact (hsimple i).map hinj
  have hne : ∀ i, (rep.vertex (source i)).val ≠ (rep.vertex (target (finish i))).val := by
    intro i h
    have hp : cylinderM1Point x.pathCount i = cylinderM2Point x.pathCount (finish i) :=
      (hsource i).symm.trans (h.trans (htarget (finish i)))
    have hr := congrArg cylinderRadius hp
    norm_num [cylinderM1Point, cylinderM2Point] at hr
  let D := fun i => walkDrawing G (W i)
  have hDG : ∀ i, (D i).IsSubdrawing G := fun i => walkDrawing_isSubdrawing G (W i)
  have hpaths : ∀ i, IsPathDrawing (D i) (cylinderM1Point x.pathCount i)
      (cylinderM2Point x.pathCount (finish i)) := by
    intro i
    have hp := isPathDrawing_walkDrawing_of_isSimple G (hWsimple i) (hne i)
    change IsPathDrawing (D i) _ _ at hp
    rw [hsource i, htarget (finish i)] at hp
    exact hp
  have hDdisj : Pairwise (fun i j => Disjoint (D i).U (D j).U) := by
    intro i j hij
    apply alg511_disjoint_subdrawing_pointSets (hDG i) (hDG j)
    apply disjoint_left.mpr
    intro v hvi hvj
    change v ∈ (walkDrawing G (W i)).V at hvi
    change v ∈ (walkDrawing G (W j)).V at hvj
    rw [walkDrawing_V, hsupport i] at hvi
    rw [walkDrawing_V, hsupport j] at hvj
    obtain ⟨a, ha, hav⟩ := List.mem_map.mp hvi
    obtain ⟨b, hb, hbv⟩ := List.mem_map.mp hvj
    have hab : a = b := hinj (hav.trans hbv.symm)
    exact hdisj i j hij ha (hab ▸ hb)
  choose f hf using fun i => (hpaths i).2
  obtain ⟨reference, hM1, hM2, hw⟩ := alg511_normalized_walk_winding rep turns hrep
  have hwindings : ∀ i, windingNumber (f i) = theta := by
    intro i
    have hparam : ParametrizesSet (f i) (walkDrawing G (W i)).U
        (rep.vertex (source i)).val (rep.vertex (target (finish i))).val := by
      change ParametrizesSet (f i) (D i).U _ _
      rw [hsource i, htarget (finish i)]
      exact hf i
    have h := hw (W i) (hWsimple i) (f i) hparam
    rw [congrArg reference (hsource i), congrArg reference (htarget (finish i)), hM1, hM2] at h
    have hscaled := alg511_scaled_winding_of_relative_turn hk i (finish i) (f i)
      (alg511InterpretedWalkTurn rep turns (W i)) (alg511_relative_curveTurn_iff.mpr h)
    rw [hturn i] at hscaled
    exact mul_left_cancel₀ (Nat.cast_ne_zero.mpr (ne_of_gt hk)) (hscaled.trans (hvalues i).symm)
  refine ⟨{
    pathDrawing := D
    curve := f
    isSubdrawing := fun i => ⟨hDG i, (hDG i).U_subset⟩
    isPath := ?_
    curve_parametrizes := ?_
    curve_one_mem := ?_
    pairwise_disjoint := hDdisj }, hwindings⟩
  · intro i
    rw [(hf i).2.2.2]
    exact hpaths i
  · intro i
    rw [(hf i).2.2.2]
    exact hf i
  · intro i
    rw [(hf i).2.2.2]
    exact ⟨finish i, rfl⟩

end GraphMinor.GM06
