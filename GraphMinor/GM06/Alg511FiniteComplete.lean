module

public import GraphMinor.Compute.GM06Alg511FiniteFeasible
public import GraphMinor.GM06.Alg511LabelTransfer
public import GraphMinor.GM06.Alg511WalkWinding
import GraphMinor.GM06.Section5Red
import Mathlib.Tactic

/-!
# Completeness of finite winding witnesses

To determine feasibility from the finite input of VI (5.11), label
the walks of an actual cylinder linkage without changing their edge
choices. Their finite supports remain disjoint and simple. The winding
formula gives exactly the integer expression in the finite predicate.
Thus every actual linkage supplies a witness using only finite graph,
cuff and edge-turn labels. None of this witness is an input field.
-/

public section
namespace GraphMinor.GM06
open GraphMinor.Compute GraphMinor.Surface GraphMinor.GM11 Set

/-- Every feasible winding has a finite labelled witness under the
supplied graph, cuff and normalized turn interpretations. -/
theorem alg511_finite_of_feasible {x : GM06Alg511Input} {G : Drawing ClosedCylinder}
    (hk : 0 < x.pathCount)
    (rep : GM06SuccessorGraphRep (x.withLinkage []) G.toGraph)
    (turns : List ℤ) (hrep : Alg511NormalizedTurnsRep rep turns)
    (source target : Fin x.pathCount → Fin x.vertexCount)
    (hsource : ∀ i, (rep.vertex (source i)).val = cylinderM1Point x.pathCount i)
    (htarget : ∀ i, (rep.vertex (target i)).val = cylinderM2Point x.pathCount i)
    (theta : ℝ) (hfeasible : IsThetaFeasible x.pathCount G theta) :
    GM06Alg511FiniteFeasible rep.pairs turns source target theta := by
  classical
  obtain ⟨L, htheta⟩ := hfeasible
  choose finish hfinish using L.curve_one_mem
  have hex : ∀ i : Fin x.pathCount,
      ∃ W : GraphWalk G.toGraph (cylinderM1Point x.pathCount i) (L.curve i 1),
        W.IsSimple ∧ (L.pathDrawing i).V = {v | v ∈ W.support} ∧
        (L.pathDrawing i).E = {e | e ∈ W.edges} := by
    intro i
    obtain ⟨W, hs, hV, hE⟩ := (L.isPath i).1
    obtain ⟨W', hsupport, hedges⟩ := (L.isSubdrawing i).1.exists_walk_up W
    refine ⟨W', ?_, ?_, ?_⟩
    · change W'.support.Nodup
      rw [hsupport]
      exact hs
    · rw [hsupport]
      exact hV
    · rw [hedges]
      exact hE
  choose W hsimple hV hE using hex
  choose labelled hsupport hturn using fun i => alg511_exists_labelWalk_of_actual_walk
    rep turns (W i) (source i) (target (finish i)) (hsource i)
      ((htarget (finish i)).trans (hfinish i))
  refine ⟨finish, labelled, ?_, ?_, ?_⟩
  · intro i
    have hn : ((labelled i).support.map (fun j => (rep.vertex j).val)).Nodup := by
      rw [hsupport i]
      exact hsimple i
    exact hn.of_map
  · intro i j hij a hai haj
    have hvi : (rep.vertex a).val ∈ (L.pathDrawing i).V := by
      rw [hV i]
      rw [← hsupport i]
      exact List.mem_map.mpr ⟨a, hai, rfl⟩
    have hvj : (rep.vertex a).val ∈ (L.pathDrawing j).V := by
      rw [hV j]
      rw [← hsupport j]
      exact List.mem_map.mpr ⟨a, haj, rfl⟩
    exact disjoint_left.mp (L.pairwise_disjoint hij)
      ((L.pathDrawing i).V_subset_U hvi) ((L.pathDrawing j).V_subset_U hvj)
  · intro i
    have hdraw : walkDrawing G (W i) = L.pathDrawing i := by
      apply Drawing.ext_of_V_E
      · rw [walkDrawing_V]
        exact (hV i).symm
      · rw [walkDrawing_E]
        exact (hE i).symm
    have hparam : ParametrizesSet (L.curve i) (walkDrawing G (W i)).U
        (cylinderM1Point x.pathCount i) (L.curve i 1) := by
      rw [hdraw]
      exact L.curve_parametrizes i
    obtain ⟨reference, hM1, hM2, hw⟩ := alg511_normalized_walk_winding rep turns hrep
    have h := hw (W i) (hsimple i) (L.curve i) hparam
    rw [← congrArg reference (hfinish i), hM1, hM2] at h
    have hscaled := alg511_scaled_winding_of_relative_turn hk i (finish i) (L.curve i)
      (alg511InterpretedWalkTurn rep turns (W i)) (alg511_relative_curveTurn_iff.mpr h)
    rw [htheta i, ← hturn i] at hscaled
    exact hscaled

end GraphMinor.GM06
