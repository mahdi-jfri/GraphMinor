module

public import GraphMinor.GM06.Alg511ConcreteReflection
public import GraphMinor.GM06.Alg511PositiveDrawingInput
public import GraphMinor.GM06.Alg511ReflectedInputRep
import Mathlib.Data.List.GetD
import Mathlib.Tactic

/-!
# The reflected positive cylinder input

The orientation step of VI (5.11), page 134, retains ordinary edge
labels and reflects the drawing. Transport its cuff augmentation
and all positive rotation charts by the concrete sphere reflection.
Restore the fixed cuff labels and curve directions by the proved
cuff permutation and parameter mask. The resulting positive rows
are exactly the rows computed by the finite reflection program.
Together with the reflected graph, cuff and normalized-turn
interpretations, this gives the full linkage-free reflected input.
No region interpretation is needed or used.
-/

public section
namespace GraphMinor.GM06
open Set Topology Real GraphMinor.Compute GraphMinor.Surface GraphMinor.GM11 unitInterval

/-- The exact computed reflected rows describe the actual reflected
cylinder drawing, with positive polar charts and both cuff families. -/
theorem alg511_reflected_successor_rotations {x : GM06Alg511Input} {G : Drawing ClosedCylinder}
    (rep : GM06SuccessorGraphRep (x.withLinkage []) G.toGraph)
    (hrot : GM06SuccessorRotationRep x.pathCount (x.withLinkage []) rep) :
    GM06SuccessorRotationRep x.pathCount (x.reflected.withLinkage []) (alg511ReflectedGraphRep rep) := by
  obtain ⟨F, edge, γ, hGF, hFU, hFV, hγ, hOld, hInner, hOuter, hEnds, hγInner, hγOuter, hlen, hrow⟩ := hrot
  change x.rotations.length = x.vertexCount at hlen
  let k := x.pathCount
  let m := rep.pairs.length
  let H := (alg511PlaneReflection (4 * π / k)).onePointCongr
  let edge' := edge.trans (alg511ImageEdgeEquiv H (cylinderSphereDrawing F))
  let mask := alg511CuffParameterMask m k edge'
  let δ := alg511ReverseEdgePar (alg511ImageEdgePar H γ) mask
  have hH : ∀ p, H (cylinderToSphere p) = cylinderToSphere (section5CylinderReflection k p) :=
    alg511_concrete_sphere_reflection k
  have hOldImage (j : Fin m) : (edge' (j.castAdd (k + k))).val =
      H '' (cylinderToSphere '' (rep.edge j).val) := by
    change H '' (edge (j.castAdd (k + k))).val = _
    rw [hOld j]
  have hInnerImage (i : Fin k) : (edge' ((i.castAdd k).natAdd m)).val =
      H '' (cylinderToSphere '' (initialCuffGapCurve k i '' Ioo 0 1)) := by
    change H '' (edge ((i.castAdd k).natAdd m)).val = _
    rw [hInner i]
  have hOuterImage (i : Fin k) : (edge' ((i.natAdd k).natAdd m)).val =
      H '' (cylinderToSphere '' (alg511OuterCuffGapCurve k i '' Ioo 0 1)) := by
    change H '' (edge ((i.natAdd k).natAdd m)).val = _
    rw [hOuter i]
  have hInnerFixed (i : Fin k) :
      (edge' (((gm06Alg511ReflectGapFin i).castAdd k).natAdd m)).val =
        cylinderToSphere '' (initialCuffGapCurve k i '' Ioo 0 1) := by
    rw [hInnerImage, alg511_sphere_reflection_image k H hH,
      alg511_reflected_initial_gap_image, gm06Alg511ReflectGapFin_involutive]
  have hOuterFixed (i : Fin k) :
      (edge' (((gm06Alg511ReflectGapFin i).natAdd k).natAdd m)).val =
        cylinderToSphere '' (alg511OuterCuffGapCurve k i '' Ioo 0 1) := by
    rw [hOuterImage, alg511_sphere_reflection_image k H hH,
      alg511_reflected_outer_gap_image, gm06Alg511ReflectGapFin_involutive]
  have hOldPar (j : Fin m) (t : I) :
      δ (H '' (cylinderToSphere '' (rep.edge j).val)) t =
        H (γ (cylinderToSphere '' (rep.edge j).val) t) := by
    unfold δ alg511ReverseEdgePar mask
    rw [← hOldImage j, alg511CuffParameterMask_old]
    simp only [Bool.false_eq_true, ite_false]
    rw [hOldImage, alg511ImageEdgePar_image]
  have hInnerPar (i : Fin k) (t : I) :
      δ (cylinderToSphere '' (initialCuffGapCurve k i '' Ioo 0 1)) t =
        cylinderToSphere (initialCuffGapCurve k i t) := by
    unfold δ alg511ReverseEdgePar mask
    rw [← hInnerFixed i, alg511CuffParameterMask_inner]
    simp only [ite_true]
    rw [hInnerImage, alg511ImageEdgePar_image, hγInner, hH, alg511_reflected_initial_gap,
      gm06Alg511ReflectGapFin_involutive, unitInterval.symm_symm]
  have hOuterPar (i : Fin k) (t : I) :
      δ (cylinderToSphere '' (alg511OuterCuffGapCurve k i '' Ioo 0 1)) t =
        cylinderToSphere (alg511OuterCuffGapCurve k i t) := by
    unfold δ alg511ReverseEdgePar mask
    rw [← hOuterFixed i, alg511CuffParameterMask_outer]
    simp only [ite_true]
    rw [hOuterImage, alg511ImageEdgePar_image, hγOuter, hH, alg511_reflected_outer_gap,
      gm06Alg511ReflectGapFin_involutive, unitInterval.symm_symm]
  have hAug := alg511_reflected_augmentation (k := k) hGF hFU hFV
  dsimp only [GM06SuccessorRotationRep, alg511ReflectedGraphRep]
  refine ⟨section5ReflectedDrawing k F, ?_⟩
  rw [alg511_concrete_reflectedDrawing_eq]
  refine ⟨(alg511CuffEdgeReflection m k).trans edge', δ, hAug.1, hAug.2.1, hAug.2.2,
    alg511_reverse_edgePar (alg511_image_edgePar H hγ) mask, ?_, ?_, ?_, ?_, hInnerPar, hOuterPar, ?_, ?_⟩
  · intro j
    change (edge' (alg511CuffEdgeReflection m k (j.castAdd (k + k)))).val =
      cylinderToSphere '' (section5CylinderReflection k '' (rep.edge j).val)
    exact (congrArg (fun a : Fin (m + (k + k)) => (edge' a).val) (alg511CuffEdgeReflection_old m k j)).trans
      ((hOldImage j).trans (alg511_sphere_reflection_image k H hH (rep.edge j).val))
  · intro i
    change (edge' (alg511CuffEdgeReflection m k ((i.castAdd k).natAdd m))).val = _
    rw [alg511CuffEdgeReflection_inner]
    exact hInnerFixed i
  · intro i
    change (edge' (alg511CuffEdgeReflection m k ((i.natAdd k).natAdd m))).val = _
    rw [alg511CuffEdgeReflection_outer]
    exact hOuterFixed i
  · intro j
    change δ (cylinderToSphere '' (section5CylinderReflection k '' (rep.edge j).val)) 0 =
        cylinderToSphere (section5CylinderReflection k (rep.vertex rep.pairs[j.val].1).val) ∧
      δ (cylinderToSphere '' (section5CylinderReflection k '' (rep.edge j).val)) 1 =
        cylinderToSphere (section5CylinderReflection k (rep.vertex rep.pairs[j.val].2).val)
    rw [← alg511_sphere_reflection_image k H hH]
    exact ⟨(hOldPar j 0).trans ((congrArg H (hEnds j).1).trans (hH _)),
      (hOldPar j 1).trans ((congrArg H (hEnds j).2).trans (hH _))⟩
  · change (x.rotations.map _).length = x.vertexCount
    simpa only [List.length_map] using hlen
  · intro v
    have hp := alg511_positive_rotation_reflected_cuffs (4 * π / k) edge γ (hrow v)
    have hendlen : x.endpoints.length = 2 * m := by
      have hh := congrArg List.length rep.endpoints
      change x.endpoints.length = (gm06EndpointWords (rep.pairs.map (fun p => (p.1.val, p.2.val)))).length at hh
      simpa only [gm06EndpointWords_length, List.length_map, m] using hh
    have hm : x.endpoints.length / 2 = m := by omega
    change GM06SuccessorRotationRowRep ((alg511CuffEdgeReflection m k).trans edge') δ
      (cylinderToSphere (section5CylinderReflection k (rep.vertex v).val))
      ((x.rotations.map (fun row => row.reverse.map (gm06Alg511ReflectAugmentedDart (x.endpoints.length / 2) k))).getD v.val [])
    change GM06SuccessorRotationRowRep _ _ _ ((x.rotations.map _).getD v.val (([] : List ℕ).reverse.map (gm06Alg511ReflectAugmentedDart (x.endpoints.length / 2) k)))
    rw [List.getD_map, hm, ← hH]
    exact hp

/-- The full linkage-free positive input relation is preserved by
the computed orientation reversal, including normalized edge turns. -/
@[expose] noncomputable def alg511ReflectedPositiveDrawingRep {x : GM06Alg511WindingInput}
    {G : Drawing ClosedCylinder} (rep : GM06Alg511PositiveDrawingRep x G)
    (hk : 0 < x.drawing.pathCount) :
    GM06Alg511PositiveDrawingRep x.reflected (section5ReflectedDrawing x.drawing.pathCount G) where
  graphTurn := alg511ReflectedInputRep rep.graphTurn hk
  denominator_ne_zero := rep.denominator_ne_zero
  regions_empty := by
    change (x.drawing.regionBoundaries.map _) = []
    rw [rep.regions_empty, List.map_nil]
  rotations := alg511_reflected_successor_rotations rep.graphTurn.graph rep.rotations

end GraphMinor.GM06
