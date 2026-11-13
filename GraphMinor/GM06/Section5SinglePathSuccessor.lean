module

public import GraphMinor.GM06.Section5SinglePathSpliceWinding
import GraphMinor.GM06.Section5OwnPathSplice
import GraphMinor.GM06.Section5ReplaceLinkagePath

/-!
# A right-seam contact gives the next one-path linkage

Concatenate the original contact path with the old path tail. The
proved splice construction gives a nondegenerate graph path, even
when the tail is a single terminal vertex. Replace the sole linkage
path with it. The right-contact winding calculation proves the new
linkage has winding one greater. This is the final construction in
the one-path case of VI (5.1), page 129.
-/

public section
namespace GraphMinor.GM06
open Set Topology GraphMinor.Surface

/-- A right lifted contact with no other old-path meetings produces
an actual linkage of winding old + 1. -/
theorem isThetaFeasible_successor_of_single_path_right_contact
    {G : Drawing ClosedCylinder} {θ : ℝ} (L : CylinderLinkage 1 G)
    (hG : IsCylinderSection5Drawing 1 G) (hθ : L.HasTheta θ)
    (u : unitInterval) (hu : 0 < u) (huV : L.curve 0 u ∈ (L.pathDrawing 0).V)
    {Q : Drawing ClosedCylinder} (hQ : IsSubpathOf G Q (cylinderM1Point 1 0) (L.curve 0 u))
    (hcontact : Q.U ∩ (L.pathDrawing 0).U ⊆ {cylinderM1Point 1 0, L.curve 0 u})
    (q : Curve ClosedCylinder) (hq : ParametrizesSet q Q.U (cylinderM1Point 1 0) (L.curve 0 u))
    (hqEnd : cylinderCurveLiftAt q (cylinderInitialLift 1 0).2 1 =
      planeToCylinderCover (liftedLinkageCurve hG.1 L 2 u)) :
    IsThetaFeasible 1 G (θ + 1) := by
  have hvs : L.curve 0 u ≠ cylinderM1Point 1 0 := by
    intro h
    have heq : L.curve 0 u = L.curve 0 0 := h.trans (L.curve_parametrizes 0).2.2.1.symm
    exact hu.ne' ((L.curve_parametrizes 0).1 heq)
  obtain ⟨T, R, hTail, hTP, hR, hRU⟩ := exists_path_after_own_linkage_tail
    (L.isSubdrawing 0).1 hQ.1 (L.isPath 0) hQ.2.2 huV hvs hcontact
  have hdisj : ∀ j : Fin 1, j ≠ 0 → Disjoint R.U (L.pathDrawing j).U := by
    intro j hj
    exact False.elim (hj (Subsingleton.elim _ _))
  obtain ⟨L', hRi, hEnd, _⟩ := exists_linkage_replacing_path L 0 hR.1 hR.2.2 hdisj
  have hR' : IsPathDrawing (L'.pathDrawing 0) (cylinderM1Point 1 0) (L.curve 0 1) := by
    simpa only [hEnd] using L'.isPath 0
  have hg := L'.curve_parametrizes 0
  have hg' : ParametrizesSet (L'.curve 0) (L'.pathDrawing 0).U (cylinderM1Point 1 0) (L.curve 0 1) :=
    ⟨hg.1, hg.2.1, hg.2.2.1, hg.2.2.2.trans hEnd⟩
  have hU : (L'.pathDrawing 0).U = Q.U ∪ T.U := by rw [hRi, hRU]
  have hw := windingNumber_single_path_right_contact_splice L hG u q hq hqEnd hTail hTP hR' hU
    (L'.curve 0) hg'
  refine ⟨L', ?_⟩
  intro i
  have hi : i = 0 := Subsingleton.elim _ _
  subst i
  rw [hw, hθ 0]

end GraphMinor.GM06
