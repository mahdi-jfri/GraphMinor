module

public import GraphMinor.GM06.Section5SinglePathSuccessor
import GraphMinor.GM06.Section5SinglePathSpliceWinding
import GraphMinor.GM06.Section5OwnPathSplice
import GraphMinor.GM06.Section5ReplaceLinkagePath

/-!
# The new one-path linkage, made explicit

The theorem `isThetaFeasible_successor_of_single_path_right_contact` (Lemma 16 for `k = 1`) proves
that some linkage has winding `θ + 1`. The algorithm needs the linkage itself: its path is the
contact path `Q` followed by the tail of `P₁` from the contact. We repeat its proof and keep the
linkage.
-/

public section
namespace GraphMinor.GM06
open Set Topology GraphMinor.Surface

/-- **Lemma 16 for `k = 1`, with the new linkage.** A path `Q` from `s₁` to `P₁(u)`, with `u > 0`,
that meets `P₁` only at its ends and whose aligned lift ends on `Γ₂`, gives a linkage of winding
`θ + 1` whose path is `Q` followed by the tail `T` of `P₁` from `P₁(u)`. -/
theorem exists_successor_linkage_of_single_path_right_contact
    {G : Drawing ClosedCylinder} {θ : ℝ} (L : CylinderLinkage 1 G)
    (hG : IsCylinderSection5Drawing 1 G) (hθ : L.HasTheta θ)
    (u : unitInterval) (hu : 0 < u) (huV : L.curve 0 u ∈ (L.pathDrawing 0).V)
    {Q : Drawing ClosedCylinder} (hQ : IsSubpathOf G Q (cylinderM1Point 1 0) (L.curve 0 u))
    (hcontact : Q.U ∩ (L.pathDrawing 0).U ⊆ {cylinderM1Point 1 0, L.curve 0 u})
    (q : Curve ClosedCylinder) (hq : ParametrizesSet q Q.U (cylinderM1Point 1 0) (L.curve 0 u))
    (hqEnd : cylinderCurveLiftAt q (cylinderInitialLift 1 0).2 1 =
      planeToCylinderCover (liftedLinkageCurve hG.1 L 2 u)) :
    ∃ (T : Drawing ClosedCylinder) (L' : CylinderLinkage 1 G), L'.HasTheta (θ + 1) ∧
      IsSection5Tail (L.pathDrawing 0) T (L.curve 0 u) (L.curve 0 1) ∧
      (L'.pathDrawing 0).U = Q.U ∪ T.U := by
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
  refine ⟨T, L', ?_, hTail, hU⟩
  intro i
  have hi : i = 0 := Subsingleton.elim _ _
  subst i
  rw [hw, hθ 0]

end GraphMinor.GM06
