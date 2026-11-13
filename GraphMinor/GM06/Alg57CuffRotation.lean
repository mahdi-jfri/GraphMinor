module

public import GraphMinor.GM06.Alg57CuffCapEdges
public import GraphMinor.GM06.Alg57OuterCuffCorner
import GraphMinor.GM06.Alg57RegionIncidence
import GraphMinor.GM06.Section5NextContact

/-!
# The two cuff darts are consecutive in the positive rotation

For the cut construction of VI (5.7), page 133, the corner after
the positive inner end lies in the inner cap. Its next edge is
therefore another inner cuff edge at that vertex. The only two
possibilities are the current positive end and the previous negative
end. A vertex with two darts cannot have a fixed rotation dart, so
the latter is next. The same argument on the exterior cap makes the
positive outer end follow the previous negative end. Loops keep
their two different dart ends, so the argument also covers one path.
-/

public section
namespace GraphMinor.GM06
open Set Metric Topology GraphMinor.Surface GraphMinor.GM11 unitInterval

/-- The cyclic successor reverses the cyclic predecessor. -/
theorem finSuccCycle_pred_eq {k : ℕ} (i : Fin k) : finSuccCycle (finPredCycle i) = i := by
  apply Fin.ext
  unfold finPredCycle
  split <;> simp only [finSuccCycle]
  all_goals split_ifs <;> simp_all
  all_goals omega

/-- A rotation fixing a dart cannot reach a different dart at
its vertex. -/
theorem IsDrawingRotation.rot_ne_self_of_other
    {Γ : Drawing (OnePoint EuclideanPlane)}
    {γ : Set (OnePoint EuclideanPlane) → I → OnePoint EuclideanPlane}
    {R : DartRotation (DrawingDart Γ)} (hR : IsDrawingRotation Γ γ R)
    (a b : DrawingDart Γ) (hv : dartVertex γ a = dartVertex γ b) (hne : a ≠ b) : R.rot a ≠ a := by
  intro hfix
  obtain ⟨n, _, hn⟩ := (hR.reach a b hv).exists_pow_eq'
  have hpow : ∀ j : ℕ, (R.rot ^ j) a = a := by
    intro j
    induction j with
    | zero => rfl
    | succ j ih => rw [pow_succ', Equiv.Perm.mul_apply, ih, hfix]
  exact hne ((hpow n).symm.trans hn)

/-- At an inner cuff vertex, the negative end of the preceding
gap follows the positive end of the current gap counterclockwise. -/
theorem inner_cuff_rotation {k : ℕ} {G F : Drawing ClosedCylinder}
    (hG : IsCylinderSection5Drawing k G) (hGF : G.IsSubdrawing F)
    (hFU : F.U = G.U ∪ bd ClosedCylinder) (hFV : F.V = G.V)
    {γ : Set (OnePoint EuclideanPlane) → I → OnePoint EuclideanPlane}
    {R : DartRotation (DrawingDart (cylinderSphereDrawing F))}
    (hγ : EdgePar (cylinderSphereDrawing F) γ)
    (hR : IsDrawingRotation (cylinderSphereDrawing F) γ R)
    (hccw : IsCcwRotation (cylinderSphereDrawing F) γ R)
    (heI : ∀ j : Fin k, cylinderToSphere '' (initialCuffGapCurve k j '' Ioo 0 1) ∈
      (cylinderSphereDrawing F).E)
    (hγI : ∀ j : Fin k, ∀ t, γ (cylinderToSphere '' (initialCuffGapCurve k j '' Ioo 0 1)) t =
      cylinderToSphere (initialCuffGapCurve k j t)) (i : Fin k) :
    (R.rot ⟨(cylinderToSphere '' (initialCuffGapCurve k i '' Ioo 0 1), false), heI i⟩).val =
      (cylinderToSphere '' (initialCuffGapCurve k (finPredCycle i) '' Ioo 0 1), true) := by
  let d : DrawingDart (cylinderSphereDrawing F) :=
    ⟨(cylinderToSphere '' (initialCuffGapCurve k i '' Ioo 0 1), false), heI i⟩
  let b : DrawingDart (cylinderSphereDrawing F) :=
    ⟨(cylinderToSphere '' (initialCuffGapCurve k (finPredCycle i) '' Ioo 0 1), true), heI _⟩
  have hd : dartVertex γ d = cylinderToSphere (cylinderM1Point k i) := by
    simp only [dartVertex, d, endOf, Bool.false_eq_true, ↓reduceIte, hγI,
      (initialCuffGapCurve_props hG i).1]
  have hb : dartVertex γ b = cylinderToSphere (cylinderM1Point k i) := by
    simp only [dartVertex, b, endOf, ↓reduceIte, hγI,
      (initialCuffGapCurve_props hG (finPredCycle i)).2.1, finSuccCycle_pred_eq]
  obtain ⟨ρ, hρ, hform⟩ := exists_cornerLabel (infty_notMem_cylinderSphereDrawing_U F) hγ hR hccw
  have hcap := inner_forward_corner_subset_closed_cap hG hFU hγ hρ hform i (heI i) (hγI i)
  have hncap : (R.rot d).val.1 ⊆ toSph '' closedBall (0 : ℂ) (1 / 2) :=
    (hρ.next_edge_subset hR d).trans hcap
  rcases inner_cap_dart_at_source hG hGF hFU hFV hγI i (R.rot d)
    ((hR.vertex_rot d).trans hd) hncap with h | h
  · have hfix : R.rot d = d := Subtype.ext h
    have hne : d ≠ b := by
      intro heq
      have hh := congrArg (fun a : DrawingDart (cylinderSphereDrawing F) => a.val.2) heq
      exact Bool.false_ne_true hh
    exact False.elim (hR.rot_ne_self_of_other d b (hd.trans hb.symm) hne hfix)
  · exact h

/-- At an outer cuff vertex, the positive end of the current gap
follows the negative end of the preceding gap counterclockwise. -/
theorem outer_cuff_rotation {k : ℕ} {G F : Drawing ClosedCylinder}
    (hG : IsCylinderSection5Drawing k G) (hGF : G.IsSubdrawing F)
    (hFU : F.U = G.U ∪ bd ClosedCylinder) (hFV : F.V = G.V)
    {γ : Set (OnePoint EuclideanPlane) → I → OnePoint EuclideanPlane}
    {R : DartRotation (DrawingDart (cylinderSphereDrawing F))}
    (hγ : EdgePar (cylinderSphereDrawing F) γ)
    (hR : IsDrawingRotation (cylinderSphereDrawing F) γ R)
    (hccw : IsCcwRotation (cylinderSphereDrawing F) γ R)
    (heO : ∀ j : Fin k, cylinderToSphere '' (alg511OuterCuffGapCurve k j '' Ioo 0 1) ∈
      (cylinderSphereDrawing F).E)
    (hγO : ∀ j : Fin k, ∀ t, γ (cylinderToSphere '' (alg511OuterCuffGapCurve k j '' Ioo 0 1)) t =
      cylinderToSphere (alg511OuterCuffGapCurve k j t)) (i : Fin k) :
    (R.rot ⟨(cylinderToSphere '' (alg511OuterCuffGapCurve k (finPredCycle i) '' Ioo 0 1), true),
      heO (finPredCycle i)⟩).val =
      (cylinderToSphere '' (alg511OuterCuffGapCurve k i '' Ioo 0 1), false) := by
  let d : DrawingDart (cylinderSphereDrawing F) :=
    ⟨(cylinderToSphere '' (alg511OuterCuffGapCurve k (finPredCycle i) '' Ioo 0 1), true), heO _⟩
  let b : DrawingDart (cylinderSphereDrawing F) :=
    ⟨(cylinderToSphere '' (alg511OuterCuffGapCurve k i '' Ioo 0 1), false), heO i⟩
  have hd : dartVertex γ d = cylinderToSphere (cylinderM2Point k i) := by
    simp only [dartVertex, d, endOf, ↓reduceIte, hγO,
      (alg511_outer_gap_ends hG (finPredCycle i)).2, finSuccCycle_pred_eq]
  have hb : dartVertex γ b = cylinderToSphere (cylinderM2Point k i) := by
    simp only [dartVertex, b, endOf, Bool.false_eq_true, ↓reduceIte, hγO,
      (alg511_outer_gap_ends hG i).1]
  obtain ⟨ρ, hρ, hform⟩ := exists_cornerLabel (infty_notMem_cylinderSphereDrawing_U F) hγ hR hccw
  have hcap := outer_reverse_corner_subset_closed_cap (finPredCycle i) hG hFU hγ hρ hform
    (heO (finPredCycle i)) (hγO (finPredCycle i))
  have hncap : (R.rot d).val.1 ⊆ (toSph '' ball (0 : ℂ) 1)ᶜ :=
    (hρ.next_edge_subset hR d).trans hcap
  rcases outer_cap_dart_at_target hG hGF hFU hFV hγO i (R.rot d)
    ((hR.vertex_rot d).trans hd) hncap with h | h
  · exact h
  · have hfix : R.rot d = d := Subtype.ext h
    have hne : d ≠ b := by
      intro heq
      have hh := congrArg (fun a : DrawingDart (cylinderSphereDrawing F) => a.val.2) heq
      exact Bool.false_ne_true hh.symm
    exact False.elim (hR.rot_ne_self_of_other d b (hd.trans hb.symm) hne hfix)

end GraphMinor.GM06
