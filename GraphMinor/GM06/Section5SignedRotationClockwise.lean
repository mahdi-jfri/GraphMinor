module

public import GraphMinor.GM06.Section5SignedHalfedgeCrossing
public import GraphMinor.GM06.Section5RotationAllEdgeCrossing

/-!
# The clockwise predicate from fixed signed rotation labels

The ordinary input rotation labels its negative cuff end, first
path end and positive cuff end. Their geometric ray interpretation
proves the clockwise criterion. Exact two-end incidence then turns
that criterion into the calibrated finite flags used by VI (5.7),
page 133. Only active original edge labels are required to represent
the current drawing, so labels survive previous edge deletions.
-/

public section
namespace GraphMinor.GM06
open Set Topology Real GraphMinor.Surface GraphMinor.GM11 GraphMinor.Compute unitInterval

/-- Fixed signed cuff and path labels in an interpreted rotation
row compute the corrected clockwise predicate for every active edge. -/
theorem clockwise_edge_iff_calibrated_signed_rotation
    {m : ℕ} (edge : Fin m → Set ClosedCylinder) (active : Fin m → Prop)
    {k : ℕ} {G F : Drawing ClosedCylinder} {θ : ℝ}
    (L : CylinderLinkage k G) (hG : IsCylinderSection5Drawing k G)
    (hGF : G.IsSubdrawing F) (hbdF : bd ClosedCylinder ⊆ F.U)
    (hθ : L.HasTheta θ) (i : Fin k)
    {γ : Set (OnePoint EuclideanPlane) → I → OnePoint EuclideanPlane}
    (hγ : EdgePar (cylinderSphereDrawing F) γ)
    {Φ : C(ClosedUnitDisc, OnePoint EuclideanPlane)}
    (hp : IsPolar (cylinderSphereDrawing F) (cylinderToSphere (cylinderM1Point k i)) Φ)
    (a b c : halfEdges (cylinderSphereDrawing F) γ
      (cylinderToSphere (cylinderM1Point k i)))
    (d : halfEdges (cylinderSphereDrawing F) γ
      (cylinderToSphere (cylinderM1Point k i)) → Circle)
    (hd : ∀ e, ∀ t : I, 0 < t → Φ (polarDiscPoint t (d e)) ∈ range (spoke γ e.1))
    (ha : a.1.2 = true) (hc : c.1.2 = false)
    (haAngle : ∀ t, γ a.1.1 t = cylinderToSphere (cylinderPoint 1 (by norm_num)
      ((cylinderInitialLift k i).2 - 2 * π / k + 2 * π * (t : ℝ) / k)))
    (hcAngle : ∀ t, γ c.1.1 t = cylinderToSphere (cylinderPoint 1 (by norm_num)
      ((cylinderInitialLift k i).2 + 2 * π * (t : ℝ) / k)))
    (hb : b.1.1 ∈ (cylinderSphereDrawing (L.pathDrawing i)).E)
    (hedge : ∀ j : Fin m, active j → edge j ∈ G.E)
    (xs : List ℕ) (z : ℕ → Circle)
    (hz : Set.InjOn z {r | r ∈ xs})
    (hs : xs.Pairwise (fun u v => circleStdCoord.angle (z u) < circleStdCoord.angle (z v)))
    (p q r : ℕ) (hpx : p ∈ xs) (hqx : q ∈ xs) (hrx : r ∈ xs)
    (hzp : z p = d a) (hzq : z q = d b) (hzr : z r = d c)
    (hlabel : ∀ (j : Fin m), active j → ∀ w : Circle,
      polarRimMap Φ w ∈ cylinderToSphere '' edge j ↔
        ∃ u ∈ xs, z u = w ∧ (u = 2 * j.val ∨ u = 2 * j.val + 1)) :
    p ≠ q ∧ p ≠ r ∧ q ≠ r ∧
      ∀ (j : Fin m), active j →
        (IsClockwiseInitialEdge L i (edge j) ↔
          gm06CalibratedSectorFlag xs p q r (2 * j.val) = 1 ∨
            gm06CalibratedSectorFlag xs p q r (2 * j.val + 1) = 1) := by
  obtain ⟨hpq, hpr, hqr, htest⟩ :=
    clockwise_edge_iff_crossing_signed_halfedges L hG hGF hbdF hθ i
      hγ hp a b c d hd ha hc haAngle hcAngle hb
  have hpq' : p ≠ q := fun hh => hpq (hzp.symm.trans ((congrArg z hh).trans hzq))
  have hpr' : p ≠ r := fun hh => hpr (hzp.symm.trans ((congrArg z hh).trans hzr))
  have hqr' : q ≠ r := fun hh => hqr (hzq.symm.trans ((congrArg z hh).trans hzr))
  refine ⟨hpq', hpr', hqr', ?_⟩
  intro j hj
  have ht := htest (edge j) (hedge j hj)
  rw [← hzp, ← hzq, ← hzr] at ht
  exact ht.trans (exists_rim_crossing_iff_either_calibrated_end_all_edges Φ xs z
    (cylinderToSphere '' edge j) j.val hz hs hpx hqx hrx hpq' hpr' hqr' (hlabel j hj))

end GraphMinor.GM06
