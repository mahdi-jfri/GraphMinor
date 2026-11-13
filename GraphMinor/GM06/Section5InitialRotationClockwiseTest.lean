module

public import GraphMinor.GM06.Section5InitialPolarInputCrossing
public import GraphMinor.GM06.Section5RotationEdgeCrossing
import GraphMinor.GM06.Section5PolarSubdrawingEnds
import GraphMinor.GM06.Section5CappedInitialPath

/-!
# The corrected clockwise test in an ordinary finite rotation row

For VI (5.7), page 133, the input row labels the edge directions
of its vertex chart. The two cuff directions and the linkage
path direction therefore have labels in the row. The geometric
crossing test and the two-end incidence theorem identify the
clockwise edges with the calibrated finite flags. All side facts
are proved from the drawing, including for a single linkage path.
-/

public section
namespace GraphMinor.GM06
open Set Topology GraphMinor.Surface GraphMinor.GM11 GraphMinor.Compute unitInterval

/-- The corrected clockwise condition has a finite calibrated sector
test on every rotation row that represents the drawing's edge ends. -/
theorem exists_initial_rotation_clockwise_test
    {k m : ℕ} {G F : Drawing ClosedCylinder} {θ : ℝ}
    (L : CylinderLinkage k G) (hG : IsCylinderSection5Drawing k G)
    (hGF : G.IsSubdrawing F) (hbdF : bd ClosedCylinder ⊆ F.U)
    (hθ : L.HasTheta θ) (i : Fin k)
    {Φ : C(ClosedUnitDisc, OnePoint EuclideanPlane)}
    (hp : IsPolar (cylinderSphereDrawing F) (cylinderToSphere (cylinderM1Point k i)) Φ)
    (edge : Fin m ≃ G.E) (xs : List ℕ) (z : ℕ → Circle)
    (hz : Set.InjOn z {r | r ∈ xs})
    (hs : xs.Pairwise (fun a b => circleStdCoord.angle (z a) < circleStdCoord.angle (z b)))
    (hcover : ∀ w : Circle, (∃ e ∈ (cylinderSphereDrawing F).E, polarRimMap Φ w ∈ e) ↔
      ∃ r ∈ xs, z r = w)
    (hlabel : ∀ (j : Fin m) (w : Circle), polarRimMap Φ w ∈ cylinderToSphere '' (edge j).1 ↔
      ∃ r ∈ xs, z r = w ∧ (r = 2 * j.val ∨ r = 2 * j.val + 1)) :
    ∃ p ∈ xs, ∃ q ∈ xs, ∃ c ∈ xs, p ≠ q ∧ p ≠ c ∧ q ≠ c ∧
      ∀ j : Fin m, Disjoint (edge j).1 (⋃ a, (L.pathDrawing a).U) →
        (IsClockwiseInitialEdge L i (edge j).1 ↔
          gm06CalibratedSectorFlag xs p q c (2 * j.val) = 1 ∨
            gm06CalibratedSectorFlag xs p q c (2 * j.val + 1) = 1) := by
  obtain ⟨p₀, q₀, c₀, hpq, hpc, hqc, hpC, hcC, hqP, htest⟩ :=
    exists_initial_input_polar_clockwise_crossing_test L hG hGF hbdF hθ i hp
  have hrow (w : Circle) (hw : polarRimMap Φ w ∈ (cylinderSphereDrawing F).U) :
      ∃ r ∈ xs, z r = w :=
    (hcover w).mp ((cylinderSphereDrawing F).exists_edge_of_mem hw (polar_rim_not_mem_vertices hp w))
  have hcuffU (w : Circle) (hw : polarRimMap Φ w ∈ cylinderToSphere '' cylinderCuff1) :
      polarRimMap Φ w ∈ (cylinderSphereDrawing F).U := by
    rw [cylinderSphereDrawing_U]
    obtain ⟨y, hy, hyw⟩ := hw
    exact ⟨y, hbdF (by rw [bd_closedCylinder]; exact Or.inl hy), hyw⟩
  obtain ⟨p, hpx, hzp⟩ := hrow p₀ (hcuffU p₀ hpC)
  obtain ⟨c, hcx, hzc⟩ := hrow c₀ (hcuffU c₀ hcC)
  obtain ⟨q, hqx, hzq⟩ := hrow q₀
    ((cylinderSphereDrawing_isSubdrawing ((L.isSubdrawing i).1.trans hGF)).U_subset hqP)
  have hpq' : p ≠ q := fun h => hpq (hzp.symm.trans ((congrArg z h).trans hzq))
  have hpc' : p ≠ c := fun h => hpc (hzp.symm.trans ((congrArg z h).trans hzc))
  have hqc' : q ≠ c := fun h => hqc (hzq.symm.trans ((congrArg z h).trans hzc))
  refine ⟨p, hpx, q, hqx, c, hcx, hpq', hpc', hqc', ?_⟩
  intro j hoff
  have hcuffOff (w : Circle) (hw : polarRimMap Φ w ∈ cylinderToSphere '' cylinderCuff1) :
      polarRimMap Φ w ∉ cylinderToSphere '' (edge j).1 := by
    rintro ⟨y, hye, hyw⟩
    obtain ⟨a, ha, haw⟩ := hw
    have hay : a = y := injective_cylinderToSphere (haw.trans hyw.symm)
    have hybd : y ∈ bd ClosedCylinder := by rw [bd_closedCylinder]; exact Or.inl (hay ▸ ha)
    exact ((edge j).2.2.1 hye).2 (hG.2.1 ⟨hybd, ((edge j).2.2.1 hye).1⟩)
  have hqOff : polarRimMap Φ q₀ ∉ cylinderToSphere '' (edge j).1 := by
    rw [cylinderSphereDrawing_U] at hqP
    rintro ⟨y, hye, hyw⟩
    obtain ⟨a, ha, haw⟩ := hqP
    have hay : a = y := injective_cylinderToSphere (haw.trans hyw.symm)
    exact disjoint_left.mp hoff hye (mem_iUnion.mpr ⟨i, hay ▸ ha⟩)
  have hgeometric := htest (edge j).1 (edge j).2 hoff
  rw [← hzp, ← hzq, ← hzc] at hgeometric
  exact hgeometric.trans (exists_rim_crossing_iff_either_calibrated_end Φ xs z
    (cylinderToSphere '' (edge j).1) j.val hz hs hpx hqx hcx hpq' hpc' hqc'
    (hlabel j) (hzp.symm ▸ hcuffOff p₀ hpC) (hzq.symm ▸ hqOff) (hzc.symm ▸ hcuffOff c₀ hcC))

end GraphMinor.GM06
