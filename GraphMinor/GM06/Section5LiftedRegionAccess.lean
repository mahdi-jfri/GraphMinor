module

public import GraphMinor.GM06.Defs
import GraphMinor.GM06.Section5LiftedAccessAvoidance
import GraphMinor.GM06.Section5BoundaryParallel
import GraphMinor.GM06.Section5SingleEdgePath
import GraphMinor.GM06.Section5DeletedInitialEdge
import GraphMinor.GM06.Section5StripProjection
import GraphMinor.GM06.Section5StripImage
import GraphMinor.GM06.Section5RegionPoint
import GraphMinor.GM06.Section4Winding
import GraphMinor.GM06.Section4
import GraphMinor.GM06.Section5Red
import GraphMinor.Surface.Jordan

/-!
# Region access on the required side of the sole linkage edge

For the base case of VI (5.3), push the initial half-gap and the
sole linkage edge into the lifted strip, avoiding the preimage of
the remaining closed drawing. Project the path back to the cylinder.
Before its terminal point it misses the whole drawing, so connectedness
puts it in the initial region. The prescribed lifted endpoints give
its winding. The construction works even when there is only one path.
-/

public section
namespace GraphMinor.GM06
open Set Real GraphMinor.Surface
/-- The access curve g in VI (5.3), pages 132–133. A thin curve
beside the lifted initial boundary arc stays in the initial region
before its terminal point and has winding θ − 1/(2k). Choosing it in
the lifted strip also fixes the side when k = 1. -/
theorem exists_region_access_curve_of_initial_valency_one {k : ℕ} {G : Drawing ClosedCylinder} {θ : ℝ} (L : CylinderLinkage k G)
    (hG : IsCylinderSection5Drawing k G) (hθ : L.HasTheta θ) (i : Fin k)
    {e : Set ClosedCylinder} {v : ClosedCylinder}
    (hval : vertexValency G.toGraph (cylinderM1Point k i) = 1)
    (hl : G.toGraph.IsLink e (cylinderM1Point k i) v) (hvC : v ∈ cylinderCuff2) :
    ∃ g : Curve ClosedCylinder, g 0 = cylinderN1Point k i ∧ g 1 = v ∧
      (∀ t : unitInterval, t < 1 → g t ∈ cylinderRegion k G i) ∧
      windingNumber g = θ - (2 * (k : ℝ))⁻¹ := by
  classical
  let m : ℤ := (i.val : ℤ) + 1
  let J := induceDrawing G (G.V \ {cylinderM1Point k i})
  have hvs : v ≠ cylinderM1Point k i :=
    disjoint_cylinderCuffs.symm.ne_of_mem hvC (cylinderM1Point_mem_cylinderCuff1 k i)
  have hcut := deleted_initial_vertex_drawing hval hl hvs
  have heq := linkage_path_eq_closed_edge_of_valency_one L hG i hval hl hvC
  obtain ⟨D, hD, hBd, hstrip⟩ := exists_closedDisc_of_liftedStripBoundary L hG hθ m
  obtain ⟨a, ha, haD⟩ := exists_lifted_initial_boundary_arc L hG hθ m hBd
  let Z := D ∩ radialCylinderProjection ⁻¹' J.U
  have hZ : IsClosed Z := hD.isClosed.inter (J.isClosed_U.preimage continuous_radialCylinderProjection)
  have hAZ : range a ∩ Z ⊆ {a 0, a 1} := by
    intro x hx
    exact Or.inr (lifted_initial_boundary_arc_inter_deleted_drawing_subset_end L hG i hval hl hvC
      a (by simpa only [m, Int.cast_add, Int.cast_one] using ha) ⟨hx.1, hx.2.2⟩)
  let E : (ℝ × ℝ) ≃ₜ EuclideanPlane :=
    Complex.equivRealProdCLM.symm.toHomeomorph.trans complexPlane.toHomeomorph
  obtain ⟨p, hpD, hpinside⟩ :=
    exists_path_inside_plane_disc_beside_boundary_arc E hD a ha.1 haD hZ hAZ
  let g : Curve ClosedCylinder :=
    ⟨radialCylinderProjection ∘ p, continuous_radialCylinderProjection.comp p.continuous⟩
  have hproj0 : radialCylinderProjection (1, (2 * (m : ℝ) + 1) * π / k) = cylinderN1Point k i := by
    apply Subtype.ext
    apply Prod.ext
    · change max 1 (min 2 1) = 1
      norm_num
    · change Circle.exp _ = Circle.exp _
      congr 1
  have hg0 : g 0 = cylinderN1Point k i := by
    change radialCylinderProjection (p 0) = _
    rw [Path.source, ha.2.2.1]
    exact hproj0
  have hg1 : g 1 = v := by
    change radialCylinderProjection (p 1) = _
    rw [Path.target, ha.2.2.2, radialCylinderProjection_liftedLinkageCurve, modIdx_natCast_succ]
    exact heq.1.symm
  have hoff (t : unitInterval) (ht0 : 0 < t) (ht1 : t < 1) : g t ∉ G.U := by
    have hpt := hpinside t ht0 ht1
    have htStrip : g t ∈ cylinderStrip L i := by
      apply stripDiscInterior_projection_mem_strip L hG hθ i hD hBd hstrip hpt.1
      · exact radialCylinderProjection_fst (hstrip (hpD (mem_range_self t)))
      · rfl
    have htold : g t ∉ closure e := by
      intro hte
      have htP : g t ∈ (L.pathDrawing i).U := heq.2.symm ▸ hte
      exact (connectedComponentIn_subset _ _ htStrip).2 (mem_iUnion.mpr ⟨i, htP⟩)
    intro htG
    rw [hcut.2.2] at htG
    rcases htG with htJ | hte
    · exact hpt.2 ⟨hpD (mem_range_self t), htJ⟩
    · exact htold hte
  have hgr : ∀ t : unitInterval, t < 1 → g t ∈ cylinderRegion k G i := by
    have hpre : IsPreconnected (g '' Iio (1 : unitInterval)) :=
      isPreconnected_Iio.image g g.continuous.continuousOn
    have hbase : cylinderN1Point k i ∈ g '' Iio (1 : unitInterval) :=
      ⟨0, by change (0 : ℝ) < 1; norm_num, hg0⟩
    have hsub : g '' Iio (1 : unitInterval) ⊆ univ \ G.U := by
      rintro _ ⟨t, ht, rfl⟩
      refine ⟨mem_univ _, ?_⟩
      by_cases ht0 : t = 0
      · rw [ht0, hg0]
        exact cylinderN1Point_not_mem_U hG i
      · exact hoff t (unitInterval.pos_iff_ne_zero.mpr ht0) ht
    exact fun t ht => hpre.subset_connectedComponentIn hbase hsub ⟨t, ht, rfl⟩
  refine ⟨g, hg0, hg1, hgr, ?_⟩
  let α : C(unitInterval, ℝ) := ⟨fun t => (p t).2, continuous_snd.comp p.continuous⟩
  have hα : ∀ t, Circle.exp (α t) = (g t).1.2 := fun _ => rfl
  rw [windingNumber_eq_of_exp_lift α hα]
  change ((p 1).2 - (p 0).2) / (2 * π) = _
  rw [Path.target, Path.source, ha.2.2.1, ha.2.2.2,
    (liftedLinkageCurve_props hG.1 L hθ m).2.2.2.2.1]
  field_simp [Nat.cast_ne_zero.mpr hG.1.ne', pi_ne_zero]
  ring
end GraphMinor.GM06
