module

public import GraphMinor.GM06.Defs
import GraphMinor.GM06.Section5ContractionFiniteVisits
import GraphMinor.GM06.Section5ContractionLift
import GraphMinor.GM06.Section5ContractionAdjoinBoundary
import GraphMinor.GM06.Section5ContractionSection
import GraphMinor.GM06.Section5NormalCurveInterior
import GraphMinor.GM06.Section5CoverCurve
import GraphMinor.GM06.Section5CoverSides
import GraphMinor.GM06.Section5RegionPoint
import GraphMinor.GM06.Section4PathTools
import GraphMinor.GM06.Section4Winding
import GraphMinor.GM06.Section4

/-!
# The contraction case of the helix comparison

This proves Reduction 3 of VI (5.5), page 130. Move nonvertex cuff
visits inward without changing the helix potential. Lift the actual
contraction and replace each interval between vertex visits in its
specified sheet, using the old neighbour above the collapsed vertex.
The finite induction preserves vertex count. The old and new lifted
endpoints agree, so their angular displacements and windings agree.
-/

public section
namespace GraphMinor.GM06
open Set GraphMinor.Surface

/-- Graph Minors VI (5.5), the complete Reduction 3 case. The
construction in fact preserves the helix potential exactly. -/
theorem theorem_5_5_red3
    {k : ℕ} {G G' : Drawing ClosedCylinder} (L : CylinderLinkage k G) (L' : CylinderLinkage k G')
    (hG : IsCylinderSection5Drawing k G) (hG' : IsCylinderSection5Drawing k G')
    (hRed : Section5Reduction3Step k G L G' L')
    (f' : Curve ClosedCylinder) (hf' : IsHelix k G' f') :
    ∃ f : Curve ClosedCylinder, IsHelix k G f ∧ curvePhi k G f ≤ curvePhi k G' f' := by
  rcases hRed with ⟨i, e, v, π, H, hval, _, _, hv, hvC, hl,
    hH0, hH1, hHbd, hfibre, _, hinjOld, hsurjOld, _, hUG, hVG, _, _, _⟩
  have hoff (x : ClosedCylinder) (hx : π x ≠ cylinderM1Point k i) : x ∉ closure e := by
    rw [← hfibre]
    exact hx
  have hinj : ∀ x y, π x ≠ cylinderM1Point k i → π y ≠ cylinderM1Point k i → π x = π y → x = y :=
    fun x y hx hy he => hinjOld x (hoff x hx) y (hoff y hy) he
  have hsurj : ∀ x, x ≠ cylinderM1Point k i → ∃ y, π y = x := by
    intro x hx
    obtain ⟨y, _, hy⟩ := hsurjOld x hx
    exact ⟨y, hy⟩
  have hπbd (p) (hp : p ∈ bd ClosedCylinder) : π p = p := (hH1 p).symm.trans (hHbd p hp 1)
  have hsV : cylinderM1Point k i ∈ G'.V :=
    (L'.isSubdrawing i).1.1 (isPathDrawing_end_vertices (L'.isPath i)).1
  obtain ⟨f₀, hf₀, hφ₀, hf₀bd⟩ := exists_helix_off_boundary_between_vertex_hits
    ⟨cylinderM1Point k i, G'.V_subset_U hsV⟩ f' hf'
  obtain ⟨F, F', hGF, _, hFU, hF'U, _, _, hU⟩ :=
    exists_cuff_drawings_of_boundary_fixed_contraction L L' hG hG' π hUG hπbd
  have hs : cylinderM1Point k i ∈ F'.U := hF'U ▸ Or.inl (G'.V_subset_U hsV)
  obtain ⟨Φ, ρ, hproj, htrans, hfix, hρ, hρv⟩ :=
    exists_cover_contraction_with_neighbour_section i hl hv π H hH0 hH1 hHbd hfibre hsurj
  let A := cylinderCurveLiftAt f₀ (cylinderAngleLift f₀ 0)
  have hA (t) : cylinderCoverProjection (A t) = f₀ t :=
    cylinderCoverProjection_curveLiftAt f₀ _ (exp_cylinderAngleLift f₀ 0) t
  have hf₀0off : f₀ 0 ∉ G'.U := by
    obtain ⟨j, hj⟩ := hf₀.2.1
    rw [← hj]
    exact cylinderN1Point_not_mem_U hG' j
  have hf₀1off : f₀ 1 ∉ G'.U := by
    obtain ⟨j, hj⟩ := hf₀.2.2.1
    rw [← hj]
    exact cylinderN2Point_not_mem_U hG' j
  have hf₀0bd : f₀ 0 ∈ bd ClosedCylinder := by
    obtain ⟨j, hj⟩ := hf₀.2.1
    rw [← hj, bd_closedCylinder]
    exact Or.inl rfl
  have hf₀1bd : f₀ 1 ∈ bd ClosedCylinder := by
    obtain ⟨j, hj⟩ := hf₀.2.2.1
    rw [← hj, bd_closedCylinder]
    exact Or.inr rfl
  have hA0 : ρ (A 0) = A 0 := section_eq_self_of_fixed_cover_contraction
    π Φ (cylinderM1Point k i) hproj htrans hinj ρ hρ (A 0)
    (by rw [hA]; intro he; exact hf₀0off (he ▸ G'.V_subset_U hsV))
    (hfix _ (by rw [hA]; exact hf₀0bd))
  have hA1 : ρ (A 1) = A 1 := section_eq_self_of_fixed_cover_contraction
    π Φ (cylinderM1Point k i) hproj htrans hinj ρ hρ (A 1)
    (by rw [hA]; intro he; exact hf₀1off (he ▸ G'.V_subset_U hsV))
    (hfix _ (by rw [hA]; exact hf₀1bd))
  let p : Path (A 0) (A 1) := ⟨A, rfl, rfl⟩
  have hpbase : (p.map continuous_cylinderCoverProjection).toContinuousMap = f₀ := by
    apply ContinuousMap.ext
    exact hA
  have hpnormal : IsNormalCurve G' (p.map continuous_cylinderCoverProjection).toContinuousMap := hpbase.symm ▸ hf₀.1
  have hpfin : (curveVertexHits G' (p.map continuous_cylinderCoverProjection).toContinuousMap).Finite := hpbase.symm ▸ hf₀.2.2.2
  have hpbd : ∀ t, 0 < t → t < 1 → cylinderCoverProjection (p t) ∉ G'.V →
      cylinderCoverProjection (p t) ∉ bd ClosedCylinder := by
    intro t ht0 ht1 htV
    change cylinderCoverProjection (A t) ∉ bd ClosedCylinder
    rw [hA]
    apply hf₀bd t ht0 ht1
    exact (hA t) ▸ htV
  obtain ⟨q, hqnormal, hqfin, hqcount⟩ := exists_cover_path_replacement_of_finite_vertex_hits
    L hG hGF hFU i hval hl hv hvC π Φ hproj htrans hfix hinj hsurj hU hs hfibre
    ρ hρ hρv hUG hVG hsV hF'U p hpnormal hpfin hpbd
  let f : Curve ClosedCylinder := (q.map continuous_cylinderCoverProjection).toContinuousMap
  have hf0 : f 0 = f₀ 0 := by
    change cylinderCoverProjection (q 0) = f₀ 0
    rw [q.source, hA0, hA]
  have hf1 : f 1 = f₀ 1 := by
    change cylinderCoverProjection (q 1) = f₀ 1
    rw [q.target, hA1, hA]
  have hf : IsHelix k G f := ⟨hqnormal, hf0 ▸ hf₀.2.1, hf1 ▸ hf₀.2.2.1, hqfin⟩
  have hcount : curveL G f = curveL G' f₀ := by rw [hpbase] at hqcount; exact hqcount
  let α : C(unitInterval, ℝ) := ⟨fun t => (q t).2, continuous_snd.comp q.continuous⟩
  let β : C(unitInterval, ℝ) := ⟨fun t => (A t).2, continuous_snd.comp A.continuous⟩
  have hwind : windingNumber f = windingNumber f₀ := by
    rw [windingNumber_eq_of_exp_lift α (fun _ => rfl),
      windingNumber_eq_of_exp_lift β (fun t => congrArg (fun x : ClosedCylinder => x.1.2) (hA t))]
    change ((q 1).2 - (q 0).2) / (2 * Real.pi) = ((A 1).2 - (A 0).2) / (2 * Real.pi)
    rw [q.target, q.source, hA0, hA1]
  have hφ : curvePhi k G f = curvePhi k G' f₀ := by simp only [curvePhi, hwind, hcount]
  exact ⟨f, hf, (hφ.trans hφ₀).le⟩

end GraphMinor.GM06
