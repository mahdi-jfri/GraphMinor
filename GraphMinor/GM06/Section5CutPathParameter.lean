module

public import GraphMinor.GM06.Section5CutPathInjection
public import GraphMinor.GM06.Section5CoverLiftUnique
public import GraphMinor.GM06.Section5CoverDisc
import GraphMinor.GM06.Section4PathTools

/-!
# Parametrizing the projected cut path with its actual lift

Parametrize the cut path and compose with projection. Injectivity
on its point set gives an injective parametrization of the original
image path. Composing the same cut parametrization with the cover
coordinates gives a cover lift. Its initial angle is the canonical
one, so lift uniqueness identifies it with the lift in corrected
Reduction 4. Its incidence and terminal contact are consequently
the actual cut-path incidence and contact, as needed in VI (5.1).
-/

public section
namespace GraphMinor.GM06
open Set Topology Real GraphMinor.Surface

/-- The projected cut path has a parametrization whose aligned lift
is incident with the selected region and reaches the actual cut endpoint. -/
theorem exists_parameterized_projection_with_cover_lift
    {G : Drawing ClosedCylinder} {θ : ℝ} (L : CylinderLinkage 1 G)
    (hG : IsCylinderSection5Drawing 1 G) (hθ : L.HasTheta θ)
    {D : Set (ℝ × ℝ)} (hD : IsClosedDisc D)
    (hBd : discBd D = liftedStripBoundary hG.1 L 1)
    (hstrip : D ⊆ {p : ℝ × ℝ | 1 ≤ p.1 ∧ p.1 ≤ 2})
    {Q : Drawing D} {s t : D} (hQ : IsPathDrawing Q s t) (hscoord : s.1 = (1, 2 * π))
    (hpoint : Q.U ∩ bd D ⊆ {s, t})
    (hends : radialCylinderProjection s.1 ≠ radialCylinderProjection t.1)
    {P : Drawing ClosedCylinder}
    (hPU : P.U = (fun p : D => radialCylinderProjection p.1) '' Q.U)
    (hQR : (fun p : D => planeToCylinderCover p.1) '' Q.U ⊆ closure (cylinderCoverRegion 1 G 0)) :
    ∃ q : Curve ClosedCylinder,
      ParametrizesSet q P.U (cylinderM1Point 1 0) (radialCylinderProjection t.1) ∧
      range (cylinderCurveLiftAt q (cylinderInitialLift 1 0).2) ⊆ closure (cylinderCoverRegion 1 G 0) ∧
      cylinderCurveLiftAt q (cylinderInitialLift 1 0).2 1 = planeToCylinderCover t.1 := by
  obtain ⟨c, hc⟩ := hQ.2
  let q : Curve ClosedCylinder :=
    ⟨fun u => radialCylinderProjection (c u).1,
      continuous_radialCylinderProjection.comp (continuous_subtype_val.comp c.continuous)⟩
  let qCover : C(unitInterval, CylinderCover) :=
    ⟨fun u => planeToCylinderCover (c u).1,
      continuous_planeToCylinderCover.comp (continuous_subtype_val.comp c.continuous)⟩
  have hinj := injOn_cut_projection_of_path_point_contact L hG hθ hD hBd hstrip hpoint hends
  have hqinj : Function.Injective q := by
    intro u v huv
    apply hc.1
    apply hinj
    · rw [← hc.2.1]
      exact mem_range_self u
    · rw [← hc.2.1]
      exact mem_range_self v
    · exact huv
  have hqRange : range q = P.U := by
    change range ((fun p : D => radialCylinderProjection p.1) ∘ c) = _
    rw [range_comp, hc.2.1, ← hPU]
  have hsproj : radialCylinderProjection s.1 = cylinderM1Point 1 0 := by
    rw [hscoord]
    apply Subtype.ext
    apply Prod.ext
    · change max 1 (min 2 (1 : ℝ)) = 1
      norm_num
    · change Circle.exp (2 * π) = Circle.exp (2 * (((0 + 1 : ℕ) : ℝ)) * π / (1 : ℕ))
      norm_num
  have hq0 : q 0 = cylinderM1Point 1 0 := by
    change radialCylinderProjection (c 0).1 = _
    rw [hc.2.2.1, hsproj]
  have hq1 : q 1 = radialCylinderProjection t.1 := by
    change radialCylinderProjection (c 1).1 = _
    rw [hc.2.2.2]
  have hcov0 : (qCover 0).2 = (cylinderInitialLift 1 0).2 := by
    change (c 0).1.2 = _
    rw [hc.2.2.1, hscoord]
    norm_num [cylinderInitialLift]
  have hLift := cylinderCurveLiftAt_eq_of_cover_lift q qCover (fun _ => rfl)
  rw [hcov0] at hLift
  refine ⟨q, ⟨hqinj, hqRange, hq0, hq1⟩, ?_, ?_⟩
  · rw [hLift]
    rintro p ⟨u, rfl⟩
    apply hQR
    refine ⟨c u, ?_, rfl⟩
    rw [← hc.2.1]
    exact mem_range_self u
  · rw [hLift]
    change planeToCylinderCover (c 1).1 = planeToCylinderCover t.1
    rw [hc.2.2.2]

end GraphMinor.GM06
