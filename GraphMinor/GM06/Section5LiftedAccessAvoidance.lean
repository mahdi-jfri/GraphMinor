module

public import GraphMinor.GM06.Section5LiftedInitialBoundaryArc
public import GraphMinor.GM06.Section3Induce
public import GraphMinor.GM06.Section5RadialProjection
import GraphMinor.GM06.Section4
import GraphMinor.GM06.Section5Red
import GraphMinor.GM06.Section5SingleEdgePath
import GraphMinor.GM06.Section5DeletedInitialEdge
import GraphMinor.GM06.Section5BoundaryGap
import GraphMinor.GM06.Section5RegionPoint
import GraphMinor.GM06.Section5StripImage
import GraphMinor.GM11.Walks

/-!
# The closed set avoided by the lifted access curve

In the base case of VI (5.3), deleting the valency-one initial
vertex leaves a closed drawing that meets the sole linkage edge
only at its terminal vertex. The initial half-gap avoids this
drawing by properness. Thus the lifted boundary arc meets its
preimage only at the terminal point, as needed for the thin-disc
construction of the region access curve.
-/

public section
namespace GraphMinor.GM06
open Set Real GraphMinor.Surface
/-- The initial half-gap misses the drawing left after removing the
valency-one start, including the start itself. -/
theorem liftedInitialHalfGap_not_mem_deleted_drawing {k : ℕ} {G : Drawing ClosedCylinder} (hG : IsCylinderSection5Drawing k G) (i : Fin k)
    {a : Set ClosedCylinder} {v : ClosedCylinder}
    (hval : vertexValency G.toGraph (cylinderM1Point k i) = 1)
    (hl : G.toGraph.IsLink a (cylinderM1Point k i) v) (hvs : v ≠ cylinderM1Point k i) :
    let J := induceDrawing G (G.V \ {cylinderM1Point k i})
    ∀ u : unitInterval, radialCylinderProjection
      (liftedInitialHalfGap k ((i.val : ℤ) + 1) u) ∉ J.U := by
  intro J u
  have hcut := deleted_initial_vertex_drawing hval hl hvs
  have hnot : cylinderM1Point k i ∉ J.U := by
    intro hsJ
    have hscl : cylinderM1Point k i ∈ closure a :=
      (show cylinderM1Point k i ∈ closure a ∩ G.V from hl.2.2.2.symm ▸ mem_insert _ {v}).1
    have heq : cylinderM1Point k i = v :=
      mem_singleton_iff.mp (hcut.2.1 ▸ ⟨hsJ, hscl⟩)
    exact hvs heq.symm
  let τ : unitInterval := ⟨(1 - (u : ℝ)) / 2, by
    constructor
    · linarith only [u.2.2]
    · linarith only [u.2.1]⟩
  have hproj : radialCylinderProjection (liftedInitialHalfGap k ((i.val : ℤ) + 1) u) =
      initialCuffGapCurve k i τ := by
    apply Subtype.ext
    apply Prod.ext
    · change max 1 (min 2 1) = 1
      norm_num
    · change Circle.exp _ = Circle.exp _
      congr 1
      dsimp [liftedInitialHalfGap, initialCuffGapCurve, τ]
      push_cast
      ring
  rw [hproj]
  have hgap := initialCuffGapCurve_props hG i
  by_cases hu : u = 1
  · have hτ0 : τ = 0 := by
      apply Subtype.ext
      change (1 - (u : ℝ)) / 2 = 0
      rw [hu]
      norm_num
    rw [hτ0, hgap.1]
    exact hnot
  · have hτ : τ ∈ Ioo (0 : unitInterval) 1 := by
      constructor
      · change 0 < (1 - (u : ℝ)) / 2
        have huR : (u : ℝ) < 1 := unitInterval.lt_one_iff_ne_one.mpr hu
        linarith only [huR]
      · change (1 - (u : ℝ)) / 2 < 1
        linarith only [u.2.1]
    intro hJ
    have hreg := hgap.2.2.2.2 ⟨τ, hτ, rfl⟩
    have hJG : J.IsSubdrawing G := induceDrawing_isSubdrawing G sdiff_subset
    exact GM11.region_subset (cylinderRegion_mem_regions hG i) hreg (hJG.U_subset hJ)
end GraphMinor.GM06

namespace GraphMinor.GM06
open Set Real GraphMinor.Surface
/-- The lifted boundary arc used for VI (5.3), pages 132–133, meets
the lifted remaining drawing only at its terminal endpoint. -/
theorem lifted_initial_boundary_arc_inter_deleted_drawing_subset_end {k : ℕ} {G : Drawing ClosedCylinder} (L : CylinderLinkage k G)
    (hG : IsCylinderSection5Drawing k G) (i : Fin k)
    {e : Set ClosedCylinder} {v : ClosedCylinder}
    (hval : vertexValency G.toGraph (cylinderM1Point k i) = 1)
    (hl : G.toGraph.IsLink e (cylinderM1Point k i) v) (hvC : v ∈ cylinderCuff2)
    (a : Curve (ℝ × ℝ))
    (ha : ParametrizesSet a
      (range (liftedInitialHalfGap k ((i.val : ℤ) + 1)) ∪
        range (liftedLinkageCurve hG.1 L ((i.val : ℤ) + 1)))
      (1, (2 * (((i.val : ℤ) + 1) : ℝ) + 1) * π / k)
      (liftedLinkageCurve hG.1 L ((i.val : ℤ) + 1) 1)) :
    let J := induceDrawing G (G.V \ {cylinderM1Point k i})
    range a ∩ radialCylinderProjection ⁻¹' J.U ⊆ {a 1} := by
  intro J x hx
  have hvs : v ≠ cylinderM1Point k i :=
    disjoint_cylinderCuffs.symm.ne_of_mem hvC (cylinderM1Point_mem_cylinderCuff1 k i)
  have hcut := deleted_initial_vertex_drawing hval hl hvs
  have heq := linkage_path_eq_closed_edge_of_valency_one L hG i hval hl hvC
  rw [ha.2.1] at hx
  rcases hx.1 with ⟨u, rfl⟩ | ⟨t, rfl⟩
  · exact False.elim (liftedInitialHalfGap_not_mem_deleted_drawing hG i hval hl hvs u hx.2)
  · have hp : radialCylinderProjection (liftedLinkageCurve hG.1 L ((i.val : ℤ) + 1) t) =
        L.curve i t := by rw [radialCylinderProjection_liftedLinkageCurve, modIdx_natCast_succ]
    have htU : L.curve i t ∈ (L.pathDrawing i).U := by
      rw [← (L.curve_parametrizes i).2.1]
      exact mem_range_self t
    have htcl : L.curve i t ∈ closure e := heq.2 ▸ htU
    have htJ : L.curve i t ∈ J.U := hp ▸ hx.2
    have htv : L.curve i t = v := mem_singleton_iff.mp (hcut.2.1 ▸ ⟨htJ, htcl⟩)
    have ht1 : t = 1 := (L.curve_parametrizes i).1 (htv.trans heq.1)
    rw [ht1, ← ha.2.2.2]
    rfl
end GraphMinor.GM06
