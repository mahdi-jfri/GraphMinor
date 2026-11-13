module

public import GraphMinor.GM06.Defs
import GraphMinor.GM06.Section5BoundaryGapArc
import GraphMinor.GM06.Section5CurvePrefix
import GraphMinor.GM06.Section5StripBoundaryPaths
import GraphMinor.GM06.Section5BoundaryGap
import GraphMinor.GM06.Section5RegionPoint
import GraphMinor.GM06.Section5RegionGraphPath
import GraphMinor.GM06.Section5ProperPaths
import GraphMinor.GM06.Section5Red
import GraphMinor.GM06.Section4

/-!
# The strip boundary arc beside the initial cuff gap

For the full boundary-contact assertion in VI (5.1), page 129,
follow the initial cuff gap and then the initial segment of Pᵢ₊₁
up to the region-path contact. These arcs meet only at sᵢ₊₁, so
their concatenation is injective. It lies on the closed strip's
boundary, contains the dual initial point, and meets Pᵢ only at sᵢ.
-/

public section
namespace GraphMinor.GM06
open Set Topology GraphMinor.Surface

private theorem path_point_on_cuff1_eq_start
    {k : ℕ} {G : Drawing ClosedCylinder} (L : CylinderLinkage k G)
    (hG : IsCylinderSection5Drawing k G) (j : Fin k) {x : ClosedCylinder}
    (hx : x ∈ (L.pathDrawing j).U) (hxC1 : x ∈ cylinderCuff1) : x = cylinderM1Point k j := by
  have hxbd : x ∈ bd ClosedCylinder := by rw [bd_closedCylinder]; exact Or.inl hxC1
  have hends := L.U_inter_boundary hG j ▸ (show x ∈ (L.pathDrawing j).U ∩ bd ClosedCylinder from ⟨hx, hxbd⟩)
  rcases hends with hxs | hxt
  · exact hxs
  · have hxend := mem_singleton_iff.mp hxt
    have hterm : L.curve j 1 ∈ cylinderCuff2 := by
      obtain ⟨l, hl⟩ := L.curve_one_mem j
      rw [← hl]
      rfl
    have hxC2 : x ∈ cylinderCuff2 := hxend.symm ▸ hterm
    have hbad : (1 : ℝ) = 2 := hxC1.symm.trans hxC2
    norm_num at hbad

/-- The boundary arc from sᵢ through the initial cuff gap to a
noninitial contact on Pᵢ₊₁ contains the dual point and otherwise
misses Pᵢ. This selects the side of the cut in VI (5.1). -/
theorem exists_region_side_boundary_arc
    {k : ℕ} {G : Drawing ClosedCylinder} {θ : ℝ} (L : CylinderLinkage k G)
    (hk : 1 < k) (hG : IsCylinderSection5Drawing k G) (hθ : L.HasTheta θ) (i : Fin k)
    {v : ClosedCylinder} (hv : v ∈ (L.pathDrawing (finSuccCycle i)).V)
    (hvne : v ≠ cylinderM1Point k (finSuccCycle i)) :
    ∃ a : Curve ClosedCylinder, Function.Injective a ∧
      a 0 = cylinderM1Point k i ∧ a 1 = v ∧
      range a ⊆ discBd (closure (cylinderStrip L i)) ∧ cylinderN1Point k i ∈ range a ∧
      range a ∩ (L.pathDrawing i).U ⊆ {cylinderM1Point k i} := by
  let j := finSuccCycle i
  let f := initialCuffGapCurve k i
  have hf := initialCuffGapCurve_parametrizes hk hG i
  have hfp := initialCuffGapCurve_props hG i
  have hvU : v ∈ (L.pathDrawing j).U := (L.pathDrawing j).V_subset_U hv
  obtain ⟨τ, hτv⟩ := (L.curve_parametrizes j).2.1.symm ▸ hvU
  have hτ0 : τ ≠ 0 := by
    intro hτ
    rw [hτ, (L.curve_parametrizes j).2.2.1] at hτv
    exact hvne hτv.symm
  obtain ⟨g, hg⟩ := exists_parametrizes_initial_curve_segment (L.curve j)
    (L.curve_parametrizes j).1 τ (unitInterval.pos_iff_ne_zero.mpr hτ0)
  have hg' : ParametrizesSet g ((L.curve j) '' Icc 0 τ) (cylinderM1Point k j) v := by
    rwa [(L.curve_parametrizes j).2.2.1, hτv] at hg
  have hprefix : (L.curve j) '' Icc 0 τ ⊆ (L.pathDrawing j).U := by
    rw [← (L.curve_parametrizes j).2.1]
    exact image_subset_range _ _
  have hinter : range f ∩ (L.curve j) '' Icc 0 τ ⊆ {cylinderM1Point k j} := by
    rintro x ⟨hxf, hxP⟩
    exact path_point_on_cuff1_eq_start L hG j (hprefix hxP) (hfp.2.2.1 hxf)
  let P1 : Path (cylinderM1Point k i) (cylinderM1Point k j) := ⟨f, hf.2.2.1, hf.2.2.2⟩
  let P2 : Path (cylinderM1Point k j) v := ⟨g, hg'.2.2.1, hg'.2.2.2⟩
  let a : Curve ClosedCylinder := (P1.trans P2).toContinuousMap
  have ha := parametrizesSet_pathTrans hf hg' hinter
  change ParametrizesSet a (range f ∪ (L.curve j) '' Icc 0 τ) (cylinderM1Point k i) v at ha
  have hfCl : range f ⊆ closure (cylinderRegion k G i) := by
    rintro x ⟨t, rfl⟩
    by_cases ht0 : t = 0
    · rw [ht0, hfp.1]
      exact (initial_vertices_mem_closure_cylinderRegion hG i).1
    · by_cases ht1 : t = 1
      · rw [ht1, hfp.2.1]
        exact (initial_vertices_mem_closure_cylinderRegion hG i).2
      · exact subset_closure (hfp.2.2.2.2 ⟨t,
          ⟨unitInterval.pos_iff_ne_zero.mpr ht0, unitInterval.lt_one_iff_ne_one.mpr ht1⟩, rfl⟩)
  refine ⟨a, ha.1, ha.2.2.1, ha.2.2.2, ?_, ?_, ?_⟩
  · rw [ha.2.1]
    apply union_subset
    · intro x hx
      apply mem_discBd_closure_strip_of_mem_cuff L hk hG hθ i
        (closure_mono (cylinderRegion_subset_strip L i) (hfCl hx))
      rw [bd_closedCylinder]
      exact Or.inl (hfp.2.2.1 hx)
    · exact hprefix.trans (linkage_paths_subset_discBd_closure_strip L hk hG hθ i).2
  · rw [ha.2.1]
    exact Or.inl (image_subset_range _ _ hfp.2.2.2.1)
  · rintro x ⟨hxA, hxPi⟩
    rw [ha.2.1] at hxA
    rcases hxA with hxf | hxj
    · exact path_point_on_cuff1_eq_start L hG i hxPi (hfp.2.2.1 hxf)
    · exact False.elim (disjoint_left.mp (L.pairwise_disjoint (finSuccCycle_ne_of_one_lt hk i))
        (hprefix hxj) hxPi)

end GraphMinor.GM06
