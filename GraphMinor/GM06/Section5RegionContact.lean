module

public import GraphMinor.GM06.Defs
import GraphMinor.GM06.Section5FirstRegionPath
import GraphMinor.GM06.Section5FirstContactOriginalGraph
import GraphMinor.GM06.Section5RegionSideBoundaryArc
import GraphMinor.GM06.Section5DiscBoundarySide
import GraphMinor.GM06.Section5StripBoundaryPaths
import GraphMinor.GM06.Section5ClosedStrip
import GraphMinor.GM06.Section5RegionPoint
import GraphMinor.GM06.Section5BoundaryGap
import GraphMinor.GM06.Section5RegionInterior
import GraphMinor.GM06.Section5RegionGraphPath
import GraphMinor.GM06.Section4PathTools
import GraphMinor.GM11.Regions
import GraphMinor.Surface.DiscMerge

/-!
# The full region-boundary contact assertion of (5.1)

Graph Minors VI, page 129, asserts that Rᵢ meets Pᵢ only at sᵢ
when the initial valency is larger than one and no reduction applies.
The first region path is a proper cross-cut of the closed strip.
Choose its side beside the initial cuff gap. The connected region
Rᵢ lies in that component of the strip minus the cut, so its closure
lies in the closed side. The boundary arc beside the gap and the cut
both miss Pᵢ except at sᵢ. A point of Pᵢ on the closed side must be
on its boundary, since both side discs are nested in the strip.
-/

public section
namespace GraphMinor.GM06
open Set Topology GraphMinor.Surface

/-- The boundary-contact assertion in the proof of Graph Minors VI
(5.1), page 129: at an initial vertex of valency different from one,
the following region closure meets its own linkage path only there. -/
theorem closure_region_inter_path_subset_start
    {k : ℕ} {G : Drawing ClosedCylinder} {θ : ℝ} (L : CylinderLinkage k G)
    (hk : 1 < k) (hG : IsCylinderSection5Drawing k G) (hθ : L.HasTheta θ)
    (hno : ¬ Section5AnyReductionApplies k G L) (i : Fin k)
    (hval : vertexValency G.toGraph (cylinderM1Point k i) ≠ 1) :
    closure (cylinderRegion k G i) ∩ (L.pathDrawing i).U ⊆ {cylinderM1Point k i} := by
  obtain ⟨v, hv, hvne, Q, hQ, hQR, _, hmeet⟩ :=
    exists_first_region_path_to_next_linkage L hk hG hθ hno i hval
  obtain ⟨a, ha, ha0, ha1, haBd, hNa, haPi⟩ := exists_region_side_boundary_arc L hk hG hθ i hv hvne
  let D := closure (cylinderStrip L i)
  have hD : IsClosedDisc D := isClosedDisc_closure_cylinderStrip L hk hG hθ i
  have hpathsBd := linkage_paths_subset_discBd_closure_strip L hk hG hθ i
  have hendsQ := isPathDrawing_end_vertices hQ.2.2
  have hQU : Q.U ⊆ D := hQR.trans (closure_mono (cylinderRegion_subset_strip L i))
  have hQBd : Q.U ∩ discBd D = {cylinderM1Point k i, v} := by
    apply subset_antisymm
    · rintro x ⟨hxQ, hxBd⟩
      rcases discBd_closure_cylinderStrip_subset L hk hG hθ i hxBd with hxL | hxbd
      · exact hmeet ⟨hxQ, hxL⟩
      · have hxG : x ∈ G.V := hG.2.1 ⟨hxbd, hQ.1.U_subset hxQ⟩
        obtain ⟨j, hxj⟩ := mem_iUnion.mp (boundary_vertex_mem_linkage_vertices L hG ⟨hxG, hxbd⟩)
        exact hmeet ⟨hxQ, mem_iUnion.mpr ⟨j, (L.pathDrawing j).V_subset_U hxj⟩⟩
    · rintro x (hxs | hxv)
      · subst x
        exact ⟨Q.V_subset_U hendsQ.1, hpathsBd.1
          ((L.pathDrawing i).V_subset_U (isPathDrawing_end_vertices (L.isPath i)).1)⟩
      · have hxv' := mem_singleton_iff.mp hxv
        subst x
        exact ⟨Q.V_subset_U hendsQ.2, hpathsBd.2 ((L.pathDrawing (finSuccCycle i)).V_subset_U hv)⟩
  obtain ⟨e, he⟩ := hQ.2.2.2
  have heD : range e ⊆ D := he.2.1 ▸ hQU
  have heBd : range e ∩ discBd D = {e 0, e 1} := by
    rw [he.2.1, he.2.2.1, he.2.2.2]
    exact hQBd
  obtain ⟨Δ, hΔ, hΔD, hΔbd, hcomp⟩ := exists_disc_side_of_boundary_arc hD a e ha he.1 haBd heD
    (ha0.trans he.2.2.1.symm) (ha1.trans he.2.2.2.symm) heBd
  have hNΔ : cylinderN1Point k i ∈ Δ := discBd_subset Δ (hΔbd.symm ▸ Or.inl hNa)
  have hNnot : cylinderN1Point k i ∉ range e :=
    fun h => cylinderN1Point_not_mem_U hG i (hQ.1.U_subset (he.2.1 ▸ h))
  have hregionSub : cylinderRegion k G i ⊆ D \ range e := by
    intro x hx
    refine ⟨subset_closure (cylinderRegion_subset_strip L i hx), ?_⟩
    intro hxe
    exact GM11.region_subset (cylinderRegion_mem_regions hG i) hx (hQ.1.U_subset (he.2.1 ▸ hxe))
  have hregionPre : IsPreconnected (cylinderRegion k G i) := isPreconnected_connectedComponentIn
  obtain ⟨z, _, hzcomp⟩ := hcomp
  have hNz : cylinderN1Point k i ∈ connectedComponentIn (D \ range e) z := by
    rw [hzcomp]
    exact ⟨hNΔ, hNnot⟩
  have hRcomp := hregionPre.subset_connectedComponentIn (cylinderN1Point_mem_region hG i) hregionSub
  rw [← connectedComponentIn_eq hNz, hzcomp] at hRcomp
  have hRΔ : closure (cylinderRegion k G i) ⊆ Δ :=
    closure_minimal (hRcomp.trans sdiff_subset) hΔ.isClosed
  have hΔPi : Δ ∩ (L.pathDrawing i).U ⊆ {cylinderM1Point k i} := by
    rintro x ⟨hxΔ, hxPi⟩
    have hxΔbd : x ∈ discBd Δ := by
      by_contra hn
      exact (discInt_mono isSurface_closedCylinder.2.2 hΔ hΔD ⟨hxΔ, hn⟩).2 (hpathsBd.1 hxPi)
    rw [hΔbd] at hxΔbd
    rcases hxΔbd with hxa | hxe
    · exact haPi ⟨hxa, hxPi⟩
    · rcases hmeet ⟨he.2.1 ▸ hxe, mem_iUnion.mpr ⟨i, hxPi⟩⟩ with hxs | hxv
      · exact hxs
      · have hxv' := mem_singleton_iff.mp hxv
        have hvPi : v ∈ (L.pathDrawing i).U := hxv' ▸ hxPi
        exact False.elim (disjoint_left.mp (L.pairwise_disjoint (finSuccCycle_ne_of_one_lt hk i))
          ((L.pathDrawing (finSuccCycle i)).V_subset_U hv) hvPi)
  exact fun x hx => hΔPi ⟨hRΔ hx.1, hx.2⟩

/-- The exact first boundary-contact assertion in VI (5.1), page 129:
the region closure meets its own path in precisely its initial vertex. -/
theorem closure_region_inter_path_eq_singleton
    {k : ℕ} {G : Drawing ClosedCylinder} {θ : ℝ} (L : CylinderLinkage k G)
    (hk : 1 < k) (hG : IsCylinderSection5Drawing k G) (hθ : L.HasTheta θ)
    (hno : ¬ Section5AnyReductionApplies k G L) (i : Fin k)
    (hval : vertexValency G.toGraph (cylinderM1Point k i) ≠ 1) :
    closure (cylinderRegion k G i) ∩ (L.pathDrawing i).U = {cylinderM1Point k i} := by
  apply subset_antisymm (closure_region_inter_path_subset_start L hk hG hθ hno i hval)
  rintro x rfl
  exact ⟨(initial_vertices_mem_closure_cylinderRegion hG i).1,
    (L.pathDrawing i).V_subset_U (isPathDrawing_end_vertices (L.isPath i)).1⟩

/-- The second boundary-contact assertion in VI (5.1), page 129:
the following region closure meets the next path at a noninitial vertex. -/
theorem exists_noninitial_next_vertex_in_region_closure
    {k : ℕ} {G : Drawing ClosedCylinder} {θ : ℝ} (L : CylinderLinkage k G)
    (hk : 1 < k) (hG : IsCylinderSection5Drawing k G) (hθ : L.HasTheta θ)
    (hno : ¬ Section5AnyReductionApplies k G L) (i : Fin k)
    (hval : vertexValency G.toGraph (cylinderM1Point k i) ≠ 1) :
    ∃ v ∈ (L.pathDrawing (finSuccCycle i)).V ∩ closure (cylinderRegion k G i),
      v ≠ cylinderM1Point k (finSuccCycle i) := by
  obtain ⟨v, hv, hvne, Q, hQ, hQR, _, _⟩ :=
    exists_first_region_path_to_next_linkage L hk hG hθ hno i hval
  exact ⟨v, ⟨hv, hQR (Q.V_subset_U (isPathDrawing_end_vertices hQ.2.2).2)⟩, hvne⟩

end GraphMinor.GM06
