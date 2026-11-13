module

public import GraphMinor.GM06.Defs
import GraphMinor.GM06.Section4
import GraphMinor.GM06.Section5ProperPaths
import GraphMinor.GM06.Section5RegionInterior
import GraphMinor.GM06.Section5RegionPoint
import GraphMinor.GM06.Section5EndpointObstruction
import GraphMinor.GM11.Walks
import GraphMinor.Surface.CutIArc
import GraphMinor.Surface.SurfacePull
import GraphMinor.GM07.Section11f

/-!
# The single linkage strip

For the one-path case of VI (5.1), page 129, cutting the cylinder
along the linkage path gives a connected surface. Its interior is
connected and dense, so the original path has connected complement.
Every extra initial edge lies in this projected strip. The clockwise
reduction condition uses the angular cover to retain the side at
the initial vertex.
-/

public section

namespace GraphMinor.GM06

open Set Topology GraphMinor.Surface

/-- A proper path joining the two cuffs does not separate the cylinder.
Cutting along it gives a connected surface. Its interior is connected
and dense, and the cut map carries the complement of its boundary
lifts onto the complement of the original path. -/
theorem isPreconnected_compl_of_spanning_cylinder_path {P : Drawing ClosedCylinder} {s t : ClosedCylinder}
    (hP : IsPathDrawing P s t) (hB : P.U ∩ bd ClosedCylinder = {s, t})
    (hs : s ∈ cylinderCuff1) (ht : t ∈ cylinderCuff2) : IsPreconnected P.Uᶜ := by
  have hconn : IsConnected (ClosedCylinder : Set (ℝ × Circle)) :=
    (isConnected_Icc (by norm_num : (1 : ℝ) ≤ 2)).prod isConnected_univ
  let : ConnectedSpace ClosedCylinder := isConnected_iff_connectedSpace.mp hconn
  have hsbd : s ∈ bd ClosedCylinder := by rw [bd_closedCylinder]; exact Or.inl hs
  have htbd : t ∈ bd ClosedCylinder := by rw [bd_closedCylinder]; exact Or.inr ht
  have hne : connectedComponentIn (bd ClosedCylinder) s ≠
      connectedComponentIn (bd ClosedCylinder) t := by
    intro he
    have hsc := mem_connectedComponentIn hsbd
    have htc : t ∈ connectedComponentIn (bd ClosedCylinder) s :=
      he.symm ▸ mem_connectedComponentIn htbd
    let r : ClosedCylinder → ℝ := fun p => p.1.1
    have hr : Continuous r := continuous_fst.comp continuous_subtype_val
    have hpre : IsPreconnected (r '' connectedComponentIn (bd ClosedCylinder) s) :=
      isPreconnected_connectedComponentIn.image r hr.continuousOn
    have h1 : (1 : ℝ) ∈ r '' connectedComponentIn (bd ClosedCylinder) s := ⟨s, hsc, hs⟩
    have h2 : (2 : ℝ) ∈ r '' connectedComponentIn (bd ClosedCylinder) s := ⟨t, htc, ht⟩
    obtain ⟨z, hz, hzr⟩ := hpre.ordConnected.out h1 h2
      (show (3 / 2 : ℝ) ∈ Icc (1 : ℝ) 2 by constructor <;> norm_num)
    have hzb := connectedComponentIn_subset _ _ hz
    rw [bd_closedCylinder] at hzb
    rcases hzb with hz1 | hz2
    · change z.1.1 = 1 at hz1
      change z.1.1 = 3 / 2 at hzr
      linarith only [hz1, hzr]
    · change z.1.1 = 2 at hz2
      change z.1.1 = 3 / 2 at hzr
      linarith only [hz2, hzr]
  have hl : IsLineWithEnds P.U s t := by
    obtain ⟨f, hf⟩ := hP.2
    let e : unitInterval ≃ₜ range f := Continuous.homeoOfEquivCompactToT2
      (f := Equiv.ofInjective f hf.1) f.continuous.rangeFactorization
    exact ⟨e.trans (Homeomorph.setCongr hf.2.1), hf.2.2.1, hf.2.2.2⟩
  obtain ⟨Y, tY, ψ, hY, hcut, hconnected, _, _⟩ :=
    cutIArc ClosedCylinder P.U s t isSurface_closedCylinder inferInstance
      (isPathDrawing_start_ne_end hP) hB hl
  let : ConnectedSpace Y := (hconnected hne).1
  have hInt : IsPreconnected ((univ : Set Y) \ bd Y) :=
    GM07.isPreconnected_diff_bd hY isOpen_univ isPreconnected_univ
  rw [← compl_eq_univ_sdiff] at hInt
  have hpre : IsPreconnected (ψ ⁻¹' P.U)ᶜ := hInt.subset_closure
    (fun _ hx hy => hx (hcut.2.2.2.2 hy))
    (fun y _ => mem_closure_compl_bd (hY.2.2 y))
  have him : ψ '' (ψ ⁻¹' P.U)ᶜ = P.Uᶜ := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact hy
    · intro hx
      obtain ⟨y, rfl⟩ := hcut.2.1 x
      exact ⟨y, hx, rfl⟩
  rw [← him]
  exact hpre.image ψ hcut.1.continuousOn
/-- With one linkage path, the only strip is its whole complement.
This handles the one-path case of the reduction argument in VI (5.1),
page 129, and the one-path correction of Reduction 4 (see the correction to Reduction 4 and (5.6) in
`corrections/GM06.md`). -/
theorem cylinderStrip_eq_compl_of_one_path
    {G : Drawing ClosedCylinder} (L : CylinderLinkage 1 G)
    (hG : IsCylinderSection5Drawing 1 G) (i : Fin 1) :
    cylinderStrip L i = (L.pathDrawing i).Uᶜ := by
  have hi : i = 0 := Subsingleton.elim _ _
  subst i
  have ht : L.curve 0 1 ∈ cylinderCuff2 := by
    obtain ⟨j, hj⟩ := L.curve_one_mem 0
    rw [← hj]
    rfl
  have hpre := isPreconnected_compl_of_spanning_cylinder_path
    (L.isPath 0) (L.U_inter_boundary hG 0) (by rfl) ht
  have hU : (⋃ j : Fin 1, (L.pathDrawing j).U) = (L.pathDrawing 0).U := by
    ext x
    constructor
    · intro hx
      obtain ⟨j, hj⟩ := mem_iUnion.mp hx
      have hj0 : j = 0 := Subsingleton.elim _ _
      subst j
      exact hj
    · intro hx
      exact mem_iUnion.mpr ⟨0, hx⟩
  have hN : cylinderN1Point 1 0 ∈ (L.pathDrawing 0).Uᶜ :=
    fun hx => cylinderN1Point_not_mem_U hG 0 ((L.isSubdrawing 0).2 hx)
  change connectedComponentIn (univ \ ⋃ j : Fin 1, (L.pathDrawing j).U)
    (cylinderN1Point 1 0) = _
  rw [hU, ← compl_eq_univ_sdiff]
  exact subset_antisymm (connectedComponentIn_subset _ _)
    (hpre.subset_connectedComponentIn hN Subset.rfl)

/-- Every edge outside the single linkage path belongs to its strip. -/
theorem edge_subset_single_strip_of_not_mem_path
    {G : Drawing ClosedCylinder} (L : CylinderLinkage 1 G)
    (hG : IsCylinderSection5Drawing 1 G) {e : Set ClosedCylinder}
    (he : e ∈ G.E) (heP : e ∉ (L.pathDrawing 0).E) :
    e ⊆ cylinderStrip L 0 := by
  rw [cylinderStrip_eq_compl_of_one_path L hG 0]
  intro x hx hxP
  have hxV : x ∉ (L.pathDrawing 0).V :=
    fun hv => (he.2.1 hx).2 ((L.isSubdrawing 0).1.1 hv)
  obtain ⟨f, hf, hxf⟩ := (L.pathDrawing 0).exists_edge_of_mem hxP hxV
  have hef := G.edge_eq_of_mem he ((L.isSubdrawing 0).1.2 hf) hx hxf
  exact heP (hef.symm ▸ hf)

end GraphMinor.GM06
