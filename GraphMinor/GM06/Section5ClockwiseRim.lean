module

public import GraphMinor.GM06.Section5ClockwisePolarRay
public import GraphMinor.GM06.Section5PolarRimCoordinates
import GraphMinor.GM06.Section5PolarAngularProjection
import GraphMinor.GM06.Section5PolarEdgeAccess
import GraphMinor.GM06.Section5CoverSides
import GraphMinor.GM06.Section4PathTools

/-!
# Reading the clockwise side on a polar rim

For VI (5.7), page 133, a sufficiently small polar chart reduces
clockwise edge incidence to a rim direction in the chosen angular
sheet. The forward implication takes a lifted edge point close to
the initial vertex and moves radially to the rim. The positive
radial segment avoids the linkage, so it stays in the same strip.
The reverse implication uses the lifted radial access curve.
-/

public section
namespace GraphMinor.GM06
open Set Topology GraphMinor.Surface GraphMinor.GM11 unitInterval

/-- In a polar chart contained in one angular sheet, an edge is
clockwise exactly when one of its rim directions lies in that strip. -/
theorem isClockwiseInitialEdge_iff_polar_rim_direction
    {k : ℕ} {G F : Drawing ClosedCylinder} (L : CylinderLinkage k G) (i : Fin k)
    (hGF : G.IsSubdrawing F) {e : Set ClosedCylinder} (he : e ∈ G.E)
    {Φ : C(ClosedUnitDisc, OnePoint EuclideanPlane)}
    (hp : IsPolar (cylinderSphereDrawing F) (cylinderToSphere (cylinderM1Point k i)) Φ)
    (η : OpenPartialHomeomorph CylinderCover ClosedCylinder)
    (hη : (η : CylinderCover → ClosedCylinder) = cylinderCoverProjection)
    (hsη : cylinderInitialLift k i ∈ η.source)
    (hsmall : ∀ y : ClosedCylinder, cylinderToSphere y ∈ range Φ → y ∈ η.target)
    (hoff : Disjoint e (⋃ j : Fin k, (L.pathDrawing j).U)) :
    IsClockwiseInitialEdge L i e ↔
      ∃ (w : Circle) (y : ClosedCylinder), polarRimMap Φ w = cylinderToSphere y ∧
        y ∈ e ∧ η.symm y ∈ cylinderCoverStrip L (i.val : ℤ) := by
  have heF : cylinderToSphere '' e ∈ (cylinderSphereDrawing F).E := by
    rw [cylinderSphereDrawing_E]
    exact mem_image_of_mem _ (hGF.2 he)
  constructor
  · rintro ⟨A, _, hAe, hsA, hAside⟩
    let N := η.source ∩ (fun z => cylinderToSphere (cylinderCoverProjection z)) ⁻¹'
      interior (range Φ)
    have hNo : IsOpen N := η.open_source.inter (isOpen_interior.preimage
      (continuous_cylinderToSphere.comp continuous_cylinderCoverProjection))
    have hsN : cylinderInitialLift k i ∈ N := ⟨hsη, hp.nhd⟩
    obtain ⟨z, hzN, hzA⟩ := mem_closure_iff.mp hsA N hNo hsN
    have hze : cylinderCoverProjection z ∈ e := hAe ▸ mem_image_of_mem _ hzA
    have hzΦ : cylinderToSphere (cylinderCoverProjection z) ∈ range Φ :=
      interior_subset hzN.2
    have hzs : cylinderToSphere (cylinderCoverProjection z) ≠
        cylinderToSphere (cylinderM1Point k i) := by
      intro hh
      have hzsi := injective_cylinderToSphere hh
      have hsiV : cylinderM1Point k i ∈ G.V :=
        (L.isSubdrawing i).1.1 (isPathDrawing_end_vertices (L.isPath i)).1
      exact (he.2.1 hze).2 (hzsi.symm ▸ hsiV)
    obtain ⟨q, _, _, hrepr⟩ := exists_polar_angular_projection hp
    obtain ⟨c, hc, hcx⟩ := hrepr _ ⟨hzΦ, hzs⟩
    let w := q (cylinderToSphere (cylinderCoverProjection z))
    have hrim : polarRimMap Φ w ∈ cylinderToSphere '' e := by
      apply (polar_ray_mem_atom_iff hp (Or.inl (Or.inr heF))
        (polarDiscPoint_one_ne_centre w) c hc).mpr
      rw [discScale_polarDiscPoint_one]
      exact hcx.symm ▸ mem_image_of_mem _ hze
    obtain ⟨y, hye, hyw⟩ := hrim
    have hxy : Φ (polarDiscPoint 1 w) = cylinderToSphere y := hyw.symm
    obtain ⟨f, _, hf1, hfe, hf⟩ := exists_polar_edge_access_of_embedding
      isClosedEmbedding_cylinderToSphere.isEmbedding hp heF
      (polarDiscPoint_one_ne_centre w) hxy hye
    have hfT (t : I) : f t ∈ η.target :=
      hsmall _ ((hf t).symm ▸ mem_range_self (discScale t (polarDiscPoint 1 w)))
    let g : Curve CylinderCover := ⟨fun t => η.symm (f t),
      η.symm.continuousOn.comp_continuous f.continuous hfT⟩
    have hgc : g c = z := by
      have hfc : f c = cylinderCoverProjection z := by
        apply injective_cylinderToSphere
        rw [hf, discScale_polarDiscPoint_one]
        exact hcx
      change η.symm (f c) = z
      rw [hfc, ← hη, η.left_inv hzN.1]
    have hsub : g '' Ioi (0 : I) ⊆ cylinderCoverProjection ⁻¹'
        (univ \ ⋃ j : Fin k, (L.pathDrawing j).U) := by
      rintro _ ⟨t, ht, rfl⟩
      change cylinderCoverProjection (η.symm (f t)) ∈
        (univ \ ⋃ j : Fin k, (L.pathDrawing j).U)
      rw [← hη, η.right_inv (hfT t)]
      exact ⟨mem_univ _, fun hh => disjoint_left.mp hoff (hfe t ht) hh⟩
    have hstrip : g '' Ioi (0 : I) ⊆ cylinderCoverStrip L (i.val : ℤ) := by
      change _ ⊆ connectedComponentIn _ _
      rw [connectedComponentIn_eq (hAside hzA)]
      exact (isPreconnected_Ioi.image g g.continuous.continuousOn).subset_connectedComponentIn ⟨c, hc, hgc⟩ hsub
    refine ⟨w, y, hxy, hye, ?_⟩
    have hh := hstrip (mem_image_of_mem g (show (1 : I) ∈ Ioi 0 from zero_lt_one))
    change η.symm (f 1) ∈ _ at hh
    rwa [hf1] at hh
  · rintro ⟨w, y, hxy, hye, hside⟩
    apply isClockwiseInitialEdge_of_polar_edge_ray L i hGF he hp
      (polarDiscPoint_one_ne_centre w) hxy hye η hη hsη _ hoff hside
    intro t
    have ht := (polar_ray_mem_atom_iff hp (Or.inl (Or.inr heF))
      (polarDiscPoint_one_ne_centre w) t)
    rcases eq_or_lt_of_le (unitInterval.nonneg t) with ht0 | ht0
    · have htzero : t = 0 := Subtype.ext ht0.symm
      rw [htzero, discScale_zero, hp.centre]
      exact ⟨_, hsmall _ (hp.centre ▸ mem_range_self polarCentre), rfl⟩
    · have hin : Φ (discScale t (polarDiscPoint 1 w)) ∈ cylinderToSphere '' e :=
        (ht ht0).mp (hxy.symm ▸ mem_image_of_mem _ hye)
      obtain ⟨z, _, hz⟩ := hin
      exact ⟨z, hsmall _ (hz.symm ▸ mem_range_self _), hz⟩

end GraphMinor.GM06
