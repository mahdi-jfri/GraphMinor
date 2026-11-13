module

public import GraphMinor.GM06.Defs
import GraphMinor.GM06.Section5LiftedInitialEdgeNeighbourhood
import GraphMinor.GM06.Section5RegionInterior
import GraphMinor.GM06.Section4
import GraphMinor.GM06.Section5CoverLocalHomeomorph
import GraphMinor.GM06.Section5LiftedEdgeIncidence
import GraphMinor.GM06.Section5ContractionCoverFibre
import GraphMinor.GM06.Section5CoverSides
import GraphMinor.GM07.Section11f
import Mathlib.Topology.Algebra.Module.LocallyConvex

/-!
# A lifted region at an initial vertex meets the initial edge

In the sheet-sensitive Reduction 3 argument of VI (5.5), page 130,
a complementary component approaching the initial lift also approaches
the lifted edge interior. Otherwise a small connected neighbourhood,
with its cuff removed, would split between that component and the
complement of its closure. The neighbourhood constructed earlier
excludes every other possible boundary point of the component.
-/

public section
namespace GraphMinor.GM06
open Set Topology GraphMinor.Surface

/-- A lifted complementary component incident with a valency-one
initial vertex is incident with the specified lifted edge interior. -/
theorem lifted_initial_region_meets_edge_interior
    {k : ℕ} {G F : Drawing ClosedCylinder} (hG : IsCylinderSection5Drawing k G)
    (hFU : F.U = G.U ∪ bd ClosedCylinder) (i : Fin k)
    {e : Set ClosedCylinder} {v : ClosedCylinder}
    (hval : vertexValency G.toGraph (cylinderM1Point k i) = 1)
    (hl : G.toGraph.IsLink e (cylinderM1Point k i) v) (hv : v ≠ cylinderM1Point k i)
    (γ : Curve ClosedCylinder) (hγ : ParametrizesSet γ (closure e) (cylinderM1Point k i) v)
    (q : C(unitInterval, CylinderCover)) (hq : ∀ t, cylinderCoverProjection (q t) = γ t)
    {r : Set CylinderCover} (hr : r ∈ componentsIn (cylinderCoverProjection ⁻¹' F.Uᶜ))
    (hcontact : q 0 ∈ closure r) : (q '' Ioo 0 1 ∩ closure r).Nonempty := by
  let : LocallyPathConnectedSpace (Icc (1 : ℝ) 2) := (convex_Icc (1 : ℝ) 2).locallyPathConnectedSpace
  let : LocallyConnectedSpace CylinderCover := inferInstance
  let : LocallyConnectedSpace ClosedCylinder := IsSurface.locallyConnected isSurface_closedCylinder
  obtain ⟨η, hqη, hη⟩ := isLocalHomeomorph_cylinderCoverProjection (q 0)
  obtain ⟨N, hNo, hNpre, hsN, hNT, hNlocal⟩ :=
    exists_initial_edge_neighbourhood_in_cover_chart i hval hl hv γ hγ q hq η hη hqη
  have hinv (x) (hx : x ∈ N) : cylinderCoverProjection (η.symm x) = x := by
    rw [hη, η.right_inv (hNT hx)]
  let O := η.symm '' N
  have hOo : IsOpen O := η.isOpen_image_symm_of_subset_target hNo hNT
  have hqO : q 0 ∈ O := by
    refine ⟨cylinderM1Point k i, hsN, ?_⟩
    rw [← hγ.2.2.1, ← hq 0, hη, η.left_inv hqη]
  let Q := η.symm '' (N \ bd ClosedCylinder)
  have hQeq : Q = O \ cylinderCoverProjection ⁻¹' bd ClosedCylinder := by
    ext z
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact ⟨⟨x, hx.1, rfl⟩, by change cylinderCoverProjection (η.symm x) ∉ bd ClosedCylinder; rw [hinv x hx.1]; exact hx.2⟩
    · rintro ⟨⟨x, hx, heq⟩, hz⟩
      refine ⟨x, ⟨hx, ?_⟩, heq⟩
      have he : cylinderCoverProjection z = x := heq ▸ hinv x hx
      exact he ▸ hz
  have hQpre : IsPreconnected Q :=
    (GM07.isPreconnected_diff_bd isSurface_closedCylinder hNo hNpre).image η.symm
      (η.symm.continuousOn.mono (fun x hx => hNT hx.1))
  have hrsub : r ⊆ cylinderCoverProjection ⁻¹' F.Uᶜ := by
    obtain ⟨x, _, rfl⟩ := hr
    exact connectedComponentIn_subset _ _
  have hro : IsOpen r := by
    obtain ⟨x, _, rfl⟩ := hr
    exact (F.isClosed_U.preimage continuous_cylinderCoverProjection).isOpen_compl.connectedComponentIn
  have hcl := closure_component_complement_subset
    (F.isClosed_U.preimage continuous_cylinderCoverProjection) hr
  by_contra hno
  have hlocal : ∀ z ∈ Q, z ∈ closure r → z ∈ r := by
    intro z hz hzr
    rcases hcl hzr with hzR | hzFU
    · exact hzR
    · have hzshape := hQeq ▸ hz
      have hzoff : cylinderCoverProjection z ∉ bd ClosedCylinder := hzshape.2
      obtain ⟨x, hxN, hxz⟩ := hzshape.1
      have hzx : cylinderCoverProjection z = x := hxz ▸ hinv x hxN
      change cylinderCoverProjection z ∈ F.U at hzFU
      rw [hFU] at hzFU
      rcases hzFU with hzG | hzbd
      · have hxG : x ∈ G.U := hzx ▸ hzG
        rcases hNlocal x ⟨hxN, hxG⟩ with hx0 | hxedge
        · have hz0 : z = q 0 := hxz.symm.trans hx0
          apply False.elim
          apply hzoff
          rw [hz0, hq, hγ.2.2.1]
          rw [bd_closedCylinder]
          exact Or.inl rfl
        · exact False.elim (hno ⟨z, hxz ▸ hxedge, hzr⟩)
      · exact False.elim (hzoff hzbd)
  obtain ⟨x, hxO, hxr⟩ := mem_closure_iff.mp hcontact O hOo hqO
  have hxoff : cylinderCoverProjection x ∉ bd ClosedCylinder := by
    intro hx
    exact hrsub hxr (hFU ▸ Or.inr hx)
  have hxQ : x ∈ Q := hQeq.symm ▸ ⟨hxO, hxoff⟩
  have hqcl : q 0 ∈ closure (q '' Ioo 0 1) := by
    apply mem_closure_image q.continuous.continuousAt
    rw [closure_Ioo (show (0 : unitInterval) ≠ 1 from zero_ne_one)]
    exact ⟨le_rfl, zero_le_one⟩
  obtain ⟨y, hyO, t, ht, hty⟩ := mem_closure_iff.mp hqcl O hOo hqO
  have hte : γ t ∈ e := image_Ioo_of_parametrizesSet_closure_edge hl γ hγ ▸ mem_image_of_mem γ ht
  have htoff : cylinderCoverProjection (q t) ∉ bd ClosedCylinder := by
    rw [hq]
    intro hb
    exact (hl.1.2.1 hte).2 (hG.2.1 ⟨hb, (hl.1.2.1 hte).1⟩)
  have hyQ : y ∈ Q := hQeq.symm ▸ ⟨hyO, hty ▸ htoff⟩
  have hycl : y ∉ closure r := fun hy => hno ⟨y, ⟨t, ht, hty⟩, hy⟩
  obtain ⟨z, _, hzr, hznot⟩ := hQpre r (closure r)ᶜ hro isClosed_closure.isOpen_compl
    (fun z hz => by
      by_cases hzr : z ∈ closure r
      · exact Or.inl (hlocal z hz hzr)
      · exact Or.inr hzr) ⟨x, hxQ, hxr⟩ ⟨y, hyQ, hycl⟩
  exact hznot (subset_closure hzr)

end GraphMinor.GM06
