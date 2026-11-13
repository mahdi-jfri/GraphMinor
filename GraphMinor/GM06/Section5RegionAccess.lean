module

public import GraphMinor.GM06.Defs
import GraphMinor.GM06.Section5CappedRegions
import GraphMinor.GM11.Theorem75
import GraphMinor.GM06.Section5RegionInterior
import GraphMinor.GM11.RadialChord

/-!
# Access to a vertex through a cylinder region

Adjoin the cuffs and use vertex access in the sphere. Pull the resulting
curve back to the cylinder. Surface charts give local path connectedness,
so a chord in the region can start at any prescribed region point.
-/

public section
open Set Topology GraphMinor.Surface Filter
universe u
namespace GraphMinor.GM06
private theorem locallyPathConnectedSpace_of_manifold_points {S : Type u} [TopologicalSpace S] (hS : ∀ x : S, IsManifoldPoint x) :
    LocallyPathConnectedSpace S := by
  refine ⟨fun x => ⟨fun U => ⟨fun hU => ?_, fun h => ?_⟩⟩⟩
  swap
  · obtain ⟨s, ⟨hs, -⟩, hsub⟩ := h
    exact mem_of_superset hs hsub
  obtain ⟨V, W, hV, hW, hxV, ⟨h⟩⟩ := hS x
  let : LocallyPathConnectedSpace W := hW.locallyPathConnectedSpace
  let T : W → S := fun y => (h.symm y).1
  have hTe : IsOpenEmbedding T := hV.isOpenEmbedding_subtypeVal.comp h.symm.isOpenEmbedding
  let c : W := h ⟨x, hxV⟩
  have hTc : T c = x := by simp [T, c]
  have hU' : T ⁻¹' U ∈ 𝓝 c := (hTe.continuous.tendsto c).mono_right (by rw [hTc]) hU
  obtain ⟨s, ⟨hs, hsp⟩, hsub⟩ := (path_connected_basis c).mem_iff.mp hU'
  refine ⟨T '' s, ⟨?_, hsp.image hTe.continuous⟩, image_subset_iff.mpr hsub⟩
  rw [← hTc, ← hTe.map_nhds_eq]
  exact image_mem_map hs

open GraphMinor.GM11
/-- A curve from a point of a cylinder region to an incident vertex,
inside the region before its last parameter, as used in VI (5.3), page 132. -/
theorem exists_curve_from_region_point_to_vertex {G F : Drawing ClosedCylinder} (hFU : F.U = G.U ∪ bd ClosedCylinder)
    (hFV : F.V = G.V) {r : Set ClosedCylinder} (hr : r ∈ G.R)
    {x v : ClosedCylinder} (hx : x ∈ r) (hv : v ∈ G.V) (hvr : v ∈ closure r) :
    ∃ f : Curve ClosedCylinder, Function.Injective f ∧ f 0 = x ∧ f 1 = v ∧
      ∀ t : unitInterval, t < 1 → f t ∈ r := by
  classical
  have hsph : IsSphere (OnePoint EuclideanPlane) := ⟨Homeomorph.refl _⟩
  have hS := GM11.IsSphere.isClosedSurface hsph
  have hvs : cylinderToSphere v ∈ (cylinderSphereDrawing F).V := by
    rw [cylinderSphereDrawing_V, hFV]
    exact mem_image_of_mem _ hv
  have hreg := image_region_sdiff_boundary_mem_sphere_regions hFU hr
  have hvcl : cylinderToSphere v ∈ closure (cylinderToSphere '' (r \ bd ClosedCylinder)) := by
    rw [closure_image_region_sdiff_boundary hr]
    exact mem_image_of_mem _ hvr
  obtain ⟨g, hg, hg0, hgp⟩ := exists_path_into_region hS.1 (cylinderSphereDrawing F) hvs hreg hvcl
  have him : ∀ t, ∃ p : ClosedCylinder, cylinderToSphere p = g t := by
    intro t
    by_cases ht : t = 0
    · exact ⟨v, by rw [ht, hg0]⟩
    · obtain ⟨p, _, hp⟩ := hgp t (unitInterval.pos_iff_ne_zero.mpr ht)
      exact ⟨p, hp⟩
  choose a ha using him
  have hac : Continuous a := isClosedEmbedding_cylinderToSphere.isEmbedding.continuous_iff.mpr (by
    have he : cylinderToSphere ∘ a = g := funext ha
    rw [he]
    exact hg)
  have ha0 : a 0 = v := injective_cylinderToSphere ((ha 0).trans hg0)
  have hap : ∀ t, 0 < t → a t ∈ r := by
    intro t ht
    obtain ⟨p, hp, hpeq⟩ := hgp t ht
    have he : a t = p := injective_cylinderToSphere ((ha t).trans hpeq.symm)
    exact he.symm ▸ hp.1
  let : LocallyConnectedSpace ClosedCylinder := IsSurface.locallyConnected isSurface_closedCylinder
  let : LocallyPathConnectedSpace ClosedCylinder :=
    locallyPathConnectedSpace_of_manifold_points isSurface_closedCylinder.2.2
  have hrpath : IsPathConnected r := (region_isOpen hr).isConnected_iff_isPathConnected.mp
    ⟨⟨x, hx⟩, region_isPreconnected hr⟩
  have hvoff : v ∉ r := fun h => region_subset hr h (G.V_subset_U hv)
  obtain ⟨e, hec, hei, he0, he1, hep, _⟩ :=
    exists_chord_to_point hrpath hvoff hx hac ha0 hap
  let f : Curve ClosedCylinder := ⟨fun t => e (unitInterval.symm t), hec.comp (by fun_prop)⟩
  refine ⟨f, ?_, ?_, ?_, ?_⟩
  · intro s t h
    have hh := congrArg unitInterval.symm (hei h)
    simpa using hh
  · change e (unitInterval.symm 0) = x
    simpa using he1
  · change e (unitInterval.symm 1) = v
    simpa using he0
  · intro t ht
    apply hep
    intro hh
    have ht1 : t = 1 := by simpa using congrArg unitInterval.symm hh
    exact ht.ne ht1
end GraphMinor.GM06
