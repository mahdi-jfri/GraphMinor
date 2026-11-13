module

public import GraphMinor.GM06.Alg511FiniteRegions
public import GraphMinor.Compute.GM06SuccessorGraphRep
import GraphMinor.GM11.PerimeterPull
import GraphMinor.GM11.Regions
import GraphMinor.GM11.Walks
import GraphMinor.GM11.Section4c
import GraphMinor.GM06.Section5RegionInterior
import Mathlib.Tactic

/-!
# Finite boundary incidence for cylinder input regions

The input coverage of VI (5.11), page 134, describes every region
before maximum flow is run. Adjoin the cuffs without a linkage and
transfer edge incidence to the sphere. Incidence at one edge point
then gives the whole edge. Hence a region's boundary is exactly the
union of its incident original vertices and edges, each of which
has a supplied finite label.
-/

public section
namespace GraphMinor.GM06
open Set GraphMinor.Surface GraphMinor.GM11 GraphMinor.Compute

/-- A cylinder region incident with a point of an edge is incident
with the whole closed edge, including both ends. -/
theorem alg511_closure_edge_subset_closure_region_of_incident
    {k : ℕ} {G : Drawing ClosedCylinder} (hG : IsCylinderSection5Drawing k G) {e R : Set ClosedCylinder}
    (he : e ∈ G.E) (hR : R ∈ G.R) (hinc : (e ∩ closure R).Nonempty) :
    closure e ⊆ closure R := by
  obtain ⟨F, _, _, hGF, hFU, _⟩ := alg511_exists_drawing_with_cuffs hG
  have heF : e ∈ F.E := hGF.2 he
  have hes : cylinderToSphere '' e ∈ (cylinderSphereDrawing F).E := by
    rw [cylinderSphereDrawing_E]
    exact mem_image_of_mem _ heF
  have hRS := image_region_sdiff_boundary_mem_sphere_regions hFU hR
  have hS : IsClosedSurface (OnePoint EuclideanPlane) :=
    (GraphMinor.GM11.IsSphere.isClosedSurface ⟨Homeomorph.refl _⟩).1
  have hi : (cylinderToSphere '' e ∩
      closure (cylinderToSphere '' (R \ bd ClosedCylinder))).Nonempty := by
    obtain ⟨x, hxe, hxR⟩ := hinc
    rw [closure_image_region_sdiff_boundary hR]
    exact ⟨cylinderToSphere x, mem_image_of_mem _ hxe, mem_image_of_mem _ hxR⟩
  have hedge := GraphMinor.GM11.edge_subset_closure_of_incident hS hes hRS hi
  apply closure_minimal _ isClosed_closure
  intro x hx
  have hxr := hedge (mem_image_of_mem cylinderToSphere hx)
  rw [closure_image_region_sdiff_boundary hR] at hxr
  obtain ⟨y, hy, heq⟩ := hxr
  exact injective_cylinderToSphere heq ▸ hy

/-- Each region boundary of the cylinder input is a union of whole
original vertices and edges, without any linkage-existence assumption. -/
theorem alg511_region_boundary_eq {k : ℕ} {G : Drawing ClosedCylinder}
    (hG : IsCylinderSection5Drawing k G) {r : Set ClosedCylinder} (hr : r ∈ G.R) :
    closure r \ r = (G.V ∩ closure r) ∪ ⋃ e ∈ {e ∈ G.E | e ⊆ closure r}, e := by
  let : LocallyConnectedSpace ClosedCylinder := IsSurface.locallyConnected isSurface_closedCylinder
  ext p
  constructor
  · intro hp
    have hpU : p ∈ G.U := (closure_region_subset hr hp.1).resolve_left hp.2
    by_cases hpV : p ∈ G.V
    · exact Or.inl ⟨hpV, hp.1⟩
    · obtain ⟨e, he, hpe⟩ := G.exists_edge_of_mem hpU hpV
      have hsub : e ⊆ closure r := subset_closure.trans
        (alg511_closure_edge_subset_closure_region_of_incident hG he hr ⟨p, hpe, hp.1⟩)
      exact Or.inr (mem_iUnion₂.mpr ⟨e, ⟨he, hsub⟩, hpe⟩)
  · rintro (hp | hp)
    · exact ⟨hp.2, fun hpr => region_subset hr hpr (G.V_subset_U hp.1)⟩
    · obtain ⟨e, ⟨he, hsub⟩, hpe⟩ := mem_iUnion₂.mp hp
      exact ⟨hsub hpe, fun hpr => region_subset hr hpr ((he.2.1 hpe).1)⟩

/-- Every input region has finite lists of its incident vertex and
edge labels, with their exact actual boundary interpretation. -/
theorem alg511_exists_region_boundary_labels {k : ℕ} {G : Drawing ClosedCylinder}
    (hG : IsCylinderSection5Drawing k G) (x : GM06SuccessorInput)
    (rep : GM06SuccessorGraphRep x G.toGraph) {r : Set ClosedCylinder} (hr : r ∈ G.R) :
    ∃ (vs : List (Fin x.vertexCount)) (es : List (Fin rep.pairs.length)),
      vs.Nodup ∧ es.Nodup ∧ closure r \ r =
        {p | ∃ i ∈ vs, (rep.vertex i).val = p} ∪ ⋃ j ∈ es, (rep.edge j).val := by
  classical
  let vs := (Finset.univ.filter (fun i => (rep.vertex i).val ∈ closure r)).toList
  let es := (Finset.univ.filter (fun j => (rep.edge j).val ⊆ closure r)).toList
  refine ⟨vs, es, Finset.nodup_toList _, Finset.nodup_toList _, ?_⟩
  rw [alg511_region_boundary_eq hG hr]
  apply congrArg₂ (· ∪ ·)
  · ext p
    constructor
    · rintro ⟨hpV, hpr⟩
      obtain ⟨i, hi⟩ := rep.vertex.surjective ⟨p, hpV⟩
      have hi' := congrArg Subtype.val hi
      refine ⟨i, ?_, hi'⟩
      simpa only [vs, Finset.mem_toList, Finset.mem_filter, Finset.mem_univ, true_and, hi'] using hpr
    · rintro ⟨i, hi, rfl⟩
      exact ⟨(rep.vertex i).property, by
        simpa only [vs, Finset.mem_toList, Finset.mem_filter, Finset.mem_univ, true_and] using hi⟩
  · ext p
    simp only [mem_iUnion, exists_prop, mem_ofPred_eq]
    constructor
    · rintro ⟨f, ⟨hf, hsub⟩, hpf⟩
      obtain ⟨j, hj⟩ := rep.edge.surjective ⟨f, hf⟩
      have hj' := congrArg Subtype.val hj
      refine ⟨j, ?_, hj'.symm ▸ hpf⟩
      simpa only [es, Finset.mem_toList, Finset.mem_filter, Finset.mem_univ, true_and, hj'] using hsub
    · rintro ⟨j, hj, hpj⟩
      refine ⟨(rep.edge j).val, ⟨(rep.edge j).property, ?_⟩, hpj⟩
      simpa only [es, Finset.mem_toList, Finset.mem_filter, Finset.mem_univ, true_and] using hj

end GraphMinor.GM06
