module

public import GraphMinor.GM06.Defs
public import GraphMinor.GM06.Section5CapDrawing
public import GraphMinor.GM11.LocalCone
import GraphMinor.GM06.Section5ContractionNeighbourEdges
import GraphMinor.GM11.PerimeterPull
import GraphMinor.GM11.OArcCircuit
import GraphMinor.GM11.Walks
import GraphMinor.GM06.Section5SeparationGeometry

/-!
# Polar charts at attachment vertices and contraction neighbours

In Reduction 3 of VI (5.5), page 130, the old neighbour has both
the contracted edge and a distinct edge of the linkage suffix.
Their images in the capped drawing give two distinct half-edges.
The finite-drawing polar-chart theorem then provides the chart
used to construct access curves in a specified angular sheet.
-/

public section
namespace GraphMinor.GM06
open Set GraphMinor.Surface GraphMinor.GM11

private theorem exists_polar_of_two_incident_edges
    {S : Type*} [TopologicalSpace S] (hS : IsClosedSurface S) (Γ : Drawing S)
    {v : S} (hv : v ∈ Γ.V) {a b : Set S} (ha : a ∈ Γ.E) (hb : b ∈ Γ.E)
    (hab : a ≠ b) (hva : v ∈ closure a) (hvb : v ∈ closure b) :
    ∃ Φ, IsPolar Γ v Φ := by
  classical
  let : T2Space S := hS.2.1
  let : Nonempty S := ⟨v⟩
  obtain ⟨γ, hγ⟩ := exists_edgePar Γ
  obtain ⟨ba, hba⟩ := exists_end_eq hγ ha hv hva
  obtain ⟨bb, hbb⟩ := exists_end_eq hγ hb hv hvb
  let ka : halfEdges Γ γ v := ⟨(a, ba), ha, hba⟩
  let kb : halfEdges Γ γ v := ⟨(b, bb), hb, hbb⟩
  have hne : ka ≠ kb := fun h => hab (congrArg (fun j : halfEdges Γ γ v => j.1.1) h)
  let : Finite (halfEdges Γ γ v) := (finite_halfEdges Γ γ v).to_subtype
  have h2 : 2 ≤ Nat.card (halfEdges Γ γ v) := by
    have hh := ncard_le_card ({ka, kb} : Set (halfEdges Γ γ v))
    rwa [ncard_pair hne] at hh
  exact exists_isPolar_of_sectors hS hγ hv h2

private theorem exists_edge_at_start_of_path
    {S : Type*} [TopologicalSpace S] {P : Drawing S} {v w : S}
    (hP : P.IsPathBetween v w) (hvw : v ≠ w) : ∃ e ∈ P.E, v ∈ closure e := by
  obtain ⟨W, _, _, _⟩ := hP
  cases W with
  | nil _ => exact False.elim (hvw rfl)
  | @cons v u w e hl R =>
    exact ⟨e, hl.1, (show v ∈ closure e ∩ P.V from hl.2.2.2.symm ▸ mem_insert v {u}).1⟩

/-- An O-arc of a drawing with two distinct vertices supplies two
incident edges and hence the polar chart used for the attached
seed-disc construction in VI (5.5), page 130. -/
theorem exists_polar_at_vertex_on_oArc
    {S : Type*} [TopologicalSpace S] [ConnectedSpace S]
    (hS : IsClosedSurface S) (Γ : Drawing S) {B : Set S} (hB : IsOArc B)
    (hBU : B ⊆ Γ.U) {v w : S} (hv : v ∈ Γ.V) (hw : w ∈ Γ.V)
    (hvB : v ∈ B) (hwB : w ∈ B) (hvw : v ≠ w) : ∃ Φ, IsPolar Γ v Φ := by
  let : T2Space S := hS.2.1
  obtain ⟨C, hC, hCΓ, hCU⟩ := exists_circuit_of_oArc hB hBU
  have hvC : v ∈ C.V := vertex_mem_of_mem_subdrawing_point_set hCΓ (hCU.symm ▸ hvB) hv
  have hwC : w ∈ C.V := vertex_mem_of_mem_subdrawing_point_set hCΓ (hCU.symm ▸ hwB) hw
  obtain ⟨P, Q, hP, hQ, hPC, hQC, _, _, _, hPQ, _⟩ :=
    Drawing.IsCircuit.exists_two_paths hC hvC hwC hvw
  obtain ⟨a, ha, hva⟩ := exists_edge_at_start_of_path hP hvw
  obtain ⟨b, hb, hvb⟩ := exists_edge_at_start_of_path hQ hvw
  have hab : a ≠ b := fun he => disjoint_left.mp hPQ ha (he.symm ▸ hb)
  exact exists_polar_of_two_incident_edges hS Γ hv (hCΓ.2 (hPC.2 ha))
    (hCΓ.2 (hQC.2 hb)) hab hva hvb

/-- The neighbour in Reduction 3 has a polar chart in any capped
cylinder drawing containing the old drawing. -/
theorem exists_polar_at_contraction_neighbour
    {k : ℕ} {G F : Drawing ClosedCylinder} (L : CylinderLinkage k G) (i : Fin k)
    (hGF : G.IsSubdrawing F) {e : Set ClosedCylinder} {v : ClosedCylinder}
    (hval : vertexValency G.toGraph (cylinderM1Point k i) = 1)
    (hl : G.toGraph.IsLink e (cylinderM1Point k i) v)
    (hv : v ≠ cylinderM1Point k i) (hvC : v ∉ cylinderCuff2) :
    ∃ Φ : C(ClosedUnitDisc, OnePoint EuclideanPlane),
      IsPolar (cylinderSphereDrawing F) (cylinderToSphere v) Φ := by
  obtain ⟨f, hf, hfe, hvf⟩ := exists_second_edge_at_contraction_neighbour L i hval hl hv hvC
  have heS : cylinderToSphere '' e ∈ (cylinderSphereDrawing F).E := by
    rw [cylinderSphereDrawing_E]
    exact mem_image_of_mem _ (hGF.2 hl.1)
  have hfS : cylinderToSphere '' f ∈ (cylinderSphereDrawing F).E := by
    rw [cylinderSphereDrawing_E]
    exact mem_image_of_mem _ (hGF.2 hf)
  have hvS : cylinderToSphere v ∈ (cylinderSphereDrawing F).V := by
    rw [cylinderSphereDrawing_V]
    exact mem_image_of_mem _ (hGF.1 hl.2.2.1)
  have hneS : cylinderToSphere '' e ≠ cylinderToSphere '' f :=
    fun heq => hfe ((Set.image_injective.mpr injective_cylinderToSphere) heq.symm)
  have hve : v ∈ closure e := by
    have hh : v ∈ closure e ∩ G.V := hl.2.2.2 ▸ mem_insert_of_mem _ rfl
    exact hh.1
  have hveS : cylinderToSphere v ∈ closure (cylinderToSphere '' e) := by
    rw [isClosedEmbedding_cylinderToSphere.closure_image_eq]
    exact mem_image_of_mem _ hve
  have hvfS : cylinderToSphere v ∈ closure (cylinderToSphere '' f) := by
    rw [isClosedEmbedding_cylinderToSphere.closure_image_eq]
    exact mem_image_of_mem _ hvf
  have hS : IsClosedSurface (OnePoint EuclideanPlane) :=
    (GraphMinor.GM11.IsSphere.isClosedSurface ⟨Homeomorph.refl _⟩).1
  exact exists_polar_of_two_incident_edges hS (cylinderSphereDrawing F)
    hvS heS hfS hneS hveS hvfS

end GraphMinor.GM06
