module

public import GraphMinor.GM06.Defs
import GraphMinor.GM06.Section5RegionSectorEdge
import GraphMinor.GM06.Section5InitialExtraEdgeStrip
import GraphMinor.GM06.Section5StripBoundaryPaths
import GraphMinor.GM06.Section5ClosedStrip
import GraphMinor.GM06.Section5BranchArc
import GraphMinor.GM06.Section5AdjoinBoundary
import GraphMinor.GM06.Section5GapEdge
import GraphMinor.GM06.Section5BoundaryGap
import GraphMinor.GM06.Section5RegionPoint
import GraphMinor.GM06.Section5CappedRegions
import GraphMinor.GM06.Section5CappedPuncture
import GraphMinor.GM06.Section4PathTools
import GraphMinor.GM11.PerimeterPull
import GraphMinor.Surface.EdgeLens
import GraphMinor.Surface.InvarianceOfDomain

/-!
# The initial linkage edge is not incident with its following region

For the boundary-contact step of VI (5.1), page 129, suppose the
initial linkage edge were incident with Rᵢ. Together with the cuff
gap it would bound that region's unique corner in the capped sphere.
The sector comparison would put every extra edge outside the strip
near sᵢ. But Reduction 1 and the adjacent-strip neighbourhood put all
extra initial edges inside that strip. Thus such an edge cannot be
incident with Rᵢ when sᵢ has valency different from one.
-/

public section
namespace GraphMinor.GM06
open Set Topology GraphMinor.Surface

/-- In the unreduced situation of VI (5.1), if sᵢ has valency
different from one, an edge of Pᵢ incident with sᵢ is not incident
with Rᵢ. -/
theorem initial_path_edge_not_subset_region_closure_of_no_reductions12
    {k : ℕ} {G : Drawing ClosedCylinder} {θ : ℝ} (L : CylinderLinkage k G)
    (hk : 1 < k) (hG : IsCylinderSection5Drawing k G) (hθ : L.HasTheta θ)
    (hno1 : ∀ (G₁ : Drawing ClosedCylinder) (L₁ : CylinderLinkage k G₁),
      IsCylinderSection5Drawing k G₁ → ¬ Section5Reduction1Step k G L G₁ L₁)
    (hno2 : ∀ (G₁ : Drawing ClosedCylinder) (L₁ : CylinderLinkage k G₁),
      IsCylinderSection5Drawing k G₁ → ¬ Section5Reduction2Step k G L G₁ L₁) (i : Fin k)
    (hval : vertexValency G.toGraph (cylinderM1Point k i) ≠ 1)
    {a : Set ClosedCylinder} (haP : a ∈ (L.pathDrawing i).E)
    (hsa : cylinderM1Point k i ∈ closure a) :
    ¬ a ⊆ closure (cylinderRegion k G i) := by
  intro haR
  have haG := (L.isSubdrawing i).1.2 haP
  have hsPi : cylinderM1Point k i ∈ (L.pathDrawing i).U :=
    (L.pathDrawing i).V_subset_U (isPathDrawing_end_vertices (L.isPath i)).1
  have hsG : cylinderM1Point k i ∈ G.V :=
    (L.isSubdrawing i).1.1 (isPathDrawing_end_vertices (L.isPath i)).1
  obtain ⟨e, heG, v, _, hle, hePi⟩ := exists_extra_initial_edge_of_valency_ne_one_of_no_reduction2 L hG hno2 i hval
  have hse : cylinderM1Point k i ∈ closure e :=
    (show cylinderM1Point k i ∈ closure e ∩ G.V from hle.2.2.2.symm ▸ mem_insert _ {v}).1
  have heL : ∀ j, e ∉ (L.pathDrawing j).E := by
    intro j
    by_cases hji : j = i
    · subst j; exact hePi
    · intro hej
      exact disjoint_left.mp (L.pairwise_disjoint hji)
        ((L.pathDrawing j).closure_subset_U hej hse) hsPi
  have heStrip := initial_extra_edge_subset_following_strip_of_no_reduction1 L hG hθ hno1 i heG hse heL
  obtain ⟨F, hGF, hFU, hFV⟩ := exists_drawing_adjoining_boundary L hG
  obtain ⟨b, hbF, _, hbG, hbBd, hbR, hsb, _, _⟩ := exists_added_initial_gap_edge hG hGF hFU hFV i
  let D0 := closure (cylinderStrip L i)
  let D := cylinderToSphere '' D0
  let Y := cylinderToSphere '' (cylinderRegion k G i \ bd ClosedCylinder)
  have hD0 : IsClosedDisc D0 := isClosedDisc_closure_cylinderStrip L hk hG hθ i
  have hDimage := hD0.image_injOn continuous_cylinderToSphere.continuousOn injective_cylinderToSphere.injOn
  have hD : IsClosedDisc D := hDimage.1
  have hDb : discBd D = cylinderToSphere '' discBd D0 := hDimage.2
  have hD0bClosed : IsClosed (discBd D0) := hD0.isOArc_discBd.isCompact.isClosed
  have haD0 : closure a ⊆ discBd D0 :=
    ((L.pathDrawing i).closure_subset_U haP).trans (linkage_paths_subset_discBd_closure_strip L hk hG hθ i).1
  have hbD0 : closure b ⊆ discBd D0 := by
    apply closure_minimal ?_ hD0bClosed
    intro x hx
    exact mem_discBd_closure_strip_of_mem_cuff L hk hG hθ i
      (subset_closure (cylinderRegion_subset_strip L i (hbR hx))) (hbBd hx)
  have hYcl : closure Y = cylinderToSphere '' closure (cylinderRegion k G i) :=
    closure_image_region_sdiff_boundary (cylinderRegion_mem_regions hG i)
  have hY : Y ∈ (cylinderSphereDrawing F).R :=
    image_region_sdiff_boundary_mem_sphere_regions hFU (cylinderRegion_mem_regions hG i)
  have hcr : cylinderToSphere (cylinderM1Point k i) ∈ closure Y := by
    rw [hYcl]
    exact mem_image_of_mem _ (initial_vertices_mem_closure_cylinderRegion hG i).1
  have hYrD : Y ⊆ D := by
    rintro x ⟨y, hy, rfl⟩
    exact mem_image_of_mem cylinderToSphere (subset_closure (cylinderRegion_subset_strip L i hy.1))
  have hclos (d : Set ClosedCylinder) : closure (cylinderToSphere '' d) = cylinderToSphere '' closure d :=
    isClosedEmbedding_cylinderToSphere.closure_image_eq d
  have hedge (d : Set ClosedCylinder) (hd : d ∈ F.E) : cylinderToSphere '' d ∈ (cylinderSphereDrawing F).E := by
    rw [cylinderSphereDrawing_E]
    exact mem_image_of_mem _ hd
  have hinj : Function.Injective (image cylinderToSphere) := injective_cylinderToSphere.image_injective
  have hab : cylinderToSphere '' a ≠ cylinderToSphere '' b :=
    fun h => hbG (hinj h ▸ haG)
  have hea : cylinderToSphere '' e ≠ cylinderToSphere '' a :=
    fun h => hePi (hinj h ▸ haP)
  have heb : cylinderToSphere '' e ≠ cylinderToSphere '' b :=
    fun h => hbG (hinj h ▸ heG)
  have hca : cylinderToSphere (cylinderM1Point k i) ∈ closure (cylinderToSphere '' a) := by
    rw [hclos]; exact mem_image_of_mem _ hsa
  have hcb : cylinderToSphere (cylinderM1Point k i) ∈ closure (cylinderToSphere '' b) := by
    rw [hclos]; exact mem_image_of_mem _ hsb
  have hce : cylinderToSphere (cylinderM1Point k i) ∈ closure (cylinderToSphere '' e) := by
    rw [hclos]; exact mem_image_of_mem _ hse
  have haY : cylinderToSphere '' a ⊆ closure Y := by rw [hYcl]; exact image_mono haR
  have hbY : cylinderToSphere '' b ⊆ closure Y := by rw [hYcl]; exact image_mono (hbR.trans subset_closure)
  have haD : closure (cylinderToSphere '' a) ⊆ discBd D := by rw [hclos, hDb]; exact image_mono haD0
  have hbD : closure (cylinderToSphere '' b) ⊆ discBd D := by rw [hclos, hDb]; exact image_mono hbD0
  have hcV : cylinderToSphere (cylinderM1Point k i) ∈ (cylinderSphereDrawing F).V := by
    rw [cylinderSphereDrawing_V, hFV]; exact mem_image_of_mem _ hsG
  have hsph : IsSphere (OnePoint EuclideanPlane) := ⟨Homeomorph.refl _⟩
  have hS := GM11.IsSphere.isClosedSurface hsph
  let : ConnectedSpace (OnePoint EuclideanPlane) := hS.2
  have hpun := (isConnected_punctured_cylinderSphereDrawing_of_no_reduction2 L hk hG hno2 hFU i).isPreconnected
  have hnot := not_subset_disc_of_two_incident_boundary_edges hS.1 hsph hcV hpun hY hcr hD hYrD
    (hedge a (hGF.2 haG)) (hedge b hbF) hab hca hcb haY hbY haD hbD
    (hedge e (hGF.2 heG)) hea heb hce
  exact hnot (image_mono (heStrip.trans subset_closure))

/-- The unreduced case in VI (5.1) excludes Reductions 1 and 2. -/
theorem initial_path_edge_not_subset_region_closure
    {k : ℕ} {G : Drawing ClosedCylinder} {θ : ℝ} (L : CylinderLinkage k G)
    (hk : 1 < k) (hG : IsCylinderSection5Drawing k G) (hθ : L.HasTheta θ)
    (hno : ¬ Section5AnyReductionApplies k G L) (i : Fin k)
    (hval : vertexValency G.toGraph (cylinderM1Point k i) ≠ 1)
    {a : Set ClosedCylinder} (haP : a ∈ (L.pathDrawing i).E)
    (hsa : cylinderM1Point k i ∈ closure a) :
    ¬ a ⊆ closure (cylinderRegion k G i) := by
  exact initial_path_edge_not_subset_region_closure_of_no_reductions12 L hk hG hθ
    (fun G₁ L₁ hG₁ hRed => hno ⟨G₁, L₁, hG₁, Or.inl hRed⟩)
    (fun G₁ L₁ hG₁ hRed => hno ⟨G₁, L₁, hG₁, Or.inr (Or.inl hRed)⟩) i hval haP hsa

end GraphMinor.GM06
