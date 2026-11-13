module

public import GraphMinor.GM06.Defs
import GraphMinor.GM06.Section5InitialPathEdgeNotIncident
import GraphMinor.GM06.Section5InitialExtraEdgeStrip
import GraphMinor.GM06.Section5RegionPoint
import GraphMinor.GM06.Section5EndpointObstruction
import GraphMinor.GM06.Section4Overlap
import GraphMinor.GM06.Section4PathTools
import GraphMinor.GM11.CircuitRegions
import GraphMinor.GM11.Walks

/-!
# From first-contact vertices to first-contact point sets

For the region prefix in VI (5.1), page 129, its initial edge is
outside the old linkage: an initial linkage edge cannot be incident
with Rᵢ at a start of larger valency. A point of that edge witnesses
that the prefix is not contained in any old linkage path. The path
overlap lemma upgrades first contact at vertices to first contact at
all points. The rest of the prefix then lies in the strip itself.
-/

public section
namespace GraphMinor.GM06
open Set GraphMinor.Surface

private theorem exists_initial_prefix_edge
    {P : Drawing ClosedCylinder} {s t : ClosedCylinder} (hP : IsPathDrawing P s t) :
    ∃ e ∈ P.E, s ∈ closure e := by
  obtain ⟨W, _, _, _⟩ := hP.1
  cases W with
  | nil _ => exact False.elim ((isPathDrawing_start_ne_end hP) rfl)
  | @cons s v t e hl R =>
    exact ⟨e, hl.1, (show s ∈ closure e ∩ P.V from hl.2.2.2.symm ▸ mem_insert s {v}).1⟩

/-- A first-contact region prefix in the original graph meets the
old linkage only at its ends, and otherwise stays in Σᵢ. -/
theorem first_contact_prefix_point_contact_and_strip
    {k : ℕ} {G Q : Drawing ClosedCylinder} {θ : ℝ} (L : CylinderLinkage k G)
    (hk : 1 < k) (hG : IsCylinderSection5Drawing k G) (hθ : L.HasTheta θ)
    (hno : ¬ Section5AnyReductionApplies k G L) (i : Fin k)
    (hval : vertexValency G.toGraph (cylinderM1Point k i) ≠ 1)
    {v : ClosedCylinder} (hQG : Q.IsSubdrawing G) (hQ : IsPathDrawing Q (cylinderM1Point k i) v)
    (hQR : Q.U ⊆ closure (cylinderRegion k G i))
    (hcontact : Q.V ∩ (⋃ j : Fin k, (L.pathDrawing j).V) ⊆ {cylinderM1Point k i, v}) :
    Q.U ∩ (⋃ j : Fin k, (L.pathDrawing j).U) ⊆ {cylinderM1Point k i, v} ∧
      Q.U ⊆ cylinderStrip L i ∪ {cylinderM1Point k i, v} := by
  obtain ⟨e, heQ, hse⟩ := exists_initial_prefix_edge hQ
  have heG := hQG.2 heQ
  have heR : e ⊆ closure (cylinderRegion k G i) := fun x hx => hQR ((heQ.2.1 hx).1)
  have hePi : e ∉ (L.pathDrawing i).E := fun he =>
    initial_path_edge_not_subset_region_closure L hk hG hθ hno i hval he hse heR
  have hsPi : cylinderM1Point k i ∈ (L.pathDrawing i).U :=
    (L.pathDrawing i).V_subset_U (isPathDrawing_end_vertices (L.isPath i)).1
  have heL : ∀ j, e ∉ (L.pathDrawing j).E := by
    intro j
    by_cases hji : j = i
    · subst j; exact hePi
    · intro hej
      exact disjoint_left.mp (L.pairwise_disjoint hji)
        ((L.pathDrawing j).closure_subset_U hej hse) hsPi
  obtain ⟨p, hp⟩ := heG.1
  have hpQ : p ∈ Q.U := (heQ.2.1 hp).1
  have hpoints : Q.U ∩ (⋃ j : Fin k, (L.pathDrawing j).U) ⊆ {cylinderM1Point k i, v} := by
    rintro x ⟨hxQ, hxL⟩
    obtain ⟨j, hxj⟩ := mem_iUnion.mp hxL
    apply path_intersection_subset_ends_of_vertices hQG (L.isSubdrawing j).1 hQ
      (fun y hy => hcontact ⟨hy.1, mem_iUnion.mpr ⟨j, hy.2⟩⟩)
      ⟨p, hpQ, hp⟩ (GM11.edge_disjoint_U (L.isSubdrawing j).1 heG (heL j)).symm ⟨hxQ, hxj⟩
  refine ⟨hpoints, ?_⟩
  intro x hx
  by_cases hxL : x ∈ ⋃ j : Fin k, (L.pathDrawing j).U
  · exact Or.inr (hpoints ⟨hx, hxL⟩)
  · apply Or.inl
    exact (closure_cylinderStrip_subset_strip_union_linkage L hG i
      (closure_mono (cylinderRegion_subset_strip L i) (hQR hx))).resolve_right hxL

end GraphMinor.GM06
