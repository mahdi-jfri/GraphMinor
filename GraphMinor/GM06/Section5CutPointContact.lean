module

public import GraphMinor.GM06.Section5CutBoundaryEdgeExclusion
public import GraphMinor.GM06.Section5CutBoundaryDrawing
import GraphMinor.GM06.Section5CutBoundaryVertices
import GraphMinor.GM06.Section5EndpointObstruction
import GraphMinor.GM06.Section4Overlap
import GraphMinor.GM06.Section4PathTools
import GraphMinor.GM11.Walks

/-!
# The first-contact cut path meets the boundary only at its ends

The initial edge of the region prefix cannot lie on the cut-disc
boundary, since the prefix avoids the gap edge and every other
boundary edge there is excluded by the corner argument. A point of
this initial edge lies off the boundary subdrawing. The path-overlap
lemma therefore upgrades first contact at boundary vertices to
first contact at all boundary points. This supplies the path inside
the cut strip in the one-path proof of VI (5.1), page 129.
-/

public section
namespace GraphMinor.GM06
open Set Topology Real GraphMinor.Surface

private theorem exists_initial_edge_of_cut_path
    {S : Type*} [TopologicalSpace S] [T2Space S] {Q : Drawing S} {s t : S}
    (hQ : IsPathDrawing Q s t) : ∃ e ∈ Q.E, s ∈ closure e := by
  obtain ⟨W, _, _, _⟩ := hQ.1
  cases W with
  | nil _ => exact False.elim ((isPathDrawing_start_ne_end hQ) rfl)
  | @cons s v t e hl R =>
    exact ⟨e, hl.1, (show s ∈ closure e ∩ Q.V from hl.2.2.2.symm ▸ mem_insert s {v}).1⟩

/-- At larger initial valency, the first-contact region prefix meets
the whole cut-disc boundary only at its two ends. -/
theorem cut_first_contact_path_point_contact
    {G : Drawing ClosedCylinder} {θ : ℝ} (L : CylinderLinkage 1 G)
    (hG : IsCylinderSection5Drawing 1 G) (hθ : L.HasTheta θ)
    (hno : ¬ Section5AnyReductionApplies 1 G L)
    (hval : vertexValency G.toGraph (cylinderM1Point 1 0) ≠ 1)
    {D : Set (ℝ × ℝ)} (hD : IsClosedDisc D)
    (hBd : discBd D = liftedStripBoundary hG.1 L 1)
    (hstrip : D ⊆ {p : ℝ × ℝ | 1 ≤ p.1 ∧ p.1 ≤ 2})
    (F : Drawing D)
    (hFU : F.U = (fun p : D => radialCylinderProjection p.1) ⁻¹' G.U ∪ bd D)
    (hFV : F.V = (fun p : D => radialCylinderProjection p.1) ⁻¹' G.V)
    (hEdges : ∀ ec ∈ F.E, ec ⊆ bd D ∨
      ∃ e ∈ G.E \ (L.pathDrawing 0).E, ec = (fun p : D => radialCylinderProjection p.1) ⁻¹' e)
    (g : Curve D) (hgcoord : ∀ t, (g t).1 = (1, 2 * (1 + (t : ℝ)) * π))
    {v : D} {Q : Drawing D} (hQ : IsSubpathOf F Q (g 0) v)
    (hQR : (fun p : D => planeToCylinderCover p.1) '' Q.U ⊆ closure (cylinderCoverRegion 1 G 0))
    (hcontact : Q.V ∩ (fun p : D => radialCylinderProjection p.1) ⁻¹' (L.pathDrawing 0).V ⊆ {g 0, v})
    {b : Set D} (hb : b ∈ F.E) (hbBd : b ⊆ bd D) (hgap : g '' Ioo 0 1 ⊆ b)
    (hbQ : b ∉ Q.E) :
    Q.U ⊆ closure (((fun p : D => planeToCylinderCover p.1) ⁻¹' cylinderCoverRegion 1 G 0) \ bd D) ∧
      Q.U ∩ bd D ⊆ {g 0, v} := by
  have hEdges' : ∀ ec ∈ F.E, ec ⊆ bd D ∨
      ∃ e ∈ G.E, ec = (fun p : D => radialCylinderProjection p.1) ⁻¹' e := by
    intro ec hec
    rcases hEdges ec hec with hbd | ⟨e, he, heq⟩
    · exact Or.inl hbd
    · exact Or.inr ⟨e, he.1, heq⟩
  have hgproj (t : unitInterval) : radialCylinderProjection (g t).1 = initialCuffGapCurve 1 0 t := by
    rw [hgcoord]
    apply Subtype.ext
    apply Prod.ext
    · change max 1 (min 2 (1 : ℝ)) = 1
      norm_num
    · change Circle.exp (2 * (1 + (t : ℝ)) * π) =
        Circle.exp (2 * (((0 + 1 : ℕ) : ℝ) + (t : ℝ)) * π / (1 : ℕ))
      norm_num
  let r := ((fun p : D => planeToCylinderCover p.1) ⁻¹' cylinderCoverRegion 1 G 0) \ bd D
  obtain ⟨_, hcl⟩ := preimage_coverRegion_sdiff_boundary_mem_regions L hG hθ hD hBd hstrip F hFU
  have hemb := isClosedEmbedding_single_strip_coverMap hD hstrip
  have hQr : Q.U ⊆ closure r := by
    intro x hx
    obtain ⟨y, hy, hyx⟩ := hcl.symm ▸ hQR (mem_image_of_mem _ hx)
    exact hemb.injective hyx ▸ hy
  obtain ⟨a, haQ, hsa⟩ := exists_initial_edge_of_cut_path hQ.2.2
  have haF := hQ.1.2 haQ
  have hab : a ≠ b := fun h => hbQ (h ▸ haQ)
  have haNotBd : ¬ a ⊆ bd D := by
    intro haBd
    apply cut_boundary_edge_not_subset_region_closure L hG hθ hno hval hD hBd hstrip
      F hFU hFV hEdges' g hgcoord hgproj hb hbBd hgap haF haBd hab hsa
    exact fun x hx => hQr ((haQ.2.1 hx).1)
  obtain ⟨p, hp, hpBd⟩ := not_subset.mp haNotBd
  obtain ⟨B, hBF, hBV, hBU⟩ := exists_boundary_subdrawing_on_single_strip L hG hθ hD hBd hstrip F hFU hEdges
  have hvertices : Q.V ∩ B.V ⊆ {g 0, v} := by
    rw [hBV, cut_boundary_vertices_eq_preimage_path_vertices L hG hθ hD hBd hstrip F hFV]
    exact hcontact
  refine ⟨hQr, ?_⟩
  rw [← hBU]
  have hdis : Disjoint B.U (bd D)ᶜ := by rw [hBU]; exact disjoint_compl_right
  exact path_intersection_subset_ends_of_vertices hQ.1 hBF hQ.2.2 hvertices
    ⟨p, (haQ.2.1 hp).1, hpBd⟩ hdis

/-- If a path meets a set only at its ends, every open drawing edge
of that path misses the set. -/
theorem edge_disjoint_of_path_point_contact
    {S : Type*} [TopologicalSpace S] [T2Space S] {Q : Drawing S} {s t : S}
    (hQ : IsPathDrawing Q s t) {T : Set S} (hpoint : Q.U ∩ T ⊆ {s, t})
    {e : Set S} (he : e ∈ Q.E) : Disjoint e T := by
  apply disjoint_left.mpr
  intro p hp hpT
  have hpV : p ∉ Q.V := (he.2.1 hp).2
  rcases hpoint ⟨(he.2.1 hp).1, hpT⟩ with hps | hpt
  · exact hpV (hps.symm ▸ (isPathDrawing_end_vertices hQ).1)
  · exact hpV ((mem_singleton_iff.mp hpt).symm ▸ (isPathDrawing_end_vertices hQ).2)

end GraphMinor.GM06
