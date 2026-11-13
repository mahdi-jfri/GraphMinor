module

public import GraphMinor.GM06.Section5CutBoundaryEdgeExclusion
import GraphMinor.GM06.Section5FirstCurveEdge
import GraphMinor.GM06.Section5DiscEdgeIncidence
import GraphMinor.GM06.Section5CutLinks
import GraphMinor.GM06.Section5CutEdgePreimage
import GraphMinor.GM06.Section4PathTools

/-!
# An initial boundary arc cannot remain incident with the chosen region

Take the first edge along the boundary arc up to its first new
vertex. Its new vertex has radius different from one, so this edge
is different from the added initial gap edge, whose ends are the
two initial copies. If the whole arc were incident with the chosen
region, one point would make this whole first edge incident. The
proved initial boundary-edge exclusion contradicts that. This is
the old-prefix obstruction needed for corrected Reduction 4 in the
one-path proof of VI (5.1), page 129.
-/

public section
namespace GraphMinor.GM06
open Set Topology Real GraphMinor.Surface

/-- A nontrivial initial boundary arc leaving the initial cuff cannot
lie wholly in the chosen cut region closure at larger initial valency,
when Reductions 1 and 2 are unavailable. -/
theorem cut_initial_boundary_arc_not_subset_region_closure_of_no_reductions12
    {G : Drawing ClosedCylinder} {θ : ℝ} (L : CylinderLinkage 1 G)
    (hG : IsCylinderSection5Drawing 1 G) (hθ : L.HasTheta θ)
    (hno1 : ∀ (H : Drawing ClosedCylinder) (M : CylinderLinkage 1 H),
      IsCylinderSection5Drawing 1 H → ¬ Section5Reduction1Step 1 G L H M)
    (hno2 : ∀ (H : Drawing ClosedCylinder) (M : CylinderLinkage 1 H),
      IsCylinderSection5Drawing 1 H → ¬ Section5Reduction2Step 1 G L H M)
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
    (hginj : Function.Injective g)
    (hgproj : ∀ t, radialCylinderProjection (g t).1 = initialCuffGapCurve 1 0 t)
    {b : Set D} (hb : b ∈ F.E) (hbBd : b ⊆ bd D) (hgap : g '' Ioo 0 1 ⊆ b)
    (f : Curve D) (hf : Function.Injective f) (hf0 : f 0 = g 0)
    (hfBd : range f ⊆ bd D) (hf1 : f 1 ∈ F.V)
    (haway : ∀ t, 0 < t → (f t).1.1 ≠ 1) :
    ¬ range f ⊆ closure (((fun p : D => planeToCylinderCover p.1) ⁻¹' cylinderCoverRegion 1 G 0) \ bd D) := by
  intro hfR
  let r := ((fun p : D => planeToCylinderCover p.1) ⁻¹' cylinderCoverRegion 1 G 0) \ bd D
  obtain ⟨hr, _⟩ := preimage_coverRegion_sdiff_boundary_mem_regions L hG hθ hD hBd hstrip F hFU
  have hbdF : bd D ⊆ F.U := by rw [hFU]; exact subset_union_right
  have hEdges' : ∀ ec ∈ F.E, ec ⊆ bd D ∨
      ∃ e ∈ G.E, ec = (fun p : D => radialCylinderProjection p.1) ⁻¹' e := by
    intro ec hec
    rcases hEdges ec hec with hbd | ⟨e, he, heq⟩
    · exact Or.inl hbd
    · exact Or.inr ⟨e, he.1, heq⟩
  have hsG : cylinderM1Point 1 0 ∈ G.V :=
    (L.isSubdrawing 0).1.1 (isPathDrawing_end_vertices (L.isPath 0)).1
  have hg0V : g 0 ∈ F.V := by
    rw [hFV]
    change radialCylinderProjection (g 0).1 ∈ G.V
    rw [hgproj, (initialCuffGapCurve_props hG 0).1]
    exact hsG
  have hg1V : g 1 ∈ F.V := by
    rw [hFV]
    change radialCylinderProjection (g 1).1 ∈ G.V
    rw [hgproj, (initialCuffGapCurve_props hG 0).2.1]
    have hi : finSuccCycle (0 : Fin 1) = 0 := Subsingleton.elim _ _
    rw [hi]
    exact hsG
  obtain ⟨_, hgb⟩ := cut_gap_edge_incidence L hG hθ hD hBd hstrip F hFU g hgcoord hb hgap
  have hbLink := isLink_of_distinct_vertices_in_closure hb hg0V hg1V
    (fun h => zero_ne_one (hginj h)) (hgb (mem_range_self 0)) (hgb (mem_range_self 1))
  obtain ⟨τ, hτ, hτV, a, ha, hfa0, hfaτ, hmeet⟩ :=
    exists_first_edge_of_injective_curve F f hf (hfBd.trans hbdF) hf1
  have haBd : a ⊆ bd D := by
    rcases hEdges a ha with hbd | ⟨e, he, heq⟩
    · exact hbd
    · obtain ⟨p, hpa, hpf⟩ := hmeet
      rw [heq] at hpa
      exact False.elim (disjoint_left.mp
        (preimage_non_seam_edge_disjoint_boundary L hG hθ hD hBd hstrip he.1 he.2) hpa (hfBd hpf))
  have hab : a ≠ b := by
    intro hab
    have hw : f τ ∈ ({g 0, g 1} : Set D) := by
      rw [← hbLink.2.2.2]
      exact ⟨hab ▸ hfaτ, hτV⟩
    rcases hw with hw0 | hw1
    · apply haway τ hτ
      rw [hw0, hgcoord]
    · apply haway τ hτ
      rw [mem_singleton_iff.mp hw1, hgcoord]
  have haR : a ⊆ closure r := by
    obtain ⟨p, hpa, hpf⟩ := hmeet
    exact edge_subset_closure_of_incident_disc_region (show IsClosedDiscSpace D from hD) hbdF hr ha
      ⟨p, hpa, hfR hpf⟩
  have hsa : g 0 ∈ closure a := hf0 ▸ hfa0
  exact cut_boundary_edge_not_subset_region_closure_of_no_reductions12 L hG hθ hno1 hno2 hval hD hBd hstrip
    F hFU hFV hEdges' g hgcoord hgproj hb hbBd hgap ha haBd hab hsa haR


/-- A nontrivial initial boundary arc leaving the initial cuff cannot
lie wholly in the chosen cut region closure at larger initial valency. -/
theorem cut_initial_boundary_arc_not_subset_region_closure
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
    (hginj : Function.Injective g)
    (hgproj : ∀ t, radialCylinderProjection (g t).1 = initialCuffGapCurve 1 0 t)
    {b : Set D} (hb : b ∈ F.E) (hbBd : b ⊆ bd D) (hgap : g '' Ioo 0 1 ⊆ b)
    (f : Curve D) (hf : Function.Injective f) (hf0 : f 0 = g 0)
    (hfBd : range f ⊆ bd D) (hf1 : f 1 ∈ F.V)
    (haway : ∀ t, 0 < t → (f t).1.1 ≠ 1) :
    ¬ range f ⊆ closure (((fun p : D => planeToCylinderCover p.1) ⁻¹' cylinderCoverRegion 1 G 0) \ bd D) := by
  exact cut_initial_boundary_arc_not_subset_region_closure_of_no_reductions12 L hG hθ
    (fun H M hH h1 => hno ⟨H, M, hH, Or.inl h1⟩)
    (fun H M hH h2 => hno ⟨H, M, hH, Or.inr (Or.inl h2)⟩)
    hval hD hBd hstrip F hFU hFV hEdges g hgcoord hginj hgproj hb hbBd hgap f hf hf0 hfBd hf1 haway

end GraphMinor.GM06
