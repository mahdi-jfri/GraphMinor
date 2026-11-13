module

public import GraphMinor.GM06.Section5CutInitialPath
import GraphMinor.GM06.Section5FirstHit
import GraphMinor.GM06.Section4PathTools

/-!
# First seam vertex of the cut-disc region path

Construct the boundary path between the two initial copies and stop
at its first new vertex above the sole linkage path. Its only seam
vertices are its start and terminal vertex. Taking this prefix keeps
both its incidence with the specified cover region and its exclusion
of the added initial gap edge. This supplies the vertex-contact part
of the one-path boundary argument in VI (5.1), page 129.
-/

public section
namespace GraphMinor.GM06
open Set Topology Real GraphMinor.Surface

/-- The cut-disc region path has a prefix ending at its first new seam
vertex, still avoiding the initial gap edge. -/
theorem exists_single_strip_first_contact_path
    {G : Drawing ClosedCylinder} {θ : ℝ} (L : CylinderLinkage 1 G)
    (hG : IsCylinderSection5Drawing 1 G) (hθ : L.HasTheta θ)
    (hno : ¬ Section5AnyReductionApplies 1 G L)
    {D : Set (ℝ × ℝ)} (hD : IsClosedDisc D)
    (hBd : discBd D = liftedStripBoundary hG.1 L 1)
    (hstrip : D ⊆ {p : ℝ × ℝ | 1 ≤ p.1 ∧ p.1 ≤ 2})
    (F : Drawing D)
    (hFU : F.U = (fun p : D => radialCylinderProjection p.1) ⁻¹' G.U ∪ bd D)
    (hFV : F.V = (fun p : D => radialCylinderProjection p.1) ⁻¹' G.V)
    (hEdges : ∀ ec ∈ F.E, ec ⊆ bd D ∨
      ∃ e ∈ G.E, ec = (fun p : D => radialCylinderProjection p.1) ⁻¹' e) :
    ∃ (g : Curve D) (v : D) (Q : Drawing D) (e : Set D),
      (∀ t, (g t).1 = (1, 2 * (1 + (t : ℝ)) * π)) ∧
      radialCylinderProjection v.1 ∈ (L.pathDrawing 0).V ∧ v ≠ g 0 ∧
      IsSubpathOf F Q (g 0) v ∧
      (fun p : D => planeToCylinderCover p.1) '' Q.U ⊆ closure (cylinderCoverRegion 1 G 0) ∧
      Q.V ∩ (fun p : D => radialCylinderProjection p.1) ⁻¹' (L.pathDrawing 0).V ⊆ {g 0, v} ∧
      e ∈ F.E ∧ e ⊆ bd D ∧ g '' Ioo 0 1 ⊆ e ∧ e ∉ Q.E := by
  classical
  obtain ⟨g, hgcoord, hginj, hgbd, hgproj⟩ := exists_single_strip_initial_gap_curve L hG hBd
  obtain ⟨A, e, hA, hAcl, he, heBd, hgap, heA⟩ :=
    exists_initial_copies_subpath_on_single_strip L hG hθ hno hD hBd hstrip F hFU hFV hEdges
      g hgcoord hginj hgbd hgproj
  let B := ((fun p : D => radialCylinderProjection p.1) ⁻¹' (L.pathDrawing 0).V) \ {g 0}
  have hsB : g 0 ∉ B := fun h => h.2 rfl
  have htB : g 1 ∈ B := by
    refine ⟨?_, fun h => zero_ne_one (hginj h.symm)⟩
    change radialCylinderProjection (g 1).1 ∈ (L.pathDrawing 0).V
    rw [hgproj, (initialCuffGapCurve_props hG 0).2.1]
    have hi : finSuccCycle (0 : Fin 1) = 0 := Subsingleton.elim _ _
    rw [hi]
    exact (isPathDrawing_end_vertices (L.isPath 0)).1
  obtain ⟨v, hvB, Q, hQA, hQV⟩ := exists_subpath_to_vertex_set hA.2.2 hsB htB
  have hQF := hQA.1.trans hA.1
  refine ⟨g, v, Q, e, hgcoord, hvB.1, hvB.2,
    ⟨hQF, hQF.U_subset, hQA.2.2⟩,
    (image_mono hQA.2.1).trans hAcl, ?_, he, heBd, hgap, ?_⟩
  · rintro x ⟨hxQ, hxP⟩
    by_cases hxs : x = g 0
    · exact Or.inl hxs
    · exact Or.inr (hQV ⟨hxQ, hxP, hxs⟩)
  · exact fun heQ => heA (hQA.1.2 heQ)

end GraphMinor.GM06
