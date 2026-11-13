module

public import GraphMinor.GM06.Section5CutStripSurface
import GraphMinor.GM06.Section5CutGraph
import GraphMinor.GM06.Section5RegionInterior
import GraphMinor.GM06.Section4PathTools
import GraphMinor.GM06.Section4SubgraphDrawing
import GraphMinor.GM06.Section5ValencyOneCase
import GraphMinor.GM07.Section46PullGraph

/-!
# The finite graph off the seam in the cut cylinder

Remove the linkage-path edges while keeping every vertex. The seam
is then normal to this drawing. The proved pullback construction for
a normal graph across a surface cut gives a proper finite drawing on
the lifted strip disc. Each lifted edge is the full preimage of an
original edge off the seam. This supplies actual graph data for the
one-path region argument of VI Section 5.
-/

public section
namespace GraphMinor.GM06
open Set GraphMinor.Surface

private theorem path_has_no_isolated_vertices
    {P : Drawing ClosedCylinder} {s t : ClosedCylinder} (hP : IsPathDrawing P s t) :
    GM07.HasNoIsolatedVertices P := by
  intro x hx
  have go {Q : Drawing ClosedCylinder} {y : ClosedCylinder}
      (hQP : Q.IsSubdrawing P) (hQ : IsPathDrawing Q x y) :
      ∃ e ∈ P.E, P.VertexIncident x e := by
    obtain ⟨e, he, w, _, hlQ⟩ := exists_nonloop_first_link hQ
    have hlP := (hQP.isLink_iff he).mp hlQ
    refine ⟨e, hlP.1, hx, Or.inl hlP.1, ?_⟩
    exact (show x ∈ closure e ∩ P.V from hlP.2.2.2.symm ▸ mem_insert x {w}).1
  by_cases hxs : x = s
  · subst x
    exact go ⟨Subset.rfl, Subset.rfl⟩ hP
  · obtain ⟨Q, hQ⟩ := exists_subpath_of_isPathDrawing hP hx (isPathDrawing_end_vertices hP).1 hxs
    exact go hQ.1 hQ.2.2

/-- The graph off the sole linkage seam pulls back to a proper finite
drawing on the cut strip disc, with exactly the lifted original vertices.
The original graph is the union of that off-seam drawing and the seam. -/
theorem exists_off_seam_drawing_on_single_strip
    {G : Drawing ClosedCylinder} {θ : ℝ} (L : CylinderLinkage 1 G)
    (hG : IsCylinderSection5Drawing 1 G) (hθ : L.HasTheta θ)
    {D : Set (ℝ × ℝ)} (hD : IsClosedDisc D)
    (hBd : discBd D = liftedStripBoundary hG.1 L 1)
    (hstrip : D ⊆ {p : ℝ × ℝ | 1 ≤ p.1 ∧ p.1 ≤ 2}) :
    ∃ (H : Drawing ClosedCylinder) (HC : Drawing D),
      H.IsSubdrawing G ∧ H.V = G.V ∧ H.E = G.E \ (L.pathDrawing 0).E ∧
      G.U = H.U ∪ (L.pathDrawing 0).U ∧ HC.IsProper ∧
      HC.U = (fun p : D => radialCylinderProjection p.1) ⁻¹' H.U ∧
      HC.V = (fun p : D => radialCylinderProjection p.1) ⁻¹' G.V ∧
      ∀ ec ∈ HC.E, ∃ e ∈ G.E \ (L.pathDrawing 0).E,
        ec = (fun p : D => radialCylinderProjection p.1) ⁻¹' e := by
  obtain ⟨H, hHG, hV, hE, hU, hN⟩ :=
    exists_drawing_without_subdrawing_edges G (L.pathDrawing 0) (L.isSubdrawing 0).1
  have hCut := isCutAlongSet_single_strip_projection L hG hθ hD hBd hstrip
  have hPproper := isProper_of_isSubdrawing hG.2.1 (L.isSubdrawing 0).1
  have hPN := path_has_no_isolated_vertices (L.isPath 0)
  have hJ := hCut.isCutAlongGraph hPproper hPN
  have hHproper := isProper_of_isSubdrawing hG.2.1 hHG
  obtain ⟨HC, hPull, hHCproper, hEdges⟩ :=
    GM07.exists_pullback_graph isSurface_closedCylinder hJ hHproper hN
  refine ⟨H, HC, hHG, hV, hE, hU, hHCproper, hPull.1, ?_, ?_⟩
  · rw [hPull.2, hV]
  · intro ec hec
    obtain ⟨e, he, heq⟩ := hEdges ec hec
    exact ⟨e, hE ▸ he, heq⟩

end GraphMinor.GM06
