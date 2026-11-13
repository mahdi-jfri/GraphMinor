module

public import GraphMinor.GM06.Defs
import GraphMinor.GM06.Section5SinglePathDiscardedEnclosures
import GraphMinor.GM06.Section5MixedDiscAvoidance
import GraphMinor.GM06.Section5SeparationClockwiseReduction
import GraphMinor.GM06.Section5SeparationHelices
import GraphMinor.GM06.Section4PathTools
import GraphMinor.GM11.Walks

/-!
# Reduction 2 for one linkage path

For VI (5.5), page 130, first delete clockwise discarded edges
using the proved Reduction 1 pullbacks. The remaining discarded
side has genuine attached cylinder-disc enclosures constructed in
the cut disc. Their finite helix detours avoid the discarded side
except at its initial attachment, with no increase in potential.
The helix is then normal in the old drawing with unchanged vertex
count. Finally apply the stored clockwise-deletion pullbacks.
-/

public section
namespace GraphMinor.GM06
open Set GraphMinor.Surface

/-- The one-path Reduction 2 case of VI (5.5) after clockwise
discarded-edge exhaustion, using the actual cut-disc enclosures. -/
theorem theorem_5_5_red2_of_one_no_clockwise_edges
    {G G₁ G₂ : Drawing ClosedCylinder} (L : CylinderLinkage 1 G)
    (hG : IsCylinderSection5Drawing 1 G) (hG₁ : IsCylinderSection5Drawing 1 G₁)
    (hLP : (L.pathDrawing 0).IsSubdrawing G₁)
    (hsep : IsGraphSeparation G.toGraph G₁.toGraph G₂.toGraph)
    (hover : G₁.V ∩ G₂.V ⊆ {cylinderM1Point 1 0})
    (hno : ∀ e ∈ G₂.E, ¬ IsClockwiseInitialEdge L 0 e)
    (f : Curve ClosedCylinder) (hf : IsHelix 1 G₁ f) :
    ∃ g : Curve ClosedCylinder, IsHelix 1 G g ∧ curvePhi 1 G g ≤ curvePhi 1 G₁ f := by
  have h₁ : G₁.IsSubdrawing G := ⟨hsep.1.vertexSet_mono, hsep.1.edgeSet_mono⟩
  have h₂ : G₂.IsSubdrawing G := ⟨hsep.2.1.vertexSet_mono, hsep.2.1.edgeSet_mono⟩
  have hs₁ : cylinderM1Point 1 0 ∈ G₁.V := hLP.1 (isPathDrawing_end_vertices (L.isPath 0)).1
  obtain ⟨F, hF, hdisc, hcover⟩ := exists_single_path_discarded_enclosures_of_no_clockwise_edges
    L hG hG₁ hLP hsep hover hno
  have hbd : ∀ D ∈ F, discBd D ∩ (G₁.U ∪ (G₂.U \ {cylinderM1Point 1 0})) ⊆
      {cylinderM1Point 1 0} := by
    intro D hD x hx
    apply (hdisc D hD).2
    refine ⟨hx.1, ?_⟩
    rcases hx.2 with hx₁ | hx₂
    · exact h₁.U_subset hx₁
    · exact h₂.U_subset hx₂.1
  obtain ⟨g, hg, hga, hφ⟩ := exists_helix_avoiding_finitely_enclosed_set_with_attachment
    hs₁ hF (G₂.U \ {cylinderM1Point 1 0}) (fun h => h.2 rfl)
    (fun D hD => (hdisc D hD).1) hbd hcover f hf
  have havoid : range g ∩ G₂.U ⊆ {cylinderM1Point 1 0} := by
    intro x hx
    by_contra hxs
    exact disjoint_left.mp hga hx.1 ⟨hx.2, hxs⟩
  obtain ⟨hgOld, heq⟩ := helix_of_separation_avoids_discarded_side hsep hs₁ g hg havoid
  exact ⟨g, hgOld, heq.le.trans hφ⟩

/-- The complete one-path Reduction 2 case of VI (5.5), including
the clockwise deletions needed before cutting the cylinder. -/
theorem theorem_5_5_red2_of_one
    {G G₁ G₂ : Drawing ClosedCylinder}
    (L : CylinderLinkage 1 G) (L₁ : CylinderLinkage 1 G₁)
    (hG : IsCylinderSection5Drawing 1 G) (hG₁ : IsCylinderSection5Drawing 1 G₁)
    (hsep : IsGraphSeparation G.toGraph G₁.toGraph G₂.toGraph)
    (hover : G₁.V ∩ G₂.V ⊆ {cylinderM1Point 1 0})
    (hPaths : L₁.pathDrawing = L.pathDrawing)
    (f : Curve ClosedCylinder) (hf : IsHelix 1 G₁ f) :
    ∃ g : Curve ClosedCylinder, IsHelix 1 G g ∧ curvePhi 1 G g ≤ curvePhi 1 G₁ f := by
  obtain ⟨H, M, T, hH, hsepH, hoverH, hno, hMP, _, hback⟩ :=
    exists_clockwise_reduced_separation_with_linkage_eq L hG 0 hsep hover
  have hLP : (M.pathDrawing 0).IsSubdrawing G₁ := by
    rw [hMP, ← hPaths]
    exact (L₁.isSubdrawing 0).1
  obtain ⟨g, hg, hφ⟩ := theorem_5_5_red2_of_one_no_clockwise_edges M hH hG₁ hLP hsepH hoverH hno f hf
  obtain ⟨u, hu, hφu⟩ := hback g hg
  exact ⟨u, hu, hφu.trans hφ⟩

end GraphMinor.GM06
