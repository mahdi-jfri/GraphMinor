module

public import GraphMinor.GM06.Section5CutInitialGap
import GraphMinor.GM06.Section5GapEdge
import GraphMinor.GM06.Section5RegionPoint
import GraphMinor.GM11.Walks

/-!
# The added initial edge of the cut drawing

The lifted initial gap misses every lifted original vertex. Its open
part is connected and therefore stays in one drawing edge. That edge
is an added boundary edge, since an original edge could not contain
a point of the open cuff gap. Both initial copies lie in its closure.
This supplies the edge avoided by the cut-disc region walk for VI (5.1).
-/

public section
namespace GraphMinor.GM06
open Set Topology GraphMinor.Surface

/-- The open initial gap of the cut disc lies in a single added boundary
edge. Its whole closed arc lies in the closure of that edge. -/
theorem exists_boundary_edge_containing_cut_initial_gap
    {G : Drawing ClosedCylinder} (hG : IsCylinderSection5Drawing 1 G)
    {D : Set (ℝ × ℝ)} (F : Drawing D)
    (hFV : F.V = (fun p : D => radialCylinderProjection p.1) ⁻¹' G.V)
    (hbd : bd D ⊆ F.U)
    (hEdges : ∀ ec ∈ F.E, ec ⊆ bd D ∨
      ∃ e ∈ G.E, ec = (fun p : D => radialCylinderProjection p.1) ⁻¹' e)
    (g : Curve D) (hgbd : range g ⊆ bd D)
    (hgproj : ∀ t, radialCylinderProjection (g t).1 = initialCuffGapCurve 1 0 t) :
    ∃ e ∈ F.E, e ⊆ bd D ∧ g '' Ioo 0 1 ⊆ e ∧ range g ⊆ closure e := by
  have hoff {t : unitInterval} (ht : t ∈ Ioo 0 1) :
      radialCylinderProjection (g t).1 ∉ G.U := by
    rw [hgproj]
    exact (connectedComponentIn_subset _ _
      ((initialCuffGapCurve_props hG 0).2.2.2.2 ⟨t, ht, rfl⟩)).2
  have hgap : g '' Ioo 0 1 ⊆ F.U \ F.V := by
    rintro x ⟨t, ht, rfl⟩
    refine ⟨hbd (hgbd (mem_range_self t)), ?_⟩
    rw [hFV]
    exact fun h => hoff ht (G.V_subset_U h)
  let t : unitInterval := ⟨1 / 2, by constructor <;> norm_num⟩
  have ht : t ∈ Ioo (0 : unitInterval) 1 := by
    constructor
    · change (0 : ℝ) < 1 / 2
      norm_num
    · change (1 / 2 : ℝ) < 1
      norm_num
  obtain ⟨e, he, hge⟩ := F.exists_edge_of_mem (hgap ⟨t, ht, rfl⟩).1
    (hgap ⟨t, ht, rfl⟩).2
  have heBd : e ⊆ bd D := by
    rcases hEdges e he with hb | ⟨e', he', heq⟩
    · exact hb
    · rw [heq] at hge
      exact False.elim (hoff ht ((he'.2.1 hge).1))
  obtain ⟨hge', hcl⟩ := arc_interior_subset_edge he hgap ⟨g t, hge, t, ht, rfl⟩
  exact ⟨e, he, heBd, hge', hcl⟩

end GraphMinor.GM06
