module

public import GraphMinor.GM06.Defs
import GraphMinor.GM06.Section5PuncturedLinkage
import GraphMinor.GM06.Section5DeletedStartComponents
import GraphMinor.GM06.Section5InitialLoop
import GraphMinor.GM06.Section3Induce
import GraphMinor.GM06.Section4PathTools
import GraphMinor.GM11.Walks

/-!
# The drawing and cuffs after deleting an initial vertex

For VI (5.1), page 129, the linkage and cuffs form a connected core
after one initial vertex is deleted. Reduction 2 excludes components
attached only at that vertex. Every other component, and each edge
incident with the deleted vertex, joins the core.
-/

public section

namespace GraphMinor.GM06

open Set Topology GraphMinor.Surface

/-- In the unreduced situation of VI (5.1), with at least two linkage
paths, removing an initial vertex from the drawing and cuffs leaves
a connected set. -/
theorem isConnected_punctured_drawing_and_cuffs_of_no_reduction2
    {k : ℕ} {G : Drawing ClosedCylinder} (L : CylinderLinkage k G)
    (hk : 1 < k) (hG : IsCylinderSection5Drawing k G)
    (hno : ∀ (G₁ : Drawing ClosedCylinder) (L₁ : CylinderLinkage k G₁),
      IsCylinderSection5Drawing k G₁ → ¬ Section5Reduction2Step k G L G₁ L₁) (i : Fin k) :
    IsConnected ((bd ClosedCylinder ∪ G.U) \ {cylinderM1Point k i}) := by
  classical
  let s := cylinderM1Point k i
  let X := (bd ClosedCylinder ∪ G.U) \ {s}
  let C := (bd ClosedCylinder ∪ ⋃ j, (L.pathDrawing j).U) \ {s}
  have hC : IsConnected C := isConnected_punctured_linkage_and_cuffs L hk i
  have hCX : C ⊆ X := by
    rintro x ⟨hx | hx, hn⟩
    · exact ⟨Or.inl hx, hn⟩
    · obtain ⟨j, hj⟩ := mem_iUnion.mp hx
      exact ⟨Or.inr ((L.isSubdrawing j).2 hj), hn⟩
  obtain ⟨a, ha⟩ := hC.nonempty
  have hsV : s ∈ G.V := (L.isSubdrawing i).1.1 (isPathDrawing_end_vertices (L.isPath i)).1
  let H := induceDrawing G (G.V \ {s})
  have hHV : H.V = G.V \ {s} := induceDrawing_V G sdiff_subset
  have hHG : H.IsSubdrawing G := induceDrawing_isSubdrawing G sdiff_subset
  have hHX : H.U ⊆ X := by
    rw [show H.U = (G.V \ {s}) ∪ ⋃ e ∈ H.E, e from induceDrawing_U G sdiff_subset]
    rintro x (hx | hx)
    · exact ⟨Or.inr (G.V_subset_U hx.1), hx.2⟩
    · obtain ⟨e, he, hx⟩ := mem_iUnion₂.mp hx
      have hh := (hHG.2 he).2.1 hx
      exact ⟨Or.inr hh.1, fun heq => hh.2 (mem_singleton_iff.mp heq ▸ hsV)⟩
  have hvertex (b : ClosedCylinder) (hb : b ∈ G.V \ {s}) :
      ∃ Y ⊆ X, a ∈ Y ∧ b ∈ Y ∧ IsConnected Y := by
    have hbH : b ∈ H.V := hHV.symm ▸ hb
    let K := compOf H.toGraph b
    have hK : IsGraphComponent K H.toGraph := isGraphComponent_compOf hbH
    have hKi : IsGraphComponent K (G.toGraph.induce (G.V \ {s})) := by
      rw [← induceDrawing_toGraph_eq_induce G sdiff_subset]
      exact hK
    obtain ⟨j, z, hzK, hzP⟩ := deleted_start_component_meets_linkage_of_no_reduction2 L hG hno i hKi
    have hKX : compPointSet K ⊆ X := by
      apply subset_trans ?_ hHX
      rw [← biUnion_compPointSet_eq_U H]
      exact fun y hy => mem_iUnion₂.mpr ⟨K, hK, hy⟩
    have hzC : z ∈ C :=
      ⟨Or.inr (mem_iUnion.mpr ⟨j, (L.pathDrawing j).V_subset_U hzP⟩),
        (show z ∈ G.V \ {s} from hKi.1.vertexSet_mono hzK).2⟩
    exact ⟨C ∪ compPointSet K, union_subset hCX hKX, Or.inl ha,
      Or.inr (Or.inl (self_mem_reachSet hbH)),
      hC.union ⟨z, hzC, Or.inl hzK⟩ (isConnected_compPointSet H hK)⟩
  refine ⟨⟨a, hCX ha⟩, ?_⟩
  apply isPreconnected_of_forall a
  intro x hx
  by_cases hxC : x ∈ C
  · exact ⟨C, hCX, ha, hxC, hC.isPreconnected⟩
  have hxG : x ∈ G.U := hx.1.resolve_left (fun hb => hxC ⟨Or.inl hb, hx.2⟩)
  by_cases hxV : x ∈ G.V
  · obtain ⟨Y, hY, haY, hxY, hcY⟩ := hvertex x ⟨hxV, hx.2⟩
    exact ⟨Y, hY, haY, hxY, hcY.isPreconnected⟩
  have hxEdges : x ∈ ⋃ e ∈ G.E, closure e := by
    rw [G.U_eq] at hxG
    exact hxG.resolve_left hxV
  obtain ⟨e, he, hxe⟩ := mem_iUnion₂.mp hxEdges
  obtain ⟨u, v, hl⟩ := G.toGraph.exists_isLink_of_mem_edgeSet he
  have hex : ∃ b, b ∈ G.V \ {s} ∧ b ∈ closure e := by
    by_cases hv : v = s
    · have hu : u ≠ s := by
        intro hu
        exact not_isLoop_at_initial_of_no_reduction2 L hG hno i e
          (by simpa only [hu, hv] using hl)
      refine ⟨u, ⟨hl.left_mem, hu⟩, ?_⟩
      have hh : u ∈ closure e ∩ G.V := hl.2.2.2 ▸ mem_insert u {v}
      exact hh.1
    · refine ⟨v, ⟨hl.right_mem, hv⟩, ?_⟩
      have hh : v ∈ closure e ∩ G.V := hl.2.2.2 ▸ mem_insert_of_mem u rfl
      exact hh.1
  obtain ⟨b, hb, hbcl⟩ := hex
  obtain ⟨Y, hY, haY, hbY, hcY⟩ := hvertex b hb
  have heC : IsConnected (closure e \ {s}) := by
    refine ⟨⟨b, hbcl, hb.2⟩, he.2.2.1.isConnected.isPreconnected.subset_closure ?_ sdiff_subset⟩
    intro y hy
    exact ⟨subset_closure hy, fun heq => (he.2.1 hy).2 (mem_singleton_iff.mp heq ▸ hsV)⟩
  have heX : closure e \ {s} ⊆ X := by
    rintro y ⟨hy, hn⟩
    exact ⟨Or.inr (G.isClosed_U.closure_subset_iff.mpr
      (he.2.1.trans sdiff_subset) hy), hn⟩
  have hjoin : IsConnected (Y ∪ (closure e \ {s})) :=
    hcY.union ⟨b, hbY, hbcl, hb.2⟩ heC
  exact ⟨Y ∪ (closure e \ {s}), union_subset hY heX, Or.inl haY,
    Or.inr ⟨hxe, hx.2⟩, hjoin.isPreconnected⟩

/-- The absence of all Section 5 reductions implies the corresponding
conclusion obtained by excluding Reduction 2 alone. -/
theorem isConnected_punctured_drawing_and_cuffs
    {k : ℕ} {G : Drawing ClosedCylinder} (L : CylinderLinkage k G)
    (hk : 1 < k) (hG : IsCylinderSection5Drawing k G)
    (hno : ¬ Section5AnyReductionApplies k G L) (i : Fin k) :
    IsConnected ((bd ClosedCylinder ∪ G.U) \ {cylinderM1Point k i}) := by
  exact isConnected_punctured_drawing_and_cuffs_of_no_reduction2 L hk hG
    (fun G₁ L₁ hG₁ hRed => hno ⟨G₁, L₁, hG₁, Or.inr (Or.inl hRed)⟩) i

end GraphMinor.GM06
