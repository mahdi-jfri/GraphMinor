module

public import GraphMinor.GM06.Defs
import GraphMinor.GM06.Section4
import GraphMinor.GM06.Section5Components
import GraphMinor.GM06.Section3Induce

/-!
# Adding the cuffs connects the drawing

In the region argument of VI (5.1), page 129, Reduction 2 has already
removed every component missing the linkage. Each remaining component
meets the inner cuff at an initial vertex. Adding that cuff therefore
joins the components. A linkage path also meets the outer cuff, so
adding both cuffs still gives a connected set. This permits following
the boundary of the region from its initial cuff gap.
-/

public section

namespace GraphMinor.GM06

open Set Topology GraphMinor.Surface

private theorem connected_of_isOArc {C : Set ClosedCylinder} (hC : IsOArc C) :
    IsConnected C := by
  obtain ⟨e⟩ := hC
  exact isConnected_iff_connectedSpace.mpr (e.surjective.connectedSpace e.continuous)

/-- If no reduction applies, adjoining the inner cuff joins all
components of the drawing in the proof of VI (5.1). -/
theorem isConnected_union_innerCuff_of_no_section5_reduction
    {k : ℕ} {G : Drawing ClosedCylinder} (L : CylinderLinkage k G)
    (hG : IsCylinderSection5Drawing k G) (hno : ¬ Section5AnyReductionApplies k G L) :
    IsConnected (G.U ∪ cylinderCuff1) := by
  have hC : IsConnected cylinderCuff1 := connected_of_isOArc isOArc_cylinderCuff1
  obtain ⟨a, ha⟩ := hC.nonempty
  have hpre : IsPreconnected (cylinderCuff1 ∪ G.U) := by
    apply isPreconnected_of_forall a
    intro x hx
    rcases hx with hxC | hxG
    · exact ⟨cylinderCuff1, subset_union_left, ha, hxC, hC.isPreconnected⟩
    · rw [← biUnion_compPointSet_eq_U G] at hxG
      obtain ⟨K, hK, hxK⟩ := mem_iUnion₂.mp hxG
      obtain ⟨i, hi⟩ := component_contains_initial_of_no_section5_reduction L hG hno hK
      have hKU : compPointSet K ⊆ G.U := by
        rw [← biUnion_compPointSet_eq_U G]
        intro y hy
        exact mem_iUnion₂.mpr ⟨K, hK, hy⟩
      have hjoin : (cylinderCuff1 ∩ compPointSet K).Nonempty :=
        ⟨cylinderM1Point k i, rfl, Or.inl hi⟩
      have hconn := hC.union hjoin (isConnected_compPointSet G hK)
      exact ⟨cylinderCuff1 ∪ compPointSet K, union_subset_union_right _ hKU,
        Or.inl ha, Or.inr hxK, hconn.isPreconnected⟩
  rw [union_comm]
  exact ⟨⟨a, Or.inl ha⟩, hpre⟩

/-- Adjoining both cuffs gives a connected set in the unreduced
situation of VI (5.1), since a linkage path joins the two cuffs. -/
theorem isConnected_union_boundary_of_no_section5_reduction
    {k : ℕ} {G : Drawing ClosedCylinder} (L : CylinderLinkage k G)
    (hG : IsCylinderSection5Drawing k G) (hno : ¬ Section5AnyReductionApplies k G L) :
    IsConnected (G.U ∪ bd ClosedCylinder) := by
  let i : Fin k := ⟨0, hG.1⟩
  have htU : L.curve i 1 ∈ G.U := (L.isSubdrawing i).2 (by
    rw [← (L.curve_parametrizes i).2.1]
    exact mem_range_self 1)
  have htC : L.curve i 1 ∈ cylinderCuff2 := by
    obtain ⟨j, hj⟩ := L.curve_one_mem i
    rw [← hj]
    rfl
  rw [bd_closedCylinder, ← union_assoc]
  exact (isConnected_union_innerCuff_of_no_section5_reduction L hG hno).union
    ⟨L.curve i 1, Or.inl htU, htC⟩ (connected_of_isOArc isOArc_cylinderCuff2)

end GraphMinor.GM06
