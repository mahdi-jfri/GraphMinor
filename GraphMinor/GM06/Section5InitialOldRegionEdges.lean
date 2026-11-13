module

public import GraphMinor.GM06.Defs
import GraphMinor.GM06.Section5InitialRegionEdges
import GraphMinor.GM06.Section5AdjoinBoundary
import GraphMinor.GM06.Section5GapEdge

/-!
# At most one original edge beside the initial region

For the boundary-contact argument in VI (5.1), page 129, adjoining
the cuffs adds an edge through the initial gap of Rᵢ. That edge is
incident with sᵢ and is absent from the original graph. The bound of
two incident edges in the enlarged drawing therefore leaves room
for at most one original edge at sᵢ incident with Rᵢ.
-/

public section
namespace GraphMinor.GM06
open Set Topology GraphMinor.Surface

/-- In the unreduced situation of VI (5.1), the designated region Rᵢ
has at most one incident original edge at sᵢ. -/
theorem ncard_initial_old_region_edges_le_one
    {k : ℕ} {G : Drawing ClosedCylinder} (L : CylinderLinkage k G)
    (hk : 1 < k) (hG : IsCylinderSection5Drawing k G)
    (hno : ¬ Section5AnyReductionApplies k G L) (i : Fin k) :
    {e ∈ G.E | cylinderM1Point k i ∈ closure e ∧ e ⊆ closure (cylinderRegion k G i)}.ncard ≤ 1 := by
  classical
  obtain ⟨F, hGF, hFU, hFV⟩ := exists_drawing_adjoining_boundary L hG
  obtain ⟨a, ha, _, haG, _, haR, hsa, _, _⟩ :=
    exists_added_initial_gap_edge hG hGF hFU hFV i
  let A := {e ∈ G.E | cylinderM1Point k i ∈ closure e ∧ e ⊆ closure (cylinderRegion k G i)}
  let B := {e ∈ F.E | cylinderM1Point k i ∈ closure e ∧ e ⊆ closure (cylinderRegion k G i)}
  have hAfin : A.Finite := G.finite_edges.subset (fun _ h => h.1)
  have hBfin : B.Finite := F.finite_edges.subset (fun _ h => h.1)
  have haA : a ∉ A := fun h => haG h.1
  have hsub : insert a A ⊆ B := by
    intro e he
    rcases he with rfl | he
    · exact ⟨ha, hsa, haR.trans subset_closure⟩
    · exact ⟨hGF.2 he.1, he.2⟩
  have hle : (insert a A).ncard ≤ 2 :=
    (ncard_le_ncard hsub hBfin).trans (ncard_initial_region_edges_le_two L hk hG hno hFU hFV i)
  rw [ncard_insert_of_notMem haA hAfin] at hle
  exact Nat.le_of_succ_le_succ hle

/-- Two original edges at sᵢ incident with Rᵢ are the same edge in
the unreduced situation of VI (5.1). -/
theorem eq_of_initial_old_region_edges
    {k : ℕ} {G : Drawing ClosedCylinder} (L : CylinderLinkage k G)
    (hk : 1 < k) (hG : IsCylinderSection5Drawing k G)
    (hno : ¬ Section5AnyReductionApplies k G L) (i : Fin k)
    {e f : Set ClosedCylinder} (he : e ∈ G.E) (hf : f ∈ G.E)
    (hse : cylinderM1Point k i ∈ closure e) (hsf : cylinderM1Point k i ∈ closure f)
    (heR : e ⊆ closure (cylinderRegion k G i))
    (hfR : f ⊆ closure (cylinderRegion k G i)) : e = f := by
  by_contra hne
  have hfin : {a ∈ G.E | cylinderM1Point k i ∈ closure a ∧
      a ⊆ closure (cylinderRegion k G i)}.Finite := G.finite_edges.subset (fun _ h => h.1)
  have hsub : ({e, f} : Set (Set ClosedCylinder)) ⊆
      {a ∈ G.E | cylinderM1Point k i ∈ closure a ∧ a ⊆ closure (cylinderRegion k G i)} := by
    rintro a (rfl | ha)
    · exact ⟨he, hse, heR⟩
    · have haf := mem_singleton_iff.mp ha
      subst a
      exact ⟨hf, hsf, hfR⟩
  have hle := (ncard_le_ncard hsub hfin).trans (ncard_initial_old_region_edges_le_one L hk hG hno i)
  rw [ncard_pair hne] at hle
  exact (by decide : ¬ (2 : ℕ) ≤ 1) hle

end GraphMinor.GM06
