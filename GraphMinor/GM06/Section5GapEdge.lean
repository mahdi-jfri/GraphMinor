module

public import GraphMinor.GM06.Defs
import GraphMinor.GM06.Section4
import GraphMinor.GM11.Walks
import GraphMinor.GM06.Section5AdjoinedEdges
public import GraphMinor.GM06.Section5BoundaryGap
import GraphMinor.GM06.Section5RegionPoint
import Mathlib.Analysis.Convex.PathConnected

/-!
# The added edge across an initial cuff gap

For VI (5.1), page 129, the dual point defining Rᵢ lies in a unique
added cuff edge. The open cuff interval from sᵢ to sᵢ₊₁ is contained
in that edge, since it is path connected and misses every vertex.
Thus both initial vertices are ends of its closure. The edge is
contained in Rᵢ and can be excluded from its boundary walk.
-/

public section

namespace GraphMinor.GM06

open Set Topology GraphMinor.Surface

universe u

private theorem isPathConnected_unitInterval_Ioo :
    IsPathConnected (Ioo (0 : unitInterval) 1) := by
  have heq : ((↑) : unitInterval → ℝ) '' Ioo (0 : unitInterval) 1 = Ioo (0 : ℝ) 1 := by
    ext x
    constructor
    · rintro ⟨t, ht, rfl⟩
      exact ht
    · intro hx
      exact ⟨⟨x, hx.1.le, hx.2.le⟩, hx, rfl⟩
  apply IsInducing.subtypeVal.isPathConnected_iff.mpr
  rw [heq]
  exact Convex.isPathConnected (convex_Ioo (𝕜 := ℝ) 0 1) ⟨1 / 2, by norm_num⟩

/-- The open part of a continuous arc that avoids the drawing's
vertices stays in one edge as soon as it meets that edge. Both ends
then lie in the edge closure. -/
theorem arc_interior_subset_edge
    {S : Type u} [TopologicalSpace S] {F : Drawing S} {e : Set S} (he : e ∈ F.E)
    {f : Curve S} (hf : f '' Ioo 0 1 ⊆ F.U \ F.V)
    (hmeet : (e ∩ f '' Ioo 0 1).Nonempty) :
    f '' Ioo 0 1 ⊆ e ∧ range f ⊆ closure e := by
  have hpc := isPathConnected_unitInterval_Ioo.image f.continuous
  have heq := he.2.2.2 (e ∪ f '' Ioo 0 1) (union_subset he.2.1 hf)
    (he.2.2.1.union hpc hmeet) subset_union_left
  have hfE : f '' Ioo 0 1 ⊆ e := fun _ hx => heq ▸ Or.inr hx
  have hcl : closure (Ioo (0 : unitInterval) 1) = univ := by
    rw [closure_Ioo (zero_ne_one : (0 : unitInterval) ≠ 1)]
    ext v
    exact iff_true_intro ⟨v.2.1, v.2.2⟩
  refine ⟨hfE, ?_⟩
  have hh := image_closure_subset_closure_image (s := Ioo (0 : unitInterval) 1) f.continuous
  rw [hcl, image_univ] at hh
  exact hh.trans (closure_mono hfE)

/-- The added cuff edge containing the dual point of Rᵢ lies in Rᵢ
and has both neighbouring initial vertices in its closure. -/
theorem exists_added_initial_gap_edge
    {k : ℕ} {G F : Drawing ClosedCylinder} (hG : IsCylinderSection5Drawing k G)
    (hGF : G.IsSubdrawing F) (hFU : F.U = G.U ∪ bd ClosedCylinder)
    (hFV : F.V = G.V) (i : Fin k) :
    ∃ e ∈ F.E, cylinderN1Point k i ∈ e ∧ e ∉ G.E ∧ e ⊆ bd ClosedCylinder ∧
      e ⊆ cylinderRegion k G i ∧ cylinderM1Point k i ∈ closure e ∧
      cylinderM1Point k (finSuccCycle i) ∈ closure e ∧
      initialCuffGapCurve k i '' Ioo 0 1 ⊆ e := by
  have hN : cylinderN1Point k i ∈ F.U := by
    rw [hFU, bd_closedCylinder]
    exact Or.inr (Or.inl rfl)
  have hNV : cylinderN1Point k i ∉ F.V := by
    rw [hFV]
    exact fun h => cylinderN1Point_not_mem_U hG i (G.V_subset_U h)
  obtain ⟨e, he, hNe⟩ := F.exists_edge_of_mem hN hNV
  have heG : e ∉ G.E := fun h => cylinderN1Point_not_mem_U hG i ((h.2.1 hNe).1)
  have heBd : e ⊆ bd ClosedCylinder :=
    (edge_mem_or_subset_boundary_of_adjoining hGF hFU hFV he).resolve_left heG
  have heGU := disjoint_old_U_of_new_edge hGF hFV he heG
  have heR : e ⊆ cylinderRegion k G i :=
    he.2.2.1.isConnected.isPreconnected.subset_connectedComponentIn hNe
      (fun _ hx => ⟨mem_univ _, disjoint_left.mp heGU hx⟩)
  let f := initialCuffGapCurve k i
  obtain ⟨hf0, hf1, hfC, hNf, hfR⟩ := initialCuffGapCurve_props hG i
  have hgap : f '' Ioo 0 1 ⊆ F.U \ F.V := by
    intro x hx
    constructor
    · rw [hFU, bd_closedCylinder]
      exact Or.inr (Or.inl (hfC (image_subset_range _ _ hx)))
    · rw [hFV]
      exact fun hxV => (connectedComponentIn_subset _ _ (hfR hx)).2 (G.V_subset_U hxV)
  obtain ⟨hfE, hends⟩ := arc_interior_subset_edge he hgap ⟨_, hNe, hNf⟩
  exact ⟨e, he, hNe, heG, heBd, heR, hf0 ▸ hends (mem_range_self 0),
    hf1 ▸ hends (mem_range_self 1), hfE⟩

end GraphMinor.GM06
