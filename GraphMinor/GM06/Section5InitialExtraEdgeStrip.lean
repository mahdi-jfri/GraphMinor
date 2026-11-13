module

public import GraphMinor.GM06.Defs
import GraphMinor.GM06.Section5LinkageDrawing
import GraphMinor.GM06.Section5RegionPoint
import GraphMinor.GM06.Section5RegionInterior
import GraphMinor.GM06.Section5InitialStripNeighbourhood
import GraphMinor.GM06.Section5NoReduction1
import GraphMinor.GM11.Regions
import GraphMinor.GM11.CircuitRegions
import GraphMinor.Surface.CutComp

/-!
# Locating extra initial edges in the following strip

For the boundary-contact step of VI (5.1), page 129, two adjacent
strip closures cover a neighbourhood of sᵢ. An edge outside all
linkage paths meets one of those closures off the linkage, hence
meets the strip itself. Connectedness places the whole edge there.
Reduction 1 rules out the preceding strip, leaving Σᵢ.
-/

public section
namespace GraphMinor.GM06
open Set Topology GraphMinor.Surface

/-- Closing a linkage strip adds only points of the linkage. -/
theorem closure_cylinderStrip_subset_strip_union_linkage
    {k : ℕ} {G : Drawing ClosedCylinder} (L : CylinderLinkage k G)
    (hG : IsCylinderSection5Drawing k G) (i : Fin k) :
    closure (cylinderStrip L i) ⊆ cylinderStrip L i ∪ ⋃ j, (L.pathDrawing j).U := by
  have : LocallyConnectedSpace ClosedCylinder := IsSurface.locallyConnected isSurface_closedCylinder
  obtain ⟨H, hHG, hHU, _, _, _, _⟩ := exists_linkage_union_drawing L hG
  have hr : cylinderStrip L i ∈ H.R := by
    change connectedComponentIn (univ \ ⋃ j, (L.pathDrawing j).U) (cylinderN1Point k i) ∈ H.R
    rw [← hHU]
    exact ⟨cylinderN1Point k i, ⟨mem_univ _,
      fun hx => cylinderN1Point_not_mem_U hG i (hHG.U_subset hx)⟩, rfl⟩
  simpa only [hHU] using GM11.closure_region_subset hr

/-- A linkage-free edge meeting a strip lies wholly in that strip. -/
theorem edge_subset_strip_of_meets
    {k : ℕ} {G : Drawing ClosedCylinder} (L : CylinderLinkage k G)
    {e : Set ClosedCylinder} (he : e ∈ G.E)
    (hnot : ∀ j, e ∉ (L.pathDrawing j).E) (i : Fin k)
    {x : ClosedCylinder} (hxe : x ∈ e) (hxS : x ∈ cylinderStrip L i) :
    e ⊆ cylinderStrip L i := by
  have hoff : e ⊆ univ \ ⋃ j, (L.pathDrawing j).U := by
    intro y hy
    refine ⟨mem_univ _, ?_⟩
    intro hyl
    obtain ⟨j, hj⟩ := mem_iUnion.mp hyl
    exact disjoint_left.mp (GM11.edge_disjoint_U (L.isSubdrawing j).1 he (hnot j)) hy hj
  have hsub := he.2.2.1.isConnected.isPreconnected.subset_connectedComponentIn hxe hoff
  have heq := connectedComponentIn_eq hxS
  change cylinderStrip L i = connectedComponentIn (univ \ ⋃ j, (L.pathDrawing j).U) x at heq
  rw [← heq] at hsub
  exact hsub

/-- With no reduction, every extra original edge incident with sᵢ
lies in the following strip Σᵢ. This is the local edge-location step
in the proof of VI (5.1), page 129. -/
theorem initial_extra_edge_subset_following_strip_of_no_reduction1
    {k : ℕ} {G : Drawing ClosedCylinder} {θ : ℝ} (L : CylinderLinkage k G)
    (hG : IsCylinderSection5Drawing k G) (hθ : L.HasTheta θ)
    (hno : ∀ (G₁ : Drawing ClosedCylinder) (L₁ : CylinderLinkage k G₁),
      IsCylinderSection5Drawing k G₁ → ¬ Section5Reduction1Step k G L G₁ L₁) (i : Fin k)
    {e : Set ClosedCylinder} (he : e ∈ G.E)
    (hs : cylinderM1Point k i ∈ closure e) (hnot : ∀ j, e ∉ (L.pathDrawing j).E) :
    e ⊆ cylinderStrip L i := by
  obtain ⟨W, hW, hsW, hcover⟩ := exists_initial_nhds_subset_adjacent_strip_closures L hG hθ i
  obtain ⟨x, hxW, hxe⟩ := mem_closure_iff.mp hs W hW hsW
  have hxoff : x ∉ ⋃ j, (L.pathDrawing j).U := by
    intro hyl
    obtain ⟨j, hj⟩ := mem_iUnion.mp hyl
    exact disjoint_left.mp (GM11.edge_disjoint_U (L.isSubdrawing j).1 he (hnot j)) hxe hj
  have hstrip (j : Fin k) (hxj : x ∈ closure (cylinderStrip L j)) : x ∈ cylinderStrip L j :=
    (closure_cylinderStrip_subset_strip_union_linkage L hG j hxj).resolve_right hxoff
  rcases hcover hxW with hxprev | hxnext
  · have heprev := edge_subset_strip_of_meets L he hnot (finPredCycle i) hxe (hstrip _ hxprev)
    by_cases hi : finPredCycle i = i
    · exact hi ▸ heprev
    · have hk : 1 < k := by
        by_contra hn
        have hk1 : k = 1 := by have hkpos := hG.1; omega
        subst k
        exact hi (Subsingleton.elim _ _)
      exact False.elim (not_subset_strip_of_no_reduction1 L hk hG hno he hs heprev)
  · exact edge_subset_strip_of_meets L he hnot i hxe (hstrip _ hxnext)

/-- The unreduced case follows by excluding the specified reduction. -/
theorem initial_extra_edge_subset_following_strip
    {k : ℕ} {G : Drawing ClosedCylinder} {θ : ℝ} (L : CylinderLinkage k G)
    (hG : IsCylinderSection5Drawing k G) (hθ : L.HasTheta θ)
    (hno : ¬ Section5AnyReductionApplies k G L) (i : Fin k)
    {e : Set ClosedCylinder} (he : e ∈ G.E)
    (hs : cylinderM1Point k i ∈ closure e) (hnot : ∀ j, e ∉ (L.pathDrawing j).E) :
    e ⊆ cylinderStrip L i := by
  exact initial_extra_edge_subset_following_strip_of_no_reduction1 L hG hθ
    (fun G₁ L₁ hG₁ hRed => hno ⟨G₁, L₁, hG₁, Or.inl hRed⟩) i he hs hnot

end GraphMinor.GM06
