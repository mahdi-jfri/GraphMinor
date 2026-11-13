module

public import GraphMinor.GM06.Defs
import GraphMinor.GM06.Section5RegionGraphPath
import GraphMinor.GM06.Section5FirstHit
import GraphMinor.GM06.Section5StripBoundary
import GraphMinor.GM06.Section5RegionPoint
import GraphMinor.GM06.Section5RegionInterior
import GraphMinor.GM06.Section5NoReduction1
import GraphMinor.GM06.Section5EndpointObstruction
import GraphMinor.GM06.Section4PathTools
import GraphMinor.GM11.Walks
import GraphMinor.Surface.CutComp

/-!
# A region path reaches beyond the next initial vertex

For VI (5.1), page 129, stop the region-boundary path at its first
contact with Pᵢ₊₁. The region closure misses every non-neighbouring
linkage path and meets Pᵢ only at sᵢ. Thus the new path stays in Σᵢ
apart from its ends. If its last vertex were sᵢ₊₁, its last edge
would permit Reduction 1. The contact is therefore farther along Pᵢ₊₁.
-/

public section

namespace GraphMinor.GM06

open Set Topology GraphMinor.Surface GraphMinor.GM11

/-- Cyclic predecessor and successor undo each other. -/
theorem finPredCycle_finSuccCycle {k : ℕ} (i : Fin k) :
    finPredCycle (finSuccCycle i) = i := by
  apply Fin.ext
  by_cases hi : i.val + 1 < k
  · simp [finSuccCycle, hi, finPredCycle]
  · have he : i.val + 1 = k := by omega
    simp [finSuccCycle, hi, finPredCycle]
    omega

private theorem mem_strip_of_mem_closure
    {k : ℕ} {G : Drawing ClosedCylinder} (L : CylinderLinkage k G) (i : Fin k)
    {x : ClosedCylinder} (hx : x ∈ closure (cylinderStrip L i))
    (hoff : x ∉ ⋃ j : Fin k, (L.pathDrawing j).U) : x ∈ cylinderStrip L i := by
  let : LocallyConnectedSpace ClosedCylinder := IsSurface.locallyConnected isSurface_closedCylinder
  let Y := univ \ ⋃ j : Fin k, (L.pathDrawing j).U
  have hY : IsOpen Y := isOpen_univ.sdiff
    (isClosed_iUnion_of_finite fun j => (L.pathDrawing j).isClosed_U)
  have hxY : x ∈ Y := ⟨mem_univ _, hoff⟩
  change x ∈ closure (connectedComponentIn Y (cylinderN1Point k i)) at hx
  change x ∈ connectedComponentIn Y (cylinderN1Point k i)
  obtain ⟨y, hyx, hyi⟩ := mem_closure_iff.mp hx _ hY.connectedComponentIn
    (mem_connectedComponentIn hxY)
  rw [connectedComponentIn_eq hyi, ← connectedComponentIn_eq hyx]
  exact mem_connectedComponentIn hxY

/-- A nondegenerate path has an edge incident with its terminal
vertex. -/
theorem exists_terminal_edge
    {S : Type*} [TopologicalSpace S] {Q : Drawing S} {s t : S} (hQ : IsPathDrawing Q s t) :
    ∃ e ∈ Q.E, t ∈ closure e := by
  have hst := isPathDrawing_start_ne_end hQ
  obtain ⟨W, _, _, hE⟩ := hQ.1
  have hr : ∃ e ∈ W.reverse.edges, t ∈ closure e := by
    cases W.reverse with
    | nil _ => exact False.elim (hst rfl)
    | @cons t a s e hl R =>
      refine ⟨e, List.mem_cons_self, ?_⟩
      have ht : t ∈ closure e ∩ Q.V := by
        rw [hl.2.2.2]
        exact mem_insert t {a}
      exact ht.1
  obtain ⟨e, he, ht⟩ := hr
  have heW : e ∈ W.edges := by
    simpa only [GraphWalk.edges_reverse, List.mem_reverse] using he
  exact ⟨e, by rw [hE]; exact heW, ht⟩

/-- The path Qᵢ in the proof of VI (5.1), page 129, follows from the
local boundary-contact condition on Pᵢ. Its terminal vertex is on Pᵢ₊₁
and differs from sᵢ₊₁, and all other points are in the intervening strip. -/
theorem exists_path_to_next_linkage_in_strip
    {k : ℕ} {G : Drawing ClosedCylinder} {θ : ℝ}
    (L : CylinderLinkage k G) (hG : IsCylinderSection5Drawing k G)
    (hk : 1 < k) (hθ : L.HasTheta θ)
    (hno : ¬ Section5AnyReductionApplies k G L) (i : Fin k)
    (hcontact : closure (cylinderRegion k G i) ∩ (L.pathDrawing i).U ⊆
      {cylinderM1Point k i}) :
    ∃ t ∈ (L.pathDrawing (finSuccCycle i)).V,
      t ≠ cylinderM1Point k (finSuccCycle i) ∧ ∃ Q : Drawing ClosedCylinder,
        IsSubpathOf G Q (cylinderM1Point k i) t ∧
        Q.U ⊆ cylinderStrip L i ∪ {cylinderM1Point k i, t} ∧
        Q.U ∩ (L.pathDrawing (finSuccCycle i)).U ⊆ {t} := by
  obtain ⟨R, hR, hRR⟩ := exists_subpath_in_original_region_closure L hG hk hθ hno i hcontact
  have hsU : cylinderM1Point k i ∈ (L.pathDrawing i).U :=
    (L.pathDrawing i).V_subset_U (isPathDrawing_end_vertices (L.isPath i)).1
  have hsOff : cylinderM1Point k i ∉ (L.pathDrawing (finSuccCycle i)).U := by
    intro hh
    exact disjoint_left.mp (L.pairwise_disjoint (finSuccCycle_ne_of_one_lt hk i).symm) hsU hh
  have htV := (isPathDrawing_end_vertices (L.isPath (finSuccCycle i))).1
  obtain ⟨t, ht, Q, hQ, hfirst⟩ := exists_subpath_first_contact hR.1
    (L.isSubdrawing (finSuccCycle i)).1 hR.2.2 hsOff htV
  have hQG : Q.IsSubdrawing G := hQ.1.trans hR.1
  have hQR : Q.U ⊆ closure (cylinderRegion k G i) := hQ.2.1.trans hRR
  have hmeet : Q.U ∩ (⋃ j : Fin k, (L.pathDrawing j).U) ⊆ {cylinderM1Point k i, t} := by
    intro x hx
    obtain ⟨j, hxj⟩ := mem_iUnion.mp hx.2
    by_cases hji : j = i
    · subst j
      exact Or.inl (mem_singleton_iff.mp (hcontact ⟨hQR hx.1, hxj⟩))
    by_cases hjs : j = finSuccCycle i
    · subst j
      exact Or.inr (hfirst ⟨hx.1, hxj⟩)
    exact False.elim (disjoint_left.mp
      (disjoint_closure_region_path_of_not_neighbour L hG hθ i j hji hjs) (hQR hx.1) hxj)
  have hconf : Q.U ⊆ cylinderStrip L i ∪ {cylinderM1Point k i, t} := by
    intro x hx
    by_cases hxL : x ∈ ⋃ j : Fin k, (L.pathDrawing j).U
    · exact Or.inr (hmeet ⟨hx, hxL⟩)
    · exact Or.inl (mem_strip_of_mem_closure L i
        (closure_mono (cylinderRegion_subset_strip L i) (hQR hx)) hxL)
  obtain ⟨e, heQ, hte⟩ := exists_terminal_edge hQ.2.2
  have heG := hQG.2 heQ
  have heStrip : e ⊆ cylinderStrip L i := by
    intro x hx
    rcases hconf ((heQ.2.1 hx).1) with hxS | hxEnds
    · exact hxS
    · apply False.elim
      apply (heG.2.1 hx).2
      rcases hxEnds with heq | heq
      · rw [heq]
        exact (L.isSubdrawing i).1.1 (isPathDrawing_end_vertices (L.isPath i)).1
      · rw [mem_singleton_iff.mp heq]
        exact (L.isSubdrawing (finSuccCycle i)).1.1 ht
  have htne : t ≠ cylinderM1Point k (finSuccCycle i) := by
    intro heq
    apply hno
    apply reduction1_applies_of_incident_edge_in_strip L hk hG heG (heq ▸ hte)
    rw [finPredCycle_finSuccCycle]
    exact heStrip
  exact ⟨t, ht, htne, Q, ⟨hQG, hQG.U_subset, hQ.2.2⟩, hconf, hfirst⟩

end GraphMinor.GM06
