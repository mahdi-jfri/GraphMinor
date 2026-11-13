module

public import GraphMinor.GM06.Section3Dual
public import GraphMinor.GM11.Defs
public import GraphMinor.Surface.TopologyStatements
import GraphMinor.GM06.Alg511ComponentRegion
import GraphMinor.GM06.Section3Induce
import GraphMinor.GM06.Section5SphereRegions
import GraphMinor.GM06.Section5RegionWalkTools
import GraphMinor.GM11.RegionCount
import GraphMinor.GM11.PerimeterCount
import GraphMinor.GM11.Walks
import Mathlib.Tactic

/-!
# Finite geometric boundary walks for the cylinder input

The drawing input of VI (5.11), page 134, may have disconnected
regions. First identify the exact point set traced by a collar
walk. Induce the drawing on one incident graph component and use
its connected sphere drawing to obtain a region collar. Shortening
the collar to avoid the other closed components keeps it in the
original region. Its walk therefore traces precisely that part of
the original frontier. An isolated vertex contributes an empty
walk. The finitely many incident components then give a disjoint
family whose union is the whole frontier. All walks and geometric
maps below are existence witnesses for the input correspondence.
-/

public section
namespace GraphMinor.GM06
open Set Topology GraphMinor.Surface GraphMinor.GM11 unitInterval
universe u

/-- A boundary walk follows a collar from the stated region. A
zero-length walk records an isolated boundary vertex. For a walk
with edges, the collar is injective at positive height and its
bottom runs once along each step of the supplied closed walk. -/
@[expose] def Alg511RegionBoundaryTrace
    {S : Type u} [TopologicalSpace S] (G : Drawing S) (r : Set S)
    (C : Graph S (Set S)) {v : S} (W : GraphWalk G.toGraph v v) : Prop :=
  W.length = 0 ∨ ∃ (h : C(Circle × I, S)) (ε : I),
    0 < ε ∧ InjOn h {p | 0 < p.2} ∧
    (∀ z t, 0 < t → t ≤ ε → h (z, t) ∈ r) ∧
    range (fun z : Circle => h (z, 0)) = frontier r ∩ compPointSet C ∧
    RunsAlongOn G (collarCurve h) 0 1 W

private theorem exists_walk_up_with_runs
    {S : Type u} [TopologicalSpace S] [T2Space S] {D G : Drawing S}
    (hDG : D.IsSubdrawing G) {u v : S} (W : GraphWalk D.toGraph u v) :
    ∃ W' : GraphWalk G.toGraph u v, W'.support = W.support ∧ W'.edges = W.edges ∧
      ∀ (φ : ℝ → S) (a b : ℝ), RunsAlongOn D φ a b W → RunsAlongOn G φ a b W' := by
  induction W with
  | nil hu => exact ⟨.nil (hDG.1 hu), rfl, rfl, fun _ _ _ h => h⟩
  | @cons u c v e he W ih =>
    obtain ⟨W', hs, hedges, hrun⟩ := ih
    refine ⟨.cons ((hDG.isLink_iff he.1).mp he) W', ?_, ?_, ?_⟩
    · simp only [GraphWalk.support_cons, hs]
    · change e :: W'.edges = e :: W.edges
      rw [hedges]
    · rintro φ a b ⟨t, hat, hφ, hinj, himage, hrest⟩
      exact ⟨t, hat, hφ, hinj, himage, hrun φ t b hrest⟩

/-- A closed walk traced once by a continuous collar has exactly the
point set of that collar's bottom, including repeated edges. -/
private theorem alg511_walkDrawing_eq_collar_bottom
    {S : Type u} [TopologicalSpace S] [T2Space S] (G : Drawing S)
    {u : S} (W : GraphWalk G.toGraph u u) (h : C(Circle × I, S))
    (hrun : RunsAlongOn G (collarCurve h) 0 1 W) :
    (walkDrawing G W).U = range (fun z : Circle => h (z, 0)) := by
  let T := range (fun z : Circle => h (z, 0))
  have hT : IsClosed T := (isCompact_range
    (h.continuous.comp (continuous_id.prodMk continuous_const))).isClosed
  have hcurve : ∀ t ∈ Icc (0 : ℝ) 1, collarCurve h t ∈ T := by
    intro t _
    exact ⟨Circle.exp (2 * Real.pi * t), rfl⟩
  obtain ⟨hvertices, hedges⟩ := support_edges_subset_of_runsAlongOn W hrun hcurve
  apply subset_antisymm
  · intro x hx
    rcases (mem_walkDrawing_U G W).mp hx with hx | ⟨e, he, hxe⟩
    · exact hvertices x hx
    · exact closure_minimal (hedges e he) hT hxe
  · rintro x ⟨z, rfl⟩
    obtain ⟨t, ht, hzt⟩ := exists_collar_time z
    have hpoint : collarCurve h t = h (z, 0) := by
      change h (Circle.exp (2 * Real.pi * t), 0) = h (z, 0)
      rw [← hzt]
    by_cases hvertex : collarCurve h t ∈ G.V
    · apply (mem_walkDrawing_U G W).mpr
      have hv := vertex_mem_support_of_runsAlongOn W hrun t ⟨ht.1, ht.2.le⟩ hvertex
      rw [hpoint] at hv
      exact Or.inl hv
    · obtain ⟨e, he, hpointEdge⟩ := runs_mem W hrun t ⟨ht.1, ht.2.le⟩ hvertex
      apply (mem_walkDrawing_U G W).mpr
      rw [hpoint] at hpointEdge
      exact Or.inr ⟨e, he, subset_closure hpointEdge⟩

/-- A component with an edge contributes one closed walk tracing
exactly its part of an actual input region's frontier. -/
private theorem alg511_exists_component_boundary_walk_of_edge
    {S : Type u} [TopologicalSpace S] [T2Space S] [ConnectedSpace S]
    (hS : IsClosedSurface S) (hsph : IsSphere S) (G : Drawing S)
    {C : Graph S (Set S)} (hC : IsGraphComponent C G.toGraph)
    (hE : C.edgeSet.Nonempty) {r : Set S} (hr : r ∈ G.R)
    (hcontact : (compPointSet C ∩ closure r).Nonempty) :
    ∃ (v : S) (W : GraphWalk G.toGraph v v),
      (walkDrawing G W).U = frontier r ∩ compPointSet C ∧
      Alg511RegionBoundaryTrace G r C W := by
  classical
  let : LocallyConnectedSpace S := IsClosedSurface.locallyConnectedSpace hS
  let D := induceDrawing G C.vertexSet
  have hDG : D.IsSubdrawing G := induceDrawing_isSubdrawing G hC.1.vertexSet_mono
  have hDU : D.U = compPointSet C := induceDrawing_U_of_component G hC
  let others := graphComponents G.toGraph \ {C}
  let Q := ⋃ B ∈ others, compPointSet B
  have hfinite : others.Finite := (finite_graphComponents G).subset sdiff_subset
  have hQ : IsClosed Q := hfinite.isClosed_biUnion
    (fun B hB => isClosed_compPointSet G hB.1)
  have hdis : Disjoint D.U Q := by
    rw [hDU]
    apply disjoint_left.mpr
    intro p hpC hpQ
    obtain ⟨B, hB, hpB⟩ := mem_iUnion₂.mp hpQ
    exact disjoint_left.mp (disjoint_compPointSet_of_ne G hC hB.1 (Ne.symm hB.2)) hpC hpB
  have hU : G.U = D.U ∪ Q := by
    apply subset_antisymm
    · intro p hp
      rw [← biUnion_compPointSet_eq_U G] at hp
      obtain ⟨B, hB, hpB⟩ := mem_iUnion₂.mp hp
      by_cases hBC : B = C
      · exact Or.inl (hDU.symm ▸ (hBC ▸ hpB))
      · exact Or.inr (mem_iUnion₂.mpr ⟨B, ⟨hB, hBC⟩, hpB⟩)
    · rintro p (hpD | hpQ)
      · exact hDG.U_subset hpD
      · obtain ⟨B, hB, hpB⟩ := mem_iUnion₂.mp hpQ
        rw [← biUnion_compPointSet_eq_U G]
        exact mem_iUnion₂.mpr ⟨B, hB.1, hpB⟩
  obtain ⟨a, har⟩ := region_nonempty hr
  have haD : a ∉ D.U := fun ha => region_subset hr har (hDG.U_subset ha)
  obtain ⟨R, hR, haR⟩ := exists_region_of_notMem haD
  have hrR : r ⊆ R := subset_region hR (region_isPreconnected hr)
    (disjoint_left.mpr (fun p hpr hpD => region_subset hr hpr (hDG.U_subset hpD))) har haR
  have hconn : IsConnected D.U := by
    rw [hDU]
    exact isConnected_compPointSet G hC
  have hDE : D.E.Nonempty := by
    change (induceDrawing G C.vertexSet).E.Nonempty
    rw [induceDrawing_E_of_component G hC]
    exact hE
  have hcell : D.IsTwoCell := isTwoCell_of_connected_drawing_in_sphere hS hsph hconn
  obtain ⟨v, W, h, _, hinj, hpos, hbot, hop, hrun, _⟩ :=
    exists_region_walk hS hsph hcell hDE hR
  obtain ⟨x, hxC, hxr⟩ := hcontact
  obtain ⟨ε, hε, hshort, hfront⟩ := alg511_component_region_collar_height hU hQ hdis hr hR hrR
    (hDU.symm ▸ hxC) hxr h hinj hpos hbot hop
  have hboundary : frontier R = frontier r ∩ D.U := by
    apply subset_antisymm
    · intro p hp
      have hnR : p ∉ R := by simpa only [(region_isOpen hR).interior_eq] using hp.2
      exact ⟨hfront hp, (closure_region_subset hR hp.1).resolve_left hnR⟩
    · rintro p ⟨hpr, hpD⟩
      refine ⟨closure_mono hrR hpr.1, ?_⟩
      rw [(region_isOpen hR).interior_eq]
      exact fun hpR => region_subset hR hpR hpD
  obtain ⟨W', hsupport, hedges, hrunUp⟩ := exists_walk_up_with_runs hDG W
  have hwalk : (walkDrawing G W').U = (walkDrawing D W).U := by
    ext p
    rw [mem_walkDrawing_U, mem_walkDrawing_U, hsupport, hedges]
  refine ⟨v, W', ?_, Or.inr ⟨h, ε, hε, hinj, hshort, ?_, hrunUp _ _ _ hrun⟩⟩
  · rw [hwalk, alg511_walkDrawing_eq_collar_bottom D W h hrun, hbot, hboundary, hDU]
  · rw [hbot, hboundary, hDU]

private theorem walk_ends_eq_of_no_edges {S : Type u} {C : Graph S (Set S)}
    (hE : C.edgeSet = ∅) {a b : S} (W : GraphWalk C a b) : a = b := by
  cases W with
  | nil _ => rfl
  | cons he _ =>
    have hmem := he.edge_mem
    rw [hE] at hmem
    exact False.elim hmem

/-- An edgeless component of the input is exactly one isolated
vertex, rather than an unrecorded empty part of a region boundary. -/
private theorem alg511_edgeless_component_pointSet
    {S : Type u} [TopologicalSpace S] (G : Drawing S)
    {C : Graph S (Set S)} (hC : IsGraphComponent C G.toGraph) (hE : C.edgeSet = ∅) :
    ∃ v ∈ C.vertexSet, compPointSet C = {v} := by
  obtain ⟨v, hv⟩ := hC.2.1.1
  have hV : C.vertexSet = {v} := by
    apply eq_singleton_iff_unique_mem.mpr
    refine ⟨hv, ?_⟩
    intro a ha
    obtain ⟨W⟩ := hC.2.1.2 a ha v hv
    exact walk_ends_eq_of_no_edges hE W
  refine ⟨v, hv, ?_⟩
  rw [compPointSet, hV, hE]
  simp

/-- Every component incident with an input region contributes a
closed walk tracing exactly its part of that region's frontier.
An isolated vertex is represented by the empty walk. -/
private theorem alg511_exists_component_boundary_walk
    {S : Type u} [TopologicalSpace S] [T2Space S] [ConnectedSpace S]
    (hS : IsClosedSurface S) (hsph : IsSphere S) (G : Drawing S)
    {C : Graph S (Set S)} (hC : IsGraphComponent C G.toGraph)
    {r : Set S} (hr : r ∈ G.R) (hcontact : (compPointSet C ∩ closure r).Nonempty) :
    ∃ (v : S) (W : GraphWalk G.toGraph v v),
      (walkDrawing G W).U = frontier r ∩ compPointSet C ∧
      Alg511RegionBoundaryTrace G r C W := by
  classical
  by_cases hE : C.edgeSet.Nonempty
  · exact alg511_exists_component_boundary_walk_of_edge hS hsph G hC hE hr hcontact
  · have hEempty : C.edgeSet = ∅ := not_nonempty_iff_eq_empty.mp hE
    obtain ⟨v, hv, hpoint⟩ := alg511_edgeless_component_pointSet G hC hEempty
    have hvG : v ∈ G.V := hC.1.vertexSet_mono hv
    have hvcl : v ∈ closure r := by
      obtain ⟨x, hxC, hxr⟩ := hcontact
      have hxv : x = v := mem_singleton_iff.mp (hpoint ▸ hxC)
      exact hxv ▸ hxr
    have hvfront : v ∈ frontier r := by
      refine ⟨hvcl, ?_⟩
      exact fun hvint => region_subset hr (interior_subset hvint) (G.V_subset_U hvG)
    refine ⟨v, .nil hvG, ?_, Or.inl rfl⟩
    rw [hpoint, inter_eq_right.mpr (singleton_subset_iff.mpr hvfront)]
    ext p
    rw [mem_walkDrawing_U]
    simp [GraphWalk.support, GraphWalk.edges]

/-- Every region of a possibly disconnected sphere drawing has a
finite disjoint family of closed boundary walks, indexed bijectively
by its incident drawing components. -/
theorem alg511_exists_region_boundary_traces
    {S : Type u} [TopologicalSpace S] [T2Space S] [ConnectedSpace S]
    (hS : IsClosedSurface S) (hsph : IsSphere S) (G : Drawing S)
    {r : Set S} (hr : r ∈ G.R) :
    ∃ (n : ℕ)
      (component : Fin n ≃ {C : Graph S (Set S) |
        IsGraphComponent C G.toGraph ∧ (compPointSet C ∩ closure r).Nonempty})
      (start : Fin n → S) (W : ∀ i, GraphWalk G.toGraph (start i) (start i)),
      (∀ i, (walkDrawing G (W i)).U = frontier r ∩ compPointSet (component i).val ∧
        Alg511RegionBoundaryTrace G r (component i).val (W i)) ∧
      (⋃ i, (walkDrawing G (W i)).U) = frontier r ∧
      Pairwise (fun i j => Disjoint (walkDrawing G (W i)).U (walkDrawing G (W j)).U) := by
  classical
  let : LocallyConnectedSpace S := IsClosedSurface.locallyConnectedSpace hS
  let T := {C : Graph S (Set S) |
    IsGraphComponent C G.toGraph ∧ (compPointSet C ∩ closure r).Nonempty}
  have hT : T.Finite := (finite_graphComponents G).subset (fun _ h => h.1)
  let : Fintype T := hT.fintype
  let component : Fin (Fintype.card T) ≃ T := (Fintype.equivFin T).symm
  choose start W hW htrace using fun i : Fin (Fintype.card T) =>
    alg511_exists_component_boundary_walk hS hsph G (component i).property.1
      hr (component i).property.2
  refine ⟨Fintype.card T, component, start, W, fun i => ⟨hW i, htrace i⟩, ?_, ?_⟩
  · ext p
    constructor
    · intro hp
      obtain ⟨i, hpi⟩ := mem_iUnion.mp hp
      rw [hW i] at hpi
      exact hpi.1
    · intro hpr
      have hpnr : p ∉ r := by simpa only [(region_isOpen hr).interior_eq] using hpr.2
      have hpU : p ∈ G.U := (closure_region_subset hr hpr.1).resolve_left hpnr
      rw [← biUnion_compPointSet_eq_U G] at hpU
      obtain ⟨C, hC, hpC⟩ := mem_iUnion₂.mp hpU
      let c : T := ⟨C, hC, p, hpC, hpr.1⟩
      obtain ⟨i, hi⟩ := component.surjective c
      refine mem_iUnion.mpr ⟨i, ?_⟩
      rw [hW i]
      refine ⟨hpr, ?_⟩
      have heq : (component i).val = C := congrArg Subtype.val hi
      rw [heq]
      exact hpC
  · intro i j hij
    rw [hW i, hW j]
    have hne : (component i).val ≠ (component j).val :=
      fun heq => hij (component.injective (Subtype.ext heq))
    exact (disjoint_compPointSet_of_ne G (component i).property.1
      (component j).property.1 hne).mono inter_subset_right inter_subset_right

/-- The finite boundary walks cover the entire region frontier,
including isolated boundary vertices, and have disjoint point sets. -/
theorem alg511_exists_region_boundary_walks
    {S : Type u} [TopologicalSpace S] [T2Space S] [ConnectedSpace S]
    (hS : IsClosedSurface S) (hsph : IsSphere S) (G : Drawing S)
    {r : Set S} (hr : r ∈ G.R) :
    ∃ (n : ℕ)
      (component : Fin n ≃ {C : Graph S (Set S) |
        IsGraphComponent C G.toGraph ∧ (compPointSet C ∩ closure r).Nonempty})
      (start : Fin n → S) (W : ∀ i, GraphWalk G.toGraph (start i) (start i)),
      (∀ i, (walkDrawing G (W i)).U = frontier r ∩ compPointSet (component i).val) ∧
      (⋃ i, (walkDrawing G (W i)).U) = frontier r ∧
      Pairwise (fun i j => Disjoint (walkDrawing G (W i)).U (walkDrawing G (W j)).U) := by
  obtain ⟨n, c, v, W, hW, hcover, hdis⟩ := alg511_exists_region_boundary_traces hS hsph G hr
  exact ⟨n, c, v, W, fun i => (hW i).1, hcover, hdis⟩

end GraphMinor.GM06
