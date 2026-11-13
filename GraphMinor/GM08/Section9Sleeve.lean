module

public import GraphMinor.GM08.Section9Counts
import GraphMinor.GM08.Section9Euler
import GraphMinor.GM08.Section9Paths
import GraphMinor.GM08.Section9Enclosed
import GraphMinor.GM08.Section8Sleeve
import GraphMinor.GM16.DrawingPointConnectivity
import GraphMinor.GM16.DrawingGraphPaths

/-!
# The sleeve obstruction in VIII (9.1)

The argument on page 270 compares the cycle counts of a sleeve and a nest.
A nonempty sleeve is connected. We count its vertices and edges, count a
subdrawing formed by nest circuits and radial paths, and use monotonicity
of the edge-minus-vertex count under inclusion in a connected graph.
-/

public section

namespace GraphMinor.GM08

open Set Surface Topology Graph

universe u

private theorem pointSet_eq_of_union_vertices_edges {S : Type u} [TopologicalSpace S]
    {H : Drawing S} {r s : ℕ} (C : Fin s → Drawing S) (P : Fin r → Drawing S)
    (hV : H.V = (⋃ j, (C j).V) ∪ ⋃ i, (P i).V)
    (hE : H.E = (⋃ j, (C j).E) ∪ ⋃ i, (P i).E) :
    H.U = (⋃ j, (C j).U) ∪ ⋃ i, (P i).U := by
  apply subset_antisymm
  · intro x hx
    by_cases hxV : x ∈ H.V
    · rw [hV] at hxV
      rcases hxV with hxC | hxP
      · obtain ⟨j, hj⟩ := mem_iUnion.mp hxC
        exact Or.inl (mem_iUnion.mpr ⟨j, (C j).V_subset_U hj⟩)
      · obtain ⟨i, hi⟩ := mem_iUnion.mp hxP
        exact Or.inr (mem_iUnion.mpr ⟨i, (P i).V_subset_U hi⟩)
    · obtain ⟨e, he, hxe⟩ := H.exists_edge_of_mem hx hxV
      rw [hE] at he
      rcases he with heC | heP
      · obtain ⟨j, hj⟩ := mem_iUnion.mp heC
        exact Or.inl (mem_iUnion.mpr ⟨j, (hj.2.1 hxe).1⟩)
      · obtain ⟨i, hi⟩ := mem_iUnion.mp heP
        exact Or.inr (mem_iUnion.mpr ⟨i, (hi.2.1 hxe).1⟩)
  · have hCH : ∀ j, (C j).IsSubdrawing H := fun j =>
      ⟨fun x hx => hV ▸ Or.inl (mem_iUnion.mpr ⟨j, hx⟩),
        fun e he => hE ▸ Or.inl (mem_iUnion.mpr ⟨j, he⟩)⟩
    have hPH : ∀ i, (P i).IsSubdrawing H := fun i =>
      ⟨fun x hx => hV ▸ Or.inr (mem_iUnion.mpr ⟨i, hx⟩),
        fun e he => hE ▸ Or.inr (mem_iUnion.mpr ⟨i, he⟩)⟩
    rintro x (hxC | hxP)
    · obtain ⟨j, hj⟩ := mem_iUnion.mp hxC
      exact (hCH j).U_subset hj
    · obtain ⟨i, hi⟩ := mem_iUnion.mp hxP
      exact (hPH i).U_subset hi

private theorem isPreconnected_union_two_families {S : Type u} [TopologicalSpace S]
    {r s : ℕ} (C : Fin s → Set S) (P : Fin r → Set S) (hr : 0 < r) (hs : 0 < s)
    (hC : ∀ j, IsPreconnected (C j)) (hP : ∀ i, IsPreconnected (P i))
    (hmeet : ∀ j i, (C j ∩ P i).Nonempty) :
    IsPreconnected ((⋃ j, C j) ∪ ⋃ i, P i) := by
  let i₀ : Fin r := ⟨0, hr⟩
  let j₀ : Fin s := ⟨0, hs⟩
  obtain ⟨a, haC, haP⟩ := hmeet j₀ i₀
  let U₀ := ⋃ j, C j ∪ P i₀
  have hU₀ : IsPreconnected U₀ := isPreconnected_iUnion
    ⟨a, mem_iInter.mpr fun j => Or.inr haP⟩
    (fun j => (hC j).union' (hmeet j i₀) (hP i₀))
  have haU₀ : a ∈ U₀ := mem_iUnion.mpr ⟨j₀, Or.inl haC⟩
  have hU₁ : IsPreconnected (⋃ i, U₀ ∪ P i) := isPreconnected_iUnion
    ⟨a, mem_iInter.mpr fun i => Or.inl haU₀⟩ (fun i => hU₀.union'
      (by obtain ⟨x, hxC, hxP⟩ := hmeet j₀ i
          exact ⟨x, mem_iUnion.mpr ⟨j₀, Or.inl hxC⟩, hxP⟩) (hP i))
  have heq : (⋃ i, U₀ ∪ P i) = (⋃ j, C j) ∪ ⋃ i, P i := by
    apply subset_antisymm
    · intro x hx
      obtain ⟨i, hxU | hxP⟩ := mem_iUnion.mp hx
      · obtain ⟨j, hxC | hxP⟩ := mem_iUnion.mp hxU
        · exact Or.inl (mem_iUnion.mpr ⟨j, hxC⟩)
        · exact Or.inr (mem_iUnion.mpr ⟨i₀, hxP⟩)
      · exact Or.inr (mem_iUnion.mpr ⟨i, hxP⟩)
    · rintro x (hxC | hxP)
      · obtain ⟨j, hxC⟩ := mem_iUnion.mp hxC
        exact mem_iUnion.mpr ⟨i₀, Or.inl (mem_iUnion.mpr ⟨j, Or.inl hxC⟩)⟩
      · obtain ⟨i, hxP⟩ := mem_iUnion.mp hxP
        exact mem_iUnion.mpr ⟨i, Or.inr hxP⟩
  exact heq ▸ hU₁

/-- A sleeve with a vertex has at least one spoke, hence a vertex on its ring. -/
theorem IsSleeve.boundary_card_pos_of_nonempty {S : Type u} [TopologicalSpace S]
    {D Γ : Drawing S} {Δ F : Set S} (h : IsSleeve D Δ F Γ) (hne : Γ.V.Nonempty) :
    0 < (D.V ∩ F).ncard := by
  obtain ⟨_, _, _, _, sd, hV, _⟩ := h
  obtain ⟨x, hx⟩ := hne
  rw [hV] at hx
  rcases hx with hxC | hxP
  · obtain ⟨j, _⟩ := mem_iUnion.mp hxC
    have := j.isLt
    omega
  · obtain ⟨i, _⟩ := mem_iUnion.mp hxP
    exact Nat.zero_lt_of_lt i.isLt

/-- A nonempty sleeve is connected: every spoke meets every circuit in a path.
This checks the connectivity hypothesis in the cycle-count comparison of VIII (9.1). -/
theorem IsSleeve.isGraphConnected_of_nonempty {S : Type u} [TopologicalSpace S] [T2Space S]
    {D Γ : Drawing S} {Δ F : Set S} (h : IsSleeve D Δ F Γ) (hne : Γ.V.Nonempty) :
    GM06.IsGraphConnected Γ.toGraph := by
  have hr := h.boundary_card_pos_of_nonempty hne
  obtain ⟨_, _, _, _, sd, hV, hE⟩ := h
  have hs : 0 < ((D.V ∩ F).ncard + 1) / 2 := by omega
  have hPconn : ∀ i, IsPreconnected (sd.spoke i).U := by
    intro i
    obtain ⟨_, a, b, _, _, _, hp, _⟩ := sd.isPath_spoke i
    exact isPreconnected_U_of_isPathBetween hp
  have hCconn : ∀ j, IsPreconnected (sd.circuitDraw j).U := fun j =>
    (IsOArc.isConnected' (GM11.IsCircuit.isOArc_U (sd.isCircuit_draw j).2.1)).isPreconnected
  have hmeet : ∀ j i, ((sd.circuitDraw j).U ∩ (sd.spoke i).U).Nonempty := by
    intro j i
    obtain ⟨Q, a, b, -, hQV, -, W, -, -, -⟩ := sd.inter_isPath i j
    have ha : a ∈ Q.V := W.mem_vertexSet_of_mem_support W.start_mem_support
    rw [hQV] at ha
    exact ⟨a, (sd.circuitDraw j).V_subset_U ha.2, (sd.spoke i).V_subset_U ha.1⟩
  have hconn : IsPreconnected Γ.U := by
    rw [pointSet_eq_of_union_vertices_edges _ _ hV hE]
    exact isPreconnected_union_two_families _ _ hr hs hCconn hPconn hmeet
  exact ⟨hne, fun a ha b hb => GM16.drawing_walk_of_isPreconnected_U hconn ha hb⟩

/-- The cyclomatic-number obstruction in VIII (9.1), page 270.
A sleeve cannot contain a nest whose lower vertex/edge count exceeds
its own count. Keeping `k / 2 + 1` enclosed circuits makes this strict
also when the boundary has only two vertices. -/
theorem no_nest_in_sleeve_of_count {S : Type u} [TopologicalSpace S]
    [T2Space S] [ConnectedSpace S] {D Γ : Drawing S} {Δ F : Set S}
    (hΔ : IsClosedDisc Δ) (hDU : D.U ⊆ Δ) (hΓ : IsSleeve D Δ F Γ)
    {r s : ℕ} (hs : 2 ≤ s)
    (hcount : (D.V ∩ F).ncard * (((D.V ∩ F).ncard + 1) / 2) + r <
      r * s + (D.V ∩ F).ncard) (N : DrawingNest Γ Δ r s) : False := by
  classical
  have hΓU : Γ.U ⊆ Δ := hΓ.2.2.2.1.U_subset.trans hDU
  have hexC : ∀ j : Fin s, ∃ C : Drawing S,
      C.IsCircuit ∧ C.IsSubdrawing Γ ∧ C.U = (N.circuit j).U :=
    fun j => GM11.exists_circuit_of_oArc (N.circuit j).isOArc_U (N.circuit j).U_sub_drawing
  choose C hC hCD hCU using hexC
  obtain ⟨P, a, b, hP, hdisP⟩ := N.exists_radial_path_drawings hΔ hs
  have hends : ∀ p, a p ∈ (P p).U ∧ b p ∈ (P p).U := by
    intro p
    obtain ⟨W, _, _, _⟩ := (hP p).2.1
    exact ⟨(P p).V_subset_U (W.mem_vertexSet_of_mem_support W.start_mem_support),
      (P p).V_subset_U (W.mem_vertexSet_of_mem_support W.end_mem_support)⟩
  let N' : DrawingNest Γ Δ r s := {
    circuit := N.circuit
    inside_of_lt := N.inside_of_lt
    radialPath p := (P p).U
    isPreconnected_radialPath p := isPreconnected_U_of_isPathBetween (hP p).2.1
    radialPath_sub_U p := (hP p).1.U_subset
    radialPath_sub_disc p := (hP p).1.U_subset.trans hΓU
    pairwise_disjoint_paths := fun p q hpq =>
      (disjoint_U_of_disjoint_V_subdrawing (hP p).1 (hP q).1 (hdisP hpq)).mono
        inter_subset_left inter_subset_left
    meets_inner p _hs := ⟨a p, (hends p).1, (hP p).2.2.1⟩
    meets_outer p _hs := ⟨b p, (hends p).2, (hP p).2.2.2.1⟩
  }
  have hmeet : ∀ j p, ((C j).V ∩ (P p).V).Nonempty := by
    intro j p
    obtain ⟨x, ⟨hxP, hxC⟩, hxV⟩ := N'.exists_radial_vertex_on_circuit hΔ hs p j
    exact ⟨x, mem_subdrawing_vertex_of_mem_U (hCD j) (hCU j ▸ hxC) hxV,
      mem_subdrawing_vertex_of_mem_U (hP p).1 hxP hxV⟩
  have hCV : Pairwise (fun j j' => Disjoint (C j).V (C j').V) := by
    intro j j' hjj'
    exact Set.disjoint_left.mpr fun x hx hx' =>
      Set.disjoint_left.mp (N.pairwise_disjoint_circuits hΔ hjj')
        (hCU j ▸ (C j).V_subset_U hx) (hCU j' ▸ (C j').V_subset_U hx')
  let V₀ := (⋃ j, (C j).V) ∪ ⋃ p, (P p).V
  let E₀ := (⋃ j, (C j).E) ∪ ⋃ p, (P p).E
  have hV₀ : V₀ ⊆ Γ.V := union_subset
    (iUnion_subset fun j => (hCD j).1) (iUnion_subset fun p => (hP p).1.1)
  have hE₀ : E₀ ⊆ Γ.E := union_subset
    (iUnion_subset fun j => (hCD j).2) (iUnion_subset fun p => (hP p).1.2)
  have hcl : ∀ e ∈ E₀, closure e ∩ Γ.V ⊆ V₀ := by
    rintro e (heC | heP) x hx
    · obtain ⟨j, hj⟩ := mem_iUnion.mp heC
      rw [← (hCD j).closure_inter_V hj] at hx
      exact Or.inl (mem_iUnion.mpr ⟨j, hx.2⟩)
    · obtain ⟨p, hp⟩ := mem_iUnion.mp heP
      rw [← (hP p).1.closure_inter_V hp] at hx
      exact Or.inr (mem_iUnion.mpr ⟨p, hx.2⟩)
  obtain ⟨H, hHΓ, hHV, hHE⟩ := exists_span_subdrawing_in_disc hΔ hΓU hV₀ hE₀ hcl
  have hHne : H.V.Nonempty := by
    obtain ⟨u, W, _, _, hV, _⟩ := hC ⟨0, by omega⟩
    refine ⟨u, ?_⟩
    rw [hHV]
    have hu : u ∈ (C ⟨0, by omega⟩).V := by
      rw [hV]
      exact W.start_mem_support
    exact Or.inl (mem_iUnion.mpr ⟨⟨0, by omega⟩, hu⟩)
  have hΓne : Γ.V.Nonempty := by
    obtain ⟨u, hu⟩ := hHne
    exact ⟨u, hHΓ.1 hu⟩
  have hmono := card_edges_add_vertices_le_of_connected_supergraph Γ.finite_V Γ.finite_edges
    (hΓ.isGraphConnected_of_nonempty hΓne) (GM16.toGraph_le_of_isSubdrawing hHΓ) hHne
  have hlower := card_edges_add_paths_ge_of_circuit_path_union C P hCD
    (fun p => (hP p).1) hC (fun p => ⟨a p, b p, (hP p).2.1⟩)
    hCV hdisP hmeet hHV hHE
  have hupper := hΓ.card_edges_add_spokes hΔ
  change H.E.ncard + Γ.V.ncard ≤ Γ.E.ncard + H.V.ncard at hmono
  omega

/-- The sleeve bound used in the corrected proof of VIII (9.1), page 270.
A sleeve with fewer than `k` ring vertices has no `(r, k/2+1)`-nest for `r ≥ k`.
The extra enclosed circuit for even `k` also settles the two-boundary-vertex case. -/
theorem no_large_nest_in_sleeve {S : Type u} [TopologicalSpace S]
    [T2Space S] [ConnectedSpace S] {D Γ : Drawing S} {Δ F : Set S}
    (hΔ : IsClosedDisc Δ) (hDU : D.U ⊆ Δ) (hΓ : IsSleeve D Δ F Γ)
    {r k : ℕ} (hk : 0 < k) (hm : (D.V ∩ F).ncard < k) (hr : k ≤ r)
    (N : DrawingNest Γ Δ r (k / 2 + 1)) : False := by
  by_cases hk2 : 2 ≤ k
  · have hstrict := sleeve_cycle_count_lt_nest_cycle_count hk2 hm hr
    have hmprod : (D.V ∩ F).ncard * (((D.V ∩ F).ncard + 1) / 2) =
        (D.V ∩ F).ncard * (((D.V ∩ F).ncard + 1) / 2 - 1) + (D.V ∩ F).ncard := by
      by_cases hm0 : (D.V ∩ F).ncard = 0
      · simp only [hm0, Nat.zero_mul, Nat.add_zero]
      · have hpos : 1 ≤ ((D.V ∩ F).ncard + 1) / 2 := by omega
        conv_lhs => rw [← Nat.sub_add_cancel hpos]
        rw [Nat.mul_add, Nat.mul_one]
    apply no_nest_in_sleeve_of_count hΔ hDU hΓ (by omega) ?_ N
    rw [hmprod, Nat.mul_add, Nat.mul_one]
    omega
  · have hk1 : k = 1 := by omega
    subst k
    obtain ⟨C, hC, hCΓ, _⟩ := GM11.exists_circuit_of_oArc
      (N.circuit ⟨0, by decide⟩).isOArc_U (N.circuit ⟨0, by decide⟩).U_sub_drawing
    obtain ⟨u, W, _, _, hV, _⟩ := hC
    have hu : u ∈ C.V := by rw [hV]; exact W.start_mem_support
    have hpos := hΓ.boundary_card_pos_of_nonempty ⟨u, hCΓ.1 hu⟩
    omega

end GraphMinor.GM08

