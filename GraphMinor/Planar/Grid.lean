module

public import GraphMinor.Planar.Defs
public import GraphMinor.GM07.Section9
import GraphMinor.Minor.Basic

/-!
# Planar Graphs Are Minors of Grids (Graph Minors V, Section 2, pages 94–95)

This file proves the fact stated in N. Robertson and P. D. Seymour, *Graph Minors. V. Excluding a
Planar Graph*, J. Combin. Theory Ser. B **41** (1986), 92–114, Section 2 (pages 94–95):

"For any planar graph $H$ there is an even value of $\theta \ge 6$ such that $H$ is isomorphic to
a minor of the $\theta$-grid. (This is easy to see, but for a proof see [1, 12].)"

Following reference [12] (*Graph Minors. VII. Disjoint paths on a surface*, (9.6), page 246):
1. Any drawing `Γ : Drawing S` in a nonempty surface `S` can be oriented to a `SurfaceDigraph S`
   (`toSurfaceDigraph Γ`) by choosing an arbitrary head and tail in `tilde e = closure e ∩ Γ.V` for
   each edge `e ∈ Γ.E` (on a sphere `Σ`, `bd Σ = ∅`, so there are no boundary root vertices).
2. Any boundary-rooted minor (`IsBoundaryRootedMinor H_dig G_dig`) or digraph minor
   (`IsDigraphMinor H_dig G_dig`) between surface digraphs induces a minor model
   (`IsMinorModel H_dig.G.toGraph G_dig.G.toGraph`) of their underlying undirected graphs, and hence
   an undirected minor (`IsIsoMinor H_dig.G.toGraph G_dig.G.toGraph`) by
   `isIsoMinor_of_isMinorModel`.
3. Given a finite planar graph `H` (`IsPlanar H`), we take its sphere drawing `Γ_H : GraphDrawing H S`,
   orient `Γ_H.drawing` to a surface digraph `H_dig`, apply `GM07.theorem_9_6` to obtain threshold
   `N₀`, choose `θ = max 6 (2 * N₀)` (which is even and `≥ 6`), draw the `θ × θ`-grid in `S` via
   `GM07.exists_isGridDrawing`, and transport the resulting undirected minor along the graph
   isomorphisms `Γ_H.iso` and `iso_G`.
-/

@[expose] public section

namespace GraphMinor.Planar

open Set Function Topology Classical
open Graph SimpleGraph
open GraphMinor.Surface GraphMinor.GM01 GraphMinor.GM07

universe u v w

variable {S : Type w} [TopologicalSpace S]

/-! ## 1. Orienting a surface drawing to a `SurfaceDigraph` -/

/-- Every edge `e ∈ Γ.E` of a drawing `Γ` has two (not necessarily distinct) endpoints `u, v ∈ Γ.V`
such that `{u, v} = tilde e`. -/
theorem exists_ends_eq_tilde (Γ : Drawing S) {e : Set S} (he : e ∈ Γ.E) :
    ∃ u v : S, u ∈ Γ.V ∧ v ∈ Γ.V ∧ ({u, v} : Set S) = tilde e := by
  rw [tilde_eq_closure_inter_V Γ he]
  rcases Γ.edge_cond e he with ⟨u, v, _, hcap, _⟩ | ⟨u, hcap, _⟩
  · have hu : u ∈ Γ.V := by
      have : u ∈ closure e ∩ Γ.V := by rw [hcap]; exact mem_insert u {v}
      exact this.2
    have hv : v ∈ Γ.V := by
      have : v ∈ closure e ∩ Γ.V := by rw [hcap]; exact mem_insert_of_mem u rfl
      exact this.2
    exact ⟨u, v, hu, hv, hcap.symm⟩
  · have hu : u ∈ Γ.V := by
      have : u ∈ closure e ∩ Γ.V := by rw [hcap]; exact mem_singleton u
      exact this.2
    refine ⟨u, u, hu, hu, ?_⟩
    rw [pair_eq_singleton, hcap]

/-- Equip any drawing `Γ : Drawing S` in a nonempty space `S` with an arbitrary edge orientation to
form a `SurfaceDigraph S`. -/
noncomputable def toSurfaceDigraph [Nonempty S] (Γ : Drawing S) : SurfaceDigraph S where
  G := Γ
  plus e :=
    if he : e ∈ Γ.E then Classical.choose (exists_ends_eq_tilde Γ he)
    else Classical.arbitrary S
  minus e :=
    if he : e ∈ Γ.E then Classical.choose (Classical.choose_spec (exists_ends_eq_tilde Γ he))
    else Classical.arbitrary S
  plus_mem e he := by
    rw [dite_eq_left he]
    exact (Classical.choose_spec (Classical.choose_spec (exists_ends_eq_tilde Γ he))).1
  minus_mem e he := by
    rw [dite_eq_left he]
    exact (Classical.choose_spec (Classical.choose_spec (exists_ends_eq_tilde Γ he))).2.1
  ends_eq e he := by
    rw [dite_eq_left he, dite_eq_left he]
    exact (Classical.choose_spec (Classical.choose_spec (exists_ends_eq_tilde Γ he))).2.2

@[simp]
theorem toSurfaceDigraph_G [Nonempty S] (Γ : Drawing S) :
    (toSurfaceDigraph Γ).G = Γ :=
  rfl

/-! ## 2. Incidence and loop characterizations for `SurfaceDigraph.G.toGraph` -/

/-- In the underlying graph `D.G.toGraph` of a `SurfaceDigraph S`, every edge `e ∈ D.G.E` links
`D.plus e` and `D.minus e`. -/
theorem _root_.GraphMinor.GM07.SurfaceDigraph.toGraph_isLink_plus_minus (D : SurfaceDigraph S)
    {e : Set S} (he : e ∈ D.G.E) :
    D.G.toGraph.IsLink e (D.plus e) (D.minus e) := by
  refine ⟨he, D.plus_mem e he, D.minus_mem e he, ?_⟩
  rw [← tilde_eq_closure_inter_V D.G he, D.ends_eq e he]

/-- In `D.G.toGraph`, an edge `e ∈ D.G.E` is incident with `x` if and only if `x = D.plus e` or
`x = D.minus e`. -/
theorem _root_.GraphMinor.GM07.SurfaceDigraph.toGraph_inc_iff (D : SurfaceDigraph S)
    {e : Set S} (he : e ∈ D.G.E) (x : S) :
    D.G.toGraph.Inc e x ↔ x = D.plus e ∨ x = D.minus e := by
  constructor
  · rintro ⟨y, _, _, _, hcap⟩
    have hx_mem : x ∈ closure e ∩ D.G.V := by
      rw [hcap]
      exact mem_insert x {y}
    rw [← tilde_eq_closure_inter_V D.G he, ← D.ends_eq e he] at hx_mem
    simpa only [mem_insert_iff, mem_singleton_iff] using hx_mem
  · rintro (rfl | rfl)
    · exact ⟨D.minus e, D.toGraph_isLink_plus_minus he⟩
    · exact ⟨D.plus e, (D.toGraph_isLink_plus_minus he).symm⟩

/-- In `D.G.toGraph`, an edge `e ∈ D.G.E` is a loop at `v` if and only if `v = D.plus e` and
`v = D.minus e`. -/
theorem _root_.GraphMinor.GM07.SurfaceDigraph.toGraph_isLoopAt_iff (D : SurfaceDigraph S)
    {e : Set S} (he : e ∈ D.G.E) (v : S) :
    D.G.toGraph.IsLoopAt e v ↔ v = D.plus e ∧ v = D.minus e := by
  constructor
  · intro hloop
    have hcap : closure e ∩ D.G.V = {v} := by
      rw [hloop.2.2.2, pair_eq_singleton]
    have hpair : ({D.plus e, D.minus e} : Set S) = {v} := by
      rw [D.ends_eq e he, tilde_eq_closure_inter_V D.G he, hcap]
    have hp : D.plus e = v := by
      have : D.plus e ∈ ({v} : Set S) := hpair ▸ mem_insert (D.plus e) {D.minus e}
      exact mem_singleton_iff.mp this
    have hm : D.minus e = v := by
      have : D.minus e ∈ ({v} : Set S) := hpair ▸ mem_insert_of_mem (D.plus e) rfl
      exact mem_singleton_iff.mp this
    exact ⟨hp.symm, hm.symm⟩
  · rintro ⟨rfl, hminus⟩
    have hlink := D.toGraph_isLink_plus_minus he
    rwa [← hminus] at hlink

/-! ## 3. Turning a `SurfaceDigraph` minor into an undirected `IsMinorModel` and `IsIsoMinor` -/

/-- Any `GraphWalk K x y` implies `Relation.ReflTransGen K.Adj x y`. -/
private lemma reflTransGen_adj_of_graphWalk {α : Type u} {β : Type v} {K : Graph α β}
    {x y : α} (W : GraphWalk K x y) :
    Relation.ReflTransGen K.Adj x y := by
  induction W with
  | nil _ => exact Relation.ReflTransGen.refl
  | cons h _ ih => exact Relation.ReflTransGen.head h.adj ih

/-- Every `IsBoundaryRootedMinor H G` between surface digraphs gives an undirected minor model
`IsMinorModel H.G.toGraph G.G.toGraph`. -/
theorem isMinorModel_of_isBoundaryRootedMinor {H G : SurfaceDigraph S}
    (hMinor : IsBoundaryRootedMinor H G) :
    ∃ (ηv : S → Set S) (ηe : Set S → Set S),
      IsMinorModel H.G.toGraph G.G.toGraph ηv ηe := by
  rcases hMinor with ⟨_, φv, φe, hφv, hφe, hdisj, hinj, hnotMem, hinc, _⟩
  refine ⟨fun v => (φv v).V, φe, ?_⟩
  have hmem_plus_iff : ∀ {v : S}, v ∈ H.G.V → ∀ {e : Set S}, e ∈ H.G.E →
      (G.plus (φe e) ∈ (φv v).V ↔ v = H.plus e) := by
    intro v hv e he
    constructor
    · intro hmem
      by_contra hne
      exact disjoint_left.mp (hdisj v hv (H.plus e) (H.plus_mem e he) hne) hmem (hinc e he).1
    · rintro rfl
      exact (hinc e he).1
  have hmem_minus_iff : ∀ {v : S}, v ∈ H.G.V → ∀ {e : Set S}, e ∈ H.G.E →
      (G.minus (φe e) ∈ (φv v).V ↔ v = H.minus e) := by
    intro v hv e he
    constructor
    · intro hmem
      by_contra hne
      exact disjoint_left.mp (hdisj v hv (H.minus e) (H.minus_mem e he) hne) hmem (hinc e he).2
    · rintro rfl
      exact (hinc e he).2
  refine
    { vertex_nonempty := fun v hv => (hφv v hv).2.1
      vertex_subset := fun v hv => (hφv v hv).1.1
      edge_mem := fun e he => hφe e he
      vertex_disjoint := fun v₁ hv₁ v₂ hv₂ hne => hdisj v₁ hv₁ v₂ hv₂ hne
      edge_injOn := fun e₁ he₁ e₂ he₂ heq => by
        by_contra hne
        exact hinj e₁ he₁ e₂ he₂ hne heq
      inc_iff := fun v hv e he => by
        rw [H.toGraph_inc_iff he v]
        constructor
        · rintro (rfl | rfl)
          · exact ⟨G.plus (φe e), (hinc e he).1,
              (G.toGraph_inc_iff (hφe e he) _).mpr (Or.inl rfl)⟩
          · exact ⟨G.minus (φe e), (hinc e he).2,
              (G.toGraph_inc_iff (hφe e he) _).mpr (Or.inr rfl)⟩
        · rintro ⟨x, hxV, hxInc⟩
          rcases (G.toGraph_inc_iff (hφe e he) x).mp hxInc with rfl | rfl
          · exact Or.inl ((hmem_plus_iff hv he).mp hxV)
          · exact Or.inr ((hmem_minus_iff hv he).mp hxV)
      isLoopAt_iff := fun v hv e he => by
        rw [H.toGraph_isLoopAt_iff he v]
        constructor
        · rintro ⟨h1, h2⟩ x hxInc
          rcases (G.toGraph_inc_iff (hφe e he) x).mp hxInc with rfl | rfl
          · exact (hmem_plus_iff hv he).mpr h1
          · exact (hmem_minus_iff hv he).mpr h2
        · intro hall
          have hp : G.plus (φe e) ∈ (φv v).V :=
            hall _ ((G.toGraph_inc_iff (hφe e he) _).mpr (Or.inl rfl))
          have hm : G.minus (φe e) ∈ (φv v).V :=
            hall _ ((G.toGraph_inc_iff (hφe e he) _).mpr (Or.inr rfl))
          exact ⟨(hmem_plus_iff hv he).mp hp, (hmem_minus_iff hv he).mp hm⟩
      connected := fun v hv => by
        refine ⟨(φv v).toGraph, ?_, rfl, ?_⟩
        · refine ⟨(hφv v hv).1.1, fun f x y hlink => ?_⟩
          rw [Graph.deleteEdges_isLink]
          refine ⟨((hφv v hv).1.isLink_iff hlink.1).mp hlink, ?_⟩
          rintro ⟨e, he, rfl⟩
          exact hnotMem v hv e he hlink.1
        · refine ⟨(hφv v hv).2.1, fun x hx y hy => ?_⟩
          obtain ⟨W⟩ := (hφv v hv).2.2.2 x hx y hy
          exact reflTransGen_adj_of_graphWalk W }

/-- Every `IsBoundaryRootedMinor H G` between surface digraphs implies that `H.G.toGraph` is
isomorphic to a minor of `G.G.toGraph`. -/
theorem isIsoMinor_of_isBoundaryRootedMinor {H G : SurfaceDigraph S}
    (hMinor : IsBoundaryRootedMinor H G) :
    IsIsoMinor H.G.toGraph G.G.toGraph := by
  obtain ⟨ηv, ηe, hm⟩ := isMinorModel_of_isBoundaryRootedMinor hMinor
  exact isIsoMinor_of_isMinorModel H.G.toGraph G.G.toGraph
    H.G.finite_V H.G.finite_edges G.G.finite_V G.G.finite_edges ηv ηe hm

/-- Every `IsDigraphMinor H G` between surface digraphs implies that `H.G.toGraph` is isomorphic to
a minor of `G.G.toGraph`. -/
theorem isIsoMinor_of_isDigraphMinor {H G : SurfaceDigraph S}
    (hMinor : IsDigraphMinor H G) :
    IsIsoMinor H.G.toGraph G.G.toGraph :=
  isIsoMinor_of_isBoundaryRootedMinor hMinor.2

/-! ## 4. Every finite planar graph is isomorphic to a minor of an even grid `≥ 6` -/

/-- **Graph Minors V, Section 2** (pages 94–95):
"For any planar graph $H$ there is an even value of $\theta \ge 6$ such that $H$ is isomorphic to a
minor of the $\theta$-grid. (This is easy to see, but for a proof see [1, 12].)"

Proved from Graph Minors VII, (9.6) (`GM07.theorem_9_6_proof`, reference [12]). -/
theorem exists_even_grid_minor_of_isPlanar {α : Type u} {β : Type v} {H : Graph α β}
    (hH : IsPlanar H) :
    ∃ θ : ℕ, 6 ≤ θ ∧ Even θ ∧ IsIsoMinor H (GM01.gridGraph θ) := by
  obtain ⟨_, _, S, tS, hS, hSph, ⟨Γ_H⟩⟩ := hH
  have : T2Space S := hS.2.1
  have : Nonempty S := by
    obtain ⟨e⟩ := hSph
    exact ⟨e.symm default⟩
  let H_dig : SurfaceDigraph S := toSurfaceDigraph Γ_H.drawing
  obtain ⟨N₀, hN₀⟩ := GM07.theorem_9_6_proof hS hSph H_dig
  let θ : ℕ := 2 * max 3 N₀
  have hθ6 : 6 ≤ θ := by dsimp [θ]; omega
  have hθ_even : Even θ := ⟨max 3 N₀, by dsimp [θ]; omega⟩
  have hN₀_le : N₀ ≤ θ := by dsimp [θ]; omega
  obtain ⟨G_draw, hGrid⟩ := GM07.exists_isGridDrawing hSph θ
  rcases hGrid with ⟨j, iso_G, hj, hV, hVertices, hEdges⟩
  have hGrid' : IsGridDrawing G_draw θ := ⟨j, iso_G, hj, hV, hVertices, hEdges⟩
  let G_dig : SurfaceDigraph S := toSurfaceDigraph G_draw
  have hDigMinor : IsDigraphMinor H_dig G_dig := hN₀ θ G_dig hN₀_le hGrid'
  have hDrawMinor : IsIsoMinor Γ_H.drawing.toGraph G_draw.toGraph :=
    isIsoMinor_of_isDigraphMinor hDigMinor
  exact ⟨θ, hθ6, hθ_even, (Iso.isIsoMinor_congr Γ_H.iso iso_G).mpr hDrawMinor⟩

/-- Every planar graph (`IsPlanar H`) is isomorphic to a minor of an even `θ × θ`-grid with
`θ ≥ 6`. -/
theorem _root_.GraphMinor.IsPlanar.exists_even_grid_minor {α : Type u} {β : Type v}
    {H : Graph α β} (hH : IsPlanar H) :
    ∃ θ : ℕ, 6 ≤ θ ∧ Even θ ∧ IsIsoMinor H (GM01.gridGraph θ) :=
  exists_even_grid_minor_of_isPlanar hH

end GraphMinor.Planar
