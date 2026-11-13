module

public import GraphMinor.GM22.Section8To13d2

import GraphMinor.GM22.GM21Proved

/-!
# Deriving Graph Minors XIII, Theorem (10.2) from Graph Minors XXII, Theorem (8.3)

This file formalizes the final paragraph of *Graph Minors XXII: Irrelevant vertices in linkage
problems* (Robertson and Seymour, page 563):

"Finally, a few words on deriving Theorem 10.2 of [5] from 8.3. In the language of [5] we have a
wall with an $h$-homogeneous subwall of height $\theta$ ($\theta$ replaces the $f(h)$ of [5]).
Take $\Gamma$ to be the original wall, and let $C_0$ be its perimeter. This wall has height at
least $\theta$ since it has a subwall of height $\theta$, and hence it contains the
$\theta \times \theta$ grid as a minor, and from theorems 6.1 and 7.3 of [3] it therefore has a
tangle $\mathcal{T}$ of order $\theta$. Let $\Pi$ be the set of corners of $\Gamma$, and let
$\mathcal{A}$ be the set of graphs called $\tilde{A}$ in the final section of [5]. Let
$\pi(A) + \omega$ be the “attachment sequence” of $A$ in the language of [5]. Let $D$ be the
closed disc with boundary the perimeter of the $h$-homogeneous subwall including the “infinite”
region of $\Gamma$. Then hypotheses (i)–(xiv) all are satisfied (for (xiii), we use that the
subwall is $h$-homogeneous). Consequently, Theorem 10.2 of [5] is true."

Each sentence of the paragraph is formalized as one or more lemmas below, culminating in
`gm13_theorem_10_2 : GM21Theorem11Statement.{u, v} → GM13.GM13Theorem102Statement.{u, v}`.
-/

@[expose] public section

namespace GraphMinor
namespace GM22

open Set Function Topology Graph Hypergraph
open GraphMinor.Surface
open GraphMinor.GM06
open GraphMinor.GM09
open GraphMinor.GM11
open GraphMinor.GM13
open GraphMinor.GM14

universe u v

/-! ## Sentence 1: Subwall Height Parameter

“In the language of [5] we have a wall with an $h$-homogeneous subwall of height $\theta$
($\theta$ replaces the $f(h)$ of [5]).” -/

/-- Given `q δ h : ℕ` with `2 ≤ h` and `Even h`, applying `theorem_8_3_in_graph` with distance
parameter `8 * h + 2` yields `θ : ℕ` and an even subwall height `f_h := max h (2 * (4 * θ + 15))`
satisfying `h ≤ f_h`, `Even f_h`, `4 ≤ f_h`, `θ ≤ f_h`, and `2 * (4 * θ + 15) ≤ f_h`
(Graph Minors XXII, Section 8, page 563). -/
theorem sentence_1_subwall_height_param
    (q δ h : ℕ) (hh2 : 2 ≤ h) (hh_even : Even h) :
    ∃ (θ f_h : ℕ),
      h ≤ f_h ∧ Even f_h ∧ 4 ≤ f_h ∧ θ ≤ f_h ∧ 2 * (4 * θ + 15) ≤ f_h ∧
      (∀ {S : Type} [TopologicalSpace S] [T2Space S]
        {α : Type u} {β : Type v} [Nonempty α] [Nonempty β]
        (R_G : RootedDigraph α β q) (W : Set α)
        (K : Graph α β) (Γ_draw : GraphDrawing K S)
        (C₀ : Drawing S) (r₀ : Set S) (orient : GM19.SurfaceOrientation S)
        (PiSet : Set S)
        (ord : ℕ) (T : Set (Hypergraph S (Set S) × Hypergraph S (Set S)))
        (d : Set S → Set S → ℕ)
        (J : Graph α β) (Z : Set α) (𝒜 : Set (Graph α β))
        (πLen : Graph α β → ℕ) (πA : ∀ A : Graph α β, Fin (πLen A) → α)
        (vA : Graph α β → S) (D_disc : Set S) (v_star : S)
        (h83 : Hypotheses83InGraph q δ (8 * h + 2) θ R_G W K Γ_draw C₀ r₀ orient PiSet ord T d
          J Z 𝒜 πLen πA vA D_disc v_star),
        HasSameDeltaFolio
          (subRootedDigraph R_G.G
            (R_G.G.toGraph.deleteVerts {drawingVertToGraph Γ_draw v_star})
            Graph.deleteVerts_le R_G.roots h83.roots_mem_deleteVerts_v_star)
          R_G δ) := by
  obtain ⟨θ, _, h4θ, hθ_spec⟩ := theorem_8_3_in_graph.{u, v} q δ (8 * h + 2)
  let f_h := max h (2 * (4 * θ + 15))
  have hf_even : Even f_h := by
    dsimp [f_h]
    rcases le_total h (2 * (4 * θ + 15)) with hle | hle
    · rw [max_eq_right hle]
      exact even_two_mul (4 * θ + 15)
    · rw [max_eq_left hle]
      exact hh_even
  refine ⟨θ, f_h, le_max_left _ _, hf_even, ?_, ?_, le_max_right _ _, hθ_spec⟩
  · have : 2 * (4 * θ + 15) ≤ f_h := le_max_right _ _
    omega
  · have : 2 * (4 * θ + 15) ≤ f_h := le_max_right _ _
    omega

/-! ## Sentence 2: Wall Drawing and Perimeter Circuit

“Take $\Gamma$ to be the original wall, and let $C_0$ be its perimeter.” -/

/-- Any wall `H : Wall α β` can be promoted to a Figure 1 drawn wall `W : DrawnWall α β` with
`W.toWall = H` and a 2-cell sphere drawing `Γ : GraphDrawing W.graph (OnePoint EuclideanPlane)`
satisfying Hypothesis (i) of Theorem (8.3), together with an outer region `r₀` and perimeter
circuit `C₀` satisfying Hypothesis (ii) of Theorem (8.3) and
`drawingVertToGraph Γ '' C₀.V = V(W.perimeter)` (Graph Minors XXII, Section 8, page 563). -/
theorem sentence_2_wall_drawing_and_perimeter {α : Type u} {β : Type v} [Nonempty α] [Nonempty β]
    (H : Wall α β) :
    ∃ (W : DrawnWall α β) (_ : W.toWall = H)
      (φ : EuclideanPlane ≃ₜ EuclideanPlane) (pos : α → ℝ × ℝ)
      (Γ : GraphDrawing W.graph (OnePoint EuclideanPlane))
      (C₀ : Drawing (OnePoint EuclideanPlane)),
      let E₀ := fig1Sph φ '' fig1EnclosedSet W.height
      let r₀ := interior (closure E₀ᶜ)
      (∀ v ∈ V(W.graph), pos v ∈ fig1Set W.height) ∧
      InjOn pos V(W.graph) ∧
      (∀ (p : ℕ × ℕ) (hp : p ∈ elementaryWallVerts W.height),
        pos (W.branchVertex p hp) = GM16.latticePoint p) ∧
      (∀ u ∈ V(W.graph), ∀ v ∈ V(W.graph), W.dist u v =
        planeWallDist (fig1PlaneEquiv '' cellSet (fig1WallCells W.height))
          (fig1PlaneEquiv (pos u)) (fig1PlaneEquiv (pos v))) ∧
      Γ.drawing.U = fig1Sph φ '' fig1Set W.height ∧
      (∀ x : V(W.graph), (Γ.iso.vertexEquiv x).1 = fig1Sph φ (pos x.1)) ∧
      (∀ (p q : ℕ × ℕ) (hadj : elementaryWallAdj W.height p q) (f : β) (hf : f ∈ E(W.graph)),
        f ∈ E(W.subdivisionPaths (W.baseEdge hadj)) →
          (Γ.iso.edgeEquiv ⟨f, hf⟩).1 ⊆ fig1Sph φ '' fig1Segment p q) ∧
      Γ.drawing.IsTwoCell ∧
      (IsSphere (OnePoint EuclideanPlane) ∧
        IsSubdivisionOfSimpleThreeConnected Γ.drawing.toGraph) ∧
      (C₀.IsSubdrawing Γ.drawing ∧ C₀.IsCircuit ∧ r₀ ∈ Γ.drawing.R ∧ subBd r₀ = C₀.U) ∧
      C₀.U = discBd E₀ ∧
      (∀ v ∈ V(W.graph), fig1Sph φ (pos v) ∈ C₀.V ↔ v ∈ V(W.perimeter)) ∧
      drawingVertToGraph Γ '' C₀.V = V(W.perimeter) := by
  obtain ⟨W, hW_toWall, hW_fig1⟩ := H.exists_drawnWall_isFigure1
  obtain ⟨φ, pos, Γ, hpos, hinj, hpos_branch, hdist, hΓU, hΓv, hΓe, h2cell⟩ :=
    exists_fig1Coords_full hW_fig1
  obtain ⟨C₀, hhyp_ii, hC₀_U, _, hmem_V, _, hC₀_draw⟩ :=
    exists_outer_region_and_perimeter_circuit hpos hinj hpos_branch hΓU hΓv hΓe
  refine ⟨W, hW_toWall, φ, pos, Γ, C₀, hpos, hinj, hpos_branch, hdist, hΓU, hΓv, hΓe, h2cell,
    ⟨⟨Homeomorph.refl _⟩,
      isSubdivision_of_iso_het
        (isSubdivisionOfSimpleThreeConnected_wall W.toWall) Γ.iso⟩,
    hhyp_ii, hC₀_U, hmem_V, hC₀_draw⟩

/-! ## Sentence 3: Wall Height and Respectful Tangle

“This wall has height at least $\theta$ since it has a subwall of height $\theta$, and hence it
contains the $\theta \times \theta$ grid as a minor, and from theorems 6.1 and 7.3 of [3] it
therefore has a tangle $\mathcal{T}$ of order $\theta$.” -/

/-- Since `W.toWall = H` has a subwall `H'` of height `f_h` with `4 ≤ f_h` and `θ ≤ f_h`, `W` has
height at least `max 4 θ` and its sphere drawing `Γ` admits a respectful tangle `T` of order
`W.height ≥ θ` with tangle metric `d` satisfying Hypothesis (iv) of Theorem (8.3)
(Graph Minors XXII, Section 8, page 563). -/
theorem sentence_3_wall_tangle {α : Type u} {β : Type v} [Nonempty α] [Nonempty β]
    {W : DrawnWall α β} {H' : Wall α β} (hsub : H'.IsSubwallOf W.toWall)
    {θ f_h : ℕ} (hf_height : H'.height = f_h) (h4_f : 4 ≤ f_h) (hθ_f : θ ≤ f_h)
    {φ : EuclideanPlane ≃ₜ EuclideanPlane} {pos : α → ℝ × ℝ}
    {Γ : GraphDrawing W.graph (OnePoint EuclideanPlane)}
    (hinj : InjOn pos V(W.graph))
    (hΓv : ∀ x : V(W.graph), (Γ.iso.vertexEquiv x).1 = fig1Sph φ (pos x.1))
    (h2cell : Γ.drawing.IsTwoCell) :
    ∃ (T : Set (Hypergraph (OnePoint EuclideanPlane) (Set (OnePoint EuclideanPlane)) ×
        Hypergraph (OnePoint EuclideanPlane) (Set (OnePoint EuclideanPlane))))
      (d : Set (OnePoint EuclideanPlane) → Set (OnePoint EuclideanPlane) → ℕ),
      (θ ≤ W.height ∧ HasTangleMetric Γ.drawing W.height T d ∧
        ∀ A B, (A, B) ∈ T → separationOrder A B ≤ 3 →
          ¬ (wallPiSet W.toWall φ pos ⊆ A.vertexSet)) ∧
      (∀ A B, (A, B) ∈ T → ∀ j : Fin W.height,
        ∃ e ∈ E(GM16.sphereWallRow W.height j), ∃ (f : β) (hf : f ∈ E(W.graph)),
          f ∈ E(W.subdivisionPaths (W.sphereEdge e)) ∧
            (Γ.iso.edgeEquiv ⟨f, hf⟩).1 ∉ A.edgeSet) := by
  have hh' : H'.height ≤ W.height := hsub.1
  have hθ_W : θ ≤ W.height := by omega
  have h4_W : 4 ≤ W.height := by omega
  exact exists_wall_tangle_for_8_3 hθ_W h4_W hinj hΓv h2cell

/-! ## Sentence 4: Corners and $\tilde{A}$-Division of $J$

“Let $\Pi$ be the set of corners of $\Gamma$, and let $\mathcal{A}$ be the set of graphs called
$\tilde{A}$ in the final section of [5].” -/

/-- Graph-level version of `compass_induce_eq_J` for a `GraphDrawing W.graph S` with
`W.toWall = H` and `drawingVertToGraph Γ '' C₀.V = V(W.perimeter)`. -/
theorem compass_induce_eq_J_in_graph {S : Type*} [TopologicalSpace S]
    {α : Type u} {β : Type v} [Nonempty α]
    {G : GM13.Digraph α β} {q : ℕ} {X : Set α} {H : Wall α β}
    {S_H : Society α β} {𝒜 : Set (Graph α β)}
    (hc : HypothesisC G q X H S_H 𝒜)
    {W : DrawnWall α β} (hW_toWall : W.toWall = H)
    {Γ : GraphDrawing W.graph S} {C₀ : Drawing S}
    (hC₀V : drawingVertToGraph Γ '' C₀.V = V(W.perimeter)) :
    let J := G.toGraph.induce (X ∪ V(S_H.G))
    J ≤ G.toGraph ∧
    J = G.toGraph.induce
      (X ∪ V(W.graph) ∪
        ⋃ C ∈ {C ∈ graphComponents
          (G.toGraph.deleteVerts ((drawingVertToGraph Γ '' C₀.V) ∪ X)) |
          (V(C) ∩ V(W.graph)).Nonempty}, V(C)) := by
  subst hW_toWall
  intro J
  have hGX : (G.deleteVertices X).toGraph = G.toGraph.deleteVerts X :=
    gm13_deleteVertices_toGraph_eq G X
  have hH_GX : W.toWall.graph ≤ G.toGraph.deleteVerts X := hGX ▸ hc.wall_in
  have hSH_G : S_H.G = wallCompass (G.toGraph.deleteVerts X) W.toWall :=
    hc.isWallSociety.1.trans (by rw [hGX])
  have hV_SH : V(S_H.G) = wallCompassVerts (G.toGraph.deleteVerts X) W.toWall := by
    rw [hSH_G]; exact vertexSet_wallCompass hH_GX
  have hSH_sub : V(S_H.G) ⊆ V(G.toGraph.deleteVerts X) := by
    rw [hV_SH]; exact wallCompassVerts_subset_vertexSet hH_GX
  have hSH_sub_G : V(S_H.G) ⊆ V(G.toGraph) :=
    hSH_sub.trans Graph.deleteVerts_le.vertexSet_mono
  have hJ_le : J ≤ G.toGraph :=
    G.toGraph.induce_le (union_subset hc.X_subset hSH_sub_G)
  refine ⟨hJ_le, ?_⟩
  dsimp only [J]
  congr 1
  rw [hC₀V, hV_SH]
  let G₀ := G.toGraph.deleteVerts (V(W.toWall.perimeter) ∪ X)
  have hG₀_eq : deleteVertices (G.toGraph.deleteVerts X) V(W.toWall.perimeter) = G₀ := by
    refine Graph.ext ?_ fun e x y => ?_
    · ext v
      simp only [G₀, vertexSet_deleteVertices, Graph.vertexSet_deleteVerts, mem_sdiff, mem_union]
      tauto
    · simp only [G₀, deleteVertices_isLink, Graph.deleteVerts_isLink, mem_union]
      tauto
  ext v
  simp only [mem_union, mem_iUnion, exists_prop]
  constructor
  · rintro (hvX | hvS)
    · exact Or.inl (Or.inl hvX)
    · rcases hvS with hvP | ⟨⟨hvGX, hvP⟩, u, hu_in, ⟨W_walk⟩⟩
      · exact Or.inl (Or.inr (W.toWall.perimeter_vertexSet_subset hvP))
      · right
        rw [hG₀_eq] at W_walk
        have hu_G₀ : u ∈ V(G₀) := W_walk.mem_vertexSet_of_mem_support W_walk.start_mem_support
        have hv_G₀ : v ∈ V(G₀) := W_walk.mem_vertexSet_of_mem_support W_walk.end_mem_support
        have hv_comp : v ∈ V(GM09.reachableComponent G₀ u) := by
          rw [GM09.vertexSet_reachableComponent]
          exact ⟨hv_G₀, ⟨W_walk⟩⟩
        have hu_comp : u ∈ V(GM09.reachableComponent G₀ u) := GM09.self_mem_reachableComponent hu_G₀
        refine ⟨GM09.reachableComponent G₀ u, ⟨GM09.isGraphComponent_reachableComponent hu_G₀, ?_⟩,
          hv_comp⟩
        exact ⟨u, ⟨hu_comp, W.toWall.insideVerts_subset hu_in⟩⟩
  · rintro ((hvX | hvH) | ⟨C, ⟨hC_comp, u, ⟨huC, huH⟩⟩, hvC⟩)
    · exact Or.inl hvX
    · have hmv := wall_vertexSet_subset_wallCompass hH_GX hvH
      rw [vertexSet_wallCompass hH_GX] at hmv
      exact Or.inr hmv
    · right
      have hu_G₀ : u ∈ V(G₀) := hC_comp.1.vertexSet_mono huC
      have hv_G₀ : v ∈ V(G₀) := hC_comp.1.vertexSet_mono hvC
      have hu_G₀' : u ∈ V(G.toGraph) \ (V(W.toWall.perimeter) ∪ X) :=
        G.toGraph.vertexSet_deleteVerts _ ▸ hu_G₀
      have hv_G₀' : v ∈ V(G.toGraph) \ (V(W.toWall.perimeter) ∪ X) :=
        G.toGraph.vertexSet_deleteVerts _ ▸ hv_G₀
      have hu_in : u ∈ W.toWall.insideVerts := ⟨huH, fun huP => hu_G₀'.2 (Or.inl huP)⟩
      obtain ⟨W_walk⟩ := hC_comp.2.1.2 u huC v hvC
      have W_G₀ : GraphWalk G₀ u v := W_walk.mono hC_comp.1
      rw [← hG₀_eq] at W_G₀
      have hv_GX : v ∈ V(G.toGraph.deleteVerts X) := by
        rw [Graph.vertexSet_deleteVerts]
        exact ⟨hv_G₀'.1, fun hvX => hv_G₀'.2 (Or.inr hvX)⟩
      exact Or.inr ⟨⟨hv_GX, fun hvP => hv_G₀'.2 (Or.inl hvP)⟩, u, hu_in, ⟨W_G₀⟩⟩

/-- Taking `PiSet := wallPiSet W.toWall φ pos`, `J := G.toGraph.induce (X ∪ V(S_H.G))`,
`Z := divTotalBoundary S_H 𝒜`, and `𝒜_83 := (fun A => (vis.tildeA A).toGraph) '' 𝒜`,
Hypotheses (iii), (v), (vi), (ix), and (x) of Theorem (8.3) all hold
(Graph Minors XXII, Section 8, page 563). -/
theorem sentence_4_corners_and_tildeA_division {α : Type u} {β : Type v} [Nonempty α]
    {G : GM13.Digraph α β} {q : ℕ} {X : Set α} {H : Wall α β}
    {S_H : Society α β} {𝒜 : Set (Graph α β)}
    (hc : HypothesisC G q X H S_H 𝒜) (vis : Vision G X H S_H 𝒜)
    {W : DrawnWall α β} (hW_toWall : W.toWall = H)
    {φ : EuclideanPlane ≃ₜ EuclideanPlane} {pos : α → ℝ × ℝ}
    {Γ : GraphDrawing W.graph (OnePoint EuclideanPlane)}
    {C₀ : Drawing (OnePoint EuclideanPlane)}
    (hinj : InjOn pos V(W.graph))
    (hpos_branch : ∀ (p : ℕ × ℕ) (hp : p ∈ elementaryWallVerts W.height),
      pos (W.branchVertex p hp) = GM16.latticePoint p)
    (hΓv : ∀ x : V(W.graph), (Γ.iso.vertexEquiv x).1 = fig1Sph φ (pos x.1))
    (hC₀_U : C₀.U = discBd (fig1Sph φ '' fig1EnclosedSet W.height))
    (hmem_V : ∀ v ∈ V(W.graph), fig1Sph φ (pos v) ∈ C₀.V ↔ v ∈ V(W.perimeter))
    (hC₀_draw : drawingVertToGraph Γ '' C₀.V = V(W.perimeter)) :
    let PiSet := wallPiSet W.toWall φ pos
    let J := G.toGraph.induce (X ∪ V(S_H.G))
    let Z := divTotalBoundary S_H 𝒜
    let 𝒜_83 := (fun A => (vis.tildeA A).toGraph) '' 𝒜
    (PiSet ⊆ C₀.V ∧ PiSet.ncard = 4) ∧
    (J ≤ G.toGraph ∧
      J = G.toGraph.induce
        (X ∪ V(W.graph) ∪
          ⋃ C ∈ {C ∈ graphComponents
            (G.toGraph.deleteVerts ((drawingVertToGraph Γ '' C₀.V) ∪ X)) |
            (V(C) ∩ V(W.graph)).Nonempty}, V(C))) ∧
    (Z ⊆ V(J) \ X ∧ drawingVertToGraph Γ '' PiSet ⊆ Z ∧
      IsZDivision J (Z ∪ X) 𝒜_83 ∧ ∀ A ∈ 𝒜_83, X ⊆ V(A)) ∧
    (∀ A ∈ 𝒜_83, ∀ u ∈ Z ∩ V(A), ∀ v ∈ Z ∩ V(A),
      ∃ P : Graph α β, IsGraphPathWithEnds (A.deleteVerts X) P u v ∧
        Disjoint (pathInternalVerts (A.deleteVerts X) P) (Z ∩ V(A))) ∧
    HasDiscDrawingWithBoundaryOrderInGraph (drawingVertToGraph Γ) C₀ PiSet Z 𝒜_83 := by
  intro PiSet J Z 𝒜_83
  subst hW_toWall
  obtain ⟨hPi_sub, hPi_card, _, hPi_draw⟩ := wallPiSet_props hinj hΓv hmem_V
  have hhyp_v := compass_induce_eq_J_in_graph hc rfl hC₀_draw
  obtain ⟨hZ_sub, hcorners_Z, hZdiv, hX_sub⟩ := tildeA_isZDivision hc vis
  have hPi_Z : drawingVertToGraph Γ '' PiSet ⊆ Z := by
    rw [hPi_draw]
    exact hcorners_Z
  have hhyp_ix := tildeA_hyp_ix hc vis
  have hhyp_x : HasDiscDrawingWithBoundaryOrderInGraph (drawingVertToGraph Γ) C₀ PiSet Z 𝒜_83 :=
    tildeA_hyp_x hc vis rfl hinj hpos_branch hΓv hC₀_U hmem_V
  exact ⟨⟨hPi_sub, hPi_card⟩, hhyp_v, ⟨hZ_sub, hPi_Z, hZdiv, hX_sub⟩, hhyp_ix, hhyp_x⟩

/-! ## Sentence 5: Attachment Sequences and Representative Vertices

“Let $\pi(A) + \omega$ be the “attachment sequence” of $A$ in the language of [5].” -/

/-- Taking `R_G := visionRootedDigraph hc vis`, `πLen := tildeA_πLen vis`,
`πA := tildeA_πA hc vis`, and `vA := tildeA_vA hc vis φ pos`, there exists a sphere orientation
`orient` such that `ordering_W` and Hypotheses (vii), (viii), and (xi) of Theorem (8.3) hold
(Graph Minors XXII, Section 8, page 563). -/
theorem sentence_5_attachment_sequences_and_vA {α : Type u} {β : Type v} [Nonempty α]
    {G : GM13.Digraph α β} {q : ℕ} {X : Set α} {H : Wall α β}
    {S_H : Society α β} {𝒜 : Set (Graph α β)}
    (hc : HypothesisC G q X H S_H 𝒜) (vis : Vision G X H S_H 𝒜)
    {W : DrawnWall α β} (hW_toWall : W.toWall = H)
    {φ : EuclideanPlane ≃ₜ EuclideanPlane} {pos : α → ℝ × ℝ}
    {Γ : GraphDrawing W.graph (OnePoint EuclideanPlane)}
    {C₀ : Drawing (OnePoint EuclideanPlane)}
    (hinj : InjOn pos V(W.graph))
    (hpos_branch : ∀ (p : ℕ × ℕ) (hp : p ∈ elementaryWallVerts W.height),
      pos (W.branchVertex p hp) = GM16.latticePoint p)
    (hΓv : ∀ x : V(W.graph), (Γ.iso.vertexEquiv x).1 = fig1Sph φ (pos x.1))
    (hC₀_U : C₀.U = discBd (fig1Sph φ '' fig1EnclosedSet W.height))
    (hmem_V : ∀ v ∈ V(W.graph), fig1Sph φ (pos v) ∈ C₀.V ↔ v ∈ V(W.perimeter)) :
    let R_G := visionRootedDigraph hc vis
    let E₀ := fig1Sph φ '' fig1EnclosedSet W.height
    let r₀ := interior (closure E₀ᶜ)
    let PiSet := wallPiSet W.toWall φ pos
    let J := G.toGraph.induce (X ∪ V(S_H.G))
    let Z := divTotalBoundary S_H 𝒜
    let 𝒜_83 := (fun A => (vis.tildeA A).toGraph) '' 𝒜
    let πLen := tildeA_πLen vis
    let πA := tildeA_πA hc vis
    let vA := tildeA_vA hc vis φ pos
    ∃ orient : GM19.SurfaceOrientation (OnePoint EuclideanPlane),
      (X ⊆ V(R_G.G.toGraph) ∧ IsOrderingOf X R_G.roots) ∧
      (∀ A ∈ 𝒜_83, πLen A ≤ 3 ∧ IsOrderingOf (Z ∩ V(A)) (πA A)) ∧
      (∀ A ∈ 𝒜_83,
        ∃ (P : Fin (πLen A) → Graph α β) (t : Fin (πLen A) → OnePoint EuclideanPlane),
          (∀ i : Fin (πLen A), t i ∈ PiSet ∧
            IsGraphPathWithEnds (J.deleteVerts X) (P i) (πA A i) (drawingVertToGraph Γ (t i))) ∧
          Pairwise (fun i j : Fin (πLen A) => Disjoint V(P i) V(P j)) ∧
          (∀ h3 : πLen A = 3,
            orient.pos (Set.univ \ r₀) (t ⟨0, by omega⟩) (t ⟨1, by omega⟩) (t ⟨2, by omega⟩))) ∧
      (∀ A ∈ 𝒜_83, vA A ∈ Γ.drawing.V ∧
        ∃ u ∈ Z ∩ V(A), ∃ P : Graph α β,
          IsGraphPathWithEnds (R_G.G.toGraph.deleteVerts X) P (drawingVertToGraph Γ (vA A)) u ∧
          V(P) ∩ V(W.graph) = {drawingVertToGraph Γ (vA A)}) := by
  intro R_G E₀ r₀ PiSet J Z 𝒜_83 πLen πA vA
  subst hW_toWall
  obtain ⟨hPi_sub, _, _, _⟩ := wallPiSet_props hinj hΓv hmem_V
  have hp_C₀ : ∀ k : Fin 4, fig1Sph φ (pos (W.toWall.corner k)) ∈ C₀.U :=
    fun k => C₀.V_subset_U (hPi_sub ⟨k, rfl⟩)
  obtain ⟨orient, horient⟩ := exists_sphere_orientation_for_wall hinj hpos_branch hC₀_U hp_C₀
  refine ⟨orient, ⟨hc.X_subset, isOrderingOf_visionXOrdering hc vis⟩,
    tildeA_hyp_vii hc vis,
    tildeA_hyp_viii hc vis rfl hinj hΓv hmem_V horient,
    tildeA_hyp_xi hc vis rfl hΓv⟩

/-! ## Sentence 6: Closed Disc $D$ of the $h$-Homogeneous Subwall

“Let $D$ be the closed disc with boundary the perimeter of the $h$-homogeneous subwall including
the “infinite” region of $\Gamma$.” -/

/-- For a subwall `H'` of `W.toWall` at shift `(i, j)` of height `f_h ≥ 2 * (4 * θ + 15)`, the
closed disc `D_disc := closure ((fig1Sph φ ∘ shiftHomeo i j) '' fig1EnclosedSet H'.height)ᶜ`
satisfies Hypothesis (xii) of Theorem (8.3) and, for both middle vertices
`u_star ∈ {H'.middleVertex₁, H'.middleVertex₂}`, `v_star := fig1Sph φ (pos u_star)` satisfies
Hypothesis (xiv) of Theorem (8.3) (Graph Minors XXII, Section 8, page 563). -/
theorem sentence_6_subwall_disc {α : Type u} {β : Type v} [Nonempty α] [Nonempty β]
    {W : DrawnWall α β}
    {φ : EuclideanPlane ≃ₜ EuclideanPlane} {pos : α → ℝ × ℝ}
    {Γ : GraphDrawing W.graph (OnePoint EuclideanPlane)}
    (hpos : ∀ v ∈ V(W.graph), pos v ∈ fig1Set W.height)
    (hinj : InjOn pos V(W.graph))
    (hpos_branch : ∀ (p : ℕ × ℕ) (hp : p ∈ elementaryWallVerts W.height),
      pos (W.branchVertex p hp) = GM16.latticePoint p)
    (hdist : ∀ u ∈ V(W.graph), ∀ v ∈ V(W.graph), W.dist u v =
      planeWallDist (fig1PlaneEquiv '' cellSet (fig1WallCells W.height))
        (fig1PlaneEquiv (pos u)) (fig1PlaneEquiv (pos v)))
    (hΓU : Γ.drawing.U = fig1Sph φ '' fig1Set W.height)
    (hΓv : ∀ x : V(W.graph), (Γ.iso.vertexEquiv x).1 = fig1Sph φ (pos x.1))
    (hΓe : ∀ (p q : ℕ × ℕ) (hadj : elementaryWallAdj W.height p q) (f : β) (hf : f ∈ E(W.graph)),
      f ∈ E(W.subdivisionPaths (W.baseEdge hadj)) →
        (Γ.iso.edgeEquiv ⟨f, hf⟩).1 ⊆ fig1Sph φ '' fig1Segment p q)
    {T : Set (Hypergraph (OnePoint EuclideanPlane) (Set (OnePoint EuclideanPlane)) ×
      Hypergraph (OnePoint EuclideanPlane) (Set (OnePoint EuclideanPlane)))}
    {d : Set (OnePoint EuclideanPlane) → Set (OnePoint EuclideanPlane) → ℕ}
    (hd : HasTangleMetric Γ.drawing W.height T d)
    (hrow : ∀ A B, (A, B) ∈ T → ∀ j : Fin W.height,
      ∃ e ∈ E(GM16.sphereWallRow W.height j), ∃ (f : β) (hf : f ∈ E(W.graph)),
        f ∈ E(W.subdivisionPaths (W.sphereEdge e)) ∧ (Γ.iso.edgeEquiv ⟨f, hf⟩).1 ∉ A.edgeSet)
    {H' : Wall α β} {i j θ : ℕ}
    (hh' : H'.height ≤ W.height) (hi_even : Even i) (hj_even : Even j)
    (hi : i ≤ 2 * W.height - 2 * H'.height) (hj : j ≤ W.height - H'.height)
    (hbranch : ∀ (p : ℕ × ℕ) (hp' : p ∈ elementaryWallVerts H'.height)
      (hp : wallShift i j p ∈ elementaryWallVerts W.height),
      H'.branchVertex p hp' = W.branchVertex (wallShift i j p) hp)
    (hpaths : H'.subdivisionPaths = W.subdivisionPaths)
    (hbase : H'.baseGraph = W.baseGraph.induce
      ((fun p : elementaryWallVerts W.height => (W.baseIso.vertexEquiv p).1) ''
        {p : elementaryWallVerts W.height |
          ∃ q ∈ elementaryWallVerts H'.height, p.1 = wallShift i j q}))
    (hθ_height : 2 * (4 * θ + 15) ≤ H'.height) :
    let E₀ := fig1Sph φ '' fig1EnclosedSet W.height
    let r₀ := interior (closure E₀ᶜ)
    let D_disc := closure ((fig1Sph φ ∘ shiftHomeo i j) '' fig1EnclosedSet H'.height)ᶜ
    (IsClosedDisc D_disc ∧ subBd D_disc ⊆ Γ.drawing.U ∧ r₀ ⊆ D_disc) ∧
    (∀ u_star : α, (u_star = H'.middleVertex₁ ∨ u_star = H'.middleVertex₂) →
      fig1Sph φ (pos u_star) ∈ Γ.drawing.V \ D_disc ∧
      θ ≤ subsetTangleDist Γ.drawing W.height d {fig1Sph φ (pos u_star)} D_disc) := by
  intro E₀ r₀ D_disc
  obtain ⟨hhyp_xii, _, _, hm₁_in, hm₂_in⟩ :=
    subwall_disc_props hinj hpos_branch hΓU hΓv hΓe hh' hi_even hj_even hi hj hbranch hpaths hbase
  refine ⟨hhyp_xii, fun u_star hu_star => ⟨?_, ?_⟩⟩
  · rcases hu_star with rfl | rfl
    · exact hm₁_in
    · exact hm₂_in
  · exact le_subsetTangleDist_middleVertex_subwall_disc hpos hpos_branch hdist hΓU hΓv hΓe
      hd hrow hh' hi_even hj_even hi hj hbranch hpaths hbase hθ_height hu_star

/-! ## Sentence 7: Verification of Hypotheses (i)–(xiv) of Theorem (8.3)

“Then hypotheses (i)–(xiv) all are satisfied (for (xiii), we use that the subwall is
$h$-homogeneous).” -/

/-- Under the hypotheses of `GM13Theorem102Statement`, for both middle vertices
`u_star ∈ {H'.middleVertex₁, H'.middleVertex₂}` of the `h`-homogeneous subwall `H'` of height
`f_h`, all hypotheses (i)–(xiv) of `Hypotheses83InGraph` are satisfied
(Graph Minors XXII, Section 8, page 563). -/
theorem sentence_7_hypotheses_8_3_satisfied {α : Type u} {β : Type v} [Nonempty α] [Nonempty β]
    {G : GM13.Digraph α β} {q δ h θ f_h : ℕ}
    (hh2 : 2 ≤ h) (hh_even : Even h)
    (hh_le_f : h ≤ f_h) (h4_f : 4 ≤ f_h) (hθ_f : θ ≤ f_h) (hθ_height : 2 * (4 * θ + 15) ≤ f_h)
    {X : Set α} {H H' : Wall α β} {S_H : Society α β} {𝒜 : Set (Graph α β)}
    (vis : Vision G X H S_H 𝒜)
    (hc : HypothesisC G q X H S_H 𝒜)
    (hhom : IsHomogeneousSubwall vis δ h H')
    (hf_height : H'.height = f_h) :
    ∃ (W : DrawnWall α β) (_ : W.toWall = H)
      (φ : EuclideanPlane ≃ₜ EuclideanPlane) (pos : α → ℝ × ℝ)
      (Γ : GraphDrawing W.graph (OnePoint EuclideanPlane))
      (C₀ : Drawing (OnePoint EuclideanPlane)) (r₀ : Set (OnePoint EuclideanPlane))
      (orient : GM19.SurfaceOrientation (OnePoint EuclideanPlane))
      (PiSet : Set (OnePoint EuclideanPlane))
      (T : Set (Hypergraph (OnePoint EuclideanPlane) (Set (OnePoint EuclideanPlane)) ×
        Hypergraph (OnePoint EuclideanPlane) (Set (OnePoint EuclideanPlane))))
      (d : Set (OnePoint EuclideanPlane) → Set (OnePoint EuclideanPlane) → ℕ)
      (D_disc : Set (OnePoint EuclideanPlane)),
      (∀ x : V(W.graph), (Γ.iso.vertexEquiv x).1 = fig1Sph φ (pos x.1)) ∧
      H'.graph ≤ W.graph ∧
      (∀ u_star : α, (u_star = H'.middleVertex₁ ∨ u_star = H'.middleVertex₂) →
        Hypotheses83InGraph q δ (8 * h + 2) θ
          (visionRootedDigraph hc vis) X W.graph Γ C₀ r₀ orient PiSet W.height T d
          (G.toGraph.induce (X ∪ V(S_H.G))) (divTotalBoundary S_H 𝒜)
          ((fun A => (vis.tildeA A).toGraph) '' 𝒜)
          (tildeA_πLen vis) (tildeA_πA hc vis) (tildeA_vA hc vis φ pos)
          D_disc (fig1Sph φ (pos u_star))) := by
  obtain ⟨W, hW_toWall, φ, pos, Γ, C₀, hpos, hinj, hpos_branch, hdist, hΓU, hΓv, hΓe, h2cell,
    hhyp_i, hhyp_ii, hC₀_U, hmem_V, hC₀_draw⟩ := sentence_2_wall_drawing_and_perimeter H
  have hsub_W : H'.IsSubwallOf W.toWall := hW_toWall.symm ▸ hhom.1
  obtain ⟨T, d, hhyp_iv, hrow⟩ :=
    sentence_3_wall_tangle hsub_W hf_height h4_f hθ_f hinj hΓv h2cell
  obtain ⟨hhyp_iii, hhyp_v, hhyp_vi, hhyp_ix, hhyp_x⟩ :=
    sentence_4_corners_and_tildeA_division hc vis hW_toWall hinj hpos_branch hΓv hC₀_U hmem_V hC₀_draw
  obtain ⟨orient, hord_W, hhyp_vii, hhyp_viii, hhyp_xi⟩ :=
    sentence_5_attachment_sequences_and_vA hc vis hW_toWall hinj hpos_branch hΓv hC₀_U hmem_V
  obtain ⟨hh', i, j, hi_even, hj_even, hi, hj, hbranch, hpaths, hbase⟩ := hsub_W
  have hle_sub : H'.graph ≤ W.graph :=
    subwall_graph_le ⟨hh', i, j, hi_even, hj_even, hi, hj, hbranch, hpaths, hbase⟩
  have hθ_height' : 2 * (4 * θ + 15) ≤ H'.height := hf_height.symm ▸ hθ_height
  have hh_le_H' : h ≤ H'.height := hf_height.symm ▸ hh_le_f
  have hd : HasTangleMetric Γ.drawing W.height T d := hhyp_iv.2.1
  obtain ⟨hhyp_xii, hhyp_xiv⟩ :=
    sentence_6_subwall_disc hpos hinj hpos_branch hdist hΓU hΓv hΓe hd hrow
      hh' hi_even hj_even hi hj hbranch hpaths hbase hθ_height'
  have hK_le : W.graph ≤ (visionRootedDigraph hc vis).G.toGraph.deleteVerts X := by
    change W.toWall.graph ≤ G.toGraph.deleteVerts X
    rw [hW_toWall, ← gm13_deleteVertices_toGraph_eq G X]
    exact hc.wall_in
  let E₀ := fig1Sph φ '' fig1EnclosedSet W.height
  let r₀ := interior (closure E₀ᶜ)
  let PiSet := wallPiSet W.toWall φ pos
  let D_disc := closure ((fig1Sph φ ∘ shiftHomeo i j) '' fig1EnclosedSet H'.height)ᶜ
  refine ⟨W, hW_toWall, φ, pos, Γ, C₀, r₀, orient, PiSet, T, d, D_disc, hΓv, hle_sub,
    fun u_star hu_star =>
      { finite_V := hc.isFinite.1
        finite_E := hc.isFinite.2
        ordering_W := hord_W
        K_le := hK_le
        hyp_i := hhyp_i
        hyp_ii := hhyp_ii
        hyp_iii := hhyp_iii
        hyp_iv := hhyp_iv
        hyp_v := hhyp_v
        hyp_vi := hhyp_vi
        hyp_vii := hhyp_vii
        hyp_viii := hhyp_viii
        hyp_ix := hhyp_ix
        hyp_x := hhyp_x
        hyp_xi := hhyp_xi
        hyp_xii := hhyp_xii
        hyp_xiii := fun tA htA hvA v hv => Or.inr (by
          obtain ⟨tA', htA', hdist_le, hlen, hfolio⟩ :=
            tildeA_hyp_xiii hh2 hh_even hc vis hW_toWall hinj hpos_branch hΓU hΓv hΓe hd
              hh_le_H' hh' hi_even hj_even hi hj hbranch hpaths hbase hhom
              tA htA hvA v hv
              ((hhyp_vi.2.2.1.2.1 tA htA).trans hhyp_v.1)
              (seqConcat_mem
                (fun k => ((hhyp_vii tA htA).2.2.subset ⟨k, rfl⟩).2)
                (fun k => hhyp_vi.2.2.2 tA htA (hord_W.2.2.subset ⟨k, rfl⟩)))
          exact ⟨tA', htA', hdist_le, hlen, hfolio _ _⟩)
        hyp_xiv := hhyp_xiv u_star hu_star }⟩

/-! ## Sentence 8: Proof of Graph Minors XIII, Theorem (10.2)

“Consequently, Theorem 10.2 of [5] is true.” -/

/-- **Graph Minors XIII, Theorem (10.2)** (derived from Graph Minors XXII, Theorem (8.3),
Section 8, page 563):
For any $q$, $\delta \ge 0$ and $h \ge 2$, even, there exists $f(h) \ge h$, even, such that under
Hypothesis C, if $H' \subseteq H$ is an $h$-homogeneous subwall of height $f(h)$ then both middle
vertices of $H'$ are irrelevant to the $\delta$-folio of $G$ relative to $X$. -/
theorem gm13_theorem_10_2 (h11 : GM21Theorem11Statement.{u, v}) :
    GM13.GM13Theorem102Statement.{u, v} := by
  intro q δ h hh2 hh_even
  obtain ⟨θ, f_h, hh_le_f, hf_even, h4_f, hθ_f, hθ_height, h83_spec⟩ :=
    sentence_1_subwall_height_param.{u, v} q δ h hh2 hh_even
  refine ⟨f_h, hh_le_f, hf_even, ?_⟩
  intro α β G X H H' S_H 𝒜 vis hc hhom hf_height
  have hαβ := H.nonempty_types
  have : Nonempty α := hαβ.1
  have : Nonempty β := hαβ.2
  obtain ⟨W, hW_toWall, φ, pos, Γ, C₀, r₀, orient, PiSet, T, d, D_disc, hΓv, hle_sub, h83_of⟩ :=
    sentence_7_hypotheses_8_3_satisfied hh2 hh_even hh_le_f h4_f hθ_f hθ_height vis hc hhom hf_height
  have hGX : (G.deleteVertices X).toGraph = G.toGraph.deleteVerts X :=
    gm13_deleteVertices_toGraph_eq G X
  have hW_GX : W.graph ≤ G.toGraph.deleteVerts X := by
    rw [← hW_toWall] at hc
    rw [← hGX]
    exact hc.wall_in
  have hirrel : ∀ u_star : α, (u_star = H'.middleVertex₁ ∨ u_star = H'.middleVertex₂) →
      IsIrrelevantVertex G δ X u_star := by
    intro u_star hu_star
    have hu_H' : u_star ∈ V(H'.graph) := by
      rcases hu_star with rfl | rfl <;> exact H'.branchVertex_mem_graph _ _
    have hu_W : u_star ∈ V(W.graph) := hle_sub.vertexSet_mono hu_H'
    have hu_del : u_star ∈ V(G.toGraph) \ X :=
      G.toGraph.vertexSet_deleteVerts X ▸ hW_GX.vertexSet_mono hu_W
    let v_star := fig1Sph φ (pos u_star)
    have hdraw_eq : drawingVertToGraph Γ v_star = u_star := by
      have h1 := drawingVertToGraph_apply_vertexEquiv Γ ⟨u_star, hu_W⟩
      rwa [hΓv ⟨u_star, hu_W⟩] at h1
    have h83 := h83_of u_star hu_star
    have hfolio :
        HasSameDeltaFolio
          (subRootedDigraph (visionRootedDigraph hc vis).G
            ((visionRootedDigraph hc vis).G.toGraph.deleteVerts {drawingVertToGraph Γ v_star})
            Graph.deleteVerts_le (visionRootedDigraph hc vis).roots
            h83.roots_mem_deleteVerts_v_star)
          (visionRootedDigraph hc vis) δ :=
      h83_spec (visionRootedDigraph hc vis) X W.graph Γ C₀ r₀ orient PiSet
        W.height T d (G.toGraph.induce (X ∪ V(S_H.G))) (divTotalBoundary S_H 𝒜)
        ((fun A => (vis.tildeA A).toGraph) '' 𝒜)
        (tildeA_πLen vis) (tildeA_πA hc vis) (tildeA_vA hc vis φ pos) D_disc v_star h83
    have hroots_del : ∀ i : Fin q,
        visionXOrdering hc vis i ∈ V(G.toGraph.deleteVerts {u_star}) := by
      intro i
      rw [← hdraw_eq]
      exact h83.roots_mem_deleteVerts_v_star i
    have hfolio' :
        HasSameDeltaFolio
          (subRootedDigraph (toGM22Digraph G) (G.toGraph.deleteVerts {u_star})
            Graph.deleteVerts_le (visionXOrdering hc vis) hroots_del)
          (visionRootedDigraph hc vis) δ := by
      intro αH βH R_H hDet
      have hsub_eq :
          subRootedDigraph (toGM22Digraph G) (G.toGraph.deleteVerts {u_star})
            Graph.deleteVerts_le (visionXOrdering hc vis) hroots_del =
          subRootedDigraph (visionRootedDigraph hc vis).G
            ((visionRootedDigraph hc vis).G.toGraph.deleteVerts {drawingVertToGraph Γ v_star})
            Graph.deleteVerts_le (visionRootedDigraph hc vis).roots
            h83.roots_mem_deleteVerts_v_star := by
        simp only [visionRootedDigraph, toGM22RootedDigraph, toGM22Digraph, subRootedDigraph,
          Digraph.ofSubgraph, hdraw_eq]
      rw [hsub_eq]
      exact hfolio R_H hDet
    exact isIrrelevantVertex_of_gm22_hasSameDeltaFolio hc.X_subset
      (isOrderingOf_visionXOrdering hc vis) hu_del.1 hu_del.2
      (visionXOrdering_mem_vertexSet hc vis) hroots_del hfolio'
  exact ⟨hirrel H'.middleVertex₁ (Or.inl rfl), hirrel H'.middleVertex₂ (Or.inr rfl)⟩

end GM22
end GraphMinor
