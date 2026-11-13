module

public import GraphMinor.GM13.Section7WallModel
public import GraphMinor.GM13.Section7Figure2
public import GraphMinor.GM16.Section4Wall
public import GraphMinor.GM15.Defs
public import GraphMinor.GM16.Section4Claim1
import GraphMinor.GM13.Section7a
import GraphMinor.GM09.Basic
import GraphMinor.GM16.ModelInducedTangle
import GraphMinor.GM16.Section4WallTangle
import GraphMinor.GM16.Section4WallRowImages
import GraphMinor.GM16.InducedTangleEdgePatterns
import GraphMinor.GM16.GraphDrawingSpanEmbedding
import GraphMinor.GM16.GraphDrawingForwardMaps
import GraphMinor.GM16.ControlFromInducedTangle
import GraphMinor.GM16.GraphIsoImage
import GraphMinor.GM16.HypergraphSupportedTangle
import GraphMinor.GM16.DrawingSkeletonPaths

/-!
# The wall of XVI (4.2) inside a wall of Graph Minors XIII

The proof of (7.4) (Graph Minors XIII, page 90) takes for `𝒯` "the set of all separations $(A, B)$
of $H$ of order $< r$ such that $A$ contains no horizontal path of $H$". The library has this
tangle for the wall `sphereWallGraph θ` of XVI (4.2) (`GM16.sphereWallTangle`). This file puts
that wall inside a wall `W` of height `h` of Graph Minors XIII, as a minor:

- the vertex `(x, y)` of `sphereWallGraph h` goes to the branch vertex `(x + 1, y)` of `W`, so
  the rows of `sphereWallGraph h` are the rows `0, …, h - 1` of `W` without their first vertex;
- the model is built from the subdivision paths of `W` by `exists_isMinorModel_of_paths`.
-/

public section

namespace GraphMinor.GM13

open Set Function
open Graph
open GraphMinor
open GraphMinor.GM09
open GraphMinor.Surface GraphMinor.GM10

universe u v

variable {α : Type u} {β : Type v}

/-- The coordinates in the elementary wall of height `h` of the vertex `(x, y)` of
`GM16.sphereWallGraph h`. -/
@[expose] def sphereToWall {h : ℕ} (a : Fin (2 * h + 1) × Fin h) : ℕ × ℕ := (a.1.val + 1, a.2.val)

theorem sphereToWall_injective (h : ℕ) : Injective (sphereToWall (h := h)) := by
  intro a b hab
  simp only [sphereToWall, Prod.mk.injEq] at hab
  exact Prod.ext (Fin.ext (by omega)) (Fin.ext hab.2)

theorem sphereToWall_mem (h : ℕ) (a : Fin (2 * h + 1) × Fin h) :
    sphereToWall a ∈ elementaryWallVerts h := by
  have h1 := a.1.isLt
  have h2 := a.2.isLt
  simp only [sphereToWall, elementaryWallVerts, mem_setOf_eq, ne_eq, Prod.mk.injEq]
  omega

theorem sphereToWall_adj {h : ℕ} {a b : Fin (2 * h + 1) × Fin h}
    (hab : (GM16.sphereWallSimpleGraph h).Adj a b) :
    elementaryWallAdj h (sphereToWall a) (sphereToWall b) := by
  refine ⟨sphereToWall_mem h a, sphereToWall_mem h b, ?_⟩
  simp only [GM16.sphereWallSimpleGraph] at hab
  simp only [sphereToWall]
  rcases hab with ⟨h2, h1⟩ | ⟨h1, h2⟩
  · left
    exact ⟨congrArg Fin.val h2, by omega⟩
  · right
    refine ⟨by rw [h1], ?_⟩
    rcases h2 with ⟨h3, h4⟩ | ⟨h3, h4⟩
    · left
      refine ⟨h3, ?_⟩
      obtain ⟨k, hk⟩ := h4
      exact ⟨k, by omega⟩
    · right
      refine ⟨h3, ?_⟩
      obtain ⟨k, hk⟩ := h4
      exact ⟨k, by omega⟩

/-- The vertex set of a wall is finite. -/
theorem Wall.vertexSet_finite (W : Wall α β) : V(W.graph).Finite := by
  rw [W.vertexSet_eq]
  have hV : V(W.baseGraph).Finite := by
    have : Finite V(elementaryWall W.height) := (elementaryWall_finite_V _).to_subtype
    have : Finite V(W.baseGraph) := Finite.of_equiv _ W.baseIso.vertexEquiv
    exact Set.toFinite _
  have hE : E(W.baseGraph).Finite := by
    have : Finite E(elementaryWall W.height) := (elementaryWall_finite_E _).to_subtype
    have : Finite E(W.baseGraph) := Finite.of_equiv _ W.baseIso.edgeEquiv
    exact Set.toFinite _
  refine hV.union (hE.biUnion fun e he => ?_)
  obtain ⟨x, y, -, hP, -⟩ := W.path_of_edge e he
  exact hP.vertexSet_finite

/-- The edge set of a wall is finite. -/
theorem Wall.edgeSet_finite (W : Wall α β) : E(W.graph).Finite := by
  rw [W.edgeSet_eq]
  have hE : E(W.baseGraph).Finite := by
    have : Finite E(elementaryWall W.height) := (elementaryWall_finite_E _).to_subtype
    have : Finite E(W.baseGraph) := Finite.of_equiv _ W.baseIso.edgeEquiv
    exact Set.toFinite _
  refine hE.biUnion fun e he => ?_
  obtain ⟨x, y, -, hP, -⟩ := W.path_of_edge e he
  exact hP.edgeSet_finite

/-- The edge of the base graph of `W` named by an edge of `GM16.sphereWallGraph` (an arbitrary
edge when the pair is not an edge). -/
noncomputable def Wall.sphereEdge (W : Wall α β) [Nonempty β]
    (e : Sym2 (Fin (2 * W.height + 1) × Fin W.height)) : β :=
  open Classical in
  if hE : Sym2.map sphereToWall e ∈ E(elementaryWall W.height) then
    (W.baseIso.edgeEquiv ⟨Sym2.map sphereToWall e, hE⟩).1
  else Classical.arbitrary β

theorem Wall.sphereEdge_mk (W : Wall α β) [Nonempty β]
    {a b : Fin (2 * W.height + 1) × Fin W.height}
    (hab : elementaryWallAdj W.height (sphereToWall a) (sphereToWall b)) :
    W.sphereEdge s(a, b) = W.baseEdge hab := by
  have hE : Sym2.map sphereToWall s(a, b) ∈ E(elementaryWall W.height) :=
    ⟨_, _, hab, by simp⟩
  rw [Wall.sphereEdge, dite_cond_eq_true (eq_true hE)]
  rfl

/-- **The wall of XVI (4.2) is a minor of a wall of height `h`.** A wall `W` of height `h` has a
minor model of `GM16.sphereWallGraph h` whose model edge of the edge `ab` is an edge of the
subdivision path of the edge from `(a.1 + 1, a.2)` to `(b.1 + 1, b.2)` of the elementary wall. -/
theorem Wall.exists_sphereWall_model (W : Wall α β) [Nonempty β] :
    ∃ (ηv : Fin (2 * W.height + 1) × Fin W.height → Set α)
      (ηe : Sym2 (Fin (2 * W.height + 1) × Fin W.height) → β),
      IsMinorModel (GM16.sphereWallGraph W.height) W.graph ηv ηe ∧
      ∀ e ∈ (GM16.sphereWallSimpleGraph W.height).edgeSet,
        ηe e ∈ E(W.subdivisionPaths (W.sphereEdge e)) := by
  classical
  let c : Fin (2 * W.height + 1) × Fin W.height → α := fun a =>
    W.branchVertex (sphereToWall a) (sphereToWall_mem _ a)
  have hc : Injective c := fun a b hab =>
    sphereToWall_injective _ (W.branchVertex_injective _ _ hab)
  have hrange : range c ⊆ V(W.baseGraph) := by
    rintro _ ⟨a, rfl⟩
    exact W.branchVertex_mem_baseGraph _ _
  let P : Sym2 (Fin (2 * W.height + 1) × Fin W.height) → Graph α β :=
    fun e => W.subdivisionPaths (W.sphereEdge e)
  have hPmk : ∀ a b (hab : (GM16.sphereWallSimpleGraph W.height).Adj a b),
      P s(a, b) = W.subdivisionPaths (W.baseEdge (sphereToWall_adj hab)) := by
    intro a b hab
    simp only [P, W.sphereEdge_mk (sphereToWall_adj hab)]
  have hInter : ∀ a b (hab : (GM16.sphereWallSimpleGraph W.height).Adj a b),
      V(P s(a, b)) ∩ V(W.baseGraph) = {c a, c b} := by
    intro a b hab
    rw [hPmk a b hab, W.vertexSet_baseEdge_inter]
  obtain ⟨ηv, ηe, hmodel, hηe⟩ := exists_isMinorModel_of_paths
    (S := GM16.sphereWallSimpleGraph W.height) (G := W.graph)
    (fun a => (Fintype.equivFin _ a : ℕ))
    (fun a b h => (Fintype.equivFin _).injective (Fin.ext h)) c hc
    (fun a => W.branchVertex_mem_graph _ _) P
    (fun a b hab => by rw [hPmk a b hab]; exact W.isGraphPathWithEnds_baseEdge _)
    (fun a b hab => by
      rw [← hInter a b hab]
      exact inter_subset_inter_right _ hrange)
    (by
      intro e he e' he' hne
      induction e using Sym2.ind with
      | _ a b =>
      induction e' using Sym2.ind with
      | _ a' b' =>
      have hab : (GM16.sphereWallSimpleGraph W.height).Adj a b := he
      intro z hz
      have hsym : s(sphereToWall a, sphereToWall b) ≠ s(sphereToWall a', sphereToWall b') := by
        intro h
        apply hne
        rcases Sym2.eq_iff.mp h with ⟨h1, h2⟩ | ⟨h1, h2⟩
        · rw [sphereToWall_injective _ h1, sphereToWall_injective _ h2]
        · rw [sphereToWall_injective _ h1, sphereToWall_injective _ h2, Sym2.eq_swap]
      have hab' : (GM16.sphereWallSimpleGraph W.height).Adj a' b' := he'
      have hzB := (W.baseEdge_paths_disjoint (sphereToWall_adj hab) (sphereToWall_adj hab')
        hsym).2 (by rw [← hPmk a b hab, ← hPmk a' b' hab']; exact hz)
      have : z ∈ V(P s(a, b)) ∩ V(W.baseGraph) := ⟨hz.1, hzB⟩
      rw [hInter a b hab] at this
      rcases this with rfl | rfl
      · exact ⟨a, rfl⟩
      · exact ⟨b, rfl⟩)
    (by
      intro e he e' he' hne
      induction e using Sym2.ind with
      | _ a b =>
      induction e' using Sym2.ind with
      | _ a' b' =>
      have hab : (GM16.sphereWallSimpleGraph W.height).Adj a b := he
      have hab' : (GM16.sphereWallSimpleGraph W.height).Adj a' b' := he'
      have hsym : s(sphereToWall a, sphereToWall b) ≠ s(sphereToWall a', sphereToWall b') := by
        intro h
        apply hne
        rcases Sym2.eq_iff.mp h with ⟨h1, h2⟩ | ⟨h1, h2⟩
        · rw [sphereToWall_injective _ h1, sphereToWall_injective _ h2]
        · rw [sphereToWall_injective _ h1, sphereToWall_injective _ h2, Sym2.eq_swap]
      rw [hPmk a b hab, hPmk a' b' hab']
      exact (W.baseEdge_paths_disjoint (sphereToWall_adj hab) (sphereToWall_adj hab') hsym).1)
  exact ⟨ηv, ηe, hmodel, hηe⟩

/-! ## The wall tangle -/

/-- A small side of the wall tangle of XVI (4.2) contains no row: if `(A, B)` is in
`GM16.sphereWallTangle θ` then no row of `GM16.sphereWallGraph θ` has all its edges in `A`. -/
theorem sphereWallTangle_no_small_row {θ : ℕ} (hθ : 2 ≤ θ)
    {A B : Hypergraph (Fin (2 * θ + 1) × Fin θ) (Sym2 (Fin (2 * θ + 1) × Fin θ))}
    (hAB : (A, B) ∈ GM16.sphereWallTangle θ) (j : Fin θ) :
    ¬ E(GM16.sphereWallRow θ j) ⊆ A.edgeSet := by
  obtain ⟨N₂, hV₂, hE₂, -, hImage, -, hT₁⟩ := GM16.exists_induced_wall_tangle θ hθ
  obtain ⟨hSep, hOrd, j', hRow'⟩ := hAB
  rcases hT₁.axiom1 hSep hOrd with h | h
  · exact GM16.induced_wall_tangle_no_small_row hθ hV₂ hE₂ hImage h j
  · exact (GM16.induced_wall_tangle_no_small_row hθ hV₂ hE₂ hImage h j' hRow').elim

/-- A minor model in a subgraph is a minor model in the whole graph. -/
theorem _root_.GraphMinor.IsMinorModel.mono {α' β' : Type*} {L : Graph α' β'} {H G : Graph α β}
    {ηv : α' → Set α} {ηe : β' → β} (h : IsMinorModel L H ηv ηe) (hHG : H ≤ G) :
    IsMinorModel L G ηv ηe := by
  have hinc : ∀ e ∈ E(L), ∀ x, G.Inc (ηe e) x ↔ H.Inc (ηe e) x := by
    intro e he x
    constructor
    · rintro ⟨y, hy⟩
      exact ⟨y, (hHG.isLink_iff' (y := y)).mpr ⟨hy, h.edge_mem e he⟩⟩
    · rintro ⟨y, hy⟩
      exact ⟨y, hy.mono hHG⟩
  refine ⟨h.vertex_nonempty, fun v hv => (h.vertex_subset v hv).trans hHG.vertexSet_mono,
    fun e he => hHG.edgeSet_mono (h.edge_mem e he), h.vertex_disjoint, h.edge_injOn, ?_, ?_, ?_⟩
  · intro v hv e he
    rw [h.inc_iff v hv e he]
    simp only [hinc e he]
  · intro v hv e he
    rw [h.isLoopAt_iff v hv e he]
    simp only [hinc e he]
  · intro v hv
    obtain ⟨K, hK, hKv, hKc⟩ := h.connected v hv
    exact ⟨K, hK.trans (Graph.deleteEdges_mono_left hHG _), hKv, hKc⟩

/-- **The wall tangle of `H`, controlling a tangle of a drawing.** Let `W` be a wall of height
`h` in a finite graph `G₀`, and let `Γ` be a drawing of `W.graph`. Then there are a span
embedding `η` of `Γ` in `G₀` that inverts the drawing, a tangle `T*` of order `h` in `G₀`, and a
tangle `T` of order `h` in `Γ` controlled by `T*`, such that no small side of `T` contains the
drawing of a row: for every `(A, B) ∈ T` and every row `j < h` of `GM16.sphereWallGraph h`,
some edge of a path subdividing an edge of that row is not drawn in `A`.

This is "taking $\mathcal{T}$ to be the set of all separations $(A, B)$ of $H$ of order $< r$ such
that $A$ contains no horizontal path of $H$" in the proof of (7.4), page 90, with `r = h`. The
tangle is
the one of XVI (4.2) (`GM16.sphereWallTangle`), induced through the minor model of
`Wall.exists_sphereWall_model`, as in the proof of XVI (4.2). -/
theorem Wall.exists_controlled_tangle {S : Type*} [TopologicalSpace S] [T2Space S] [Nonempty S]
    [Nonempty α] [Nonempty β] (W : Wall α β) {G₀ : Graph α β} (hG₀ : W.graph ≤ G₀)
    (hV : V(G₀).Finite) (hE : E(G₀).Finite) (Γ : GraphDrawing W.graph S) :
    ∃ (η : GM14.SpanEmbedding Γ.drawing G₀) (Tstar : Set (Hypergraph α β × Hypergraph α β))
      (T : Set (Hypergraph S (Set S) × Hypergraph S (Set S))),
      η.imageGraph = W.graph ∧
      (∀ x : V(W.graph), η.vMap (Γ.iso.vertexEquiv x).1 = x.1) ∧
      GM15.IsControllingTangle G₀ Γ.drawing η W.height W.height Tstar T ∧
      ∀ A B, (A, B) ∈ T → ∀ j : Fin W.height,
        ∃ e ∈ E(GM16.sphereWallRow W.height j), ∃ (f : β) (hf : f ∈ E(W.graph)),
          f ∈ E(W.subdivisionPaths (W.sphereEdge e)) ∧ (Γ.iso.edgeEquiv ⟨f, hf⟩).1 ∉ A.edgeSet := by
  classical
  have hTwo := W.two_le_height
  obtain ⟨ηv, ηe, hmodel, hηe⟩ := W.exists_sphereWall_model
  have hVH := W.vertexSet_finite
  have hEH := W.edgeSet_finite
  obtain ⟨K, hVK, hEK, -, hImage, -, hTN⟩ := GM16.exists_model_induced_tangle
    (Set.toFinite _) (Set.toFinite _) hVH hEH hmodel hTwo (GM16.theorem_4_2_claim_1 hTwo)
  obtain ⟨K', hVK', hEK', -, hImage', -, hTstar⟩ := GM16.exists_model_induced_tangle
    (Set.toFinite _) (Set.toFinite _) hV hE (hmodel.mono hG₀) hTwo (GM16.theorem_4_2_claim_1 hTwo)
  let Wsph := Hypergraph.ofGraph (GM16.sphereWallGraph W.height) (Set.toFinite _) (Set.toFinite _)
  let TN := inducedTangle (Hypergraph.ofGraph W.graph hVH hEH) (Hypergraph.ofGraph K hVK hEK)
    (GM16.imageHypergraphTangle ηv ηe (GM16.sphereWallTangle W.height)) W.height
  let Tstar := inducedTangle (Hypergraph.ofGraph G₀ hV hE) (Hypergraph.ofGraph K' hVK' hEK')
    (GM16.imageHypergraphTangle ηv ηe (GM16.sphereWallTangle W.height)) W.height
  have hTstarG : GM15.IsGraphTangle G₀ W.height Tstar := ⟨hV, hE, hTstar⟩
  have hChosen : ηe '' Wsph.edgeSet ⊆ (Hypergraph.ofGraph W.graph hVH hEH).edgeSet := by
    rintro e ⟨e₀, he₀, rfl⟩
    exact hmodel.edge_mem e₀ he₀
  have hConformal : inducedTangle (Hypergraph.ofGraph G₀ hTstarG.finite_V hTstarG.finite_E)
      (Hypergraph.ofGraph W.graph hVH hEH) TN W.height ⊆ Tstar := by
    have hSub := GM16.inducedTangle_subset_of_same_edge_pattern Wsph
      (Hypergraph.ofGraph G₀ hV hE) (Hypergraph.ofGraph W.graph hVH hEH)
      ηv ηv ηe (GM16.sphereWallTangle W.height) W.height hChosen
    simpa only [TN, Tstar, hImage, hImage'] using hSub
  -- the drawing tangle, as in `GM16.exists_controlled_drawing_tangle`
  obtain ⟨η, hηImage, hηV, hηE⟩ := GM16.exists_spanEmbedding_of_graphDrawing hG₀ Γ
  obtain ⟨f, g, hf, hg, hfInj, hgInj⟩ := GM16.exists_graphDrawing_forward_maps Γ
  have hHyp : GM16.imageHypergraph f g (Hypergraph.ofGraph W.graph hVH hEH) =
      Γ.drawing.toHypergraph :=
    (GM16.imageHypergraph_of_iso hVH hEH Γ.drawing.finite_V Γ.drawing.finite_edges Γ.iso f g
      (fun x => (hf x).symm) (fun e => (hg e).symm)).trans (GM16.drawing_ofGraph_toGraph Γ.drawing)
  have hTD : IsTangle Γ.drawing.toHypergraph W.height (GM16.imageHypergraphTangle f g TN) := by
    rw [← hHyp]
    exact GM16.isTangle_imageHypergraphTangle_on f g hfInj hgInj hTN
  have hInv : LeftInvOn η.eMap g E(W.graph) := by
    intro e he
    rw [hg ⟨e, he⟩, hηE (Γ.iso.edgeEquiv ⟨e, he⟩)]
    exact congrArg Subtype.val (Γ.iso.edgeEquiv.symm_apply_apply ⟨e, he⟩)
  have hCtrl := GM16.controllingTangle_of_induced_subset η hηImage hTstarG le_rfl hVH hEH TN hTN
    f g hInv hTD hConformal
  refine ⟨η, Tstar, GM16.imageHypergraphTangle f g TN, hηImage, ?_, hCtrl, ?_⟩
  · intro x
    have h1 := hηV ⟨(Γ.iso.vertexEquiv x).1, (Γ.iso.vertexEquiv x).2⟩
    rw [h1]
    exact congrArg Subtype.val (Γ.iso.vertexEquiv.symm_apply_apply x)
  · -- no small row
    rintro A B ⟨⟨A', B'⟩, hA'B', hpair⟩ j
    have hA : A = GM16.imageHypergraph f g A' := (congrArg Prod.fst hpair).symm
    obtain ⟨hSep', -, p', hp', hp'E⟩ := hA'B'
    obtain ⟨⟨A₀, B₀⟩, h₀, hp'eq⟩ := hp'
    have hA₀E : ηe '' A₀.edgeSet = A'.edgeSet ∩ E(K) := by
      rw [← hp'eq] at hp'E
      exact hp'E
    by_contra hall
    push Not at hall
    apply sphereWallTangle_no_small_row hTwo h₀ j
    intro e he
    have heW : e ∈ (GM16.sphereWallSimpleGraph W.height).edgeSet :=
      (GM16.sphereWallRow_le W.height j).edgeSet_mono he
    have hfW : ηe e ∈ E(W.graph) := hmodel.edge_mem e heW
    have hgA : g (ηe e) ∈ A.edgeSet := by
      rw [hg ⟨_, hfW⟩]
      exact hall e he (ηe e) hfW (hηe e heW)
    rw [hA] at hgA
    obtain ⟨f', hf', hgf'⟩ := hgA
    have hf'W : f' ∈ E(W.graph) := hSep'.left_le.edgeSet_subset hf'
    have hf'eq : f' = ηe e := hgInj hf'W hfW hgf'
    have hKE : E(K) = ηe '' Wsph.edgeSet := congrArg Hypergraph.edgeSet hImage
    have hmem : ηe e ∈ A'.edgeSet ∩ E(K) := ⟨hf'eq ▸ hf', hKE ▸ ⟨e, heW, rfl⟩⟩
    rw [← hA₀E] at hmem
    obtain ⟨e₀, he₀, he₀eq⟩ := hmem
    have he₀W : e₀ ∈ Wsph.edgeSet := (GM10.IsTangle.isSeparation
      (GM16.theorem_4_2_claim_1 hTwo) h₀).left_le.edgeSet_subset he₀
    rw [← hmodel.edge_injOn he₀W heW he₀eq]
    exact he₀

end GraphMinor.GM13
