module

public import GraphMinor.Compute.Algorithm44ModelBridge
public import GraphMinor.GM13.Section7a

/-!
# Bridge Between `GM13.theorem_4_2_proof` / `GM13.isPlanar_elementaryWall` and `HasPlanarGridThreshold`

This file eliminates the `HasPlanarGridThreshold` hypothesis in GM XIII Algorithm (4.4) and
Algorithm (7.2) by deriving it from `GM13.theorem_4_2_proof` (`GraphMinor/GM13/Section4.lean`)
and `GM13.isPlanar_elementaryWall` (`GraphMinor/GM13/Section7a.lean`):

1. `hasDigraphModel_of_isIsoMinor_targetGMGraph`: if `targetGMGraph p edgesH` is isomorphic to a
   minor of `G.toGMDigraph.toGraph` (`GM13.IsIsoMinor`), then `HasDigraphModel edgesH G` holds.
2. `exists_hasPlanarGridThreshold_of_isPlanarGraph`: for any planar graph `H`
   (`IsPlanar (targetGMGraph p edgesH)`), `GM13.theorem_4_2_proof` yields `ω ≥ 2` satisfying
   `HasPlanarGridThreshold edgesH ω`.
3. `targetGMGraphIsoElementaryWall` and `isPlanarGraph_targetGMGraph_elemWall`: constructs the
   graph isomorphism between `targetGMGraph (elemWallNumVerts h) (elemWallEdges h)` and
   `GM13.elementaryWall h`, and deduces `IsPlanar (targetGMGraph (elemWallNumVerts h) (elemWallEdges h))`
   from `GM13.isPlanar_elementaryWall h`.
4. `exists_elemWall_planarGridThreshold`: deduces `∃ ω₀ ≥ 2, HasPlanarGridThreshold (elemWallEdges h) ω₀`
   unconditionally for every `h : ℕ`.
-/

@[expose] public section

namespace GraphMinor.Compute

open Set Function Graph SimpleGraph Classical
open GraphMinor GraphMinor.Surface GraphMinor.GM13

/-! ### Section 1: Basic Lemmas on `targetGMGraph p edgesH` -/

@[simp]
theorem vertexSet_targetGMGraph (p : ℕ) (edgesH : List (Fin p × Fin p)) :
    V(targetGMGraph p edgesH) = {u : ℕ | u < p} := rfl

@[simp]
theorem edgeSet_targetGMGraph (p : ℕ) (edgesH : List (Fin p × Fin p)) :
    E(targetGMGraph p edgesH) = {k : ℕ | k < edgesH.length} := rfl

theorem targetGMGraph_isLink_of_lt {p : ℕ} (edgesH : List (Fin p × Fin p))
    (k : Fin edgesH.length) :
    (targetGMGraph p edgesH).IsLink k.1 (edgesH[k.1]'k.2).2.1 (edgesH[k.1]'k.2).1.1 := by
  refine ⟨k.2, Or.inl ⟨?_, ?_⟩⟩
  · change (if h : k.1 < edgesH.length then (edgesH[k.1]'h).2.1 else 0) = (edgesH[k.1]'k.2).2.1
    rw [dite_eq_left k.2]
  · change (if h : k.1 < edgesH.length then (edgesH[k.1]'h).1.1 else 0) = (edgesH[k.1]'k.2).1.1
    rw [dite_eq_left k.2]

theorem targetGMGraph_isLink_iff {p : ℕ} (edgesH : List (Fin p × Fin p))
    (k x y : ℕ) :
    (targetGMGraph p edgesH).IsLink k x y ↔
      ∃ hk : k < edgesH.length,
        ((edgesH[k]'hk).2.1 = x ∧ (edgesH[k]'hk).1.1 = y) ∨
        ((edgesH[k]'hk).2.1 = y ∧ (edgesH[k]'hk).1.1 = x) := by
  constructor
  · rintro ⟨hk, hlink⟩
    change k < edgesH.length at hk
    refine ⟨hk, ?_⟩
    change ((if h : k < edgesH.length then (edgesH[k]'h).2.1 else 0) = x ∧
        (if h : k < edgesH.length then (edgesH[k]'h).1.1 else 0) = y) ∨
      ((if h : k < edgesH.length then (edgesH[k]'h).2.1 else 0) = y ∧
        (if h : k < edgesH.length then (edgesH[k]'h).1.1 else 0) = x) at hlink
    rwa [dite_eq_left hk, dite_eq_left hk] at hlink
  · rintro ⟨hk, hlink⟩
    refine ⟨hk, ?_⟩
    change ((if h : k < edgesH.length then (edgesH[k]'h).2.1 else 0) = x ∧
        (if h : k < edgesH.length then (edgesH[k]'h).1.1 else 0) = y) ∨
      ((if h : k < edgesH.length then (edgesH[k]'h).2.1 else 0) = y ∧
        (if h : k < edgesH.length then (edgesH[k]'h).1.1 else 0) = x)
    rwa [dite_eq_left hk, dite_eq_left hk]

theorem targetGMGraph_isLink_of_mem_iff {p : ℕ} (edgesH : List (Fin p × Fin p))
    (k : E(targetGMGraph p edgesH)) (x y : ℕ) :
    (targetGMGraph p edgesH).IsLink k.1 x y ↔
      (((edgesH[k.1]'k.2).2.1 = x ∧ (edgesH[k.1]'k.2).1.1 = y) ∨
       ((edgesH[k.1]'k.2).2.1 = y ∧ (edgesH[k.1]'k.2).1.1 = x)) := by
  rw [targetGMGraph_isLink_iff]
  exact ⟨fun ⟨_, h⟩ => h, fun h => ⟨k.2, h⟩⟩

/-! ### Section 2: From `GM13.IsIsoMinor (targetGMGraph p edgesH) G.toGMDigraph.toGraph` to `HasDigraphModel` -/

/-- If `K ≤ D.toGraph`, any edge `e ∈ E(K)` has `D.head e ∈ V(K)` and `D.tail e ∈ V(K)`. -/
private theorem head_and_tail_mem_of_le_toGraph {α β : Type*} {D : GM13.Digraph α β}
    {K : Graph α β} (hle : K ≤ D.toGraph) {e : β} (he : e ∈ E(K)) :
    D.head e ∈ V(K) ∧ D.tail e ∈ V(K) := by
  obtain ⟨x, y, hlinkK⟩ := (K.edge_mem_iff_exists_isLink e).mp he
  have hx : x ∈ V(K) := hlinkK.left_mem
  have hy : y ∈ V(K) := hlinkK.right_mem
  have hlinkD : D.toGraph.IsLink e x y := hlinkK.mono hle
  rcases hlinkD.2 with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact ⟨hx, hy⟩
  · exact ⟨hy, hx⟩

/-- Build a `DigraphSubgraph G.toMultiComputeDigraph` from a subgraph `K ≤ G.toGMDigraph.toGraph`. -/
noncomputable def digraphSubgraphOfSub {n : ℕ} (G : MultiDigraph n)
    {K : Graph ℕ (ℕ × ℕ × ℕ)} (hle : K ≤ G.toGMDigraph.toGraph) :
    DigraphSubgraph G.toMultiComputeDigraph where
  verts := Finset.univ.filter (fun x : Fin n => x.1 ∈ V(K))
  edges := Finset.univ.filter (fun i : Fin G.numEdges => (G.multiEdgeEquiv i).1 ∈ E(K))
  head_mem i hi := by
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
    rw [← G.head_multiEdgeEquiv i]
    exact (head_and_tail_mem_of_le_toGraph hle hi).1
  tail_mem i hi := by
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
    rw [← G.tail_multiEdgeEquiv i]
    exact (head_and_tail_mem_of_le_toGraph hle hi).2

@[simp]
theorem mem_verts_digraphSubgraphOfSub {n : ℕ} (G : MultiDigraph n)
    {K : Graph ℕ (ℕ × ℕ × ℕ)} (hle : K ≤ G.toGMDigraph.toGraph) (x : Fin n) :
    x ∈ (digraphSubgraphOfSub G hle).verts ↔ x.1 ∈ V(K) := by
  unfold digraphSubgraphOfSub
  exact Finset.mem_filter.trans (and_iff_right (Finset.mem_univ x))

@[simp]
theorem mem_edges_digraphSubgraphOfSub {n : ℕ} (G : MultiDigraph n)
    {K : Graph ℕ (ℕ × ℕ × ℕ)} (hle : K ≤ G.toGMDigraph.toGraph) (i : Fin G.numEdges) :
    i ∈ (digraphSubgraphOfSub G hle).edges ↔ (G.multiEdgeEquiv i).1 ∈ E(K) := by
  unfold digraphSubgraphOfSub
  exact Finset.mem_filter.trans (and_iff_right (Finset.mem_univ i))

private theorem reachable_digraphSubgraphOfSub_of_reflTransGen {n : ℕ} (G : MultiDigraph n)
    {K : Graph ℕ (ℕ × ℕ × ℕ)} (hle : K ≤ G.toGMDigraph.toGraph)
    {a b : ℕ} (h : Relation.ReflTransGen K.Adj a b) (ha : a < n) (hb : b < n) :
    (digraphSubgraphOfSub G hle).underlyingSimpleGraph.Reachable ⟨a, ha⟩ ⟨b, hb⟩ := by
  induction h with
  | refl => exact SimpleGraph.Reachable.refl _
  | @tail c d _ hcd ih =>
    rcases hcd with ⟨e, hlinkK⟩
    have hc_mem : c ∈ V(K) := hlinkK.left_mem
    have hc : c < n := hle.vertexSet_mono hc_mem
    have hreach_ac := ih hc
    by_cases hcd_eq : (⟨c, hc⟩ : Fin n) = ⟨d, hb⟩
    · rwa [hcd_eq] at hreach_ac
    · have heK : e ∈ E(K) := hlinkK.edge_mem
      have hlinkD : G.toGMDigraph.toGraph.IsLink e c d := hlinkK.mono hle
      have heD : e ∈ G.toGMDigraph.edgeSet := hlinkD.1
      let i : Fin G.numEdges := G.multiEdgeEquiv.symm ⟨e, heD⟩
      have hi_eq : (G.multiEdgeEquiv i).1 = e :=
        congrArg Subtype.val (G.multiEdgeEquiv.apply_symm_apply ⟨e, heD⟩)
      have hadj : (digraphSubgraphOfSub G hle).underlyingSimpleGraph.Adj ⟨c, hc⟩ ⟨d, hb⟩ := by
        refine ⟨hcd_eq, i, ?_, ?_⟩
        · rw [mem_edges_digraphSubgraphOfSub, hi_eq]
          exact heK
        · have hh : (G.toMultiComputeDigraph.head i).1 = G.toGMDigraph.head e := by
            rw [← hi_eq, G.head_multiEdgeEquiv]
          have ht : (G.toMultiComputeDigraph.tail i).1 = G.toGMDigraph.tail e := by
            rw [← hi_eq, G.tail_multiEdgeEquiv]
          rcases hlinkD.2 with ⟨hc_eq, hd_eq⟩ | ⟨hd_eq, hc_eq⟩
          · exact Or.inl ⟨Fin.ext (hh.trans hc_eq), Fin.ext (ht.trans hd_eq)⟩
          · exact Or.inr ⟨Fin.ext (hh.trans hd_eq), Fin.ext (ht.trans hc_eq)⟩
      exact hreach_ac.trans hadj.reachable

theorem isNonNullConnected_digraphSubgraphOfSub {n : ℕ} (G : MultiDigraph n)
    {K : Graph ℕ (ℕ × ℕ × ℕ)} (hle : K ≤ G.toGMDigraph.toGraph)
    (hconn : GraphConnected K) :
    (digraphSubgraphOfSub G hle).IsNonNullConnected := by
  rcases hconn with ⟨⟨x₀, hx₀⟩, hreach⟩
  have hx₀_lt : x₀ < n := hle.vertexSet_mono hx₀
  refine ⟨⟨⟨x₀, hx₀_lt⟩, (mem_verts_digraphSubgraphOfSub G hle ⟨x₀, hx₀_lt⟩).mpr hx₀⟩,
    fun u hu v hv => ?_⟩
  rw [mem_verts_digraphSubgraphOfSub] at hu hv
  exact reachable_digraphSubgraphOfSub_of_reflTransGen G hle (hreach u.1 hu v.1 hv) u.2 v.2

/-- If `targetGMGraph p edgesH` is isomorphic to a minor of `G.toGMDigraph.toGraph`, then
`HasDigraphModel edgesH G` holds. -/
theorem hasDigraphModel_of_isIsoMinor_targetGMGraph {p n : ℕ}
    (edgesH : List (Fin p × Fin p)) (G : MultiDigraph n)
    (hminor : IsIsoMinor (targetGMGraph p edgesH) G.toGMDigraph.toGraph) :
    HasDigraphModel edgesH G := by
  let H := targetGMGraph p edgesH
  let D := G.toGMDigraph
  have : Nonempty (ℕ × ℕ × ℕ) := ⟨(0, 0, 0)⟩
  have hVD : V(D.toGraph).Finite := G.isFinite_toGMDigraph.finite_V
  have hED : E(D.toGraph).Finite := G.isFinite_toGMDigraph.finite_E
  obtain ⟨ηv, ηe, hm⟩ := exists_isMinorModel_of_isIsoMinor hVD hED hminor
  have hK (u : Fin p) := hm.connected u.1 u.2
  let KOf (u : Fin p) : Graph ℕ (ℕ × ℕ × ℕ) := (hK u).choose
  have hK_le (u : Fin p) : KOf u ≤ D.toGraph.deleteEdges (ηe '' E(H)) := (hK u).choose_spec.1
  have hK_V (u : Fin p) : V(KOf u) = ηv u.1 := (hK u).choose_spec.2.1
  have hK_conn (u : Fin p) : GraphConnected (KOf u) := (hK u).choose_spec.2.2
  have hle_D (u : Fin p) : KOf u ≤ D.toGraph := (hK_le u).trans Graph.deleteEdges_le
  have hends (k : Fin edgesH.length) :
      (D.head (ηe k.1) ∈ ηv (edgesH[k.1]'k.2).2.1 ∧
       D.tail (ηe k.1) ∈ ηv (edgesH[k.1]'k.2).1.1) ∨
      (D.head (ηe k.1) ∈ ηv (edgesH[k.1]'k.2).1.1 ∧
       D.tail (ηe k.1) ∈ ηv (edgesH[k.1]'k.2).2.1) := by
    obtain ⟨u₀, _, v₀, _, hlink₀, hhead₀, htail₀⟩ :=
      GM13.exists_ends_in_minorModel_of_digraph hm (e := k.1) k.2
    have hlink_k := targetGMGraph_isLink_of_lt edgesH k
    rcases hlink₀.eq_and_eq_or_eq_and_eq hlink_k with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact Or.inl ⟨hhead₀, htail₀⟩
    · exact Or.inr ⟨hhead₀, htail₀⟩
  let flips (k : Fin edgesH.length) : Bool :=
    decide ¬ (D.head (ηe k.1) ∈ ηv (edgesH[k.1]'k.2).2.1 ∧
              D.tail (ηe k.1) ∈ ηv (edgesH[k.1]'k.2).1.1)
  let edgeChoice (k : Fin edgesH.length) : Fin G.numEdges :=
    G.multiEdgeEquiv.symm ⟨ηe k.1, hm.edge_mem k.1 k.2⟩
  have hedgeChoice_eq (k : Fin edgesH.length) :
      (G.multiEdgeEquiv (edgeChoice k)).1 = ηe k.1 :=
    congrArg Subtype.val (G.multiEdgeEquiv.apply_symm_apply ⟨ηe k.1, hm.edge_mem k.1 k.2⟩)
  refine (hasDigraphModel_iff_exists_hasRootedDigraphModel edgesH G).mpr ⟨flips, ⟨{
    vertMap := fun u => digraphSubgraphOfSub G (hle_D u)
    edgeMap := edgeChoice
    connected := fun u => isNonNullConnected_digraphSubgraphOfSub G (hle_D u) (hK_conn u)
    vert_disjoint := fun u v hne => by
      rw [Finset.disjoint_left]
      intro x hxu hxv
      rw [mem_verts_digraphSubgraphOfSub, hK_V] at hxu hxv
      exact Set.disjoint_left.mp
        (hm.vertex_disjoint u.1 u.2 v.1 v.2 (fun h => hne (Fin.ext h))) hxu hxv
    edge_injective := fun k₁ k₂ heq => by
      have hsub := congrArg G.multiEdgeEquiv heq
      have hval : ηe k₁.1 = ηe k₂.1 := by
        rw [← hedgeChoice_eq k₁, ← hedgeChoice_eq k₂, hsub]
      exact Fin.ext (hm.edge_injOn k₁.2 k₂.2 hval)
    edge_notMem_vert := fun u k hmem => by
      rw [mem_edges_digraphSubgraphOfSub, hedgeChoice_eq] at hmem
      have hdel := (hK_le u).edgeSet_mono hmem
      rw [Graph.edgeSet_deleteEdges] at hdel
      exact hdel.2 ⟨k.1, k.2, rfl⟩
    head_mem_vertMap := fun k => by
      rw [mem_verts_digraphSubgraphOfSub, hK_V]
      have hh : (G.toMultiComputeDigraph.head (edgeChoice k)).1 = D.head (ηe k.1) := by
        rw [← hedgeChoice_eq k, G.head_multiEdgeEquiv]
      change (G.toMultiComputeDigraph.head (edgeChoice k)).1 ∈
        ηv (if flips k then (edgesH[k.1]'k.2).1 else (edgesH[k.1]'k.2).2).1
      rw [hh]
      dsimp [flips]
      by_cases hdir : D.head (ηe k.1) ∈ ηv (edgesH[k.1]'k.2).2.1 ∧
          D.tail (ηe k.1) ∈ ηv (edgesH[k.1]'k.2).1.1
      · simp [hdir]
      · simp only [hdir, not_false_eq_true, decide_true, ↓reduceIte]
        rcases hends k with h1 | h2
        · exact False.elim (hdir h1)
        · exact h2.1
    tail_mem_vertMap := fun k => by
      rw [mem_verts_digraphSubgraphOfSub, hK_V]
      have ht : (G.toMultiComputeDigraph.tail (edgeChoice k)).1 = D.tail (ηe k.1) := by
        rw [← hedgeChoice_eq k, G.tail_multiEdgeEquiv]
      change (G.toMultiComputeDigraph.tail (edgeChoice k)).1 ∈
        ηv (if flips k then (edgesH[k.1]'k.2).2 else (edgesH[k.1]'k.2).1).1
      rw [ht]
      dsimp [flips]
      by_cases hdir : D.head (ηe k.1) ∈ ηv (edgesH[k.1]'k.2).2.1 ∧
          D.tail (ηe k.1) ∈ ηv (edgesH[k.1]'k.2).1.1
      · simp [hdir]
      · simp only [hdir, not_false_eq_true, decide_true, ↓reduceIte]
        rcases hends k with h1 | h2
        · exact False.elim (hdir h1)
        · exact h2.2
    root_mem_vertMap := fun i => i.elim0
  }⟩⟩

/-! ### Section 3: `HasPlanarGridThreshold` from `GM13.theorem_4_2_proof` -/

/-- **GM XIII (4.2) Theorem property (page 76)** for a planar graph `H` (with `p` vertices and
edges `edgesH`) and branch-width threshold `ω`:
"For every planar graph $H$ there is a number $\omega$ such that every graph with branch-width
$\ge \omega$ has a minor isomorphic to $H$." -/
def HasPlanarGridThreshold {p : ℕ} (edgesH : List (Fin p × Fin p)) (ω : ℕ) : Prop :=
  ∀ {n : ℕ} (G' : MultiDigraph n), HasBranchWidthGe G' ω → HasDigraphModel edgesH G'

theorem HasBranchWidthGe.not_graphBranchWidthLE_sub_one {n ω : ℕ} (hω : 1 ≤ ω)
    {G : MultiDigraph n} (h : HasBranchWidthGe G ω) :
    ¬ GM13.GraphBranchWidthLE G.toGMDigraph.toGraph (ω - 1) := by
  intro hbw
  exact h.2 (ω - 1) (by omega) ((hasBranchDecompOfWidthLe_iff_graphBranchWidthLE G (ω - 1)).mpr hbw)

/-- **GM XIII (4.2) Theorem (page 76)** for `targetGMGraph p edgesH`:
If `targetGMGraph p edgesH` is planar (`IsPlanar (targetGMGraph p edgesH)`), then there
exists `ω ≥ 2` satisfying `HasPlanarGridThreshold edgesH ω`. -/
theorem exists_hasPlanarGridThreshold_of_isPlanarGraph {p : ℕ}
    (edgesH : List (Fin p × Fin p))
    (hPlanar : IsPlanar (targetGMGraph p edgesH)) :
    ∃ ω : ℕ, 2 ≤ ω ∧ HasPlanarGridThreshold edgesH ω := by
  obtain ⟨ω, hω2, h42⟩ :=
    GM13.theorem_4_2_proof (α := ℕ) (β := ℕ × ℕ × ℕ) (targetGMGraph p edgesH) hPlanar
  refine ⟨ω, hω2, fun {n} G' hbw => ?_⟩
  have hnot_bw : ¬ GM13.GraphBranchWidthLE G'.toGMDigraph.toGraph (ω - 1) :=
    hbw.not_graphBranchWidthLE_sub_one (by omega)
  have hminor : IsIsoMinor (targetGMGraph p edgesH) G'.toGMDigraph.toGraph :=
    h42 G'.toGMDigraph.toGraph
      G'.isFinite_toGMDigraph.finite_V G'.isFinite_toGMDigraph.finite_E hnot_bw
  exact hasDigraphModel_of_isIsoMinor_targetGMGraph edgesH G' hminor

/-! ### Section 4: Planarity of `targetGMGraph (elemWallNumVerts h) (elemWallEdges h)` -/

/-- Vertex bijection `V(targetGMGraph (elemWallNumVerts h) (elemWallEdges h)) ≃ V(GM13.elementaryWall h)`. -/
def elemWallTargetVertexEquiv (h : ℕ) :
    V(targetGMGraph (elemWallNumVerts h) (elemWallEdges h)) ≃ V(GM13.elementaryWall h) where
  toFun u := elemWallCoordEquiv h ⟨u.1, u.2⟩
  invFun p := ⟨(elemWallCoordEquiv h).symm p, ((elemWallCoordEquiv h).symm p).2⟩
  left_inv u := by
    ext
    exact congrArg Fin.val ((elemWallCoordEquiv h).symm_apply_apply ⟨u.1, u.2⟩)
  right_inv p := (elemWallCoordEquiv h).apply_symm_apply p

/-- Edge map `E(targetGMGraph (elemWallNumVerts h) (elemWallEdges h)) → E(GM13.elementaryWall h)`. -/
def elemWallTargetEdgeTo (h : ℕ)
    (k : E(targetGMGraph (elemWallNumVerts h) (elemWallEdges h))) :
    E(GM13.elementaryWall h) :=
  ⟨elemWallEdgeSym2 h ⟨k.1, k.2⟩, elemWallEdgeSym2_mem_edgeSet h ⟨k.1, k.2⟩⟩

theorem elemWallTargetEdgeTo_bijective (h : ℕ) :
    Function.Bijective (elemWallTargetEdgeTo h) := by
  refine ⟨?_, ?_⟩
  · intro k₁ k₂ heq
    have hval := congrArg Subtype.val heq
    have hfin := elemWallEdgeSym2_injective h hval
    exact Subtype.ext (congrArg Fin.val hfin)
  · rintro ⟨e₀, p, q, hadj, rfl⟩
    rcases exists_elemWallEdgeSym2_of_elementaryWallAdj hadj with ⟨k, hk⟩
    exact ⟨⟨k.1, k.2⟩, Subtype.ext hk⟩

@[simp]
theorem elemWallTargetVertexEquiv_val (h : ℕ)
    (x : V(targetGMGraph (elemWallNumVerts h) (elemWallEdges h))) :
    (elemWallTargetVertexEquiv h x).1 = elemWallVertCoord h ⟨x.1, x.2⟩ := rfl

@[simp]
theorem elemWallTargetEdgeTo_val (h : ℕ)
    (k : E(targetGMGraph (elemWallNumVerts h) (elemWallEdges h))) :
    (elemWallTargetEdgeTo h k).1 = elemWallEdgeSym2 h ⟨k.1, k.2⟩ := rfl

theorem elemWallEdgeSym2_eq (h : ℕ) (k : Fin (elemWallEdges h).length) :
    elemWallEdgeSym2 h k =
      s(elemWallVertCoord h ((elemWallEdges h)[k.1]'k.2).1,
        elemWallVertCoord h ((elemWallEdges h)[k.1]'k.2).2) := rfl

theorem elementaryWall_isLink_iff (h : ℕ) (e : Sym2 (ℕ × ℕ)) (p q : ℕ × ℕ) :
    (GM13.elementaryWall h).IsLink e p q ↔
      GM13.elementaryWallAdj h p q ∧ e = s(p, q) := Iff.rfl

theorem targetGMGraph_elemWall_isLink_iff (h : ℕ)
    (k : E(targetGMGraph (elemWallNumVerts h) (elemWallEdges h)))
    (x y : V(targetGMGraph (elemWallNumVerts h) (elemWallEdges h))) :
    (targetGMGraph (elemWallNumVerts h) (elemWallEdges h)).IsLink k.1 x.1 y.1 ↔
      (GM13.elementaryWall h).IsLink (elemWallTargetEdgeTo h k).1
        (elemWallTargetVertexEquiv h x).1 (elemWallTargetVertexEquiv h y).1 := by
  have hadj_k :
      GM13.elementaryWallAdj h
        (elemWallVertCoord h ((elemWallEdges h)[k.1]'k.2).1)
        (elemWallVertCoord h ((elemWallEdges h)[k.1]'k.2).2) :=
    elemWallEdge_elementaryWallAdj h ⟨k.1, k.2⟩
  rw [targetGMGraph_isLink_of_mem_iff (elemWallEdges h) k x.1 y.1,
    elementaryWall_isLink_iff,
    elemWallTargetEdgeTo_val, elemWallTargetVertexEquiv_val, elemWallTargetVertexEquiv_val,
    elemWallEdgeSym2_eq]
  generalize ((elemWallEdges h)[k.1]'k.2) = e at hadj_k ⊢
  constructor
  · rintro (⟨hx_eq, hy_eq⟩ | ⟨hy_eq, hx_eq⟩)
    · have hx_eq' : (⟨x.1, x.2⟩ : Fin (elemWallNumVerts h)) = e.2 := Fin.ext hx_eq.symm
      have hy_eq' : (⟨y.1, y.2⟩ : Fin (elemWallNumVerts h)) = e.1 := Fin.ext hy_eq.symm
      rw [hx_eq', hy_eq']
      exact ⟨GM13.elementaryWallAdj_symm hadj_k, Sym2.eq_swap⟩
    · have hx_eq' : (⟨x.1, x.2⟩ : Fin (elemWallNumVerts h)) = e.1 := Fin.ext hx_eq.symm
      have hy_eq' : (⟨y.1, y.2⟩ : Fin (elemWallNumVerts h)) = e.2 := Fin.ext hy_eq.symm
      rw [hx_eq', hy_eq']
      exact ⟨hadj_k, rfl⟩
  · rintro ⟨_, hsym⟩
    rcases Sym2.eq_iff.mp hsym with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · have he1 : e.1 = ⟨x.1, x.2⟩ := elemWallVertCoord_injective h h1
      have he2 : e.2 = ⟨y.1, y.2⟩ := elemWallVertCoord_injective h h2
      exact Or.inr ⟨congrArg Fin.val he2, congrArg Fin.val he1⟩
    · have he1 : e.1 = ⟨y.1, y.2⟩ := elemWallVertCoord_injective h h1
      have he2 : e.2 = ⟨x.1, x.2⟩ := elemWallVertCoord_injective h h2
      exact Or.inl ⟨congrArg Fin.val he2, congrArg Fin.val he1⟩

/-- Canonical graph isomorphism between `targetGMGraph (elemWallNumVerts h) (elemWallEdges h)`
and `GM13.elementaryWall h`. -/
noncomputable def targetGMGraphIsoElementaryWall (h : ℕ) :
    Iso (targetGMGraph (elemWallNumVerts h) (elemWallEdges h)) (GM13.elementaryWall h) where
  vertexEquiv := elemWallTargetVertexEquiv h
  edgeEquiv := Equiv.ofBijective (elemWallTargetEdgeTo h) (elemWallTargetEdgeTo_bijective h)
  isLink_iff := targetGMGraph_elemWall_isLink_iff h

/-- Every elementary wall `targetGMGraph (elemWallNumVerts h) (elemWallEdges h)` is planar
(`IsPlanar`). -/
theorem isPlanarGraph_targetGMGraph_elemWall (h : ℕ) :
    IsPlanar (targetGMGraph (elemWallNumVerts h) (elemWallEdges h)) :=
  IsPlanar.of_iso (targetGMGraphIsoElementaryWall h) (GM13.isPlanar_elementaryWall h)

/-- **GM XIII (7.1) / (4.2) Threshold for the Elementary Wall**:
For every `h : ℕ`, there exists `ω₀ ≥ 2` such that `HasPlanarGridThreshold (elemWallEdges h) ω₀`. -/
theorem exists_elemWall_planarGridThreshold (h : ℕ) :
    ∃ ω₀ : ℕ, 2 ≤ ω₀ ∧ HasPlanarGridThreshold (elemWallEdges h) ω₀ :=
  exists_hasPlanarGridThreshold_of_isPlanarGraph (elemWallEdges h)
    (isPlanarGraph_targetGMGraph_elemWall h)

end GraphMinor.Compute
