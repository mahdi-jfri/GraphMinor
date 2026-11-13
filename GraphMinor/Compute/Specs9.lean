module

public import GraphMinor.Compute.Specs3
public import GraphMinor.Compute.Specs13
public import GraphMinor.Compute.Specs105
public import GraphMinor.Compute.Algorithm81
public import GraphMinor.Compute.Algorithm86
public import GraphMinor.GM13.Section9

/-!
# Shared Definitions and Algorithm Statements for GM XIII Section 9

This file defines on `WallOfHeight` (`GraphMinor/Compute/Wall.lean`) the Section 9 concepts from
Robertson and Seymour, *Graph Minors. XIII. The Disjoint Paths Problem*, J. Combin. Theory Ser. B
**63** (1995), 65–110 (pages 97–106), proves their equivalence with `GM13`'s definitions through
`WallOfHeight.toGMWall`, and states the Section 9 algorithms on the shared formats:
* **Section 1:** Wall simple graph, perimeter, inside vertices, corners, seed vertex, interior
  connectivity, and `(G \ X) ∪ H` (`wallUnionMultiDigraph`).
* **Section 2:** Subwalls (`WallOfHeight.subwallAt`, `WallOfHeight.IsSubwallOf`), brick distance
  bounds on shifted subwalls, compasses, dividing/non-dividing subwalls, crosses, flat subwalls,
  and `(l, m)`-stars, with bridges to `GM13` via `WallOfHeight.toGMWall`.
* **Section 3:** Statements of the algorithms of (9.1) (page 98), (9.2) (page 99), (9.4) (page
  102), (9.7) (page 103), and (9.9) (page 104) on the shared `MultiDigraph` and `WallOfHeight`
  formats, together with
  `ram3Case3Decoder : Case3BlockDecoder`.
-/

@[expose] public section

namespace GraphMinor.Compute

open SimpleGraph Classical
open scoped BigOperators Graph

theorem subgraphSUnion_isLink {α β : Type*} {G : Graph α β} {P_set : Set (Graph α β)}
    (hP : ∀ P ∈ P_set, P ≤ G) (b : β) (x y : α) :
    (GM09.subgraphSUnion G P_set).IsLink b x y ↔ ∃ P ∈ P_set, P.IsLink b x y := by
  constructor
  · intro hl
    have hb : b ∈ E(GM09.subgraphSUnion G P_set) := hl.edge_mem
    rw [GM09.edgeSet_subgraphSUnion hP, Set.mem_iUnion₂] at hb
    rcases hb with ⟨P, hP_mem, hbP⟩
    exact ⟨P, hP_mem, ((GM09.le_subgraphSUnion hP hP_mem).isLink_iff').mpr ⟨hl, hbP⟩⟩
  · rintro ⟨P, hP_mem, hlP⟩
    exact hlP.mono (GM09.le_subgraphSUnion hP hP_mem)

theorem walkSubgraph_toGMDigraph_isLink {n : ℕ} {G : MultiDigraph n} {a c : ℕ}
    (w : Surface.GraphWalk G.toGMDigraph.toGraph a c) (b : ℕ × ℕ × ℕ) (x y : ℕ) :
    (GM09.walkSubgraph w).IsLink b x y ↔
      b ∈ w.edges ∧ ((b.2.1 = x ∧ b.1 = y) ∨ (b.2.1 = y ∧ b.1 = x)) := by
  rw [GM09.walkSubgraph_isLink]
  refine and_congr_right fun hb => ?_
  have hbE : b ∈ G.toGMDigraph.edgeSet := GM09.walk_edges_subset_edgeSet w b hb
  exact ⟨fun h => h.2, fun h => ⟨hbE, h⟩⟩

namespace WallOfHeight

variable {h n : ℕ} {G : MultiDigraph n}

/-! ### Section 1: Wall Simple Graph, Perimeter, Inside, Seed, and `(G \ X) ∪ H` -/

/-- Boolean check whether `(u, v)` or `(v, u)` occurs as a consecutive pair in `L`. -/
def isListConsec {α : Type*} [DecidableEq α] (u v : α) : List α → Bool
  | [] => false
  | [_] => false
  | a :: b :: rest =>
    ((a == u && b == v) || (a == v && b == u)) || isListConsec u v (b :: rest)

theorem isListConsec_symm {α : Type*} [DecidableEq α] (u v : α) (L : List α) :
    isListConsec u v L = isListConsec v u L := by
  induction L with
  | nil => rfl
  | cons a rest ih =>
    cases rest with
    | nil => rfl
    | cons b tail =>
      simp only [isListConsec, ih]
      rw [Bool.or_comm (a == u && b == v) (a == v && b == u)]

theorem isListConsec_iff_mem_zip {α : Type*} [DecidableEq α] (u v : α) :
    ∀ L : List α,
      isListConsec u v L = true ↔
        (u, v) ∈ L.zip (L.drop 1) ∨ (v, u) ∈ L.zip (L.drop 1)
  | [] => by simp [isListConsec]
  | [_] => by simp [isListConsec]
  | a :: b :: rest => by
    simp only [isListConsec, Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq,
      isListConsec_iff_mem_zip u v (b :: rest), List.drop_succ_cons, List.drop_zero,
      List.zip_cons_cons, List.mem_cons, Prod.mk.injEq]
    tauto

/-- Decidable check for `W.IsWallEdge u v`. -/
def isWallEdgeBool (W : WallOfHeight h G) (u v : Fin n) : Bool :=
  (List.finRange (elemWallEdges h).length).any (fun k => isListConsec u v (W.subdivPathVerts k))

theorem isWallEdgeBool_eq_true_iff (W : WallOfHeight h G) (u v : Fin n) :
    W.isWallEdgeBool u v = true ↔ W.IsWallEdge u v := by
  unfold isWallEdgeBool IsWallEdge
  simp only [List.any_eq_true, List.mem_finRange, true_and, isListConsec_iff_mem_zip]

instance instDecidableIsWallEdge (W : WallOfHeight h G) (u v : Fin n) :
    Decidable (W.IsWallEdge u v) :=
  decidable_of_iff (W.isWallEdgeBool u v = true) (W.isWallEdgeBool_eq_true_iff u v)

theorem IsWallEdge.symm (W : WallOfHeight h G) {u v : Fin n} (huv : W.IsWallEdge u v) :
    W.IsWallEdge v u := by
  rcases huv with ⟨k, h1 | h2⟩
  · exact ⟨k, Or.inr h1⟩
  · exact ⟨k, Or.inl h2⟩

theorem isSimpleWalkList_adj_of_mem_zip {G : MultiDigraph n} {u v : Fin n} :
    ∀ {L : List (Fin n)},
      IsSimpleWalkList G L →
      (u, v) ∈ L.zip (L.drop 1) →
      G.toSimpleGraph.Adj u v
  | [], _, hmem => by simp at hmem
  | [_], _, hmem => by simp at hmem
  | a :: b :: rest, hw, hmem => by
    simp only [List.drop_succ_cons, List.drop_zero, List.zip_cons_cons, List.mem_cons,
      Prod.mk.injEq] at hmem
    rcases hmem with ⟨rfl, rfl⟩ | htail
    · exact hw.1
    · exact isSimpleWalkList_adj_of_mem_zip hw.2 htail

theorem mem_of_mem_zip_drop_one {α : Type*} {u v : α} :
    ∀ {L : List α}, (u, v) ∈ L.zip (L.drop 1) → u ∈ L ∧ v ∈ L
  | [], h => by simp at h
  | [_], h => by simp at h
  | a :: b :: rest, h => by
    simp only [List.drop_succ_cons, List.drop_zero, List.zip_cons_cons, List.mem_cons,
      Prod.mk.injEq] at h
    rcases h with ⟨rfl, rfl⟩ | htail
    · exact ⟨List.mem_cons_self, List.mem_cons_of_mem _ List.mem_cons_self⟩
    · rcases mem_of_mem_zip_drop_one htail with ⟨hu, hv⟩
      exact ⟨List.mem_cons_of_mem a hu, List.mem_cons_of_mem a hv⟩

theorem mem_vertexFinset_iff (W : WallOfHeight h G) (v : Fin n) :
    v ∈ W.vertexFinset ↔
      (∃ u : Fin (elemWallNumVerts h), W.branchVert u = v) ∨
      (∃ k : Fin (elemWallEdges h).length, v ∈ W.internalVerts k) := by
  unfold vertexFinset
  simp only [Finset.mem_union, Finset.mem_image, Finset.mem_univ,
    List.mem_toFinset, List.mem_flatMap, List.mem_finRange, true_and]

theorem mem_vertexFinset_of_mem_subdivPathVerts (W : WallOfHeight h G)
    {k : Fin (elemWallEdges h).length} {v : Fin n} (hv : v ∈ W.subdivPathVerts k) :
    v ∈ W.vertexFinset := by
  rw [W.mem_subdivPathVerts_iff k] at hv
  rw [W.mem_vertexFinset_iff]
  rcases hv with rfl | hint | rfl
  · exact Or.inl ⟨_, rfl⟩
  · exact Or.inr ⟨k, hint⟩
  · exact Or.inl ⟨_, rfl⟩

theorem IsWallEdge.adj_toSimpleGraph {W : WallOfHeight h G} (hW : W.IsValid)
    {u v : Fin n} (huv : W.IsWallEdge u v) :
    G.toSimpleGraph.Adj u v := by
  rcases huv with ⟨k, h1 | h2⟩
  · exact isSimpleWalkList_adj_of_mem_zip (hW.2.1 k).2 h1
  · exact (isSimpleWalkList_adj_of_mem_zip (hW.2.1 k).2 h2).symm

theorem IsWallEdge.ne {W : WallOfHeight h G} (hW : W.IsValid)
    {u v : Fin n} (huv : W.IsWallEdge u v) : u ≠ v :=
  (huv.adj_toSimpleGraph hW).ne

theorem IsWallEdge.mem_vertexFinset (W : WallOfHeight h G)
    {u v : Fin n} (huv : W.IsWallEdge u v) :
    u ∈ W.vertexFinset ∧ v ∈ W.vertexFinset := by
  rcases huv with ⟨k, h1 | h2⟩
  · rcases mem_of_mem_zip_drop_one h1 with ⟨hu, hv⟩
    exact ⟨W.mem_vertexFinset_of_mem_subdivPathVerts hu,
      W.mem_vertexFinset_of_mem_subdivPathVerts hv⟩
  · rcases mem_of_mem_zip_drop_one h2 with ⟨hv, hu⟩
    exact ⟨W.mem_vertexFinset_of_mem_subdivPathVerts hu,
      W.mem_vertexFinset_of_mem_subdivPathVerts hv⟩

/-- The underlying `SimpleGraph (Fin n)` of a wall `W : WallOfHeight h G`. -/
def wallSimpleGraph (W : WallOfHeight h G) : SimpleGraph (Fin n) where
  Adj u v := u ≠ v ∧ W.IsWallEdge u v
  symm := ⟨fun _ _ h => ⟨h.1.symm, h.2.symm⟩⟩
  loopless := ⟨fun _ h => h.1 rfl⟩

instance instDecidableRelWallSimpleGraphAdj (W : WallOfHeight h G) :
    DecidableRel W.wallSimpleGraph.Adj := by
  intro u v
  change Decidable (u ≠ v ∧ W.IsWallEdge u v)
  infer_instance

theorem wallSimpleGraph_adj_of_isValid {W : WallOfHeight h G} (hW : W.IsValid) (u v : Fin n) :
    W.wallSimpleGraph.Adj u v ↔ W.IsWallEdge u v :=
  ⟨fun h => h.2, fun h => ⟨h.ne hW, h⟩⟩

theorem wallSimpleGraph_le_of_isValid {W : WallOfHeight h G} (hW : W.IsValid) :
    W.wallSimpleGraph ≤ G.toSimpleGraph :=
  fun _ _ h => h.2.adj_toSimpleGraph hW

theorem isSubgraphOn_wallSimpleGraph (W : WallOfHeight h G) :
    IsSubgraphOn W.vertexFinset W.wallSimpleGraph :=
  fun _ _ h => h.2.mem_vertexFinset W

/-- Reinterpret `W : WallOfHeight h G` as a wall in another `G' : MultiDigraph n`. -/
def castGraph (W : WallOfHeight h G) (G' : MultiDigraph n) : WallOfHeight h G' where
  branchVert := W.branchVert
  internalVerts := W.internalVerts

@[simp]
theorem castGraph_subdivPathVerts (W : WallOfHeight h G) (G' : MultiDigraph n)
    (k : Fin (elemWallEdges h).length) :
    (W.castGraph G').subdivPathVerts k = W.subdivPathVerts k := rfl

@[simp]
theorem castGraph_vertexFinset (W : WallOfHeight h G) (G' : MultiDigraph n) :
    (W.castGraph G').vertexFinset = W.vertexFinset := rfl

@[simp]
theorem castGraph_encList (W : WallOfHeight h G) (G' : MultiDigraph n) :
    (W.castGraph G').encList = W.encList := rfl

@[simp]
theorem castGraph_isWallEdge (W : WallOfHeight h G) (G' : MultiDigraph n) (u v : Fin n) :
    (W.castGraph G').IsWallEdge u v ↔ W.IsWallEdge u v := Iff.rfl

@[simp]
theorem castGraph_vertCell (W : WallOfHeight h G) (G' : MultiDigraph n) (v : Fin n) :
    (W.castGraph G').vertCell v = W.vertCell v := rfl

@[simp]
theorem castGraph_brickDist (W : WallOfHeight h G) (G' : MultiDigraph n) (u v : Fin n) :
    (W.castGraph G').brickDist u v = W.brickDist u v := by
  unfold brickDist
  rw [castGraph_vertCell, castGraph_vertCell]

theorem isSimpleWalkList_of_congr {G₁ G₂ : MultiDigraph n} :
    ∀ {L : List (Fin n)},
      (∀ u v : Fin n, (u, v) ∈ L.zip (L.drop 1) → G₁.toSimpleGraph.Adj u v → G₂.toSimpleGraph.Adj u v) →
      IsSimpleWalkList G₁ L →
      IsSimpleWalkList G₂ L
  | [], _, _ => trivial
  | [_], _, _ => trivial
  | a :: b :: rest, himp, ⟨hab, hrest⟩ =>
    ⟨himp a b (by simp) hab,
      isSimpleWalkList_of_congr
        (fun u v huv => himp u v (List.mem_cons_of_mem _ huv)) hrest⟩

theorem isValid_castGraph {W : WallOfHeight h G} (hW : W.IsValid) {G' : MultiDigraph n}
    (hadj : ∀ u v : Fin n, W.IsWallEdge u v → G'.toSimpleGraph.Adj u v) :
    (W.castGraph G').IsValid := by
  refine ⟨hW.1, fun k => ⟨(hW.2.1 k).1, ?_⟩, hW.2.2.1, hW.2.2.2⟩
  apply isSimpleWalkList_of_congr (G₁ := G)
  · intro u v huv _
    exact hadj u v ⟨k, Or.inl huv⟩
  · exact (hW.2.1 k).2

/-- Vertex set of `W.toGMGraph hW` is `W.vertexFinset.toNatSet` (`1 ≤ h`). -/
theorem vertexSet_toGMGraph_eq (hh : 1 ≤ h) {W : WallOfHeight h G} (hW : W.IsValid) :
    V(W.toGMGraph hW) = W.vertexFinset.toNatSet := by
  have hveq := (W.toWallData hh hW).vertexSet_eq
  dsimp [toWallData] at hveq
  rw [hveq, W.image_branchVertAtCoord_eq]
  ext x
  simp only [Finset.toNatSet, Set.mem_image, Finset.mem_coe, W.mem_vertexFinset_iff,
    Set.mem_union, Set.mem_ofPred_eq, Set.mem_iUnion, exists_prop]
  constructor
  · rintro (⟨u, rfl⟩ | ⟨e, ⟨p, q, hpq, rfl⟩, hx⟩)
    · exact ⟨W.branchVert u, Or.inl ⟨u, rfl⟩, rfl⟩
    · rcases exists_elemWallEdgeSym2_of_elementaryWallAdj hpq with ⟨k, hk⟩
      rw [← hk, W.subdivPathOfSym2_elemWallEdgeSym2 hW k, W.vertexSet_subdivPathGraph hW k] at hx
      simp only [Set.mem_ofPred_eq, List.mem_map] at hx
      rcases hx with ⟨v, hv, rfl⟩
      exact ⟨v, (W.mem_vertexFinset_iff v).mp (W.mem_vertexFinset_of_mem_subdivPathVerts hv), rfl⟩
  · rintro ⟨v, ⟨u, rfl⟩ | ⟨k, hk⟩, rfl⟩
    · exact Or.inl ⟨u, rfl⟩
    · refine Or.inr ⟨elemWallEdgeSym2 h k, elemWallEdgeSym2_mem_edgeSet h k, ?_⟩
      rw [W.subdivPathOfSym2_elemWallEdgeSym2 hW k, W.vertexSet_subdivPathGraph hW k]
      simp only [Set.mem_ofPred_eq, List.mem_map]
      exact ⟨v, (W.mem_subdivPathVerts_iff k v).mpr (Or.inr (Or.inl hk)), rfl⟩

@[simp]
theorem vertexSet_toGMWall_eq (h2 : 2 ≤ h) (he : Even h) {W : WallOfHeight h G} (hW : W.IsValid) :
    V((W.toGMWall h2 he hW).graph) = W.vertexFinset.toNatSet :=
  W.vertexSet_toGMGraph_eq (by omega) hW

theorem edges_toGMGraphWalk_iff {G : MultiDigraph n} :
    ∀ {L : List (Fin n)} (hne : L ≠ []) (hw : IsSimpleWalkList G L) (b : ℕ × ℕ × ℕ),
      b ∈ (toGMGraphWalk hne hw).edges ↔
        ∃ u v : Fin n, (u, v) ∈ L.zip (L.drop 1) ∧ b = adjEdgeTriple G u v
  | [], hne, _, _ => False.elim (hne rfl)
  | [_], _, _, b => by simp [toGMGraphWalk, Surface.GraphWalk.edges]
  | a :: c :: rest, _, hw, b => by
    change b ∈ adjEdgeTriple G a c :: (toGMGraphWalk (List.cons_ne_nil c rest) hw.2).edges ↔ _
    rw [List.mem_cons, edges_toGMGraphWalk_iff (List.cons_ne_nil c rest) hw.2 b]
    simp only [List.drop_succ_cons, List.drop_zero, List.zip_cons_cons, List.mem_cons,
      Prod.mk.injEq]
    constructor
    · rintro (rfl | ⟨u, v, huv, rfl⟩)
      · exact ⟨a, c, Or.inl ⟨rfl, rfl⟩, rfl⟩
      · exact ⟨u, v, Or.inr huv, rfl⟩
    · rintro ⟨u, v, ⟨rfl, rfl⟩ | huv, rfl⟩
      · exact Or.inl rfl
      · exact Or.inr ⟨u, v, huv, rfl⟩

theorem edgeSet_toGMGraph_iff {W : WallOfHeight h G} (hW : W.IsValid) (b : ℕ × ℕ × ℕ) :
    b ∈ E(W.toGMGraph hW) ↔
      ∃ (k : Fin (elemWallEdges h).length) (u v : Fin n),
        (u, v) ∈ (W.subdivPathVerts k).zip ((W.subdivPathVerts k).drop 1) ∧
        b = adjEdgeTriple G u v := by
  unfold toGMGraph
  rw [GM09.edgeSet_subgraphSUnion]
  · simp only [Set.mem_iUnion, Set.mem_image]
    constructor
    · rintro ⟨P, ⟨⟨e, ⟨p, q, hpq, rfl⟩, rfl⟩, hb⟩⟩
      rcases exists_elemWallEdgeSym2_of_elementaryWallAdj hpq with ⟨k, hk⟩
      rw [← hk, W.subdivPathOfSym2_elemWallEdgeSym2 hW k] at hb
      unfold subdivPathGraph subdivGraphWalk at hb
      rw [GM09.edgeSet_walkSubgraph, Set.mem_ofPred_eq,
        edges_toGMGraphWalk_iff] at hb
      rcases hb with ⟨u, v, huv, rfl⟩
      exact ⟨k, u, v, huv, rfl⟩
    · rintro ⟨k, u, v, huv, rfl⟩
      refine ⟨W.subdivPathGraph hW k,
        ⟨⟨elemWallEdgeSym2 h k, elemWallEdgeSym2_mem_edgeSet h k,
          W.subdivPathOfSym2_elemWallEdgeSym2 hW k⟩, ?_⟩⟩
      unfold subdivPathGraph subdivGraphWalk
      rw [GM09.edgeSet_walkSubgraph, Set.mem_ofPred_eq, edges_toGMGraphWalk_iff]
      exact ⟨u, v, huv, rfl⟩
  · rintro P ⟨e, he, rfl⟩
    exact W.subdivPathOfSym2_le hW he

/-- If `G₁` and `G₂` agree on `adjEdgeTriple` along the edges of `W`, then `W.toGMWall` in `G₁`
and `(W.castGraph G₂).toGMWall` in `G₂` are equal as `GM13.Wall`s. -/
theorem toGMWall_castGraph_eq (h2 : 2 ≤ h) (he : Even h)
    {W : WallOfHeight h G} (hW : W.IsValid) {G' : MultiDigraph n}
    (hW' : (W.castGraph G').IsValid)
    (htriple : ∀ u v : Fin n, W.IsWallEdge u v → adjEdgeTriple G' u v = adjEdgeTriple G u v) :
    (W.castGraph G').toGMWall h2 he hW' = W.toGMWall h2 he hW := by
  have hsubdiv_eq : ∀ k : Fin (elemWallEdges h).length,
      (W.castGraph G').subdivPathGraph hW' k = W.subdivPathGraph hW k := by
    intro k
    apply Graph.ext
    · rw [vertexSet_subdivPathGraph, vertexSet_subdivPathGraph, castGraph_subdivPathVerts]
    · intro b x y
      unfold subdivPathGraph
      rw [walkSubgraph_toGMDigraph_isLink, walkSubgraph_toGMDigraph_isLink]
      refine and_congr_left fun _ => ?_
      unfold subdivGraphWalk
      rw [edges_toGMGraphWalk_iff, edges_toGMGraphWalk_iff]
      simp only [castGraph_subdivPathVerts]
      constructor <;>
      · rintro ⟨u, v, huv, rfl⟩
        have hwe : W.IsWallEdge u v := ⟨k, Or.inl huv⟩
        refine ⟨u, v, huv, ?_⟩
        first | exact (htriple u v hwe).symm | exact htriple u v hwe
  have hsym_eq : (W.castGraph G').subdivPathOfSym2 hW' = W.subdivPathOfSym2 hW := by
    funext e
    unfold subdivPathOfSym2
    cases findElemWallEdgeIdx h e with
    | none => rfl
    | some k => exact hsubdiv_eq k
  have hgraph_eq : (W.castGraph G').toGMGraph hW' = W.toGMGraph hW := by
    apply Graph.ext
    · rw [W.vertexSet_toGMGraph_eq (by omega) hW,
        (W.castGraph G').vertexSet_toGMGraph_eq (by omega) hW', castGraph_vertexFinset]
    · intro b x y
      unfold toGMGraph
      rw [subgraphSUnion_isLink, subgraphSUnion_isLink]
      · rw [hsym_eq]
      · rintro P ⟨e, he_mem, rfl⟩
        exact W.subdivPathOfSym2_le hW he_mem
      · rintro P ⟨e, he_mem, rfl⟩
        exact (W.castGraph G').subdivPathOfSym2_le hW' he_mem
  have hdata_eq : (W.castGraph G').toWallData (by omega) hW' = W.toWallData (by omega) hW := by
    unfold toWallData
    have hc_eq : (W.castGraph G').branchVertAtCoord = W.branchVertAtCoord := rfl
    simp only [hgraph_eq, hc_eq, hsym_eq]
  unfold toGMWall
  rw [hdata_eq]

/-! ### `(G \ X) ∪ H` on `MultiDigraph` (`wallUnionMultiDigraph`) -/

/-- The multigraph `(G \ X) ∪ H` of GM XIII (9.4) Step (2) and (9.7) (pages 102–103), retaining
all directed edges `(u, v)` of `G` such that `(u ∉ X ∧ v ∉ X) ∨ H.IsWallEdge u v`. -/
def wallUnionMultiDigraph (G : MultiDigraph n) (X : Finset (Fin n)) (H : WallOfHeight h G) :
    MultiDigraph n where
  edgeMult u v := if (u ∉ X ∧ v ∉ X) ∨ H.IsWallEdge u v then G.edgeMult u v else 0

theorem wallUnionMultiDigraph_edgeMult (G : MultiDigraph n) (X : Finset (Fin n))
    (H : WallOfHeight h G) (u v : Fin n) :
    (wallUnionMultiDigraph G X H).edgeMult u v =
      if (u ∉ X ∧ v ∉ X) ∨ H.IsWallEdge u v then G.edgeMult u v else 0 := rfl

theorem wallUnionMultiDigraph_edgeMult_le (G : MultiDigraph n) (X : Finset (Fin n))
    (H : WallOfHeight h G) (u v : Fin n) :
    (wallUnionMultiDigraph G X H).edgeMult u v ≤ G.edgeMult u v := by
  rw [wallUnionMultiDigraph_edgeMult]
  split_ifs <;> omega

theorem wallUnionMultiDigraph_numEdges_le (G : MultiDigraph n) (X : Finset (Fin n))
    (H : WallOfHeight h G) :
    (wallUnionMultiDigraph G X H).numEdges ≤ G.numEdges :=
  MultiDigraph.numEdges_mono (wallUnionMultiDigraph_edgeMult_le G X H)

theorem wallUnionMultiDigraph_adj (G : MultiDigraph n) (X : Finset (Fin n))
    (H : WallOfHeight h G) (u v : Fin n) :
    (wallUnionMultiDigraph G X H).toSimpleGraph.Adj u v ↔
      G.toSimpleGraph.Adj u v ∧ ((u ∉ X ∧ v ∉ X) ∨ H.IsWallEdge u v) := by
  rw [MultiDigraph.toSimpleGraph_adj, MultiDigraph.toSimpleGraph_adj,
    wallUnionMultiDigraph_edgeMult, wallUnionMultiDigraph_edgeMult]
  have hsymm : H.IsWallEdge v u ↔ H.IsWallEdge u v := ⟨IsWallEdge.symm H, IsWallEdge.symm H⟩
  have hcond_symm : ((v ∉ X ∧ u ∉ X) ∨ H.IsWallEdge v u) ↔ ((u ∉ X ∧ v ∉ X) ∨ H.IsWallEdge u v) := by
    rw [and_comm (a := v ∉ X), hsymm]
  simp only [hcond_symm]
  split_ifs with hcond
  · tauto
  · simp [hcond]

theorem wallUnionMultiDigraph_toSimpleGraph_le (G : MultiDigraph n) (X : Finset (Fin n))
    (H : WallOfHeight h G) :
    (wallUnionMultiDigraph G X H).toSimpleGraph ≤ G.toSimpleGraph :=
  fun u v h => ((wallUnionMultiDigraph_adj G X H u v).mp h).1

theorem adjEdgeTriple_wallUnionMultiDigraph (G : MultiDigraph n) (X : Finset (Fin n))
    (H : WallOfHeight h G) {u v : Fin n} (hwe : H.IsWallEdge u v) :
    adjEdgeTriple (wallUnionMultiDigraph G X H) u v = adjEdgeTriple G u v := by
  simp [adjEdgeTriple, wallUnionMultiDigraph_edgeMult, hwe]

theorem isValid_castGraph_wallUnionMultiDigraph {G : MultiDigraph n} (X : Finset (Fin n))
    {H : WallOfHeight h G} (hH : H.IsValid) :
    (H.castGraph (wallUnionMultiDigraph G X H)).IsValid := by
  apply H.isValid_castGraph hH
  intro u v hwe
  rw [wallUnionMultiDigraph_adj]
  exact ⟨hwe.adj_toSimpleGraph hH, Or.inr hwe⟩

@[simp]
theorem toGMWall_castGraph_wallUnionMultiDigraph (h2 : 2 ≤ h) (he : Even h)
    {G : MultiDigraph n} (X : Finset (Fin n)) {H : WallOfHeight h G} (hH : H.IsValid) :
    (H.castGraph (wallUnionMultiDigraph G X H)).toGMWall h2 he
      (isValid_castGraph_wallUnionMultiDigraph X hH) =
    H.toGMWall h2 he hH :=
  H.toGMWall_castGraph_eq h2 he hH (isValid_castGraph_wallUnionMultiDigraph X hH)
    (fun _ _ hwe => adjEdgeTriple_wallUnionMultiDigraph G X H hwe)

/-! ### Perimeter, Inside Vertices, Corners, and Seed Vertex on `WallOfHeight` -/

/-- Whether a coordinate `p : ℕ × ℕ` lies on the perimeter of the elementary wall of height `h`
(`GM13.elementaryWallPerimeterVerts`, page 89). -/
def isElemWallPerimCoord (h : ℕ) (p : ℕ × ℕ) : Bool :=
  decide (p.2 = 0 ∨ p.2 = h ∨ p.1 ≤ 1 ∨ 2 * h ≤ p.1)

/-- Whether the `k`-th edge of `elemWallEdges h` lies on the perimeter of the elementary wall of
height `h` (`E(GM13.elementaryWallPerimeter h)`, page 89). -/
def isElemWallPerimEdge (h : ℕ) (k : Fin (elemWallEdges h).length) : Bool :=
  let e := (elemWallEdges h)[k.1]'k.2
  isElemWallPerimCoord h (elemWallVertCoord h e.1) &&
  isElemWallPerimCoord h (elemWallVertCoord h e.2)

theorem isElemWallPerimEdge_iff_mem_elementaryWallPerimeter (h : ℕ)
    (k : Fin (elemWallEdges h).length) :
    isElemWallPerimEdge h k = true ↔
      elemWallEdgeSym2 h k ∈ E(GM13.elementaryWallPerimeter h) := by
  unfold isElemWallPerimEdge isElemWallPerimCoord GM13.elementaryWallPerimeter
    GM13.elementaryWallPerimeterVerts
  let e := (elemWallEdges h)[k.1]'k.2
  have hadj := elemWallEdge_elementaryWallAdj h k
  have hp_mem : elemWallVertCoord h e.1 ∈ GM13.elementaryWallVerts h :=
    elemWallVertCoord_mem_elementaryWallVerts h e.1
  have hq_mem : elemWallVertCoord h e.2 ∈ GM13.elementaryWallVerts h :=
    elemWallVertCoord_mem_elementaryWallVerts h e.2
  simp only [Bool.and_eq_true, decide_eq_true_eq]
  constructor
  · rintro ⟨hp, hq⟩
    exact ⟨elemWallVertCoord h e.1, elemWallVertCoord h e.2,
      ⟨hadj, rfl⟩, ⟨hp_mem, hp⟩, ⟨hq_mem, hq⟩⟩
  · rintro ⟨p, q, ⟨_, heq⟩, ⟨_, hp⟩, ⟨_, hq⟩⟩
    change s(elemWallVertCoord h e.1, elemWallVertCoord h e.2) = s(p, q) at heq
    rcases Sym2.eq_iff.mp heq with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact ⟨hp, hq⟩
    · exact ⟨hq, hp⟩

/-- The perimeter vertex set `V(C(W)) ⊆ V(W)` of a wall `W : WallOfHeight h G` (GM XIII page 89). -/
def perimeterFinset (W : WallOfHeight h G) : Finset (Fin n) :=
  (((List.finRange (elemWallEdges h).length).filter (isElemWallPerimEdge h)).flatMap
    W.subdivPathVerts).toFinset

/-- The inside vertex set `V(W) \ V(C(W))` of a wall `W : WallOfHeight h G` (GM XIII page 98). -/
def insideFinset (W : WallOfHeight h G) : Finset (Fin n) :=
  W.vertexFinset \ W.perimeterFinset

theorem mem_perimeterFinset_iff (W : WallOfHeight h G) (v : Fin n) :
    v ∈ W.perimeterFinset ↔
      ∃ k : Fin (elemWallEdges h).length,
        isElemWallPerimEdge h k = true ∧ v ∈ W.subdivPathVerts k := by
  unfold perimeterFinset
  simp only [List.mem_toFinset, List.mem_flatMap, List.mem_filter, List.mem_finRange, true_and]

theorem perimeterFinset_subset_vertexFinset (W : WallOfHeight h G) :
    W.perimeterFinset ⊆ W.vertexFinset := by
  intro v hv
  rcases (W.mem_perimeterFinset_iff v).mp hv with ⟨k, _, hvk⟩
  exact W.mem_vertexFinset_of_mem_subdivPathVerts hvk

@[simp]
theorem castGraph_perimeterFinset (W : WallOfHeight h G) (G' : MultiDigraph n) :
    (W.castGraph G').perimeterFinset = W.perimeterFinset := rfl

@[simp]
theorem castGraph_insideFinset (W : WallOfHeight h G) (G' : MultiDigraph n) :
    (W.castGraph G').insideFinset = W.insideFinset := rfl

theorem wall_ofData_subdivisionPaths_edgeEquiv {α β : Type*} {h : ℕ}
    (h2 : 2 ≤ h) (he : Even h) (D : GM13.WallData α β h)
    (e₀ : Sym2 (ℕ × ℕ)) (he₀' : e₀ ∈ E(GM13.elementaryWall h)) :
    (GM13.Wall.ofData h2 he D).subdivisionPaths
      ((GM13.Wall.ofData h2 he D).baseIso.edgeEquiv ⟨e₀, he₀'⟩).1 = D.P e₀ :=
  D.pathOf_lab he₀'

theorem vertexSet_perimeter_ofData {α β : Type*} {h : ℕ}
    (h2 : 2 ≤ h) (he : Even h) (D : GM13.WallData α β h) :
    V((GM13.Wall.ofData h2 he D).perimeter) =
      ⋃ e₀ ∈ E(GM13.elementaryWallPerimeter h), V(D.P e₀) := by
  unfold GM13.Wall.perimeter
  rw [GM09.vertexSet_subgraphSUnion]
  ext x
  simp only [Set.mem_iUnion, Set.mem_ofPred_eq, exists_prop]
  constructor
  · rintro ⟨P, ⟨e₀, he₀, rfl⟩, hxP⟩
    have he₀' : e₀ ∈ E(GM13.elementaryWall h) :=
      let ⟨p, q, hpq⟩ := he₀; ⟨p, q, hpq.1.1, hpq.1.2⟩
    rw [wall_ofData_subdivisionPaths_edgeEquiv h2 he D e₀ he₀'] at hxP
    exact ⟨e₀, he₀, hxP⟩
  · rintro ⟨e₀, he₀, hxP⟩
    have he₀' : e₀ ∈ E(GM13.elementaryWall h) :=
      let ⟨p, q, hpq⟩ := he₀; ⟨p, q, hpq.1.1, hpq.1.2⟩
    refine ⟨D.P e₀, ⟨e₀, he₀, (wall_ofData_subdivisionPaths_edgeEquiv h2 he D e₀ he₀').symm⟩, hxP⟩

/-- Bridge: `V((W.toGMWall h2 he hW).perimeter) = W.perimeterFinset.toNatSet`. -/
theorem vertexSet_perimeter_toGMWall_eq (h2 : 2 ≤ h) (he : Even h)
    {W : WallOfHeight h G} (hW : W.IsValid) :
    V((W.toGMWall h2 he hW).perimeter) = W.perimeterFinset.toNatSet := by
  unfold toGMWall
  rw [vertexSet_perimeter_ofData h2 he (W.toWallData (by omega) hW)]
  change (⋃ e₀ ∈ E(GM13.elementaryWallPerimeter h), V(W.subdivPathOfSym2 hW e₀)) =
    W.perimeterFinset.toNatSet
  ext x
  simp only [Set.mem_iUnion, exists_prop, Finset.toNatSet, Set.mem_image, Finset.mem_coe,
    W.mem_perimeterFinset_iff]
  constructor
  · rintro ⟨e₀, he₀, hxP⟩
    have he₀_copy := he₀
    rcases he₀ with ⟨p, q, ⟨hpq, rfl⟩, _, _⟩
    rcases exists_elemWallEdgeSym2_of_elementaryWallAdj hpq with ⟨k, hk⟩
    have hperim_k : isElemWallPerimEdge h k = true := by
      rw [isElemWallPerimEdge_iff_mem_elementaryWallPerimeter, hk]
      exact he₀_copy
    rw [← hk, W.subdivPathOfSym2_elemWallEdgeSym2 hW k, W.vertexSet_subdivPathGraph hW k] at hxP
    simp only [Set.mem_ofPred_eq, List.mem_map] at hxP
    rcases hxP with ⟨v, hvk, rfl⟩
    exact ⟨v, ⟨k, hperim_k, hvk⟩, rfl⟩
  · rintro ⟨v, ⟨k, hperim_k, hvk⟩, rfl⟩
    have he₀ : elemWallEdgeSym2 h k ∈ E(GM13.elementaryWallPerimeter h) :=
      (isElemWallPerimEdge_iff_mem_elementaryWallPerimeter h k).mp hperim_k
    refine ⟨elemWallEdgeSym2 h k, he₀, ?_⟩
    rw [W.subdivPathOfSym2_elemWallEdgeSym2 hW k, W.vertexSet_subdivPathGraph hW k]
    exact List.mem_map_of_mem hvk

/-- Bridge: `(W.toGMWall h2 he hW).insideVerts = W.insideFinset.toNatSet`. -/
theorem insideVerts_toGMWall_eq (h2 : 2 ≤ h) (he : Even h)
    {W : WallOfHeight h G} (hW : W.IsValid) :
    (W.toGMWall h2 he hW).insideVerts = W.insideFinset.toNatSet := by
  unfold GM13.Wall.insideVerts insideFinset
  rw [W.vertexSet_toGMWall_eq h2 he hW, W.vertexSet_perimeter_toGMWall_eq h2 he hW]
  ext x
  simp only [Set.mem_sdiff, Finset.toNatSet, Set.mem_image, Finset.mem_coe, Finset.mem_sdiff]
  constructor
  · rintro ⟨⟨u, hu, rfl⟩, hnot⟩
    exact ⟨u, ⟨hu, fun hp => hnot ⟨u, hp, rfl⟩⟩, rfl⟩
  · rintro ⟨u, ⟨hu, hnot⟩, rfl⟩
    refine ⟨⟨u, hu, rfl⟩, ?_⟩
    rintro ⟨v, hv, heq⟩
    exact hnot (Fin.ext heq ▸ hv)

/-- The `k`-th corner vertex (`k : Fin 4`) of `W : WallOfHeight h G` (`2 ≤ h`). -/
def cornerVert (W : WallOfHeight h G) (h2 : 2 ≤ h) (k : Fin 4) : Fin n :=
  W.branchVert (elemWallCornerIdx h2 k)

@[simp]
theorem toGMWall_corner_eq_cornerVert (h2 : 2 ≤ h) (he : Even h)
    {W : WallOfHeight h G} (hW : W.IsValid) (k : Fin 4) :
    (W.toGMWall h2 he hW).corner k = (W.cornerVert h2 k).1 :=
  W.toGMWall_corner h2 he hW k

theorem cornerVert_injective (h2 : 2 ≤ h) {W : WallOfHeight h G} (hW : W.IsValid) :
    Function.Injective (W.cornerVert h2) := by
  intro c₁ c₂ heq
  have hu_eq : elemWallCornerIdx h2 c₁ = elemWallCornerIdx h2 c₂ := hW.1 heq
  have hc_eq := congrArg (elemWallVertCoord h) hu_eq
  unfold elemWallCornerIdx at hc_eq
  rw [elemWallVertCoord_elemWallCoordIdx, elemWallVertCoord_elemWallCoordIdx] at hc_eq
  fin_cases c₁ <;> fin_cases c₂ <;> simp [GM13.elementaryWallCorner] at hc_eq <;> try rfl
  all_goals omega

theorem cornerVert_mem_perimeterFinset (W : WallOfHeight h G) (h2 : 2 ≤ h) (he : Even h)
    (c : Fin 4) :
    W.cornerVert h2 c ∈ W.perimeterFinset := by
  have hp_perim : GM13.elementaryWallCorner h c ∈ GM13.elementaryWallPerimeterVerts h := by
    refine ⟨elementaryWallCorner_mem_elementaryWallVerts h2 c, ?_⟩
    fin_cases c <;> simp [GM13.elementaryWallCorner]
  obtain ⟨q, hq_perim, hpq⟩ := GM13.exists_adj_elementaryWallPerimeterVerts' h2 he hp_perim
  obtain ⟨k, hk⟩ := exists_elemWallEdgeSym2_of_elementaryWallAdj hpq
  have hperim_k : isElemWallPerimEdge h k = true := by
    rw [isElemWallPerimEdge_iff_mem_elementaryWallPerimeter, hk]
    exact ⟨_, _, ⟨hpq, rfl⟩, hp_perim, hq_perim⟩
  rw [W.mem_perimeterFinset_iff]
  refine ⟨k, hperim_k, ?_⟩
  let e := (elemWallEdges h)[k.1]'k.2
  change s(elemWallVertCoord h e.1, elemWallVertCoord h e.2) =
    s(GM13.elementaryWallCorner h c, q) at hk
  rw [W.mem_subdivPathVerts_iff k]
  unfold cornerVert elemWallCornerIdx
  rcases Sym2.eq_iff.mp hk with ⟨h1, _⟩ | ⟨_, h2'⟩
  · left
    congr 1
    apply elemWallVertCoord_injective h
    rw [elemWallVertCoord_elemWallCoordIdx, h1]
  · right; right
    congr 1
    apply elemWallVertCoord_injective h
    rw [elemWallVertCoord_elemWallCoordIdx, h2']

/-- The distinguished interior seed vertex `W.branchVert (elemWallMiddle₁Idx h2)` at coordinate
`(h, h / 2)` of `W : WallOfHeight h G` (`2 ≤ h`). -/
def seedVert (W : WallOfHeight h G) (h2 : 2 ≤ h) : Fin n :=
  W.branchVert (elemWallMiddle₁Idx h2)

@[simp]
theorem toGMWall_middleVertex₁_eq_seedVert (h2 : 2 ≤ h) (he : Even h)
    {W : WallOfHeight h G} (hW : W.IsValid) :
    (W.toGMWall h2 he hW).middleVertex₁ = (W.seedVert h2).1 :=
  W.toGMWall_middleVertex₁ h2 he hW

theorem branchVert_mem_insideFinset_of_not_perimCoord {W : WallOfHeight h G} (hW : W.IsValid)
    (u : Fin (elemWallNumVerts h)) (hnot : isElemWallPerimCoord h (elemWallVertCoord h u) = false) :
    W.branchVert u ∈ W.insideFinset := by
  unfold insideFinset
  rw [Finset.mem_sdiff]
  refine ⟨(W.mem_vertexFinset_iff _).mpr (Or.inl ⟨u, rfl⟩), ?_⟩
  rw [W.mem_perimeterFinset_iff]
  rintro ⟨k, hperim_k, hmem_k⟩
  unfold isElemWallPerimEdge at hperim_k
  simp only [Bool.and_eq_true] at hperim_k
  rw [W.mem_subdivPathVerts_iff k] at hmem_k
  rcases hmem_k with heq1 | hint | heq2
  · have hu : u = ((elemWallEdges h)[k.1]'k.2).1 := hW.1 heq1
    subst hu
    rw [hnot] at hperim_k
    exact Bool.false_ne_true hperim_k.1
  · exact hW.2.2.1 k u hint
  · have hu : u = ((elemWallEdges h)[k.1]'k.2).2 := hW.1 heq2
    subst hu
    rw [hnot] at hperim_k
    exact Bool.false_ne_true hperim_k.2

theorem seedVert_mem_insideFinset (h2 : 2 ≤ h) {W : WallOfHeight h G} (hW : W.IsValid) :
    W.seedVert h2 ∈ W.insideFinset := by
  apply branchVert_mem_insideFinset_of_not_perimCoord hW
  unfold elemWallMiddle₁Idx
  rw [elemWallVertCoord_elemWallCoordIdx]
  unfold isElemWallPerimCoord GM13.elementaryWallMiddle₁
  simp only [decide_eq_false_iff_not, not_or]
  omega

/-! ### Section 2: Interior Connectivity, Subwalls, Compass, and Drawn Wall Distance -/

theorem isListConsec_getElem :
    ∀ (l : List (Fin n)) (i : ℕ) (hi : i + 1 < l.length),
      isListConsec (l[i]'(by omega)) (l[i + 1]'hi) l = true
  | [], _, hi => by simp at hi
  | [_], _, hi => by simp at hi
  | x :: y :: rest, 0, _ => by
    simp [isListConsec]
  | x :: y :: rest, i + 1, hi => by
    have hi' : i + 1 < (y :: rest).length := by simpa using hi
    have hrec := isListConsec_getElem (y :: rest) i hi'
    unfold isListConsec
    rw [Bool.or_eq_true]
    exact Or.inr hrec

theorem isWallEdge_subdivPathVerts_getElem (W : WallOfHeight h G)
    (k : Fin (elemWallEdges h).length) (i : ℕ) (hi : i + 1 < (W.subdivPathVerts k).length) :
    W.IsWallEdge ((W.subdivPathVerts k)[i]'(by omega)) ((W.subdivPathVerts k)[i + 1]'hi) :=
  ⟨k, (isListConsec_iff_mem_zip _ _ _).mp (isListConsec_getElem (W.subdivPathVerts k) i hi)⟩

private lemma reachable_head_of_consec_wallEdge {G' : SimpleGraph (Fin n)} {W : WallOfHeight h G}
    (hW : W.IsValid) (hsub : W.wallSimpleGraph ≤ G') :
    ∀ (l : List (Fin n)) (hl : l ≠ []),
      (∀ i (hi : i + 1 < l.length), W.IsWallEdge (l[i]'(by omega)) (l[i + 1]'hi)) →
      (∀ x ∈ l, x ∉ W.perimeterFinset) →
      ∀ a ∈ l,
        (restrictGraph G' (Finset.univ \ W.perimeterFinset)).Reachable (l.head hl) a
  | [], hl, _, _, _, _ => absurd rfl hl
  | [x], _, _, _, a, ha => by
    simp only [List.mem_singleton] at ha
    subst ha
    exact SimpleGraph.Reachable.refl _
  | x :: y :: rest, _, hconsec, hnotP, a, ha => by
    simp only [List.head_cons]
    have hxy_edge : W.IsWallEdge x y := by
      simpa using hconsec 0 (by simp)
    have hx_notP : x ∉ W.perimeterFinset := hnotP x (by simp)
    have hy_notP : y ∉ W.perimeterFinset := hnotP y (by simp)
    have hadj_xy : (restrictGraph G' (Finset.univ \ W.perimeterFinset)).Adj x y := by
      rw [restrictGraph_adj]
      refine ⟨by simp [hx_notP], by simp [hy_notP],
        hsub ((W.wallSimpleGraph_adj_of_isValid hW x y).mpr hxy_edge)⟩
    rcases List.mem_cons.mp ha with rfl | ha_tail
    · exact SimpleGraph.Reachable.refl _
    · have hrec := reachable_head_of_consec_wallEdge hW hsub (y :: rest) (List.cons_ne_nil y rest)
        (fun i hi => by
          have hi' : (i + 1) + 1 < (x :: y :: rest).length := by simpa using hi
          simpa using hconsec (i + 1) hi')
        (fun z hz => hnotP z (List.mem_cons_of_mem x hz))
        a ha_tail
      exact hadj_xy.reachable.trans hrec

theorem reachable_of_consec_wallEdge {G' : SimpleGraph (Fin n)} {W : WallOfHeight h G}
    (hW : W.IsValid) (hsub : W.wallSimpleGraph ≤ G')
    (l : List (Fin n))
    (hconsec : ∀ i (hi : i + 1 < l.length), W.IsWallEdge (l[i]'(by omega)) (l[i + 1]'hi))
    (hnotP : ∀ x ∈ l, x ∉ W.perimeterFinset)
    {a b : Fin n} (ha : a ∈ l) (hb : b ∈ l) :
    (restrictGraph G' (Finset.univ \ W.perimeterFinset)).Reachable a b := by
  have hl : l ≠ [] := List.ne_nil_of_mem ha
  exact (reachable_head_of_consec_wallEdge hW hsub l hl hconsec hnotP a ha).symm.trans
    (reachable_head_of_consec_wallEdge hW hsub l hl hconsec hnotP b hb)

theorem internalVerts_not_mem_perimeterFinset_of_not_perimEdge {W : WallOfHeight h G}
    (hW : W.IsValid) (k : Fin (elemWallEdges h).length)
    (hnot_perim : isElemWallPerimEdge h k = false)
    {v : Fin n} (hv : v ∈ W.internalVerts k) :
    v ∉ W.perimeterFinset := by
  rw [W.mem_perimeterFinset_iff]
  rintro ⟨k', hperim_k', hmem_k'⟩
  have hne : k' ≠ k := by
    intro heq
    subst heq
    rw [hnot_perim] at hperim_k'
    exact Bool.false_ne_true hperim_k'
  rw [W.mem_subdivPathVerts_iff k'] at hmem_k'
  rcases hmem_k' with heq1 | hint' | heq2
  · exact hW.2.2.1 k _ (heq1 ▸ hv)
  · exact List.disjoint_left.mp (hW.2.2.2 k k' hne.symm) hv hint'
  · exact hW.2.2.1 k _ (heq2 ▸ hv)

theorem reachable_branchVert_of_not_perim_endpoints {G' : SimpleGraph (Fin n)}
    {W : WallOfHeight h G} (hW : W.IsValid) (hsub : W.wallSimpleGraph ≤ G')
    (k : Fin (elemWallEdges h).length)
    (hnot1 : isElemWallPerimCoord h (elemWallVertCoord h ((elemWallEdges h)[k.1]'k.2).1) = false)
    (hnot2 : isElemWallPerimCoord h (elemWallVertCoord h ((elemWallEdges h)[k.1]'k.2).2) = false) :
    (restrictGraph G' (Finset.univ \ W.perimeterFinset)).Reachable
      (W.branchVert ((elemWallEdges h)[k.1]'k.2).1)
      (W.branchVert ((elemWallEdges h)[k.1]'k.2).2) := by
  have hnot_perim : isElemWallPerimEdge h k = false := by
    unfold isElemWallPerimEdge
    simp [hnot1]
  have hb1 : W.branchVert ((elemWallEdges h)[k.1]'k.2).1 ∉ W.perimeterFinset :=
    (Finset.mem_sdiff.mp
      (W.branchVert_mem_insideFinset_of_not_perimCoord hW ((elemWallEdges h)[k.1]'k.2).1 hnot1)).2
  have hb2 : W.branchVert ((elemWallEdges h)[k.1]'k.2).2 ∉ W.perimeterFinset :=
    (Finset.mem_sdiff.mp
      (W.branchVert_mem_insideFinset_of_not_perimCoord hW ((elemWallEdges h)[k.1]'k.2).2 hnot2)).2
  refine reachable_of_consec_wallEdge hW hsub (W.subdivPathVerts k)
    (W.isWallEdge_subdivPathVerts_getElem k) ?_
    ((W.mem_subdivPathVerts_iff k _).mpr (Or.inl rfl))
    ((W.mem_subdivPathVerts_iff k _).mpr (Or.inr (Or.inr rfl)))
  intro x hx
  rw [W.mem_subdivPathVerts_iff k] at hx
  rcases hx with rfl | hint | rfl
  · exact hb1
  · exact W.internalVerts_not_mem_perimeterFinset_of_not_perimEdge hW k hnot_perim hint
  · exact hb2

theorem exists_branchVert_reachable_of_mem_internalVerts {G' : SimpleGraph (Fin n)}
    {W : WallOfHeight h G} (hW : W.IsValid) (hsub : W.wallSimpleGraph ≤ G')
    (k : Fin (elemWallEdges h).length) {v : Fin n} (hv : v ∈ W.internalVerts k)
    (hv_notP : v ∉ W.perimeterFinset) :
    ∃ u : Fin (elemWallNumVerts h),
      isElemWallPerimCoord h (elemWallVertCoord h u) = false ∧
      (restrictGraph G' (Finset.univ \ W.perimeterFinset)).Reachable (W.branchVert u) v := by
  have hnot_perim : isElemWallPerimEdge h k = false := by
    by_contra hperim
    simp only [Bool.not_eq_false] at hperim
    exact hv_notP ((W.mem_perimeterFinset_iff v).mpr
      ⟨k, hperim, (W.mem_subdivPathVerts_iff k v).mpr (Or.inr (Or.inl hv))⟩)
  let u₁ := ((elemWallEdges h)[k.1]'k.2).1
  let u₂ := ((elemWallEdges h)[k.1]'k.2).2
  have hsubdiv_eq : W.subdivPathVerts k = W.branchVert u₁ :: (W.internalVerts k ++ [W.branchVert u₂]) := rfl
  have hnot_end :
      isElemWallPerimCoord h (elemWallVertCoord h u₁) = false ∨
      isElemWallPerimCoord h (elemWallVertCoord h u₂) = false := by
    unfold isElemWallPerimEdge at hnot_perim
    exact Bool.and_eq_false_iff.mp hnot_perim
  rcases hnot_end with hnot1 | hnot2
  · refine ⟨u₁, hnot1, ?_⟩
    let l₁ := W.branchVert u₁ :: W.internalVerts k
    have hb1 : W.branchVert u₁ ∉ W.perimeterFinset :=
      (Finset.mem_sdiff.mp
        (W.branchVert_mem_insideFinset_of_not_perimCoord hW u₁ hnot1)).2
    refine reachable_of_consec_wallEdge hW hsub l₁ ?_ ?_
      List.mem_cons_self (List.mem_cons_of_mem _ hv)
    · intro i hi
      have hlen : (W.subdivPathVerts k).length = l₁.length + 1 := by
        simp [hsubdiv_eq, l₁]
      have hi' : i + 1 < (W.subdivPathVerts k).length := by omega
      have heq_l : W.subdivPathVerts k = l₁ ++ [W.branchVert u₂] := by
        simp [hsubdiv_eq, l₁]
      have h1 : (W.subdivPathVerts k)[i]'(by omega) = l₁[i]'(by omega) := by
        simp only [heq_l]
        exact List.getElem_append_left (by omega)
      have h2 : (W.subdivPathVerts k)[i + 1]'hi' = l₁[i + 1]'hi := by
        simp only [heq_l]
        exact List.getElem_append_left hi
      rw [← h1, ← h2]
      exact W.isWallEdge_subdivPathVerts_getElem k i hi'
    · intro x hx
      simp only [l₁, List.mem_cons] at hx
      rcases hx with rfl | hx_int
      · exact hb1
      · exact W.internalVerts_not_mem_perimeterFinset_of_not_perimEdge hW k hnot_perim hx_int
  · refine ⟨u₂, hnot2, ?_⟩
    let l₂ := W.internalVerts k ++ [W.branchVert u₂]
    have hb2 : W.branchVert u₂ ∉ W.perimeterFinset :=
      (Finset.mem_sdiff.mp
        (W.branchVert_mem_insideFinset_of_not_perimCoord hW u₂ hnot2)).2
    have hmem_b2 : W.branchVert u₂ ∈ l₂ :=
      List.mem_append_right _ (List.mem_singleton.mpr rfl)
    have hmem_v : v ∈ l₂ := List.mem_append_left _ hv
    refine reachable_of_consec_wallEdge hW hsub l₂ ?_ ?_ hmem_b2 hmem_v
    · intro i hi
      have heq_l : W.subdivPathVerts k = W.branchVert u₁ :: l₂ := hsubdiv_eq
      have hlen : (W.subdivPathVerts k).length = l₂.length + 1 := by
        rw [heq_l, List.length_cons]
      have hi' : (i + 1) + 1 < (W.subdivPathVerts k).length := by omega
      have h1 : (W.subdivPathVerts k)[i + 1]'(by omega) = l₂[i]'(by omega) := by
        simp only [heq_l, List.getElem_cons_succ]
      have h2 : (W.subdivPathVerts k)[(i + 1) + 1]'hi' = l₂[i + 1]'hi := by
        simp only [heq_l, List.getElem_cons_succ]
      rw [← h1, ← h2]
      exact W.isWallEdge_subdivPathVerts_getElem k (i + 1) hi'
    · intro x hx
      simp only [l₂, List.mem_append, List.mem_singleton] at hx
      rcases hx with hx_int | rfl
      · exact W.internalVerts_not_mem_perimeterFinset_of_not_perimEdge hW k hnot_perim hx_int
      · exact hb2

theorem mem_elementaryWallVerts_of_bounds {p : ℕ × ℕ}
    (hx1 : 1 ≤ p.1) (hx2 : p.1 ≤ 2 * h) (hy : p.2 ≤ h) :
    p ∈ GM13.elementaryWallVerts h := by
  refine ⟨by omega, hy, ?_, ?_⟩
  · intro heq
    have : p.1 = 0 := congrArg Prod.fst heq
    omega
  · intro heq
    have : p.1 = 2 * h + 1 := congrArg Prod.fst heq
    omega

theorem not_perimCoord_of_branchVert_not_mem_perimeterFinset (h2 : 2 ≤ h)
    {W : WallOfHeight h G} (u : Fin (elemWallNumVerts h))
    (hnotP : W.branchVert u ∉ W.perimeterFinset) :
    isElemWallPerimCoord h (elemWallVertCoord h u) = false := by
  by_contra hperim
  simp only [Bool.not_eq_false] at hperim
  set p := elemWallVertCoord h u
  have hp_mem : p ∈ GM13.elementaryWallVerts h := elemWallVertCoord_mem_elementaryWallVerts h u
  rcases hp_mem with ⟨hx_le, hy_le, hne_00, hne_top⟩
  have hperim' : p.2 = 0 ∨ p.2 = h ∨ p.1 ≤ 1 ∨ 2 * h ≤ p.1 := by
    unfold isElemWallPerimCoord at hperim
    simpa [decide_eq_true_eq, or_assoc] using hperim
  -- Construct a horizontal neighbor q on the perimeter
  have hex_q : ∃ q : ℕ × ℕ, ∃ hq : q ∈ GM13.elementaryWallVerts h,
      isElemWallPerimCoord h q = true ∧
      (isElemWallEdgeCoord p q = true ∨ isElemWallEdgeCoord q p = true) := by
    by_cases hy0 : p.2 = 0
    · have hx_ge1 : 1 ≤ p.1 := by
        by_contra hlt
        have hx_eq : p.1 = 0 := by omega
        exact hne_00 (Prod.ext hx_eq hy0)
      by_cases hx1 : p.1 = 1
      · refine ⟨(2, 0), mem_elementaryWallVerts_of_bounds (by omega) (by omega) (by omega), ?_, Or.inl ?_⟩
        · unfold isElemWallPerimCoord; simp
        · unfold isElemWallEdgeCoord; simp [hx1, hy0]
      · refine ⟨(p.1 - 1, 0), mem_elementaryWallVerts_of_bounds (by omega) (by omega) (by omega), ?_, Or.inr ?_⟩
        · unfold isElemWallPerimCoord; simp
        · unfold isElemWallEdgeCoord
          simp only [Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq]
          exact Or.inl ⟨by omega, by omega⟩
    · by_cases hyh : p.2 = h
      · have hx_lt : p.1 ≤ 2 * h := by
          by_contra hgt
          have hx_eq : p.1 = 2 * h + 1 := by omega
          exact hne_top (Prod.ext hx_eq hyh)
        by_cases hx0 : p.1 = 0
        · refine ⟨(1, h), mem_elementaryWallVerts_of_bounds (by omega) (by omega) (by omega), ?_, Or.inl ?_⟩
          · unfold isElemWallPerimCoord; simp
          · unfold isElemWallEdgeCoord; simp [hx0, hyh]
        · refine ⟨(p.1 - 1, h), ?_, ?_, Or.inr ?_⟩
          · refine ⟨by omega, by omega, ?_, ?_⟩
            · intro h1; have := congrArg Prod.snd h1; dsimp at this; omega
            · intro h1; have := congrArg Prod.fst h1; dsimp at this; omega
          · unfold isElemWallPerimCoord; simp
          · unfold isElemWallEdgeCoord
            simp only [Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq]
            exact Or.inl ⟨by omega, by omega⟩
      · -- 0 < p.2 < h, so either p.1 ≤ 1 or 2 * h ≤ p.1
        rcases hperim' with hy0' | hyh' | hx_le1 | hx_ge2h
        · exact absurd hy0' hy0
        · exact absurd hyh' hyh
        · by_cases hx0 : p.1 = 0
          · refine ⟨(1, p.2), mem_elementaryWallVerts_of_bounds (by omega) (by omega) hy_le, ?_, Or.inl ?_⟩
            · unfold isElemWallPerimCoord; simp
            · unfold isElemWallEdgeCoord; simp [hx0]
          · have hx1 : p.1 = 1 := by omega
            refine ⟨(0, p.2), ?_, ?_, Or.inr ?_⟩
            · refine ⟨by omega, hy_le, ?_, ?_⟩
              · intro h1; exact hy0 (congrArg Prod.snd h1)
              · intro h1; have := congrArg Prod.fst h1; dsimp at this; omega
            · unfold isElemWallPerimCoord; simp
            · unfold isElemWallEdgeCoord; simp [hx1]
        · by_cases hx2h : p.1 = 2 * h
          · refine ⟨(2 * h + 1, p.2), ?_, ?_, Or.inl ?_⟩
            · refine ⟨by omega, hy_le, ?_, ?_⟩
              · intro h1; have := congrArg Prod.fst h1; dsimp at this; omega
              · intro h1; exact hyh (congrArg Prod.snd h1)
            · unfold isElemWallPerimCoord; simp
            · unfold isElemWallEdgeCoord; simp [hx2h]
          · have hx2h1 : p.1 = 2 * h + 1 := by omega
            refine ⟨(2 * h, p.2), mem_elementaryWallVerts_of_bounds (by omega) (by omega) hy_le, ?_, Or.inr ?_⟩
            · unfold isElemWallPerimCoord; simp
            · unfold isElemWallEdgeCoord; simp [hx2h1]
  rcases hex_q with ⟨q, hq, hq_perim, hedge⟩
  let v := elemWallCoordIdx h q hq
  have hv_coord : elemWallVertCoord h v = q := elemWallVertCoord_elemWallCoordIdx h hq
  rcases hedge with hpq | hqp
  · have hmem_e : (u, v) ∈ elemWallEdges h := by
      rw [mem_elemWallEdges_iff]
      simpa [p, hv_coord] using hpq
    rcases List.mem_iff_getElem.mp hmem_e with ⟨idx, hidx, hget⟩
    let k : Fin (elemWallEdges h).length := ⟨idx, hidx⟩
    have hk_perim : isElemWallPerimEdge h k = true := by
      unfold isElemWallPerimEdge
      have hk_eq : (elemWallEdges h)[k.1]'k.2 = (u, v) := hget
      rw [hk_eq, Bool.and_eq_true]
      exact ⟨by simpa [p] using hperim, by simpa [hv_coord] using hq_perim⟩
    exact hnotP ((W.mem_perimeterFinset_iff _).mpr ⟨k, hk_perim, by
      rw [W.mem_subdivPathVerts_iff k]
      left
      have hk_eq : (elemWallEdges h)[k.1]'k.2 = (u, v) := hget
      rw [hk_eq]⟩)
  · have hmem_e : (v, u) ∈ elemWallEdges h := by
      rw [mem_elemWallEdges_iff]
      simpa [p, hv_coord] using hqp
    rcases List.mem_iff_getElem.mp hmem_e with ⟨idx, hidx, hget⟩
    let k : Fin (elemWallEdges h).length := ⟨idx, hidx⟩
    have hk_perim : isElemWallPerimEdge h k = true := by
      unfold isElemWallPerimEdge
      have hk_eq : (elemWallEdges h)[k.1]'k.2 = (v, u) := hget
      rw [hk_eq, Bool.and_eq_true]
      exact ⟨by simpa [hv_coord] using hq_perim, by simpa [p] using hperim⟩
    exact hnotP ((W.mem_perimeterFinset_iff _).mpr ⟨k, hk_perim, by
      rw [W.mem_subdivPathVerts_iff k]
      right; right
      have hk_eq : (elemWallEdges h)[k.1]'k.2 = (v, u) := hget
      rw [hk_eq]⟩)

/-- Interior coordinate `(x, y)` of the elementary wall of height `h`:
`2 ≤ x < 2 * h` and `1 ≤ y < h`. -/
def IsInteriorElemCoord (h : ℕ) (p : ℕ × ℕ) : Prop :=
  2 ≤ p.1 ∧ p.1 < 2 * h ∧ 1 ≤ p.2 ∧ p.2 < h

theorem IsInteriorElemCoord.mem_elementaryWallVerts {p : ℕ × ℕ} (hp : IsInteriorElemCoord h p) :
    p ∈ GM13.elementaryWallVerts h := by
  rcases hp with ⟨hx1, hx2, hy1, hy2⟩
  exact mem_elementaryWallVerts_of_bounds (by omega) (by omega) (by omega)

theorem IsInteriorElemCoord.not_perimCoord {p : ℕ × ℕ} (hp : IsInteriorElemCoord h p) :
    isElemWallPerimCoord h p = false := by
  rcases hp with ⟨hx1, hx2, hy1, hy2⟩
  unfold isElemWallPerimCoord
  simp only [decide_eq_false_iff_not, not_or]
  omega

theorem isInteriorElemCoord_of_not_perimCoord (u : Fin (elemWallNumVerts h))
    (hnot : isElemWallPerimCoord h (elemWallVertCoord h u) = false) :
    IsInteriorElemCoord h (elemWallVertCoord h u) := by
  have hp := elemWallVertCoord_mem_elementaryWallVerts h u
  rcases hp with ⟨hx_le, hy_le, _, _⟩
  unfold isElemWallPerimCoord at hnot
  simp only [decide_eq_false_iff_not, not_or] at hnot
  refine ⟨by omega, by omega, by omega, by omega⟩

/-- The branch vertex of `W` at an interior coordinate `p`. -/
def interiorBranchVert (W : WallOfHeight h G) (p : ℕ × ℕ) (hp : IsInteriorElemCoord h p) : Fin n :=
  W.branchVert (elemWallCoordIdx h p hp.mem_elementaryWallVerts)

theorem reachable_interiorBranchVert_of_edge {G' : SimpleGraph (Fin n)}
    {W : WallOfHeight h G} (hW : W.IsValid) (hsub : W.wallSimpleGraph ≤ G')
    {p q : ℕ × ℕ} (hp : IsInteriorElemCoord h p) (hq : IsInteriorElemCoord h q)
    (hedge : isElemWallEdgeCoord p q = true) :
    (restrictGraph G' (Finset.univ \ W.perimeterFinset)).Reachable
      (W.interiorBranchVert p hp) (W.interiorBranchVert q hq) := by
  let u := elemWallCoordIdx h p hp.mem_elementaryWallVerts
  let v := elemWallCoordIdx h q hq.mem_elementaryWallVerts
  have hu : elemWallVertCoord h u = p := elemWallVertCoord_elemWallCoordIdx h hp.mem_elementaryWallVerts
  have hv : elemWallVertCoord h v = q := elemWallVertCoord_elemWallCoordIdx h hq.mem_elementaryWallVerts
  have hmem_e : (u, v) ∈ elemWallEdges h := by
    rw [mem_elemWallEdges_iff, hu, hv]
    exact hedge
  rcases List.mem_iff_getElem.mp hmem_e with ⟨idx, hidx, hget⟩
  let k : Fin (elemWallEdges h).length := ⟨idx, hidx⟩
  have hk1 : ((elemWallEdges h)[k.1]'k.2).1 = u := congrArg Prod.fst hget
  have hk2 : ((elemWallEdges h)[k.1]'k.2).2 = v := congrArg Prod.snd hget
  have hreach := W.reachable_branchVert_of_not_perim_endpoints hW hsub k
    (by rw [hk1, hu]; exact hp.not_perimCoord)
    (by rw [hk2, hv]; exact hq.not_perimCoord)
  simpa [interiorBranchVert, u, v, hk1, hk2] using hreach

theorem reachable_interiorBranchVert_horiz {G' : SimpleGraph (Fin n)}
    {W : WallOfHeight h G} (hW : W.IsValid) (hsub : W.wallSimpleGraph ≤ G')
    (y : ℕ) (hy1 : 1 ≤ y) (hy2 : y < h) :
    ∀ d : ℕ, ∀ hd : 2 + d < 2 * h,
      (restrictGraph G' (Finset.univ \ W.perimeterFinset)).Reachable
        (W.interiorBranchVert (2, y) ⟨by omega, by omega, hy1, hy2⟩)
        (W.interiorBranchVert (2 + d, y) ⟨by omega, hd, hy1, hy2⟩)
  | 0, _ => SimpleGraph.Reachable.refl _
  | d + 1, hd => by
    have hprev := reachable_interiorBranchVert_horiz hW hsub y hy1 hy2 d (by omega)
    have hstep : (restrictGraph G' (Finset.univ \ W.perimeterFinset)).Reachable
        (W.interiorBranchVert (2 + d, y) ⟨by omega, by omega, hy1, hy2⟩)
        (W.interiorBranchVert (2 + (d + 1), y) ⟨by omega, hd, hy1, hy2⟩) := by
      apply W.reachable_interiorBranchVert_of_edge hW hsub
      unfold isElemWallEdgeCoord
      simp [Nat.add_assoc]
    exact hprev.trans hstep

theorem reachable_interiorBranchVert_vert_step {G' : SimpleGraph (Fin n)} (h2 : 2 ≤ h)
    {W : WallOfHeight h G} (hW : W.IsValid) (hsub : W.wallSimpleGraph ≤ G')
    (y : ℕ) (hy1 : 1 ≤ y) (hy2 : y + 1 < h) :
    (restrictGraph G' (Finset.univ \ W.perimeterFinset)).Reachable
      (W.interiorBranchVert (2, y) ⟨by omega, by omega, hy1, by omega⟩)
      (W.interiorBranchVert (2, y + 1) ⟨by omega, by omega, by omega, hy2⟩) := by
  by_cases hodd : (2 + y) % 2 = 1
  · apply W.reachable_interiorBranchVert_of_edge hW hsub
    unfold isElemWallEdgeCoord
    simp [hodd]
  · have hodd3 : (3 + y) % 2 = 1 := by omega
    have h1 := W.reachable_interiorBranchVert_horiz hW hsub y hy1 (by omega) 1 (by omega)
    have h2' : (restrictGraph G' (Finset.univ \ W.perimeterFinset)).Reachable
        (W.interiorBranchVert (3, y) ⟨by omega, by omega, hy1, by omega⟩)
        (W.interiorBranchVert (3, y + 1) ⟨by omega, by omega, by omega, hy2⟩) := by
      apply W.reachable_interiorBranchVert_of_edge hW hsub
      unfold isElemWallEdgeCoord
      simp [hodd3]
    have h3 := (W.reachable_interiorBranchVert_horiz hW hsub (y + 1) (by omega) hy2 1 (by omega)).symm
    exact h1.trans (h2'.trans h3)

theorem reachable_interiorBranchVert_from_base {G' : SimpleGraph (Fin n)} (h2 : 2 ≤ h)
    {W : WallOfHeight h G} (hW : W.IsValid) (hsub : W.wallSimpleGraph ≤ G') :
    ∀ d : ℕ, ∀ hd : 1 + d < h,
      (restrictGraph G' (Finset.univ \ W.perimeterFinset)).Reachable
        (W.interiorBranchVert (2, 1) ⟨by omega, by omega, by omega, by omega⟩)
        (W.interiorBranchVert (2, 1 + d) ⟨by omega, by omega, by omega, hd⟩)
  | 0, _ => SimpleGraph.Reachable.refl _
  | d + 1, hd => by
    have hprev := reachable_interiorBranchVert_from_base h2 hW hsub d (by omega)
    have hstep := reachable_interiorBranchVert_vert_step h2 hW hsub (1 + d) (by omega) hd
    exact hprev.trans hstep

theorem reachable_interiorBranchVert_any {G' : SimpleGraph (Fin n)} (h2 : 2 ≤ h)
    {W : WallOfHeight h G} (hW : W.IsValid) (hsub : W.wallSimpleGraph ≤ G')
    {p q : ℕ × ℕ} (hp : IsInteriorElemCoord h p) (hq : IsInteriorElemCoord h q) :
    (restrictGraph G' (Finset.univ \ W.perimeterFinset)).Reachable
      (W.interiorBranchVert p hp) (W.interiorBranchVert q hq) := by
  have to_base : ∀ (r : ℕ × ℕ) (hr : IsInteriorElemCoord h r),
      (restrictGraph G' (Finset.univ \ W.perimeterFinset)).Reachable
        (W.interiorBranchVert (2, 1) ⟨by omega, by omega, by omega, by omega⟩)
        (W.interiorBranchVert r hr) := by
    intro r hr
    rcases hr with ⟨hrx1, hrx2, hry1, hry2⟩
    have hy := reachable_interiorBranchVert_from_base h2 hW hsub (r.2 - 1) (by omega)
    have hx := reachable_interiorBranchVert_horiz hW hsub r.2 hry1 hry2 (r.1 - 2) (by omega)
    have heq_y : (2, 1 + (r.2 - 1)) = (2, r.2) := Prod.ext rfl (by omega)
    have heq_x : (2 + (r.1 - 2), r.2) = r := Prod.ext (by omega) rfl
    have hy' : (restrictGraph G' (Finset.univ \ W.perimeterFinset)).Reachable
        (W.interiorBranchVert (2, 1) ⟨by omega, by omega, by omega, by omega⟩)
        (W.interiorBranchVert (2, r.2) ⟨by omega, by omega, hry1, hry2⟩) := by
      simpa [interiorBranchVert, heq_y] using hy
    have hx' : (restrictGraph G' (Finset.univ \ W.perimeterFinset)).Reachable
        (W.interiorBranchVert (2, r.2) ⟨by omega, by omega, hry1, hry2⟩)
        (W.interiorBranchVert r ⟨hrx1, hrx2, hry1, hry2⟩) := by
      simpa [interiorBranchVert, heq_x] using hx
    exact hy'.trans hx'
  exact (to_base p hp).symm.trans (to_base q hq)

/-- Every vertex `v ∈ W.insideFinset` is reachable from `W.seedVert h2` in
`restrictGraph G' (Finset.univ \ W.perimeterFinset)` whenever `W.wallSimpleGraph ≤ G'`. -/
theorem reachable_seedVert_of_mem_insideFinset {G' : SimpleGraph (Fin n)}
    (h2 : 2 ≤ h) {W : WallOfHeight h G} (hW : W.IsValid)
    (hsub : W.wallSimpleGraph ≤ G') {v : Fin n} (hv : v ∈ W.insideFinset) :
    (restrictGraph G' (Finset.univ \ W.perimeterFinset)).Reachable (W.seedVert h2) v := by
  have hp_seed : IsInteriorElemCoord h (GM13.elementaryWallMiddle₁ h) := by
    unfold IsInteriorElemCoord GM13.elementaryWallMiddle₁
    refine ⟨by omega, by omega, by omega, by omega⟩
  have hseed_eq : W.seedVert h2 = W.interiorBranchVert (GM13.elementaryWallMiddle₁ h) hp_seed := rfl
  rw [hseed_eq]
  unfold insideFinset at hv
  rw [Finset.mem_sdiff, W.mem_vertexFinset_iff] at hv
  rcases hv with ⟨⟨u, rfl⟩ | ⟨k, hv_int⟩, hv_notP⟩
  · have hnot_u := W.not_perimCoord_of_branchVert_not_mem_perimeterFinset h2 u hv_notP
    have hp_u : IsInteriorElemCoord h (elemWallVertCoord h u) :=
      isInteriorElemCoord_of_not_perimCoord u hnot_u
    have hu_eq : W.branchVert u = W.interiorBranchVert (elemWallVertCoord h u) hp_u := by
      unfold interiorBranchVert
      rw [elemWallCoordIdx_elemWallVertCoord]
    rw [hu_eq]
    exact W.reachable_interiorBranchVert_any h2 hW hsub hp_seed hp_u
  · rcases W.exists_branchVert_reachable_of_mem_internalVerts hW hsub k hv_int hv_notP with
      ⟨u, hnot_u, hreach_uv⟩
    have hp_u : IsInteriorElemCoord h (elemWallVertCoord h u) :=
      isInteriorElemCoord_of_not_perimCoord u hnot_u
    have hu_eq : W.branchVert u = W.interiorBranchVert (elemWallVertCoord h u) hp_u := by
      unfold interiorBranchVert
      rw [elemWallCoordIdx_elemWallVertCoord]
    have hreach_su := W.reachable_interiorBranchVert_any h2 hW hsub hp_seed hp_u
    rw [← hu_eq] at hreach_su
    exact hreach_su.trans hreach_uv

/-! ### Section 2b: Compass of a `WallOfHeight` and Agreement with `GM13.wallCompass` -/

variable (W : WallOfHeight h G)

/-- The vertex set of the compass of `W` in `G \ X` (`X : Finset (Fin n)`), defined as the union of
`W.perimeterFinset` and the vertices of `G` reachable from `W.insideFinset` in
`restrictGraph G.toSimpleGraph (Finset.univ \ (X ∪ W.perimeterFinset))`
(GM XIII Section 9, page 102). -/
noncomputable def compassFinsetAvoid (X : Finset (Fin n)) : Finset (Fin n) :=
  W.perimeterFinset ∪
    (W.insideFinset.biUnion (fun s =>
      reachSet (restrictGraph G.toSimpleGraph (Finset.univ \ (X ∪ W.perimeterFinset))) s))

/-- The vertex set of the compass of `W` in `G` (`compassFinsetAvoid ∅`, GM XIII Section 9,
page 102). -/
noncomputable def compassFinset : Finset (Fin n) :=
  W.compassFinsetAvoid ∅

/-- When `Disjoint X W.vertexFinset` and `W.IsValid`, `W.wallSimpleGraph` is a subgraph of
`restrictGraph G.toSimpleGraph (Finset.univ \ X)`. -/
theorem wallSimpleGraph_le_restrictGraph_sdiff (hW : W.IsValid)
    {X : Finset (Fin n)} (hdisj : Disjoint X W.vertexFinset) :
    W.wallSimpleGraph ≤ restrictGraph G.toSimpleGraph (Finset.univ \ X) := by
  intro u v hadj
  rw [restrictGraph_adj]
  obtain ⟨hu, hv⟩ := W.isSubgraphOn_wallSimpleGraph hadj
  refine ⟨?_, ?_, W.wallSimpleGraph_le_of_isValid hW hadj⟩
  · rw [Finset.mem_sdiff]
    exact ⟨Finset.mem_univ u, Finset.disjoint_right.mp hdisj hu⟩
  · rw [Finset.mem_sdiff]
    exact ⟨Finset.mem_univ v, Finset.disjoint_right.mp hdisj hv⟩

theorem restrictGraph_sdiff_sdiff {G' : SimpleGraph (Fin n)} (X Y : Finset (Fin n)) :
    restrictGraph (restrictGraph G' (Finset.univ \ X)) (Finset.univ \ Y) =
      restrictGraph G' (Finset.univ \ (X ∪ Y)) := by
  ext u v
  simp only [restrictGraph_adj, Finset.mem_sdiff, Finset.mem_univ, true_and, Finset.mem_union,
    not_or]
  tauto

/-- When `2 ≤ h`, `W.IsValid`, and `Disjoint X W.vertexFinset`, every vertex in `W.insideFinset`
is in the same connected component of
`restrictGraph G.toSimpleGraph (Finset.univ \ (X ∪ W.perimeterFinset))` as `W.seedVert h2`, so
`W.compassFinsetAvoid X` equals `W.perimeterFinset ∪ reachSet ... (W.seedVert h2)`. -/
theorem compassFinsetAvoid_eq_reachSet_seedVert (h2 : 2 ≤ h) (hW : W.IsValid)
    {X : Finset (Fin n)} (hdisj : Disjoint X W.vertexFinset) :
    W.compassFinsetAvoid X =
      W.perimeterFinset ∪
        reachSet (restrictGraph G.toSimpleGraph (Finset.univ \ (X ∪ W.perimeterFinset)))
          (W.seedVert h2) := by
  have hsub := W.wallSimpleGraph_le_restrictGraph_sdiff hW hdisj
  have hreach_all : ∀ s ∈ W.insideFinset,
      (restrictGraph G.toSimpleGraph (Finset.univ \ (X ∪ W.perimeterFinset))).Reachable
        (W.seedVert h2) s := by
    intro s hs
    have hr := W.reachable_seedVert_of_mem_insideFinset h2 hW hsub hs
    rwa [restrictGraph_sdiff_sdiff] at hr
  unfold compassFinsetAvoid
  ext v
  simp only [Finset.mem_union, Finset.mem_biUnion, mem_reachSet]
  refine or_congr_right ⟨?_, ?_⟩
  · rintro ⟨s, hs, hr⟩
    exact (hreach_all s hs).trans hr
  · intro hr
    exact ⟨W.seedVert h2, W.seedVert_mem_insideFinset h2 hW, hr⟩

/-- `W.compassFinset` equals `W.perimeterFinset ∪ reachSet ... (W.seedVert h2)`. -/
theorem compassFinset_eq_reachSet_seedVert (h2 : 2 ≤ h) (hW : W.IsValid) :
    W.compassFinset =
      W.perimeterFinset ∪
        reachSet (restrictGraph G.toSimpleGraph (Finset.univ \ W.perimeterFinset))
          (W.seedVert h2) := by
  have h := W.compassFinsetAvoid_eq_reachSet_seedVert h2 hW (Finset.disjoint_empty_left _)
  simpa [compassFinset] using h

/-- A walk in `restrictGraph G.toSimpleGraph (Finset.univ \ Y)` lifts to a `Surface.GraphWalk` in
`GM09.deleteVertices G.toGMDigraph.toGraph (Fin.val '' (Y : Set (Fin n)))`. -/
def liftWalkRestrictToDeleteVertices (Y : Finset (Fin n)) :
    ∀ {u v : Fin n},
      (restrictGraph G.toSimpleGraph (Finset.univ \ Y)).Walk u v →
      u ∉ Y →
      Surface.GraphWalk (GM09.deleteVertices G.toGMDigraph.toGraph (Fin.val '' (Y : Set (Fin n)))) u.1 v.1
  | u, _, .nil, hu =>
    .nil ⟨u.2, fun ⟨w, hw, heq⟩ => hu (Fin.ext heq ▸ hw)⟩
  | u, _, .cons (v := v) hadj rest, _ => by
    rw [restrictGraph_adj, Finset.mem_sdiff, Finset.mem_sdiff] at hadj
    rcases hadj with ⟨⟨_, hu_notY⟩, ⟨_, hv_notY⟩, hadjG⟩
    have hu_not : u.1 ∉ Fin.val '' (Y : Set (Fin n)) :=
      fun ⟨w, hw, heq⟩ => hu_notY (Fin.ext heq ▸ hw)
    have hv_not : v.1 ∉ Fin.val '' (Y : Set (Fin n)) :=
      fun ⟨w, hw, heq⟩ => hv_notY (Fin.ext heq ▸ hw)
    have hlink : (GM09.deleteVertices G.toGMDigraph.toGraph (Fin.val '' (Y : Set (Fin n)))).IsLink
        (adjEdgeTriple G u v) u.1 v.1 := by
      unfold GM09.deleteVertices
      rw [Graph.induce_isLink]
      exact ⟨isLink_adjEdgeTriple hadjG, ⟨u.2, hu_not⟩, ⟨v.2, hv_not⟩⟩
    exact .cons hlink (liftWalkRestrictToDeleteVertices Y rest hv_notY)

/-- A `Surface.GraphWalk` in `GM09.deleteVertices G.toGMDigraph.toGraph (Fin.val '' (Y : Set (Fin n)))`
yields reachability in `restrictGraph G.toSimpleGraph (Finset.univ \ Y)`. -/
theorem reachable_restrict_of_graphWalk_deleteVertices (Y : Finset (Fin n)) :
    ∀ {a b : ℕ}
      (_w : Surface.GraphWalk (GM09.deleteVertices G.toGMDigraph.toGraph (Fin.val '' (Y : Set (Fin n)))) a b)
      (ha : a < n) (hb : b < n),
      (restrictGraph G.toSimpleGraph (Finset.univ \ Y)).Reachable ⟨a, ha⟩ ⟨b, hb⟩
  | _, _, .nil _, _, _ => SimpleGraph.Reachable.refl _
  | a, b, .cons (e := e) (v := c) hlink rest, ha, hb => by
    unfold GM09.deleteVertices at hlink
    rw [Graph.induce_isLink] at hlink
    rcases hlink with ⟨hlinkG, ⟨_, ha_not⟩, ⟨hc_lt, hc_not⟩⟩
    have hrest := reachable_restrict_of_graphWalk_deleteVertices Y rest hc_lt hb
    by_cases hac : (⟨a, ha⟩ : Fin n) = ⟨c, hc_lt⟩
    · rw [hac]; exact hrest
    · have hadjG : G.toSimpleGraph.Adj ⟨a, ha⟩ ⟨c, hc_lt⟩ := by
        rw [MultiDigraph.toSimpleGraph_adj]
        refine ⟨hac, ?_⟩
        rcases hlinkG with ⟨⟨hu, hv, hmult⟩, ⟨h1, h2⟩ | ⟨h1, h2⟩⟩
        · right
          have hpos : 0 < G.edgeMult ⟨e.1, hu⟩ ⟨e.2.1, hv⟩ := Nat.zero_lt_of_lt hmult
          convert hpos using 2
          · exact Fin.ext h2.symm
          · exact Fin.ext h1.symm
        · left
          have hpos : 0 < G.edgeMult ⟨e.1, hu⟩ ⟨e.2.1, hv⟩ := Nat.zero_lt_of_lt hmult
          convert hpos using 2
          · exact Fin.ext h2.symm
          · exact Fin.ext h1.symm
      have ha_mem : (⟨a, ha⟩ : Fin n) ∈ Finset.univ \ Y := by
        rw [Finset.mem_sdiff]
        exact ⟨Finset.mem_univ _, fun h => ha_not ⟨⟨a, ha⟩, h, rfl⟩⟩
      have hc_mem : (⟨c, hc_lt⟩ : Fin n) ∈ Finset.univ \ Y := by
        rw [Finset.mem_sdiff]
        exact ⟨Finset.mem_univ _, fun h => hc_not ⟨⟨c, hc_lt⟩, h, rfl⟩⟩
      have hadjR : (restrictGraph G.toSimpleGraph (Finset.univ \ Y)).Adj ⟨a, ha⟩ ⟨c, hc_lt⟩ := by
        rw [restrictGraph_adj]
        exact ⟨ha_mem, hc_mem, hadjG⟩
      exact (SimpleGraph.Adj.reachable hadjR).trans hrest

theorem not_mem_of_reachable_restrictGraph {Y : Finset (Fin n)} {s v : Fin n}
    (hs : s ∉ Y) (h : (restrictGraph G.toSimpleGraph (Finset.univ \ Y)).Reachable s v) :
    v ∉ Y := by
  rcases h.symm with ⟨w⟩
  cases w with
  | nil => exact hs
  | cons hadj _ =>
    rw [restrictGraph_adj, Finset.mem_sdiff] at hadj
    exact hadj.1.2

theorem deleteVertices_empty {α β : Type*} (G₀ : Graph α β) :
    GM09.deleteVertices G₀ ∅ = G₀ := by
  refine Graph.ext (by simp [GM09.deleteVertices]) fun e x y => ?_
  unfold GM09.deleteVertices
  rw [Graph.induce_isLink, Set.sdiff_empty]
  exact ⟨fun h => h.1, fun h => ⟨h, h.left_mem, h.right_mem⟩⟩

theorem deleteVertices_deleteVertices {α β : Type*} (G₀ : Graph α β) (X Y : Set α) :
    GM09.deleteVertices (GM09.deleteVertices G₀ X) Y = GM09.deleteVertices G₀ (X ∪ Y) := by
  refine Graph.ext (by ext; simp [GM09.deleteVertices]; tauto) fun e x y => ?_
  unfold GM09.deleteVertices
  rw [Graph.induce_isLink, Graph.induce_isLink, Graph.induce_isLink]
  simp only [Set.mem_sdiff, Set.mem_union]
  tauto

/-- The vertex set of `W.compassFinsetAvoid X` (mapped by `Fin.val`) equals the vertex set of the
`GM13` compass `GM13.wallCompass (GM09.deleteVertices G.toGMDigraph.toGraph (Fin.val '' X)) (W.toGMWall h2 he hW)`. -/
theorem val_compassFinsetAvoid_eq_wallCompassVerts (h2 : 2 ≤ h) (he : Even h) (hW : W.IsValid)
    (X : Finset (Fin n)) (hdisj : Disjoint X W.vertexFinset) :
    ((W.compassFinsetAvoid X : Set (Fin n)).image Fin.val) =
      GM13.wallCompassVerts
        (GM09.deleteVertices G.toGMDigraph.toGraph (Fin.val '' (X : Set (Fin n))))
        (W.toGMWall h2 he hW) := by
  have hperim_eq : V((W.toGMWall h2 he hW).perimeter) = Fin.val '' (W.perimeterFinset : Set (Fin n)) :=
    W.vertexSet_perimeter_toGMWall_eq h2 he hW
  have hinside_eq : (W.toGMWall h2 he hW).insideVerts = Fin.val '' (W.insideFinset : Set (Fin n)) :=
    W.insideVerts_toGMWall_eq h2 he hW
  have hdel_eq :
      GM09.deleteVertices
        (GM09.deleteVertices G.toGMDigraph.toGraph (Fin.val '' (X : Set (Fin n))))
        V((W.toGMWall h2 he hW).perimeter) =
        GM09.deleteVertices G.toGMDigraph.toGraph
          (Fin.val '' ((X ∪ W.perimeterFinset : Finset (Fin n)) : Set (Fin n))) := by
    rw [hperim_eq, deleteVertices_deleteVertices, Finset.coe_union, Set.image_union]
  unfold GM13.wallCompassVerts compassFinsetAvoid
  rw [hdel_eq, hperim_eq, hinside_eq]
  ext z
  simp only [Set.mem_image, Finset.mem_coe, Finset.mem_union,
    Finset.mem_biUnion, mem_reachSet, Set.mem_union, Set.mem_ofPred_eq, Set.mem_sdiff]
  constructor
  · rintro ⟨v, hvP | ⟨s, hsI, hreach⟩, rfl⟩
    · exact Or.inl ⟨v, hvP, rfl⟩
    · have hs_not : s ∉ X ∪ W.perimeterFinset := by
        rw [Finset.mem_union, not_or]
        have hsW : s ∈ W.vertexFinset := Finset.sdiff_subset hsI
        exact ⟨Finset.disjoint_right.mp hdisj hsW, (Finset.mem_sdiff.mp hsI).2⟩
      have hv_not : v ∉ X ∪ W.perimeterFinset :=
        not_mem_of_reachable_restrictGraph hs_not hreach
      rw [Finset.mem_union, not_or] at hv_not
      refine Or.inr ⟨⟨⟨v.2, fun ⟨w, hw, heq⟩ => hv_not.1 (Fin.ext heq ▸ hw)⟩,
        fun ⟨w, hw, heq⟩ => hv_not.2 (Fin.ext heq ▸ hw)⟩, ?_⟩
      rcases hreach with ⟨w⟩
      exact ⟨s.1, ⟨s, hsI, rfl⟩,
        ⟨liftWalkRestrictToDeleteVertices (X ∪ W.perimeterFinset) w hs_not⟩⟩
  · rintro (⟨v, hvP, rfl⟩ | ⟨⟨⟨hz_lt, hz_notX⟩, hz_notP⟩, ⟨_, ⟨s, hsI, rfl⟩, ⟨w⟩⟩⟩)
    · exact ⟨v, Or.inl hvP, rfl⟩
    · refine ⟨⟨z, hz_lt⟩, Or.inr ⟨s, hsI, ?_⟩, rfl⟩
      exact reachable_restrict_of_graphWalk_deleteVertices (X ∪ W.perimeterFinset) w s.2 hz_lt

/-- The vertex set of `W.compassFinset` (mapped by `Fin.val`) equals the vertex set of
`GM13.wallCompass G.toGMDigraph.toGraph (W.toGMWall h2 he hW)`. -/
theorem val_compassFinset_eq_wallCompassVerts (h2 : 2 ≤ h) (he : Even h) (hW : W.IsValid) :
    ((W.compassFinset : Set (Fin n)).image Fin.val) =
      GM13.wallCompassVerts G.toGMDigraph.toGraph (W.toGMWall h2 he hW) := by
  have h := W.val_compassFinsetAvoid_eq_wallCompassVerts h2 he hW ∅ (Finset.disjoint_empty_left _)
  have hdel :
      GM09.deleteVertices G.toGMDigraph.toGraph (Fin.val '' ((∅ : Finset (Fin n)) : Set (Fin n))) =
        G.toGMDigraph.toGraph := by
    rw [Finset.coe_empty, Set.image_empty, deleteVertices_empty]
  unfold compassFinset
  rw [h, hdel]

/-! ### Section 2c: Subwalls of a `WallOfHeight` and Agreement with `GM13` -/

end WallOfHeight

/-- Any coordinate `q ∈ GM13.elementaryWallVerts h'` (`1 ≤ h'`) shifted by `(i, j)` with
`h' ≤ h`, `i ≤ 2 * h - 2 * h'`, and `j ≤ h - h'` lies in `GM13.elementaryWallVerts h`. -/
theorem wallShift_mem_elementaryWallVerts_of_one_le {i j h' h : ℕ}
    (_hh' : 1 ≤ h') (hle : h' ≤ h)
    (hi_le : i ≤ 2 * h - 2 * h') (hj_le : j ≤ h - h')
    {q : ℕ × ℕ} (hq : q ∈ GM13.elementaryWallVerts h') :
    GM13.wallShift i j q ∈ GM13.elementaryWallVerts h := by
  rcases q with ⟨x, y⟩
  rcases hq with ⟨hx, hy, h00, hlast⟩
  dsimp [GM13.wallShift, GM13.elementaryWallVerts] at hx hy ⊢
  refine ⟨by omega, by omega, ?_, ?_⟩
  · intro h0
    injection h0 with h1 h2
    exact h00 (Prod.ext (by omega) (by omega))
  · intro h1
    injection h1 with h1a h1b
    exact hlast (Prod.ext (by omega) (by omega))

/-- Shift a branch-vertex index `u : Fin (elemWallNumVerts h')` (`1 ≤ h'`) by `(i, j)` into
`Fin (elemWallNumVerts h)`. -/
def shiftElemWallVertIdx (i j h' h : ℕ) (hh' : 1 ≤ h') (hle : h' ≤ h)
    (hi_le : i ≤ 2 * h - 2 * h') (hj_le : j ≤ h - h')
    (u : Fin (elemWallNumVerts h')) : Fin (elemWallNumVerts h) :=
  elemWallCoordIdx h (GM13.wallShift i j (elemWallVertCoord h' u))
    (wallShift_mem_elementaryWallVerts_of_one_le hh' hle hi_le hj_le
      (elemWallVertCoord_mem_elementaryWallVerts h' u))

@[simp]
theorem elemWallVertCoord_shiftElemWallVertIdx {i j h' h : ℕ}
    (hh' : 1 ≤ h') (hle : h' ≤ h) (hi_le : i ≤ 2 * h - 2 * h') (hj_le : j ≤ h - h')
    (u : Fin (elemWallNumVerts h')) :
    elemWallVertCoord h (shiftElemWallVertIdx i j h' h hh' hle hi_le hj_le u) =
      GM13.wallShift i j (elemWallVertCoord h' u) := by
  unfold shiftElemWallVertIdx
  exact elemWallVertCoord_elemWallCoordIdx h _

theorem shiftElemWallVertIdx_injective {i j h' h : ℕ}
    (hh' : 1 ≤ h') (hle : h' ≤ h) (hi_le : i ≤ 2 * h - 2 * h') (hj_le : j ≤ h - h') :
    Function.Injective (shiftElemWallVertIdx i j h' h hh' hle hi_le hj_le) := by
  intro u₁ u₂ heq
  have hc := congrArg (elemWallVertCoord h) heq
  rw [elemWallVertCoord_shiftElemWallVertIdx, elemWallVertCoord_shiftElemWallVertIdx] at hc
  have hq : elemWallVertCoord h' u₁ = elemWallVertCoord h' u₂ := by
    unfold GM13.wallShift at hc
    injection hc with h1 h2
    exact Prod.ext (by omega) (by omega)
  exact elemWallVertCoord_injective h' hq

theorem isElemWallEdgeCoord_wallShift {i j : ℕ} (hi_even : Even i) (hj_even : Even j)
    (p q : ℕ × ℕ) :
    isElemWallEdgeCoord (GM13.wallShift i j p) (GM13.wallShift i j q) =
      isElemWallEdgeCoord p q := by
  rcases hi_even with ⟨ki, rfl⟩
  rcases hj_even with ⟨kj, rfl⟩
  unfold isElemWallEdgeCoord GM13.wallShift
  dsimp only
  have h1 : (p.2 + (kj + kj) == q.2 + (kj + kj)) = (p.2 == q.2) := by
    by_cases h : p.2 = q.2 <;> simp [h]
  have h2 : (q.1 + (ki + ki) == p.1 + (ki + ki) + 1) = (q.1 == p.1 + 1) := by
    by_cases h : q.1 = p.1 + 1 <;> simp [h] <;> omega
  have h3 : (p.1 + (ki + ki) == q.1 + (ki + ki)) = (p.1 == q.1) := by
    by_cases h : p.1 = q.1 <;> simp [h]
  have h4 : (q.2 + (kj + kj) == p.2 + (kj + kj) + 1) = (q.2 == p.2 + 1) := by
    by_cases h : q.2 = p.2 + 1 <;> simp [h] <;> omega
  have h5 : (p.1 + (ki + ki) + (p.2 + (kj + kj))) % 2 = (p.1 + p.2) % 2 := by omega
  rw [h1, h2, h3, h4, h5]

theorem shiftElemWallEdge_mem_elemWallEdges {i j h' h : ℕ}
    (hh' : 1 ≤ h') (hle : h' ≤ h) (hi_even : Even i) (hj_even : Even j)
    (hi_le : i ≤ 2 * h - 2 * h') (hj_le : j ≤ h - h')
    (k : Fin (elemWallEdges h').length) :
    let e := (elemWallEdges h')[k.1]'k.2
    (shiftElemWallVertIdx i j h' h hh' hle hi_le hj_le e.1,
     shiftElemWallVertIdx i j h' h hh' hle hi_le hj_le e.2) ∈ elemWallEdges h := by
  intro e
  rw [mem_elemWallEdges_iff, elemWallVertCoord_shiftElemWallVertIdx,
    elemWallVertCoord_shiftElemWallVertIdx, isElemWallEdgeCoord_wallShift hi_even hj_even]
  exact elemWallEdge_isElemWallEdgeCoord h' k

/-- Find the edge index in `Fin (elemWallEdges h).length` of the `(i, j)`-shifted `k`-th edge of
`elemWallEdges h'`. -/
def shiftElemWallEdgeOption (i j h' h : ℕ) (k : Fin (elemWallEdges h').length) :
    Option (Fin (elemWallEdges h).length) :=
  findElemWallEdgeIdx h (Sym2.map (GM13.wallShift i j) (elemWallEdgeSym2 h' k))

theorem exists_shiftElemWallEdgeIdx {i j h' h : ℕ}
    (hh' : 1 ≤ h') (hle : h' ≤ h) (hi_even : Even i) (hj_even : Even j)
    (hi_le : i ≤ 2 * h - 2 * h') (hj_le : j ≤ h - h')
    (k : Fin (elemWallEdges h').length) :
    ∃ kW : Fin (elemWallEdges h).length,
      shiftElemWallEdgeOption i j h' h k = some kW ∧
      (elemWallEdges h)[kW.1]'kW.2 =
        (shiftElemWallVertIdx i j h' h hh' hle hi_le hj_le ((elemWallEdges h')[k.1]'k.2).1,
         shiftElemWallVertIdx i j h' h hh' hle hi_le hj_le ((elemWallEdges h')[k.1]'k.2).2) ∧
      elemWallEdgeSym2 h kW = Sym2.map (GM13.wallShift i j) (elemWallEdgeSym2 h' k) := by
  have hmem := shiftElemWallEdge_mem_elemWallEdges hh' hle hi_even hj_even hi_le hj_le k
  rcases List.mem_iff_getElem.mp hmem with ⟨idx, hidx, hget⟩
  let kW : Fin (elemWallEdges h).length := ⟨idx, hidx⟩
  have hget' : (elemWallEdges h)[kW.1]'kW.2 =
      (shiftElemWallVertIdx i j h' h hh' hle hi_le hj_le ((elemWallEdges h')[k.1]'k.2).1,
       shiftElemWallVertIdx i j h' h hh' hle hi_le hj_le ((elemWallEdges h')[k.1]'k.2).2) := hget
  have hsym2 : elemWallEdgeSym2 h kW = Sym2.map (GM13.wallShift i j) (elemWallEdgeSym2 h' k) := by
    unfold elemWallEdgeSym2
    dsimp only
    rw [hget', elemWallVertCoord_shiftElemWallVertIdx, elemWallVertCoord_shiftElemWallVertIdx]
    rfl
  refine ⟨kW, ?_, hget', hsym2⟩
  unfold shiftElemWallEdgeOption
  rw [← hsym2, findElemWallEdgeIdx_elemWallEdgeSym2]

namespace WallOfHeight

variable {h n : ℕ} {G : MultiDigraph n} (W : WallOfHeight h G)

/-- The `(i, j)`-shifted subwall of `W` of height `h'` (`1 ≤ h' ≤ h`), for even `i ≤ 2h - 2h'` and
even `j ≤ h - h'` (GM XIII Section 9, pages 97–98). -/
def subwallAt (i j h' : ℕ) (hh' : 1 ≤ h') (hle : h' ≤ h)
    (_hi_even : Even i) (_hj_even : Even j)
    (hi_le : i ≤ 2 * h - 2 * h') (hj_le : j ≤ h - h') : WallOfHeight h' G where
  branchVert u := W.branchVert (shiftElemWallVertIdx i j h' h hh' hle hi_le hj_le u)
  internalVerts k :=
    match shiftElemWallEdgeOption i j h' h k with
    | some kW => W.internalVerts kW
    | none => []

theorem exists_subdivPathVerts_subwallAt (i j h' : ℕ) (hh' : 1 ≤ h') (hle : h' ≤ h)
    (hi_even : Even i) (hj_even : Even j)
    (hi_le : i ≤ 2 * h - 2 * h') (hj_le : j ≤ h - h')
    (k : Fin (elemWallEdges h').length) :
    ∃ kW : Fin (elemWallEdges h).length,
      shiftElemWallEdgeOption i j h' h k = some kW ∧
      elemWallEdgeSym2 h kW = Sym2.map (GM13.wallShift i j) (elemWallEdgeSym2 h' k) ∧
      (W.subwallAt i j h' hh' hle hi_even hj_even hi_le hj_le).internalVerts k =
        W.internalVerts kW ∧
      (W.subwallAt i j h' hh' hle hi_even hj_even hi_le hj_le).subdivPathVerts k =
        W.subdivPathVerts kW := by
  obtain ⟨kW, hopt, hget, hsym2⟩ :=
    exists_shiftElemWallEdgeIdx hh' hle hi_even hj_even hi_le hj_le k
  have hint :
      (W.subwallAt i j h' hh' hle hi_even hj_even hi_le hj_le).internalVerts k =
        W.internalVerts kW := by
    unfold subwallAt
    dsimp only
    rw [hopt]
  refine ⟨kW, hopt, hsym2, hint, ?_⟩
  unfold subdivPathVerts
  rw [hint]
  unfold subwallAt
  dsimp only
  rw [hget]

/-- If `W` is valid, then `W.subwallAt i j h' ...` is valid. -/
theorem isValid_subwallAt (hW : W.IsValid) (i j h' : ℕ) (hh' : 1 ≤ h') (hle : h' ≤ h)
    (hi_even : Even i) (hj_even : Even j)
    (hi_le : i ≤ 2 * h - 2 * h') (hj_le : j ≤ h - h') :
    (W.subwallAt i j h' hh' hle hi_even hj_even hi_le hj_le).IsValid := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro u₁ u₂ heq
    exact shiftElemWallVertIdx_injective hh' hle hi_le hj_le (hW.1 heq)
  · intro k
    obtain ⟨kW, _, _, _, hpath⟩ :=
      W.exists_subdivPathVerts_subwallAt i j h' hh' hle hi_even hj_even hi_le hj_le k
    rw [hpath]
    exact hW.2.1 kW
  · intro k u
    obtain ⟨kW, _, _, hint, _⟩ :=
      W.exists_subdivPathVerts_subwallAt i j h' hh' hle hi_even hj_even hi_le hj_le k
    rw [hint]
    exact hW.2.2.1 kW _
  · intro k₁ k₂ hne
    obtain ⟨kW₁, _, hsym₁, hint₁, _⟩ :=
      W.exists_subdivPathVerts_subwallAt i j h' hh' hle hi_even hj_even hi_le hj_le k₁
    obtain ⟨kW₂, _, hsym₂, hint₂, _⟩ :=
      W.exists_subdivPathVerts_subwallAt i j h' hh' hle hi_even hj_even hi_le hj_le k₂
    rw [hint₁, hint₂]
    apply hW.2.2.2 kW₁ kW₂
    intro heq
    subst heq
    have hmap_eq : Sym2.map (GM13.wallShift i j) (elemWallEdgeSym2 h' k₁) =
        Sym2.map (GM13.wallShift i j) (elemWallEdgeSym2 h' k₂) :=
      hsym₁.symm.trans hsym₂
    have hsym_eq : elemWallEdgeSym2 h' k₁ = elemWallEdgeSym2 h' k₂ :=
      Sym2.map.injective (GM13.wallShift_inj' i j) hmap_eq
    exact hne (elemWallEdgeSym2_injective h' hsym_eq)

/-- Every vertex of `W.subwallAt i j h' ...` is a vertex of `W`. -/
theorem subwallAt_vertexFinset_subset (i j h' : ℕ) (hh' : 1 ≤ h') (hle : h' ≤ h)
    (hi_even : Even i) (hj_even : Even j)
    (hi_le : i ≤ 2 * h - 2 * h') (hj_le : j ≤ h - h') :
    (W.subwallAt i j h' hh' hle hi_even hj_even hi_le hj_le).vertexFinset ⊆ W.vertexFinset := by
  intro v hv
  rw [mem_vertexFinset_iff] at hv ⊢
  rcases hv with ⟨u, rfl⟩ | ⟨k, hvk⟩
  · exact Or.inl ⟨shiftElemWallVertIdx i j h' h hh' hle hi_le hj_le u, rfl⟩
  · obtain ⟨kW, _, _, hint, _⟩ :=
      W.exists_subdivPathVerts_subwallAt i j h' hh' hle hi_even hj_even hi_le hj_le k
    rw [hint] at hvk
    exact Or.inr ⟨kW, hvk⟩

/-- `W' : WallOfHeight h' G` is a subwall of `W : WallOfHeight h G` if `2 ≤ h' ≤ h`, `Even h'`, and
`W' = W.subwallAt i j h' ...` for some even offsets `i ≤ 2h - 2h'` and `j ≤ h - h'`
(GM XIII Section 9, pages 97–98). -/
def IsSubwallOf {h' : ℕ} (W' : WallOfHeight h' G) (W : WallOfHeight h G) : Prop :=
  ∃ (h2' : 2 ≤ h') (_ : Even h') (hle : h' ≤ h) (i j : ℕ)
    (hi_even : Even i) (hj_even : Even j)
    (hi_le : i ≤ 2 * h - 2 * h') (hj_le : j ≤ h - h'),
    W' = W.subwallAt i j h' (by omega) hle hi_even hj_even hi_le hj_le

/-- Two subgraphs `H₁, H₂ ≤ G₀` with equal vertex sets and equal edge sets are equal. -/
theorem graph_eq_of_le_of_vertexSet_eq_of_edgeSet_eq {α β : Type*}
    {G₀ H₁ H₂ : Graph α β} (h₁ : H₁ ≤ G₀) (h₂ : H₂ ≤ G₀)
    (hV : V(H₁) = V(H₂)) (hE : E(H₁) = E(H₂)) : H₁ = H₂ := by
  refine Graph.ext hV fun e x y => ⟨fun hl => ?_, fun hl => ?_⟩
  · obtain ⟨u, v, hl₂⟩ := (H₂.edge_mem_iff_exists_isLink e).mp (hE ▸ hl.edge_mem)
    rcases (h₁.isLink_mono hl).eq_and_eq_or_eq_and_eq (h₂.isLink_mono hl₂) with
      ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact hl₂
    · exact hl₂.symm
  · obtain ⟨u, v, hl₁⟩ := (H₁.edge_mem_iff_exists_isLink e).mp (hE.symm ▸ hl.edge_mem)
    rcases (h₂.isLink_mono hl).eq_and_eq_or_eq_and_eq (h₁.isLink_mono hl₁) with
      ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact hl₁
    · exact hl₁.symm

theorem subdivPathOfSym2_subwallAt (hW : W.IsValid)
    (i j h' : ℕ) (hh' : 1 ≤ h') (hle : h' ≤ h)
    (hi_even : Even i) (hj_even : Even j)
    (hi_le : i ≤ 2 * h - 2 * h') (hj_le : j ≤ h - h')
    {p q : ℕ × ℕ} (hpq : GM13.elementaryWallAdj h' p q) :
    (W.subwallAt i j h' hh' hle hi_even hj_even hi_le hj_le).subdivPathOfSym2
      (W.isValid_subwallAt hW i j h' hh' hle hi_even hj_even hi_le hj_le) s(p, q) =
      W.subdivPathOfSym2 hW s(GM13.wallShift i j p, GM13.wallShift i j q) := by
  rcases exists_elemWallEdgeSym2_of_elementaryWallAdj hpq with ⟨k, hk⟩
  obtain ⟨kW, _, hsym2, _, hpath_eq⟩ :=
    W.exists_subdivPathVerts_subwallAt i j h' hh' hle hi_even hj_even hi_le hj_le k
  have hkW : elemWallEdgeSym2 h kW = s(GM13.wallShift i j p, GM13.wallShift i j q) := by
    rw [hsym2, hk]
    rfl
  rw [← hk, ← hkW, subdivPathOfSym2_elemWallEdgeSym2, subdivPathOfSym2_elemWallEdgeSym2]
  have h1 : ∀ {L₁ L₂ : List (Fin n)} (hL : L₁ = L₂) (hne₁ : L₁ ≠ []) (hne₂ : L₂ ≠ [])
      (hw₁ : IsSimpleWalkList G L₁) (hw₂ : IsSimpleWalkList G L₂),
      GM09.walkSubgraph (toGMGraphWalk hne₁ hw₁) = GM09.walkSubgraph (toGMGraphWalk hne₂ hw₂) := by
    rintro L₁ L₂ rfl _ _ _ _
    rfl
  exact h1 hpath_eq _ _ _ _

theorem gmWall_subwallAt_branchVertex {α β : Type*} (W₀ : GM13.Wall α β)
    (i j h' : ℕ) (h2' : 2 ≤ h') (he' : Even h') (hle : h' ≤ W₀.height)
    (hi_even : Even i) (hj_even : Even j)
    (hi_le : i ≤ 2 * W₀.height - 2 * h') (hj_le : j ≤ W₀.height - h')
    (p : ℕ × ℕ) (hp : p ∈ GM13.elementaryWallVerts h') :
    (W₀.subwallAt i j h' h2' he' hle hi_even hj_even hi_le hj_le).branchVertex p hp =
      W₀.branchVertex (GM13.wallShift i j p)
        (GM13.wallShift_mem_elementaryWallVerts' h2' hle hi_le hj_le hp) := rfl

theorem gmWall_subwallAt_baseEdge {α β : Type*} (W₀ : GM13.Wall α β)
    (i j h' : ℕ) (h2' : 2 ≤ h') (he' : Even h') (hle : h' ≤ W₀.height)
    (hi_even : Even i) (hj_even : Even j)
    (hi_le : i ≤ 2 * W₀.height - 2 * h') (hj_le : j ≤ W₀.height - h')
    {p q : ℕ × ℕ} (hpq : GM13.elementaryWallAdj h' p q) :
    (W₀.subwallAt i j h' h2' he' hle hi_even hj_even hi_le hj_le).baseEdge hpq =
      W₀.baseEdge
        ((GM13.elementaryWallAdj_wallShift_iff h2' hle hi_even hj_even hi_le hj_le hpq.1 hpq.2.1).mp hpq) := rfl

theorem gmWall_subwallAt_subdivisionPaths {α β : Type*} (W₀ : GM13.Wall α β)
    (i j h' : ℕ) (h2' : 2 ≤ h') (he' : Even h') (hle : h' ≤ W₀.height)
    (hi_even : Even i) (hj_even : Even j)
    (hi_le : i ≤ 2 * W₀.height - 2 * h') (hj_le : j ≤ W₀.height - h') :
    (W₀.subwallAt i j h' h2' he' hle hi_even hj_even hi_le hj_le).subdivisionPaths =
      W₀.subdivisionPaths := rfl

theorem mem_baseGraph_iff_exists_branchVertex {α β : Type*} (W₀ : GM13.Wall α β) (x : α) :
    x ∈ V(W₀.baseGraph) ↔
      ∃ p, ∃ hp : p ∈ GM13.elementaryWallVerts W₀.height, W₀.branchVertex p hp = x := by
  constructor
  · intro hx
    let u := W₀.baseIso.vertexEquiv.symm ⟨x, hx⟩
    refine ⟨u.1, u.2, ?_⟩
    unfold GM13.Wall.branchVertex
    exact congrArg Subtype.val (W₀.baseIso.vertexEquiv.apply_symm_apply ⟨x, hx⟩)
  · rintro ⟨p, hp, rfl⟩
    exact (W₀.baseIso.vertexEquiv ⟨p, hp⟩).2

/-- The `GM13` subwall `(W.toGMWall h2 he hW).subwallAt i j h' ...` of `W.toGMWall`. -/
noncomputable def toGMSubwallAt (h2 : 2 ≤ h) (he : Even h) (hW : W.IsValid)
    (i j h' : ℕ) (h2' : 2 ≤ h') (he' : Even h') (hle : h' ≤ h)
    (hi_even : Even i) (hj_even : Even j)
    (hi_le : i ≤ 2 * h - 2 * h') (hj_le : j ≤ h - h') : GM13.Wall ℕ (ℕ × ℕ × ℕ) :=
  (W.toGMWall h2 he hW).subwallAt i j h' h2' he' hle hi_even hj_even hi_le hj_le

/-- `W.toGMSubwallAt` satisfies `GM13.Wall.IsSubwallOf (W.toGMWall h2 he hW)`. -/
theorem toGMSubwallAt_isSubwallOf (h2 : 2 ≤ h) (he : Even h) (hW : W.IsValid)
    (i j h' : ℕ) (h2' : 2 ≤ h') (he' : Even h') (hle : h' ≤ h)
    (hi_even : Even i) (hj_even : Even j)
    (hi_le : i ≤ 2 * h - 2 * h') (hj_le : j ≤ h - h') :
    (W.toGMSubwallAt h2 he hW i j h' h2' he' hle hi_even hj_even hi_le hj_le).IsSubwallOf
      (W.toGMWall h2 he hW) :=
  (W.toGMWall h2 he hW).subwallAt_isSubwallOf i j h' h2' he' hle hi_even hj_even hi_le hj_le

/-- `(W.subwallAt ...).toGMWall` and `W.toGMSubwallAt` have identical branch vertices at every
coordinate `p ∈ GM13.elementaryWallVerts h'`. -/
theorem subwallAt_toGMWall_branchVertex_eq (h2 : 2 ≤ h) (he : Even h) (hW : W.IsValid)
    (i j h' : ℕ) (h2' : 2 ≤ h') (he' : Even h') (hle : h' ≤ h)
    (hi_even : Even i) (hj_even : Even j)
    (hi_le : i ≤ 2 * h - 2 * h') (hj_le : j ≤ h - h')
    (p : ℕ × ℕ) (hp : p ∈ GM13.elementaryWallVerts h') :
    ((W.subwallAt i j h' (by omega) hle hi_even hj_even hi_le hj_le).toGMWall h2' he'
      (W.isValid_subwallAt hW i j h' (by omega) hle hi_even hj_even hi_le hj_le)).branchVertex p hp =
      (W.toGMSubwallAt h2 he hW i j h' h2' he' hle hi_even hj_even hi_le hj_le).branchVertex p hp := by
  have hpW : GM13.wallShift i j p ∈ GM13.elementaryWallVerts h :=
    GM13.wallShift_mem_elementaryWallVerts' h2' hle hi_le hj_le hp
  have h2_br :
      (W.toGMSubwallAt h2 he hW i j h' h2' he' hle hi_even hj_even hi_le hj_le).branchVertex p hp =
        (W.toGMWall h2 he hW).branchVertex (GM13.wallShift i j p) hpW :=
    gmWall_subwallAt_branchVertex (W.toGMWall h2 he hW) i j h' h2' he' hle hi_even hj_even hi_le hj_le p hp
  rw [h2_br, toGMWall_branchVertex, toGMWall_branchVertex]
  unfold subwallAt shiftElemWallVertIdx
  dsimp only
  have hidx :
      elemWallCoordIdx h
        (GM13.wallShift i j (elemWallVertCoord h' (elemWallCoordIdx h' p hp)))
        (wallShift_mem_elementaryWallVerts_of_one_le (by omega) hle hi_le hj_le
          (elemWallVertCoord_mem_elementaryWallVerts h' (elemWallCoordIdx h' p hp))) =
      elemWallCoordIdx h (GM13.wallShift i j p) hpW := by
    apply elemWallVertCoord_injective h
    rw [elemWallVertCoord_elemWallCoordIdx, elemWallVertCoord_elemWallCoordIdx,
      elemWallVertCoord_elemWallCoordIdx]
  rw [hidx]

theorem wall_ofData_subdivisionPaths_baseEdge {α β : Type*} {h : ℕ}
    (h2 : 2 ≤ h) (he : Even h) (D : GM13.WallData α β h)
    {p q : ℕ × ℕ} (hpq : GM13.elementaryWallAdj h p q) :
    (GM13.Wall.ofData h2 he D).subdivisionPaths
      ((GM13.Wall.ofData h2 he D).baseEdge hpq) = D.P s(p, q) :=
  D.pathOf_lab ⟨p, q, hpq, rfl⟩

@[simp]
theorem toGMWall_subdivisionPaths_baseEdge_s9 (h2 : 2 ≤ h) (he : Even h) (hW : W.IsValid)
    {p q : ℕ × ℕ} (hpq : GM13.elementaryWallAdj h p q) :
    (W.toGMWall h2 he hW).subdivisionPaths ((W.toGMWall h2 he hW).baseEdge hpq) =
      W.subdivPathOfSym2 hW s(p, q) := by
  unfold toGMWall
  rw [wall_ofData_subdivisionPaths_baseEdge h2 he (W.toWallData (by omega) hW) hpq]
  rfl

/-- `(W.subwallAt ...).toGMWall` and `W.toGMSubwallAt` have identical subdivision path subgraphs for
every edge `hpq : GM13.elementaryWallAdj h' p q`. -/
theorem subwallAt_toGMWall_subdivisionPaths_baseEdge_eq (h2 : 2 ≤ h) (he : Even h) (hW : W.IsValid)
    (i j h' : ℕ) (h2' : 2 ≤ h') (he' : Even h') (hle : h' ≤ h)
    (hi_even : Even i) (hj_even : Even j)
    (hi_le : i ≤ 2 * h - 2 * h') (hj_le : j ≤ h - h')
    {p q : ℕ × ℕ} (hpq : GM13.elementaryWallAdj h' p q) :
    let W₁ := (W.subwallAt i j h' (by omega) hle hi_even hj_even hi_le hj_le).toGMWall h2' he'
      (W.isValid_subwallAt hW i j h' (by omega) hle hi_even hj_even hi_le hj_le)
    let W₂ := W.toGMSubwallAt h2 he hW i j h' h2' he' hle hi_even hj_even hi_le hj_le
    W₁.subdivisionPaths (W₁.baseEdge hpq) = W₂.subdivisionPaths (W₂.baseEdge hpq) := by
  intro W₁ W₂
  have hadjW : GM13.elementaryWallAdj h (GM13.wallShift i j p) (GM13.wallShift i j q) :=
    (GM13.elementaryWallAdj_wallShift_iff h2' hle hi_even hj_even hi_le hj_le hpq.1 hpq.2.1).mp hpq
  have h1 : W₁.subdivisionPaths (W₁.baseEdge hpq) =
      (W.subwallAt i j h' (by omega) hle hi_even hj_even hi_le hj_le).subdivPathOfSym2
        (W.isValid_subwallAt hW i j h' (by omega) hle hi_even hj_even hi_le hj_le) s(p, q) :=
    (W.subwallAt i j h' (by omega) hle hi_even hj_even hi_le hj_le).toGMWall_subdivisionPaths_baseEdge_s9
      h2' he' _ hpq
  have h2_edge : W₂.baseEdge hpq = (W.toGMWall h2 he hW).baseEdge hadjW :=
    gmWall_subwallAt_baseEdge (W.toGMWall h2 he hW) i j h' h2' he' hle hi_even hj_even hi_le hj_le hpq
  have h2_sub : W₂.subdivisionPaths = (W.toGMWall h2 he hW).subdivisionPaths :=
    gmWall_subwallAt_subdivisionPaths (W.toGMWall h2 he hW) i j h' h2' he' hle hi_even hj_even hi_le hj_le
  have h2_eq : W₂.subdivisionPaths (W₂.baseEdge hpq) =
      W.subdivPathOfSym2 hW s(GM13.wallShift i j p, GM13.wallShift i j q) := by
    rw [h2_sub, h2_edge]
    exact W.toGMWall_subdivisionPaths_baseEdge_s9 h2 he hW hadjW
  rw [h1, h2_eq]
  exact W.subdivPathOfSym2_subwallAt hW i j h' (by omega) hle hi_even hj_even hi_le hj_le hpq

/-- `(W.subwallAt ...).toGMWall` and `W.toGMSubwallAt` have the exact same underlying graph
`Graph ℕ (ℕ × ℕ × ℕ)`. -/
theorem subwallAt_toGMWall_graph_eq (h2 : 2 ≤ h) (he : Even h) (hW : W.IsValid)
    (i j h' : ℕ) (h2' : 2 ≤ h') (he' : Even h') (hle : h' ≤ h)
    (hi_even : Even i) (hj_even : Even j)
    (hi_le : i ≤ 2 * h - 2 * h') (hj_le : j ≤ h - h') :
    ((W.subwallAt i j h' (by omega) hle hi_even hj_even hi_le hj_le).toGMWall h2' he'
      (W.isValid_subwallAt hW i j h' (by omega) hle hi_even hj_even hi_le hj_le)).graph =
      (W.toGMSubwallAt h2 he hW i j h' h2' he' hle hi_even hj_even hi_le hj_le).graph := by
  let W₁ := (W.subwallAt i j h' (by omega) hle hi_even hj_even hi_le hj_le).toGMWall h2' he'
    (W.isValid_subwallAt hW i j h' (by omega) hle hi_even hj_even hi_le hj_le)
  let W₂ := W.toGMSubwallAt h2 he hW i j h' h2' he' hle hi_even hj_even hi_le hj_le
  have hle₁ : W₁.graph ≤ G.toGMDigraph.toGraph :=
    (W.subwallAt i j h' (by omega) hle hi_even hj_even hi_le hj_le).isWallIn_toGMWall h2' he' _
  have hle₂ : W₂.graph ≤ G.toGMDigraph.toGraph :=
    (GM13.Wall.IsSubwallOf.graph_le
      (W.toGMSubwallAt_isSubwallOf h2 he hW i j h' h2' he' hle hi_even hj_even hi_le hj_le)).trans
      (W.isWallIn_toGMWall h2 he hW)
  have hbaseV : V(W₁.baseGraph) = V(W₂.baseGraph) := by
    ext x
    rw [mem_baseGraph_iff_exists_branchVertex W₁, mem_baseGraph_iff_exists_branchVertex W₂]
    refine exists_congr fun p => exists_congr fun hp => ?_
    rw [W.subwallAt_toGMWall_branchVertex_eq h2 he hW i j h' h2' he' hle hi_even hj_even hi_le hj_le p hp]
  have hpaths : ∀ {γ : Type} (F : Graph ℕ (ℕ × ℕ × ℕ) → Set γ) {x : γ},
      (x ∈ ⋃ b ∈ E(W₁.baseGraph), F (W₁.subdivisionPaths b)) ↔
      (x ∈ ⋃ b ∈ E(W₂.baseGraph), F (W₂.subdivisionPaths b)) := by
    intro γ F x
    simp only [Set.mem_iUnion, exists_prop]
    constructor
    · rintro ⟨b, hb, hx⟩
      obtain ⟨p, q, hadj, rfl⟩ := W₁.exists_baseEdge_eq hb
      refine ⟨W₂.baseEdge hadj, (W₂.baseIso.edgeEquiv (GM13.elementaryWallEdge hadj)).2, ?_⟩
      rwa [← W.subwallAt_toGMWall_subdivisionPaths_baseEdge_eq h2 he hW i j h' h2' he' hle
        hi_even hj_even hi_le hj_le hadj]
    · rintro ⟨b, hb, hx⟩
      obtain ⟨p, q, hadj, rfl⟩ := W₂.exists_baseEdge_eq hb
      refine ⟨W₁.baseEdge hadj, (W₁.baseIso.edgeEquiv (GM13.elementaryWallEdge hadj)).2, ?_⟩
      rwa [W.subwallAt_toGMWall_subdivisionPaths_baseEdge_eq h2 he hW i j h' h2' he' hle
        hi_even hj_even hi_le hj_le hadj]
  apply graph_eq_of_le_of_vertexSet_eq_of_edgeSet_eq hle₁ hle₂
  · rw [W₁.vertexSet_eq, W₂.vertexSet_eq, hbaseV]
    ext x
    simp only [Set.mem_union]
    exact or_congr_right (hpaths (fun P => V(P)))
  · rw [W₁.edgeSet_eq, W₂.edgeSet_eq]
    ext e
    exact hpaths (fun P => E(P))

/-- `(W.subwallAt ...).toGMWall` and `W.toGMSubwallAt` have the exact same perimeter subgraph. -/
theorem subwallAt_toGMWall_perimeter_eq (h2 : 2 ≤ h) (he : Even h) (hW : W.IsValid)
    (i j h' : ℕ) (h2' : 2 ≤ h') (he' : Even h') (hle : h' ≤ h)
    (hi_even : Even i) (hj_even : Even j)
    (hi_le : i ≤ 2 * h - 2 * h') (hj_le : j ≤ h - h') :
    ((W.subwallAt i j h' (by omega) hle hi_even hj_even hi_le hj_le).toGMWall h2' he'
      (W.isValid_subwallAt hW i j h' (by omega) hle hi_even hj_even hi_le hj_le)).perimeter =
      (W.toGMSubwallAt h2 he hW i j h' h2' he' hle hi_even hj_even hi_le hj_le).perimeter := by
  let W₁ := (W.subwallAt i j h' (by omega) hle hi_even hj_even hi_le hj_le).toGMWall h2' he'
    (W.isValid_subwallAt hW i j h' (by omega) hle hi_even hj_even hi_le hj_le)
  let W₂ := W.toGMSubwallAt h2 he hW i j h' h2' he' hle hi_even hj_even hi_le hj_le
  unfold GM13.Wall.perimeter
  have hG : W₁.graph = W₂.graph :=
    W.subwallAt_toGMWall_graph_eq h2 he hW i j h' h2' he' hle hi_even hj_even hi_le hj_le
  have hH : W₁.height = h' := rfl
  have hH2 : W₂.height = h' := rfl
  rw [hG]
  congr 1
  ext P
  simp only [Set.mem_ofPred_eq]
  refine exists_congr fun e₀ => exists_congr fun he₀ => ?_
  rcases he₀ with ⟨p, q, ⟨hadj, rfl⟩, _⟩
  have h1 : W₁.subdivisionPaths (W₁.baseIso.edgeEquiv ⟨s(p, q), ⟨p, q, hadj, rfl⟩⟩).1 =
      W₁.subdivisionPaths (W₁.baseEdge hadj) := rfl
  have h2_eq : W₂.subdivisionPaths (W₂.baseIso.edgeEquiv ⟨s(p, q), ⟨p, q, hadj, rfl⟩⟩).1 =
      W₂.subdivisionPaths (W₂.baseEdge hadj) := rfl
  rw [h1, h2_eq, W.subwallAt_toGMWall_subdivisionPaths_baseEdge_eq h2 he hW i j h' h2' he' hle
    hi_even hj_even hi_le hj_le hadj]

/-- `(W.subwallAt ...).toGMWall` and `W.toGMSubwallAt` have the exact same `insideVerts`. -/
theorem subwallAt_toGMWall_insideVerts_eq (h2 : 2 ≤ h) (he : Even h) (hW : W.IsValid)
    (i j h' : ℕ) (h2' : 2 ≤ h') (he' : Even h') (hle : h' ≤ h)
    (hi_even : Even i) (hj_even : Even j)
    (hi_le : i ≤ 2 * h - 2 * h') (hj_le : j ≤ h - h') :
    ((W.subwallAt i j h' (by omega) hle hi_even hj_even hi_le hj_le).toGMWall h2' he'
      (W.isValid_subwallAt hW i j h' (by omega) hle hi_even hj_even hi_le hj_le)).insideVerts =
      (W.toGMSubwallAt h2 he hW i j h' h2' he' hle hi_even hj_even hi_le hj_le).insideVerts := by
  unfold GM13.Wall.insideVerts
  rw [W.subwallAt_toGMWall_graph_eq h2 he hW i j h' h2' he' hle hi_even hj_even hi_le hj_le,
    W.subwallAt_toGMWall_perimeter_eq h2 he hW i j h' h2' he' hle hi_even hj_even hi_le hj_le]

/-- `(W.subwallAt ...).toGMWall` and `W.toGMSubwallAt` have the exact same corners. -/
theorem subwallAt_toGMWall_corner_eq (h2 : 2 ≤ h) (he : Even h) (hW : W.IsValid)
    (i j h' : ℕ) (h2' : 2 ≤ h') (he' : Even h') (hle : h' ≤ h)
    (hi_even : Even i) (hj_even : Even j)
    (hi_le : i ≤ 2 * h - 2 * h') (hj_le : j ≤ h - h') (k : Fin 4) :
    ((W.subwallAt i j h' (by omega) hle hi_even hj_even hi_le hj_le).toGMWall h2' he'
      (W.isValid_subwallAt hW i j h' (by omega) hle hi_even hj_even hi_le hj_le)).corner k =
      (W.toGMSubwallAt h2 he hW i j h' h2' he' hle hi_even hj_even hi_le hj_le).corner k := by
  unfold GM13.Wall.corner
  exact W.subwallAt_toGMWall_branchVertex_eq h2 he hW i j h' h2' he' hle hi_even hj_even hi_le hj_le
    (GM13.elementaryWallCorner h' k) (elementaryWallCorner_mem_elementaryWallVerts h2' k)

theorem wallCornerCyclicPerm_eq_of_corner_eq {α β : Type*}
    {W₁ W₂ : GM13.Wall α β} (hc : W₁.corner = W₂.corner) :
    GM13.wallCornerCyclicPerm W₁ = GM13.wallCornerCyclicPerm W₂ := by
  unfold GM13.wallCornerCyclicPerm GM13.Wall.corners
  congr 1 <;> simp only [hc]

/-- `(W.subwallAt ...).toGMWall` and `W.toGMSubwallAt` have the exact same `wallCornerCyclicPerm`. -/
theorem subwallAt_toGMWall_wallCornerCyclicPerm_eq (h2 : 2 ≤ h) (he : Even h) (hW : W.IsValid)
    (i j h' : ℕ) (h2' : 2 ≤ h') (he' : Even h') (hle : h' ≤ h)
    (hi_even : Even i) (hj_even : Even j)
    (hi_le : i ≤ 2 * h - 2 * h') (hj_le : j ≤ h - h') :
    GM13.wallCornerCyclicPerm
      ((W.subwallAt i j h' (by omega) hle hi_even hj_even hi_le hj_le).toGMWall h2' he'
        (W.isValid_subwallAt hW i j h' (by omega) hle hi_even hj_even hi_le hj_le)) =
      GM13.wallCornerCyclicPerm
        (W.toGMSubwallAt h2 he hW i j h' h2' he' hle hi_even hj_even hi_le hj_le) := by
  apply wallCornerCyclicPerm_eq_of_corner_eq
  ext k
  exact W.subwallAt_toGMWall_corner_eq h2 he hW i j h' h2' he' hle hi_even hj_even hi_le hj_le k

/-- `(W.subwallAt ...).toGMWall` and `W.toGMSubwallAt` have the exact same `wallCompass` in any
graph `G₀`. -/
theorem subwallAt_toGMWall_wallCompass_eq (G₀ : Graph ℕ (ℕ × ℕ × ℕ))
    (h2 : 2 ≤ h) (he : Even h) (hW : W.IsValid)
    (i j h' : ℕ) (h2' : 2 ≤ h') (he' : Even h') (hle : h' ≤ h)
    (hi_even : Even i) (hj_even : Even j)
    (hi_le : i ≤ 2 * h - 2 * h') (hj_le : j ≤ h - h') :
    GM13.wallCompass G₀
      ((W.subwallAt i j h' (by omega) hle hi_even hj_even hi_le hj_le).toGMWall h2' he'
        (W.isValid_subwallAt hW i j h' (by omega) hle hi_even hj_even hi_le hj_le)) =
      GM13.wallCompass G₀
        (W.toGMSubwallAt h2 he hW i j h' h2' he' hle hi_even hj_even hi_le hj_le) := by
  unfold GM13.wallCompass GM13.wallCompassVerts
  rw [W.subwallAt_toGMWall_perimeter_eq h2 he hW i j h' h2' he' hle hi_even hj_even hi_le hj_le,
    W.subwallAt_toGMWall_insideVerts_eq h2 he hW i j h' h2' he' hle hi_even hj_even hi_le hj_le]

/-! ### Section 2d: Drawn Wall `toDrawnGMWall` and Agreement of `brickDist` with `DrawnWall.dist` -/

/-- Canonical `GM13.DrawnWall ℕ (ℕ × ℕ × ℕ)` of `W : WallOfHeight h G` drawn as in Fig. 1
(`W.toGMWall.exists_isFigure1CoordDrawing`). -/
noncomputable def toDrawnGMWall (h2 : 2 ≤ h) (he : Even h) (hW : W.IsValid) :
    GM13.DrawnWall ℕ (ℕ × ℕ × ℕ) :=
  let W_gm := W.toGMWall h2 he hW
  let Γ := Classical.choose W_gm.exists_isFigure1CoordDrawing
  { toWall := W_gm
    drawingU := Γ.drawing.U
    vertexPoint := GM13.ptV Γ
    vertexPoint_mem := fun _ hu => Γ.drawing.V_subset_U (GM13.ptV_mem_V Γ hu)
    vertexPoint_injOn := GM13.ptV_injOn Γ }

@[simp]
theorem toDrawnGMWall_toWall (h2 : 2 ≤ h) (he : Even h) (hW : W.IsValid) :
    (W.toDrawnGMWall h2 he hW).toWall = W.toGMWall h2 he hW := rfl

@[simp]
theorem toDrawnGMWall_graph (h2 : 2 ≤ h) (he : Even h) (hW : W.IsValid) :
    (W.toDrawnGMWall h2 he hW).graph = (W.toGMWall h2 he hW).graph := rfl

@[simp]
theorem toDrawnGMWall_height (h2 : 2 ≤ h) (he : Even h) (hW : W.IsValid) :
    (W.toDrawnGMWall h2 he hW).height = h := rfl

/-- `W.toDrawnGMWall h2 he hW` is drawn as in Fig. 1 (`GM13.DrawnWall.IsFigure1`). -/
theorem isFigure1_toDrawnGMWall (h2 : 2 ≤ h) (he : Even h) (hW : W.IsValid) :
    (W.toDrawnGMWall h2 he hW).IsFigure1 := by
  let W_gm := W.toGMWall h2 he hW
  let Γ := Classical.choose W_gm.exists_isFigure1CoordDrawing
  have hΓ : GM13.IsFigure1CoordDrawing W_gm Γ :=
    Classical.choose_spec W_gm.exists_isFigure1CoordDrawing
  refine ⟨Homeomorph.refl Surface.EuclideanPlane, Γ, hΓ, ?_, ?_⟩
  · change Γ.drawing.U = (Homeomorph.refl Surface.EuclideanPlane) '' Γ.drawing.U
    simp
  · intro u hu
    change GM13.ptV Γ u = (Γ.iso.vertexEquiv ⟨u, hu⟩).1
    exact GM13.ptV_of_mem Γ hu

theorem elemWallVertCell_eq_vCell (h : ℕ) (u : Fin (elemWallNumVerts h)) :
    elemWallVertCell h u = GM13.vCell (elemWallVertCoord h u) := rfl

theorem edgeCell_eq_eCell_of_isElemWallEdgeCoord {p₁ p₂ : ℕ × ℕ}
    (hadj : isElemWallEdgeCoord p₁ p₂ = true) :
    (if p₁.2 = p₂.2 then (2 * (p₁.1 : ℤ) + 1, 2 * (p₁.2 : ℤ))
     else (2 * (p₁.1 : ℤ), 2 * (p₁.2 : ℤ) + 1)) =
      GM13.eCell p₁ p₂ := by
  unfold isElemWallEdgeCoord GM13.eCell at *
  simp only [Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq] at hadj
  rcases hadj with ⟨hy, hx⟩ | ⟨⟨hx, hy⟩, _⟩
  · rw [ite_eq_left_iff.mpr (fun h => False.elim (h hy))]
    ext <;> omega
  · have hne : p₁.2 ≠ p₂.2 := by omega
    rw [ite_eq_right_iff.mpr (fun h => False.elim (hne h))]
    ext <;> omega

theorem elemWallEdgeCell_eq_eCell (h : ℕ) (k : Fin (elemWallEdges h).length) :
    let e := (elemWallEdges h)[k.1]'k.2
    elemWallEdgeCell h k =
      GM13.eCell (elemWallVertCoord h e.1) (elemWallVertCoord h e.2) :=
  edgeCell_eq_eCell_of_isElemWallEdgeCoord (elemWallEdge_isElemWallEdgeCoord h k)

theorem vertCell_branchVert_s9 (hW : W.IsValid) (u : Fin (elemWallNumVerts h)) :
    W.vertCell (W.branchVert u) = elemWallVertCell h u := by
  unfold vertCell
  cases hfind : (List.finRange (elemWallNumVerts h)).find?
      (fun u' => decide (W.branchVert u' = W.branchVert u)) with
  | none =>
    have hfalse := List.find?_eq_none.mp hfind u (List.mem_finRange u)
    simp at hfalse
  | some u' =>
    have heq : W.branchVert u' = W.branchVert u := by
      simpa using List.find?_some hfind
    rw [hW.1 heq]

theorem vertCell_of_mem_internalVerts_s9 (hW : W.IsValid)
    (k : Fin (elemWallEdges h).length) {v : Fin n} (hv : v ∈ W.internalVerts k) :
    W.vertCell v = elemWallEdgeCell h k := by
  unfold vertCell
  have hfind1 : (List.finRange (elemWallNumVerts h)).find?
      (fun u => decide (W.branchVert u = v)) = none := by
    rw [List.find?_eq_none]
    intro u _
    simp only [decide_eq_true_eq]
    intro heq
    subst heq
    exact hW.2.2.1 k u hv
  rw [hfind1]
  cases hfind2 : (List.finRange (elemWallEdges h).length).find?
      (fun k' => decide (v ∈ W.internalVerts k')) with
  | none =>
    have hfalse := List.find?_eq_none.mp hfind2 k (List.mem_finRange k)
    simp [hv] at hfalse
  | some k' =>
    have hv' : v ∈ W.internalVerts k' := by
      simpa using List.find?_some hfind2
    have hk_eq : k' = k := by
      by_contra hne
      exact hW.2.2.2 k' k hne hv' hv
    rw [hk_eq]

/-- Every vertex `v ∈ W.vertexFinset` has `W.vertCell v ∈ GM13.fig1WallCells h` and
`v.1 ∈ (W.toGMWall h2 he hW).elemV (W.vertCell v)`. -/
theorem vertCell_mem_fig1WallCells_and_elemV (h2 : 2 ≤ h) (he : Even h) (hW : W.IsValid)
    {v : Fin n} (hv : v ∈ W.vertexFinset) :
    W.vertCell v ∈ GM13.fig1WallCells h ∧
      v.1 ∈ (W.toGMWall h2 he hW).elemV (W.vertCell v) := by
  let W_gm := W.toGMWall h2 he hW
  rw [W.mem_vertexFinset_iff] at hv
  rcases hv with ⟨u, rfl⟩ | ⟨k, hvk⟩
  · rw [W.vertCell_branchVert_s9 hW u, elemWallVertCell_eq_vCell]
    have hp := elemWallVertCoord_mem_elementaryWallVerts h u
    refine ⟨GM13.mem_fig1WallCells_vCell h2 he hp, ?_⟩
    have hbr : (W.branchVert u).1 = W_gm.branchVertex (elemWallVertCoord h u) hp :=
      (W.toGMWall_branchVertex_elemWallVertCoord h2 he hW u).symm
    rw [hbr]
    exact W_gm.branchVertex_mem_elemV hp
  · rw [W.vertCell_of_mem_internalVerts_s9 hW k hvk, elemWallEdgeCell_eq_eCell]
    let e := (elemWallEdges h)[k.1]'k.2
    have hadj : GM13.elementaryWallAdj h (elemWallVertCoord h e.1) (elemWallVertCoord h e.2) :=
      elemWallEdge_elementaryWallAdj h k
    refine ⟨GM13.mem_fig1WallCells_eCell h2 he hadj, ?_⟩
    rw [W_gm.mem_elemV_eCell hadj]
    have hsub_eq : W_gm.subdivisionPaths (W_gm.baseEdge hadj) = W.subdivPathGraph hW k := by
      have h1 : W_gm.subdivisionPaths (W_gm.baseEdge hadj) =
          W.subdivPathOfSym2 hW s(elemWallVertCoord h e.1, elemWallVertCoord h e.2) :=
        W.toGMWall_subdivisionPaths_baseEdge_s9 h2 he hW hadj
      rw [h1]
      exact W.subdivPathOfSym2_elemWallEdgeSym2 hW k
    rw [hsub_eq, W.vertexSet_subdivPathGraph hW k]
    refine ⟨?_, ?_⟩
    · simp only [Set.mem_ofPred_eq, List.mem_map]
      exact ⟨v, (W.mem_subdivPathVerts_iff k v).mpr (Or.inr (Or.inl hvk)), rfl⟩
    · intro hvB
      have hvB' : v.1 ∈ W.branchVertAtCoord '' GM13.elementaryWallVerts h := hvB
      rw [W.image_branchVertAtCoord_eq] at hvB'
      rcases hvB' with ⟨u, hu⟩
      have hvu : v = W.branchVert u := Fin.ext hu.symm
      subst hvu
      exact hW.2.2.1 k u hvk

theorem fig1CellBrickDist_self {h : ℕ} {m : ℤ × ℤ} (hm : m ∈ GM13.fig1WallCells h) :
    fig1CellBrickDist h m m = 2 := by
  unfold fig1CellBrickDist
  rw [GM13.cellInd_of_mem hm]
  have h0 : sInf ((fun qq' : (ℤ × ℤ) × (ℤ × ℤ) =>
      (GM13.faceDist h (GM13.wallFace h qq'.1) (GM13.wallFace h qq'.2)).toNat) ''
      (GM13.squaresAbove m ×ˢ GM13.squaresAbove m)) = 0 := by
    apply Nat.eq_zero_of_le_zero
    obtain ⟨q, hq⟩ := GM13.squaresAbove_nonempty m
    refine Nat.sInf_le ⟨(q, q), ⟨hq, hq⟩, ?_⟩
    dsimp only
    rw [GM13.faceDist_self (GM13.isBrick_or_eq_outFace_wallFace h q)]
    rfl
  omega

/-- **Exact Agreement of `W.brickDist` and `(W.toDrawnGMWall h2 he hW).dist` on `W.vertexFinset`:**
For any two vertices `u, v ∈ W.vertexFinset`, `(W.toDrawnGMWall h2 he hW).dist u.1 v.1` equals
`W.brickDist u v` on the nose. -/
theorem toDrawnGMWall_dist_eq_brickDist (h2 : 2 ≤ h) (he : Even h) (hW : W.IsValid)
    {u v : Fin n} (hu : u ∈ W.vertexFinset) (hv : v ∈ W.vertexFinset) :
    (W.toDrawnGMWall h2 he hW).dist u.1 v.1 = W.brickDist u v := by
  by_cases huv : u = v
  · subst huv
    simp [GM13.DrawnWall.dist, GM13.DrawnWall.planeDist, GM13.planeWallDist, brickDist]
  · have hh1 : 1 ≤ h := Nat.le_trans (by decide) h2
    let W_gm := W.toGMWall h2 he hW
    let Γ := Classical.choose W_gm.exists_isFigure1CoordDrawing
    have hΓ : GM13.IsFigure1CoordDrawing W_gm Γ :=
      Classical.choose_spec W_gm.exists_isFigure1CoordDrawing
    have hD : GM13.DrawnOnCells Γ W_gm (GM13.CellWall.fig1 hh1 he) :=
      GM13.drawnOnCells_fig1 hΓ hh1 he
    obtain ⟨hmu, hu_elem⟩ := W.vertCell_mem_fig1WallCells_and_elemV h2 he hW hu
    obtain ⟨hmv, hv_elem⟩ := W.vertCell_mem_fig1WallCells_and_elemV h2 he hW hv
    obtain ⟨s, hs_cell, hs_pt⟩ := hD.exists_cell hmu hu_elem
    obtain ⟨t, ht_cell, ht_pt⟩ := hD.exists_cell hmv hv_elem
    have hs_code : GM13.cellCode s = W.vertCell u := by
      change GM13.cellCode s ∈ ({W.vertCell u} : Set (ℤ × ℤ)) at hs_cell
      exact Set.mem_singleton_iff.mp hs_cell
    have ht_code : GM13.cellCode t = W.vertCell v := by
      change GM13.cellCode t ∈ ({W.vertCell v} : Set (ℤ × ℤ)) at ht_cell
      exact Set.mem_singleton_iff.mp ht_cell
    have hdist_eq :
        (W.toDrawnGMWall h2 he hW).dist u.1 v.1 =
          GM13.planeWallDist (GM13.fig1WallSet h) (GM13.fig1PlaneEquiv s) (GM13.fig1PlaneEquiv t) := by
      unfold toDrawnGMWall GM13.DrawnWall.dist GM13.DrawnWall.planeDist
      dsimp only
      rw [hΓ.drawing_U_eq, hs_pt, ht_pt]
      rfl
    rw [hdist_eq]
    by_cases hc : W.vertCell u = W.vertCell v
    · have hU : GM13.fig1WallSet h =
          GM13.fig1PlaneEquiv '' GM13.cellSet (GM13.CellWall.fig1 hh1 he).𝒰 := by
        rw [GM13.fig1WallSet_eq_cellSet]
        rfl
      rw [hU]
      have ht_cell' : GM13.cellCode t ∈ (GM13.CellWall.fig1 hh1 he).cells (W.vertCell u) := by
        rw [hc]
        exact ht_cell
      have hle2 :
          GM13.planeWallDist
            (GM13.fig1PlaneEquiv '' GM13.cellSet (GM13.CellWall.fig1 hh1 he).𝒰)
            (GM13.fig1PlaneEquiv s) (GM13.fig1PlaneEquiv t) ≤ 2 :=
        (GM13.CellWall.fig1 hh1 he).planeWallDist_le_two hmu hs_cell ht_cell'
      have hu_memG : u.1 ∈ V(W_gm.graph) := W_gm.elemV_subset _ hu_elem
      have hv_memG : v.1 ∈ V(W_gm.graph) := W_gm.elemV_subset _ hv_elem
      have hne_pt : GM13.fig1PlaneEquiv s ≠ GM13.fig1PlaneEquiv t := by
        rw [← hs_pt, ← ht_pt]
        exact fun heq => huv (Fin.ext (GM13.ptV_injOn Γ hu_memG hv_memG heq))
      have hs_memU : s ∈ GM13.cellSet (GM13.CellWall.fig1 hh1 he).𝒰 :=
        (GM13.CellWall.fig1 hh1 he).mem_U_of_mem_cells hmu hs_cell
      have ht_memU : t ∈ GM13.cellSet (GM13.CellWall.fig1 hh1 he).𝒰 :=
        (GM13.CellWall.fig1 hh1 he).mem_U_of_mem_cells hmu ht_cell'
      have hge2 :
          2 ≤ GM13.planeWallDist
            (GM13.fig1PlaneEquiv '' GM13.cellSet (GM13.CellWall.fig1 hh1 he).𝒰)
            (GM13.fig1PlaneEquiv s) (GM13.fig1PlaneEquiv t) :=
        GM13.CellWall.two_le_planeWallDist
          (GM13.CellWall.fig1 hh1 he).naming.not_square hne_pt
          ⟨s, hs_memU, rfl⟩ ⟨t, ht_memU, rfl⟩
      have hbrick2 : W.brickDist u v = 2 := by
        unfold brickDist
        rw [ite_eq_right_iff.mpr (fun h => False.elim (huv h)), hc]
        exact fig1CellBrickDist_self hmv
      omega
    · have hst : GM13.cellCode s ≠ GM13.cellCode t := by rw [hs_code, ht_code]; exact hc
      rw [planeWallDist_fig1_eq_fig1CellBrickDist hh1 he hst, hs_code, ht_code]
      simp [brickDist, huv]

/-- Two subwalls `W₁, W₂` of `W` are at brick distance at least `r` (`d(W₁, W₂) ≥ r`,
GM XIII Section 9, page 98) if `r ≤ W.brickDist u v` for all `u ∈ W₁.vertexFinset` and
`v ∈ W₂.vertexFinset`. -/
def SubwallDistGe {h₁ h₂ : ℕ} (W₁ : WallOfHeight h₁ G) (W₂ : WallOfHeight h₂ G) (r : ℕ) : Prop :=
  ∀ u ∈ W₁.vertexFinset, ∀ v ∈ W₂.vertexFinset, r ≤ W.brickDist u v

/-- **Exact Agreement of `W.SubwallDistGe W₁ W₂ r` and `r ≤ GM13.wallSubgraphDist`:**
If `W₁` and `W₂` are valid walls with vertex sets contained in `W.vertexFinset`, then
`W.SubwallDistGe W₁ W₂ r` holds if and only if
`r ≤ GM13.wallSubgraphDist (W.toDrawnGMWall h2 he hW) (W₁.toGMWall h2₁ he₁ hW₁).graph (W₂.toGMWall h2₂ he₂ hW₂).graph`. -/
theorem subwallDistGe_iff_le_wallSubgraphDist (h2 : 2 ≤ h) (he : Even h) (hW : W.IsValid)
    {h₁ h₂ : ℕ} (h2₁ : 2 ≤ h₁) (he₁ : Even h₁) (h2₂ : 2 ≤ h₂) (he₂ : Even h₂)
    {W₁ : WallOfHeight h₁ G} {W₂ : WallOfHeight h₂ G}
    (hW₁ : W₁.IsValid) (hW₂ : W₂.IsValid)
    (hsub₁ : W₁.vertexFinset ⊆ W.vertexFinset) (hsub₂ : W₂.vertexFinset ⊆ W.vertexFinset)
    (r : ℕ) :
    W.SubwallDistGe W₁ W₂ r ↔
      r ≤ GM13.wallSubgraphDist (W.toDrawnGMWall h2 he hW)
        (W₁.toGMWall h2₁ he₁ hW₁).graph (W₂.toGMWall h2₂ he₂ hW₂).graph := by
  constructor
  · intro hdist
    unfold GM13.wallSubgraphDist
    let S : Set ℕ :=
      {k : ℕ | ∃ v₁ ∈ V((W₁.toGMWall h2₁ he₁ hW₁).graph),
        ∃ v₂ ∈ V((W₂.toGMWall h2₂ he₂ hW₂).graph),
        (W.toDrawnGMWall h2 he hW).dist v₁ v₂ = k}
    have hne : S.Nonempty := by
      have hu₁ : W₁.seedVert h2₁ ∈ W₁.vertexFinset :=
        Finset.sdiff_subset (W₁.seedVert_mem_insideFinset h2₁ hW₁)
      have hu₂ : W₂.seedVert h2₂ ∈ W₂.vertexFinset :=
        Finset.sdiff_subset (W₂.seedVert_mem_insideFinset h2₂ hW₂)
      have h1 := W₁.vertexSet_toGMWall_eq h2₁ he₁ hW₁
      have h2' := W₂.vertexSet_toGMWall_eq h2₂ he₂ hW₂
      exact ⟨_, ⟨(W₁.seedVert h2₁).1, by rw [h1]; exact ⟨_, hu₁, rfl⟩,
        (W₂.seedVert h2₂).1, by rw [h2']; exact ⟨_, hu₂, rfl⟩, rfl⟩⟩
    have hmem : sInf S ∈ S := Nat.sInf_mem hne
    rcases hmem with ⟨x₁, hx₁, x₂, hx₂, h_sInf⟩
    rw [W₁.vertexSet_toGMWall_eq h2₁ he₁ hW₁] at hx₁
    rw [W₂.vertexSet_toGMWall_eq h2₂ he₂ hW₂] at hx₂
    rcases hx₁ with ⟨u₁, hu₁, rfl⟩
    rcases hx₂ with ⟨u₂, hu₂, rfl⟩
    have h1 := hdist u₁ hu₁ u₂ hu₂
    have h2' := W.toDrawnGMWall_dist_eq_brickDist h2 he hW (hsub₁ hu₁) (hsub₂ hu₂)
    change r ≤ sInf S
    rw [← h_sInf, h2']
    exact h1
  · intro hdist u₁ hu₁ u₂ hu₂
    have hx₁ : u₁.1 ∈ V((W₁.toGMWall h2₁ he₁ hW₁).graph) := by
      rw [W₁.vertexSet_toGMWall_eq h2₁ he₁ hW₁]
      exact ⟨u₁, hu₁, rfl⟩
    have hx₂ : u₂.1 ∈ V((W₂.toGMWall h2₂ he₂ hW₂).graph) := by
      rw [W₂.vertexSet_toGMWall_eq h2₂ he₂ hW₂]
      exact ⟨u₂, hu₂, rfl⟩
    have hsInf_le :
        GM13.wallSubgraphDist (W.toDrawnGMWall h2 he hW)
          (W₁.toGMWall h2₁ he₁ hW₁).graph (W₂.toGMWall h2₂ he₂ hW₂).graph ≤
        (W.toDrawnGMWall h2 he hW).dist u₁.1 u₂.1 :=
      Nat.sInf_le ⟨u₁.1, hx₁, u₂.1, hx₂, rfl⟩
    rw [W.toDrawnGMWall_dist_eq_brickDist h2 he hW (hsub₁ hu₁) (hsub₂ hu₂)] at hsInf_le
    exact hdist.trans hsInf_le

/-! ### Section 2e: `H`-Paths, Dividing Subwalls, Crosses, Flat Walls, and `(l, m)`-Stars -/

theorem two_le_of_isSubwallOf {h' : ℕ} {W' : WallOfHeight h' G} (hsub : W'.IsSubwallOf W) :
    2 ≤ h' :=
  hsub.choose

theorem even_of_isSubwallOf {h' : ℕ} {W' : WallOfHeight h' G} (hsub : W'.IsSubwallOf W) :
    Even h' :=
  hsub.choose_spec.choose

theorem isValid_of_isSubwallOf (hW : W.IsValid) {h' : ℕ} {W' : WallOfHeight h' G}
    (hsub : W'.IsSubwallOf W) :
    W'.IsValid := by
  rcases hsub with ⟨h2', _, hle, i, j, hi_even, hj_even, hi_le, hj_le, rfl⟩
  exact W.isValid_subwallAt hW i j h' (by omega) hle hi_even hj_even hi_le hj_le

theorem subwall_vertexFinset_subset {h' : ℕ} {W' : WallOfHeight h' G}
    (hsub : W'.IsSubwallOf W) :
    W'.vertexFinset ⊆ W.vertexFinset := by
  rcases hsub with ⟨_, _, hle, i, j, hi_even, hj_even, hi_le, hj_le, rfl⟩
  exact W.subwallAt_vertexFinset_subset i j h' (by omega) hle hi_even hj_even hi_le hj_le

/-- Turn a subwall `W'` of `W` (`hsub : W'.IsSubwallOf W`) into a `GM13.Wall ℕ (ℕ × ℕ × ℕ)` that
satisfies `GM13.Wall.IsSubwallOf (W.toGMWall h2 he hW)` and shares the same graph, perimeter,
inside vertices, corners, and compass as `W'.toGMWall`. -/
noncomputable def toGMSubwallOf (h2 : 2 ≤ h) (he : Even h) (hW : W.IsValid)
    {h' : ℕ} {W' : WallOfHeight h' G} (hsub : W'.IsSubwallOf W) :
    GM13.Wall ℕ (ℕ × ℕ × ℕ) :=
  let h2' := hsub.choose
  let s1 := hsub.choose_spec
  let he' := s1.choose
  let s2 := s1.choose_spec
  let hle := s2.choose
  let s3 := s2.choose_spec
  let i := s3.choose
  let s4 := s3.choose_spec
  let j := s4.choose
  let s5 := s4.choose_spec
  let hi_even := s5.choose
  let s6 := s5.choose_spec
  let hj_even := s6.choose
  let s7 := s6.choose_spec
  let hi_le := s7.choose
  let s8 := s7.choose_spec
  let hj_le := s8.choose
  W.toGMSubwallAt h2 he hW i j h' h2' he' hle hi_even hj_even hi_le hj_le

theorem toGMSubwallOf_isSubwallOf (h2 : 2 ≤ h) (he : Even h) (hW : W.IsValid)
    {h' : ℕ} {W' : WallOfHeight h' G} (hsub : W'.IsSubwallOf W) :
    (W.toGMSubwallOf h2 he hW hsub).IsSubwallOf (W.toGMWall h2 he hW) :=
  W.toGMSubwallAt_isSubwallOf h2 he hW _ _ _ _ _ _ _ _ _ _

theorem toGMWall_eq_of_eq {h' : ℕ} {W₁ W₂ : WallOfHeight h' G} (h2' : 2 ≤ h') (he' : Even h')
    {hW₁ : W₁.IsValid} {hW₂ : W₂.IsValid} (heq : W₁ = W₂) :
    W₁.toGMWall h2' he' hW₁ = W₂.toGMWall h2' he' hW₂ := by
  subst heq
  rfl

theorem toGMSubwallOf_graph_eq (h2 : 2 ≤ h) (he : Even h) (hW : W.IsValid)
    {h' : ℕ} {W' : WallOfHeight h' G} (hsub : W'.IsSubwallOf W)
    (h2' : 2 ≤ h') (he' : Even h') (hW' : W'.IsValid) :
    (W.toGMSubwallOf h2 he hW hsub).graph = (W'.toGMWall h2' he' hW').graph := by
  let s1 := hsub.choose_spec
  let s2 := s1.choose_spec
  let s3 := s2.choose_spec
  let s4 := s3.choose_spec
  let s5 := s4.choose_spec
  let s6 := s5.choose_spec
  let s7 := s6.choose_spec
  let s8 := s7.choose_spec
  have hW'_eq : W' = W.subwallAt s3.choose s4.choose h' _ s2.choose
      s5.choose s6.choose s7.choose s8.choose := s8.choose_spec
  have h1 := W.subwallAt_toGMWall_graph_eq h2 he hW
    s3.choose s4.choose h' hsub.choose s1.choose s2.choose s5.choose s6.choose s7.choose s8.choose
  change (W.toGMSubwallAt h2 he hW _ _ _ _ _ _ _ _ _ _).graph = (W'.toGMWall h2' he' hW').graph
  rw [← h1]
  exact congrArg GM13.Wall.graph (toGMWall_eq_of_eq h2' he' hW'_eq.symm)

theorem toGMSubwallOf_perimeter_eq (h2 : 2 ≤ h) (he : Even h) (hW : W.IsValid)
    {h' : ℕ} {W' : WallOfHeight h' G} (hsub : W'.IsSubwallOf W)
    (h2' : 2 ≤ h') (he' : Even h') (hW' : W'.IsValid) :
    (W.toGMSubwallOf h2 he hW hsub).perimeter = (W'.toGMWall h2' he' hW').perimeter := by
  let s1 := hsub.choose_spec
  let s2 := s1.choose_spec
  let s3 := s2.choose_spec
  let s4 := s3.choose_spec
  let s5 := s4.choose_spec
  let s6 := s5.choose_spec
  let s7 := s6.choose_spec
  let s8 := s7.choose_spec
  have hW'_eq : W' = W.subwallAt s3.choose s4.choose h' _ s2.choose
      s5.choose s6.choose s7.choose s8.choose := s8.choose_spec
  have h1 := W.subwallAt_toGMWall_perimeter_eq h2 he hW
    s3.choose s4.choose h' hsub.choose s1.choose s2.choose s5.choose s6.choose s7.choose s8.choose
  change (W.toGMSubwallAt h2 he hW _ _ _ _ _ _ _ _ _ _).perimeter =
    (W'.toGMWall h2' he' hW').perimeter
  rw [← h1]
  exact congrArg GM13.Wall.perimeter (toGMWall_eq_of_eq h2' he' hW'_eq.symm)

theorem toGMSubwallOf_insideVerts_eq (h2 : 2 ≤ h) (he : Even h) (hW : W.IsValid)
    {h' : ℕ} {W' : WallOfHeight h' G} (hsub : W'.IsSubwallOf W)
    (h2' : 2 ≤ h') (he' : Even h') (hW' : W'.IsValid) :
    (W.toGMSubwallOf h2 he hW hsub).insideVerts = (W'.toGMWall h2' he' hW').insideVerts := by
  unfold GM13.Wall.insideVerts
  rw [W.toGMSubwallOf_graph_eq h2 he hW hsub h2' he' hW',
    W.toGMSubwallOf_perimeter_eq h2 he hW hsub h2' he' hW']

theorem toGMSubwallOf_wallCompass_eq (G₀ : Graph ℕ (ℕ × ℕ × ℕ))
    (h2 : 2 ≤ h) (he : Even h) (hW : W.IsValid)
    {h' : ℕ} {W' : WallOfHeight h' G} (hsub : W'.IsSubwallOf W)
    (h2' : 2 ≤ h') (he' : Even h') (hW' : W'.IsValid) :
    GM13.wallCompass G₀ (W.toGMSubwallOf h2 he hW hsub) =
      GM13.wallCompass G₀ (W'.toGMWall h2' he' hW') := by
  unfold GM13.wallCompass GM13.wallCompassVerts
  rw [W.toGMSubwallOf_perimeter_eq h2 he hW hsub h2' he' hW',
    W.toGMSubwallOf_insideVerts_eq h2 he hW hsub h2' he' hW']

theorem toGMSubwallOf_corner_eq (h2 : 2 ≤ h) (he : Even h) (hW : W.IsValid)
    {h' : ℕ} {W' : WallOfHeight h' G} (hsub : W'.IsSubwallOf W)
    (h2' : 2 ≤ h') (he' : Even h') (hW' : W'.IsValid) (k : Fin 4) :
    (W.toGMSubwallOf h2 he hW hsub).corner k = (W'.toGMWall h2' he' hW').corner k := by
  let s1 := hsub.choose_spec
  let s2 := s1.choose_spec
  let s3 := s2.choose_spec
  let s4 := s3.choose_spec
  let s5 := s4.choose_spec
  let s6 := s5.choose_spec
  let s7 := s6.choose_spec
  let s8 := s7.choose_spec
  have hW'_eq : W' = W.subwallAt s3.choose s4.choose h' _ s2.choose
      s5.choose s6.choose s7.choose s8.choose := s8.choose_spec
  have h1 := W.subwallAt_toGMWall_corner_eq h2 he hW
    s3.choose s4.choose h' hsub.choose s1.choose s2.choose s5.choose s6.choose s7.choose s8.choose k
  change (W.toGMSubwallAt h2 he hW _ _ _ _ _ _ _ _ _ _).corner k =
    (W'.toGMWall h2' he' hW').corner k
  rw [← h1]
  exact congrArg (fun W₀ => W₀.corner k) (toGMWall_eq_of_eq h2' he' hW'_eq.symm)

theorem le_wallSubgraphDist_of_le_brickDist (h2 : 2 ≤ h) (he : Even h) (hW : W.IsValid)
    {h₁ h₂ r : ℕ} {W₁ : WallOfHeight h₁ G} {W₂ : WallOfHeight h₂ G}
    (hsub₁ : W₁.IsSubwallOf W) (hsub₂ : W₂.IsSubwallOf W)
    (hdist : ∀ u ∈ W₁.vertexFinset, ∀ v ∈ W₂.vertexFinset, r ≤ W.brickDist u v) :
    r ≤ GM13.wallSubgraphDist (W.toDrawnGMWall h2 he hW)
      (W.toGMSubwallOf h2 he hW hsub₁).graph (W.toGMSubwallOf h2 he hW hsub₂).graph := by
  have h2₁ := W.two_le_of_isSubwallOf hsub₁
  have he₁ := W.even_of_isSubwallOf hsub₁
  have hW₁ := W.isValid_of_isSubwallOf hW hsub₁
  have h2₂ := W.two_le_of_isSubwallOf hsub₂
  have he₂ := W.even_of_isSubwallOf hsub₂
  have hW₂ := W.isValid_of_isSubwallOf hW hsub₂
  rw [W.toGMSubwallOf_graph_eq h2 he hW hsub₁ h2₁ he₁ hW₁,
    W.toGMSubwallOf_graph_eq h2 he hW hsub₂ h2₂ he₂ hW₂]
  exact (W.subwallDistGe_iff_le_wallSubgraphDist h2 he hW h2₁ he₁ h2₂ he₂ hW₁ hW₂
    (W.subwall_vertexFinset_subset hsub₁) (W.subwall_vertexFinset_subset hsub₂) r).mp hdist

theorem mem_wallCompassVerts_toGMWall_iff (h2 : 2 ≤ h) (he : Even h) (hW : W.IsValid)
    (v : Fin n) :
    v.1 ∈ GM13.wallCompassVerts G.toGMDigraph.toGraph (W.toGMWall h2 he hW) ↔
      v ∈ W.compassFinset := by
  have heq := Set.ext_iff.mp (W.val_compassFinset_eq_wallCompassVerts h2 he hW) v.1
  rw [← heq]
  simp only [Set.mem_image, Finset.mem_coe, Fin.val_inj, exists_eq_right]

theorem compassFinset_eq_compassFinsetAvoid_empty :
    W.compassFinset = W.compassFinsetAvoid ∅ := rfl

theorem mem_compassFinset_of_reachable {s v : Fin n} (hs : s ∈ W.insideFinset)
    (hr : (restrictGraph G.toSimpleGraph (Finset.univ \ W.perimeterFinset)).Reachable s v) :
    v ∈ W.compassFinset := by
  unfold compassFinset compassFinsetAvoid
  rw [Finset.mem_union, Finset.mem_biUnion]
  refine Or.inr ⟨s, hs, ?_⟩
  rw [mem_reachSet, Finset.empty_union]
  exact hr

attribute [irreducible] compassFinsetAvoid compassFinset toGMSubwallAt toGMSubwallOf

theorem adj_toSimpleGraph_of_isLink_toGMDigraph {e : ℕ × ℕ × ℕ} {a c : ℕ}
    (hlink : G.toGMDigraph.toGraph.IsLink e a c)
    (hne : (⟨a, hlink.left_mem⟩ : Fin n) ≠ ⟨c, hlink.right_mem⟩) :
    G.toSimpleGraph.Adj ⟨a, hlink.left_mem⟩ ⟨c, hlink.right_mem⟩ := by
  rw [MultiDigraph.toSimpleGraph_adj]
  refine ⟨hne, ?_⟩
  rcases hlink with ⟨⟨hu, hv, hmult⟩, ⟨h1, h2⟩ | ⟨h1, h2⟩⟩
  · right
    have hpos : 0 < G.edgeMult ⟨e.1, hu⟩ ⟨e.2.1, hv⟩ := Nat.zero_lt_of_lt hmult
    convert hpos using 2
    · exact Fin.ext h2.symm
    · exact Fin.ext h1.symm
  · left
    have hpos : 0 < G.edgeMult ⟨e.1, hu⟩ ⟨e.2.1, hv⟩ := Nat.zero_lt_of_lt hmult
    convert hpos using 2
    · exact Fin.ext h2.symm
    · exact Fin.ext h1.symm

/-- Convert a `Surface.GraphWalk G.toGMDigraph.toGraph a b` (`ha : a < n`) into a vertex list
`List (Fin n)`. -/
def graphWalkToFinList :
    ∀ {a b : ℕ} (_w : Surface.GraphWalk G.toGMDigraph.toGraph a b) (_ha : a < n), List (Fin n)
  | a, _, .nil _, ha => [⟨a, ha⟩]
  | a, _, .cons hlink rest, ha =>
    ⟨a, ha⟩ :: graphWalkToFinList rest (show _ < n from hlink.right_mem)

@[simp]
theorem map_val_graphWalkToFinList :
    ∀ {a b : ℕ} (w : Surface.GraphWalk G.toGMDigraph.toGraph a b) (ha : a < n),
      (graphWalkToFinList w ha).map Fin.val = w.support
  | _, _, .nil _, _ => rfl
  | _, _, .cons hlink rest, _ => by
    change _ :: (graphWalkToFinList rest (show _ < n from hlink.right_mem)).map Fin.val =
      _ :: rest.support
    rw [map_val_graphWalkToFinList rest]

theorem graphWalkToFinList_ne_nil {a b : ℕ} (w : Surface.GraphWalk G.toGMDigraph.toGraph a b)
    (ha : a < n) :
    graphWalkToFinList w ha ≠ [] := by
  cases w <;> simp [graphWalkToFinList]

theorem head_graphWalkToFinList :
    ∀ {a b : ℕ} (w : Surface.GraphWalk G.toGMDigraph.toGraph a b) (ha : a < n),
      (graphWalkToFinList w ha).head (graphWalkToFinList_ne_nil w ha) = ⟨a, ha⟩
  | _, _, .nil _, _ => rfl
  | _, _, .cons _ _, _ => rfl

theorem getLast_graphWalkToFinList :
    ∀ {a b : ℕ} (w : Surface.GraphWalk G.toGMDigraph.toGraph a b) (ha : a < n) (hb : b < n),
      (graphWalkToFinList w ha).getLast (graphWalkToFinList_ne_nil w ha) = ⟨b, hb⟩
  | _, _, .nil _, _, _ => rfl
  | _, _, .cons hlink rest, _, hb => by
    have hc : _ < n := hlink.right_mem
    change (⟨_, _⟩ :: graphWalkToFinList rest hc).getLast _ = ⟨_, hb⟩
    rw [List.getLast_cons (graphWalkToFinList_ne_nil rest hc)]
    exact getLast_graphWalkToFinList rest hc hb

theorem mem_graphWalkToFinList_iff {a b : ℕ} (w : Surface.GraphWalk G.toGMDigraph.toGraph a b)
    (ha : a < n) (v : Fin n) :
    v ∈ graphWalkToFinList w ha ↔ v.1 ∈ w.support := by
  rw [← map_val_graphWalkToFinList w ha, List.mem_map_of_injective Fin.val_injective]

theorem nodup_graphWalkToFinList_of_isSimple {a b : ℕ}
    {w : Surface.GraphWalk G.toGMDigraph.toGraph a b} (ha : a < n) (hw : w.IsSimple) :
    (graphWalkToFinList w ha).Nodup := by
  rw [← List.nodup_map_iff Fin.val_injective, map_val_graphWalkToFinList]
  exact hw

theorem isSimpleWalkList_graphWalkToFinList :
    ∀ {a b : ℕ} (w : Surface.GraphWalk G.toGMDigraph.toGraph a b) (ha : a < n),
      w.IsSimple → IsSimpleWalkList G (graphWalkToFinList w ha)
  | _, _, .nil _, _, _ => trivial
  | a, _, .cons (v := c) hlink rest, ha, hw => by
    have hc : c < n := hlink.right_mem
    unfold Surface.GraphWalk.IsSimple at hw
    change (a :: rest.support).Nodup at hw
    rw [List.nodup_cons] at hw
    have hc_mem : c ∈ rest.support := rest.start_mem_support
    have hne : (⟨a, ha⟩ : Fin n) ≠ ⟨c, hc⟩ := by
      intro heq
      have hac : a = c := congrArg Fin.val heq
      exact hw.1 (hac ▸ hc_mem)
    have hadj : G.toSimpleGraph.Adj ⟨a, ha⟩ ⟨c, hc⟩ :=
      adj_toSimpleGraph_of_isLink_toGMDigraph hlink hne
    have hrest := isSimpleWalkList_graphWalkToFinList rest hc hw.2
    change IsSimpleWalkList G (⟨a, ha⟩ :: graphWalkToFinList rest hc)
    cases hlist : graphWalkToFinList rest hc with
    | nil => exact False.elim (graphWalkToFinList_ne_nil rest hc hlist)
    | cons x xs =>
      have hx : x = ⟨c, hc⟩ := by
        have hhead := head_graphWalkToFinList rest hc
        simpa [hlist] using hhead
      subst hx
      rw [hlist] at hrest
      exact ⟨hadj, hrest⟩

theorem two_le_length_of_ne_head_getLast {α : Type*} {L : List α} (hne : L ≠ [])
    (hdiff : L.head hne ≠ L.getLast hne) :
    2 ≤ L.length := by
  rcases L with _ | ⟨x, _ | ⟨y, ys⟩⟩
  · exact False.elim (hne rfl)
  · exact False.elim (hdiff rfl)
  · simp

theorem mem_head_or_drop_one_dropLast_or_getLast {α : Type*} :
    ∀ {L : List α} (hne : L ≠ []) {v : α}, v ∈ L →
      v = L.head hne ∨ v ∈ (L.drop 1).dropLast ∨ v = L.getLast hne
  | [], hne, _, _ => False.elim (hne rfl)
  | [x], _, v, hv => Or.inl (List.mem_singleton.mp hv)
  | x :: y :: ys, _, v, hv => by
    rcases List.mem_cons.mp hv with rfl | htail
    · exact Or.inl rfl
    · have hys : y :: ys ≠ [] := List.cons_ne_nil y ys
      have hsplit : (y :: ys).dropLast ++ [(y :: ys).getLast hys] = y :: ys :=
        List.dropLast_append_getLast hys
      rw [← hsplit, List.mem_append, List.mem_singleton] at htail
      rcases htail with hdl | rfl
      · exact Or.inr (Or.inl hdl)
      · exact Or.inr (Or.inr rfl)

theorem not_mem_drop_one_dropLast_iff {α : Type*} {L : List α} (hne : L ≠ [])
    (h2 : 2 ≤ L.length) (hnd : L.Nodup) (S : Finset α)
    (hhead : L.head hne ∈ S) (hlast : L.getLast hne ∈ S) :
    (∀ v ∈ (L.drop 1).dropLast, v ∉ S) ↔
      (∀ v ∈ L, v ∈ S → v = L.head hne ∨ v = L.getLast hne) := by
  constructor
  · intro hall v hvL hvS
    rcases mem_head_or_drop_one_dropLast_or_getLast hne hvL with rfl | hmid | rfl
    · exact Or.inl rfl
    · exact False.elim (hall v hmid hvS)
    · exact Or.inr rfl
  · intro himp v hv_mid hvS
    rcases L with _ | ⟨x, _ | ⟨y, ys⟩⟩
    · exact False.elim (hne rfl)
    · simp at h2
    · have hys : y :: ys ≠ [] := List.cons_ne_nil y ys
      have hsplit : (y :: ys).dropLast ++ [(y :: ys).getLast hys] = y :: ys :=
        List.dropLast_append_getLast hys
      change v ∈ (y :: ys).dropLast at hv_mid
      have hvL : v ∈ x :: y :: ys := by
        apply List.mem_cons_of_mem x
        rw [← hsplit, List.mem_append]
        exact Or.inl hv_mid
      rw [List.nodup_cons] at hnd
      have hnd_ys := hnd.2
      rw [← hsplit, List.nodup_append] at hnd_ys
      rcases himp v hvL hvS with rfl | rfl
      · apply hnd.1
        rw [← hsplit, List.mem_append]
        exact Or.inl hv_mid
      · change (y :: ys).getLast hys ∈ (y :: ys).dropLast at hv_mid
        exact hnd_ys.2.2 _ hv_mid _ (List.mem_singleton_self _) rfl

/-- If `W.IsWallEdge a b` (`hW : W.IsValid`), then `adjEdgeTriple G u v` (for one of `(a, b)` or
`(b, a)`) links `a.1` and `b.1` in `(W.toGMWall h2 he hW).graph`. -/
theorem exists_isLink_toGMWall_of_isWallEdge_s9 (h2 : 2 ≤ h) (he : Even h) (hW : W.IsValid)
    {a b : Fin n} (hab : W.IsWallEdge a b) :
    ∃ e : ℕ × ℕ × ℕ, (W.toGMWall h2 he hW).graph.IsLink e a.1 b.1 := by
  have hle : (W.toGMWall h2 he hW).graph ≤ G.toGMDigraph.toGraph := W.isWallIn_toGMWall h2 he hW
  rcases hab with ⟨k, h1 | h2'⟩
  · refine ⟨adjEdgeTriple G a b, ?_⟩
    have he_mem : adjEdgeTriple G a b ∈ E((W.toGMWall h2 he hW).graph) := by
      change adjEdgeTriple G a b ∈ E(W.toGMGraph hW)
      rw [W.edgeSet_toGMGraph_iff hW]
      exact ⟨k, a, b, h1, rfl⟩
    have hadj : G.toSimpleGraph.Adj a b :=
      isSimpleWalkList_adj_of_mem_zip (hW.2.1 k).2 h1
    exact (hle.isLink_iff he_mem).mpr (isLink_adjEdgeTriple hadj)
  · refine ⟨adjEdgeTriple G b a, ?_⟩
    have he_mem : adjEdgeTriple G b a ∈ E((W.toGMWall h2 he hW).graph) := by
      change adjEdgeTriple G b a ∈ E(W.toGMGraph hW)
      rw [W.edgeSet_toGMGraph_iff hW]
      exact ⟨k, b, a, h2', rfl⟩
    have hadj : G.toSimpleGraph.Adj b a :=
      isSimpleWalkList_adj_of_mem_zip (hW.2.1 k).2 h2'
    exact ((hle.isLink_iff he_mem).mpr (isLink_adjEdgeTriple hadj)).symm

/-- For any subwall `W'` of `W`, no wall edge of `W` joins a vertex `a ∈ W'.insideFinset` to a
vertex `b ∈ W.vertexFinset \ W'.vertexFinset`. -/
theorem not_isWallEdge_inside_to_outside (h2 : 2 ≤ h) (he : Even h) (hW : W.IsValid)
    {h' : ℕ} {W' : WallOfHeight h' G} (hsub : W'.IsSubwallOf W)
    {a b : Fin n} (ha : a ∈ W'.insideFinset) (hb : b ∈ W.vertexFinset \ W'.vertexFinset) :
    ¬ W.IsWallEdge a b := by
  intro hab
  have h2' : 2 ≤ h' := W.two_le_of_isSubwallOf hsub
  have he' : Even h' := W.even_of_isSubwallOf hsub
  have hW' : W'.IsValid := W.isValid_of_isSubwallOf hW hsub
  have hsub_gm : (W.toGMSubwallOf h2 he hW hsub).IsSubwallOf (W.toGMWall h2 he hW) :=
    W.toGMSubwallOf_isSubwallOf h2 he hW hsub
  have hprop := hsub_gm.toIsProperSubwallOf
  rcases W.exists_isLink_toGMWall_of_isWallEdge_s9 h2 he hW hab with ⟨e, hlink⟩
  have ha_in : a.1 ∈ (W.toGMSubwallOf h2 he hW hsub).insideVerts := by
    rw [W.toGMSubwallOf_insideVerts_eq h2 he hW hsub h2' he' hW',
      W'.insideVerts_toGMWall_eq h2' he' hW']
    exact ⟨a, ha, rfl⟩
  have hb_in_W' : b.1 ∈ V((W.toGMSubwallOf h2 he hW hsub).graph) :=
    hprop.no_edge_inside_to_outside hlink ha_in
  rw [W.toGMSubwallOf_graph_eq h2 he hW hsub h2' he' hW',
    W'.vertexSet_toGMWall_eq h2' he' hW'] at hb_in_W'
  rcases hb_in_W' with ⟨b', hb', heq⟩
  exact (Finset.mem_sdiff.mp hb).2 (Fin.ext heq ▸ hb')

/-- A subwall `W'` of `W` in `G` is dividing in `G` (GM XIII Section 9, page 99):
`W'.IsSubwallOf W` and there is no `H`-path `P` of `W` in `G` (`W.IsHPath P`) with its start in
`W'.insideFinset` and its end in `W.vertexFinset \ W'.vertexFinset`. -/
def IsDividingSubwall {h' : ℕ} (W : WallOfHeight h G) (W' : WallOfHeight h' G) : Prop :=
  W'.IsSubwallOf W ∧
    ∀ P : List (Fin n), ∀ hne : P ≠ [], W.IsHPath P →
      ¬ (P.head hne ∈ W'.insideFinset ∧ P.getLast hne ∈ W.vertexFinset \ W'.vertexFinset)

/-- A subwall `W'` of `W` in `G` is non-dividing in `G` (GM XIII Section 9, page 99). -/
def IsNonDividingSubwall {h' : ℕ} (W : WallOfHeight h G) (W' : WallOfHeight h' G) : Prop :=
  W'.IsSubwallOf W ∧
    ∃ P : List (Fin n), ∃ hne : P ≠ [], W.IsHPath P ∧
      P.head hne ∈ W'.insideFinset ∧ P.getLast hne ∈ W.vertexFinset \ W'.vertexFinset

theorem not_isDividingSubwall_iff_isNonDividingSubwall {h' : ℕ} {W' : WallOfHeight h' G}
    (hsub : W'.IsSubwallOf W) :
    ¬ W.IsDividingSubwall W' ↔ W.IsNonDividingSubwall W' := by
  unfold IsDividingSubwall IsNonDividingSubwall
  push Not
  exact ⟨fun h => ⟨hsub, h hsub⟩, fun ⟨_, P, hne, hP, ha, hb⟩ _ => ⟨P, hne, hP, ha, hb⟩⟩

private lemma reachable_getLast_of_isSimpleWalkList {Y : Finset (Fin n)} :
    ∀ {L : List (Fin n)} (hne : L ≠ []),
      IsSimpleWalkList G L →
      (∀ v ∈ L, v ∉ Y) →
      (restrictGraph G.toSimpleGraph (Finset.univ \ Y)).Reachable (L.head hne) (L.getLast hne)
  | [], hne, _, _ => False.elim (hne rfl)
  | [_], _, _, _ => SimpleGraph.Reachable.refl _
  | x :: y :: rest, _, ⟨hadj, hrest⟩, havoid => by
    have hx : x ∈ Finset.univ \ Y :=
      Finset.mem_sdiff.mpr ⟨Finset.mem_univ x, havoid x List.mem_cons_self⟩
    have hy : y ∈ Finset.univ \ Y :=
      Finset.mem_sdiff.mpr ⟨Finset.mem_univ y, havoid y (List.mem_cons_of_mem x List.mem_cons_self)⟩
    have hadjR : (restrictGraph G.toSimpleGraph (Finset.univ \ Y)).Adj x y := by
      rw [restrictGraph_adj]
      exact ⟨hx, hy, hadj⟩
    exact hadjR.reachable.trans
      (reachable_getLast_of_isSimpleWalkList (List.cons_ne_nil y rest) hrest
        (fun v hv => havoid v (List.mem_cons_of_mem x hv)))

/-- If `Disjoint W'.compassFinset (W.vertexFinset \ W'.vertexFinset)` and `W'.IsSubwallOf W`, then
`W.IsDividingSubwall W'`. -/
theorem isDividingSubwall_of_disjoint_compassFinset {h' : ℕ} {W' : WallOfHeight h' G}
    (hsub : W'.IsSubwallOf W)
    (hdisj : Disjoint W'.compassFinset (W.vertexFinset \ W'.vertexFinset)) :
    W.IsDividingSubwall W' := by
  refine ⟨hsub, fun P hne hP ⟨ha, hb⟩ => ?_⟩
  rcases hP with ⟨_, h2_len, hnd, hwalk, hhead_W, hlast_W, hmid_not_W, _⟩
  have himp := (not_mem_drop_one_dropLast_iff hne h2_len hnd W.vertexFinset hhead_W hlast_W).mp
    hmid_not_W
  have havoid : ∀ v ∈ P, v ∉ W'.perimeterFinset := by
    intro v hvP hvPerim
    have hvW' : v ∈ W'.vertexFinset := W'.perimeterFinset_subset_vertexFinset hvPerim
    have hvW : v ∈ W.vertexFinset := W.subwall_vertexFinset_subset hsub hvW'
    rcases himp v hvP hvW with rfl | rfl
    · exact (Finset.mem_sdiff.mp ha).2 hvPerim
    · exact (Finset.mem_sdiff.mp hb).2 hvW'
  have hreach :
      (restrictGraph G.toSimpleGraph (Finset.univ \ W'.perimeterFinset)).Reachable
        (P.head hne) (P.getLast hne) :=
    reachable_getLast_of_isSimpleWalkList hne hwalk havoid
  have hlast_comp : P.getLast hne ∈ W'.compassFinset :=
    W'.mem_compassFinset_of_reachable ha hreach
  exact Finset.disjoint_left.mp hdisj hlast_comp hb

/-- If `W.IsDividingSubwall W'`, then for any `W'_gm : GM13.Wall ℕ (ℕ × ℕ × ℕ)` with
`W'_gm.IsSubwallOf (W.toGMWall h2 he hW)`, `W'_gm.insideVerts = (W'.toGMWall h2' he' hW').insideVerts`,
and `W'_gm.graph = (W'.toGMWall h2' he' hW').graph`, `GM13.IsDividingSubwall` holds for `W'_gm`. -/
theorem isDividingSubwall_gm_of_isDividingSubwall (h2 : 2 ≤ h) (he : Even h) (hW : W.IsValid)
    {h' : ℕ} (h2' : 2 ≤ h') (he' : Even h')
    {W' : WallOfHeight h' G} (hW' : W'.IsValid)
    (hdiv : W.IsDividingSubwall W')
    {W'_gm : GM13.Wall ℕ (ℕ × ℕ × ℕ)}
    (hsub_gm : W'_gm.IsSubwallOf (W.toGMWall h2 he hW))
    (hG_eq : W'_gm.graph = (W'.toGMWall h2' he' hW').graph)
    (hI_eq : W'_gm.insideVerts = (W'.toGMWall h2' he' hW').insideVerts) :
    GM13.IsDividingSubwall G.toGMDigraph.toGraph (W.toGMWall h2 he hW) W'_gm := by
  refine ⟨hsub_gm, fun P_gm a b hP_gm ⟨ha_in, hb_out⟩ => ?_⟩
  rcases hP_gm with ⟨_, ⟨hP_le, W₀, hW₀_simple, hVP_eq, _⟩, hab_ne, ha_W, hb_W, hVP_inter, _⟩
  obtain ⟨w, hw_supp, _⟩ := GM09.exists_walk_up_of_le hP_le W₀
  have hw_simple : w.IsSimple := by
    unfold Surface.GraphWalk.IsSimple
    rw [hw_supp]
    exact hW₀_simple
  rw [hI_eq, W'.insideVerts_toGMWall_eq h2' he' hW'] at ha_in
  rcases ha_in with ⟨a_fin, ha_fin, rfl⟩
  have hb_W_fin := hb_W
  rw [W.vertexSet_toGMWall_eq h2 he hW] at hb_W_fin
  rcases hb_W_fin with ⟨b_fin, hb_fin, rfl⟩
  have hb_not_W' : b_fin ∉ W'.vertexFinset := by
    intro hb'
    apply hb_out.2
    rw [hG_eq, W'.vertexSet_toGMWall_eq h2' he' hW']
    exact ⟨b_fin, hb', rfl⟩
  have hb_sdiff : b_fin ∈ W.vertexFinset \ W'.vertexFinset :=
    Finset.mem_sdiff.mpr ⟨hb_fin, hb_not_W'⟩
  let P := graphWalkToFinList w a_fin.2
  have hne : P ≠ [] := graphWalkToFinList_ne_nil w a_fin.2
  have hhead : P.head hne = a_fin := head_graphWalkToFinList w a_fin.2
  have hlast : P.getLast hne = b_fin := getLast_graphWalkToFinList w a_fin.2 b_fin.2
  have hnd : P.Nodup := nodup_graphWalkToFinList_of_isSimple a_fin.2 hw_simple
  have hwalk : IsSimpleWalkList G P := isSimpleWalkList_graphWalkToFinList w a_fin.2 hw_simple
  have h2_len : 2 ≤ P.length := by
    apply two_le_length_of_ne_head_getLast hne
    rw [hhead, hlast]
    exact fun heq => hab_ne (congrArg Fin.val heq)
  have hhead_W : P.head hne ∈ W.vertexFinset := by
    rw [hhead]
    exact W.subwall_vertexFinset_subset hdiv.1 (Finset.sdiff_subset ha_fin)
  have hlast_W : P.getLast hne ∈ W.vertexFinset := by
    rw [hlast]
    exact hb_fin
  have hmid_not_W : ∀ v ∈ (P.drop 1).dropLast, v ∉ W.vertexFinset := by
    rw [not_mem_drop_one_dropLast_iff hne h2_len hnd W.vertexFinset hhead_W hlast_W]
    intro v hvP hvW
    have hv_supp : v.1 ∈ W₀.support := by
      rw [← hw_supp, ← mem_graphWalkToFinList_iff w a_fin.2]
      exact hvP
    have hv_VP : v.1 ∈ V(P_gm) := by rw [hVP_eq]; exact hv_supp
    have hv_VW : v.1 ∈ V((W.toGMWall h2 he hW).graph) := by
      rw [W.vertexSet_toGMWall_eq h2 he hW]
      exact ⟨v, hvW, rfl⟩
    have hv_ab : v.1 ∈ ({a_fin.1, b_fin.1} : Set ℕ) := by
      rw [← hVP_inter]
      exact ⟨hv_VP, hv_VW⟩
    rcases hv_ab with heq | heq
    · left; rw [hhead]; exact Fin.ext heq
    · right; rw [hlast]; exact Fin.ext heq
  have hno_edge : P.length = 2 → ¬ W.IsWallEdge (P.head hne) (P.getLast hne) := by
    intro _
    rw [hhead, hlast]
    exact W.not_isWallEdge_inside_to_outside h2 he hW hdiv.1 ha_fin hb_sdiff
  have hP_isH : W.IsHPath P :=
    ⟨hne, h2_len, hnd, hwalk, hhead_W, hlast_W, hmid_not_W, hno_edge⟩
  exact hdiv.2 P hne hP_isH ⟨hhead.symm ▸ ha_fin, hlast.symm ▸ hb_sdiff⟩

/-- If `GM13.IsDividingSubwall G.toGMDigraph.toGraph (W.toGMWall h2 he hW) W'_gm` holds where
`W'_gm` has the same graph and compass as `W'.toGMWall h2' he' hW'`, then
`Disjoint W'.compassFinset (W.vertexFinset \ W'.vertexFinset)`. -/
theorem disjoint_compassFinset_of_isDividingSubwall_gm
    (h2 : 2 ≤ h) (he : Even h) (hW : W.IsValid)
    {h' : ℕ} (h2' : 2 ≤ h') (he' : Even h')
    {W' : WallOfHeight h' G} (hW' : W'.IsValid)
    {W'_gm : GM13.Wall ℕ (ℕ × ℕ × ℕ)}
    (hG_eq : W'_gm.graph = (W'.toGMWall h2' he' hW').graph)
    (hK_eq : GM13.wallCompass G.toGMDigraph.toGraph W'_gm =
      GM13.wallCompass G.toGMDigraph.toGraph (W'.toGMWall h2' he' hW'))
    (hdiv_gm : GM13.IsDividingSubwall G.toGMDigraph.toGraph (W.toGMWall h2 he hW) W'_gm) :
    Disjoint W'.compassFinset (W.vertexFinset \ W'.vertexFinset) := by
  have hprop := hdiv_gm.1.toIsProperSubwallOf
  have hsub_compass :=
    GM13.compass_inter_wall_vertexSet_subset (W.isWallIn_toGMWall h2 he hW) hprop hdiv_gm
  rw [Finset.disjoint_left]
  intro v hv_comp hv_sdiff
  rcases Finset.mem_sdiff.mp hv_sdiff with ⟨hvW, hv_notW'⟩
  have hv_K : v.1 ∈ V(GM13.wallCompass G.toGMDigraph.toGraph W'_gm) := by
    rw [hK_eq]
    exact (W'.mem_wallCompassVerts_toGMWall_iff h2' he' hW' v).mpr hv_comp
  have hv_VW : v.1 ∈ V((W.toGMWall h2 he hW).graph) := by
    rw [W.vertexSet_toGMWall_eq h2 he hW]
    exact ⟨v, hvW, rfl⟩
  have hv_VW' : v.1 ∈ V(W'_gm.graph) := hsub_compass ⟨hv_K, hv_VW⟩
  rw [hG_eq, W'.vertexSet_toGMWall_eq h2' he' hW'] at hv_VW'
  rcases hv_VW' with ⟨v', hv', heq⟩
  exact hv_notW' (Fin.ext heq ▸ hv')

/-- **Exact Agreement of `W.IsDividingSubwall W'` and `GM13.IsDividingSubwall` (via `toGMSubwallOf`):** -/
theorem isDividingSubwall_iff_toGMSubwallOf (h2 : 2 ≤ h) (he : Even h) (hW : W.IsValid)
    {h' : ℕ} {W' : WallOfHeight h' G} (hsub : W'.IsSubwallOf W) :
    W.IsDividingSubwall W' ↔
      GM13.IsDividingSubwall G.toGMDigraph.toGraph
        (W.toGMWall h2 he hW) (W.toGMSubwallOf h2 he hW hsub) := by
  have h2' := W.two_le_of_isSubwallOf hsub
  have he' := W.even_of_isSubwallOf hsub
  have hW' := W.isValid_of_isSubwallOf hW hsub
  exact
    ⟨fun hdiv =>
      W.isDividingSubwall_gm_of_isDividingSubwall h2 he hW h2' he' hW' hdiv
        (W.toGMSubwallOf_isSubwallOf h2 he hW hsub)
        (W.toGMSubwallOf_graph_eq h2 he hW hsub h2' he' hW')
        (W.toGMSubwallOf_insideVerts_eq h2 he hW hsub h2' he' hW'),
     fun hdiv_gm =>
      W.isDividingSubwall_of_disjoint_compassFinset hsub
        (W.disjoint_compassFinset_of_isDividingSubwall_gm h2 he hW h2' he' hW'
          (W.toGMSubwallOf_graph_eq h2 he hW hsub h2' he' hW')
          (W.toGMSubwallOf_wallCompass_eq _ h2 he hW hsub h2' he' hW')
          hdiv_gm)⟩

/-- **Exact Agreement of `W.IsDividingSubwall (W.subwallAt ...)` and `GM13.IsDividingSubwall`:** -/
theorem isDividingSubwall_subwallAt_iff_toGMSubwallAt (h2 : 2 ≤ h) (he : Even h) (hW : W.IsValid)
    (i j h' : ℕ) (h2' : 2 ≤ h') (he' : Even h') (hle : h' ≤ h)
    (hi_even : Even i) (hj_even : Even j)
    (hi_le : i ≤ 2 * h - 2 * h') (hj_le : j ≤ h - h') :
    W.IsDividingSubwall (W.subwallAt i j h' (by omega) hle hi_even hj_even hi_le hj_le) ↔
      GM13.IsDividingSubwall G.toGMDigraph.toGraph (W.toGMWall h2 he hW)
        (W.toGMSubwallAt h2 he hW i j h' h2' he' hle hi_even hj_even hi_le hj_le) := by
  let W' := W.subwallAt i j h' (by omega) hle hi_even hj_even hi_le hj_le
  have hW' : W'.IsValid := W.isValid_subwallAt hW i j h' (by omega) hle hi_even hj_even hi_le hj_le
  have hsub : W'.IsSubwallOf W := ⟨h2', he', hle, i, j, hi_even, hj_even, hi_le, hj_le, rfl⟩
  exact
    ⟨fun hdiv =>
      W.isDividingSubwall_gm_of_isDividingSubwall h2 he hW h2' he' hW' hdiv
        (W.toGMSubwallAt_isSubwallOf h2 he hW i j h' h2' he' hle hi_even hj_even hi_le hj_le)
        (W.subwallAt_toGMWall_graph_eq h2 he hW i j h' h2' he' hle hi_even hj_even hi_le hj_le).symm
        (W.subwallAt_toGMWall_insideVerts_eq h2 he hW i j h' h2' he' hle hi_even hj_even hi_le hj_le).symm,
     fun hdiv_gm =>
      W.isDividingSubwall_of_disjoint_compassFinset hsub
        (W.disjoint_compassFinset_of_isDividingSubwall_gm h2 he hW h2' he' hW'
          (W.subwallAt_toGMWall_graph_eq h2 he hW i j h' h2' he' hle hi_even hj_even hi_le hj_le).symm
          (W.subwallAt_toGMWall_wallCompass_eq _ h2 he hW i j h' h2' he' hle hi_even hj_even hi_le hj_le).symm
          hdiv_gm)⟩

/-- **Exact Agreement of `W.IsDividingSubwall W'` and Compass Disjointness (GM XIII (9.5)):**
For a subwall `W'` of `W` (`hsub : W'.IsSubwallOf W`), `W.IsDividingSubwall W'` holds if and only
if `Disjoint W'.compassFinset (W.vertexFinset \ W'.vertexFinset)`. -/
theorem isDividingSubwall_iff_disjoint_compassFinset (h2 : 2 ≤ h) (he : Even h) (hW : W.IsValid)
    {h' : ℕ} {W' : WallOfHeight h' G} (hsub : W'.IsSubwallOf W) :
    W.IsDividingSubwall W' ↔ Disjoint W'.compassFinset (W.vertexFinset \ W'.vertexFinset) := by
  have h2' := W.two_le_of_isSubwallOf hsub
  have he' := W.even_of_isSubwallOf hsub
  have hW' := W.isValid_of_isSubwallOf hW hsub
  exact
    ⟨fun hdiv =>
      W.disjoint_compassFinset_of_isDividingSubwall_gm h2 he hW h2' he' hW'
        (W.toGMSubwallOf_graph_eq h2 he hW hsub h2' he' hW')
        (W.toGMSubwallOf_wallCompass_eq _ h2 he hW hsub h2' he' hW')
        ((W.isDividingSubwall_iff_toGMSubwallOf h2 he hW hsub).mp hdiv),
     W.isDividingSubwall_of_disjoint_compassFinset hsub⟩

/-- **Exact Agreement of `W.IsNonDividingSubwall W'` and `GM13.IsNonDividingSubwall`:** -/
theorem isNonDividingSubwall_iff_toGMSubwallOf (h2 : 2 ≤ h) (he : Even h) (hW : W.IsValid)
    {h' : ℕ} {W' : WallOfHeight h' G} (hsub : W'.IsSubwallOf W) :
    W.IsNonDividingSubwall W' ↔
      GM13.IsNonDividingSubwall G.toGMDigraph.toGraph
        (W.toGMWall h2 he hW) (W.toGMSubwallOf h2 he hW hsub) := by
  have hsub_gm := W.toGMSubwallOf_isSubwallOf h2 he hW hsub
  rw [← W.not_isDividingSubwall_iff_isNonDividingSubwall hsub,
    ← GM13.not_isDividingSubwall_iff_isNonDividingSubwall hsub_gm]
  exact not_congr (W.isDividingSubwall_iff_toGMSubwallOf h2 he hW hsub)

/-- **Exact Agreement of `W.IsNonDividingSubwall (W.subwallAt ...)` and `GM13.IsNonDividingSubwall`:** -/
theorem isNonDividingSubwall_subwallAt_iff_toGMSubwallAt (h2 : 2 ≤ h) (he : Even h) (hW : W.IsValid)
    (i j h' : ℕ) (h2' : 2 ≤ h') (he' : Even h') (hle : h' ≤ h)
    (hi_even : Even i) (hj_even : Even j)
    (hi_le : i ≤ 2 * h - 2 * h') (hj_le : j ≤ h - h') :
    W.IsNonDividingSubwall (W.subwallAt i j h' (by omega) hle hi_even hj_even hi_le hj_le) ↔
      GM13.IsNonDividingSubwall G.toGMDigraph.toGraph (W.toGMWall h2 he hW)
        (W.toGMSubwallAt h2 he hW i j h' h2' he' hle hi_even hj_even hi_le hj_le) := by
  have hsub : (W.subwallAt i j h' (by omega) hle hi_even hj_even hi_le hj_le).IsSubwallOf W :=
    ⟨h2', he', hle, i, j, hi_even, hj_even, hi_le, hj_le, rfl⟩
  have hsub_gm := W.toGMSubwallAt_isSubwallOf h2 he hW i j h' h2' he' hle hi_even hj_even hi_le hj_le
  rw [← W.not_isDividingSubwall_iff_isNonDividingSubwall hsub,
    ← GM13.not_isDividingSubwall_iff_isNonDividingSubwall hsub_gm]
  exact not_congr (W.isDividingSubwall_subwallAt_iff_toGMSubwallAt h2 he hW
    i j h' h2' he' hle hi_even hj_even hi_le hj_le)

/-- Two vertex lists `P₁, P₂ : List (Fin n)` form a cross over `W : WallOfHeight h G` (`2 ≤ h`)
in `G` (GM XIII Section 9, page 98): `P₁` and `P₂` are mutually vertex-disjoint simple paths in
`G.toSimpleGraph` with ends `(W.cornerVert h2 0, W.cornerVert h2 2)` and
`(W.cornerVert h2 1, W.cornerVert h2 3)`, respectively. -/
structure IsCrossOverWall (W : WallOfHeight h G) (h2 : 2 ≤ h) (P₁ P₂ : List (Fin n)) : Prop where
  ne_nil₁ : P₁ ≠ []
  ne_nil₂ : P₂ ≠ []
  nodup₁ : P₁.Nodup
  nodup₂ : P₂.Nodup
  isWalk₁ : IsSimpleWalkList G P₁
  isWalk₂ : IsSimpleWalkList G P₂
  head₁ : P₁.head ne_nil₁ = W.cornerVert h2 0
  getLast₁ : P₁.getLast ne_nil₁ = W.cornerVert h2 2
  head₂ : P₂.head ne_nil₂ = W.cornerVert h2 1
  getLast₂ : P₂.getLast ne_nil₂ = W.cornerVert h2 3
  disjoint : List.Disjoint P₁ P₂

/-- Lift a `Surface.GraphWalk G₀ a b` whose support lies in `S : Set α` to `G₀.induce S`. -/
def liftGraphWalkToInduce {α β : Type*} {G₀ : Graph α β} (S : Set α) :
    ∀ {a b : α} (w : Surface.GraphWalk G₀ a b),
      (∀ x ∈ w.support, x ∈ S) →
      Surface.GraphWalk (G₀.induce S) a b
  | a, _, .nil _, hmem => .nil (hmem a (by simp [Surface.GraphWalk.support]))
  | a, _, .cons (e := e) (v := c) hlink rest, hmem =>
    have ha : a ∈ S := hmem a (by simp [Surface.GraphWalk.support])
    have hc : c ∈ S := hmem c (List.mem_cons_of_mem a rest.start_mem_support)
    .cons ((Graph.induce_isLink G₀ S e a c).mpr ⟨hlink, ha, hc⟩)
      (liftGraphWalkToInduce S rest (fun x hx => hmem x (List.mem_cons_of_mem a hx)))

@[simp]
theorem support_liftGraphWalkToInduce {α β : Type*} {G₀ : Graph α β} (S : Set α) :
    ∀ {a b : α} (w : Surface.GraphWalk G₀ a b) (hmem : ∀ x ∈ w.support, x ∈ S),
      (liftGraphWalkToInduce S w hmem).support = w.support
  | _, _, .nil _, _ => rfl
  | _, _, .cons _ rest, hmem => by
    change _ :: (liftGraphWalkToInduce S rest _).support = _ :: rest.support
    rw [support_liftGraphWalkToInduce S rest]

theorem isCrossOverWall_toGMWall_of_isCrossOverWall (h2 : 2 ≤ h) (he : Even h) (hW : W.IsValid)
    {P₁ P₂ : List (Fin n)} (hcr : W.IsCrossOverWall h2 P₁ P₂) :
    GM13.IsCrossOverWall G.toGMDigraph.toGraph (W.toGMWall h2 he hW)
      (GM09.walkSubgraph (toGMGraphWalk hcr.ne_nil₁ hcr.isWalk₁))
      (GM09.walkSubgraph (toGMGraphWalk hcr.ne_nil₂ hcr.isWalk₂)) := by
  let w₁ := toGMGraphWalk hcr.ne_nil₁ hcr.isWalk₁
  let w₂ := toGMGraphWalk hcr.ne_nil₂ hcr.isWalk₂
  let Sub₁ : Graph ℕ (ℕ × ℕ × ℕ) := GM09.walkSubgraph w₁
  let Sub₂ : Graph ℕ (ℕ × ℕ × ℕ) := GM09.walkSubgraph w₂
  have hw₁_s : w₁.IsSimple := isSimple_toGMGraphWalk hcr.ne_nil₁ hcr.isWalk₁ hcr.nodup₁
  have hw₂_s : w₂.IsSimple := isSimple_toGMGraphWalk hcr.ne_nil₂ hcr.isWalk₂ hcr.nodup₂
  have hP₁ : GM09.IsGraphPathWithEnds G.toGMDigraph.toGraph Sub₁
      ((W.toGMWall h2 he hW).corner 0) ((W.toGMWall h2 he hW).corner 2) := by
    have hp : GM09.IsGraphPathWithEnds G.toGMDigraph.toGraph Sub₁
        (P₁.head hcr.ne_nil₁).1 (P₁.getLast hcr.ne_nil₁).1 :=
      GM09.isGraphPathWithEnds_walkSubgraph hw₁_s
    rwa [hcr.head₁, hcr.getLast₁,
      ← W.toGMWall_corner_eq_cornerVert h2 he hW 0,
      ← W.toGMWall_corner_eq_cornerVert h2 he hW 2] at hp
  have hP₂ : GM09.IsGraphPathWithEnds G.toGMDigraph.toGraph Sub₂
      ((W.toGMWall h2 he hW).corner 1) ((W.toGMWall h2 he hW).corner 3) := by
    have hp : GM09.IsGraphPathWithEnds G.toGMDigraph.toGraph Sub₂
        (P₂.head hcr.ne_nil₂).1 (P₂.getLast hcr.ne_nil₂).1 :=
      GM09.isGraphPathWithEnds_walkSubgraph hw₂_s
    rwa [hcr.head₂, hcr.getLast₂,
      ← W.toGMWall_corner_eq_cornerVert h2 he hW 1,
      ← W.toGMWall_corner_eq_cornerVert h2 he hW 3] at hp
  refine ⟨?_, hP₁, hP₂⟩
  rw [GM09.vertexSet_walkSubgraph, GM09.vertexSet_walkSubgraph,
    support_toGMGraphWalk, support_toGMGraphWalk, Set.disjoint_left]
  intro x hx₁ hx₂
  simp only [Set.mem_ofPred_eq, List.mem_map] at hx₁ hx₂
  rcases hx₁ with ⟨u, hu, rfl⟩
  rcases hx₂ with ⟨v, hv, heq⟩
  exact hcr.disjoint hu (Fin.ext heq ▸ hv)

theorem isCrossOverWall_toGMSubwallOf_of_isCrossOverWall (h2 : 2 ≤ h) (he : Even h) (hW : W.IsValid)
    {h' : ℕ} {W' : WallOfHeight h' G} (hsub : W'.IsSubwallOf W)
    {P₁ P₂ : List (Fin n)} (hcr : W'.IsCrossOverWall (W.two_le_of_isSubwallOf hsub) P₁ P₂) :
    GM13.IsCrossOverWall G.toGMDigraph.toGraph (W.toGMSubwallOf h2 he hW hsub)
      (GM09.walkSubgraph (toGMGraphWalk hcr.ne_nil₁ hcr.isWalk₁))
      (GM09.walkSubgraph (toGMGraphWalk hcr.ne_nil₂ hcr.isWalk₂)) := by
  have h2' := W.two_le_of_isSubwallOf hsub
  have he' := W.even_of_isSubwallOf hsub
  have hW' := W.isValid_of_isSubwallOf hW hsub
  have hcr_gm := W'.isCrossOverWall_toGMWall_of_isCrossOverWall h2' he' hW' hcr
  let Sub₁ : Graph ℕ (ℕ × ℕ × ℕ) := GM09.walkSubgraph (toGMGraphWalk hcr.ne_nil₁ hcr.isWalk₁)
  let Sub₂ : Graph ℕ (ℕ × ℕ × ℕ) := GM09.walkSubgraph (toGMGraphWalk hcr.ne_nil₂ hcr.isWalk₂)
  rcases hcr_gm with ⟨hdisj, hP₁, hP₂⟩
  change GM09.IsGraphPathWithEnds G.toGMDigraph.toGraph Sub₁ _ _ at hP₁
  change GM09.IsGraphPathWithEnds G.toGMDigraph.toGraph Sub₂ _ _ at hP₂
  rw [← W.toGMSubwallOf_corner_eq h2 he hW hsub h2' he' hW' 0,
    ← W.toGMSubwallOf_corner_eq h2 he hW hsub h2' he' hW' 2] at hP₁
  rw [← W.toGMSubwallOf_corner_eq h2 he hW hsub h2' he' hW' 1,
    ← W.toGMSubwallOf_corner_eq h2 he hW hsub h2' he' hW' 3] at hP₂
  exact ⟨hdisj, hP₁, hP₂⟩

/-- **Exact Agreement of Crosses in `W.compassFinset` and `GM13.IsCrossOverWall` in `wallCompass`:** -/
theorem exists_isCrossOverWall_compassFinset_iff_toGMWall
    (h2 : 2 ≤ h) (he : Even h) (hW : W.IsValid) :
    (∃ P₁ P₂ : List (Fin n),
      W.IsCrossOverWall h2 P₁ P₂ ∧
      (∀ v ∈ P₁, v ∈ W.compassFinset) ∧
      (∀ v ∈ P₂, v ∈ W.compassFinset)) ↔
    (∃ P Q : Graph ℕ (ℕ × ℕ × ℕ),
      GM13.IsCrossOverWall
        (GM13.wallCompass G.toGMDigraph.toGraph (W.toGMWall h2 he hW))
        (W.toGMWall h2 he hW) P Q) := by
  constructor
  · rintro ⟨P₁, P₂, hcr, hmem₁, hmem₂⟩
    let S_comp : Set ℕ := GM13.wallCompassVerts G.toGMDigraph.toGraph (W.toGMWall h2 he hW)
    let w₁ := toGMGraphWalk hcr.ne_nil₁ hcr.isWalk₁
    let w₂ := toGMGraphWalk hcr.ne_nil₂ hcr.isWalk₂
    have hw₁_comp : ∀ x ∈ w₁.support, x ∈ S_comp := by
      intro x hx
      rw [support_toGMGraphWalk] at hx
      rcases List.mem_map.mp hx with ⟨v, hv, rfl⟩
      exact (W.mem_wallCompassVerts_toGMWall_iff h2 he hW v).mpr (hmem₁ v hv)
    have hw₂_comp : ∀ x ∈ w₂.support, x ∈ S_comp := by
      intro x hx
      rw [support_toGMGraphWalk] at hx
      rcases List.mem_map.mp hx with ⟨v, hv, rfl⟩
      exact (W.mem_wallCompassVerts_toGMWall_iff h2 he hW v).mpr (hmem₂ v hv)
    let w₁' := liftGraphWalkToInduce S_comp w₁ hw₁_comp
    let w₂' := liftGraphWalkToInduce S_comp w₂ hw₂_comp
    let Sub₁' : Graph ℕ (ℕ × ℕ × ℕ) := GM09.walkSubgraph w₁'
    let Sub₂' : Graph ℕ (ℕ × ℕ × ℕ) := GM09.walkSubgraph w₂'
    have hw₁'_s : w₁'.IsSimple := by
      unfold Surface.GraphWalk.IsSimple
      rw [support_liftGraphWalkToInduce]
      exact isSimple_toGMGraphWalk hcr.ne_nil₁ hcr.isWalk₁ hcr.nodup₁
    have hw₂'_s : w₂'.IsSimple := by
      unfold Surface.GraphWalk.IsSimple
      rw [support_liftGraphWalkToInduce]
      exact isSimple_toGMGraphWalk hcr.ne_nil₂ hcr.isWalk₂ hcr.nodup₂
    refine ⟨Sub₁', Sub₂', ?_, ?_, ?_⟩
    · change Disjoint V(GM09.walkSubgraph w₁') V(GM09.walkSubgraph w₂')
      rw [GM09.vertexSet_walkSubgraph, GM09.vertexSet_walkSubgraph,
        support_liftGraphWalkToInduce, support_liftGraphWalkToInduce,
        support_toGMGraphWalk, support_toGMGraphWalk, Set.disjoint_left]
      intro x hx₁ hx₂
      simp only [Set.mem_ofPred_eq, List.mem_map] at hx₁ hx₂
      rcases hx₁ with ⟨u, hu, rfl⟩
      rcases hx₂ with ⟨v, hv, heq⟩
      exact hcr.disjoint hu (Fin.ext heq ▸ hv)
    · have hp : GM09.IsGraphPathWithEnds
          (GM13.wallCompass G.toGMDigraph.toGraph (W.toGMWall h2 he hW)) Sub₁'
          (P₁.head hcr.ne_nil₁).1 (P₁.getLast hcr.ne_nil₁).1 :=
        GM09.isGraphPathWithEnds_walkSubgraph hw₁'_s
      rwa [hcr.head₁, hcr.getLast₁,
        ← W.toGMWall_corner_eq_cornerVert h2 he hW 0,
        ← W.toGMWall_corner_eq_cornerVert h2 he hW 2] at hp
    · have hp : GM09.IsGraphPathWithEnds
          (GM13.wallCompass G.toGMDigraph.toGraph (W.toGMWall h2 he hW)) Sub₂'
          (P₂.head hcr.ne_nil₂).1 (P₂.getLast hcr.ne_nil₂).1 :=
        GM09.isGraphPathWithEnds_walkSubgraph hw₂'_s
      rwa [hcr.head₂, hcr.getLast₂,
        ← W.toGMWall_corner_eq_cornerVert h2 he hW 1,
        ← W.toGMWall_corner_eq_cornerVert h2 he hW 3] at hp
  · rintro ⟨P, Q, hdisj, ⟨hP_le, W₁, hW₁_s, hVP, _⟩, ⟨hQ_le, W₂, hW₂_s, hVQ, _⟩⟩
    have hK_le : GM13.wallCompass G.toGMDigraph.toGraph (W.toGMWall h2 he hW) ≤
        G.toGMDigraph.toGraph :=
      GM13.wallCompass_le (W.isWallIn_toGMWall h2 he hW)
    obtain ⟨w₁, hs₁, _⟩ := GM09.exists_walk_up_of_le (hP_le.trans hK_le) W₁
    obtain ⟨w₂, hs₂, _⟩ := GM09.exists_walk_up_of_le (hQ_le.trans hK_le) W₂
    have hw₁_s : w₁.IsSimple := by unfold Surface.GraphWalk.IsSimple; rw [hs₁]; exact hW₁_s
    have hw₂_s : w₂.IsSimple := by unfold Surface.GraphWalk.IsSimple; rw [hs₂]; exact hW₂_s
    have hc0 : (W.toGMWall h2 he hW).corner 0 < n := by
      rw [W.toGMWall_corner_eq_cornerVert h2 he hW 0]; exact (W.cornerVert h2 0).2
    have hc2 : (W.toGMWall h2 he hW).corner 2 < n := by
      rw [W.toGMWall_corner_eq_cornerVert h2 he hW 2]; exact (W.cornerVert h2 2).2
    have hc1 : (W.toGMWall h2 he hW).corner 1 < n := by
      rw [W.toGMWall_corner_eq_cornerVert h2 he hW 1]; exact (W.cornerVert h2 1).2
    have hc3 : (W.toGMWall h2 he hW).corner 3 < n := by
      rw [W.toGMWall_corner_eq_cornerVert h2 he hW 3]; exact (W.cornerVert h2 3).2
    let P₁ := graphWalkToFinList w₁ hc0
    let P₂ := graphWalkToFinList w₂ hc1
    refine ⟨P₁, P₂,
      { ne_nil₁ := graphWalkToFinList_ne_nil w₁ hc0
        ne_nil₂ := graphWalkToFinList_ne_nil w₂ hc1
        nodup₁ := nodup_graphWalkToFinList_of_isSimple hc0 hw₁_s
        nodup₂ := nodup_graphWalkToFinList_of_isSimple hc1 hw₂_s
        isWalk₁ := isSimpleWalkList_graphWalkToFinList w₁ hc0 hw₁_s
        isWalk₂ := isSimpleWalkList_graphWalkToFinList w₂ hc1 hw₂_s
        head₁ := by
          rw [head_graphWalkToFinList]
          exact Fin.ext (W.toGMWall_corner_eq_cornerVert h2 he hW 0)
        getLast₁ := by
          rw [getLast_graphWalkToFinList w₁ hc0 hc2]
          exact Fin.ext (W.toGMWall_corner_eq_cornerVert h2 he hW 2)
        head₂ := by
          rw [head_graphWalkToFinList]
          exact Fin.ext (W.toGMWall_corner_eq_cornerVert h2 he hW 1)
        getLast₂ := by
          rw [getLast_graphWalkToFinList w₂ hc1 hc3]
          exact Fin.ext (W.toGMWall_corner_eq_cornerVert h2 he hW 3)
        disjoint := by
          intro v hv₁ hv₂
          rw [mem_graphWalkToFinList_iff, hs₁] at hv₁
          rw [mem_graphWalkToFinList_iff, hs₂] at hv₂
          have hvP : v.1 ∈ V(P) := by rw [hVP]; exact hv₁
          have hvQ : v.1 ∈ V(Q) := by rw [hVQ]; exact hv₂
          exact Set.disjoint_left.mp hdisj hvP hvQ }, ?_, ?_⟩
    · intro v hv
      rw [mem_graphWalkToFinList_iff, hs₁] at hv
      have hvP : v.1 ∈ V(P) := by rw [hVP]; exact hv
      have hvK : v.1 ∈ GM13.wallCompassVerts G.toGMDigraph.toGraph (W.toGMWall h2 he hW) :=
        hP_le.vertexSet_mono hvP
      exact (W.mem_wallCompassVerts_toGMWall_iff h2 he hW v).mp hvK
    · intro v hv
      rw [mem_graphWalkToFinList_iff, hs₂] at hv
      have hvQ : v.1 ∈ V(Q) := by rw [hVQ]; exact hv
      have hvK : v.1 ∈ GM13.wallCompassVerts G.toGMDigraph.toGraph (W.toGMWall h2 he hW) :=
        hQ_le.vertexSet_mono hvQ
      exact (W.mem_wallCompassVerts_toGMWall_iff h2 he hW v).mp hvK

/-- A wall `W : WallOfHeight h G` (`2 ≤ h`) is flat in `G` (GM XIII Section 9, page 103):
`W.IsValid` and there is no cross `(P₁, P₂)` over `W` in `G` whose vertices lie in
`W.compassFinset`. -/
def IsFlatWall (W : WallOfHeight h G) (h2 : 2 ≤ h) : Prop :=
  W.IsValid ∧
    ¬ ∃ P₁ P₂ : List (Fin n),
      W.IsCrossOverWall h2 P₁ P₂ ∧
      (∀ v ∈ P₁, v ∈ W.compassFinset) ∧
      (∀ v ∈ P₂, v ∈ W.compassFinset)

/-- **Exact Agreement of `W.IsFlatWall h2` and `GM13.IsFlatWallIn`:** -/
theorem isFlatWall_iff_toGMWall (h2 : 2 ≤ h) (he : Even h) (hW : W.IsValid) :
    W.IsFlatWall h2 ↔
      GM13.IsFlatWallIn G.toGMDigraph.toGraph (W.toGMWall h2 he hW) := by
  unfold IsFlatWall GM13.IsFlatWallIn
  have hle : (W.toGMWall h2 he hW).graph ≤ G.toGMDigraph.toGraph := W.isWallIn_toGMWall h2 he hW
  rw [and_iff_right hW, and_iff_right hle]
  exact not_congr (W.exists_isCrossOverWall_compassFinset_iff_toGMWall h2 he hW)

/-- A center `c : Fin n` and family of rays `rays : Fin l → List (Fin n)` form an `(l, m)`-star
over `W : WallOfHeight h G` in `G` (GM XIII Section 7, pages 90–91), matching the star conditions
of `Alg77Input` (`Specs13.lean`). -/
structure IsLMStar (W : WallOfHeight h G) (l m : ℕ) (c : Fin n)
    (rays : Fin l → List (Fin n)) : Prop where
  three_le_l : 3 ≤ l
  rays_valid : ∀ i : Fin l, W.IsStarRay c (rays i)
  rays_meet : ∀ i j : Fin l, i ≠ j → ∀ v : Fin n, v ∈ rays i → v ∈ rays j → v = c
  ends_dist : ∀ i j : Fin l, i ≠ j → ∀ u v : Fin n,
    (rays i).getLast? = some u → (rays j).getLast? = some v → m ≤ W.brickDist u v

/-- An `(l, m)`-star over `W` with center `c` is external if `c ∉ W.vertexFinset`
(GM XIII Section 7, page 91). -/
def IsExternalLMStar (W : WallOfHeight h G) (l m : ℕ) (c : Fin n)
    (rays : Fin l → List (Fin n)) : Prop :=
  W.IsLMStar l m c rays ∧ c ∉ W.vertexFinset

/-- Any `(l, m)`-star over `W.castGraph (wallUnionMultiDigraph G X W)` in `(G \ X) ∪ H` has its
center outside `X` (`c ∉ X`) and is also a valid `(l, m)`-star over `W` in `G` (GM XIII Section 9,
page 102, Step (2) of (9.3)). -/
theorem IsLMStar.of_wallUnionMultiDigraph (X : Finset (Fin n))
    {l m : ℕ} {c : Fin n} {rays : Fin l → List (Fin n)}
    (hstar : (W.castGraph (wallUnionMultiDigraph G X W)).IsLMStar l m c rays) :
    c ∉ X ∧ W.IsLMStar l m c rays := by
  have hl : 3 ≤ l := hstar.three_le_l
  let i₀ : Fin l := ⟨0, by omega⟩
  rcases hstar.rays_valid i₀ with ⟨hne₀, hhead₀, h2₀, _, hwalk₀, _, _, hnot_we₀⟩
  have hc_not_X : c ∉ X := by
    rcases h_eq : rays i₀ with _ | ⟨x, _ | ⟨y, ys⟩⟩
    · exact False.elim (hne₀ h_eq)
    · rw [h_eq] at h2₀; simp at h2₀
    · have hx : x = c := by simpa [h_eq] using hhead₀
      subst hx
      rw [h_eq] at hwalk₀ hnot_we₀
      have hadj_union : (wallUnionMultiDigraph G X W).toSimpleGraph.Adj x y := hwalk₀.1
      have hnot_xy : ¬ W.IsWallEdge x y := by
        simpa using hnot_we₀ x y (by simp)
      rw [wallUnionMultiDigraph_adj] at hadj_union
      rcases hadj_union.2 with ⟨hx_notX, _⟩ | hwe
      · exact hx_notX
      · exact False.elim (hnot_xy hwe)
  refine ⟨hc_not_X, {
    three_le_l := hl
    rays_valid := fun i => by
      rcases hstar.rays_valid i with ⟨hne, hhead, h2, hnd, hwalk, hlast, hmid, hnot_we⟩
      rw [castGraph_vertexFinset] at hlast hmid
      refine ⟨hne, hhead, h2, hnd, ?_, hlast, hmid, fun u v huv => ?_⟩
      · exact isSimpleWalkList_of_congr
          (fun u v _ hadj => wallUnionMultiDigraph_toSimpleGraph_le G X W hadj) hwalk
      · simpa using hnot_we u v huv
    rays_meet := hstar.rays_meet
    ends_dist := fun i j hij u v hu hv => by
      simpa [castGraph_brickDist] using hstar.ends_dist i j hij u v hu hv
  }⟩

end WallOfHeight

/-! ### Section 2f: `UnderlyingGraphModel` (`Specs13`) ↔ `IsCliqueModel` (`Specs105`) Bridge -/

theorem adj_toSimpleGraph_of_digraphSubgraph_adj {n : ℕ} (G : MultiDigraph n)
    (S : DigraphSubgraph G.toComputeDigraph) {u v : Fin n}
    (hadj : S.underlyingSimpleGraph.Adj u v) :
    G.toSimpleGraph.Adj u v := by
  rcases hadj with ⟨hne, e, _, hdir⟩
  exact (G.toSimpleGraph_adj_iff_toComputeDigraph u v).mpr ⟨hne, e, hdir⟩

private lemma reachable_induce_of_digraphSubgraph_walk {n : ℕ} (G : MultiDigraph n)
    (S : DigraphSubgraph G.toComputeDigraph) :
    ∀ {u v : Fin n} (_w : S.underlyingSimpleGraph.Walk u v)
      (hu : u ∈ S.verts) (hv : v ∈ S.verts),
      (G.toSimpleGraph.induce (S.verts : Set (Fin n))).Reachable ⟨u, hu⟩ ⟨v, hv⟩
  | _, _, .nil, _, _ => SimpleGraph.Reachable.refl _
  | u, v, @SimpleGraph.Walk.cons _ _ _ z _ hadj rest, hu, hv => by
    rcases hadj with ⟨hne, e, he, hdir⟩
    have hz : z ∈ S.verts := by
      rcases hdir with ⟨_, rfl⟩ | ⟨rfl, _⟩
      · exact S.tail_mem he
      · exact S.head_mem he
    have hadjG : G.toSimpleGraph.Adj u z :=
      adj_toSimpleGraph_of_digraphSubgraph_adj G S ⟨hne, e, he, hdir⟩
    have hadj_ind : (G.toSimpleGraph.induce (S.verts : Set (Fin n))).Adj ⟨u, hu⟩ ⟨z, hz⟩ :=
      hadjG
    exact hadj_ind.reachable.trans (reachable_induce_of_digraphSubgraph_walk G S rest hz hv)

theorem mem_completeGraphEdges_of_lt {p : ℕ} {u v : Fin p} (huv : u < v) :
    (u, v) ∈ completeGraphEdges p := by
  unfold completeGraphEdges
  rw [List.mem_filter]
  exact ⟨mem_allDirectedPairs (u, v), decide_eq_true huv⟩

/-- Every `M : UnderlyingGraphModel (completeComputeDigraph p) G.toComputeDigraph` (`Specs13.lean`)
induces a valid `IsCliqueModel G.toSimpleGraph p (fun u => (M.vertMap u).verts)`. -/
theorem UnderlyingGraphModel.to_isCliqueModel {n p : ℕ} {G : MultiDigraph n}
    (M : UnderlyingGraphModel (completeComputeDigraph p) G.toComputeDigraph) :
    IsCliqueModel G.toSimpleGraph p (fun u => (M.vertMap u).verts) := by
  have hadj_of_lt : ∀ {u v : Fin p}, u < v →
      ∃ x ∈ (M.vertMap u).verts, ∃ y ∈ (M.vertMap v).verts, G.toSimpleGraph.Adj x y := by
    intro u v huv
    rcases List.mem_iff_getElem.mp (mem_completeGraphEdges_of_lt huv) with ⟨i, hi, heq⟩
    let e : Fin (completeComputeDigraph p).numEdges := ⟨i, hi⟩
    have htail : (completeComputeDigraph p).tail e = u :=
      congrArg Prod.fst heq
    have hhead : (completeComputeDigraph p).head e = v :=
      congrArg Prod.snd heq
    have hends := M.ends_mem_vertMap e
    rw [htail, hhead] at hends
    let f := M.edgeMap e
    rcases hends with ⟨ht_u, hh_v⟩ | ⟨hh_u, ht_v⟩
    · refine ⟨G.toComputeDigraph.tail f, ht_u, G.toComputeDigraph.head f, hh_v, ?_⟩
      have hne_xy : G.toComputeDigraph.tail f ≠ G.toComputeDigraph.head f :=
        fun h => Finset.disjoint_left.mp (M.vert_disjoint u v (ne_of_lt huv)) ht_u (h ▸ hh_v)
      exact (G.toSimpleGraph_adj_iff_toComputeDigraph _ _).mpr ⟨hne_xy, f, Or.inr ⟨rfl, rfl⟩⟩
    · refine ⟨G.toComputeDigraph.head f, hh_u, G.toComputeDigraph.tail f, ht_v, ?_⟩
      have hne_xy : G.toComputeDigraph.head f ≠ G.toComputeDigraph.tail f :=
        fun h => Finset.disjoint_left.mp (M.vert_disjoint u v (ne_of_lt huv)) hh_u (h ▸ ht_v)
      exact (G.toSimpleGraph_adj_iff_toComputeDigraph _ _).mpr ⟨hne_xy, f, Or.inl ⟨rfl, rfl⟩⟩
  refine ⟨fun u => ⟨(M.connected u).1, ?_⟩, M.vert_disjoint, fun u v huv => ?_⟩
  · rcases (M.connected u).1 with ⟨x₀, hx₀⟩
    have : Nonempty ((M.vertMap u).verts : Set (Fin n)) := ⟨⟨x₀, hx₀⟩⟩
    refine SimpleGraph.Connected.mk ?_
    rintro ⟨x, hx⟩ ⟨y, hy⟩
    rcases (M.connected u).2 x hx y hy with ⟨w⟩
    exact reachable_induce_of_digraphSubgraph_walk G (M.vertMap u) w hx hy
  · rcases lt_or_gt_of_ne huv with hlt | hgt
    · exact hadj_of_lt hlt
    · rcases hadj_of_lt hgt with ⟨y, hy, x, hx, hadj⟩
      exact ⟨x, hx, y, hy, hadj.symm⟩

theorem flatMap_take_finRange_bitSetList {n p : ℕ} (X : Fin p → Finset (Fin n)) :
    ∀ (j : ℕ) (_hj : j ≤ p),
      ((List.finRange p).take j).flatMap (fun u => bitSetList (X u)) = encBitSetsUpTo X j
  | 0, _ => rfl
  | j + 1, hj => by
    have hj_lt : j < (List.finRange p).length := by simp; omega
    rw [List.take_add_one, List.getElem?_eq_getElem hj_lt, Option.toList_some,
      List.flatMap_append, flatMap_take_finRange_bitSetList X j (by omega)]
    simp [encBitSetsUpTo, show j < p by omega]

theorem flatMap_finRange_bitSetList_eq_encBitSetsUpTo {n p : ℕ} (X : Fin p → Finset (Fin n)) :
    (List.finRange p).flatMap (fun u => bitSetList (X u)) = encBitSetsUpTo X p := by
  have h := flatMap_take_finRange_bitSetList X p le_rfl
  rwa [List.take_of_length_le (by simp)] at h

/-- Dropping the `2 + 2 * (completeGraphEdges p).length` header words from
`encUnderlyingGraphModel M` (`M : UnderlyingGraphModel (completeComputeDigraph p) G.toComputeDigraph`)
yields `encBitSetsUpTo (fun u => (M.vertMap u).verts) p`. -/
theorem drop_encUnderlyingGraphModel_eq_encBitSetsUpTo {n p : ℕ} {G : MultiDigraph n}
    (M : UnderlyingGraphModel (completeComputeDigraph p) G.toComputeDigraph) :
    (encUnderlyingGraphModel M).drop (2 + 2 * (completeGraphEdges p).length) =
      encBitSetsUpTo (fun u => (M.vertMap u).verts) p := by
  unfold encUnderlyingGraphModel
  let pre := [(completeComputeDigraph p).numVerts, (completeComputeDigraph p).numEdges] ++
    (List.finRange (completeComputeDigraph p).numEdges).flatMap (fun e =>
      [(G.toComputeDigraph.tail (M.edgeMap e)).1, (G.toComputeDigraph.head (M.edgeMap e)).1])
  have hpre_len : pre.length = 2 + 2 * (completeGraphEdges p).length := by
    change ([_, _] ++ (List.finRange (completeComputeDigraph p).numEdges).flatMap _).length = _
    rw [List.length_append, List.length_flatMap]
    have hmap :
        List.map
          (fun e : Fin (completeComputeDigraph p).numEdges =>
            ([(G.toComputeDigraph.tail (M.edgeMap e)).1,
              (G.toComputeDigraph.head (M.edgeMap e)).1]).length)
          (List.finRange (completeComputeDigraph p).numEdges) =
        List.replicate (List.finRange (completeComputeDigraph p).numEdges).length 2 := by
      rw [List.map_eq_replicate_iff]
      intro _ _
      rfl
    rw [hmap, List.length_finRange, List.sum_replicate, smul_eq_mul]
    change 2 + (completeGraphEdges p).length * 2 = 2 + 2 * (completeGraphEdges p).length
    omega
  have hdrop :
      (pre ++ (List.finRange (completeComputeDigraph p).numVerts).flatMap
        (fun u => bitSetList (M.vertMap u).verts)).drop pre.length =
      (List.finRange (completeComputeDigraph p).numVerts).flatMap
        (fun u => bitSetList (M.vertMap u).verts) :=
    List.drop_left
  rw [← hpre_len]
  exact hdrop.trans (flatMap_finRange_bitSetList_eq_encBitSetsUpTo (fun u => (M.vertMap u).verts))

/-! ### Section 3: Pure Decoders, Subroutine Wrapper, and Section 9 Algorithm Statements -/

/-- Parse `k` length-prefixed `List ℕ` segments from `L`, returning `(segments, remaining)`. -/
def splitLengthPrefixedLists : ℕ → List ℕ → List (List ℕ) × List ℕ
  | 0, L => ([], L)
  | k + 1, [] => ([] :: List.replicate k [], [])
  | k + 1, len :: rest =>
    let (xs, rem) := splitLengthPrefixedLists k (rest.drop len)
    (rest.take len :: xs, rem)

@[simp]
theorem length_fst_splitLengthPrefixedLists :
    ∀ (k : ℕ) (L : List ℕ), (splitLengthPrefixedLists k L).1.length = k
  | 0, _ => rfl
  | k + 1, [] => by simp [splitLengthPrefixedLists]
  | k + 1, _ :: rest => by
    simp [splitLengthPrefixedLists, length_fst_splitLengthPrefixedLists k]

theorem splitLengthPrefixedLists_flatMap :
    ∀ (ls : List (List ℕ)) (rem : List ℕ),
      splitLengthPrefixedLists ls.length
        (ls.flatMap (fun l => l.length :: l) ++ rem) = (ls, rem)
  | [], _ => rfl
  | l :: ls, rem => by
    simp only [List.length_cons, List.flatMap_cons, List.cons_append, List.append_assoc,
      splitLengthPrefixedLists, List.drop_left, List.take_left,
      splitLengthPrefixedLists_flatMap ls rem]

/-- Filter-map a `List ℕ` into `List (Fin n)` by keeping entries `< n`. -/
def filterFinList (n : ℕ) (l : List ℕ) : List (Fin n) :=
  l.filterMap (fun x => if hx : x < n then some ⟨x, hx⟩ else none)

@[simp]
theorem filterFinList_map_val {n : ℕ} :
    ∀ (P : List (Fin n)), filterFinList n (P.map Fin.val) = P
  | [] => rfl
  | v :: vs => by
    simp [filterFinList, v.2]

/-- Pure left-inverse decoder for `encHPaths` (`Specs13.lean`), returning `(paths, remaining)`. -/
def decHPaths (n k : ℕ) (L : List ℕ) : (Fin k → List (Fin n)) × List ℕ :=
  let p := splitLengthPrefixedLists k L
  (fun i => filterFinList n (p.1.getD i.1 []), p.2)

theorem flatMap_finRange_eq_map_flatMap {α β : Type*} (k : ℕ) (f : Fin k → List α)
    (g : List α → List β) :
    (List.finRange k).flatMap (fun i => g (f i)) =
      ((List.finRange k).map f).flatMap g := by
  rw [List.flatMap_map]

@[simp]
theorem decHPaths_encHPaths_append {n k : ℕ} (paths : Fin k → List (Fin n)) (rem : List ℕ) :
    decHPaths n k (encHPaths paths ++ rem) = (paths, rem) := by
  unfold decHPaths encHPaths
  let ls : List (List ℕ) := (List.finRange k).map (fun i => (paths i).map Fin.val)
  have hlen : ls.length = k := by simp [ls]
  have hflat :
      (List.finRange k).flatMap (fun i => (paths i).length :: (paths i).map Fin.val) =
        ls.flatMap (fun l => l.length :: l) := by
    rw [List.flatMap_map]
    congr 1
    funext i
    simp
  have hparse :
      splitLengthPrefixedLists k
        ((List.finRange k).flatMap (fun i => (paths i).length :: (paths i).map Fin.val) ++ rem) =
        (ls, rem) := by
    rw [hflat, ← hlen, splitLengthPrefixedLists_flatMap]
  dsimp only
  rw [hparse]
  dsimp only
  congr 1
  funext i
  have hi : i.1 < ls.length := by rw [hlen]; exact i.2
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi, Option.getD_some]
  simp [ls]

/-- Pure left-inverse decoder for `WallOfHeight.encList` (`Wall.lean`) when `0 < n`, returning
`(W, remaining)`. -/
def decWallOfHeight (h n : ℕ) (hn : 0 < n) (G : MultiDigraph n) (L : List ℕ) :
    WallOfHeight h G × List ℕ :=
  let numV := elemWallNumVerts h
  let numE := (elemWallEdges h).length
  let brRaw := (L.drop 3).take numV
  let p := splitLengthPrefixedLists numE (L.drop (3 + numV))
  ({ branchVert := fun u =>
       let x := brRaw.getD u.1 0
       if hx : x < n then ⟨x, hx⟩ else ⟨0, hn⟩
     internalVerts := fun k => filterFinList n (p.1.getD k.1 []) },
   p.2)

@[ext]
theorem WallOfHeight.ext {h n : ℕ} {G : MultiDigraph n} {W₁ W₂ : WallOfHeight h G}
    (hbr : ∀ u, W₁.branchVert u = W₂.branchVert u)
    (hint : ∀ k, W₁.internalVerts k = W₂.internalVerts k) :
    W₁ = W₂ := by
  cases W₁
  cases W₂
  congr
  · funext u; exact hbr u
  · funext k; exact hint k

@[simp]
theorem decWallOfHeight_encList_append {h n : ℕ} (hn : 0 < n) {G : MultiDigraph n}
    (W : WallOfHeight h G) (rem : List ℕ) :
    decWallOfHeight h n hn G (W.encList ++ rem) = (W, rem) := by
  let numV := elemWallNumVerts h
  let numE := (elemWallEdges h).length
  let hdr : List ℕ := [h, numV, numE]
  let brList : List ℕ := (List.finRange numV).map (fun u => (W.branchVert u).1)
  let intLs : List (List ℕ) := (List.finRange numE).map (fun k => (W.internalVerts k).map Fin.val)
  have hhdr_len : hdr.length = 3 := rfl
  have hbr_len : brList.length = numV := by simp [brList]
  have hint_len : intLs.length = numE := by simp [intLs]
  have hint_flat :
      (List.finRange numE).flatMap (fun k => (W.internalVerts k).length :: (W.internalVerts k).map Fin.val) =
        intLs.flatMap (fun l => l.length :: l) := by
    rw [List.flatMap_map]
    congr 1
    funext k
    simp
  have henc_eq : W.encList ++ rem =
      (hdr ++ brList ++ intLs.flatMap (fun l => l.length :: l)) ++ rem := by
    unfold WallOfHeight.encList
    rw [hint_flat]
  have hdrop3 : (W.encList ++ rem).drop 3 =
      brList ++ (intLs.flatMap (fun l => l.length :: l) ++ rem) := by
    rw [henc_eq, List.append_assoc (hdr ++ brList), List.append_assoc hdr, ← hhdr_len, List.drop_left]
  have htake_br : ((W.encList ++ rem).drop 3).take numV = brList := by
    rw [hdrop3, ← hbr_len, List.take_left]
  have hdrop_all :
      (W.encList ++ rem).drop (3 + numV) =
        intLs.flatMap (fun l => l.length :: l) ++ rem := by
    have hlen_hb : (hdr ++ brList).length = 3 + numV := by
      rw [List.length_append, hhdr_len, hbr_len]
    rw [henc_eq, List.append_assoc (hdr ++ brList), ← hlen_hb, List.drop_left]
  have hparse :
      splitLengthPrefixedLists numE ((W.encList ++ rem).drop (3 + numV)) = (intLs, rem) := by
    rw [hdrop_all, ← hint_len, splitLengthPrefixedLists_flatMap]
  unfold decWallOfHeight
  dsimp only
  rw [htake_br, hparse]
  dsimp only
  congr 1
  apply WallOfHeight.ext
  · intro u
    dsimp only
    have hu : u.1 < brList.length := by rw [hbr_len]; exact u.2
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hu, Option.getD_some]
    simp [brList]
  · intro k
    dsimp only
    have hk : k.1 < intLs.length := by rw [hint_len]; exact k.2
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hk, Option.getD_some]
    simp [intLs]

/-- General subroutine execution lemma for `ComputesArrRelInTime`: any program `P` satisfying
`ComputesArrRelInTime size encIn Spec P T` can be executed at any word size `w ≥ wordSize c (size x)`
from any state `s` with `s.arrs inArr = encIn x`, producing `s'.arrs outArr` satisfying `Spec x` in
at most `C * T (size x)` steps while preserving all registers `r ≥ folioCallerRegBase P` and all
arrays `a ≥ folioCallerArrBase P`. -/
theorem ComputesArrRelInTime.subroutine_exec {X : Type*} {size : X → ℕ} {encIn : X → List ℕ}
    {Spec : X → List ℕ → Prop} {P : Cmd} {T : ℕ → ℕ}
    (hP : ComputesArrRelInTime size encIn Spec P T) :
    ∃ C c : ℕ, 1 ≤ C ∧ 1 ≤ c ∧
      ∀ (x : X) (w : ℕ), wordSize c (size x) ≤ w →
      ∀ (s : State), s.arrs inArr = encIn x →
        ∃ (s' : State) (t : ℕ),
          Exec w P s s' t ∧
          t ≤ C * T (size x) ∧
          Spec x (s'.arrs outArr) ∧
          (∀ r : Reg, folioCallerRegBase P ≤ r → s'.regs r = s.regs r) ∧
          (∀ a : Arr, folioCallerArrBase P ≤ a → s'.arrs a = s.arrs a) := by
  rcases hP with ⟨C, c, hC, hc, hexec⟩
  refine ⟨C, c, hC, hc, fun x w hw s hs => ?_⟩
  rcases hexec x s hs with ⟨s', t, hex, ht, hout⟩
  have hex_w : Exec w P s s' t := hex.mono_wordSize hw
  refine ⟨s', t, hex_w, ht, hout, ?_, ?_⟩
  · intro r hr
    exact hex_w.regs_eq_of_not_mem_writtenRegs (not_mem_writtenRegs_of_ge_folioCallerRegBase P hr)
  · intro a ha
    exact hex_w.arrs_eq_of_not_mem_writtenArrs (not_mem_writtenArrs_of_ge_folioCallerArrBase P ha)

/-- Copy the entire contents of array `src` into array `dst` (`src ≠ dst`) using scratch registers
`r_len` and `r_idx` (`r_len ≠ r_idx`). -/
def copyArrLoopProg (src dst : Arr) (r_len r_idx : Reg) : Cmd :=
  .seq (.assign r_len (.len src))
    (.seq (.alloc dst (.reg r_len))
      (.seq (.assign r_idx (.const 0))
        (forUp r_idx (.reg r_len)
          (.write dst (.reg r_idx) (.read src (.reg r_idx))))))

theorem copyArrLoopProg_exec {w : ℕ} (src dst : Arr) (r_len r_idx : Reg)
    (hne_arr : src ≠ dst) (hne_reg : r_len ≠ r_idx)
    (hw1 : 1 < 2 ^ w) (s : State)
    (hlen_w : (s.arrs src).length < 2 ^ w)
    (hvals_w : ∀ x ∈ s.arrs src, x < 2 ^ w) :
    ∃ s' t,
      Exec w (copyArrLoopProg src dst r_len r_idx) s s' t ∧
      t ≤ 8 + 15 * (s.arrs src).length ∧
      s'.arrs dst = s.arrs src ∧
      (∀ a : Arr, a ≠ dst → s'.arrs a = s.arrs a) ∧
      (∀ r : Reg, r ≠ r_len → r ≠ r_idx → s'.regs r = s.regs r) := by
  let s₁ := s.setReg r_len (s.arrs src).length
  have hex₁ : Exec w (.assign r_len (.len src)) s s₁ 2 :=
    .assign (by simp [Expr.eval, checkWord, hlen_w])
  let s₂ := s₁.setArr dst (List.replicate (s.arrs src).length 0)
  have hex₂ : Exec w (.alloc dst (.reg r_len)) s₁ s₂ (1 + (s.arrs src).length) :=
    .alloc (by simp [s₁, Expr.eval, checkWord, hlen_w])
  let s₂_init := s₂.setReg r_idx 0
  have hex_init : Exec w (.assign r_idx (.const 0)) s₂ s₂_init 2 :=
    .assign (by simp [Expr.eval, checkWord, show 0 < 2 ^ w by omega])
  let Inv (i : ℕ) (st : State) : Prop :=
    st.arrs src = s.arrs src ∧
    (st.arrs dst).length = (s.arrs src).length ∧
    (∀ j < i, (st.arrs dst).getD j 0 = (s.arrs src).getD j 0) ∧
    st.regs r_len = (s.arrs src).length ∧
    st.regs r_idx = i ∧
    (∀ a : Arr, a ≠ dst → st.arrs a = s.arrs a) ∧
    (∀ r : Reg, r ≠ r_len → r ≠ r_idx → st.regs r = s.regs r)
  have hLoop :
      ⦃Inv 0⦄[w]
        forUp r_idx (.reg r_len) (.write dst (.reg r_idx) (.read src (.reg r_idx)))
      ⦃Inv (s.arrs src).length⦄ ≤ fun _ => 3 + (s.arrs src).length * (7 + 4) := by
    apply Triple.forUp_const Inv (s.arrs src).length 4 hw1 hlen_w
    · intro i _ st ⟨_, _, _, hr_len, hr_idx, _, _⟩
      exact ⟨hr_idx, by simp [Expr.eval, checkWord, hr_len, hlen_w]⟩
    · intro i hi st ⟨hsrc, hdst_len, hpref, hr_len, hr_idx, harrs, hregs⟩
      have hi_w : i < 2 ^ w := by omega
      have hval_w : (s.arrs src)[i]'hi < 2 ^ w := hvals_w _ (List.getElem_mem hi)
      have hidx_eval : (Expr.reg r_idx).eval w st = some i := by
        simp [Expr.eval, checkWord, hr_idx, hi_w]
      have hval_eval : (Expr.read src (.reg r_idx)).eval w st = some ((s.arrs src)[i]'hi) := by
        simp [Expr.eval, checkWord, hr_idx, hi_w, hsrc, hi, hval_w]
      have hi_dst : i < (st.arrs dst).length := by rw [hdst_len]; exact hi
      let st' := st.writeArr dst i ((s.arrs src)[i]'hi)
      have hex_w : Exec w (.write dst (.reg r_idx) (.read src (.reg r_idx))) st st' 4 :=
        .write hidx_eval hval_eval hi_dst
      refine ⟨st', 4, hex_w, le_rfl, ?_, by simp [st', hr_idx]⟩
      refine ⟨by simpa [st', State.writeArr_arrs_ne _ _ _ hne_arr] using hsrc,
        by simp [st', hdst_len],
        fun j hj => ?_,
        by simp [st', State.setReg_regs_ne _ _ hne_reg, hr_len],
        State.setReg_regs_self st' r_idx (i + 1),
        fun a ha => by rw [State.setReg_arrs, State.writeArr_arrs_ne _ _ _ ha]; exact harrs a ha,
        fun r hr1 hr2 => by rw [State.setReg_regs_ne _ _ hr2, State.writeArr_regs]; exact hregs r hr1 hr2⟩
      simp only [st', State.setReg_arrs, State.writeArr_arrs_self]
      by_cases hji : j = i
      · subst hji
        have hj_set : j < ((st.arrs dst).set j ((s.arrs src)[j]'hi)).length := by
          rw [List.length_set]; exact hi_dst
        rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj_set, Option.getD_some,
          List.getElem_set_self, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi, Option.getD_some]
      · have hj_lt : j < i := by omega
        have hj_src : j < (s.arrs src).length := by omega
        have hj_dst : j < (st.arrs dst).length := by rw [hdst_len]; exact hj_src
        have hj_set : j < ((st.arrs dst).set i ((s.arrs src)[i]'hi)).length := by
          rw [List.length_set]; exact hj_dst
        have h1 : ((st.arrs dst).set i ((s.arrs src)[i]'hi)).getD j 0 = (st.arrs dst)[j]'hj_dst := by
          rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj_set, Option.getD_some,
            List.getElem_set_ne (by omega)]
        have h2 : (st.arrs dst).getD j 0 = (st.arrs dst)[j]'hj_dst := by
          rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj_dst, Option.getD_some]
        rw [h1, ← h2]
        exact hpref j hj_lt
  have hInv0 : Inv 0 s₂_init := by
    refine ⟨by simp [s₂_init, s₂, s₁, State.setArr_arrs_ne _ _ hne_arr],
      by simp [s₂_init, s₂],
      fun j hj => by omega,
      by simp [s₂_init, s₂, s₁, State.setReg_regs_ne _ _ hne_reg],
      by simp [s₂_init],
      fun a ha => by simp [s₂_init, s₂, s₁, State.setArr_arrs_ne _ _ ha],
      fun r hr1 hr2 => by simp [s₂_init, s₂, s₁, State.setReg_regs_ne _ _ hr1, State.setReg_regs_ne _ _ hr2]⟩
  rcases hLoop s₂_init hInv0 with ⟨s₃, t₃, hex₃, ht₃, hsrc₃, hdst_len₃, hpref₃, _, _, harrs₃, hregs₃⟩
  dsimp only at ht₃
  refine ⟨s₃, 2 + ((1 + (s.arrs src).length) + (2 + t₃)), .seq hex₁ (.seq hex₂ (.seq hex_init hex₃)),
    by omega, ?_, harrs₃, hregs₃⟩
  refine List.ext_getElem hdst_len₃ (fun j hj1 hj2 => ?_)
  have h := hpref₃ j hj2
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj1, Option.getD_some,
    List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj2, Option.getD_some] at h
  exact h

/-! ### Section 3: Algorithm Statements for (9.1), (9.2), (9.4), (9.7), and (9.9) -/

/-! #### 3a. Algorithm of (9.1) (page 98) -/

/-- Input to the algorithm of **Graph Minors XIII, (9.1)** (Section 9, page 98):
> "(9.1) *For any integer $p \ge 0$ there exist $k, r \ge 0$ such that the following holds. Let $H$
> be a wall in $G$, and let $H_1, \dots, H_k$ be subwalls of $H$ with $d(H_i, H_j) \ge r$
> ($1 \le i < j \le k$), where $d$ is the distance function of $H$. For $1 \le i \le k$, let
> $P_i \cup Q_i$ be a cross over $H_i$, such that*
> *(i) $(P_i \cup Q_i) \cap H \subseteq H_i$, for $1 \le i \le k$*
> *(ii) $(P_i \cup Q_i) \cap (P_j \cup Q_j)$ is null for $1 \le i < j \le k$.*
> *Then $G$ has a $K_p$-minor.*"
> "Moreover, a model of $K_p$ in $G$ can be found in time $\le C\varepsilon(G)$, where $C$ depends
> only on $p$ and the height of $H$." -/
structure Alg91Input (p h k r : ℕ) where
  /-- Number of vertices `|V(G)|`. -/
  n : ℕ
  /-- The input graph `G` on `Fin n`. -/
  G : MultiDigraph n
  /-- The wall `H` of height `h` in `G`. -/
  W : WallOfHeight h G
  /-- Heights `h_sub a` of the `k` subwalls `H_1, …, H_k`. -/
  h_sub : Fin k → ℕ
  /-- The `k` subwalls `H_1, …, H_k` of `H`. -/
  W_sub : ∀ a : Fin k, WallOfHeight (h_sub a) G
  /-- First path `P_a` of the cross over `H_a`. -/
  P : Fin k → List (Fin n)
  /-- Second path `Q_a` of the cross over `H_a`. -/
  Q : Fin k → List (Fin n)
  /-- `h ≥ 2` is even and `W` is a valid wall in `G`. -/
  hW_valid : 2 ≤ h ∧ Even h ∧ W.IsValid
  /-- Each `W_sub a` is a subwall of `W`. -/
  hsub : ∀ a : Fin k, (W_sub a).IsSubwallOf W
  /-- Pairwise distance `d(H_i, H_j) ≥ r` (`1 ≤ i < j ≤ k`). -/
  hdist : ∀ a b : Fin k, a ≠ b →
    ∀ u ∈ (W_sub a).vertexFinset, ∀ v ∈ (W_sub b).vertexFinset, r ≤ W.brickDist u v
  /-- For each `a`, `(P a, Q a)` is a cross over `W_sub a` in `G`. -/
  hcross : ∀ a : Fin k, (W_sub a).IsCrossOverWall (hsub a).1 (P a) (Q a)
  /-- Condition (i): `(P_a ∪ Q_a) ∩ H ⊆ H_a` for `1 ≤ a ≤ k`. -/
  hinter : ∀ a : Fin k, ∀ v : Fin n,
    (v ∈ P a ∨ v ∈ Q a) → v ∈ W.vertexFinset → v ∈ (W_sub a).vertexFinset
  /-- Condition (ii): `(P_a ∪ Q_a) ∩ (P_b ∪ Q_b)` is null for `a ≠ b`. -/
  hdisj : ∀ a b : Fin k, a ≠ b → ∀ v : Fin n,
    ¬ ((v ∈ P a ∨ v ∈ Q a) ∧ (v ∈ P b ∨ v ∈ Q b))

/-- Problem size `ε(G) = |E(G)| + |V(G)| + 1` for (9.1). -/
def alg91Size {p h k r : ℕ} (x : Alg91Input p h k r) : ℕ :=
  x.G.numEdges + x.n + 1

/-- Flat Word RAM input encoding of `x : Alg91Input p h k r` in `inArr`:
`x.G.enc ++ x.W.encList`, followed for each `a : Fin k` by `(x.W_sub a).encList` and the two
length-prefixed cross paths `P a` and `Q a`. -/
def encAlg91In {p h k r : ℕ} (x : Alg91Input p h k r) : List ℕ :=
  x.G.enc ++ x.W.encList ++
    (List.finRange k).flatMap (fun a =>
      (x.W_sub a).encList ++
      ((x.P a).length :: (x.P a).map Fin.val) ++
      ((x.Q a).length :: (x.Q a).map Fin.val))

/-- Output specification for the algorithm of (9.1) on input `x : Alg91Input p h k r`:
`out = encBitSetsUpTo K p` for a valid model `K : Fin p → Finset (Fin x.n)` of $K_p$ in `x.G`. -/
def IsAlg91Output (p : ℕ) {h k r : ℕ} (x : Alg91Input p h k r) (out : List ℕ) : Prop :=
  ∃ K : Fin p → Finset (Fin x.n),
    out = encBitSetsUpTo K p ∧
    IsCliqueModel x.G.toSimpleGraph p K

/-- **Statement of the Algorithm of Graph Minors XIII, (9.1) (page 98)** on the Word RAM:
For every integer `p ≥ 0`, there exist `k, r ≥ 0` such that for every even height `h ≥ 2`, there is
a Word RAM program `P` with running time `≤ C * ε(G)` (where `C` depends only on `p` and the height
`h` of `H`) that, given `G`, a wall `H` of height `h` in `G`, `k` subwalls `H_1, …, H_k` of `H` at
pairwise distance `≥ r` in `H`, and crosses `P_i ∪ Q_i` over `H_i` satisfying (i) and (ii), outputs
a model of $K_p$ in `G`. -/
def Algorithm91Statement : Prop :=
  ∀ p : ℕ, ∃ k r : ℕ, ∀ h : ℕ, 2 ≤ h → Even h →
    ∃ P : Cmd,
      ComputesArrRelInTime (alg91Size (p := p) (h := h) (k := k) (r := r))
        (encAlg91In (p := p) (h := h) (k := k) (r := r))
        (IsAlg91Output p) P (fun s => s)

/-! #### 3b. Algorithm of (9.2) (page 99) -/

/-- Input to the algorithm of **Graph Minors XIII, (9.2)** (Section 9, page 99):
> "(9.2) *For any $l \ge 3$, and $m, p \ge 0$, there exist $k, r \ge 0$ such that the following
> holds. Let $H$ be a wall with distance function $d$ in a graph $G$, and let $H_1, \dots, H_k$ be
> non-dividing subwalls of $H$, with*
> $$d(H_i, H_j) \ge r \quad (1 \le i < j \le k).$$
> *Then either there is an $(l, m)$-star over $H$ or $G$ has a $K_p$-minor.*"
> "Moreover, there is an algorithm with running time $\le C\varepsilon(G)$ where $C$ depends only on
> $l, m, p$ and the height of $H$, which, given $G, H, H_1, \dots, H_k$ as above, finds either an
> $(l, m)$-star over $H$ or a model of $K_p$ in $G$." -/
structure Alg92Input (l m p h k r : ℕ) where
  /-- Number of vertices `|V(G)|`. -/
  n : ℕ
  /-- The input graph `G` on `Fin n`. -/
  G : MultiDigraph n
  /-- The wall `H` of height `h` in `G`. -/
  W : WallOfHeight h G
  /-- Heights `h_sub a` of the `k` non-dividing subwalls `H_1, …, H_k`. -/
  h_sub : Fin k → ℕ
  /-- The `k` non-dividing subwalls `H_1, …, H_k` of `H`. -/
  W_sub : ∀ a : Fin k, WallOfHeight (h_sub a) G
  /-- `h ≥ 2` is even and `W` is a valid wall in `G`. -/
  hW_valid : 2 ≤ h ∧ Even h ∧ W.IsValid
  /-- Each `W_sub a` is a non-dividing subwall of `W` in `G`. -/
  hnondiv : ∀ a : Fin k, W.IsNonDividingSubwall (W_sub a)
  /-- Pairwise distance `d(H_i, H_j) ≥ r` (`1 ≤ i < j ≤ k`). -/
  hdist : ∀ a b : Fin k, a ≠ b →
    ∀ u ∈ (W_sub a).vertexFinset, ∀ v ∈ (W_sub b).vertexFinset, r ≤ W.brickDist u v

/-- Problem size `ε(G) = |E(G)| + |V(G)| + 1` for (9.2). -/
def alg92Size {l m p h k r : ℕ} (x : Alg92Input l m p h k r) : ℕ :=
  x.G.numEdges + x.n + 1

/-- Flat Word RAM input encoding of `x : Alg92Input l m p h k r` in `inArr`:
`x.G.enc ++ x.W.encList`, followed for each `a : Fin k` by `(x.W_sub a).encList`. -/
def encAlg92In {l m p h k r : ℕ} (x : Alg92Input l m p h k r) : List ℕ :=
  x.G.enc ++ x.W.encList ++
    (List.finRange k).flatMap (fun a => (x.W_sub a).encList)

/-- Output specification for the algorithm of (9.2) on input `x : Alg92Input l m p h k r`:
either
- `out = 0 :: c.1 :: encHPaths rays` for an `(l, m)`-star over `x.W` in `x.G` with center `c` and
  rays `rays : Fin l → List (Fin x.n)` (in the shared star format of `Alg77Input`), or
- `out = 1 :: encBitSetsUpTo K p` for a valid model `K : Fin p → Finset (Fin x.n)` of $K_p$ in
  `x.G`. -/
def IsAlg92Output (l m p : ℕ) {h k r : ℕ} (x : Alg92Input l m p h k r) (out : List ℕ) : Prop :=
  (∃ (c : Fin x.n) (rays : Fin l → List (Fin x.n)),
    out = 0 :: c.1 :: encHPaths rays ∧
    (∀ i : Fin l, x.W.IsStarRay c (rays i)) ∧
    (∀ i j : Fin l, i ≠ j → ∀ v, v ∈ rays i → v ∈ rays j → v = c) ∧
    (∀ i j : Fin l, i ≠ j → ∀ u v,
      (rays i).getLast? = some u → (rays j).getLast? = some v → m ≤ x.W.brickDist u v)) ∨
  (∃ K : Fin p → Finset (Fin x.n),
    out = 1 :: encBitSetsUpTo K p ∧
    IsCliqueModel x.G.toSimpleGraph p K)

/-- **Statement of the Algorithm of Graph Minors XIII, (9.2) (page 99)** on the Word RAM:
For every `l ≥ 3` and `m, p ≥ 0`, there exist `k, r ≥ 0` such that for every even height `h ≥ 2`,
there is a Word RAM program `P` with running time `≤ C * ε(G)` (where `C` depends only on
`l, m, p` and the height `h` of `H`) that, given `G`, a wall `H` of height `h` in `G`, and `k`
non-dividing subwalls `H_1, …, H_k` of `H` at pairwise distance `≥ r` in `H`, outputs either an
`(l, m)`-star over `H` or a model of $K_p$ in `G`. -/
def Algorithm92Statement : Prop :=
  ∀ l m p : ℕ, 3 ≤ l →
    ∃ k r : ℕ, ∀ h : ℕ, 2 ≤ h → Even h →
      ∃ P : Cmd,
        ComputesArrRelInTime (alg92Size (l := l) (m := m) (p := p) (h := h) (k := k) (r := r))
          (encAlg92In (l := l) (m := m) (p := p) (h := h) (k := k) (r := r))
          (IsAlg92Output l m p) P (fun s => s)

/-! #### 3c. Algorithm (9.4) (page 102) -/

/-- Input to **Graph Minors XIII, Algorithm (9.4)** (Section 9, page 102):
> "(9.3) *For any $p \ge 0$ there exists $k, r \ge 0$ such that there is an algorithm as in (9.4),
> with running time $\le C\varepsilon(G)$, where $C$ depends on $p, t$, and the height of $H$.*"
> "(9.4) Algorithm.
> *Input:* A graph $G$, a wall $H \subseteq G$ with distance function $d$, and subwalls
> $H_1, \dots, H_t$ of $H$ with $d(H_i, H_j) \ge r$ ($1 \le i < j \le t$).
> *Output:* Either
> (i) a model of $K_p$ in $G$, or
> (ii) a subset $X \subseteq V(G)$ with $|X| < \binom{p}{2}$ and a subset
> $I \subseteq \{1, \dots, t\}$ with $|I| \ge t - k$ such that for all $i \in I$, $H_i$ is dividing
> in $(G \setminus X) \cup H$." -/
structure Alg94Input (p t h k r : ℕ) where
  /-- Number of vertices `|V(G)|`. -/
  n : ℕ
  /-- The input graph `G` on `Fin n`. -/
  G : MultiDigraph n
  /-- The wall `H` of height `h` in `G`. -/
  W : WallOfHeight h G
  /-- Heights `h_sub a` of the `t` subwalls `H_1, …, H_t`. -/
  h_sub : Fin t → ℕ
  /-- The `t` subwalls `H_1, …, H_t` of `H`. -/
  W_sub : ∀ a : Fin t, WallOfHeight (h_sub a) G
  /-- `h ≥ 2` is even and `W` is a valid wall in `G`. -/
  hW_valid : 2 ≤ h ∧ Even h ∧ W.IsValid
  /-- Each `W_sub a` is a subwall of `W`. -/
  hsub : ∀ a : Fin t, (W_sub a).IsSubwallOf W
  /-- Pairwise distance `d(H_i, H_j) ≥ r` (`1 ≤ i < j ≤ t`). -/
  hdist : ∀ a b : Fin t, a ≠ b →
    ∀ u ∈ (W_sub a).vertexFinset, ∀ v ∈ (W_sub b).vertexFinset, r ≤ W.brickDist u v

/-- Problem size `ε(G) = |E(G)| + |V(G)| + 1` for (9.4). -/
def alg94Size {p t h k r : ℕ} (x : Alg94Input p t h k r) : ℕ :=
  x.G.numEdges + x.n + 1

/-- Flat Word RAM input encoding of `x : Alg94Input p t h k r` in `inArr`:
`x.G.enc ++ x.W.encList`, followed for each `a : Fin t` by `(x.W_sub a).encList`. -/
def encAlg94In {p t h k r : ℕ} (x : Alg94Input p t h k r) : List ℕ :=
  x.G.enc ++ x.W.encList ++
    (List.finRange t).flatMap (fun a => (x.W_sub a).encList)

/-- Output specification for **Algorithm (9.4)** on input `x : Alg94Input p t h k r`:
either
- (i) `out = 0 :: encBitSetsUpTo K p` for a valid model `K : Fin p → Finset (Fin x.n)` of $K_p$ in
  `x.G`, or
- (ii) `out = 1 :: (bitSetList X ++ (List.finRange t).map (fun a => if a ∈ I then 1 else 0))` for a
  subset `X ⊆ V(G)` with `|X| < p.choose 2` and a subset `I ⊆ Fin t` with `t - k ≤ |I|` such that
  for all `a ∈ I`, `H_a` is dividing in `(G \ X) ∪ H`. -/
def IsAlg94Output (p t k : ℕ) {h r : ℕ} (x : Alg94Input p t h k r) (out : List ℕ) : Prop :=
  (∃ K : Fin p → Finset (Fin x.n),
    out = 0 :: encBitSetsUpTo K p ∧
    IsCliqueModel x.G.toSimpleGraph p K) ∨
  (∃ (X : Finset (Fin x.n)) (I : Finset (Fin t)),
    out = 1 :: (bitSetList X ++ (List.finRange t).map (fun a => if a ∈ I then 1 else 0)) ∧
    X.card < p.choose 2 ∧
    t - k ≤ I.card ∧
    let G' := WallOfHeight.wallUnionMultiDigraph x.G X x.W
    ∀ a ∈ I,
      (x.W.castGraph G').IsDividingSubwall ((x.W_sub a).castGraph G'))

/-- **Statement of Graph Minors XIII, (9.3) and Algorithm (9.4) (page 102)** on the
Word RAM:
For every `p ≥ 0`, there exist `k, r ≥ 0` such that for every `t` and every even height `h ≥ 2`,
there is a Word RAM program `P` with running time `≤ C * ε(G)` (where `C` depends only on `p, t`,
and the height `h` of `H`) that computes an output satisfying `IsAlg94Output p t k`. -/
def Algorithm94Statement : Prop :=
  ∀ p : ℕ, ∃ k r : ℕ, ∀ t h : ℕ, 2 ≤ h → Even h →
    ∃ P : Cmd,
      ComputesArrRelInTime (alg94Size (p := p) (t := t) (h := h) (k := k) (r := r))
        (encAlg94In (p := p) (t := t) (h := h) (k := k) (r := r))
        (IsAlg94Output p t k) P (fun s => s)

/-! #### 3d. Algorithm (9.7) (page 103) -/

/-- Input to **Graph Minors XIII, Algorithm (9.7)** (Section 9, page 103):
> "(9.6) *For any $p, s \ge 0$ and $h \ge 2$, even, there exists $h' \ge p^2 + 2$, even, and an
> algorithm as in (9.7) with running time $O(v\varepsilon)$ for fixed $p, s, h$.*"
> "(9.7) Algorithm.
> *Input:* A graph $G$, and a wall $H$ in $G$ of height $h'$.
> *Output:* Either
> (i) a model of $K_p$ in $G$, or
> (ii) a subset $X \subseteq V(G)$ with $|X| < \binom{p}{2}$ and $s$ subwalls $H_1, \dots, H_s$ of
> $H$ of height $h$, mutually vertex-disjoint, and each flat and dividing in
> $(G \setminus X) \cup H$, and each disjoint from $X$." -/
structure Alg97Input (h' : ℕ) where
  /-- Number of vertices `|V(G)|`. -/
  n : ℕ
  /-- The input graph `G` on `Fin n`. -/
  G : MultiDigraph n
  /-- The wall `H` of height `h'` in `G`. -/
  W : WallOfHeight h' G
  /-- `h' ≥ 2` is even and `W` is a valid wall in `G`. -/
  hW_valid : 2 ≤ h' ∧ Even h' ∧ W.IsValid

/-- Problem size `v(G) * ε(G) = (|V(G)| + 1) * (|E(G)| + |V(G)| + 1)` for (9.7). -/
def alg97Size {h' : ℕ} (x : Alg97Input h') : ℕ :=
  (x.n + 1) * (x.G.numEdges + x.n + 1)

/-- Flat Word RAM input encoding of `x : Alg97Input h'` in `inArr`:
`x.G.enc ++ x.W.encList`. -/
def encAlg97In {h' : ℕ} (x : Alg97Input h') : List ℕ :=
  x.G.enc ++ x.W.encList

/-- Output specification for **Algorithm (9.7)** on input `x : Alg97Input h'`:
either
- (i) `out = 0 :: encBitSetsUpTo K p` for a valid model `K : Fin p → Finset (Fin x.n)` of $K_p$ in
  `x.G`, or
- (ii) `out = 1 :: (bitSetList X ++ (List.finRange s).flatMap (fun a => (W_flat a).encList))` for a
  subset `X ⊆ V(G)` with `|X| < p.choose 2` and `s` mutually vertex-disjoint subwalls
  `W_flat : Fin s → WallOfHeight h x.G` of `x.W` of height `h`, each disjoint from `X`, and each
  flat and dividing in `(G \ X) ∪ H`. -/
def IsAlg97Output (p s h h' : ℕ) (x : Alg97Input h') (out : List ℕ) : Prop :=
  (∃ K : Fin p → Finset (Fin x.n),
    out = 0 :: encBitSetsUpTo K p ∧
    IsCliqueModel x.G.toSimpleGraph p K) ∨
  (∃ (X : Finset (Fin x.n)) (W_flat : Fin s → WallOfHeight h x.G)
      (hsub : ∀ a : Fin s, (W_flat a).IsSubwallOf x.W),
    out = 1 :: (bitSetList X ++ (List.finRange s).flatMap (fun a => (W_flat a).encList)) ∧
    X.card < p.choose 2 ∧
    Pairwise (fun a b : Fin s => Disjoint (W_flat a).vertexFinset (W_flat b).vertexFinset) ∧
    let G' := WallOfHeight.wallUnionMultiDigraph x.G X x.W
    ∀ a : Fin s,
      Disjoint (W_flat a).vertexFinset X ∧
      ((W_flat a).castGraph G').IsFlatWall (hsub a).1 ∧
      (x.W.castGraph G').IsDividingSubwall ((W_flat a).castGraph G'))

/-- **Statement of Graph Minors XIII, (9.6) and Algorithm (9.7) (page 103)** on the
Word RAM:
For every `p, s ≥ 0` and even `h ≥ 2`, there exists an even height `h' ≥ p ^ 2 + 2` and a Word RAM
program `P` with running time `O(vε)` (`≤ C * alg97Size x`, where `C` depends only on `p, s, h`)
that computes an output satisfying `IsAlg97Output p s h h'`. -/
def Algorithm97Statement : Prop :=
  ∀ p s h : ℕ, 2 ≤ h → Even h →
    ∃ h' : ℕ, p ^ 2 + 2 ≤ h' ∧ Even h' ∧
      ∃ P : Cmd,
        ComputesArrRelInTime (alg97Size (h' := h'))
          (encAlg97In (h' := h'))
          (IsAlg97Output p s h h') P (fun m => m)

/-! #### 3e. Algorithm (9.9) (page 104) -/

/-- Standalone input to **Graph Minors XIII, Algorithm (9.9)** (Section 9, page 104):
> "(9.8) *For all $p \ge 0$ and $h \ge 2$, even, there exists $\omega \ge 0$ such that there is an
> algorithm as in (9.9), with running time $O(v\varepsilon)$ for fixed $p, h$.*
> (9.9) Algorithm.
> *Input:* A graph $G$.
> *Output:* Either
> (i) a branch-decomposition of $G$ of width $\le \omega$, or
> (ii) a model of $K_p$ in $G$, or
> (iii) a subset $X \subseteq V$ with $|X| < \binom{p}{2}$ and a flat wall $H$ in $G \setminus X$ of
> height $h$, and a rural division $\mathcal{A}$ of the society of $H$ in $G \setminus X$, and a
> branch-decomposition of width $\le \omega$ of each interior member of $\mathcal{A}$." -/
structure Alg99Input where
  /-- Number of vertices `|V(G)|`. -/
  n : ℕ
  /-- The input graph `G` on `Fin n`. -/
  G : MultiDigraph n

/-- Problem size `v(G) * ε(G) = (|V(G)| + 1) * (|E(G)| + |V(G)| + 1)` for (9.9). -/
def alg99Size (x : Alg99Input) : ℕ :=
  (x.n + 1) * (x.G.numEdges + x.n + 1)

/-- Flat Word RAM input encoding of `x : Alg99Input` in `inArr`: `x.G.enc`. -/
def encAlg99In (x : Alg99Input) : List ℕ :=
  x.G.enc

/-- Output specification for **Algorithm (9.9)** on input `x : Alg99Input`, parameterized by a
`Case3BlockDecoder` `dec`:
either
- (i) `out = 0 :: code` with `IsValidBranchDecompCode ω x.G code` (giving
  `GM13.GraphBranchWidthLE x.G.toGMDigraph.toGraph ω`), or
- (ii) `out = 1 :: encBitSetsUpTo K p` with `IsCliqueModel x.G.toSimpleGraph p K` (giving
  `GM13.HasGraphModel (GM16.completeGraph p) x.G.toGMDigraph.toGraph`), or
- (iii) `out = 2 :: (bitSetList X ++ block)` for a subset `X : Finset (Fin x.n)` with
  `X.card < p.choose 2` and a Case (iii) block `block` whose decoding via `dec` yields a flat wall
  `H` of height `h` in `G \ X`, its wall society `S_H` in `G \ X`, a rural division `𝒜` of `S_H`,
  and for each interior member `A` of `𝒜` a branch-decomposition of `A` of width `≤ ω` (or
  `E(A).ncard ≤ 1`). -/
def IsAlg99Output (dec : Case3BlockDecoder) (p h ω : ℕ) (x : Alg99Input) (out : List ℕ) : Prop :=
  (∃ code : List ℕ,
    out = 0 :: code ∧
    IsValidBranchDecompCode ω x.G code) ∨
  (∃ K : Fin p → Finset (Fin x.n),
    out = 1 :: encBitSetsUpTo K p ∧
    IsCliqueModel x.G.toSimpleGraph p K) ∨
  (∃ (X : Finset (Fin x.n)) (block : List ℕ),
    out = 2 :: (bitSetList X ++ block) ∧
    X.card < p.choose 2 ∧
    let H := dec.wall x.n x.G X block
    let S_H := dec.society x.n x.G X block
    let 𝒜 := dec.division x.n x.G X block
    H.height = h ∧
    GM13.IsFlatWallIn
      (GM09.deleteVertices x.G.toGMDigraph.toGraph X.toNatSet) H ∧
    GM13.IsWallSociety
      (GM09.deleteVertices x.G.toGMDigraph.toGraph X.toNatSet) H S_H ∧
    GM13.IsRuralDivision S_H 𝒜 ∧
    ∀ ⦃A : Graph ℕ (ℕ × ℕ × ℕ)⦄,
      GM13.IsInteriorMember H 𝒜 A →
        let bd := dec.branchDecomp x.n x.G X block A
        E(A).ncard ≤ 1 ∨
          (GM13.IsGraphBranchDecomposition A bd.2.1 bd.2.2 ∧
            GM13.graphBranchDecompWidth A bd.2.1 bd.2.2 ≤ ω))

/-- **Statement of Graph Minors XIII, (9.8) and Algorithm (9.9) (page 104)** on the
Word RAM, parameterized by `dec : Case3BlockDecoder`:
For every `p ≥ 0` and even `h ≥ 2`, there exists `ω ≥ 0` and a Word RAM program `P` with running
time `O(vε)` (`≤ C * alg99Size x`, where `C` depends only on `p, h`) that computes an output
satisfying `IsAlg99Output dec p h ω`, as well as meeting `Alg99Spec dec p h ω` (`Specs105.lean`). -/
def Algorithm99Statement (dec : Case3BlockDecoder) : Prop :=
  ∀ p h : ℕ, 2 ≤ h → Even h →
    ∃ ω : ℕ,
      (∃ P : Cmd,
        ComputesArrRelInTime alg99Size encAlg99In (IsAlg99Output dec p h ω) P (fun m => m)) ∧
      Alg99Spec dec p h ω

end GraphMinor.Compute
