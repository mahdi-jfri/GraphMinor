module

public import GraphMinor.Compute.Specs9
import GraphMinor.GM13.Section9b

/-!
# Graph Minors XIII, (9.2): every input has a correct output (`Algorithm92Exists.lean`)

This file proves `exists_isAlg92Output`: for `l ≥ 3` and `m, p ≥ 0`, with `k, r` as in
**Graph Minors XIII, (9.2)** (page 99), every input `x : Alg92Input l m p h k r` of the algorithm
of (9.2) has an output `out` with `IsAlg92Output l m p x out`. So the statement
`Algorithm92Statement` asks for something that exists.

The proof applies `GM13.theorem_9_2_proof` to the graph of `x.G` and the wall `x.W` drawn as in Fig. 1
(`WallOfHeight.toDrawnGMWall`), and then writes its star or its model of `K_p` in the formats of
`IsAlg92Output`.

One point needs care. A graph `x.G` may have several edges between two vertices that are joined by
an edge of the wall. The paper's star may use such a parallel edge, since it is not an edge of
`H`. The format of `IsAlg92Output` writes a ray as a list of vertices, and it asks that no two
consecutive vertices of a ray are joined by an edge of the wall. So we first delete every edge of
`G` that is not an edge of `H` but joins two vertices that are joined by an edge of `H`
(`keptEdges`). Every `H_i` is still non-dividing after this, because an `H`-path from inside `H_i`
to outside `H_i` never uses such an edge: its two ends would be joined by an edge of `H` from inside
`H_i` to outside `H_i`, and a subwall has no such edge. A star in the smaller graph is then written
as lists, and a model of `K_p` in the smaller graph is a model in `G`.
-/

public section

namespace GraphMinor.Compute

open Set Function Graph
open GraphMinor.Surface

namespace Alg92

/-- The edges of `G` that we keep: the edges of `H`, and the edges of `G` none of whose links joins
two distinct vertices that are joined by an edge of `H`. -/
def keptEdges {α β : Type*} (G H : Graph α β) : Set β :=
  E(H) ∪ {e | ∀ a b, G.IsLink e a b → a ≠ b → ¬ ∃ f, H.IsLink f a b}

private theorem le_restrict_of_le {α β : Type*} {P G : Graph α β} {E₀ : Set β}
    (hle : P ≤ G) (hE : E(P) ⊆ E₀) : P ≤ G.restrict E₀ where
  vertexSet_mono := hle.vertexSet_mono
  isLink_mono _ _ _ h := ⟨hE h.edge_mem, hle.isLink_mono h⟩

/-- Every edge of an `H`-path `P` whose ends are not joined by an edge of `H` is kept. -/
private theorem edgeSet_subset_keptEdges {α β : Type*} {G H P : Graph α β} {a b : α}
    (hP : GM14.IsHPathWithEnds G H P a b) (hab : ¬ ∃ f, H.IsLink f a b) :
    E(P) ⊆ keptEdges G H := by
  intro e he
  refine Or.inr fun x y hxy hne ⟨f, hf⟩ => ?_
  obtain ⟨x', y', hP'⟩ := (P.edge_mem_iff_exists_isLink e).mp he
  have hG' : G.IsLink e x' y' := hP.2.1.1.isLink_mono hP'
  have hxP : x ∈ V(P) ∧ y ∈ V(P) := by
    rcases hxy.eq_and_eq_or_eq_and_eq hG' with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact ⟨hP'.left_mem, hP'.right_mem⟩
    · exact ⟨hP'.right_mem, hP'.left_mem⟩
  have hinter : V(P) ∩ V(H) = {a, b} := hP.2.2.2.2.2.1
  have hx : x ∈ ({a, b} : Set α) := hinter ▸ ⟨hxP.1, hf.left_mem⟩
  have hy : y ∈ ({a, b} : Set α) := hinter ▸ ⟨hxP.2, hf.right_mem⟩
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx hy
  rcases hx with rfl | rfl <;> rcases hy with rfl | rfl
  · exact hne rfl
  · exact hab ⟨f, hf⟩
  · exact hab ⟨f, hf.symm⟩
  · exact hne rfl

/-- A subwall that is non-dividing in `G` is non-dividing in `G` restricted to `keptEdges`. -/
private theorem isNonDividingSubwall_restrict {α β : Type*} {G : Graph α β}
    {W W' : GM13.Wall α β} (h : GM13.IsNonDividingSubwall G W W') :
    GM13.IsNonDividingSubwall (G.restrict (keptEdges G W.graph)) W W' := by
  obtain ⟨hsub, P, a, b, hP, ha, hb⟩ := h
  have hab : ¬ ∃ f, W.graph.IsLink f a b := fun ⟨f, hf⟩ =>
    hb.2 (hsub.toIsProperSubwallOf.no_edge_inside_to_outside hf ha)
  refine ⟨hsub, P, a, b, ⟨le_restrict_of_le hP.1 Set.subset_union_left,
    ⟨le_restrict_of_le hP.2.1.1 (edgeSet_subset_keptEdges hP hab), hP.2.1.2⟩, hP.2.2⟩, ha, hb⟩

/-- Lift a walk along a subgraph inclusion `P ≤ Q`. -/
private def walkMono {α β : Type*} {P Q : Graph α β} (hle : P ≤ Q) :
    ∀ {u v : α}, GraphWalk P u v → GraphWalk Q u v
  | _, _, .nil hv => .nil (hle.vertexSet_mono hv)
  | _, _, .cons hl rest => .cons (hle.isLink_mono hl) (walkMono hle rest)

private theorem support_walkMono {α β : Type*} {P Q : Graph α β} (hle : P ≤ Q) :
    ∀ {u v : α} (w : GraphWalk P u v), (walkMono hle w).support = w.support
  | _, _, .nil _ => rfl
  | _, _, .cons _ rest => by
    simp only [walkMono, GraphWalk.support, support_walkMono hle rest]

private theorem edges_walkMono {α β : Type*} {P Q : Graph α β} (hle : P ≤ Q) :
    ∀ {u v : α} (w : GraphWalk P u v), (walkMono hle w).edges = w.edges
  | _, _, .nil _ => rfl
  | _, _, .cons _ rest => by
    simp only [walkMono, GraphWalk.edges, edges_walkMono hle rest]

/-- Two consecutive vertices of the list of a walk are joined by an edge of the walk. -/
private theorem exists_edge_of_mem_zip {n : ℕ} {G : MultiDigraph n} :
    ∀ {a b : ℕ} (w : GraphWalk G.toGMDigraph.toGraph a b) (ha : a < n) {x y : Fin n},
      (x, y) ∈ (WallOfHeight.graphWalkToFinList w ha).zip
        ((WallOfHeight.graphWalkToFinList w ha).drop 1) →
      ∃ e ∈ w.edges, G.toGMDigraph.toGraph.IsLink e x.1 y.1
  | _, _, .nil _, _, _, _, hxy => by
    simp [WallOfHeight.graphWalkToFinList] at hxy
  | a, _, .cons (v := c) (e := e) hlink rest, ha, x, y, hxy => by
    have hc : c < n := hlink.right_mem
    have hhead := WallOfHeight.head_graphWalkToFinList rest hc
    change (x, y) ∈ (⟨a, ha⟩ :: WallOfHeight.graphWalkToFinList rest hc).zip
      (WallOfHeight.graphWalkToFinList rest hc) at hxy
    have ih := exists_edge_of_mem_zip rest hc (x := x) (y := y)
    cases hlist : WallOfHeight.graphWalkToFinList rest hc with
    | nil => exact False.elim (WallOfHeight.graphWalkToFinList_ne_nil rest hc hlist)
    | cons z zs =>
      have hz : z = ⟨c, hc⟩ := by simpa [hlist] using hhead
      rw [hlist] at hxy ih
      simp only [List.zip_cons_cons, List.mem_cons, Prod.mk.injEq] at hxy
      rcases hxy with ⟨rfl, rfl⟩ | h
      · rw [hz]
        exact ⟨e, List.mem_cons_self .., hlink⟩
      · obtain ⟨e', he', hl⟩ := ih (by simpa using h)
        exact ⟨e', List.mem_cons_of_mem _ he', hl⟩

/-- An inner vertex of a list without repetitions is neither its first nor its last vertex. -/
private theorem ne_head_and_ne_getLast {α : Type*} {L : List α} (hne : L ≠ []) (hnd : L.Nodup)
    {y : α} (hy : y ∈ (L.drop 1).dropLast) : y ≠ L.head hne ∧ y ≠ L.getLast hne := by
  rcases L with _ | ⟨x, rest⟩
  · exact False.elim (hne rfl)
  · simp only [List.drop_succ_cons, List.drop_zero] at hy
    have hrest : rest ≠ [] := by
      rintro rfl
      simp at hy
    have hyr : y ∈ rest := List.dropLast_subset rest hy
    have hnd' := (List.nodup_cons.mp hnd)
    refine ⟨fun h => hnd'.1 (by rw [h] at hyr; exact hyr), fun h => ?_⟩
    have hsplit := hnd'.2
    rw [← List.dropLast_append_getLast hrest] at hsplit
    rw [List.getLast_cons hrest] at h
    exact (List.nodup_append.mp hsplit).2.2 y hy _ (List.mem_singleton_self _) h

/-- A walk in a subgraph `Q` of the graph of `G` joins two vertices of any vertex set `S` that
contains `V(Q)` in the graph of `G` induced on `S`. -/
private theorem reachable_induce_of_walk {n : ℕ} {G : MultiDigraph n}
    {Q : Graph ℕ (ℕ × ℕ × ℕ)} (hQ : Q ≤ G.toGMDigraph.toGraph) (S : Finset (Fin n))
    (hS : ∀ v : Fin n, v.1 ∈ V(Q) → v ∈ S) :
    ∀ {a b : ℕ} (_w : GraphWalk Q a b) (ha : a < n) (hb : b < n) (haS : ⟨a, ha⟩ ∈ S)
      (hbS : ⟨b, hb⟩ ∈ S),
      (G.toSimpleGraph.induce (S : Set (Fin n))).Reachable ⟨⟨a, ha⟩, haS⟩ ⟨⟨b, hb⟩, hbS⟩
  | _, _, .nil _, _, _, _, _ => SimpleGraph.Reachable.refl _
  | a, b, .cons (v := c) hlink rest, ha, hb, haS, hbS => by
    have hlink' := hQ.isLink_mono hlink
    have hc : c < n := hlink'.right_mem
    have hcS : (⟨c, hc⟩ : Fin n) ∈ S := hS ⟨c, hc⟩ hlink.right_mem
    have ih := reachable_induce_of_walk hQ S hS rest hc hb hcS hbS
    by_cases hac : a = c
    · subst hac
      exact ih
    · have hadj : G.toSimpleGraph.Adj ⟨a, ha⟩ ⟨c, hc⟩ :=
        WallOfHeight.adj_toSimpleGraph_of_isLink_toGMDigraph hlink'
          (fun h => hac (congrArg Fin.val h))
      exact (SimpleGraph.Adj.reachable (G := G.toSimpleGraph.induce (S : Set (Fin n)))
        (u := ⟨⟨a, ha⟩, haS⟩) (v := ⟨⟨c, hc⟩, hcS⟩) hadj).trans ih

/-- A model of `K_p` in the graph of `G` (in the sense of `GM13.HasGraphModel`) gives `p` vertex
sets that form a model of `K_p` in the sense of `IsCliqueModel`. -/
theorem isCliqueModel_of_hasGraphModel {n p : ℕ} (G : MultiDigraph n)
    (h : GM13.HasGraphModel (GM16.completeGraph p) G.toGMDigraph.toGraph) :
    ∃ K : Fin p → Finset (Fin n), IsCliqueModel G.toSimpleGraph p K := by
  classical
  obtain ⟨vMap, eMap, hM⟩ := h
  have hV : ∀ i : Fin p, i ∈ V(GM16.completeGraph p) := fun i => Set.mem_univ i
  let K : Fin p → Finset (Fin n) := fun i =>
    Finset.univ.filter (fun v : Fin n => v.1 ∈ V(vMap i))
  have hK : ∀ i (v : Fin n), v ∈ K i ↔ v.1 ∈ V(vMap i) := fun i v => by simp [K]
  have hlt : ∀ i x, x ∈ V(vMap i) → x < n := fun i x hx =>
    (hM.sub_of_mem (hV i)).vertexSet_mono hx
  refine ⟨K, fun i => ⟨?_, ?_⟩, fun i j hij => ?_, fun i j hij => ?_⟩
  · obtain ⟨x, hx⟩ := hM.nonempty_of_mem (hV i)
    exact ⟨⟨x, hlt i x hx⟩, (hK i _).mpr hx⟩
  · obtain ⟨x, hx⟩ := hM.nonempty_of_mem (hV i)
    rw [SimpleGraph.connected_iff]
    refine ⟨fun u v => ?_, ⟨⟨⟨x, hlt i x hx⟩, (hK i _).mpr hx⟩⟩⟩
    obtain ⟨⟨a, ha⟩, haK⟩ := u
    obtain ⟨⟨b, hb⟩, hbK⟩ := v
    have haV : a ∈ V(vMap i) := (hK i _).mp haK
    have hbV : b ∈ V(vMap i) := (hK i _).mp hbK
    obtain ⟨w⟩ := hM.connected_of_mem (hV i) a haV b hbV
    exact reachable_induce_of_walk (hM.sub_of_mem (hV i)) (K i)
      (fun v hv => (hK i v).mpr hv) w ha hb haK hbK
  · rw [Finset.disjoint_left]
    intro v hvi hvj
    exact Set.disjoint_left.mp (hM.disjoint_of_ne (hV i) (hV j) hij) ((hK i v).mp hvi)
      ((hK j v).mp hvj)
  · have hlink : (GM16.completeGraph p).IsLink s(i, j) i j := ⟨hij, rfl⟩
    obtain ⟨x, hx, y, hy, hxy⟩ := hM.link_ends_of_ne hlink hij
    refine ⟨⟨x, hxy.left_mem⟩, (hK i _).mpr hx, ⟨y, hxy.right_mem⟩, (hK j _).mpr hy, ?_⟩
    refine WallOfHeight.adj_toSimpleGraph_of_isLink_toGMDigraph hxy fun h => ?_
    have hxy' : x = y := congrArg Fin.val h
    subst hxy'
    exact Set.disjoint_left.mp (hM.disjoint_of_ne (hV i) (hV j) hij) hx hy

/-- An `(l, m)`-star over the drawn wall of `W` in the graph of `G` restricted to `keptEdges`
(`GM13.IsLMStarOver`) gives a center `c` and `l` rays in the format of `IsAlg92Output`. -/
theorem exists_rays_of_isLMStarOver {h n : ℕ} {G : MultiDigraph n} (W : WallOfHeight h G)
    (h2 : 2 ≤ h) (he : Even h) (hW : W.IsValid) {l m : ℕ} {S : Graph ℕ (ℕ × ℕ × ℕ)} {v : ℕ}
    (hstar : GM13.IsLMStarOver
      (G.toGMDigraph.toGraph.restrict
        (keptEdges G.toGMDigraph.toGraph (W.toDrawnGMWall h2 he hW).graph))
      (W.toDrawnGMWall h2 he hW) l m S v) :
    ∃ (c : Fin n) (rays : Fin l → List (Fin n)),
      (∀ i : Fin l, W.IsStarRay c (rays i)) ∧
      (∀ i j : Fin l, i ≠ j → ∀ y, y ∈ rays i → y ∈ rays j → y = c) ∧
      (∀ i j : Fin l, i ≠ j → ∀ a b,
        (rays i).getLast? = some a → (rays j).getLast? = some b → m ≤ W.brickDist a b) := by
  set G₀ := G.toGMDigraph.toGraph with hG₀
  set H := W.toDrawnGMWall h2 he hW with hH
  obtain ⟨P, u, -, hP, hPP, hdist⟩ := hstar.exists_paths
  have hv : v < n := hstar.center_mem
  have hle : ∀ i, P i ≤ G₀ := fun i => (hP i).1.1.trans Graph.restrict_le
  choose w hw using fun i => (hP i).1.2
  let w' : ∀ i, GraphWalk G₀ v (u i) := fun i => walkMono (hle i) (w i)
  let rays : Fin l → List (Fin n) := fun i => WallOfHeight.graphWalkToFinList (w' i) hv
  have hHV : V(H.graph) = W.vertexFinset.toNatSet := W.vertexSet_toGMWall_eq h2 he hW
  have hu : ∀ i, ∃ u' : Fin n, u' ∈ W.vertexFinset ∧ u'.1 = u i := fun i => by
    have h := (hP i).2.2.1
    rw [hHV] at h
    obtain ⟨u', hu', heq⟩ := h
    exact ⟨u', hu', heq⟩
  choose u' hu'W hu'eq using hu
  have hun : ∀ i, u i < n := fun i => hu'eq i ▸ (u' i).2
  have hne : ∀ i, rays i ≠ [] := fun i => WallOfHeight.graphWalkToFinList_ne_nil _ hv
  have hhead : ∀ i, (rays i).head (hne i) = ⟨v, hv⟩ := fun i =>
    WallOfHeight.head_graphWalkToFinList _ hv
  have hlast : ∀ i, (rays i).getLast (hne i) = u' i := fun i => by
    rw [WallOfHeight.getLast_graphWalkToFinList (w' i) hv (hun i)]
    exact Fin.ext (hu'eq i).symm
  have hmem : ∀ i (y : Fin n), y ∈ rays i ↔ y.1 ∈ V(P i) := fun i y => by
    rw [WallOfHeight.mem_graphWalkToFinList_iff, support_walkMono, (hw i).2.1]
    rfl
  have hnd : ∀ i, (rays i).Nodup := fun i => by
    apply WallOfHeight.nodup_graphWalkToFinList_of_isSimple
    change (walkMono (hle i) (w i)).support.Nodup
    rw [support_walkMono]
    exact (hw i).1
  have hcu : ∀ i, (⟨v, hv⟩ : Fin n) ≠ u' i := fun i h =>
    (hP i).2.1 (by rw [← hu'eq i, ← h])
  have hPH : ∀ i, V(P i) ∩ V(H.graph) ⊆ {v, u i} := fun i => (hP i).2.2.2.1
  refine ⟨⟨v, hv⟩, rays, fun i => ?_, fun i j hij y hyi hyj => ?_,
    fun i j hij a b ha hb => ?_⟩
  · refine ⟨hne i, hhead i, ?_, hnd i,
      WallOfHeight.isSimpleWalkList_graphWalkToFinList (w' i) hv ?_, ?_, ?_, ?_⟩
    · apply WallOfHeight.two_le_length_of_ne_head_getLast (hne i)
      rw [hhead i, hlast i]
      exact hcu i
    · change (walkMono (hle i) (w i)).support.Nodup
      rw [support_walkMono]
      exact (hw i).1
    · rw [hlast i]
      exact hu'W i
    · intro y hy hyW
      obtain ⟨hyh, hyl⟩ := ne_head_and_ne_getLast (hne i) (hnd i) hy
      have hyP : y.1 ∈ V(P i) :=
        (hmem i y).mp (List.drop_subset 1 _ (List.dropLast_subset _ hy))
      have hyH : y.1 ∈ V(H.graph) := by
        rw [hHV]
        exact (mem_toNatSet_iff _ _).mpr hyW
      rcases hPH i ⟨hyP, hyH⟩ with h | h
      · exact hyh (by rw [hhead i]; exact Fin.ext h)
      · exact hyl (by rw [hlast i]; exact Fin.ext (h.trans (hu'eq i).symm))
    · intro a b hab hwall
      obtain ⟨e, hew, hlink⟩ := exists_edge_of_mem_zip (w' i) hv hab
      have heP : e ∈ E(P i) := by
        rw [(hw i).2.2]
        change e ∈ (walkMono (hle i) (w i)).edges at hew
        rw [edges_walkMono] at hew
        exact hew
      have heH : e ∉ E(H.graph) := fun h => Set.disjoint_left.mp (hP i).2.2.2.2 heP h
      have hekept : e ∈ keptEdges G₀ H.graph := ((hP i).1.1.edgeSet_mono heP).2
      have hadj := WallOfHeight.isSimpleWalkList_adj_of_mem_zip
        (WallOfHeight.isSimpleWalkList_graphWalkToFinList (w' i) hv (by
          change (walkMono (hle i) (w i)).support.Nodup
          rw [support_walkMono]
          exact (hw i).1)) hab
      rcases hekept with h | h
      · exact heH h
      · exact h a.1 b.1 hlink (fun h' => hadj.ne (Fin.ext h'))
          (W.exists_isLink_toGMWall_of_isWallEdge_s9 h2 he hW hwall)
  · have hy : y.1 ∈ V(P i) ∩ V(P j) := ⟨(hmem i y).mp hyi, (hmem j y).mp hyj⟩
    rw [hPP i j hij] at hy
    exact Fin.ext hy
  · rw [List.getLast?_eq_some_getLast (hne i), hlast i, Option.some.injEq] at ha
    rw [List.getLast?_eq_some_getLast (hne j), hlast j, Option.some.injEq] at hb
    subst ha hb
    rw [← W.toDrawnGMWall_dist_eq_brickDist h2 he hW (hu'W i) (hu'W j), hu'eq i, hu'eq j]
    exact hdist i j hij

/-- **Graph Minors XIII, (9.2), the output exists** (page 99): "For any $l \ge 3$, and
$m, p \ge 0$, there exist $k, r \ge 0$ such that the following holds. Let $H$ be a wall with
distance function $d$ in a graph $G$, and let $H_1, \dots, H_k$ be non-dividing subwalls of $H$,
with $$d(H_i, H_j) \ge r \quad (1 \le i < j \le k).$$ Then either there is an $(l, m)$-star over
$H$ or $G$ has a $K_p$-minor." Here it is stated on the input and output formats of the algorithm
of (9.2): every `x : Alg92Input l m p h k r` has an output `out` with `IsAlg92Output l m p x out`.
It follows from `GM13.theorem_9_2_proof`. -/
theorem exists_isAlg92Output (l m p : ℕ) (hl : 3 ≤ l) :
    ∃ k r : ℕ, ∀ (h : ℕ) (x : Alg92Input l m p h k r),
      ∃ out : List ℕ, IsAlg92Output l m p x out := by
  obtain ⟨k, r, h92⟩ := GM13.theorem_9_2_proof.{0, 0} l m p hl
  refine ⟨k, r, fun h x => ?_⟩
  obtain ⟨h2, he, hW⟩ := x.hW_valid
  set G₀ := x.G.toGMDigraph.toGraph with hG₀
  set H := x.W.toDrawnGMWall h2 he hW with hH
  have hsub : ∀ a, (x.W_sub a).IsSubwallOf x.W := fun a => (x.hnondiv a).1
  let Hs : Fin k → GM13.Wall ℕ (ℕ × ℕ × ℕ) := fun a => x.W.toGMSubwallOf h2 he hW (hsub a)
  have hHG₀ : GM13.IsWallIn G₀ H.toWall := x.W.isWallIn_toGMWall h2 he hW
  have hHG₁ : GM13.IsWallIn (G₀.restrict (keptEdges G₀ H.graph)) H.toWall :=
    le_restrict_of_le hHG₀ Set.subset_union_left
  have hnd : ∀ a, GM13.IsNonDividingSubwall (G₀.restrict (keptEdges G₀ H.graph)) H.toWall
      (Hs a) := fun a =>
    isNonDividingSubwall_restrict
      ((x.W.isNonDividingSubwall_iff_toGMSubwallOf h2 he hW (hsub a)).mp (x.hnondiv a))
  have hd : ∀ a b : Fin k, a ≠ b → r ≤ GM13.wallSubgraphDist H (Hs a).graph (Hs b).graph :=
    fun a b hab => x.W.le_wallSubgraphDist_of_le_brickDist h2 he hW (hsub a) (hsub b)
      (x.hdist a b hab)
  rcases h92 (G₀.restrict (keptEdges G₀ H.graph)) H Hs (x.W.isFigure1_toDrawnGMWall h2 he hW)
      hHG₁ hnd hd with ⟨S, v, hstar⟩ | hmod
  · obtain ⟨c, rays, hrays, hdisj, hfar⟩ := exists_rays_of_isLMStarOver x.W h2 he hW hstar
    exact ⟨_, Or.inl ⟨c, rays, rfl, hrays, hdisj, hfar⟩⟩
  · obtain ⟨K, hK⟩ := isCliqueModel_of_hasGraphModel x.G
      (GM13.HasGraphModel.mono_right Graph.restrict_le hmod)
    exact ⟨_, Or.inr ⟨K, rfl, hK⟩⟩

end Alg92

end GraphMinor.Compute
