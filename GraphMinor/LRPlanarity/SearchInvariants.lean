module

public import GraphMinor.LRPlanarity.Statements
import Mathlib.Data.List.Chain

/-!
# Invariants of the explicit-frame depth-first search

This file establishes the array, stack, ancestor, and edge-record invariants of
`addEdge`, `finishEdge`, and `searchFrames` from `GraphMinor/LRPlanarity/Algorithm.lean`,
following Part I, Section 1 of `docs/planarity/planarity_test.tex`.
-/

@[expose] public section

namespace GraphMinor.LRPlanarity

open Classical

/-! ### Basic properties of `Forest.IsDFS` and `Forest.Ancestor` -/

theorem Forest.Ancestor.refl {N : ℕ} (T : Forest N) (u : Fin N) : T.Ancestor u u :=
  Relation.ReflTransGen.refl

theorem Forest.Ancestor.trans {N : ℕ} {T : Forest N} {u v w : Fin N}
    (huv : T.Ancestor u v) (hvw : T.Ancestor v w) : T.Ancestor u w :=
  Relation.ReflTransGen.trans huv hvw

theorem Forest.Ancestor.of_parent {N : ℕ} {T : Forest N} {u v : Fin N}
    (h : T.parent v = some u) : T.Ancestor u v :=
  Relation.ReflTransGen.single h

theorem Forest.depth_le_of_ancestor {N : ℕ} {T : Forest N} {u v : Fin N}
    (hstep : ∀ x y : Fin N, T.parent y = some x → T.depth y = T.depth x + 1)
    (h : T.Ancestor u v) : T.depth u ≤ T.depth v := by
  induction h with
  | refl => exact le_rfl
  | @tail b c _ hbc ih =>
    have hcd := hstep b c hbc
    omega

theorem Forest.eq_of_ancestor_of_depth_le {N : ℕ} {T : Forest N} {u v : Fin N}
    (hstep : ∀ x y : Fin N, T.parent y = some x → T.depth y = T.depth x + 1)
    (h : T.Ancestor u v) (hd : T.depth v ≤ T.depth u) : u = v := by
  induction h with
  | refl => rfl
  | @tail b c hab hbc _ =>
    have hdb := Forest.depth_le_of_ancestor hstep hab
    have hdc := hstep b c hbc
    omega

theorem Forest.depth_lt_of_ancestor_of_ne {N : ℕ} {T : Forest N} {u v : Fin N}
    (hstep : ∀ x y : Fin N, T.parent y = some x → T.depth y = T.depth x + 1)
    (h : T.Ancestor u v) (hne : u ≠ v) : T.depth u < T.depth v := by
  have hle := Forest.depth_le_of_ancestor hstep h
  rcases Nat.eq_or_lt_of_le hle with heq | hlt
  · exact absurd (Forest.eq_of_ancestor_of_depth_le hstep h (by omega)) hne
  · exact hlt

theorem Forest.Ancestor.mono {N : ℕ} {T₁ T₂ : Forest N} {u v : Fin N}
    (h : ∀ x y : Fin N, T₁.parent y = some x → T₂.parent y = some x)
    (hanc : T₁.Ancestor u v) : T₂.Ancestor u v := by
  induction hanc with
  | refl => exact Relation.ReflTransGen.refl
  | @tail b c _ hbc ih => exact Relation.ReflTransGen.tail ih (h b c hbc)

/-! ### Array and `finishEdge` / `addEdge` helper lemmas -/

theorem getElem?_join_set! {α : Type*} (a : Array (Option α)) (w : ℕ) (val : Option α)
    (hw : w < a.size) (v : ℕ) :
    ((a.set! w val)[v]?).join = if v = w then val else (a[v]?).join := by
  have hsize : (a.set! w val).size = a.size := by simp
  by_cases hvw : v = w
  · subst hvw
    simp only [↓reduceIte]
    rw [Array.getElem?_eq_getElem (by omega)]
    simp [Array.set!, Array.setIfInBounds, hw]
  · simp only [hvw, ↓reduceIte]
    by_cases hv : v < a.size
    · rw [Array.getElem?_eq_getElem (by omega), Array.getElem?_eq_getElem hv]
      simp [Array.set!, Array.setIfInBounds, hw, Array.getElem_set, Ne.symm hvw]
    · rw [Array.getElem?_eq_none (by omega), Array.getElem?_eq_none (by omega)]

theorem getElem?_join_eq_none_of_ge {α : Type*} (a : Array (Option α)) {v : ℕ}
    (hv : a.size ≤ v) : (a[v]?).join = none := by
  rw [Array.getElem?_eq_none hv]
  rfl

theorem getElem?_join_initialSearch_depth (n v : ℕ) :
    ((initialSearch n).depth[v]?).join = none := by
  unfold initialSearch
  by_cases hv : v < n
  · rw [Array.getElem?_eq_getElem (by simp [hv])]
    simp
  · rw [Array.getElem?_eq_none (by simp; omega)]
    rfl

theorem getElem?_join_initialSearch_parent (n v : ℕ) :
    ((initialSearch n).parent[v]?).join = none := by
  unfold initialSearch
  by_cases hv : v < n
  · rw [Array.getElem?_eq_getElem (by simp [hv])]
    simp
  · rw [Array.getElem?_eq_none (by simp; omega)]
    rfl

theorem getElem?_join_initialSearch_parentEdge (n v : ℕ) :
    ((initialSearch n).parentEdge[v]?).join = none := by
  unfold initialSearch
  by_cases hv : v < n
  · rw [Array.getElem?_eq_getElem (by simp [hv])]
    simp
  · rw [Array.getElem?_eq_none (by simp; omega)]
    rfl

@[simp]
theorem finishEdge_depth (s : Search) (i : ℕ) : (finishEdge s i).depth = s.depth := by
  unfold finishEdge Id.run
  dsimp only
  split <;> rfl

@[simp]
theorem finishEdge_parent (s : Search) (i : ℕ) : (finishEdge s i).parent = s.parent := by
  unfold finishEdge Id.run
  dsimp only
  split <;> rfl

@[simp]
theorem finishEdge_parentEdge (s : Search) (i : ℕ) :
    (finishEdge s i).parentEdge = s.parentEdge := by
  unfold finishEdge Id.run
  dsimp only
  split <;> rfl

@[simp]
theorem finishEdge_postorder (s : Search) (i : ℕ) :
    (finishEdge s i).postorder = s.postorder := by
  unfold finishEdge Id.run
  dsimp only
  split <;> rfl

@[simp]
theorem finishEdge_forest (s : Search) (i N : ℕ) :
    (finishEdge s i).forest N = s.forest N := by
  simp [Search.forest]

@[simp]
theorem finishEdge_edges_size (s : Search) (i : ℕ) :
    (finishEdge s i).edges.size = s.edges.size := by
  unfold finishEdge Id.run
  dsimp only
  split
  · change ((s.edges.set! i _).set! _ _).size = s.edges.size
    simp
  · change (s.edges.set! i _).size = s.edges.size
    simp

theorem getElem!_set!_EdgeRecord (edges : Array EdgeRecord) (idx j : ℕ) (e : EdgeRecord)
    (hidx : idx < edges.size) :
    (edges.set! idx e)[j]! = if j = idx then e else edges[j]! := by
  by_cases hj : j = idx
  · subst hj
    simp [Array.set!, Array.setIfInBounds, hidx]
  · simp only [hj, ↓reduceIte]
    by_cases hlt : j < edges.size
    · simp [Array.set!, Array.setIfInBounds, hidx, hlt, Ne.symm hj]
    · simp [hlt]

private theorem set!_edges_source (edges : Array EdgeRecord) (k j : ℕ) (e : EdgeRecord)
    (he : e.source = (edges[k]!).source) :
    ((edges.set! k e)[j]!).source = (edges[j]!).source := by
  by_cases hk : k < edges.size
  · rw [getElem!_set!_EdgeRecord edges k j e hk]
    split_ifs with hjk
    · subst hjk; exact he
    · rfl
  · have hset : edges.set! k e = edges := by
      simp [Array.set!, Array.setIfInBounds, hk]
    rw [hset]

private theorem set!_edges_target (edges : Array EdgeRecord) (k j : ℕ) (e : EdgeRecord)
    (he : e.target = (edges[k]!).target) :
    ((edges.set! k e)[j]!).target = (edges[j]!).target := by
  by_cases hk : k < edges.size
  · rw [getElem!_set!_EdgeRecord edges k j e hk]
    split_ifs with hjk
    · subst hjk; exact he
    · rfl
  · have hset : edges.set! k e = edges := by
      simp [Array.set!, Array.setIfInBounds, hk]
    rw [hset]

private theorem set!_edges_tree (edges : Array EdgeRecord) (k j : ℕ) (e : EdgeRecord)
    (he : e.tree = (edges[k]!).tree) :
    ((edges.set! k e)[j]!).tree = (edges[j]!).tree := by
  by_cases hk : k < edges.size
  · rw [getElem!_set!_EdgeRecord edges k j e hk]
    split_ifs with hjk
    · subst hjk; exact he
    · rfl
  · have hset : edges.set! k e = edges := by
      simp [Array.set!, Array.setIfInBounds, hk]
    rw [hset]

theorem finishEdge_edges_source (s : Search) (i j : ℕ) :
    ((finishEdge s i).edges[j]!).source = (s.edges[j]!).source := by
  unfold finishEdge Id.run
  dsimp only
  split
  · next p hp =>
    change (((s.edges.set! i _).set! p _)[j]!).source = (s.edges[j]!).source
    rw [set!_edges_source, set!_edges_source] <;> rfl
  · change ((s.edges.set! i _)[j]!).source = (s.edges[j]!).source
    rw [set!_edges_source]
    rfl

theorem finishEdge_edges_target (s : Search) (i j : ℕ) :
    ((finishEdge s i).edges[j]!).target = (s.edges[j]!).target := by
  unfold finishEdge Id.run
  dsimp only
  split
  · next p hp =>
    change (((s.edges.set! i _).set! p _)[j]!).target = (s.edges[j]!).target
    rw [set!_edges_target, set!_edges_target] <;> rfl
  · change ((s.edges.set! i _)[j]!).target = (s.edges[j]!).target
    rw [set!_edges_target]
    rfl

theorem finishEdge_edges_tree (s : Search) (i j : ℕ) :
    ((finishEdge s i).edges[j]!).tree = (s.edges[j]!).tree := by
  unfold finishEdge Id.run
  dsimp only
  split
  · next p hp =>
    change (((s.edges.set! i _).set! p _)[j]!).tree = (s.edges[j]!).tree
    rw [set!_edges_tree, set!_edges_tree] <;> rfl
  · change ((s.edges.set! i _)[j]!).tree = (s.edges[j]!).tree
    rw [set!_edges_tree]
    rfl

theorem getElem!_push_EdgeRecord (edges : Array EdgeRecord) (e : EdgeRecord) (j : ℕ)
    (hj : j ≤ edges.size) :
    (edges.push e)[j]! = if j = edges.size then e else edges[j]! := by
  by_cases hjeq : j = edges.size
  · subst hjeq
    simp
  · have hjlt : j < edges.size := by omega
    simp only [hjeq, ↓reduceIte]
    have hjlt' : j < (edges.push e).size := by simp; omega
    rw [getElem!_pos (edges.push e) j hjlt', getElem!_pos edges j hjlt, Array.getElem_push_lt hjlt]

@[simp]
theorem addEdge_fst_depth (s : Search) (v w : ℕ) (tree : Bool) :
    (addEdge s v w tree).1.depth = s.depth := rfl

@[simp]
theorem addEdge_fst_parent (s : Search) (v w : ℕ) (tree : Bool) :
    (addEdge s v w tree).1.parent = s.parent := rfl

@[simp]
theorem addEdge_fst_parentEdge (s : Search) (v w : ℕ) (tree : Bool) :
    (addEdge s v w tree).1.parentEdge = s.parentEdge := rfl

@[simp]
theorem addEdge_fst_postorder (s : Search) (v w : ℕ) (tree : Bool) :
    (addEdge s v w tree).1.postorder = s.postorder := rfl

@[simp]
theorem addEdge_fst_forest (s : Search) (v w : ℕ) (tree : Bool) (N : ℕ) :
    (addEdge s v w tree).1.forest N = s.forest N := rfl

@[simp]
theorem addEdge_fst_edges_size (s : Search) (v w : ℕ) (tree : Bool) :
    (addEdge s v w tree).1.edges.size = s.edges.size + 1 := by
  simp [addEdge]

@[simp]
theorem addEdge_snd (s : Search) (v w : ℕ) (tree : Bool) :
    (addEdge s v w tree).2 = s.edges.size := rfl

theorem addEdge_edges_source (s : Search) (v w : ℕ) (tree : Bool) (i : ℕ) (hi : i ≤ s.edges.size) :
    ((addEdge s v w tree).1.edges[i]!).source = if i = s.edges.size then v else (s.edges[i]!).source := by
  dsimp only [addEdge]
  rw [getElem!_push_EdgeRecord s.edges _ i hi]
  split_ifs <;> rfl

theorem addEdge_edges_target (s : Search) (v w : ℕ) (tree : Bool) (i : ℕ) (hi : i ≤ s.edges.size) :
    ((addEdge s v w tree).1.edges[i]!).target = if i = s.edges.size then w else (s.edges[i]!).target := by
  dsimp only [addEdge]
  rw [getElem!_push_EdgeRecord s.edges _ i hi]
  split_ifs <;> rfl

theorem addEdge_edges_tree (s : Search) (v w : ℕ) (tree : Bool) (i : ℕ) (hi : i ≤ s.edges.size) :
    ((addEdge s v w tree).1.edges[i]!).tree = if i = s.edges.size then tree else (s.edges[i]!).tree := by
  dsimp only [addEdge]
  rw [getElem!_push_EdgeRecord s.edges _ i hi]
  split_ifs <;> rfl

/-! ### Adjacency array helper lemmas -/

theorem adjArray_size {N : ℕ} (lists : Fin N → List ℕ) :
    (List.ofFn lists).toArray.size = N := by
  simp

theorem adjArray_getElem! {N : ℕ} (lists : Fin N → List ℕ) (v : ℕ) (hv : v < N) :
    (List.ofFn lists).toArray[v]! = lists ⟨v, hv⟩ := by
  have hv' : v < (List.ofFn lists).toArray.size := by simp [hv]
  rw [getElem!_pos (List.ofFn lists).toArray v hv']
  simp

theorem adj_mem_lt {N : ℕ} {G : SimpleGraph (Fin N)}
    {lists : Fin N → List ℕ} (hAdj : Compute.IsAdjListFamily G lists)
    {v w : ℕ} (hv : v < N) (hw : w ∈ (List.ofFn lists).toArray[v]!) : w < N := by
  rw [adjArray_getElem! lists v hv] at hw
  exact (hAdj ⟨v, hv⟩).1 w hw

theorem adj_nodup {N : ℕ} {G : SimpleGraph (Fin N)}
    {lists : Fin N → List ℕ} (hAdj : Compute.IsAdjListFamily G lists)
    {v : ℕ} (hv : v < N) : ((List.ofFn lists).toArray[v]!).Nodup := by
  rw [adjArray_getElem! lists v hv]
  exact (hAdj ⟨v, hv⟩).2.1

theorem adj_mem_iff {N : ℕ} {G : SimpleGraph (Fin N)}
    {lists : Fin N → List ℕ} (hAdj : Compute.IsAdjListFamily G lists)
    {u v : ℕ} (hu : u < N) (hv : v < N) :
    v ∈ (List.ofFn lists).toArray[u]! ↔ G.Adj ⟨u, hu⟩ ⟨v, hv⟩ := by
  rw [adjArray_getElem! lists u hu]
  exact (hAdj ⟨u, hu⟩).2.2.2 ⟨v, hv⟩

theorem adj_ne_of_mem {N : ℕ} {G : SimpleGraph (Fin N)}
    {lists : Fin N → List ℕ} (hAdj : Compute.IsAdjListFamily G lists)
    {v w : ℕ} (hv : v < N) (hw : w ∈ (List.ofFn lists).toArray[v]!) : w ≠ v := by
  have hw_lt := adj_mem_lt hAdj hv hw
  have hadj := (adj_mem_iff hAdj hv hw_lt).mp hw
  intro heq
  subst heq
  exact G.ne_of_adj hadj rfl

/-! ### `Visited`, `Scanned`, `workDone`, and `DFSInv` -/

/-- A vertex is visited when its depth entry is `some _`. -/
def Search.Visited (s : Search) (v : ℕ) : Prop :=
  (s.depth[v]?.join).isSome = true

theorem Search.not_visited_iff (s : Search) (v : ℕ) :
    ¬ s.Visited v ↔ (s.depth[v]?.join).isNone = true := by
  simp [Search.Visited, Option.isNone_iff_eq_none, Option.isSome_iff_ne_none]

theorem Search.visited_iff_ne_none (s : Search) (v : ℕ) :
    s.Visited v ↔ s.depth[v]?.join ≠ none := by
  simp [Search.Visited, Option.isSome_iff_ne_none]

@[simp]
theorem Search.visited_finishEdge (s : Search) (i v : ℕ) :
    (finishEdge s i).Visited v ↔ s.Visited v := by
  simp [Search.Visited]

@[simp]
theorem addEdge_fst_Visited (s : Search) (v w : ℕ) (tree : Bool) (u : ℕ) :
    (addEdge s v w tree).1.Visited u ↔ s.Visited u := Iff.rfl

/-- Incidence `(v, k)` has been scanned if `v` is completed or `f ∈ stack` has `f.vertex = v`
and `k < f.next`. -/
def Scanned (N : ℕ) (lists : Fin N → List ℕ) (s : Search) (stack : List Frame)
    (v k : ℕ) : Prop :=
  v < N ∧ k < ((List.ofFn lists).toArray[v]!).length ∧
    (v ∈ s.postorder ∨ ∃ f ∈ stack, f.vertex = v ∧ k < f.next)

@[simp]
theorem scanned_finishEdge (N : ℕ) (lists : Fin N → List ℕ) (s : Search)
    (stack : List Frame) (i v k : ℕ) :
    Scanned N lists (finishEdge s i) stack v k ↔ Scanned N lists s stack v k := by
  simp [Scanned]

/-- Total number of frame steps (incidence scans and vertex completions) performed so far. -/
def workDone (adj : Array (List ℕ)) (s : Search) (stack : List Frame) : ℕ :=
  (s.postorder.map (fun u => (adj[u]!).length + 1)).sum + (stack.map Frame.next).sum

@[simp]
theorem workDone_finishEdge (adj : Array (List ℕ)) (s : Search) (stack : List Frame) (i : ℕ) :
    workDone adj (finishEdge s i) stack = workDone adj s stack := by
  simp [workDone]

/-- Full state invariant maintained by `searchFrames` and the outer loop of `depthFirstSearch`. -/
structure DFSInv (N : ℕ) (G : SimpleGraph (Fin N)) (lists : Fin N → List ℕ)
    (s : Search) (stack : List Frame) : Prop where
  depth_size : s.depth.size = N
  parent_size : s.parent.size = N
  parentEdge_size : s.parentEdge.size = N
  active_lt : ∀ v ∈ stack.map Frame.vertex, v < N
  postorder_lt : ∀ v ∈ s.postorder, v < N
  nodup_verts : (stack.map Frame.vertex ++ s.postorder).Nodup
  frame_next_le : ∀ f ∈ stack, f.next ≤ ((List.ofFn lists).toArray[f.vertex]!).length
  visited_iff : ∀ v, s.Visited v ↔ v ∈ stack.map Frame.vertex ∨ v ∈ s.postorder
  unvisited_none : ∀ v, ¬ s.Visited v →
    s.parent[v]?.join = none ∧ s.parentEdge[v]?.join = none
  root_depth : ∀ v : Fin N, s.Visited v.val → s.parent[v.val]?.join = none →
    (s.forest N).depth v = 0 ∧ s.parentEdge[v.val]?.join = none
  parent_spec : ∀ v : Fin N, ∀ u : ℕ, s.parent[v.val]?.join = some u →
    ∃ hu : u < N, s.Visited v.val ∧ s.Visited u ∧
      G.Adj ⟨u, hu⟩ v ∧
      (s.forest N).depth v = (s.forest N).depth ⟨u, hu⟩ + 1 ∧
      ∃ k, Scanned N lists s stack u k ∧ ((List.ofFn lists).toArray[u]!)[k]! = v.val
  stack_chain : stack.IsChain (fun f₁ f₂ => s.parent[f₁.vertex]?.join = some f₂.vertex)
  active_parent_mem : ∀ v ∈ stack.map Frame.vertex, ∀ u,
    s.parent[v]?.join = some u → u ∈ stack.map Frame.vertex
  postorder_order : s.postorder.Pairwise (fun u w => s.parent[u]?.join ≠ some w)
  scanned_visited : ∀ v k, Scanned N lists s stack v k →
    s.Visited (((List.ofFn lists).toArray[v]!)[k]!)
  completed_adj : ∀ u v : Fin N, u.val ∈ s.postorder → G.Adj u v →
    (v.val ∈ stack.map Frame.vertex → (s.forest N).Ancestor v u) ∧
    (v.val ∈ s.postorder → (s.forest N).Ancestor u v ∨ (s.forest N).Ancestor v u)
  edges_valid : ∀ i < s.edges.size,
    let r := s.edges[i]!
    ∃ (hs : r.source < N) (ht : r.target < N),
      s.Visited r.source ∧ s.Visited r.target ∧
      (∃ k, Scanned N lists s stack r.source k ∧
        ((List.ofFn lists).toArray[r.source]!)[k]! = r.target) ∧
      (if r.tree then
        s.parent[r.target]?.join = some r.source ∧ s.parentEdge[r.target]?.join = some i
       else
        s.parent[r.source]?.join ≠ some r.target ∧
          (s.forest N).depth ⟨r.target, ht⟩ < (s.forest N).depth ⟨r.source, hs⟩)
  parentEdge_iff : ∀ w < N, ∀ i,
    s.parentEdge[w]?.join = some i ↔
      i < s.edges.size ∧ (s.edges[i]!).tree = true ∧ (s.edges[i]!).target = w
  parent_iff_edge : ∀ w < N, ∀ v,
    s.parent[w]?.join = some v ↔
      ∃ i < s.edges.size, (s.edges[i]!).tree = true ∧
        (s.edges[i]!).source = v ∧ (s.edges[i]!).target = w
  edges_inj : ∀ i < s.edges.size, ∀ j < s.edges.size,
    (s.edges[i]!).source = (s.edges[j]!).source →
    (s.edges[i]!).target = (s.edges[j]!).target → i = j
  scanned_edge_exists : ∀ v k, Scanned N lists s stack v k →
    ∀ (hv : v < N),
    let w := ((List.ofFn lists).toArray[v]!)[k]!
    ∀ (hw : w < N),
    (s.parent[w]?.join = some v ∨
      (s.parent[v]?.join ≠ some w ∧
        (s.forest N).depth ⟨w, hw⟩ < (s.forest N).depth ⟨v, hv⟩)) →
    ∃ i < s.edges.size, (s.edges[i]!).source = v ∧ (s.edges[i]!).target = w

theorem DFSInv.finishEdge {N : ℕ} {G : SimpleGraph (Fin N)} {lists : Fin N → List ℕ}
    {s : Search} {stack : List Frame} (h : DFSInv N G lists s stack) (idx : ℕ) :
    DFSInv N G lists (GraphMinor.LRPlanarity.finishEdge s idx) stack where
  depth_size := by simp [h.depth_size]
  parent_size := by simp [h.parent_size]
  parentEdge_size := by simp [h.parentEdge_size]
  active_lt := h.active_lt
  postorder_lt := by simpa using h.postorder_lt
  nodup_verts := by simpa using h.nodup_verts
  frame_next_le := h.frame_next_le
  visited_iff v := by simpa using h.visited_iff v
  unvisited_none v hv := by simpa using h.unvisited_none v (by simpa using hv)
  root_depth v hv hp := by simpa using h.root_depth v (by simpa using hv) (by simpa using hp)
  parent_spec v u hp := by simpa using h.parent_spec v u (by simpa using hp)
  stack_chain := by simpa using h.stack_chain
  active_parent_mem v hv u hp := h.active_parent_mem v hv u (by simpa using hp)
  postorder_order := by simpa using h.postorder_order
  scanned_visited v k hsc := by simpa using h.scanned_visited v k (by simpa using hsc)
  completed_adj u v hu hadj := by simpa using h.completed_adj u v (by simpa using hu) hadj
  edges_valid i hi := by
    rw [finishEdge_edges_size] at hi
    simp only [finishEdge_edges_source, finishEdge_edges_target, finishEdge_edges_tree,
      Search.visited_finishEdge, scanned_finishEdge, finishEdge_parent, finishEdge_parentEdge,
      finishEdge_forest]
    exact h.edges_valid i hi
  parentEdge_iff w hw i := by
    simp only [finishEdge_parentEdge, finishEdge_edges_size, finishEdge_edges_tree,
      finishEdge_edges_target]
    exact h.parentEdge_iff w hw i
  parent_iff_edge w hw v := by
    simp only [finishEdge_parent, finishEdge_edges_size, finishEdge_edges_tree,
      finishEdge_edges_source, finishEdge_edges_target]
    exact h.parent_iff_edge w hw v
  edges_inj i hi j hj hs ht := by
    rw [finishEdge_edges_size] at hi hj
    rw [finishEdge_edges_source, finishEdge_edges_source] at hs
    rw [finishEdge_edges_target, finishEdge_edges_target] at ht
    exact h.edges_inj i hi j hj hs ht
  scanned_edge_exists v k hsc hv hw hcond := by
    simp only [scanned_finishEdge] at hsc
    simp only [finishEdge_parent, finishEdge_forest] at hcond
    simp only [finishEdge_edges_size, finishEdge_edges_source, finishEdge_edges_target]
    exact h.scanned_edge_exists v k hsc hv hw hcond

/-! ### Consequences of `DFSInv` -/

theorem DFSInv.forest_parent_some_iff {N : ℕ} {G : SimpleGraph (Fin N)} {lists : Fin N → List ℕ}
    {s : Search} {stack : List Frame} (h : DFSInv N G lists s stack) (u v : Fin N) :
    (s.forest N).parent v = some u ↔ s.parent[v.val]?.join = some u.val := by
  simp only [Search.forest]
  cases hp : s.parent[v.val]?.join with
  | none => simp
  | some p =>
    obtain ⟨hp_lt, _⟩ := h.parent_spec v p hp
    simp [hp_lt, Fin.ext_iff]

theorem DFSInv.forest_parent_none_iff {N : ℕ} {G : SimpleGraph (Fin N)} {lists : Fin N → List ℕ}
    {s : Search} {stack : List Frame} (h : DFSInv N G lists s stack) (v : Fin N) :
    (s.forest N).parent v = none ↔ s.parent[v.val]?.join = none := by
  simp only [Search.forest]
  cases hp : s.parent[v.val]?.join with
  | none => simp
  | some p =>
    obtain ⟨hp_lt, _⟩ := h.parent_spec v p hp
    simp [hp_lt]

theorem DFSInv.depth_step {N : ℕ} {G : SimpleGraph (Fin N)} {lists : Fin N → List ℕ}
    {s : Search} {stack : List Frame} (h : DFSInv N G lists s stack) (u v : Fin N)
    (hp : (s.forest N).parent v = some u) :
    (s.forest N).depth v = (s.forest N).depth u + 1 := by
  rw [h.forest_parent_some_iff] at hp
  obtain ⟨_, _, _, _, hd, _⟩ := h.parent_spec v u.val hp
  exact hd

private theorem isChain_ancestor_aux {N : ℕ} {G : SimpleGraph (Fin N)} {lists : Fin N → List ℕ}
    {s : Search} {stack : List Frame} (h : DFSInv N G lists s stack) :
    ∀ (l : List Frame) (f : Frame),
      (∀ g ∈ f :: l, g.vertex < N) →
      (f :: l).IsChain (fun f₁ f₂ => s.parent[f₁.vertex]?.join = some f₂.vertex) →
      ∀ u ∈ l.map Frame.vertex, ∀ (hu : u < N) (hf : f.vertex < N),
        (s.forest N).Ancestor ⟨u, hu⟩ ⟨f.vertex, hf⟩
  | [], _, _, _, _, hu_mem, _, _ => by simp at hu_mem
  | g :: rest, f, hlt, hchain, u, hu_mem, hu, hf => by
    rw [List.isChain_cons_cons] at hchain
    have hg : g.vertex < N := hlt g (by simp)
    have hfg_par : (s.forest N).parent ⟨f.vertex, hf⟩ = some ⟨g.vertex, hg⟩ :=
      (h.forest_parent_some_iff ⟨g.vertex, hg⟩ ⟨f.vertex, hf⟩).mpr hchain.1
    have hfg : (s.forest N).Ancestor ⟨g.vertex, hg⟩ ⟨f.vertex, hf⟩ :=
      Forest.Ancestor.of_parent hfg_par
    simp only [List.mem_map, List.mem_cons] at hu_mem
    rcases hu_mem with ⟨x, rfl | hx, rfl⟩
    · exact hfg
    · have hlt' : ∀ x ∈ g :: rest, x.vertex < N := fun x hx => hlt x (List.mem_cons_of_mem f hx)
      have hux : (s.forest N).Ancestor ⟨x.vertex, hu⟩ ⟨g.vertex, hg⟩ :=
        isChain_ancestor_aux h rest g hlt' hchain.2 x.vertex (List.mem_map_of_mem hx) hu hg
      exact hux.trans hfg

theorem DFSInv.ancestor_of_mem_stack_tail {N : ℕ} {G : SimpleGraph (Fin N)}
    {lists : Fin N → List ℕ} {s : Search} {f : Frame} {rest : List Frame}
    (h : DFSInv N G lists s (f :: rest))
    {u : ℕ} (hu_mem : u ∈ rest.map Frame.vertex) (hu : u < N) (hf : f.vertex < N) :
    (s.forest N).Ancestor ⟨u, hu⟩ ⟨f.vertex, hf⟩ :=
  isChain_ancestor_aux h rest f
    (fun g hg => h.active_lt g.vertex (List.mem_map_of_mem hg))
    h.stack_chain u hu_mem hu hf

theorem DFSInv.not_parent_of_mem_stack_tail {N : ℕ} {G : SimpleGraph (Fin N)}
    {lists : Fin N → List ℕ} {s : Search} {f : Frame} {rest : List Frame}
    (h : DFSInv N G lists s (f :: rest))
    {u : ℕ} (hu_mem : u ∈ rest.map Frame.vertex) :
    s.parent[u]?.join ≠ some f.vertex := by
  intro hpar
  have hu : u < N := h.active_lt u (List.mem_cons_of_mem f.vertex hu_mem)
  have hf : f.vertex < N := h.active_lt f.vertex (by simp)
  have hanc := h.ancestor_of_mem_stack_tail hu_mem hu hf
  have hle := Forest.depth_le_of_ancestor h.depth_step hanc
  have hpar' : (s.forest N).parent ⟨u, hu⟩ = some ⟨f.vertex, hf⟩ :=
    (h.forest_parent_some_iff ⟨f.vertex, hf⟩ ⟨u, hu⟩).mpr hpar
  have hstep := h.depth_step ⟨f.vertex, hf⟩ ⟨u, hu⟩ hpar'
  omega

theorem DFSInv.isDFS_of_nil {N : ℕ} {G : SimpleGraph (Fin N)} {lists : Fin N → List ℕ}
    {s : Search} (h : DFSInv N G lists s []) (hall : ∀ v < N, s.Visited v) :
    (s.forest N).IsDFS G := by
  refine ⟨?_, ?_, ?_⟩
  · intro v hp
    rw [h.forest_parent_none_iff] at hp
    exact (h.root_depth v (hall v.val v.2) hp).1
  · intro u v hp
    rw [h.forest_parent_some_iff] at hp
    obtain ⟨_, _, _, hadj, hd, _⟩ := h.parent_spec v u.val hp
    exact ⟨hadj, hd⟩
  · intro u v hadj
    have hu : u.val ∈ s.postorder := by
      have := (h.visited_iff u.val).mp (hall u.val u.2)
      simpa using this
    have hv : v.val ∈ s.postorder := by
      have := (h.visited_iff v.val).mp (hall v.val v.2)
      simpa using this
    exact (h.completed_adj u v hu hadj).2 hv

/-! ### `Scanned` transition lemmas -/

theorem scanned_pop_iff {N : ℕ} {lists : Fin N → List ℕ} {s s' : Search}
    {f : Frame} {rest : List Frame}
    (hpost : s'.postorder = f.vertex :: s.postorder)
    (hge : ((List.ofFn lists).toArray[f.vertex]!).length ≤ f.next)
    (u k : ℕ) :
    Scanned N lists s' rest u k ↔ Scanned N lists s (f :: rest) u k := by
  simp only [Scanned, hpost, List.mem_cons]
  refine and_congr_right fun _ => and_congr_right fun hk => ?_
  by_cases huf : u = f.vertex
  · subst huf
    constructor
    · intro _; exact Or.inr ⟨f, Or.inl rfl, rfl, Nat.lt_of_lt_of_le hk hge⟩
    · intro _; exact Or.inl (Or.inl rfl)
  · have hne : f.vertex ≠ u := Ne.symm huf
    simp [huf, hne]

theorem not_scanned_current {N : ℕ} {G : SimpleGraph (Fin N)} {lists : Fin N → List ℕ}
    {s : Search} {f : Frame} {rest : List Frame}
    (h : DFSInv N G lists s (f :: rest)) :
    ¬ Scanned N lists s (f :: rest) f.vertex f.next := by
  rintro ⟨_, _, hpost | ⟨g, hg, hgv, hlt⟩⟩
  · have hnodup := h.nodup_verts
    simp only [List.map_cons, List.cons_append, List.nodup_cons, List.mem_append] at hnodup
    exact hnodup.1 (Or.inr hpost)
  · rcases List.mem_cons.mp hg with rfl | hg_rest
    · exact Nat.lt_irrefl _ hlt
    · have hnodup := h.nodup_verts
      simp only [List.map_cons, List.cons_append, List.nodup_cons, List.mem_append] at hnodup
      exact hnodup.1 (Or.inl (hgv ▸ List.mem_map_of_mem hg_rest))

theorem scanned_step_iff {N : ℕ} {G : SimpleGraph (Fin N)} {lists : Fin N → List ℕ}
    {s s' : Search} {f : Frame} {rest : List Frame}
    (h : DFSInv N G lists s (f :: rest))
    (hpost : s'.postorder = s.postorder)
    (hlen : f.next < ((List.ofFn lists).toArray[f.vertex]!).length)
    (u k : ℕ) :
    Scanned N lists s' ({ f with next := f.next + 1 } :: rest) u k ↔
      (u = f.vertex ∧ k = f.next) ∨ Scanned N lists s (f :: rest) u k := by
  have hf_lt : f.vertex < N := h.active_lt f.vertex (by simp)
  simp only [Scanned, hpost, List.mem_cons]
  constructor
  · rintro ⟨hu, hk, hupost | ⟨g, hgm, hgv, hkg⟩⟩
    · exact Or.inr ⟨hu, hk, Or.inl hupost⟩
    · rcases hgm with hgf | hg
      · subst hgf
        rcases Nat.eq_or_lt_of_le (Nat.le_of_lt_succ hkg) with rfl | hlt
        · exact Or.inl ⟨hgv.symm, rfl⟩
        · exact Or.inr ⟨hu, hk, Or.inr ⟨f, Or.inl rfl, hgv, hlt⟩⟩
      · exact Or.inr ⟨hu, hk, Or.inr ⟨g, Or.inr hg, hgv, hkg⟩⟩
  · rintro (⟨rfl, rfl⟩ | ⟨hu, hk, hupost | ⟨g, hgm, hgv, hkg⟩⟩)
    · exact ⟨hf_lt, hlen, Or.inr ⟨⟨f.vertex, f.next + 1⟩, Or.inl rfl, rfl, Nat.lt_succ_self _⟩⟩
    · exact ⟨hu, hk, Or.inl hupost⟩
    · rcases hgm with hgf | hg
      · subst g
        exact ⟨hu, hk, Or.inr ⟨⟨f.vertex, f.next + 1⟩, Or.inl rfl, hgv, Nat.lt_succ_of_lt hkg⟩⟩
      · exact ⟨hu, hk, Or.inr ⟨g, Or.inr hg, hgv, hkg⟩⟩

theorem scanned_push_zero_iff {N : ℕ} {lists : Fin N → List ℕ} {s : Search}
    {stack : List Frame} (w u k : ℕ) :
    Scanned N lists s (⟨w, 0⟩ :: stack) u k ↔ Scanned N lists s stack u k := by
  simp [Scanned]

/-! ### Fuel bound via `workDone` -/

private theorem sum_map_le_of_nodup_subset (g : ℕ → ℕ) :
    ∀ (L R : List ℕ), L.Nodup → (∀ x ∈ L, x ∈ R) → (L.map g).sum ≤ (R.map g).sum
  | [], _, _, _ => by simp
  | a :: L, R, hnodup, hsub => by
    rw [List.nodup_cons] at hnodup
    have ha : a ∈ R := hsub a List.mem_cons_self
    have hperm : R.Perm (a :: R.erase a) := List.perm_cons_erase ha
    have hsumR : (R.map g).sum = g a + ((R.erase a).map g).sum := by
      rw [(hperm.map g).sum_eq, List.map_cons, List.sum_cons]
    have hsub' : ∀ x ∈ L, x ∈ R.erase a := by
      intro x hx
      have hxa : x ≠ a := fun h => hnodup.1 (h ▸ hx)
      exact (List.mem_erase_of_ne hxa).mpr (hsub x (List.mem_cons_of_mem a hx))
    have ih := sum_map_le_of_nodup_subset g L (R.erase a) hnodup.2 hsub'
    simp only [List.map_cons, List.sum_cons, hsumR]
    omega

private theorem sum_stack_next_le (adj : Array (List ℕ)) :
    ∀ (stack : List Frame),
      (∀ f ∈ stack, f.next ≤ (adj[f.vertex]!).length) →
      (stack.map Frame.next).sum ≤
        ((stack.map Frame.vertex).map (fun u => (adj[u]!).length + 1)).sum
  | [], _ => by simp
  | f :: rest, hle => by
    have hf := hle f List.mem_cons_self
    have ih := sum_stack_next_le adj rest (fun g hg => hle g (List.mem_cons_of_mem f hg))
    simp only [List.map_cons, List.sum_cons]
    omega

private theorem foldl_length_eq_sum :
    ∀ (l : List (List ℕ)) (init : ℕ),
      l.foldl (fun total x => total + x.length) init = init + (l.map List.length).sum
  | [], init => by simp
  | x :: xs, init => by
    simp only [List.foldl_cons, List.map_cons, List.sum_cons]
    rw [foldl_length_eq_sum xs (init + x.length)]
    omega

private theorem sum_range_getElem!_length (adj : Array (List ℕ)) :
    ∀ n ≤ adj.size,
      ((List.range n).map (fun u => (adj[u]!).length + 1)).sum =
        ((adj.toList.take n).map List.length).sum + n
  | 0, _ => by simp
  | n + 1, hn => by
    rw [List.range_succ, List.map_append, List.sum_append,
      sum_range_getElem!_length adj n (by omega)]
    have hlt : n < adj.toList.length := by simpa using hn
    rw [List.take_add_one, List.getElem?_eq_getElem hlt]
    have hget : adj[n]! = adj.toList[n] := by
      have hn' : n < adj.size := hn
      rw [getElem!_pos adj n hn']
      rfl
    simp only [Option.toList, List.map_append, List.sum_append, List.map_cons, List.map_nil,
      List.sum_cons, List.sum_nil, hget]
    omega

theorem DFSInv.workDone_le {N : ℕ} {G : SimpleGraph (Fin N)} {lists : Fin N → List ℕ}
    {s : Search} {stack : List Frame} (h : DFSInv N G lists s stack) :
    let adj := (List.ofFn lists).toArray
    workDone adj s stack ≤ adj.foldl (fun total l => total + l.length) 0 + adj.size := by
  intro adj
  have h1 := sum_stack_next_le adj stack h.frame_next_le
  have hwork : workDone adj s stack ≤
      (((stack.map Frame.vertex ++ s.postorder).map (fun u => (adj[u]!).length + 1)).sum) := by
    simp only [workDone, List.map_append, List.sum_append]
    omega
  have hsub : ∀ x ∈ stack.map Frame.vertex ++ s.postorder, x ∈ List.range adj.size := by
    intro x hx
    rw [List.mem_range, adjArray_size]
    rcases List.mem_append.mp hx with hx | hx
    · exact h.active_lt x hx
    · exact h.postorder_lt x hx
  have h2 := sum_map_le_of_nodup_subset (fun u => (adj[u]!).length + 1)
    (stack.map Frame.vertex ++ s.postorder) (List.range adj.size) h.nodup_verts hsub
  have h3 := sum_range_getElem!_length adj adj.size le_rfl
  rw [ ← Array.foldl_toList, foldl_length_eq_sum]
  have htake : adj.toList.take adj.size = adj.toList := List.take_length
  rw [htake] at h3
  omega

/-! ### Initialization and root push for `DFSInv` -/

theorem DFSInv.init (N : ℕ) (G : SimpleGraph (Fin N)) (lists : Fin N → List ℕ) :
    DFSInv N G lists (initialSearch N) [] where
  depth_size := by simp [initialSearch]
  parent_size := by simp [initialSearch]
  parentEdge_size := by simp [initialSearch]
  active_lt := by simp
  postorder_lt := by simp [initialSearch]
  nodup_verts := by simp [initialSearch]
  frame_next_le := by simp
  visited_iff v := by
    rw [Search.Visited, getElem?_join_initialSearch_depth]
    simp [initialSearch]
  unvisited_none v _ :=
    ⟨getElem?_join_initialSearch_parent N v, getElem?_join_initialSearch_parentEdge N v⟩
  root_depth v hv _ := by
    exfalso
    simp [Search.Visited, getElem?_join_initialSearch_depth] at hv
  parent_spec v u hp := by
    rw [getElem?_join_initialSearch_parent] at hp
    nomatch hp
  stack_chain := List.isChain_nil
  active_parent_mem := by simp
  postorder_order := by simp [initialSearch]
  scanned_visited v k hsc := by
    exfalso
    rcases hsc with ⟨_, _, h1 | ⟨_, h2, _⟩⟩
    · simp [initialSearch] at h1
    · simp at h2
  completed_adj u v hu _ := by
    exfalso
    simp [initialSearch] at hu
  edges_valid i hi := by
    exfalso
    simp [initialSearch] at hi
  parentEdge_iff w _ i := by
    rw [getElem?_join_initialSearch_parentEdge]
    simp [initialSearch]
  parent_iff_edge w _ v := by
    rw [getElem?_join_initialSearch_parent]
    simp [initialSearch]
  edges_inj i hi := by
    exfalso
    simp [initialSearch] at hi
  scanned_edge_exists v k hsc := by
    exfalso
    rcases hsc with ⟨_, _, h1 | ⟨_, h2, _⟩⟩
    · simp [initialSearch] at h1
    · simp at h2

theorem DFSInv.push_root {N : ℕ} {G : SimpleGraph (Fin N)} {lists : Fin N → List ℕ}
    {s : Search} (hAdj : Compute.IsAdjListFamily G lists)
    (h : DFSInv N G lists s []) {root : ℕ} (hroot : root < N)
    (hunvis : (s.depth[root]?.join).isNone = true) :
    let s₀ : Search := { s with depth := s.depth.set! root (some 0) }
    DFSInv N G lists s₀ [⟨root, 0⟩] := by
  intro s₀
  have hnot_vis : ¬ s.Visited root := (Search.not_visited_iff s root).mpr hunvis
  have hnot_post : root ∉ s.postorder := fun hm =>
    hnot_vis ((h.visited_iff root).mpr (Or.inr hm))
  have hroot_sz : root < s.depth.size := by rw [h.depth_size]; exact hroot
  have hdepth_s0 : ∀ v, s₀.depth[v]?.join = if v = root then some 0 else s.depth[v]?.join :=
    getElem?_join_set! s.depth root (some 0) hroot_sz
  have hvis_s0 : ∀ v, s₀.Visited v ↔ v = root ∨ s.Visited v := by
    intro v
    simp only [Search.Visited, hdepth_s0]
    split_ifs with hvr
    · subst hvr; simp
    · simp [hvr]
  have hdepth_old : ∀ v : Fin N, s.Visited v.val → (s₀.forest N).depth v = (s.forest N).depth v := by
    intro v hv
    have hvr : v.val ≠ root := fun heq => hnot_vis (heq ▸ hv)
    simp [Search.forest, hdepth_s0, hvr]
  have hforest_par : (s₀.forest N).parent = (s.forest N).parent := rfl
  have hanc_eq : ∀ u v : Fin N, (s₀.forest N).Ancestor u v ↔ (s.forest N).Ancestor u v := by
    intro u v
    simp [Forest.Ancestor, hforest_par]
  refine
    { depth_size := by simp [s₀, h.depth_size]
      parent_size := h.parent_size
      parentEdge_size := h.parentEdge_size
      active_lt := by simpa using hroot
      postorder_lt := h.postorder_lt
      nodup_verts := by
        have hnodup : s.postorder.Nodup := by simpa using h.nodup_verts
        simpa [s₀, List.nodup_cons, hnot_post] using hnodup
      frame_next_le := by simp
      visited_iff := fun v => by
        rw [hvis_s0, h.visited_iff]
        simp [s₀]
      unvisited_none := fun v hv => by
        rw [hvis_s0, not_or] at hv
        exact h.unvisited_none v hv.2
      root_depth := fun v hv hp => by
        rw [hvis_s0] at hv
        rcases hv with hvr | hv
        · refine ⟨?_, (h.unvisited_none v.val (hvr ▸ hnot_vis)).2⟩
          simp [Search.forest, hdepth_s0, hvr]
        · rw [hdepth_old v hv]
          exact h.root_depth v hv hp
      parent_spec := fun v u hp => by
        obtain ⟨hu, hv_vis, hu_vis, hadj, hd, k, hsc, hk⟩ := h.parent_spec v u hp
        refine ⟨hu, (hvis_s0 v.val).mpr (Or.inr hv_vis), (hvis_s0 u).mpr (Or.inr hu_vis),
          hadj, ?_, k, ?_, hk⟩
        · rw [hdepth_old v hv_vis, hdepth_old ⟨u, hu⟩ hu_vis]
          exact hd
        · simpa [Scanned, s₀] using hsc
      stack_chain := List.isChain_singleton _
      active_parent_mem := by
        intro v hv u hp
        simp only [List.map_cons, List.map_nil, List.mem_singleton] at hv
        subst hv
        have hp' : s.parent[v]?.join = some u := hp
        rw [(h.unvisited_none v hnot_vis).1] at hp'
        nomatch hp'
      postorder_order := h.postorder_order
      scanned_visited := fun v k hsc => by
        have hsc' : Scanned N lists s [] v k := by simpa [Scanned, s₀] using hsc
        exact (hvis_s0 _).mpr (Or.inr (h.scanned_visited v k hsc'))
      completed_adj := fun u v hu hadj => by
        refine ⟨?_, ?_⟩
        · intro hv_act
          simp only [List.map_cons, List.map_nil, List.mem_singleton] at hv_act
          exfalso
          have hmem : v.val ∈ (List.ofFn lists).toArray[u.val]! :=
            (adj_mem_iff hAdj u.2 v.2).mpr hadj
          obtain ⟨k, hk, hget⟩ := List.getElem_of_mem hmem
          have hsc : Scanned N lists s [] u.val k := ⟨u.2, hk, Or.inl hu⟩
          have hvis_v := h.scanned_visited u.val k hsc
          rw [getElem!_pos _ k hk, hget, hv_act] at hvis_v
          exact hnot_vis hvis_v
        · intro hv_post
          rw [hanc_eq, hanc_eq]
          exact (h.completed_adj u v hu hadj).2 hv_post
      edges_valid := fun i hi => by
        obtain ⟨hs, ht, hvs, hvt, ⟨k, hsc, hk⟩, htree⟩ := h.edges_valid i hi
        refine ⟨hs, ht, (hvis_s0 _).mpr (Or.inr hvs), (hvis_s0 _).mpr (Or.inr hvt),
          ⟨k, by simpa [Scanned, s₀] using hsc, hk⟩, ?_⟩
        rw [hdepth_old ⟨_, ht⟩ hvt, hdepth_old ⟨_, hs⟩ hvs]
        exact htree
      parentEdge_iff := h.parentEdge_iff
      parent_iff_edge := h.parent_iff_edge
      edges_inj := h.edges_inj
      scanned_edge_exists := fun v k hsc hv hw hcond => by
        have hsc' : Scanned N lists s [] v k := by simpa [Scanned, s₀] using hsc
        have hv_vis : s.Visited v := by
          rcases hsc' with ⟨_, _, h1 | ⟨_, h2, _⟩⟩
          · exact (h.visited_iff v).mpr (Or.inr h1)
          · simp at h2
        have hw_vis : s.Visited (((List.ofFn lists).toArray[v]!)[k]!) :=
          h.scanned_visited v k hsc'
        rw [hdepth_old ⟨_, hw⟩ hw_vis, hdepth_old ⟨v, hv⟩ hv_vis] at hcond
        exact h.scanned_edge_exists v k hsc' hv hw hcond }

end GraphMinor.LRPlanarity
