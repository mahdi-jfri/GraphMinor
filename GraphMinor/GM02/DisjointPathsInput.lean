module

public import GraphMinor.Compute.DPStatement
public import GraphMinor.Compute.GM02MultiTerminatedInput
public import GraphMinor.Compute.GM02TerminatedInput
import GraphMinor.Compute.GM02RowMajorPairs
import GraphMinor.GM02.FeasibilityVertices
import GraphMinor.GM02.MinorWidth
import GraphMinor.Compute.GM13ClassFolio

/-!
# Disjoint paths instances as terminated graphs

Graph Minors II, (1.3), asks for `k` disjoint paths joining given pairs
`(s_i, t_i)`. When the `2k` ends are distinct, the pairs form a termination in
the sense of II, page 310, and the paths exist exactly when this terminated
graph is feasible. This file builds the terminated graph (`dpMultiInput`) and
proves that equivalence (`hasDisjointPaths_iff_feasible`). Loops and parallel
edges do not matter for paths, so the multiplicities are capped at one first.
It also lists the pairs in the canonical order used by the encoding of II
(3.2) (`edgeListOf_dpMultiInput`).
-/

@[expose] public section

namespace GraphMinor.GM02

open GraphMinor.Compute Graph Set Classical

/-- Graph Minors II, Section 1, page 310: a termination has pairs of vertices
whose endpoints are all distinct. This predicate imposes that condition on
the terminal pairs of a disjoint-paths instance. -/
def IsTermination {k : ℕ} (x : DPInput k) : Prop :=
  Function.Injective (Sum.elim (fun i : Fin k => (x.pairs i).1)
    (fun i : Fin k => (x.pairs i).2))

variable {k : ℕ}

theorem IsTermination.fst_ne_snd {x : DPInput k} (hx : IsTermination x) (i : Fin k) :
    (x.pairs i).1 ≠ (x.pairs i).2 := fun h => by
  have := @hx (Sum.inl i) (Sum.inr i) h
  simp at this

theorem IsTermination.fst_inj {x : DPInput k} (hx : IsTermination x) {i j : Fin k}
    (h : (x.pairs i).1 = (x.pairs j).1) : i = j := by
  have := @hx (Sum.inl i) (Sum.inl j) h
  simpa using this

theorem IsTermination.snd_inj {x : DPInput k} (hx : IsTermination x) {i j : Fin k}
    (h : (x.pairs i).2 = (x.pairs j).2) : i = j := by
  have := @hx (Sum.inr i) (Sum.inr j) h
  simpa using this

theorem IsTermination.fst_ne_snd' {x : DPInput k} (hx : IsTermination x) (i j : Fin k) :
    (x.pairs i).1 ≠ (x.pairs j).2 := fun h => by
  have := @hx (Sum.inl i) (Sum.inr j) h
  simp at this

/-- The `i`-th terminal pair as an unordered pair of vertices of `Fin n`. -/
def dpPair (x : DPInput k) (i : Fin k) : Sym2 (Fin x.n) :=
  s((x.pairs i).1, (x.pairs i).2)

/-- Two terminal pairs are equal only for the same index. -/
theorem IsTermination.dpPair_injective {x : DPInput k} (hx : IsTermination x) :
    Function.Injective (dpPair x) := by
  intro i j h
  rcases Sym2.eq_iff.1 h with ⟨h1, -⟩ | ⟨h1, -⟩
  · exact hx.fst_inj h1
  · exact absurd h1 (hx.fst_ne_snd' i j)

/-- A vertex of the `i`-th pair is not in the `j`-th pair, for `i ≠ j`. -/
theorem IsTermination.not_mem_dpPair {x : DPInput k} (hx : IsTermination x) {i j : Fin k}
    (hij : i ≠ j) {v : Fin x.n} (hi : v ∈ dpPair x i) : v ∉ dpPair x j := by
  intro hj
  simp only [dpPair, Sym2.mem_iff] at hi hj
  rcases hi with rfl | rfl <;> rcases hj with h | h
  · exact hij (hx.fst_inj h)
  · exact hx.fst_ne_snd' i j h
  · exact hx.fst_ne_snd' j i h.symm
  · exact hij (hx.snd_inj h)

/-- The terminal pairs, on the natural-number names of the vertices. -/
def dpTerminalPairs (x : DPInput k) : Finset (Sym2 ℕ) :=
  Finset.univ.image fun i => (dpPair x i).map Fin.val

/-- The terminal pairs of a disjoint-paths instance form a termination of any
multigraph on the same vertices. -/
def dpTermination (x : DPInput k) (hx : IsTermination x) (H : MultiDigraph x.n) :
    Termination V(H.toGMDigraph.toGraph) where
  pairs := dpTerminalPairs x
  not_diag := by
    intro p hp
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.1 hp
    simp only [dpPair, Sym2.map_mk, Sym2.mk_isDiag_iff]
    exact fun h => hx.fst_ne_snd i (Fin.ext h)
  vertex_mem := by
    intro p hp v hv
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.1 hp
    simp only [dpPair, Sym2.map_mk, Sym2.mem_iff] at hv
    show v < x.n
    rcases hv with h | h
    · rw [h]; exact (x.pairs i).1.2
    · rw [h]; exact (x.pairs i).2.2
  disjoint := by
    intro p hp q hq hpq
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.1 hp
    obtain ⟨j, -, rfl⟩ := Finset.mem_image.1 hq
    have hij : i ≠ j := fun h => hpq (h ▸ rfl)
    rw [Set.disjoint_left]
    intro v hvi hvj
    simp only [Set.mem_ofPred_eq, Sym2.mem_map] at hvi hvj
    obtain ⟨a, ha, rfl⟩ := hvi
    obtain ⟨b, hb, hab⟩ := hvj
    rw [Fin.val_inj] at hab
    subst hab
    exact hx.not_mem_dpPair hij ha hb

/-- The terminated multigraph of a disjoint-paths instance, with the
multiplicities capped at one. -/
noncomputable def dpMultiInput (x : DPInput k) (hx : IsTermination x) :
    GM02MultiTerminatedInput :=
  ⟨x.n, x.G.cap 0, dpTermination x hx (x.G.cap 0)⟩

theorem dpMultiInput_index (x : DPInput k) (hx : IsTermination x) :
    (dpMultiInput x hx).A.index = k := by
  have hinj : Function.Injective fun i => (dpPair x i).map Fin.val := fun i j h =>
    hx.dpPair_injective (Sym2.map.injective Fin.val_injective h)
  change (dpTerminalPairs x).card = k
  rw [dpTerminalPairs, Finset.card_image_of_injective _ hinj, Finset.card_univ, Fintype.card_fin]

/-- The pairs of the numbered simple instance are the terminal pairs. -/
theorem mem_dpMultiInput_simple_pairs (x : DPInput k) (hx : IsTermination x)
    (p : Sym2 (Fin x.n)) :
    p ∈ (dpMultiInput x hx).simple.A.pairs ↔ ∃ i, dpPair x i = p := by
  have h := (dpMultiInput x hx).simple_pairs_val
  have hinj : Function.Injective (Sym2.map (fun u : Fin x.n => u.val)) :=
    Sym2.map.injective Fin.val_injective
  constructor
  · intro hp
    have hm : Sym2.map (fun u : Fin x.n => u.val) p ∈ dpTerminalPairs x := by
      change _ ∈ (dpMultiInput x hx).A.pairs
      rw [← h]
      exact Finset.mem_image_of_mem _ hp
    obtain ⟨i, -, hi⟩ := Finset.mem_image.1 hm
    exact ⟨i, hinj hi⟩
  · rintro ⟨i, rfl⟩
    have hm : Sym2.map (fun u : Fin x.n => u.val) (dpPair x i) ∈ (dpMultiInput x hx).A.pairs :=
      Finset.mem_image.2 ⟨i, Finset.mem_univ _, rfl⟩
    rw [← h] at hm
    obtain ⟨q, hq, hqe⟩ := Finset.mem_image.1 hm
    have hqi : q = dpPair x i := hinj hqe
    rw [← hqi]
    exact hq

theorem dpMultiInput_simple_graph (x : DPInput k) (hx : IsTermination x) :
    (dpMultiInput x hx).simple.G = x.G.toSimpleGraph := by
  rw [GM02MultiTerminatedInput.simple_graph]
  exact MultiDigraph.toSimpleGraph_cap 0 x.G

/-- The paths of the disjoint-paths problem exist exactly when the terminated
graph is feasible. A path for a pair may run in either direction; reversing it
does not change its vertices. -/
theorem hasDisjointPaths_iff_feasible (x : DPInput k) (hx : IsTermination x) :
    Compute.HasDisjointPaths x ↔
      (dpMultiInput x hx).A.Feasible (dpMultiInput x hx).G.toGMDigraph.toGraph := by
  rw [← GM02MultiTerminatedInput.simple_feasible_iff, Termination.Feasible,
    pathGraph_ofSimpleGraph, dpMultiInput_simple_graph]
  have hmem : ∀ p, p ∈ (dpMultiInput x hx).simple.A.pairs ↔ ∃ i, dpPair x i = p :=
    mem_dpMultiInput_simple_pairs x hx
  constructor
  · rintro ⟨P, hpath, hdisj⟩
    let idx : {p // p ∈ (dpMultiInput x hx).simple.A.pairs} → Fin k :=
      fun p => ((hmem p.1).1 p.2).choose
    have hidx : ∀ p, dpPair x (idx p) = p.1 := fun p => ((hmem p.1).1 p.2).choose_spec
    refine ⟨fun p => ⟨(x.pairs (idx p)).1, (x.pairs (idx p)).2, hidx p, P (idx p),
      hpath (idx p)⟩, fun p q hpq => ?_⟩
    have hne : idx p ≠ idx q := fun h => hpq (Subtype.ext ((hidx p).symm.trans (h ▸ hidx q)))
    rw [Set.disjoint_left]
    intro v hvp hvq
    exact hdisj _ _ hne hvp hvq
  · rintro ⟨Q, hdisj⟩
    have hin : ∀ i, dpPair x i ∈ (dpMultiInput x hx).simple.A.pairs :=
      fun i => (hmem _).2 ⟨i, rfl⟩
    have hends : ∀ i, ((Q ⟨_, hin i⟩).start = (x.pairs i).1 ∧
        (Q ⟨_, hin i⟩).finish = (x.pairs i).2) ∨
        ((Q ⟨_, hin i⟩).start = (x.pairs i).2 ∧ (Q ⟨_, hin i⟩).finish = (x.pairs i).1) :=
      fun i => Sym2.eq_iff.1 (Q ⟨_, hin i⟩).ends_eq
    let W : ∀ i, x.G.toSimpleGraph.Walk (x.pairs i).1 (x.pairs i).2 := fun i =>
      if h : (Q ⟨_, hin i⟩).start = (x.pairs i).1 ∧ (Q ⟨_, hin i⟩).finish = (x.pairs i).2 then
        (Q ⟨_, hin i⟩).walk.copy h.1 h.2
      else
        (Q ⟨_, hin i⟩).walk.reverse.copy ((hends i).resolve_left h).2
          ((hends i).resolve_left h).1
    have hc : ∀ {a b c d : Fin x.n} (w : x.G.toSimpleGraph.Walk a b) (h1 : a = c) (h2 : b = d)
        (v : Fin x.n), v ∈ (w.copy h1 h2).support ↔ v ∈ w.support := by
      intros; subst_vars; rfl
    have hr : ∀ {a b c d : Fin x.n} (w : x.G.toSimpleGraph.Walk a b) (h1 : b = c) (h2 : a = d)
        (v : Fin x.n), v ∈ (w.reverse.copy h1 h2).support ↔ v ∈ w.support := by
      intros; subst_vars; simp
    have hsupp : ∀ i v, v ∈ (W i).support ↔ v ∈ (Q ⟨_, hin i⟩).walk.support := by
      intro i v
      by_cases h : (Q ⟨_, hin i⟩).start = (x.pairs i).1 ∧ (Q ⟨_, hin i⟩).finish = (x.pairs i).2
      · rw [show W i = _ from dite_eq_left_of_eq_true (eq_true h)]
        exact hc _ _ _ v
      · rw [show W i = _ from dite_eq_right_of_eq_false (eq_false h)]
        exact hr _ _ _ v
    refine ⟨W, fun i => ?_, fun i j hij => ?_⟩
    · by_cases h : (Q ⟨_, hin i⟩).start = (x.pairs i).1 ∧ (Q ⟨_, hin i⟩).finish = (x.pairs i).2
      · rw [show W i = _ from dite_eq_left_of_eq_true (eq_true h)]
        exact (SimpleGraph.Walk.isPath_copy _ _ _).2 (Q ⟨_, hin i⟩).isPath
      · rw [show W i = _ from dite_eq_right_of_eq_false (eq_false h)]
        exact (SimpleGraph.Walk.isPath_copy _ _ _).2 (Q ⟨_, hin i⟩).isPath.reverse
    · have hne : (⟨_, hin i⟩ : {p // p ∈ (dpMultiInput x hx).simple.A.pairs}) ≠ ⟨_, hin j⟩ :=
        fun h => hij (hx.dpPair_injective (congrArg Subtype.val h))
      intro v hvi hvj
      exact Set.disjoint_left.1 (hdisj _ _ hne) ((hsupp i v).1 hvi) ((hsupp j v).1 hvj)

/-- The test used by the program: `(u, v)` is increasing and is a terminal
pair in one of its two orders. -/
def dpPairTest (x : DPInput k) (p : Fin x.n × Fin x.n) : Prop :=
  p.1.val < p.2.val ∧ ∃ i : Fin k,
    ((x.pairs i).1 = p.1 ∧ (x.pairs i).2 = p.2) ∨ ((x.pairs i).1 = p.2 ∧ (x.pairs i).2 = p.1)

instance (x : DPInput k) : DecidablePred (dpPairTest x) := fun _ => by
  unfold dpPairTest
  infer_instance

/-- The canonical list of terminal pairs, in the row-major order of all
vertex pairs. -/
theorem edgeListOf_dpMultiInput (x : DPInput k) (hx : IsTermination x) :
    edgeListOf (dpMultiInput x hx).simple.A.pairGraph =
      (List.ofFn fun j : Fin (x.n * x.n) => finProdFinEquiv.symm j).filter
        fun p => decide (dpPairTest x p) := by
  rw [edgeListOf, gm02AllPairs_eq_ofFn]
  apply List.filter_congr
  intro p _
  apply decide_eq_decide.2
  rw [Termination.pairGraph_adj_iff]
  refine (and_congr_right fun _ => mem_dpMultiInput_simple_pairs x hx s(p.1, p.2)).trans ?_
  simp only [dpPairTest, dpPair]
  constructor
  · rintro ⟨hlt, i, hi⟩
    refine ⟨hlt, i, ?_⟩
    rcases Sym2.eq_iff.1 hi with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact Or.inl ⟨h1, h2⟩
    · exact Or.inr ⟨h1, h2⟩
  · rintro ⟨hlt, i, hi⟩
    refine ⟨hlt, i, ?_⟩
    rcases hi with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · rw [h1, h2]
    · rw [h1, h2, Sym2.eq_swap]

/-- There are exactly `k` terminal pairs in the list. -/
theorem dpPairList_length (x : DPInput k) (hx : IsTermination x) :
    ((List.ofFn fun j : Fin (x.n * x.n) => finProdFinEquiv.symm j).filter
        fun p => decide (dpPairTest x p)).length = k := by
  have h := gm02Termination_pairList_length (dpMultiInput x hx).simple.A
  rw [GM02MultiTerminatedInput.simple_index, dpMultiInput_index, edgeListOf_dpMultiInput x hx] at h
  exact h

/-- The encoding of the terminated graph: the capped graph, the number `k`,
and the terminal pairs in row-major order. -/
theorem dpMultiInput_enc (x : DPInput k) (hx : IsTermination x) :
    (dpMultiInput x hx).enc = (x.G.cap 0).enc ++ [k] ++
      flatEdges ((List.ofFn fun j : Fin (x.n * x.n) => finProdFinEquiv.symm j).filter
        fun p => decide (dpPairTest x p)) := by
  show (x.G.cap 0).enc ++ [(dpMultiInput x hx).A.index] ++
    flatEdges (edgeListOf (dpMultiInput x hx).simple.A.pairGraph) = _
  rw [edgeListOf_dpMultiInput, dpMultiInput_index]
  rfl

/-- The terminated graph has the same tree-width bounds as a subgraph of the
input graph: capping only deletes edges. -/
theorem dpMultiInput_treeWidthLE (x : DPInput k) (hx : IsTermination x) {q : ℕ}
    (h : TreeWidthLE x.G.toGMDigraph.toGraph q) :
    TreeWidthLE (dpMultiInput x hx).G.toGMDigraph.toGraph q :=
  h.of_isIsoMinor x.G.isFinite_toGMDigraph.finite_V x.G.isFinite_toGMDigraph.finite_E
    (isIsoMinor_of_multi_le43 (x.G.cap_le 0))

end GraphMinor.GM02
