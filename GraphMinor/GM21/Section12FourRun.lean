module

public import GraphMinor.GM21.Section12FourGood
public import GraphMinor.GM21.Section12Chain

/-!
# Graph Minors XXI, (12.4): a run of good vertices gives a chain

The sketch of the proof of (12.4) says: "For each component $C$ of $P \setminus B$, the graph
$\bigcup (W(t) \cap (G \setminus Z) : t \in V(C))$ is a $(w + 1)$-chain, since no vertex of $C$ is
bad." We prove this for a tree-decomposition in which each edge of `G` is in one bag.

A *run* is a path `s 0, s 1, …, s (m + 1)` of `T` with `m ≥ 1`, whose ends are bad and whose inner
vertices are good (`IsRun`). At the inner vertex `s j` the bag `W(s j)` is good for the sets it
shares with `W(s (j - 1))` and `W(s (j + 1))`, and the separations of `G` at the edges of the run
form a chain as in the converse of (12.1) (`uniqSystem_of_steps`). So the union `K` of the bags
of the inner vertices has a unique set of disjoint paths between the sets `S, S'` that it shares
with the bags at the two ends, and it uses all vertices of `K`. A vertex of `K` that is in a bag at
a bad vertex is in `S ∪ S'`. So `K` without the bags at bad vertices is `K \ (S ∪ S')`, which is a
chain (`UniqSystem.isChain_deleteVertices`).
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace GraphMinor
namespace GM21

open Set SimpleGraph Hypergraph

universe u v

variable {α : Type u} {β : Type v}

/-! ## Trees -/

section Tree

variable {κ : Type*} [Fintype κ] {T : SimpleGraph κ}

/-- In a tree, `r` is on the side of `w` of the edge `wu` exactly when `u` is not on the path from
`w` to `r`. -/
theorem reachable_deleteEdges_iff (hT : T.IsTree) {u w : κ} (hadj : T.Adj w u) (r : κ) :
    (T.deleteEdges {s(w, u)}).Reachable w r ↔ ¬ Thomas.OnTreePath T w r u := by
  constructor
  · intro hr hu
    have he := onTreePathEdge_of_onTreePath hT hadj (Thomas.onTreePath_left T w r) hu
    exact ((Thomas.onTreePathEdge_iff_not_reachable_deleteEdges).1 he).2 hr
  · intro hu
    have := reachable_deleteEdges_of_not_onTreePath hT (u := u) (v := w) (x := r)
      (fun h ↦ hu (Thomas.onTreePath_symm h))
    rw [Sym2.eq_swap] at this
    exact this.symm

variable {W : κ → Hypergraph α β}

/-- At a good vertex `x`, two distinct neighbours `a, c` are all its neighbours. -/
theorem GoodAt.eq_or_eq {x a c : κ} (hx : GoodAt T W x) (ha : T.Adj x a) (hc : T.Adj x c)
    (hac : a ≠ c) : ∀ z, T.Adj x z → z = a ∨ z = c := by
  obtain ⟨u, u', -, hN, -⟩ := hx
  intro z hz
  rcases (hN a).1 ha with h1 | h1 <;> rcases (hN c).1 hc with h2 | h2 <;>
    rcases (hN z).1 hz with h3 | h3
  all_goals first
    | exact Or.inl (h3.trans h1.symm)
    | exact Or.inr (h3.trans h2.symm)
    | exact absurd (h1.trans h2.symm) hac

/-- **The first bad vertex in a direction.** Let `t` be good and `u` a neighbour of `t`. Then there
is a bad vertex `b` such that the path from `t` to `b` goes through `u` and all its vertices other
than `b` are good. Take the farthest vertex `x` beyond `u` such that the path from `t` to `x` has
only good vertices; the neighbour of `x` away from `t` is bad, since otherwise it would be farther. -/
theorem exists_first_bad (hT : T.IsTree) {N : Set κ} (hgood : ∀ z ∉ N, GoodAt T W z)
    {t u : κ} (ht : t ∉ N) (hu : T.Adj t u) :
    ∃ b ∈ N, Thomas.OnTreePath T t b u ∧ ∀ x, Thomas.OnTreePath T t b x → x ≠ b → x ∉ N := by
  classical
  by_cases huN : u ∈ N
  · refine ⟨u, huN, Thomas.onTreePath_right T t u, fun x hx hxu ↦ ?_⟩
    rcases (onTreePath_adj_iff hT hu).1 hx with h | h
    · exact h ▸ ht
    · exact absurd h hxu
  set S := {x | Thomas.OnTreePath T t x u ∧ ∀ y, Thomas.OnTreePath T t x y → y ∉ N} with hS
  have huS : u ∈ S := ⟨Thomas.onTreePath_right T t u, fun y hy ↦ by
    rcases (onTreePath_adj_iff hT hu).1 hy with h | h
    · exact h ▸ ht
    · exact h ▸ huN⟩
  obtain ⟨x, hxS, hxmax⟩ := (toFinite S).toFinset.exists_max_image
    (fun x ↦ {y | Thomas.OnTreePath T t x y}.ncard) ⟨u, (toFinite S).mem_toFinset.2 huS⟩
  rw [Finite.mem_toFinset] at hxS
  obtain ⟨hxu, hxgood⟩ := hxS
  have hxN : x ∉ N := hxgood x (Thomas.onTreePath_right T t x)
  have hxt : x ≠ t := by
    rintro rfl
    rw [Thomas.onTreePath_self] at hxu
    exact hu.ne hxu.symm
  obtain ⟨p, hxp, hp⟩ := exists_adj_onTreePath hT hxt
  obtain ⟨y, hxy, hyp⟩ : ∃ y, T.Adj x y ∧ y ≠ p := by
    obtain ⟨u₀, u₀', hne, hN, -⟩ := hgood x hxN
    by_cases h : u₀ = p
    · exact ⟨u₀', (hN u₀').2 (Or.inr rfl), fun h' ↦ hne (h.trans h'.symm)⟩
    · exact ⟨u₀, (hN u₀).2 (Or.inl rfl), h⟩
  have hxty : Thomas.OnTreePath T t y x := by
    rcases Thomas.onTreePath_adj_dichotomy hT hxy t with ⟨h1, -⟩ | ⟨h1, -⟩
    · exact h1
    · exact absurd (eq_of_adj_of_onTreePath hT hxy hxp (Thomas.onTreePath_symm h1) hp) hyp
  have hsplit : ∀ z, Thomas.OnTreePath T t y z → Thomas.OnTreePath T t x z ∨ z = y := by
    intro z hz
    rcases (Thomas.onTreePath_split_iff hT hxty).1 hz with h | h
    · exact Or.inl h
    · rcases (onTreePath_adj_iff hT hxy).1 h with h' | h'
      · exact Or.inl (h' ▸ Thomas.onTreePath_right T t x)
      · exact Or.inr h'
  have hyN : y ∈ N := by
    by_contra hyN
    have hyS : y ∈ S := ⟨Thomas.onTreePath_trans_left hT hxty hxu, fun z hz ↦ by
      rcases hsplit z hz with h | h
      · exact hxgood z h
      · exact h ▸ hyN⟩
    have := hxmax y ((toFinite S).mem_toFinset.2 hyS)
    refine absurd this (not_le.2 (ncard_lt_ncard ⟨fun z hz ↦ Thomas.onTreePath_trans_left hT hxty hz,
      fun hsub ↦ hxy.ne ?_⟩ (toFinite _)))
    exact Thomas.onTreePath_antisymm hT hxty (hsub (Thomas.onTreePath_right T t y))
  refine ⟨y, hyN, Thomas.onTreePath_trans_left hT hxty hxu, fun z hz hzy ↦ ?_⟩
  rcases hsplit z hz with h | h
  · exact hxgood z h
  · exact absurd h hzy

end Tree

/-! ## Runs -/

section Run

variable {κ : Type*} [Fintype κ] {T : SimpleGraph κ}

/-- A *run*: a path `s 0, …, s (m + 1)` of `T` with `m ≥ 1`, whose two ends are in `N` and whose
inner vertices are not in `N` and have no neighbours other than the next and previous vertex. -/
structure IsRun (T : SimpleGraph κ) (N : Set κ) (s : ℕ → κ) (m : ℕ) : Prop where
  seq : IsSeqPath T s (m + 1)
  one_le : 1 ≤ m
  first : s 0 ∈ N
  last : s (m + 1) ∈ N
  inner : ∀ j, 1 ≤ j → j ≤ m → s j ∉ N
  nbr : ∀ j, 1 ≤ j → j ≤ m → ∀ z, T.Adj (s j) z → z = s (j - 1) ∨ z = s (j + 1)

/-- The inner vertices of a run. -/
def runSet (s : ℕ → κ) (m : ℕ) : Set κ := {z | ∃ j, 1 ≤ j ∧ j ≤ m ∧ s j = z}

variable {N : Set κ} {s : ℕ → κ} {m : ℕ}

theorem IsRun.notMem_of_mem (hr : IsRun T N s m) {z : κ} (hz : z ∈ runSet s m) : z ∉ N := by
  obtain ⟨j, h1, h2, rfl⟩ := hz
  exact hr.inner j h1 h2

theorem IsRun.inj (hr : IsRun T N s m) {i j : ℕ} (hi : i ≤ m + 1) (hj : j ≤ m + 1)
    (h : s i = s j) : i = j :=
  hr.seq.injOn (mem_Iic.2 hi) (mem_Iic.2 hj) h

/-- The path between `s i` and `s j` is `s i, …, s j`. -/
theorem IsRun.eq_of_onTreePath (hr : IsRun T N s m) {i j : ℕ} (hij : i ≤ j) (hj : j ≤ m + 1)
    {z : κ} (hz : Thomas.OnTreePath T (s i) (s j) z) : ∃ l, i ≤ l ∧ l ≤ j ∧ s l = z := by
  obtain ⟨k, rfl⟩ : ∃ k, j = i + k := ⟨j - i, by omega⟩
  have := hz _ (isPath_seqWalk hr.seq i k hj)
  rwa [mem_support_seqWalk] at this

variable (hT : T.IsTree)

include hT

/-- The path between two inner vertices has only inner vertices. -/
theorem IsRun.mem_of_onTreePath (hr : IsRun T N s m) {z₁ z₂ z : κ} (h₁ : z₁ ∈ runSet s m)
    (h₂ : z₂ ∈ runSet s m) (hz : Thomas.OnTreePath T z₁ z₂ z) : z ∈ runSet s m := by
  obtain ⟨i, hi1, him, rfl⟩ := h₁
  obtain ⟨j, hj1, hjm, rfl⟩ := h₂
  rcases le_total i j with hij | hji
  · obtain ⟨l, h1, h2, rfl⟩ := hr.eq_of_onTreePath hij (by omega) hz
    exact ⟨l, by omega, by omega, rfl⟩
  · obtain ⟨l, h1, h2, rfl⟩ := hr.eq_of_onTreePath hji (by omega) (Thomas.onTreePath_symm hz)
    exact ⟨l, by omega, by omega, rfl⟩

/-- **Leaving a run.** The path from an inner vertex `z` to a vertex `x` outside the run leaves it
through the edge `s 1 s 0` or the edge `s m s (m + 1)`. -/
theorem IsRun.exit (hr : IsRun T N s m) {z x : κ} (hz : z ∈ runSet s m) (hx : x ∉ runSet s m) :
    Thomas.OnTreePathEdge T z x (s 1) (s 0) ∨ Thomas.OnTreePathEdge T z x (s m) (s (m + 1)) := by
  obtain ⟨y, y', hyy, hyI, hy'I⟩ := Thomas.exists_onTreePathEdge_of_prop hT (· ∈ runSet s m) hz hx
  obtain ⟨j, hj1, hjm, rfl⟩ := hyI
  rcases hr.nbr j hj1 hjm y' hyy.1 with h | h
  · have : j = 1 := by
      by_contra hj
      exact hy'I ⟨j - 1, by omega, by omega, h.symm⟩
    subst this
    left
    rw [h] at hyy
    exact hyy
  · have : j = m := by
      by_contra hj
      exact hy'I ⟨j + 1, by omega, by omega, h.symm⟩
    right
    rw [h] at hyy
    rw [← this]
    exact hyy

/-- An inner vertex is on the side of `s 1` of the first edge and on the side of `s m` of the last
edge. -/
theorem IsRun.not_onTreePath_first (hr : IsRun T N s m) {z : κ} (hz : z ∈ runSet s m) :
    ¬ Thomas.OnTreePath T (s 1) z (s 0) := by
  obtain ⟨j, hj1, hjm, rfl⟩ := hz
  intro h
  obtain ⟨l, h1, h2, hl⟩ := hr.eq_of_onTreePath hj1 (by omega) h
  have := hr.inj (by omega) (by omega) hl
  omega

theorem IsRun.not_onTreePath_last (hr : IsRun T N s m) {z : κ} (hz : z ∈ runSet s m) :
    ¬ Thomas.OnTreePath T (s m) z (s (m + 1)) := by
  obtain ⟨j, hj1, hjm, rfl⟩ := hz
  intro h
  obtain ⟨l, h1, h2, hl⟩ := hr.eq_of_onTreePath hjm (by omega) (Thomas.onTreePath_symm h)
  have := hr.inj (by omega) (by omega) hl
  omega

/-- If `r` is on the side of `s 1` of the first edge and `r'` on the side of `s m` of the last
edge, and `r'` is not an inner vertex, then `s 1` is on the path between them, since `r'` is beyond
`s 0`. -/
theorem IsRun.onTreePath_one (hr : IsRun T N s m) {r r' : κ}
    (hr₁ : ¬ Thomas.OnTreePath T (s 1) r (s 0)) (hr₂ : ¬ Thomas.OnTreePath T (s m) r' (s (m + 1)))
    (hr'I : r' ∉ runSet s m) : Thomas.OnTreePath T r r' (s 1) := by
  have h1I : s 1 ∈ runSet s m := ⟨1, le_rfl, hr.one_le, rfl⟩
  have hmI : s m ∈ runSet s m := ⟨m, hr.one_le, le_rfl, rfl⟩
  have hadj : T.Adj (s 1) (s 0) := (hr.seq.adj 0 (by omega)).symm
  have hs₁ : Thomas.OnTreePath T r (s 0) (s 1) := by
    rcases Thomas.onTreePath_adj_dichotomy hT hadj r with ⟨h1, -⟩ | ⟨h1, -⟩
    · exact h1
    · exact absurd (Thomas.onTreePath_symm h1) hr₁
  rcases hr.exit hT hmI hr'I with h' | h'
  swap
  · exact absurd h'.onTreePath_right hr₂
  have hs₂ : Thomas.OnTreePath T r' (s 1) (s 0) := by
    have h10 : Thomas.OnTreePath T (s m) (s 0) (s 1) := Thomas.onTreePath_symm
      (onTreePath_seq hT hr.seq (i := 0) (j := m) (l := 1) (by omega) hr.one_le (by omega))
    have h1r' : Thomas.OnTreePath T (s m) r' (s 1) :=
      Thomas.onTreePath_trans_left hT h'.onTreePath_right h10
    rcases (Thomas.onTreePath_split_iff hT h1r').1 h'.onTreePath_right with h2 | h2
    · obtain ⟨l, hl1, hlm, hl⟩ := hr.eq_of_onTreePath (i := 1) (j := m) hr.one_le (by omega)
        (Thomas.onTreePath_symm h2)
      have := hr.inj (by omega) (by omega) hl
      omega
    · exact Thomas.onTreePath_symm h2
  exact (Thomas.onTreePath_of_sides hT hadj hs₁ hs₂).1

end Run

/-! ## The separations at a good vertex -/

section Sides

variable {κ : Type*} [Fintype κ] {T : SimpleGraph κ} {G : Hypergraph α β}
  {W : κ → Hypergraph α β}

theorem mem_treeDecompSide_edgeSet {e : Sym2 κ} {x : κ} {f : β} :
    f ∈ (GM10.treeDecompSide T W e x).edgeSet ↔
      ∃ r, (T.deleteEdges {e}).Reachable x r ∧ f ∈ (W r).edgeSet := by
  classical
  simp [GM10.treeDecompSide, Hypergraph.biUnion]

theorem treeDecompSide_le (hTD : GM10.IsTreeDecomposition G T W) (e : Sym2 κ) (x : κ) :
    GM10.treeDecompSide T W e x ≤ G :=
  GM10.biUnion_le_of_le fun t _ ↦ hTD.le t

/-- **The two sides at a vertex of degree `2`.** If `t` has exactly the neighbours `u ≠ u'`, then
the side of `t` of the edge `ut` and the side of `t` of the edge `tu'` meet in `W(t)`. -/
theorem treeDecompSide_inter_eq (hTD : GM10.IsTreeDecomposition G T W) {t u u' : κ}
    (hu : T.Adj t u) (hu' : T.Adj t u') (hne : u ≠ u') (hN : ∀ z, T.Adj t z → z = u ∨ z = u') :
    GM10.treeDecompSide T W s(u, t) t ∩ GM10.treeDecompSide T W s(t, u') t = W t := by
  have hT := hTD.isTree
  have h1 : ∀ r, (T.deleteEdges {s(u, t)}).Reachable t r ↔ ¬ Thomas.OnTreePath T t r u := by
    intro r
    rw [Sym2.eq_swap]
    exact reachable_deleteEdges_iff hT hu r
  have h2 : ∀ r, (T.deleteEdges {s(t, u')}).Reachable t r ↔ ¬ Thomas.OnTreePath T t r u' :=
    reachable_deleteEdges_iff hT hu'
  -- A vertex `r ≠ t` on the first side is beyond `u'`, and on the second side beyond `u`.
  have hb1 : ∀ r, ¬ Thomas.OnTreePath T t r u → r ≠ t → Thomas.OnTreePath T t r u' := by
    intro r hr hrt
    obtain ⟨z, htz, hz⟩ := exists_adj_onTreePath hT (Ne.symm hrt)
    rcases hN z htz with rfl | rfl
    · exact absurd hz hr
    · exact hz
  have hb2 : ∀ r, ¬ Thomas.OnTreePath T t r u' → r ≠ t → Thomas.OnTreePath T t r u := by
    intro r hr hrt
    obtain ⟨z, htz, hz⟩ := exists_adj_onTreePath hT (Ne.symm hrt)
    rcases hN z htz with rfl | rfl
    · exact hz
    · exact absurd hz hr
  refine GM10.eq_of_le_of_vertexSet_eq_of_edgeSet_eq
    (GM10.inter_le (treeDecompSide_le hTD _ _) (treeDecompSide_le hTD _ _)) (hTD.le t) ?_ ?_
  · ext y
    refine ⟨fun ⟨hy1, hy2⟩ ↦ ?_, fun hy ↦ ⟨mem_treeDecompSide_vertexSet.2 ⟨t, Reachable.refl _, hy⟩,
      mem_treeDecompSide_vertexSet.2 ⟨t, Reachable.refl _, hy⟩⟩⟩
    obtain ⟨r, hr, hyr⟩ := mem_treeDecompSide_vertexSet.1 hy1
    obtain ⟨r', hr', hyr'⟩ := mem_treeDecompSide_vertexSet.1 hy2
    by_cases hrt : r = t
    · exact hrt ▸ hyr
    by_cases hr't : r' = t
    · exact hr't ▸ hyr'
    have hru' := hb1 r ((h1 r).1 hr) hrt
    have hr'u := hb2 r' ((h2 r').1 hr') hr't
    have hs₁ : Thomas.OnTreePath T r' u' t := by
      rcases Thomas.onTreePath_adj_dichotomy hT hu' r' with ⟨h, -⟩ | ⟨h, -⟩
      · exact h
      · exact absurd (eq_of_adj_of_onTreePath hT hu hu' hr'u (Thomas.onTreePath_symm h)) hne
    have hpath := (Thomas.onTreePath_of_sides hT hu' hs₁ (Thomas.onTreePath_symm hru')).1
    exact (hTD.inter_le hpath).vertexSet_subset ⟨hyr', hyr⟩
  · ext f
    refine ⟨fun ⟨hf1, hf2⟩ ↦ ?_, fun hf ↦ ⟨mem_treeDecompSide_edgeSet.2 ⟨t, Reachable.refl _, hf⟩,
      mem_treeDecompSide_edgeSet.2 ⟨t, Reachable.refl _, hf⟩⟩⟩
    obtain ⟨r, hr, hfr⟩ := mem_treeDecompSide_edgeSet.1 hf1
    obtain ⟨r', hr', hfr'⟩ := mem_treeDecompSide_edgeSet.1 hf2
    have hrr : r = r' := by
      by_contra hrr
      have := hTD.edgeSet_inter_eq hrr
      exact (eq_empty_iff_forall_notMem.1 this) f ⟨hfr, hfr'⟩
    subst hrr
    by_cases hrt : r = t
    · exact hrt ▸ hfr
    exact absurd (eq_of_adj_of_onTreePath hT hu hu' (hb2 r ((h2 r).1 hr') hrt)
      (hb1 r ((h1 r).1 hr) hrt)) hne

end Sides

/-! ## A step of the chain -/

section Step

variable {k : ℕ}

/-- A good bag between two separations gives a step as in the converse of (12.1). -/
theorem isChainStep'_of_isGoodBag {A B A₁ B₁ K : Hypergraph α β} {S S' : Set α}
    (hK : B ∩ A₁ = K) (hS : (A ∩ B).vertexSet = S) (hS' : (A₁ ∩ B₁).vertexSet = S')
    (hg : IsGoodBag K S S') (hk : S.ncard = k) (hSf : S.Finite) :
    IsChainStep' k A B A₁ B₁ ∧
      (B ∩ A₁).vertexSet ⊆ (A ∩ B).vertexSet ∪ (A₁ ∩ B₁).vertexSet := by
  rw [hK, hS, hS']
  rcases hg with ⟨h1, h2⟩ | ⟨hcov, X, v, v', g, hE, hends, hvv', hvX, hv'X, h1, h2⟩
  · refine ⟨Or.inl ⟨?_, ?_⟩, h1 ▸ subset_union_left⟩
    · rw [hS, hK, h1]
    · rw [hS', hK, h2]
  refine ⟨Or.inr ⟨g, by rw [hK, hE], Or.inr ⟨X, v, v', ?_, ?_, by rw [hK, hends], by rw [hS, h1],
    by rw [hS', h2]⟩⟩, hcov⟩
  · rw [hS, hS', h1, h2]
    ext y
    simp only [mem_inter_iff, mem_insert_iff]
    constructor
    · rintro ⟨h | h, h' | h'⟩
      · exact absurd (h.symm.trans h') hvv'
      · exact absurd (h ▸ h') hvX
      · exact h
      · exact h
    · intro h
      exact ⟨Or.inr h, Or.inr h⟩
  · have hXf : X.Finite := hSf.subset (h1 ▸ subset_insert v X)
    rw [← hk, h1, ncard_insert_of_notMem hvX hXf]
    omega

end Step

/-! ## A run gives a chain -/

section Chain

variable {κ : Type*} [Fintype κ] {T : SimpleGraph κ} {G : Hypergraph α β}
  {W : κ → Hypergraph α β} {N : Set κ} {s : ℕ → κ} {m w : ℕ}

/-- The sizes of the two sets of a good bag agree. -/
theorem IsGoodBag.ncard_eq {K : Hypergraph α β} {S S' : Set α} (h : IsGoodBag K S S') :
    S.ncard = S'.ncard := by
  rcases h with ⟨h1, h2⟩ | ⟨-, X, v, v', g, -, -, -, hvX, hv'X, h1, h2⟩
  · rw [h1, h2]
  · rw [h1, h2]
    by_cases hXf : X.Finite
    · rw [ncard_insert_of_notMem hvX hXf, ncard_insert_of_notMem hv'X hXf]
    · rw [(Set.Infinite.mono (subset_insert v X) hXf).ncard,
        (Set.Infinite.mono (subset_insert v' X) hXf).ncard]

/-- **A run gives a chain.** In a tree-decomposition with each edge in one bag, and with every
vertex outside `N` good, the union of the bags at the inner vertices of a run, without the
vertices of the bags at `N`, is a `(w + 1)`-chain. -/
theorem IsRun.isChain [Nonempty β] (hTD : GM10.IsTreeDecomposition G T W)
    (hgood : ∀ z ∉ N, GoodAt T W z) (hw : ∀ t, (W t).vertexSet.ncard ≤ w + 1)
    (hr : IsRun T N s m) :
    IsChain ((bagUnion W (· ∈ runSet s m)).deleteVertices (bagUnion W (· ∈ N)).vertexSet)
      (w + 1) := by
  classical
  have hT := hTD.isTree
  have h21 := hTD.isTreeDecomp21
  set A : ℕ → Hypergraph α β := fun j ↦ GM10.treeDecompSide T W s(s j, s (j + 1)) (s j) with hA
  set B : ℕ → Hypergraph α β := fun j ↦ GM10.treeDecompSide T W s(s j, s (j + 1)) (s (j + 1))
    with hB
  have hadj : ∀ j ≤ m, T.Adj (s j) (s (j + 1)) := fun j hj ↦ hr.seq.adj j (by omega)
  have hsep : ∀ j ≤ m, G.IsSeparation (A j) (B j) := fun j hj ↦
    hTD.isSeparation_treeDecompSide (hadj j hj)
  have hmid : ∀ j ≤ m, (A j ∩ B j).vertexSet =
      (W (s j)).vertexSet ∩ (W (s (j + 1))).vertexSet := fun j hj ↦ h21.treeEdgeSet_eq (hadj j hj)
  -- The bag at the inner vertex `s (j + 1)`.
  have hnb : ∀ j < m, ∀ z, T.Adj (s (j + 1)) z → z = s j ∨ z = s (j + 2) := by
    intro j hj z hz
    have := hr.nbr (j + 1) (by omega) (by omega) z hz
    simpa using this
  have hne : ∀ j < m, s j ≠ s (j + 2) := fun j hj h ↦ by
    have := hr.inj (by omega) (by omega) h
    omega
  have hbag : ∀ j < m, IsGoodBag (W (s (j + 1)))
      ((W (s (j + 1))).vertexSet ∩ (W (s j)).vertexSet)
      ((W (s (j + 1))).vertexSet ∩ (W (s (j + 2))).vertexSet) := fun j hj ↦
    (hgood _ (hr.inner (j + 1) (by omega) (by omega))).isGoodBag (hadj j (by omega)).symm
      (hadj (j + 1) (by omega)) (hne j hj)
  set k := (A 0 ∩ B 0).vertexSet.ncard with hk
  have hord : ∀ j ≤ m, (A j ∩ B j).vertexSet.ncard = k := by
    intro j
    induction j with
    | zero => intro _; rfl
    | succ j ih =>
      intro hj
      rw [← ih (by omega), hmid (j + 1) hj, hmid j (by omega),
        Set.inter_comm (W (s j)).vertexSet]
      exact ((hbag j (by omega)).ncard_eq).symm
  have hmono : ∀ j < m, A j ≤ A (j + 1) ∧ B (j + 1) ≤ B j := fun j hj ↦
    GM10.treeDecompSide_le_of_distinct_edges hTD (hadj j (by omega)) (hadj (j + 1) (by omega))
      (Reachable.refl _) (reachable_seq_left hr.seq (i := j) (j := j + 1) (by omega) (by omega))
  have hstep : ∀ j < m, IsChainStep' k (A j) (B j) (A (j + 1)) (B (j + 1)) ∧
      (B j ∩ A (j + 1)).vertexSet ⊆ (A j ∩ B j).vertexSet ∪ (A (j + 1) ∩ B (j + 1)).vertexSet := by
    intro j hj
    refine isChainStep'_of_isGoodBag
      (treeDecompSide_inter_eq hTD (hadj j (by omega)).symm (hadj (j + 1) (by omega)) (hne j hj)
        (hnb j hj)) (by rw [hmid j (by omega), Set.inter_comm]) (hmid (j + 1) hj) (hbag j hj) ?_
      (((W (s (j + 1))).vertexSet_finite).subset inter_subset_left)
    rw [Set.inter_comm, ← hmid j (by omega)]
    exact hord j (by omega)
  have hU := uniqSystem_of_steps m A B hsep hord hmono hstep
  have hch := hU.isChain_deleteVertices (A 0 ∩ B 0).vertexSet_finite
    (A m ∩ B m).vertexSet_finite rfl (hord m le_rfl)
  have hkw : k ≤ w + 1 := by
    rw [hk, hmid 0 (Nat.zero_le m)]
    exact (ncard_le_ncard inter_subset_left (W _).vertexSet_finite).trans (hw _)
  refine IsChain.mono ?_ hkw
  convert hch using 1
  -- The two hypergraphs agree.
  set D := (bagUnion W (· ∈ N)).vertexSet with hD
  set SLR := (A 0 ∩ B 0).vertexSet ∪ (A m ∩ B m).vertexSet with hSLR
  have hbagG : bagUnion W (· ∈ runSet s m) ≤ G := GM10.biUnion_le_of_le fun t _ ↦ hTD.le t
  have hKG : B 0 ∩ A m ≤ G := GM10.inter_le (treeDecompSide_le hTD _ _) (treeDecompSide_le hTD _ _)
  have hSLR : SLR ⊆ D := by
    rintro y (hy | hy)
    · rw [hmid 0 (Nat.zero_le m)] at hy
      exact mem_bagUnion_vertexSet.2 ⟨s 0, hr.first, hy.1⟩
    · rw [hmid m le_rfl] at hy
      exact mem_bagUnion_vertexSet.2 ⟨s (m + 1), hr.last, hy.2⟩
  -- A vertex of an inner bag that is in a bag at `N` is in `S ∪ S'`.
  have hbad : ∀ z ∈ runSet s m, ∀ y ∈ (W z).vertexSet, y ∈ D → y ∈ SLR := by
    intro z hz y hyz hyD
    obtain ⟨x, hxN, hyx⟩ := mem_bagUnion_vertexSet.1 hyD
    have hxI : x ∉ runSet s m := fun h ↦ hr.notMem_of_mem h hxN
    have hle : ∀ t, GM10.OnTreePath T z x t → y ∈ (W t).vertexSet := fun t ht ↦
      (hTD.inter_le ht).vertexSet_subset ⟨hyz, hyx⟩
    rcases hr.exit hT hz hxI with h | h
    · left
      rw [hmid 0 (Nat.zero_le m)]
      exact ⟨hle _ h.onTreePath_right, hle _ h.onTreePath_left⟩
    · right
      rw [hmid m le_rfl]
      exact ⟨hle _ h.onTreePath_left, hle _ h.onTreePath_right⟩
  -- The sides of the first and the last edge.
  have hside₁ : ∀ r, (T.deleteEdges {s(s 0, s (0 + 1))}).Reachable (s (0 + 1)) r ↔
      ¬ Thomas.OnTreePath T (s 1) r (s 0) := by
    intro r
    rw [Sym2.eq_swap]
    exact reachable_deleteEdges_iff hT (hadj 0 (Nat.zero_le m)).symm r
  have hside₂ : ∀ r, (T.deleteEdges {s(s m, s (m + 1))}).Reachable (s m) r ↔
      ¬ Thomas.OnTreePath T (s m) r (s (m + 1)) := fun r ↦
    reachable_deleteEdges_iff hT (hadj m le_rfl) r
  have hinI₁ : ∀ z ∈ runSet s m, (T.deleteEdges {s(s 0, s (0 + 1))}).Reachable (s (0 + 1)) z :=
    fun z hz ↦ (hside₁ z).2 (hr.not_onTreePath_first hT hz)
  have hinI₂ : ∀ z ∈ runSet s m, (T.deleteEdges {s(s m, s (m + 1))}).Reachable (s m) z :=
    fun z hz ↦ (hside₂ z).2 (hr.not_onTreePath_last hT hz)
  have h1I : s 1 ∈ runSet s m := ⟨1, le_rfl, hr.one_le, rfl⟩
  -- Incidence in a subgraph is incidence in `G`.
  have hinc : ∀ {K : Hypergraph α β}, K ≤ G → ∀ {f : β}, f ∈ K.edgeSet → ∀ y,
      K.Inc f y ↔ G.Inc f y := by
    intro K hK f hf y
    change y ∈ K.ends f ↔ y ∈ G.ends f
    rw [hK.ends_eq f hf]
  refine GM10.eq_of_le_of_vertexSet_eq_of_edgeSet_eq
    ((GM10.deleteVertices_le _ _).trans hbagG) ((GM10.deleteVertices_le _ _).trans hKG) ?_ ?_
  · ext y
    change y ∈ (bagUnion W (· ∈ runSet s m)).vertexSet \ D ↔ y ∈ (B 0 ∩ A m).vertexSet \ SLR
    constructor
    · rintro ⟨hy, hyD⟩
      obtain ⟨z, hz, hyz⟩ := mem_bagUnion_vertexSet.1 hy
      exact ⟨⟨mem_treeDecompSide_vertexSet.2 ⟨z, hinI₁ z hz, hyz⟩,
        mem_treeDecompSide_vertexSet.2 ⟨z, hinI₂ z hz, hyz⟩⟩, fun h ↦ hyD (hSLR h)⟩
    · rintro ⟨⟨hy1, hy2⟩, hyS⟩
      obtain ⟨r, hr1, hyr⟩ := mem_treeDecompSide_vertexSet.1 hy1
      obtain ⟨r', hr2, hyr'⟩ := mem_treeDecompSide_vertexSet.1 hy2
      -- `y` is in the bag of an inner vertex.
      obtain ⟨z, hz, hyz⟩ : ∃ z ∈ runSet s m, y ∈ (W z).vertexSet := by
        by_cases hrI : r ∈ runSet s m
        · exact ⟨r, hrI, hyr⟩
        by_cases hr'I : r' ∈ runSet s m
        · exact ⟨r', hr'I, hyr'⟩
        exact ⟨s 1, h1I, (hTD.inter_le (hr.onTreePath_one hT ((hside₁ r).1 hr1) ((hside₂ r').1 hr2)
          hr'I)).vertexSet_subset ⟨hyr, hyr'⟩⟩
      exact ⟨mem_bagUnion_vertexSet.2 ⟨z, hz, hyz⟩, fun hyD ↦ hyS (hbad z hz y hyz hyD)⟩
  · ext f
    change f ∈ {e ∈ (bagUnion W (· ∈ runSet s m)).edgeSet |
        ∀ v ∈ D, ¬ (bagUnion W (· ∈ runSet s m)).Inc e v} ↔
      f ∈ {e ∈ (B 0 ∩ A m).edgeSet | ∀ v ∈ SLR, ¬ (B 0 ∩ A m).Inc e v}
    constructor
    · rintro ⟨hf, hfD⟩
      obtain ⟨z, hz, hfz⟩ := mem_bagUnion_edgeSet.1 hf
      have hfK : f ∈ (B 0 ∩ A m).edgeSet := ⟨mem_treeDecompSide_edgeSet.2 ⟨z, hinI₁ z hz, hfz⟩,
        mem_treeDecompSide_edgeSet.2 ⟨z, hinI₂ z hz, hfz⟩⟩
      refine ⟨hfK, fun v hv hinc' ↦ hfD v (hSLR hv) ?_⟩
      rw [hinc hbagG hf]
      rwa [hinc hKG hfK] at hinc'
    · rintro ⟨hf, hfS⟩
      obtain ⟨r, hr1, hfr⟩ := mem_treeDecompSide_edgeSet.1 hf.1
      obtain ⟨r', hr2, hfr'⟩ := mem_treeDecompSide_edgeSet.1 hf.2
      have hrr : r = r' := by
        by_contra hrr
        have := hTD.edgeSet_inter_eq hrr
        exact (eq_empty_iff_forall_notMem.1 this) f ⟨hfr, hfr'⟩
      subst hrr
      have hrI : r ∈ runSet s m := by
        by_contra hrI
        have := hr.onTreePath_one hT ((hside₁ r).1 hr1) ((hside₂ r).1 hr2) hrI
        rw [Thomas.onTreePath_self] at this
        exact hrI (this ▸ h1I)
      have hfb : f ∈ (bagUnion W (· ∈ runSet s m)).edgeSet := mem_bagUnion_edgeSet.2 ⟨r, hrI, hfr⟩
      refine ⟨hfb, fun v hv hinc' ↦ ?_⟩
      rw [hinc hbagG hfb] at hinc'
      have hvr : v ∈ (W r).vertexSet := by
        have : v ∈ (W r).ends f := by rw [← (hTD.le r).ends_eq f hfr]; exact hinc'
        exact (W r).vertex_mem_of_inc this
      refine hfS v (hbad r hrI v hvr hv) ?_
      rw [hinc hKG hf]
      exact hinc'

end Chain

end GM21
end GraphMinor
