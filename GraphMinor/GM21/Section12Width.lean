module

public import GraphMinor.GM21.Section12Link

/-!
# Graph Minors XXI, (12.2): width

Step (3) of the proof of (12.2): `(T*, W*)` has width `≤ w`.

The bags of `T*` from `T₁` and `T₂` are bags of `T`. An inner bag `W'(t)` of `P` has at most
`k + 1` vertices, which is enough when `k ≤ w`. If `k = w + 1`, then by step (2) all bags along the
path `Q` of `T` from `f₁` to `f₂` have the same vertex set, so `W(f₁) = W(f₂)`, and then every
`W'(e)` equals `W(f₁)`, and the inner bags have at most `k` vertices.

The paper's bound `|V(W'(t))| ≤ k + 1` uses that every vertex of an inner bag `W'(t)` is in `W'(e)`
for an edge `e` of `P` at `t`. Statements (i)–(iii) of (12.1) do not say this, so we assume it
(hypothesis `hiv`). See the correction to (12.2) in `corrections/GM21.md`.
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace GraphMinor
namespace GM21

open Set SimpleGraph Hypergraph

universe u v

variable {α : Type u} {β : Type v}

/-- Along a walk of `T` all of whose edges `e` have `|W(e)| ≥ k`, in a tree-decomposition whose
bags have at most `k` vertices, all bags have the same vertex set. For an edge `xy`, the set `W(xy)`
is `V(W(x)) ∩ V(W(y))`, which has at least `k` vertices, so it equals both `V(W(x))` and
`V(W(y))`. -/
theorem vertexSet_eq_of_walk {ι : Type*} [Fintype ι] {T : SimpleGraph ι} {G : Hypergraph α β}
    {W : ι → Hypergraph α β} (h : IsTreeDecomp21 G T W) {k : ℕ}
    (hbag : ∀ t, (W t).vertexSet.ncard ≤ k) {u v : ι} (p : T.Walk u v)
    (hp : ∀ x y, s(x, y) ∈ p.edges → k ≤ (treeEdgeSet T W x y).ncard) :
    (W u).vertexSet = (W v).vertexSet := by
  induction p with
  | nil => rfl
  | @cons u x v hux p ih =>
    have hk := hp u x (by simp)
    rw [h.treeEdgeSet_eq hux] at hk
    have h1 : (W u).vertexSet ∩ (W x).vertexSet = (W u).vertexSet :=
      eq_of_subset_of_ncard_le inter_subset_left ((hbag u).trans hk) (W u).vertexSet_finite
    have h2 : (W u).vertexSet ∩ (W x).vertexSet = (W x).vertexSet :=
      eq_of_subset_of_ncard_le inter_subset_right ((hbag x).trans hk) (W x).vertexSet_finite
    rw [← h1, h2]
    exact ih fun y z hyz ↦ hp y z (by simp [hyz])

section Width

variable {ι : Type*} [Fintype ι] {T : SimpleGraph ι} {a₁ c₁ c₂ a₂ : ι} {m : ℕ}
  {G : Hypergraph α β} {W : ι → Hypergraph α β} {W' : Fin (m + 2) → Hypergraph α β}

variable (hT : T.IsTree) (he₁ : T.Adj a₁ c₁) (he₂ : T.Adj c₂ a₂) (hne : s(a₁, c₁) ≠ s(c₂, a₂))
  (h0 : (cutTwo T a₁ c₁ c₂ a₂).Reachable c₁ c₂)
  (h : IsTreeDecomp21 G T W) (hP : IsTreeDecomp21 G (pathGraph (m + 2)) W')
  (hA : W' 0 = bagUnion W ((cutTwo T a₁ c₁ c₂ a₂).Reachable a₁))
  (hB : bagUnion W' (· ≠ 0) = bagUnion W (fun t ↦ ¬ (cutTwo T a₁ c₁ c₂ a₂).Reachable a₁ t))
  (hA' : bagUnion W' (· ≠ Fin.last (m + 1)) =
    bagUnion W (fun t ↦ ¬ (cutTwo T a₁ c₁ c₂ a₂).Reachable a₂ t))
  (hB' : W' (Fin.last (m + 1)) = bagUnion W ((cutTwo T a₁ c₁ c₂ a₂).Reachable a₂))
  {k : ℕ} (hii : ∀ i, (pEdge W' i).ncard = k) (hstep : ∀ j, PStep W' k j)

include hT he₁ he₂ hne h0 h hP hA hB hA' hB' hii hstep in
/-- **Step (3) of the proof of (12.2).** `(T*, W*)` has width `≤ w`. -/
theorem width_splice {w : ℕ} (hw : ∀ t, (W t).vertexSet.ncard ≤ w + 1)
    (hiv : ∀ j : Fin m, (W' j.succ.castSucc).vertexSet ⊆ pEdge W' j.castSucc ∪ pEdge W' j.succ)
    (t : joinSet T a₁ c₁ c₂ a₂ ⊕ Fin m) :
    (spliceBag T a₁ c₁ c₂ a₂ m W W' t).vertexSet.ncard ≤ w + 1 := by
  rcases t with x | j
  · exact hw x.1
  change (W' j.succ.castSucc).vertexSet.ncard ≤ w + 1
  have hS₁ := treeEdgeSet_e₁_eq hT he₁ he₂ hne h0 h hP hA hB
  have hS₂ := treeEdgeSet_e₂_eq hT he₁ he₂ hne h0 h hP hA' hB'
  -- `k ≤ w + 1`, since `W(f₁) ⊆ V(W(a₁))`.
  have hka : treeEdgeSet T W a₁ c₁ ⊆ (W a₁).vertexSet := by
    rw [h.treeEdgeSet_eq he₁]; exact inter_subset_left
  have hkw : k ≤ w + 1 := by
    rw [← hii 0, ← hS₁]
    exact (ncard_le_ncard hka (W a₁).vertexSet_finite).trans (hw a₁)
  -- The inner bag has at most `k + 1` vertices, by (12.1)(iii) and `hiv`.
  have hV : (W' j.succ.castSucc).vertexSet.ncard ≤ k + 1 := by
    rcases hstep j with heq | ⟨X, v, v', g, -, -, hX, h1, h2⟩
    · have := hiv j
      rw [← heq, union_self] at this
      rw [← hii j.castSucc]
      exact (ncard_le_ncard this (pEdge_finite _)).trans (Nat.le_succ _)
    · have hsub : (W' j.succ.castSucc).vertexSet ⊆ insert v (insert v' X) := by
        refine (hiv j).trans ?_
        rw [h1, h2]
        rintro y (hy | hy) <;> simp only [mem_insert_iff] at hy ⊢ <;> tauto
      have hXf : X.Finite := by
        have := pEdge_finite (W' := W') j.succ
        rw [h2] at this
        exact this.subset (subset_insert _ _)
      refine (ncard_le_ncard hsub ((hXf.insert _).insert _)).trans ?_
      refine (ncard_insert_le _ _).trans ?_
      have := ncard_insert_le v' X
      omega
  rcases Nat.lt_or_ge k (w + 1) with hk | hk
  · omega
  obtain rfl : k = w + 1 := le_antisymm hkw hk
  -- Now `k = w + 1`. All bags along `Q` have the same vertex set, by step (2).
  have hbag : (W a₁).vertexSet = (W a₂).vertexSet := by
    refine vertexSet_eq_of_walk h hw (Thomas.treePath hT a₁ a₂) fun x y hxy ↦ ?_
    refine le_ncard_of_onTreePathEdge_a₁_a₂ hT he₁ he₂ hne h0 h hP hA hB hA' hB' hii hstep ?_
    exact (Thomas.onTreePathEdge_iff_mem_treePath hT).2
      ⟨(Thomas.treePath hT a₁ a₂).adj_of_mem_edges hxy, hxy⟩
  -- So `W(f₁) = V(W(a₁)) = V(W(a₂)) ⊇ W(f₂)`.
  have hSa : treeEdgeSet T W a₁ c₁ = (W a₁).vertexSet :=
    eq_of_subset_of_ncard_le hka (by rw [hS₁, hii 0]; exact hw a₁) (W a₁).vertexSet_finite
  have hS₂a : treeEdgeSet T W c₂ a₂ ⊆ (W a₂).vertexSet := by
    rw [h.treeEdgeSet_eq he₂]; exact inter_subset_right
  have hSS : pEdge W' 0 = pEdge W' (Fin.last m) := by
    rw [← hS₁, ← hS₂]
    exact (eq_of_subset_of_ncard_le hS₂a (by rw [← hbag, ← hSa, hS₂, hS₁, hii, hii])
      (W a₂).vertexSet_finite).trans (hSa.trans hbag).symm |>.symm
  -- Every vertex of `W(f₁)` is in every bag of `P`, so `W'(e) = W(f₁)` for every edge `e` of `P`.
  have hall : ∀ i, pEdge W' i = pEdge W' 0 := by
    intro i
    refine (eq_of_subset_of_ncard_le (fun y hy ↦ ?_) (by rw [hii, hii]) (pEdge_finite _)).symm
    have hy0 : y ∈ (W' 0).vertexSet := hy.1
    have hyl : y ∈ (W' (Fin.last (m + 1))).vertexSet := by
      have : y ∈ pEdge W' (Fin.last m) := hSS ▸ hy
      exact this.2
    have hQ := isMemProp_vertex W W' y
    exact ⟨hQ.between hP hy0 hyl (Nat.zero_le _) (by simp),
      hQ.between hP hy0 hyl (Nat.zero_le _) (by simp; omega)⟩
  have := hiv j
  rw [hall j.castSucc, hall j.succ, union_self] at this
  rw [← hii 0]
  exact ncard_le_ncard this (pEdge_finite _)

end Width

/-! ## (12.2) -/

/-- For the edge of `P` between positions `i` and `i + 1`, `W'(e)` is `pEdge W' i`, in either
orientation. -/
theorem treeEdgeSet_pathGraph_eq {m : ℕ} {G : Hypergraph α β} {W' : Fin (m + 2) → Hypergraph α β}
    (hP : IsTreeDecomp21 G (pathGraph (m + 2)) W') (i : Fin (m + 1)) {t u : Fin (m + 2)}
    (ht : t.1 = i.1) (hu : u.1 = i.1 + 1) :
    treeEdgeSet (pathGraph (m + 2)) W' t u = pEdge W' i ∧
      treeEdgeSet (pathGraph (m + 2)) W' u t = pEdge W' i := by
  obtain rfl : t = i.castSucc := Fin.ext ht
  obtain rfl : u = i.succ := Fin.ext hu
  have hadj : (pathGraph (m + 2)).Adj i.castSucc i.succ := pathGraph_adj.2 (Or.inl (by simp))
  rw [hP.treeEdgeSet_eq hadj, hP.treeEdgeSet_eq hadj.symm, inter_comm (W' i.succ).vertexSet]
  exact ⟨rfl, rfl⟩

/-- **Graph Minors XXI, (12.2)**, in the form used by `theorem_12_2`. The tree `T*` is
`spliceTree T a₁ c₁ c₂ a₂ m` and its bags are `spliceBag T a₁ c₁ c₂ a₂ m W W'`. Hypothesis `hiv` is
added to the paper's statement (see the correction to (12.2) in `corrections/GM21.md`). -/
theorem theorem_12_2_proof {ι : Type*} [Fintype ι] {G : Hypergraph α β} {T : SimpleGraph ι}
    {W : ι → Hypergraph α β} (h : IsTreeDecomp21 G T W) (hL : IsLinkedTreeDecomp G T W) {w : ℕ}
    (hw : ∀ t, (W t).vertexSet.ncard ≤ w + 1) {a₁ c₁ c₂ a₂ : ι} (he₁ : T.Adj a₁ c₁)
    (he₂ : T.Adj c₂ a₂) (hne : s(a₁, c₁) ≠ s(c₂, a₂))
    (h0 : (cutTwo T a₁ c₁ c₂ a₂).Reachable c₁ c₂) {k : ℕ}
    {m : ℕ} {W' : Fin (m + 2) → Hypergraph α β} (hP : IsTreeDecomp21 G (pathGraph (m + 2)) W')
    (hA : W' 0 = bagUnion W ((cutTwo T a₁ c₁ c₂ a₂).Reachable a₁))
    (hB : bagUnion W' (· ≠ 0) = bagUnion W (fun t ↦ ¬ (cutTwo T a₁ c₁ c₂ a₂).Reachable a₁ t))
    (hA' : bagUnion W' (· ≠ Fin.last (m + 1)) =
      bagUnion W (fun t ↦ ¬ (cutTwo T a₁ c₁ c₂ a₂).Reachable a₂ t))
    (hB' : W' (Fin.last (m + 1)) = bagUnion W ((cutTwo T a₁ c₁ c₂ a₂).Reachable a₂))
    (hii : ∀ t u, (pathGraph (m + 2)).Adj t u →
      (treeEdgeSet (pathGraph (m + 2)) W' t u).ncard = k)
    (hiii : ∀ t : Fin (m + 2), t ≠ 0 → t ≠ Fin.last (m + 1) → ∃ g, (W' t).edgeSet = {g} ∧
      ∀ u u', (pathGraph (m + 2)).Adj t u → (pathGraph (m + 2)).Adj t u' → u ≠ u' →
        (treeEdgeSet (pathGraph (m + 2)) W' t u = (W' t).vertexSet ∧
          treeEdgeSet (pathGraph (m + 2)) W' t u' = (W' t).vertexSet) ∨
        ∃ X : Set α, ∃ v v' : α,
          treeEdgeSet (pathGraph (m + 2)) W' t u ∩ treeEdgeSet (pathGraph (m + 2)) W' t u' = X ∧
          X.ncard = k - 1 ∧ (W' t).ends g = {v, v'} ∧
          treeEdgeSet (pathGraph (m + 2)) W' t u = insert v X ∧
          treeEdgeSet (pathGraph (m + 2)) W' t u' = insert v' X)
    (hiv : ∀ t : Fin (m + 2), t ≠ 0 → t ≠ Fin.last (m + 1) → ∀ y ∈ (W' t).vertexSet,
      ∃ u, (pathGraph (m + 2)).Adj t u ∧ y ∈ treeEdgeSet (pathGraph (m + 2)) W' t u) :
    IsTreeDecomp21 G (spliceTree T a₁ c₁ c₂ a₂ m) (spliceBag T a₁ c₁ c₂ a₂ m W W') ∧
      IsLinkedTreeDecomp G (spliceTree T a₁ c₁ c₂ a₂ m) (spliceBag T a₁ c₁ c₂ a₂ m W W') ∧
      ∀ t, (spliceBag T a₁ c₁ c₂ a₂ m W W' t).vertexSet.ncard ≤ w + 1 := by
  have hT := h.isTree
  -- (12.1)(ii) in terms of `pEdge`.
  have hk : ∀ i, (pEdge W' i).ncard = k := by
    intro i
    rw [← (treeEdgeSet_pathGraph_eq hP i (t := i.castSucc) (u := i.succ) rfl (by simp)).1]
    exact hii _ _ (pathGraph_adj.2 (Or.inl (by simp)))
  -- At the inner vertex `j + 1`, the left edge is `pEdge j.castSucc`, the right one `pEdge j.succ`.
  have hL' : ∀ j : Fin m, treeEdgeSet (pathGraph (m + 2)) W' j.succ.castSucc j.castSucc.castSucc =
      pEdge W' j.castSucc :=
    fun j ↦ (treeEdgeSet_pathGraph_eq hP j.castSucc (t := j.castSucc.castSucc) rfl (by simp)).2
  have hR' : ∀ j : Fin m, treeEdgeSet (pathGraph (m + 2)) W' j.succ.castSucc j.succ.succ =
      pEdge W' j.succ :=
    fun j ↦ (treeEdgeSet_pathGraph_eq hP j.succ (u := j.succ.succ) (by simp) (by simp)).1
  have hin0 : ∀ j : Fin m, j.succ.castSucc ≠ 0 := fun j h' ↦ by simp [Fin.ext_iff] at h'
  have hinl : ∀ j : Fin m, j.succ.castSucc ≠ Fin.last (m + 1) := fun j h' ↦ by
    simp [Fin.ext_iff] at h'; omega
  have hadjL : ∀ j : Fin m, (pathGraph (m + 2)).Adj j.succ.castSucc j.castSucc.castSucc :=
    fun j ↦ pathGraph_adj.2 (Or.inr (by simp))
  have hadjR : ∀ j : Fin m, (pathGraph (m + 2)).Adj j.succ.castSucc j.succ.succ :=
    fun j ↦ pathGraph_adj.2 (Or.inl (by simp))
  -- (12.1)(iii) in terms of `pEdge`.
  have hstep : ∀ j, PStep W' k j := by
    intro j
    obtain ⟨g, hg, hcase⟩ := hiii _ (hin0 j) (hinl j)
    rcases hcase _ _ (hadjL j) (hadjR j) (fun h' ↦ by simp [Fin.ext_iff] at h'; omega)
      with ⟨h1, h2⟩ | ⟨X, v, v', -, hX, hends, h1, h2⟩
    · left
      rw [← hL', ← hR', h1, h2]
    · right
      rw [hL'] at h1
      rw [hR'] at h2
      refine ⟨X, v, v', g, by rw [hg]; rfl, hends, ?_, h1, h2⟩
      have hXf : X.Finite := ((pEdge_finite (W' := W') j.castSucc).subset
        (by rw [h1]; exact subset_insert _ _))
      have hvX : v ∉ X := by
        intro hv
        rw [insert_eq_of_mem hv] at h1
        have := hk j.castSucc
        rw [h1] at this
        have hk0 : k = 0 := by omega
        subst hk0
        exact (ncard_eq_zero hXf).1 hX |>.subset hv
      have := hk j.castSucc
      rw [h1, ncard_insert_of_notMem hvX hXf] at this
      exact this
  -- The hypothesis `hiv` of the corrected (12.2), in terms of `pEdge`.
  have hiv' : ∀ j : Fin m,
      (W' j.succ.castSucc).vertexSet ⊆ pEdge W' j.castSucc ∪ pEdge W' j.succ := by
    intro j y hy
    obtain ⟨u, hu, hyu⟩ := hiv _ (hin0 j) (hinl j) y hy
    rcases pathGraph_adj.1 hu with hu | hu
    · obtain rfl : u = j.succ.succ := Fin.ext (by simp at hu ⊢; omega)
      exact Or.inr (hR' j ▸ hyu)
    · obtain rfl : u = j.castSucc.castSucc := Fin.ext (by simp at hu ⊢; omega)
      exact Or.inl (hL' j ▸ hyu)
  exact ⟨isTreeDecomp21_splice hT he₁ he₂ hne h0 h hP hA hB hA' hB',
    isLinkedTreeDecomp_splice hT he₁ he₂ hne h0 h hP hA hB hA' hB' hL hk hstep,
    width_splice hT he₁ he₂ hne h0 h hP hA hB hA' hB' hk hstep hw hiv'⟩

end GM21
end GraphMinor
