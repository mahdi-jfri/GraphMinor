module

public import GraphMinor.GM21.Section12Two
public import GraphMinor.GM21.Section12Menger
import GraphMinor.GM21.Section11Two

/-!
# Graph Minors XXI, (12.2): linkedness and width

The second half of the proof of (12.2). The sets `W'(e)` for the edges `e` of `P` are
`pEdge W' i` (the edge between positions `i` and `i + 1`).

* `hasDisjointPaths_pEdge`: there are `k` disjoint paths between `W'(e)` and `W'(e')` for any two
  edges `e, e'` of `P`. This is the paper's "If $e_1, e_2 \in E(P)$ this is clear", and gives (1).
  We go along `P` one bag at a time: by (12.1)(iii) each inner bag carries `k` disjoint paths from
  the set of its left edge to the set of its right edge (`hasDisjointPaths_insert`), and the paths
  are paired through the separation at each edge of `P` (`hasDisjointPaths_trans`).
* `le_ncard_of_onTreePathEdge_a₁_a₂`: step (2).
* `hasDisjointPaths_side₁`: the paths from an edge of `T₁` to `f₁`, given by linkedness of `T`.
* `isLinkedTreeDecomp_splice`: `(T*, W*)` is linked, by the paper's case analysis.
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace GraphMinor
namespace GM21

open Set SimpleGraph Hypergraph

universe u v

variable {α : Type u} {β : Type v}

/-! ## Paths in trees -/

section TreePaths

variable {ι : Type*} {T : SimpleGraph ι}

/-- A vertex on the path between two vertices of the path from `a` to `b` is on the path from `a`
to `b`. -/
theorem onTreePath_of_onTreePath_of_onTreePath (hT : T.IsTree) {a b x z w : ι}
    (hx : Thomas.OnTreePath T a b x) (hz : Thomas.OnTreePath T a b z)
    (hw : Thomas.OnTreePath T x z w) : Thomas.OnTreePath T a b w := by
  rcases (Thomas.onTreePath_split_iff hT hx).1 hz with h | h
  · -- `z` is between `a` and `x`.
    exact Thomas.onTreePath_trans_left hT hx
      (Thomas.onTreePath_trans_right hT h (Thomas.onTreePath_symm hw))
  · exact Thomas.onTreePath_trans_right hT hx (Thomas.onTreePath_trans_left hT h hw)

/-- **Linkedness without orientation.** If `(T, W)` is linked, `|W(uv)| = |W(u'v')| = k`, and every
edge on a path of `T` from an end of `uv` to an end of `u'v'` has `|W(e)| ≥ k`, then there are `k`
disjoint paths between `W(uv)` and `W(u'v')`. -/
theorem hasDisjointPaths_of_linked [Fintype ι] {G : Hypergraph α β} {W : ι → Hypergraph α β}
    (h : IsTreeDecomp21 G T W) (hL : IsLinkedTreeDecomp G T W) {u v u' v' : ι} (huv : T.Adj u v)
    (hu'v' : T.Adj u' v') {k : ℕ} (hk : (treeEdgeSet T W u v).ncard = k)
    (hk' : (treeEdgeSet T W u' v').ncard = k)
    (hmin : ∀ x z, (x = u ∨ x = v) → (z = u' ∨ z = v') → ∀ s s',
      Thomas.OnTreePathEdge T x z s s' → k ≤ (treeEdgeSet T W s s').ncard) :
    HasDisjointPaths G.skeleton (treeEdgeSet T W u v) (treeEdgeSet T W u' v') k := by
  have hT := h.isTree
  -- Orient `uv` as `a b` with `b` on the path from `a` to `u'`.
  obtain ⟨a, b, hab, hsab, ha, hb⟩ : ∃ a b, T.Adj a b ∧
      treeEdgeSet T W a b = treeEdgeSet T W u v ∧ (a = u ∨ a = v) ∧
      Thomas.OnTreePath T a u' b := by
    rcases Thomas.onTreePath_adj_dichotomy hT huv u' with ⟨h1, -⟩ | ⟨h1, -⟩
    · exact ⟨v, u, huv.symm, treeEdgeSet_comm h huv.symm, Or.inr rfl, Thomas.onTreePath_symm h1⟩
    · exact ⟨u, v, huv, rfl, Or.inl rfl, Thomas.onTreePath_symm h1⟩
  -- Orient `u'v'` as `c d` with `c` on the path from `a` to `d`.
  obtain ⟨c, d, hcd, hscd, hd, hc, hbd⟩ : ∃ c d, T.Adj c d ∧
      treeEdgeSet T W c d = treeEdgeSet T W u' v' ∧ (d = u' ∨ d = v') ∧
      Thomas.OnTreePath T a d c ∧ Thomas.OnTreePath T a d b := by
    rcases Thomas.onTreePath_adj_dichotomy hT hu'v' a with ⟨h1, -⟩ | ⟨h1, -⟩
    · exact ⟨u', v', hu'v', rfl, Or.inr rfl, h1, Thomas.onTreePath_trans_left hT h1 hb⟩
    · exact ⟨v', u', hu'v'.symm, treeEdgeSet_comm h hu'v'.symm, Or.inl rfl, h1, hb⟩
  rw [← hsab, ← hscd]
  exact hL hab hcd hbd hc k (by rw [hsab]; exact hk) (by rw [hscd]; exact hk')
    fun s s' hss ↦ hmin a d ha hd s s' hss

end TreePaths

/-! ## Disjoint paths along `P` -/

section PathPart

variable {m : ℕ} {G : Hypergraph α β} {W' : Fin (m + 2) → Hypergraph α β} {k : ℕ}

/-- `W'(e)` for the edge `e` of `P` between the positions `i` and `i + 1`. -/
def pEdge (W' : Fin (m + 2) → Hypergraph α β) (i : Fin (m + 1)) : Set α :=
  (W' i.castSucc).vertexSet ∩ (W' i.succ).vertexSet

/-- Statement (iii) of (12.1) at the inner vertex `j + 1` of `P`, for the two edges at it: either
(a) the two sets `W'(e)` are equal, or (b) they are `X ∪ {v}` and `X ∪ {v'}` with `|X| = k - 1`,
where `vv'` is an edge of the bag. -/
def PStep (W' : Fin (m + 2) → Hypergraph α β) (k : ℕ) (j : Fin m) : Prop :=
  pEdge W' j.castSucc = pEdge W' j.succ ∨
    ∃ (X : Set α) (v v' : α) (g : β), g ∈ (W' j.succ.castSucc).edgeSet ∧
      (W' j.succ.castSucc).ends g = {v, v'} ∧ X.ncard + 1 = k ∧
      pEdge W' j.castSucc = insert v X ∧ pEdge W' j.succ = insert v' X

/-- In the path `pathGraph L` without the edge `uv`, where `v = u + 1`, the vertices up to `u` are
joined to `u`. -/
theorem pathGraph_reachable_left {L : ℕ} {u v t : Fin L} (huv : v.1 = u.1 + 1) (ht : t.1 ≤ u.1) :
    ((pathGraph L).deleteEdges {s(u, v)}).Reachable u t := by
  classical
  obtain ⟨p, hp⟩ := exists_bounded_walk_pathGraph t u ht
  refine (reachable_deleteEdges_iff_exists_walk.2 ⟨p, fun he ↦ ?_⟩).symm
  have := hp v (p.snd_mem_support_of_mem_edges he)
  omega

/-- In the path `pathGraph L` without the edge `uv`, where `v = u + 1`, the vertices from `v` on are
joined to `v`. -/
theorem pathGraph_reachable_right {L : ℕ} {u v t : Fin L} (huv : v.1 = u.1 + 1) (ht : v.1 ≤ t.1) :
    ((pathGraph L).deleteEdges {s(u, v)}).Reachable v t := by
  classical
  obtain ⟨p, hp⟩ := exists_bounded_walk_pathGraph v t ht
  refine reachable_deleteEdges_iff_exists_walk.2 ⟨p, fun he ↦ ?_⟩
  have := hp u (p.fst_mem_support_of_mem_edges he)
  omega

theorem pEdge_finite (i : Fin (m + 1)) : (pEdge W' i).Finite :=
  (W' i.castSucc).vertexSet_finite.inter_of_left _

/-- **Disjoint paths along `P`.** -/
theorem hasDisjointPaths_pEdge (hP : IsTreeDecomp21 G (pathGraph (m + 2)) W')
    (hk : ∀ i, (pEdge W' i).ncard = k) (hstep : ∀ j, PStep W' k j) (i j : Fin (m + 1)) :
    HasDisjointPaths G.skeleton (pEdge W' i) (pEdge W' j) k := by
  -- One step, inside the bag at position `j + 1`.
  have local_step : ∀ j : Fin m,
      HasDisjointPaths G.skeleton (pEdge W' j.castSucc) (pEdge W' j.succ) k := by
    intro j
    rcases hstep j with heq | ⟨X, v, v', g, hg, hends, hX, h1, h2⟩
    · rw [heq]
      exact hasDisjointPaths_self _ (pEdge_finite _) (hk _)
    · have hXf : X.Finite := (pEdge_finite j.castSucc).subset (h1 ▸ subset_insert v X)
      have hnot : ∀ {w : α}, (insert w X).ncard = k → w ∉ X := by
        intro w hw hwX
        rw [insert_eq_of_mem hwX] at hw
        omega
      rw [h1, h2]
      have hXG : X ⊆ G.vertexSet := fun x hx ↦ by
        have : x ∈ pEdge W' j.castSucc := h1 ▸ mem_insert_of_mem v hx
        exact (hP.le _).vertexSet_subset this.1
      refine hasDisjointPaths_insert (g := g) hXG hXf hX (hnot (h1 ▸ hk _)) (hnot (h2 ▸ hk _)) ?_
      rw [(hP.le _).ends_eq g hg, hends]
  -- The steps from `i` to `j ≥ i`.
  have main : ∀ n (i j : Fin (m + 1)), j.1 = i.1 + n →
      HasDisjointPaths G.skeleton (pEdge W' i) (pEdge W' j) k := by
    intro n
    induction n with
    | zero =>
      intro i j hij
      obtain rfl : i = j := Fin.ext (by omega)
      exact hasDisjointPaths_self _ (pEdge_finite _) (hk _)
    | succ n ih =>
      intro i j hij
      let j₀ : Fin m := ⟨j.1 - 1, by omega⟩
      have hj₀v : j₀.1 = j.1 - 1 := rfl
      have hj₀ : j₀.succ = j := Fin.ext (by simp only [Fin.val_succ]; omega)
      have h₁ := ih i j₀.castSucc (by simp only [Fin.val_castSucc]; omega)
      have h₂ := local_step j₀
      rw [hj₀] at h₂
      have hadj : (pathGraph (m + 2)).Adj j₀.castSucc.castSucc j₀.succ.castSucc :=
        pathGraph_adj.2 (Or.inl (by simp))
      obtain ⟨G₁, G₂, hs, hmid, hG₁, hG₂⟩ := exists_separation_of_treeDecomp hP hadj
      have hmid' : (G₁ ∩ G₂).vertexSet = pEdge W' j₀.castSucc := by
        rw [hmid, hP.treeEdgeSet_eq hadj]
        rfl
      rw [← hmid'] at h₁ h₂
      refine hasDisjointPaths_trans hs ?_ ?_ ?_ h₁ h₂
      · intro x hx
        refine hG₁ i.castSucc (pathGraph_reachable_left (by simp)
          (by simp only [Fin.val_castSucc]; omega)) hx.1
      · intro x hx
        refine hG₂ j.castSucc (pathGraph_reachable_right (by simp)
          (by simp only [Fin.val_castSucc, Fin.val_succ]; omega)) hx.1
      · rw [separationOrder, hmid', hk]
  rcases le_total i.1 j.1 with hij | hij
  · exact main (j.1 - i.1) i j (by omega)
  · exact HasDisjointPaths.symm (main (i.1 - j.1) j i (by omega))

end PathPart

/-! ## The sides `T₁` and `T₂` -/

section Sides

variable {ι : Type*} [Fintype ι] {T : SimpleGraph ι} {a₁ c₁ c₂ a₂ : ι} {G : Hypergraph α β}
  {W : ι → Hypergraph α β}

theorem cutTwo_swap : cutTwo T a₂ c₂ c₁ a₁ = cutTwo T a₁ c₁ c₂ a₂ := by
  simp only [cutTwo]
  rw [Set.pair_comm, Sym2.eq_swap (a := a₂), Sym2.eq_swap (a := c₁)]

variable (hT : T.IsTree) (he₁ : T.Adj a₁ c₁) (he₂ : T.Adj c₂ a₂) (hne : s(a₁, c₁) ≠ s(c₂, a₂))
  (h0 : (cutTwo T a₁ c₁ c₂ a₂).Reachable c₁ c₂)
  (h : IsTreeDecomp21 G T W) (hL : IsLinkedTreeDecomp G T W)

include hT he₁ he₂ hne h0 h hL in
/-- **From an edge of `T₁` to `f₁`.** Let `pq` be an edge of `T₁` with `|W(pq)| = |W(f₁)| = k`, such
that every edge on the path of `T` from `p` or `q` to `a₁` has `|W(e)| ≥ k`. Then there are `k`
disjoint paths between `W(pq)` and `W(f₁)`, since `(T, W)` is linked. -/
theorem hasDisjointPaths_side₁ {p q : ι} (hp : (cutTwo T a₁ c₁ c₂ a₂).Reachable a₁ p)
    (hq : (cutTwo T a₁ c₁ c₂ a₂).Reachable a₁ q) (hpq : T.Adj p q) {k : ℕ}
    (hk : (treeEdgeSet T W p q).ncard = k) (hk₁ : (treeEdgeSet T W a₁ c₁).ncard = k)
    (hpath : ∀ w, (w = p ∨ w = q) → ∀ s s', Thomas.OnTreePathEdge T w a₁ s s' →
      k ≤ (treeEdgeSet T W s s').ncard) :
    HasDisjointPaths G.skeleton (treeEdgeSet T W p q) (treeEdgeSet T W a₁ c₁) k := by
  refine hasDisjointPaths_of_linked h hL hpq he₁ hk hk₁ ?_
  intro w z hw hz s s' hss
  have hwR : (cutTwo T a₁ c₁ c₂ a₂).Reachable a₁ w := by rcases hw with rfl | rfl <;> assumption
  have hc₁ : ¬ (cutTwo T a₁ c₁ c₂ a₂).Reachable a₁ c₁ := not_reachable_a₁_c₁ hT he₁ he₂ hne h0
  -- `a₁` is on the path from `w` to `c₁`.
  have ha₁ : Thomas.OnTreePath T w c₁ a₁ :=
    (onTreePathEdge_e₁_of hT he₁ he₂ hne h0 hwR hc₁).onTreePath_left
  -- The path from `w` to `z` lies on the path from `w` to `c₁`.
  have hsub : ∀ r, Thomas.OnTreePath T w z r → Thomas.OnTreePath T w c₁ r := by
    intro r hr
    rcases hz with rfl | rfl
    · exact Thomas.onTreePath_trans_left hT ha₁ hr
    · exact hr
  -- Every vertex there is on the path from `w` to `a₁`, or is `c₁`.
  have hsplit : ∀ r, Thomas.OnTreePath T w z r → Thomas.OnTreePath T w a₁ r ∨ r = c₁ := by
    intro r hr
    rcases (Thomas.onTreePath_split_iff hT ha₁).1 (hsub r hr) with h' | h'
    · exact Or.inl h'
    · rcases eq_or_eq_of_onTreePath_adj he₁ h' with rfl | rfl
      · exact Or.inl (Thomas.onTreePath_right _ _ _)
      · exact Or.inr rfl
  -- A vertex of the path from `w` to `a₁` adjacent to `c₁` is `a₁`.
  have hnb : ∀ r, Thomas.OnTreePath T w a₁ r → T.Adj r c₁ → r = a₁ := by
    intro r hr hrc
    have hrR := reachable_of_onTreePath hT hwR (Reachable.refl _) hr
    rcases eq_of_adj_not_mem hT he₁ he₂ hne h0 hrc (Or.inl hrR)
      (c₁_not_mem hT he₁ he₂ hne h0) with h' | h'
    · exact h'
    · exact (not_reachable_a₁_a₂ hT he₁ he₂ hne h0 (h' ▸ hrR)).elim
  have hf₁ : (treeEdgeSet T W c₁ a₁).ncard = k := by rw [treeEdgeSet_comm h he₁.symm, hk₁]
  rcases hsplit s hss.onTreePath_left with hs | rfl <;>
    rcases hsplit s' hss.onTreePath_right with hs' | rfl
  · exact hpath w hw s s' (onTreePathEdge_of_onTreePath hT hss.1 hs hs')
  · rw [hnb s hs hss.1, hk₁]
  · rw [hnb s' hs' hss.1.symm, hf₁]
  · exact (hss.1.ne rfl).elim

include hT he₁ he₂ hne h0 h hL in
/-- **From an edge of `T₂` to `f₂`.** The same as `hasDisjointPaths_side₁`, with the roles of the
two sides exchanged. -/
theorem hasDisjointPaths_side₂ {p q : ι} (hp : (cutTwo T a₁ c₁ c₂ a₂).Reachable a₂ p)
    (hq : (cutTwo T a₁ c₁ c₂ a₂).Reachable a₂ q) (hpq : T.Adj p q) {k : ℕ}
    (hk : (treeEdgeSet T W p q).ncard = k) (hk₂ : (treeEdgeSet T W c₂ a₂).ncard = k)
    (hpath : ∀ w, (w = p ∨ w = q) → ∀ s s', Thomas.OnTreePathEdge T w a₂ s s' →
      k ≤ (treeEdgeSet T W s s').ncard) :
    HasDisjointPaths G.skeleton (treeEdgeSet T W p q) (treeEdgeSet T W c₂ a₂) k := by
  rw [treeEdgeSet_comm h he₂]
  have hne' : s(a₂, c₂) ≠ s(c₁, a₁) := by
    rw [Sym2.eq_swap (a := a₂), Sym2.eq_swap (a := c₁)]
    exact hne.symm
  rw [← cutTwo_swap] at hp hq h0
  exact hasDisjointPaths_side₁ hT he₂.symm he₁.symm hne' h0.symm h hL hp hq hpq hk
    (by rw [treeEdgeSet_comm h he₂.symm, hk₂]) hpath

end Sides

/-! ## `(T*, W*)` is linked -/

section Linked

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

include hT he₁ he₂ hne h0 h hA hB in
/-- A vertex of `W'(0) = A` that is in a later bag of `P` is in `W(a₁)` and `W(c₁)`. -/
theorem mem_a₁_c₁ {y : α} {j : Fin (m + 2)} (hj : j ≠ 0) (hy0 : y ∈ (W' 0).vertexSet)
    (hyj : y ∈ (W' j).vertexSet) : y ∈ (W a₁).vertexSet ∧ y ∈ (W c₁).vertexSet := by
  have hQ := isMemProp_vertex W W' y
  rw [hA, mem_bagUnion_vertexSet] at hy0
  obtain ⟨t, ht, hyt⟩ := hy0
  have hyB : y ∈ (bagUnion W' (· ≠ 0)).vertexSet := mem_bagUnion_vertexSet.2 ⟨j, hj, hyj⟩
  rw [hB, mem_bagUnion_vertexSet] at hyB
  obtain ⟨t', ht', hyt'⟩ := hyB
  have he := onTreePathEdge_e₁_of hT he₁ he₂ hne h0 ht ht'
  exact ⟨hQ.onPath h hyt hyt' he.onTreePath_left, hQ.onPath h hyt hyt' he.onTreePath_right⟩

include hT he₁ he₂ hne h0 h hA' hB' in
/-- A vertex of `W'(m + 1) = B'` that is in an earlier bag of `P` is in `W(a₂)` and `W(c₂)`. -/
theorem mem_a₂_c₂ {y : α} {j : Fin (m + 2)} (hj : j ≠ Fin.last (m + 1))
    (hyl : y ∈ (W' (Fin.last (m + 1))).vertexSet) (hyj : y ∈ (W' j).vertexSet) :
    y ∈ (W a₂).vertexSet ∧ y ∈ (W c₂).vertexSet := by
  have hQ := isMemProp_vertex W W' y
  rw [hB', mem_bagUnion_vertexSet] at hyl
  obtain ⟨t, ht, hyt⟩ := hyl
  have hyA : y ∈ (bagUnion W' (· ≠ Fin.last (m + 1))).vertexSet :=
    mem_bagUnion_vertexSet.2 ⟨j, hj, hyj⟩
  rw [hA', mem_bagUnion_vertexSet] at hyA
  obtain ⟨t', ht', hyt'⟩ := hyA
  have he := onTreePathEdge_e₂_of hT he₁ he₂ hne h0 ht' ht
  exact ⟨hQ.onPath h hyt' hyt he.onTreePath_right, hQ.onPath h hyt' hyt he.onTreePath_left⟩

include hT he₁ he₂ hne h0 h hP hA hB in
/-- `W(f₁) = W'(e)` for the first edge `e` of `P`. -/
theorem treeEdgeSet_e₁_eq : treeEdgeSet T W a₁ c₁ = pEdge W' 0 := by
  rw [h.treeEdgeSet_eq he₁]
  simp only [pEdge, Fin.castSucc_zero, Fin.succ_zero_eq_one]
  ext y
  refine ⟨fun ⟨ha, hc⟩ ↦ ?_, fun ⟨h0', h1'⟩ ↦ mem_a₁_c₁ hT he₁ he₂ hne h0 h hA hB
    (j := 1) (by simp) h0' h1'⟩
  have hQ := isMemProp_vertex W W' y
  have hy0 : y ∈ (W' 0).vertexSet := by
    rw [hA]
    exact mem_bagUnion_vertexSet.2 ⟨a₁, Reachable.refl _, ha⟩
  refine ⟨hy0, ?_⟩
  have hyB : y ∈ (bagUnion W fun t ↦ ¬ (cutTwo T a₁ c₁ c₂ a₂).Reachable a₁ t).vertexSet :=
    mem_bagUnion_vertexSet.2 ⟨c₁, not_reachable_a₁_c₁ hT he₁ he₂ hne h0, hc⟩
  rw [← hB, mem_bagUnion_vertexSet] at hyB
  obtain ⟨i, hi, hyi⟩ := hyB
  refine hQ.between hP hy0 hyi (by simp) ?_
  have : i.1 ≠ 0 := fun h' ↦ hi (Fin.ext h')
  simp
  omega

include hT he₁ he₂ hne h0 h hP hA' hB' in
/-- `W(f₂) = W'(e)` for the last edge `e` of `P`. -/
theorem treeEdgeSet_e₂_eq : treeEdgeSet T W c₂ a₂ = pEdge W' (Fin.last m) := by
  rw [h.treeEdgeSet_eq he₂]
  simp only [pEdge, Fin.succ_last]
  ext y
  refine ⟨fun ⟨hc, ha⟩ ↦ ?_, fun ⟨hm, hl⟩ ↦ (mem_a₂_c₂ hT he₁ he₂ hne h0 h hA' hB'
    (j := (Fin.last m).castSucc) (Fin.castSucc_lt_last _).ne hl hm).symm⟩
  have hQ := isMemProp_vertex W W' y
  have hyl : y ∈ (W' (Fin.last (m + 1))).vertexSet := by
    rw [hB']
    exact mem_bagUnion_vertexSet.2 ⟨a₂, Reachable.refl _, ha⟩
  refine ⟨?_, hyl⟩
  have hyA : y ∈ (bagUnion W fun t ↦ ¬ (cutTwo T a₁ c₁ c₂ a₂).Reachable a₂ t).vertexSet :=
    mem_bagUnion_vertexSet.2 ⟨c₂, fun h' ↦ not_reachable_a₂_c₁ hT he₁ he₂ hne h0
      (h'.trans h0.symm), hc⟩
  rw [← hA', mem_bagUnion_vertexSet] at hyA
  obtain ⟨i, hi, hyi⟩ := hyA
  refine hQ.between hP hyi hyl ?_ (by simp)
  have : i.1 ≠ m + 1 := fun h' ↦ hi (Fin.ext h')
  simp
  omega

include hT he₁ he₂ hne h0 h hP hA hB hA' hB' in
/-- `W*(e) = W'(e)` for the edge `e` of `P` at position `i`. -/
theorem treeEdgeSet_splice_spliceVert {i : ℕ} (hi : i ≤ m) :
    treeEdgeSet (spliceTree T a₁ c₁ c₂ a₂ m) (spliceBag T a₁ c₁ c₂ a₂ m W W')
      (spliceVert T a₁ c₁ c₂ a₂ m i) (spliceVert T a₁ c₁ c₂ a₂ m (i + 1)) =
      pEdge W' ⟨i, by omega⟩ := by
  have hD := isTreeDecomp21_splice hT he₁ he₂ hne h0 h hP hA hB hA' hB'
  rw [hD.treeEdgeSet_eq (spliceTree_adj_spliceVert hT he₁ he₂ hne h0 hi)]
  -- The bag at position `l`: inside `W'(l)`, and equal to it at an inner position.
  have hinner : ∀ l (h1 : 1 ≤ l) (h2 : l ≤ m),
      spliceBag T a₁ c₁ c₂ a₂ m W W' (spliceVert T a₁ c₁ c₂ a₂ m l) = W' ⟨l, by omega⟩ := by
    intro l h1 h2
    rw [spliceVert_of_le h1 h2]
    simp only [spliceBag]
    congr 2
    omega
  have hto : ∀ l (hl : l ≤ m + 1) y,
      y ∈ (spliceBag T a₁ c₁ c₂ a₂ m W W' (spliceVert T a₁ c₁ c₂ a₂ m l)).vertexSet →
      y ∈ (W' ⟨l, by omega⟩).vertexSet := by
    intro l hl y hy
    rcases Nat.eq_zero_or_pos l with rfl | hl0
    · rw [spliceVert_zero] at hy
      change y ∈ (W' 0).vertexSet
      rw [hA]
      exact mem_bagUnion_vertexSet.2 ⟨a₁, Reachable.refl _, hy⟩
    · rcases Nat.lt_or_ge m l with hlm | hlm
      · obtain rfl : l = m + 1 := by omega
        rw [spliceVert_succ_self] at hy
        change y ∈ (W' (Fin.last (m + 1))).vertexSet
        rw [hB']
        exact mem_bagUnion_vertexSet.2 ⟨a₂, Reachable.refl _, hy⟩
      · rwa [hinner l hl0 hlm] at hy
  ext y
  constructor
  · rintro ⟨hy1, hy2⟩
    exact ⟨hto i (by omega) y hy1, hto (i + 1) (by omega) y hy2⟩
  · rintro ⟨hy1, hy2⟩
    change y ∈ (W' ⟨i, by omega⟩).vertexSet at hy1
    change y ∈ (W' ⟨i + 1, by omega⟩).vertexSet at hy2
    constructor
    · rcases Nat.eq_zero_or_pos i with rfl | hi0
      · rw [spliceVert_zero]
        exact (mem_a₁_c₁ hT he₁ he₂ hne h0 h hA hB (j := ⟨1, by omega⟩)
          (fun h' ↦ by simp [Fin.ext_iff] at h') hy1 hy2).1
      · rw [hinner i hi0 hi]
        exact hy1
    · rcases Nat.lt_or_ge (i + 1) (m + 1) with him | him
      · rw [hinner (i + 1) (by omega) (by omega)]
        exact hy2
      · obtain rfl : i = m := by omega
        rw [spliceVert_succ_self]
        exact (mem_a₂_c₂ hT he₁ he₂ hne h0 h hA' hB' (j := ⟨i, by omega⟩)
          (fun h' ↦ by simp [Fin.ext_iff] at h') hy2 hy1).1

variable (hL : IsLinkedTreeDecomp G T W) {k : ℕ} (hii : ∀ i, (pEdge W' i).ncard = k)
  (hstep : ∀ j, PStep W' k j)

include hT he₁ he₂ hne h0 h hP hA hB hA' hB' hii hstep in
/-- **Step (2) of the proof of (12.2).** Every edge `e` of the path of `T` between `f₁` and `f₂` has
`|W(e)| ≥ k`, by (1). -/
theorem le_ncard_of_onTreePathEdge_a₁_a₂ {s s' : ι} (hss : Thomas.OnTreePathEdge T a₁ a₂ s s') :
    k ≤ (treeEdgeSet T W s s').ncard := by
  -- (1): `k` disjoint paths between `W(f₁)` and `W(f₂)`.
  have h1 : HasDisjointPaths G.skeleton (treeEdgeSet T W a₁ c₁) (treeEdgeSet T W c₂ a₂) k := by
    rw [treeEdgeSet_e₁_eq hT he₁ he₂ hne h0 h hP hA hB,
      treeEdgeSet_e₂_eq hT he₁ he₂ hne h0 h hP hA' hB']
    exact hasDisjointPaths_pEdge hP hii hstep _ _
  refine le_ncard_of_hasDisjointPaths h h1 ?_ ?_ hss
  · rw [h.treeEdgeSet_eq he₁]
    exact inter_subset_left
  · rw [h.treeEdgeSet_eq he₂]
    exact inter_subset_right

include hT he₁ he₂ hne h0 h hP hA hB hA' hB' hL hii hstep in
/-- **The main case of linkedness.** Let `R` be the path of `T*` from `x` to `z`, with
`|W*(e)| ≥ k'` for all its edges. Let `pq` be an edge of `T₁` or `T₂`, and `e = uv` an edge of
`T*`, all of whose ends are on `R`, with `|W(pq)| = |W*(e)| = k'`. Then there are `k'` disjoint paths
between `W(pq)` and `W*(e)`. -/
theorem hasDisjointPaths_splice_core {x z : joinSet T a₁ c₁ c₂ a₂ ⊕ Fin m} {k' : ℕ}
    (hmin : ∀ ⦃s s' : joinSet T a₁ c₁ c₂ a₂ ⊕ Fin m⦄,
      Thomas.OnTreePathEdge (spliceTree T a₁ c₁ c₂ a₂ m) x z s s' →
      k' ≤ (treeEdgeSet (spliceTree T a₁ c₁ c₂ a₂ m) (spliceBag T a₁ c₁ c₂ a₂ m W W') s s').ncard)
    {p q : joinSet T a₁ c₁ c₂ a₂} (hpq : T.Adj p.1 q.1)
    (hp : Thomas.OnTreePath (spliceTree T a₁ c₁ c₂ a₂ m) x z (Sum.inl p))
    (hq : Thomas.OnTreePath (spliceTree T a₁ c₁ c₂ a₂ m) x z (Sum.inl q))
    (hk : (treeEdgeSet T W p.1 q.1).ncard = k') {u v : joinSet T a₁ c₁ c₂ a₂ ⊕ Fin m}
    (huv : (spliceTree T a₁ c₁ c₂ a₂ m).Adj u v)
    (hu : Thomas.OnTreePath (spliceTree T a₁ c₁ c₂ a₂ m) x z u)
    (hv : Thomas.OnTreePath (spliceTree T a₁ c₁ c₂ a₂ m) x z v)
    (hk' : (treeEdgeSet (spliceTree T a₁ c₁ c₂ a₂ m) (spliceBag T a₁ c₁ c₂ a₂ m W W') u v).ncard
      = k') :
    HasDisjointPaths G.skeleton (treeEdgeSet T W p.1 q.1)
      (treeEdgeSet (spliceTree T a₁ c₁ c₂ a₂ m) (spliceBag T a₁ c₁ c₂ a₂ m W W') u v) k' := by
  classical
  have hT' := isTree_spliceTree hT he₁ he₂ hne h0 (m := m)
  have hD := isTreeDecomp21_splice hT he₁ he₂ hne h0 h hP hA hB hA' hB'
  set R := fun w ↦ Thomas.OnTreePath (spliceTree T a₁ c₁ c₂ a₂ m) x z w
  have hconv : ∀ {w₁ w₂ w}, R w₁ → R w₂ →
      Thomas.OnTreePath (spliceTree T a₁ c₁ c₂ a₂ m) w₁ w₂ w → R w :=
    fun h₁ h₂ h₃ ↦ onTreePath_of_onTreePath_of_onTreePath hT' h₁ h₂ h₃
  have hminR : ∀ {s s'}, (spliceTree T a₁ c₁ c₂ a₂ m).Adj s s' → R s → R s' →
      k' ≤ (treeEdgeSet (spliceTree T a₁ c₁ c₂ a₂ m) (spliceBag T a₁ c₁ c₂ a₂ m W W') s s').ncard :=
    fun hss hs hs' ↦ hmin (onTreePathEdge_of_onTreePath hT' hss hs hs')
  have hTE : ∀ {s s' : joinSet T a₁ c₁ c₂ a₂}, T.Adj s.1 s'.1 →
      treeEdgeSet (spliceTree T a₁ c₁ c₂ a₂ m) (spliceBag T a₁ c₁ c₂ a₂ m W W') (Sum.inl s)
        (Sum.inl s') = treeEdgeSet T W s.1 s'.1 := fun hss ↦ by
    rw [hD.treeEdgeSet_eq (spliceTree_adj_inl hss), h.treeEdgeSet_eq hss]
    rfl
  -- An edge of `T` on the path of `T` between two vertices of `R`, with both ends in `T₁ ∪ T₂`.
  have hR_T : ∀ {x' z' : joinSet T a₁ c₁ c₂ a₂}, R (Sum.inl x') → R (Sum.inl z') →
      ∀ {s s' : ι}, Thomas.OnTreePathEdge T x'.1 z'.1 s s' →
      ∀ (hs : s ∈ joinSet T a₁ c₁ c₂ a₂) (hs' : s' ∈ joinSet T a₁ c₁ c₂ a₂),
      k' ≤ (treeEdgeSet T W s s').ncard := by
    intro x' z' hx' hz' s s' hss hs hs'
    have h1 := hconv hx' hz' (onTreePath_splice_of hT he₁ he₂ hne h0 (m := m)
      (s := ⟨s, hs⟩) hss.onTreePath_left)
    have h2 := hconv hx' hz' (onTreePath_splice_of hT he₁ he₂ hne h0 (m := m)
      (s := ⟨s', hs'⟩) hss.onTreePath_right)
    have := hminR (spliceTree_adj_inl (x := ⟨s, hs⟩) (y := ⟨s', hs'⟩) hss.1) h1 h2
    rwa [hTE hss.1] at this
  have hpR : R (Sum.inl p) := hp
  have hside : ∀ w : joinSet T a₁ c₁ c₂ a₂, T.Adj p.1 w.1 ∨ w = p →
      ((cutTwo T a₁ c₁ c₂ a₂).Reachable a₁ p.1 ↔ (cutTwo T a₁ c₁ c₂ a₂).Reachable a₁ w.1) := by
    rintro w (hw | rfl)
    · exact reachable_iff_of_adj hT he₁ he₂ hne h0 hw
    · exact Iff.rfl
  have hk₀ : (pEdge W' 0).ncard = k := hii 0
  have hpE : ∀ i (hi : i ≤ m),
      treeEdgeSet (spliceTree T a₁ c₁ c₂ a₂ m) (spliceBag T a₁ c₁ c₂ a₂ m W W')
        (spliceVert T a₁ c₁ c₂ a₂ m i) (spliceVert T a₁ c₁ c₂ a₂ m (i + 1)) =
        pEdge W' ⟨i, by omega⟩ :=
    fun i hi ↦ treeEdgeSet_splice_spliceVert hT he₁ he₂ hne h0 h hP hA hB hA' hB' hi
  rcases spliceTree_adj_cases hT he₁ he₂ hne h0 huv with ⟨p', q', rfl, rfl, hpq', -⟩ |
    ⟨i, hi, huv' | huv'⟩
  · -- `e` is an edge of `T`.
    rw [hTE hpq'] at hk' ⊢
    refine hasDisjointPaths_of_linked h hL hpq hpq' hk hk' ?_
    intro w y hw hy s s' hss
    obtain ⟨w, hwR, rfl⟩ : ∃ w' : joinSet T a₁ c₁ c₂ a₂, R (Sum.inl w') ∧ w'.1 = w := by
      rcases hw with rfl | rfl
      exacts [⟨p, hp, rfl⟩, ⟨q, hq, rfl⟩]
    obtain ⟨y, hyR, rfl⟩ : ∃ y' : joinSet T a₁ c₁ c₂ a₂, R (Sum.inl y') ∧ y'.1 = y := by
      rcases hy with rfl | rfl
      exacts [⟨p', hu, rfl⟩, ⟨q', hv, rfl⟩]
    by_cases hS : s ∈ joinSet T a₁ c₁ c₂ a₂ ∧ s' ∈ joinSet T a₁ c₁ c₂ a₂
    · exact hR_T hwR hyR hss hS.1 hS.2
    -- Otherwise `w` and `y` are in different ones of `T₁, T₂`, and the edge is between `f₁` and
    -- `f₂`.
    have hdiff : ∀ {w y : joinSet T a₁ c₁ c₂ a₂}, R (Sum.inl w) → R (Sum.inl y) →
        Thomas.OnTreePathEdge T w.1 y.1 s s' → (cutTwo T a₁ c₁ c₂ a₂).Reachable a₁ w.1 →
        (cutTwo T a₁ c₁ c₂ a₂).Reachable a₂ y.1 → k' ≤ (treeEdgeSet T W s s').ncard := by
      intro w y hwR hyR hss hw hy
      have hend : ∀ {r r' : ι}, T.Adj r r' → Thomas.OnTreePath T w.1 y.1 r →
          ¬ (r ∈ joinSet T a₁ c₁ c₂ a₂ ∧ r' ∈ joinSet T a₁ c₁ c₂ a₂) →
          Thomas.OnTreePath T w.1 y.1 r' → Thomas.OnTreePath T a₁ a₂ r := by
        intro r r' hrr hr hn hr'
        by_cases hrS : r ∈ joinSet T a₁ c₁ c₂ a₂
        · have hr'S : r' ∉ joinSet T a₁ c₁ c₂ a₂ := fun h' ↦ hn ⟨hrS, h'⟩
          rcases eq_of_adj_not_mem hT he₁ he₂ hne h0 hrr hrS hr'S with rfl | rfl
          · exact Thomas.onTreePath_left _ _ _
          · exact Thomas.onTreePath_right _ _ _
        · exact onTreePath_a₁_a₂ hT he₁ he₂ hne h0 hw hy hr hrS
      have hE : Thomas.OnTreePathEdge T a₁ a₂ s s' :=
        onTreePathEdge_of_onTreePath hT hss.1
          (hend hss.1 hss.onTreePath_left hS hss.onTreePath_right)
          (hend hss.1.symm hss.onTreePath_right (fun h' ↦ hS ⟨h'.2, h'.1⟩) hss.onTreePath_left)
      have hkk := le_ncard_of_onTreePathEdge_a₁_a₂ hT he₁ he₂ hne h0 h hP hA hB hA' hB' hii hstep hE
      -- `k' ≤ k`: the first edge of `P` is on `R`.
      have hP0 := onTreePathEdge_splice hT he₁ he₂ hne h0 (m := m) (i := 0) (Nat.zero_le _)
        (u := Sum.inl w) (v := Sum.inl y)
        (by rw [splicePos_inl_of_reachable hw])
        (by rw [splicePos_inl_of_not (not_reachable_a₁_of_a₂ hT he₁ he₂ hne h0 hy)]; omega)
      have := hminR (spliceTree_adj_spliceVert hT he₁ he₂ hne h0 (Nat.zero_le m))
        (hconv hwR hyR hP0.onTreePath_left) (hconv hwR hyR hP0.onTreePath_right)
      rw [hpE 0 (Nat.zero_le _)] at this
      exact this.trans (hk₀.symm ▸ hkk)
    rcases w.2 with hw | hw <;> rcases y.2 with hy | hy
    · exact (hS ⟨Or.inl (reachable_of_onTreePath hT hw hy hss.onTreePath_left),
        Or.inl (reachable_of_onTreePath hT hw hy hss.onTreePath_right)⟩).elim
    · exact hdiff hwR hyR hss hw hy
    · exact hdiff hyR hwR (Thomas.onTreePathEdge_symm_endpoints hss) hy hw
    · exact (hS ⟨Or.inr (reachable_of_onTreePath hT hw hy hss.onTreePath_left),
        Or.inr (reachable_of_onTreePath hT hw hy hss.onTreePath_right)⟩).elim
  all_goals
    obtain ⟨hφi, hφi1, hEuv⟩ : R (spliceVert T a₁ c₁ c₂ a₂ m i) ∧
        R (spliceVert T a₁ c₁ c₂ a₂ m (i + 1)) ∧
        treeEdgeSet (spliceTree T a₁ c₁ c₂ a₂ m) (spliceBag T a₁ c₁ c₂ a₂ m W W') u v =
          pEdge W' ⟨i, by omega⟩ := by
      first
      | (obtain ⟨rfl, rfl⟩ := huv'; exact ⟨hu, hv, hpE i hi⟩)
      | (obtain ⟨rfl, rfl⟩ := huv'
         exact ⟨hv, hu, by rw [treeEdgeSet_comm hD huv]; exact hpE i hi⟩)
    rw [hEuv] at hk' ⊢
    have hkk : k' = k := hk'.symm.trans (hii _)
    subst hkk
    have hk₁ : (treeEdgeSet T W a₁ c₁).ncard = k' := by
      rw [treeEdgeSet_e₁_eq hT he₁ he₂ hne h0 h hP hA hB]; exact hii _
    have hk₂ : (treeEdgeSet T W c₂ a₂).ncard = k' := by
      rw [treeEdgeSet_e₂_eq hT he₁ he₂ hne h0 h hP hA' hB']; exact hii _
    have hXp : treeEdgeSet T W p.1 q.1 ⊆ (W p.1).vertexSet := by
      rw [h.treeEdgeSet_eq hpq]; exact inter_subset_left
    by_cases hp1 : (cutTwo T a₁ c₁ c₂ a₂).Reachable a₁ p.1
    · -- `pq` is in `T₁`: go through `f₁`.
      have hq1 := (hside q (Or.inl hpq)).1 hp1
      have hRa₁ : R (Sum.inl joinLeft) := by
        rcases Nat.eq_zero_or_pos i with rfl | hi0
        · rwa [spliceVert_zero] at hφi
        · have hE := onTreePathEdge_splice hT he₁ he₂ hne h0 (i := 0) (Nat.zero_le m)
            (u := Sum.inl p) (v := spliceVert T a₁ c₁ c₂ a₂ m i)
            (by rw [splicePos_inl_of_reachable hp1])
            (by rw [splicePos_spliceVert hT he₁ he₂ hne h0 (by omega)]; exact hi0)
          have := hconv hp hφi hE.onTreePath_left
          rwa [spliceVert_zero] at this
      have hpath : ∀ w, (w = p.1 ∨ w = q.1) → ∀ s s', Thomas.OnTreePathEdge T w a₁ s s' →
          k' ≤ (treeEdgeSet T W s s').ncard := by
        intro w hw s s' hss
        obtain ⟨w, hwR, hw1, rfl⟩ : ∃ w' : joinSet T a₁ c₁ c₂ a₂, R (Sum.inl w') ∧
            (cutTwo T a₁ c₁ c₂ a₂).Reachable a₁ w'.1 ∧ w'.1 = w := by
          rcases hw with rfl | rfl
          exacts [⟨p, hp, hp1, rfl⟩, ⟨q, hq, hq1, rfl⟩]
        exact hR_T (z' := joinLeft) hwR hRa₁ hss
          (Or.inl (reachable_of_onTreePath hT hw1 (Reachable.refl _) hss.onTreePath_left))
          (Or.inl (reachable_of_onTreePath hT hw1 (Reachable.refl _) hss.onTreePath_right))
      have h₁ := hasDisjointPaths_side₁ hT he₁ he₂ hne h0 h hL hp1 hq1 hpq hk hk₁ hpath
      have h₂ := hasDisjointPaths_pEdge hP hii hstep 0 ⟨i, by omega⟩
      rw [← treeEdgeSet_e₁_eq hT he₁ he₂ hne h0 h hP hA hB] at h₂
      obtain ⟨G₁, G₂, hs, hmid, hG₁, hG₂⟩ := exists_separation_of_treeDecomp h he₁
      rw [← hmid] at h₁ h₂
      refine hasDisjointPaths_trans hs (hXp.trans (hG₁ p.1 (hp1.mono cutTwo_le_left))) ?_
        (by rw [separationOrder, hmid, hk₁]) h₁ h₂
      intro y hy
      have hyB : y ∈ (bagUnion W' (· ≠ 0)).vertexSet :=
        mem_bagUnion_vertexSet.2 ⟨_, fun h' ↦ by simp [Fin.ext_iff] at h', hy.2⟩
      rw [hB, mem_bagUnion_vertexSet] at hyB
      obtain ⟨t, ht, hyt⟩ := hyB
      refine hG₂ t ?_ hyt
      rcases mem_joinSet_or_reachable hT he₁ he₂ hne h0 t with htS | ht0
      · exact (reachable_c₁_of_e₁ hT he₁ he₂ hne h0 (Or.inl (htS.resolve_left ht))).symm
      · exact (reachable_c₁_of_e₁ hT he₁ he₂ hne h0 (Or.inr ht0)).symm
    · -- `pq` is in `T₂`: go through `f₂`.
      have hp2 := reachable_a₂_of_not hT he₁ he₂ hne h0 hp1
      have hq2 : (cutTwo T a₁ c₁ c₂ a₂).Reachable a₂ q.1 :=
        reachable_a₂_of_not hT he₁ he₂ hne h0 (fun h' ↦ hp1 ((hside q (Or.inl hpq)).2 h'))
      have hRa₂ : R (Sum.inl joinRight) := by
        rcases Nat.lt_or_ge i m with him | him
        · have hE := onTreePathEdge_splice hT he₁ he₂ hne h0 (i := m) le_rfl
            (u := spliceVert T a₁ c₁ c₂ a₂ m (i + 1)) (v := Sum.inl p)
            (by rw [splicePos_spliceVert hT he₁ he₂ hne h0 (by omega)]; omega)
            (by rw [splicePos_inl_of_not hp1]; omega)
          have := hconv hφi1 hp hE.onTreePath_right
          rwa [spliceVert_succ_self] at this
        · obtain rfl : i = m := by omega
          rwa [spliceVert_succ_self] at hφi1
      have hpath : ∀ w, (w = p.1 ∨ w = q.1) → ∀ s s', Thomas.OnTreePathEdge T w a₂ s s' →
          k' ≤ (treeEdgeSet T W s s').ncard := by
        intro w hw s s' hss
        obtain ⟨w, hwR, hw2, rfl⟩ : ∃ w' : joinSet T a₁ c₁ c₂ a₂, R (Sum.inl w') ∧
            (cutTwo T a₁ c₁ c₂ a₂).Reachable a₂ w'.1 ∧ w'.1 = w := by
          rcases hw with rfl | rfl
          exacts [⟨p, hp, hp2, rfl⟩, ⟨q, hq, hq2, rfl⟩]
        exact hR_T (z' := joinRight) hwR hRa₂ hss
          (Or.inr (reachable_of_onTreePath hT hw2 (Reachable.refl _) hss.onTreePath_left))
          (Or.inr (reachable_of_onTreePath hT hw2 (Reachable.refl _) hss.onTreePath_right))
      have h₁ := hasDisjointPaths_side₂ hT he₁ he₂ hne h0 h hL hp2 hq2 hpq hk hk₂ hpath
      have h₂ := hasDisjointPaths_pEdge hP hii hstep (Fin.last m) ⟨i, by omega⟩
      rw [← treeEdgeSet_e₂_eq hT he₁ he₂ hne h0 h hP hA' hB'] at h₂
      rw [treeEdgeSet_comm h he₂] at h₁ h₂
      obtain ⟨G₁, G₂, hs, hmid, hG₁, hG₂⟩ := exists_separation_of_treeDecomp h he₂.symm
      rw [← hmid] at h₁ h₂
      have hsw : s(a₂, c₂) = s(c₂, a₂) := Sym2.eq_swap
      refine hasDisjointPaths_trans hs
        (hXp.trans (hG₁ p.1 (by rw [hsw]; exact hp2.mono cutTwo_le_right))) ?_
        (by rw [separationOrder, hmid, treeEdgeSet_comm h he₂.symm, hk₂]) h₁ h₂
      intro y hy
      have hyA : y ∈ (bagUnion W' (· ≠ Fin.last (m + 1))).vertexSet :=
        mem_bagUnion_vertexSet.2 ⟨_, fun h' ↦ by simp [Fin.ext_iff] at h'; omega, hy.1⟩
      rw [hA', mem_bagUnion_vertexSet] at hyA
      obtain ⟨t, ht, hyt⟩ := hyA
      refine hG₂ t ?_ hyt
      rw [hsw]
      rcases mem_joinSet_or_reachable hT he₁ he₂ hne h0 t with htS | ht0
      · exact (reachable_c₂_of_e₂ hT he₁ he₂ hne h0 (Or.inl (htS.resolve_right ht))).symm
      · exact (reachable_c₂_of_e₂ hT he₁ he₂ hne h0 (Or.inr ht0)).symm

include hT he₁ he₂ hne h0 h hP hA hB hA' hB' in
/-- An edge of `T*` between two vertices of `T₁ ∪ T₂` has `W*(e) = W(e)`. -/
theorem treeEdgeSet_splice_inl {s s' : joinSet T a₁ c₁ c₂ a₂} (hss : T.Adj s.1 s'.1) :
    treeEdgeSet (spliceTree T a₁ c₁ c₂ a₂ m) (spliceBag T a₁ c₁ c₂ a₂ m W W') (Sum.inl s)
      (Sum.inl s') = treeEdgeSet T W s.1 s'.1 := by
  have hD := isTreeDecomp21_splice hT he₁ he₂ hne h0 h hP hA hB hA' hB'
  rw [hD.treeEdgeSet_eq (spliceTree_adj_inl hss), h.treeEdgeSet_eq hss]
  rfl

include hT he₁ he₂ hne h0 h hP hA hB hA' hB' hL hii hstep in
/-- **(12.2), linkedness.** `(T*, W*)` is linked. We follow the paper's cases: if both edges are
edges of `P`, this is (1); if one is an edge of `T₁` or `T₂`, this is
`hasDisjointPaths_splice_core`. -/
theorem isLinkedTreeDecomp_splice :
    IsLinkedTreeDecomp G (spliceTree T a₁ c₁ c₂ a₂ m) (spliceBag T a₁ c₁ c₂ a₂ m W W') := by
  intro x y u z hxy huz hy hu k' hk₁ hk₂ hmin
  have hx : Thomas.OnTreePath (spliceTree T a₁ c₁ c₂ a₂ m) x z x := Thomas.onTreePath_left _ _ _
  have hz : Thomas.OnTreePath (spliceTree T a₁ c₁ c₂ a₂ m) x z z := Thomas.onTreePath_right _ _ _
  have hpE : ∀ i (hi : i ≤ m),
      treeEdgeSet (spliceTree T a₁ c₁ c₂ a₂ m) (spliceBag T a₁ c₁ c₂ a₂ m W W')
        (spliceVert T a₁ c₁ c₂ a₂ m i) (spliceVert T a₁ c₁ c₂ a₂ m (i + 1)) =
        pEdge W' ⟨i, by omega⟩ :=
    fun i hi ↦ treeEdgeSet_splice_spliceVert hT he₁ he₂ hne h0 h hP hA hB hA' hB' hi
  have hD := isTreeDecomp21_splice hT he₁ he₂ hne h0 h hP hA hB hA' hB'
  -- An edge of `P` has `W*(e) = W'(e)` for some edge of `P`, in either orientation.
  have hPE : ∀ {s s' : joinSet T a₁ c₁ c₂ a₂ ⊕ Fin m} (hss : (spliceTree T a₁ c₁ c₂ a₂ m).Adj s s')
      (i : ℕ) (hi : i ≤ m),
      (s = spliceVert T a₁ c₁ c₂ a₂ m i ∧ s' = spliceVert T a₁ c₁ c₂ a₂ m (i + 1)) ∨
      (s' = spliceVert T a₁ c₁ c₂ a₂ m i ∧ s = spliceVert T a₁ c₁ c₂ a₂ m (i + 1)) →
      treeEdgeSet (spliceTree T a₁ c₁ c₂ a₂ m) (spliceBag T a₁ c₁ c₂ a₂ m W W') s s' =
        pEdge W' ⟨i, by omega⟩ := by
    rintro s s' hss i hi (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
    · exact hpE i hi
    · rw [treeEdgeSet_comm hD hss]; exact hpE i hi
  rcases spliceTree_adj_cases hT he₁ he₂ hne h0 hxy with ⟨p, q, rfl, rfl, hpq, -⟩ |
    ⟨i, hi, hxy'⟩
  · -- The first edge is an edge of `T`.
    rw [treeEdgeSet_splice_inl hT he₁ he₂ hne h0 h hP hA hB hA' hB' hpq] at hk₁ ⊢
    exact hasDisjointPaths_splice_core hT he₁ he₂ hne h0 h hP hA hB hA' hB' hL hii hstep
      hmin hpq hx hy hk₁ huz hu hz hk₂
  rcases spliceTree_adj_cases hT he₁ he₂ hne h0 huz with ⟨p, q, rfl, rfl, hpq, -⟩ |
    ⟨j, hj, huz'⟩
  · -- The second edge is an edge of `T`: reverse the path.
    rw [treeEdgeSet_splice_inl hT he₁ he₂ hne h0 h hP hA hB hA' hB' hpq] at hk₂ ⊢
    refine HasDisjointPaths.symm (hasDisjointPaths_splice_core hT he₁ he₂ hne h0 h hP hA hB hA' hB' hL hii hstep
      (fun s s' hss ↦ hmin (Thomas.onTreePathEdge_symm_endpoints hss)) hpq
      (Thomas.onTreePath_symm hu) (Thomas.onTreePath_symm hz) hk₂ hxy
      (Thomas.onTreePath_symm hx) (Thomas.onTreePath_symm hy) hk₁)
  · -- Both edges are edges of `P`: this is (1).
    rw [hPE hxy i hi hxy'] at hk₁ ⊢
    rw [hPE huz j hj huz'] at hk₂ ⊢
    have hkk : k' = k := hk₁.symm.trans (hii _)
    subst hkk
    exact hasDisjointPaths_pEdge hP hii hstep _ _

end Linked

end GM21
end GraphMinor
