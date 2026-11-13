module

public import GraphMinor.GM21.Section12Splice
public import GraphMinor.GM21.Section12One
public import GraphMinor.GM21.Section11Tree
import GraphMinor.Menger.Basic

/-!
# Graph Minors XXI, (12.2)

"**12.2** *Let $(T, W)$ be a linked tree-decomposition of a graph $G$, with width $\le w$. Let
$f_1, f_2 \in E(T)$ be distinct, and let $T_1, T_2, T_0$ be the three components of
$T \setminus \{f_1, f_2\}$ where $f_i$ has ends in $T_i$ and $T_0$ ($i = 1, 2$). Let
$|W(f_1)| = |W(f_2)| = k$, and let $(P, W')$ be a path-decomposition of $G$ satisfying statements
(i)–(iii) of (12.1), with $W, A, B, A', B'$ replaced by $W', W(T_1), W(T_0) \cup W(T_2),
W(T_0) \cup W(T_1), W(T_2)$. Let $P$ have ends $s_1, s_2$, where $s_i$ is the end of $f_i$ in
$V(T_i)$ ($i = 1, 2$), and otherwise let $P$ be disjoint from $T$. Let $T^*$ be the tree
$T_1 \cup T_2 \cup P$, and define $W^*(t) = W(t)$ if $t \in V(T_1) \cup V(T_2)$ and
$W^*(t) = W'(t)$ if $t \in V(P) \setminus \{s, s'\}$. Then $(T^*, W^*)$ is a linked
tree-decomposition of $G$, with width $\le w$.*" (page 49.)

We write `f₁ = a₁c₁` and `f₂ = c₂a₂` with `a₁ ∈ T₁`, `a₂ ∈ T₂`. The tree `T*` is `spliceTree`
(file `Section12Splice`), and `W*` is `spliceBag`. The path-decomposition `(P, W')` is on
`pathGraph (m + 2)`, with `s₁ = 0` and `s₂ = m + 1`.

The proof follows the paper. That `(T*, W*)` is a tree-decomposition, which the paper calls easy,
is shown by checking that for each vertex and each edge of `G`, the vertices of `T*` whose bags
contain it are joined by a walk of `T*` through such vertices (`exists_goodWalk`).
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace GraphMinor
namespace GM21

open Set SimpleGraph Hypergraph

universe u v

variable {α : Type u} {β : Type v}

/-! ## Two general facts -/

/-- A subgraph of `G` is a subgraph of another subgraph of `G` with more vertices and edges. -/
theorem le_of_subset_of_le {G H₁ H₂ : Hypergraph α β} (h₁ : H₁ ≤ G) (h₂ : H₂ ≤ G)
    (hV : H₁.vertexSet ⊆ H₂.vertexSet) (hE : H₁.edgeSet ⊆ H₂.edgeSet) : H₁ ≤ H₂ :=
  ⟨hV, hE, fun e he ↦ (h₂.ends_eq e (hE he)).symm.trans (h₁.ends_eq e he)⟩

/-- In `pathGraph L`, every vertex between `a` and `b` is on the path between them. -/
theorem onTreePath_pathGraph_of_le {L : ℕ} {a b c : Fin L} (hac : a.1 ≤ c.1) (hcb : c.1 ≤ b.1) :
    Thomas.OnTreePath (pathGraph L) a b c := by
  rw [Thomas.onTreePath_iff_forall_walk]
  have key : ∀ {u v : Fin L} (p : (pathGraph L).Walk u v), u.1 ≤ c.1 → c.1 ≤ v.1 →
      c ∈ p.support := by
    intro u v p
    induction p with
    | @nil w =>
      intro h1 h2
      have : c = w := Fin.ext (by omega)
      rw [this]
      exact List.mem_singleton_self _
    | @cons x y z h p ih =>
      intro h1 h2
      rw [Walk.support_cons]
      by_cases hx : x = c
      · rw [hx]
        exact List.mem_cons_self
      · have : x.1 ≠ c.1 := fun h' ↦ hx (Fin.ext h')
        rcases pathGraph_adj.1 h with h' | h'
        · exact List.mem_cons_of_mem _ (ih (by omega) h2)
        · exact List.mem_cons_of_mem _ (ih (by omega) h2)
  exact fun p ↦ key p hac hcb

/-! ## The bags of `T*` -/

section Bags

variable {ι : Type*} [Fintype ι] {T : SimpleGraph ι} {a₁ c₁ c₂ a₂ : ι} {m : ℕ}

variable (T a₁ c₁ c₂ a₂ m) in
/-- The bags `W*` of `T*`: `W(t)` on `T₁ ∪ T₂`, and `W'(i)` at the inner vertex at position `i`. -/
def spliceBag (W : ι → Hypergraph α β) (W' : Fin (m + 2) → Hypergraph α β) :
    joinSet T a₁ c₁ c₂ a₂ ⊕ Fin m → Hypergraph α β
  | Sum.inl x => W x.1
  | Sum.inr j => W' ⟨j + 1, by omega⟩

variable {G : Hypergraph α β} {W : ι → Hypergraph α β} {W' : Fin (m + 2) → Hypergraph α β}

variable (hT : T.IsTree) (he₁ : T.Adj a₁ c₁) (he₂ : T.Adj c₂ a₂) (hne : s(a₁, c₁) ≠ s(c₂, a₂))
  (h0 : (cutTwo T a₁ c₁ c₂ a₂).Reachable c₁ c₂)
  (h : IsTreeDecomp21 G T W) (hP : IsTreeDecomp21 G (pathGraph (m + 2)) W')
  (hA : W' 0 = bagUnion W ((cutTwo T a₁ c₁ c₂ a₂).Reachable a₁))
  (hB : bagUnion W' (· ≠ 0) = bagUnion W (fun t ↦ ¬ (cutTwo T a₁ c₁ c₂ a₂).Reachable a₁ t))
  (hA' : bagUnion W' (· ≠ Fin.last (m + 1)) =
    bagUnion W (fun t ↦ ¬ (cutTwo T a₁ c₁ c₂ a₂).Reachable a₂ t))
  (hB' : W' (Fin.last (m + 1)) = bagUnion W ((cutTwo T a₁ c₁ c₂ a₂).Reachable a₂))

/-! ### Properties of vertices and edges of `G` -/

/-- A property `Q` of subgraphs of `G` such as "contains the vertex `y`" or "contains the edge
`e`". -/
structure IsMemProp (W : ι → Hypergraph α β) (W' : Fin (m + 2) → Hypergraph α β)
    (Q : Hypergraph α β → Prop) : Prop where
  inter : ∀ H H', Q (H ∩ H') ↔ Q H ∧ Q H'
  mono : ∀ H H', H ≤ H' → Q H → Q H'
  bag : ∀ P : ι → Prop, Q (bagUnion W P) ↔ ∃ t, P t ∧ Q (W t)
  bag' : ∀ P : Fin (m + 2) → Prop, Q (bagUnion W' P) ↔ ∃ i, P i ∧ Q (W' i)

omit [Fintype ι] in
theorem isMemProp_vertex [Fintype ι] (W : ι → Hypergraph α β) (W' : Fin (m + 2) → Hypergraph α β)
    (y : α) : IsMemProp W W' (fun H ↦ y ∈ H.vertexSet) :=
  ⟨fun _ _ ↦ Iff.rfl, fun _ _ h hy ↦ h.vertexSet_subset hy, fun _ ↦ mem_bagUnion_vertexSet,
    fun _ ↦ mem_bagUnion_vertexSet⟩

omit [Fintype ι] in
theorem isMemProp_edge [Fintype ι] (W : ι → Hypergraph α β) (W' : Fin (m + 2) → Hypergraph α β)
    (e : β) : IsMemProp W W' (fun H ↦ e ∈ H.edgeSet) :=
  ⟨fun _ _ ↦ Iff.rfl, fun _ _ h he ↦ h.edgeSet_subset he, fun _ ↦ mem_bagUnion_edgeSet,
    fun _ ↦ mem_bagUnion_edgeSet⟩

variable {Q : Hypergraph α β → Prop}

include hP in
/-- A property held by two bags of `P` is held by every bag between them. -/
theorem IsMemProp.between (hQ : IsMemProp W W' Q) {i j l : Fin (m + 2)} (hi : Q (W' i))
    (hj : Q (W' j)) (hil : i.1 ≤ l.1) (hlj : l.1 ≤ j.1) : Q (W' l) :=
  hQ.mono _ _ (hP.inter_le (onTreePath_pathGraph_of_le hil hlj)) ((hQ.inter _ _).2 ⟨hi, hj⟩)

include h in
/-- A property held by two bags of `T` is held by every bag on the path between them. -/
theorem IsMemProp.onPath (hQ : IsMemProp W W' Q) {t t' s : ι} (ht : Q (W t)) (ht' : Q (W t'))
    (hs : Thomas.OnTreePath T t t' s) : Q (W s) :=
  hQ.mono _ _ (h.inter_le hs) ((hQ.inter _ _).2 ⟨ht, ht'⟩)

include hT he₁ he₂ hne h0 h in
/-- If `Q` holds for a bag of `T₁` and for `B`, then for `W(a₁)`. -/
theorem IsMemProp.left (hQ : IsMemProp W W' Q) {t : ι}
    (ht : (cutTwo T a₁ c₁ c₂ a₂).Reachable a₁ t) (hQt : Q (W t))
    (hQB : Q (bagUnion W (fun t ↦ ¬ (cutTwo T a₁ c₁ c₂ a₂).Reachable a₁ t))) : Q (W a₁) := by
  obtain ⟨t', ht', hQt'⟩ := (hQ.bag _).1 hQB
  exact hQ.onPath h hQt hQt' (onTreePathEdge_e₁_of hT he₁ he₂ hne h0 ht ht').onTreePath_left

include hT he₁ he₂ hne h0 h in
/-- If `Q` holds for a bag of `T₂` and for `A'`, then for `W(a₂)`. -/
theorem IsMemProp.right (hQ : IsMemProp W W' Q) {t : ι}
    (ht : (cutTwo T a₁ c₁ c₂ a₂).Reachable a₂ t) (hQt : Q (W t))
    (hQA' : Q (bagUnion W (fun t ↦ ¬ (cutTwo T a₁ c₁ c₂ a₂).Reachable a₂ t))) : Q (W a₂) := by
  obtain ⟨t', ht', hQt'⟩ := (hQ.bag _).1 hQA'
  exact hQ.onPath h hQt' hQt (onTreePathEdge_e₂_of hT he₁ he₂ hne h0 ht' ht).onTreePath_right

/-! ### Walks through bags with a property -/

variable (T a₁ c₁ c₂ a₂ m) in
/-- `u` and `v` are joined by a walk of `T*` all of whose bags have the property `Q`. -/
def GoodWalk (W : ι → Hypergraph α β) (W' : Fin (m + 2) → Hypergraph α β)
    (Q : Hypergraph α β → Prop) (u v : joinSet T a₁ c₁ c₂ a₂ ⊕ Fin m) : Prop :=
  ∃ q : (spliceTree T a₁ c₁ c₂ a₂ m).Walk u v, ∀ z ∈ q.support, Q (spliceBag T a₁ c₁ c₂ a₂ m W W' z)

omit [Fintype ι] in
theorem GoodWalk.trans {u v w : joinSet T a₁ c₁ c₂ a₂ ⊕ Fin m}
    (h₁ : GoodWalk T a₁ c₁ c₂ a₂ m W W' Q u v) (h₂ : GoodWalk T a₁ c₁ c₂ a₂ m W W' Q v w) :
    GoodWalk T a₁ c₁ c₂ a₂ m W W' Q u w := by
  obtain ⟨q₁, hq₁⟩ := h₁
  obtain ⟨q₂, hq₂⟩ := h₂
  refine ⟨q₁.append q₂, fun z hz ↦ ?_⟩
  rcases (Walk.mem_support_append_iff _ _).1 hz with hz | hz
  exacts [hq₁ z hz, hq₂ z hz]

omit [Fintype ι] in
theorem GoodWalk.symm {u v : joinSet T a₁ c₁ c₂ a₂ ⊕ Fin m}
    (h₁ : GoodWalk T a₁ c₁ c₂ a₂ m W W' Q u v) : GoodWalk T a₁ c₁ c₂ a₂ m W W' Q v u := by
  obtain ⟨q, hq⟩ := h₁
  exact ⟨q.reverse, fun z hz ↦ hq z (by simpa using hz)⟩

include h in
/-- Two vertices of one of `T₁, T₂` whose bags have `Q` are joined by a good walk: the path of `T`
between them. -/
theorem goodWalk_side (hQ : IsMemProp W W' Q) {a : ι} {x z : joinSet T a₁ c₁ c₂ a₂}
    (hx : (cutTwo T a₁ c₁ c₂ a₂).Reachable a x.1) (hz : (cutTwo T a₁ c₁ c₂ a₂).Reachable a z.1)
    (ha : a = a₁ ∨ a = a₂) (hQx : Q (W x.1)) (hQz : Q (W z.1)) :
    GoodWalk T a₁ c₁ c₂ a₂ m W W' Q (Sum.inl x) (Sum.inl z) := by
  classical
  have hp : ∀ y ∈ (Thomas.treePath h.isTree x.1 z.1).support, y ∈ joinSet T a₁ c₁ c₂ a₂ := by
    intro y hy
    have := reachable_of_onTreePath h.isTree hx hz
      ((Thomas.onTreePath_iff_mem_treePath h.isTree).2 hy)
    rcases ha with rfl | rfl
    exacts [Or.inl this, Or.inr this]
  obtain ⟨q, hq⟩ := exists_splice_walk_of_walk (m := m) _ hp
  refine ⟨q, fun w hw ↦ ?_⟩
  obtain ⟨y, hy, rfl⟩ := hq w hw
  exact hQ.onPath h hQx hQz ((Thomas.onTreePath_iff_mem_treePath h.isTree).2 hy)

include hT he₁ he₂ hne h0 h hP hA hB hA' hB' in
/-- **The tree-decomposition.** For a property `Q` of a vertex or an edge of `G`, two vertices of
`T*` whose bags have `Q` are joined by a walk of `T*` through vertices whose bags have `Q`. -/
theorem exists_goodWalk (hQ : IsMemProp W W' Q) {u v : joinSet T a₁ c₁ c₂ a₂ ⊕ Fin m}
    (hu : Q (spliceBag T a₁ c₁ c₂ a₂ m W W' u)) (hv : Q (spliceBag T a₁ c₁ c₂ a₂ m W W' v)) :
    GoodWalk T a₁ c₁ c₂ a₂ m W W' Q u v := by
  classical
  -- The bag of `u` lies in the bag of `P` at the position of `u`.
  have hvirt : ∀ w, Q (spliceBag T a₁ c₁ c₂ a₂ m W W' w) →
      Q (W' ⟨splicePos T a₁ c₁ c₂ a₂ m w, by have := splicePos_le hT he₁ he₂ hne h0 w; omega⟩) := by
    intro w hw
    rcases w with x | j
    · by_cases hx : (cutTwo T a₁ c₁ c₂ a₂).Reachable a₁ x.1
      · have hp : splicePos T a₁ c₁ c₂ a₂ m (Sum.inl x) = 0 := splicePos_inl_of_reachable hx
        have : (⟨splicePos T a₁ c₁ c₂ a₂ m (Sum.inl x), by omega⟩ : Fin (m + 2)) = 0 := Fin.ext hp
        rw [this, hA]
        exact (hQ.bag _).2 ⟨x.1, hx, hw⟩
      · have hp : splicePos T a₁ c₁ c₂ a₂ m (Sum.inl x) = m + 1 := splicePos_inl_of_not hx
        have : (⟨splicePos T a₁ c₁ c₂ a₂ m (Sum.inl x), by omega⟩ : Fin (m + 2)) = Fin.last (m + 1) := Fin.ext hp
        rw [this, hB']
        exact (hQ.bag _).2 ⟨x.1, reachable_a₂_of_not hT he₁ he₂ hne h0 hx, hw⟩
    · exact hw
  -- A bag at a position `≥ 1` lies in `B`, and a bag at a position `≤ m` lies in `A'`.
  have hQB : ∀ w, Q (spliceBag T a₁ c₁ c₂ a₂ m W W' w) → 1 ≤ splicePos T a₁ c₁ c₂ a₂ m w →
      Q (bagUnion W (fun t ↦ ¬ (cutTwo T a₁ c₁ c₂ a₂).Reachable a₁ t)) := by
    intro w hw hpos
    rw [← hB]
    exact (hQ.bag' _).2 ⟨_, fun h' ↦ by
      have := congrArg Fin.val h'
      simp at this
      omega, hvirt w hw⟩
  have hQA' : ∀ w, Q (spliceBag T a₁ c₁ c₂ a₂ m W W' w) → splicePos T a₁ c₁ c₂ a₂ m w ≤ m →
      Q (bagUnion W (fun t ↦ ¬ (cutTwo T a₁ c₁ c₂ a₂).Reachable a₂ t)) := by
    intro w hw hpos
    rw [← hA']
    exact (hQ.bag' _).2 ⟨_, fun h' ↦ by
      have := congrArg Fin.val h'
      simp at this
      omega, hvirt w hw⟩
  -- The main case: `splicePos T a₁ c₁ c₂ a₂ m u ≤ splicePos T a₁ c₁ c₂ a₂ m v`.
  have main : ∀ u v, Q (spliceBag T a₁ c₁ c₂ a₂ m W W' u) →
      Q (spliceBag T a₁ c₁ c₂ a₂ m W W' v) → splicePos T a₁ c₁ c₂ a₂ m u ≤ splicePos T a₁ c₁ c₂ a₂ m v →
      GoodWalk T a₁ c₁ c₂ a₂ m W W' Q u v := by
    intro u v hu hv hle
    have hu' := hvirt u hu
    have hv' := hvirt v hv
    have hpu := splicePos_le hT he₁ he₂ hne h0 u
    have hpv := splicePos_le hT he₁ he₂ hne h0 v
    -- Every vertex of `P` between the two positions has a good bag.
    have hmid : ∀ l, splicePos T a₁ c₁ c₂ a₂ m u ≤ l → l ≤ splicePos T a₁ c₁ c₂ a₂ m v → splicePos T a₁ c₁ c₂ a₂ m u < splicePos T a₁ c₁ c₂ a₂ m v →
        Q (spliceBag T a₁ c₁ c₂ a₂ m W W' (spliceVert T a₁ c₁ c₂ a₂ m l)) := by
      intro l h1 h2 hlt
      unfold spliceVert
      split_ifs with hl0 hlm
      · -- `l = 0`, so `u ∈ T₁`.
        subst hl0
        rcases u with x | j
        · have hx : (cutTwo T a₁ c₁ c₂ a₂).Reachable a₁ x.1 :=
            (splicePos_inl_eq_zero_iff hT he₁ he₂ hne h0 (m := m)).1 (by omega)
          exact hQ.left hT he₁ he₂ hne h0 h hx hu (hQB v hv (by omega))
        · simp at h1
      · have hl : (⟨l - 1 + 1, by omega⟩ : Fin (m + 2)) = ⟨l, by omega⟩ := Fin.ext (by simp; omega)
        show Q (W' ⟨l - 1 + 1, _⟩)
        rw [hl]
        exact hQ.between hP hu' hv' (l := ⟨l, by omega⟩) h1 h2
      · -- `l = m + 1`, so `v ∈ T₂`.
        rcases v with z | j
        · have hz : ¬ (cutTwo T a₁ c₁ c₂ a₂).Reachable a₁ z.1 := fun h' ↦ by
            have := splicePos_inl_of_reachable (m := m) h'
            omega
          exact hQ.right hT he₁ he₂ hne h0 h (reachable_a₂_of_not hT he₁ he₂ hne h0 hz) hv
            (hQA' u hu (by omega))
        · simp at h2
          omega
    -- The walk from `u` to the vertex of `P` at its position, and from there to `v`.
    have hstart : GoodWalk T a₁ c₁ c₂ a₂ m W W' Q u (spliceVert T a₁ c₁ c₂ a₂ m (splicePos T a₁ c₁ c₂ a₂ m u)) ∨
        splicePos T a₁ c₁ c₂ a₂ m u = splicePos T a₁ c₁ c₂ a₂ m v := by
      rcases Nat.lt_or_ge (splicePos T a₁ c₁ c₂ a₂ m u) (splicePos T a₁ c₁ c₂ a₂ m v) with hlt | hge
      · left
        rcases u with x | j
        · by_cases hx : (cutTwo T a₁ c₁ c₂ a₂).Reachable a₁ x.1
          · have hp : splicePos T a₁ c₁ c₂ a₂ m (Sum.inl x) = 0 := splicePos_inl_of_reachable hx
            rw [hp, spliceVert_zero]
            have hQa₁ := hmid 0 (by omega) (by omega) hlt
            rw [spliceVert_zero] at hQa₁
            exact goodWalk_side h hQ hx (Reachable.refl _) (Or.inl rfl) hu hQa₁
          · have hp : splicePos T a₁ c₁ c₂ a₂ m (Sum.inl x) = m + 1 := splicePos_inl_of_not hx
            omega
        · rw [splicePos_inr, spliceVert_inr]
          exact ⟨Walk.nil, fun z hz ↦ by simp at hz; rw [hz]; exact hu⟩
      · right; omega
    have hend : GoodWalk T a₁ c₁ c₂ a₂ m W W' Q (spliceVert T a₁ c₁ c₂ a₂ m (splicePos T a₁ c₁ c₂ a₂ m v)) v ∨
        splicePos T a₁ c₁ c₂ a₂ m u = splicePos T a₁ c₁ c₂ a₂ m v := by
      rcases Nat.lt_or_ge (splicePos T a₁ c₁ c₂ a₂ m u) (splicePos T a₁ c₁ c₂ a₂ m v) with hlt | hge
      · left
        rcases v with z | j
        · by_cases hz : (cutTwo T a₁ c₁ c₂ a₂).Reachable a₁ z.1
          · have hp : splicePos T a₁ c₁ c₂ a₂ m (Sum.inl z) = 0 := splicePos_inl_of_reachable hz
            omega
          · have hp : splicePos T a₁ c₁ c₂ a₂ m (Sum.inl z) = m + 1 := splicePos_inl_of_not hz
            have hz₂ := reachable_a₂_of_not hT he₁ he₂ hne h0 hz
            rw [hp, spliceVert_succ_self]
            have hQa₂ := hmid (m + 1) (by omega) (by omega) hlt
            rw [spliceVert_succ_self] at hQa₂
            exact goodWalk_side h hQ (Reachable.refl _) hz₂ (Or.inr rfl) hQa₂ hv
        · rw [splicePos_inr, spliceVert_inr]
          exact ⟨Walk.nil, fun z hz ↦ by simp at hz; rw [hz]; exact hv⟩
      · right; omega
    rcases Nat.lt_or_ge (splicePos T a₁ c₁ c₂ a₂ m u) (splicePos T a₁ c₁ c₂ a₂ m v) with hlt | hge
    · rcases hstart with hs | heq
      · rcases hend with he | heq
        · refine hs.trans (GoodWalk.trans ?_ he)
          obtain ⟨q, hq⟩ := exists_splice_walk_along hT he₁ he₂ hne h0
            (i := splicePos T a₁ c₁ c₂ a₂ m u) hle hpv
          exact ⟨q, fun z hz ↦ by
            obtain ⟨l, h1, h2, rfl⟩ := hq z hz
            exact hmid l h1 h2 hlt⟩
        · omega
      · omega
    · have heq : splicePos T a₁ c₁ c₂ a₂ m u = splicePos T a₁ c₁ c₂ a₂ m v := by omega
      -- Equal positions: both in `T₁`, both in `T₂`, or the same inner vertex.
      rcases u with x | j <;> rcases v with z | j'
      · by_cases hx : (cutTwo T a₁ c₁ c₂ a₂).Reachable a₁ x.1
        · have hz : (cutTwo T a₁ c₁ c₂ a₂).Reachable a₁ z.1 := by
            rw [← splicePos_inl_eq_zero_iff hT he₁ he₂ hne h0 (m := m)]
            rw [← heq]
            exact splicePos_inl_of_reachable hx
          exact goodWalk_side h hQ hx hz (Or.inl rfl) hu hv
        · have hz : ¬ (cutTwo T a₁ c₁ c₂ a₂).Reachable a₁ z.1 := by
            rw [← splicePos_inl_eq_zero_iff hT he₁ he₂ hne h0 (m := m)]
            rw [← heq]
            simp only [splicePos_inl_of_not hx]
            omega
          exact goodWalk_side h hQ (reachable_a₂_of_not hT he₁ he₂ hne h0 hx)
            (reachable_a₂_of_not hT he₁ he₂ hne h0 hz) (Or.inr rfl) hu hv
      · exfalso
        by_cases hx : (cutTwo T a₁ c₁ c₂ a₂).Reachable a₁ x.1
        · simp only [splicePos_inl_of_reachable hx, splicePos_inr] at heq
          omega
        · simp only [splicePos_inl_of_not hx, splicePos_inr] at heq
          omega
      · exfalso
        by_cases hz : (cutTwo T a₁ c₁ c₂ a₂).Reachable a₁ z.1
        · simp only [splicePos_inl_of_reachable hz, splicePos_inr] at heq
          omega
        · simp only [splicePos_inl_of_not hz, splicePos_inr] at heq
          omega
      · have : j = j' := Fin.ext (by simpa using heq)
        subst this
        exact ⟨Walk.nil, fun z hz ↦ by simp at hz; rw [hz]; exact hu⟩
  rcases le_total (splicePos T a₁ c₁ c₂ a₂ m u) (splicePos T a₁ c₁ c₂ a₂ m v) with hle | hle
  · exact main u v hu hv hle
  · exact (main v u hv hu hle).symm

include hT he₁ he₂ hne h0 h hP hA hB hA' hB' in
/-- `(T*, W*)` is a tree-decomposition of `G`. -/
theorem isTreeDecomp21_splice :
    IsTreeDecomp21 G (spliceTree T a₁ c₁ c₂ a₂ m) (spliceBag T a₁ c₁ c₂ a₂ m W W') := by
  classical
  have hle : ∀ u, spliceBag T a₁ c₁ c₂ a₂ m W W' u ≤ G := by
    rintro (x | j)
    · exact h.le x.1
    · exact hP.le _
  -- Every vertex or edge of `G` is in a bag of `T*`.
  have hcover : ∀ {Q : Hypergraph α β → Prop}, IsMemProp W W' Q → ∀ t, Q (W t) →
      ∃ u, Q (spliceBag T a₁ c₁ c₂ a₂ m W W' u) := by
    intro Q hQ t ht
    rcases mem_joinSet_or_reachable hT he₁ he₂ hne h0 t with htS | ht0
    · exact ⟨Sum.inl ⟨t, htS⟩, ht⟩
    · have hn : ¬ (cutTwo T a₁ c₁ c₂ a₂).Reachable a₁ t := fun h' ↦
        not_mem_joinSet_of_reachable hT he₁ he₂ hne h0 ht0 (Or.inl h')
      have hQB := (hQ.bag (fun t ↦ ¬ (cutTwo T a₁ c₁ c₂ a₂).Reachable a₁ t)).2 ⟨t, hn, ht⟩
      rw [← hB, hQ.bag'] at hQB
      obtain ⟨i, hi0, hi⟩ := hQB
      by_cases hil : i = Fin.last (m + 1)
      · rw [hil, hB', hQ.bag] at hi
        obtain ⟨t', ht', hQt'⟩ := hi
        exact ⟨Sum.inl ⟨t', Or.inr ht'⟩, hQt'⟩
      · have h1 : 1 ≤ i.1 := by
          have : i.1 ≠ 0 := fun h' ↦ hi0 (Fin.ext h')
          omega
        have h2 : i.1 ≤ m := by
          have : i.1 ≠ m + 1 := fun h' ↦ hil (Fin.ext h')
          omega
        refine ⟨Sum.inr ⟨i.1 - 1, by omega⟩, ?_⟩
        have : (⟨i.1 - 1 + 1, by omega⟩ : Fin (m + 2)) = i := Fin.ext (by simp; omega)
        show Q (W' ⟨i.1 - 1 + 1, _⟩)
        rwa [this]
  refine ⟨isTree_spliceTree hT he₁ he₂ hne h0, hle, ?_, ?_⟩
  · refine GM10.eq_of_le_of_vertexSet_eq_of_edgeSet_eq
      (GM10.biUnion_le_of_le fun u _ ↦ hle u) le_rfl ?_ ?_
    · apply Subset.antisymm
      · intro y hy
        simp only [Hypergraph.biUnion, Finset.mem_univ, iUnion_true, mem_iUnion] at hy
        obtain ⟨u, hu⟩ := hy
        exact (hle u).vertexSet_subset hu
      · intro y hy
        rw [← h.biUnion_eq] at hy
        simp only [Hypergraph.biUnion, Finset.mem_univ, iUnion_true, mem_iUnion] at hy ⊢
        obtain ⟨t, ht⟩ := hy
        exact hcover (isMemProp_vertex W W' y) t ht
    · apply Subset.antisymm
      · intro e he
        simp only [Hypergraph.biUnion, Finset.mem_univ, iUnion_true, mem_iUnion] at he
        obtain ⟨u, hu⟩ := he
        exact (hle u).edgeSet_subset hu
      · intro e he
        rw [← h.biUnion_eq] at he
        simp only [Hypergraph.biUnion, Finset.mem_univ, iUnion_true, mem_iUnion] at he ⊢
        obtain ⟨t, ht⟩ := he
        exact hcover (isMemProp_edge W W' e) t ht
  · intro u w v hp
    have hp' := Thomas.onTreePath_iff_forall_walk.1 hp
    refine le_of_subset_of_le (GM10.inter_le (hle u) (hle v)) (hle w) ?_ ?_
    · rintro y ⟨hyu, hyv⟩
      obtain ⟨q, hq⟩ := exists_goodWalk hT he₁ he₂ hne h0 h hP hA hB hA' hB'
        (isMemProp_vertex W W' y) hyu hyv
      exact hq w (hp' q)
    · rintro e ⟨heu, hev⟩
      obtain ⟨q, hq⟩ := exists_goodWalk hT he₁ he₂ hne h0 h hP hA hB hA' hB'
        (isMemProp_edge W W' e) heu hev
      exact hq w (hp' q)

end Bags

end GM21
end GraphMinor
