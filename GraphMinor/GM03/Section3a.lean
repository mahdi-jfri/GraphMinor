module

public import GraphMinor.GM03.Defs
public import GraphMinor.GM03.Cited
public import GraphMinor.GM03.Section1
public import GraphMinor.Menger.Basic

/-!
# Graph Minors III, Section 3: Sleeve Unions

This file formalizes Section 3 of
N. Robertson and P. D. Seymour, *Graph Minors. III. Planar Tree-Width*,
J. Combin. Theory Ser. B **36** (1984), 49–64 (pages 56–59):
- `theorem_3_1`, (3.1): branches $T_t(v)$ of $T$ at $t$ for $v \notin X_t$.
- `theorem_3_2`, (3.2): adjacent vertices outside $X_t$ lie in the same branch $T_t(v) = T_t(v')$.
- `theorem_3_3`, (3.3): vertices not separated by $X_t$ have $T_t(v) = T_t(v')$.
- `theorem_3_4`, (3.4): for an edge $e = \{t, t'\}$ of $T$, $X_t \cap X_{t'}$ separates the bags
  of the two components $N, N'$ of $T \setminus e$.
- `theorem_3_5`, (3.5): for $|V(T)| \ge 2$ and connected subgraphs $G_t$ disjoint from $X_t$,
  there is an edge $\{t, t'\}$ of $T$ such that $X_t \cap X_{t'}$ separates $V(G_t)$ and $V(G_{t'})$.
- `theorem_3_6`, (3.6): Menger's theorem on the $r \times s$ cylinder ($r \le 2s$).
- `theorem_3_7`, (3.7): in any tree-decomposition of the $r \times s$ cylinder ($r \le 2s$), some
  bag $X_{t_0}$ has $r$ vertex-disjoint paths to the central circle $C_s$.
- `theorem_3_8`, (3.8): identifying the central circle of an $r \times s$ cylinder with $r$
  vertices $v_1, \dots, v_r$ of $H$ forces $v_1, \dots, v_r$ into a single bag of a
  tree-decomposition of $H$ of width $\le w$.
- `theorem_3_9`, (3.9): if $G$ is the sleeve union of $G_1, G_2$, then $G_1, G_2$ are isomorphic
  to proper minors of $G$.
- `theorem_3_10`, (3.10): if $G$ is the sleeve union of $G_1, G_2$, then the tree-width of $G$ is
  the maximum of the tree-widths of $G_1, G_2$.
-/

@[expose] public section

namespace GraphMinor.GM03

open Set Function Classical
open Graph SimpleGraph Hypergraph
open GraphMinor GraphMinor.Surface GraphMinor.GM06 GraphMinor.GM09
open GraphMinor.GM22 GraphMinor.Thomas

universe u v u₁ v₁ u₂ v₂ w

/-! ## 1. Branches of a Tree-Decomposition: (3.1)–(3.5) -/

/-- A walk in `T` between `s` and `s'` avoiding `t` exists if and only if `¬ OnTreePath T s s' t`. -/
lemma exists_walk_avoiding_iff_not_onTreePath {ι : Type w} (T : SimpleGraph ι) (s s' t : ι) :
    (∃ w : T.Walk s s', t ∉ w.support) ↔ ¬ OnTreePath T s s' t := by
  rw [onTreePath_iff_forall_walk, not_forall]

/-- If `¬ OnTreePath T s s' t`, then `s' ≠ t`. -/
lemma ne_of_not_onTreePath {ι : Type w} {T : SimpleGraph ι} {s s' t : ι}
    (h : ¬ OnTreePath T s s' t) : s' ≠ t := by
  rintro rfl
  exact h (onTreePath_right T s s')

/-- In a tree `T`, if `¬ OnTreePath T s₁ s₂ t` and `¬ OnTreePath T s₂ s₃ t`, then
`¬ OnTreePath T s₁ s₃ t`. -/
lemma not_onTreePath_trans {ι : Type w} {T : SimpleGraph ι} (hT : T.IsTree) {s₁ s₂ s₃ t : ι}
    (h₁₂ : ¬ OnTreePath T s₁ s₂ t) (h₂₃ : ¬ OnTreePath T s₂ s₃ t) :
    ¬ OnTreePath T s₁ s₃ t := by
  intro h₁₃
  rcases onTreePath_left_or_right hT s₂ h₁₃ with h | h
  · exact h₁₂ h
  · exact h₂₃ h

/-- If `(T, X)` is a tree-decomposition of `G`, `v ∉ X t`, and `v ∈ X s₀`, then `treeBranchAt T X t v`
is the branch of `T` at `t` containing `s₀`. -/
lemma treeBranchAt_eq_of_mem_bag {α : Type u} {β : Type v} {ι : Type w}
    {G : Graph α β} {T : SimpleGraph ι} {X : ι → Set α}
    (hTD : IsTreeDecomposition G T X) {t s₀ : ι} {v : α}
    (hv : v ∉ X t) (hs₀ : v ∈ X s₀) :
    treeBranchAt T X t v = {s' : ι | s' ≠ t ∧ ∃ w : T.Walk s₀ s', t ∉ w.support} := by
  ext s'
  simp only [treeBranchAt, mem_ofPred_eq, exists_walk_avoiding_iff_not_onTreePath]
  constructor
  · rintro ⟨hs't, s, hvs, hss'⟩
    refine ⟨hs't, ?_⟩
    have hs₀s : ¬ OnTreePath T s₀ s t := fun hp ↦ hv (hTD.inter_subset_on_path hp ⟨hs₀, hvs⟩)
    exact not_onTreePath_trans hTD.isTree hs₀s hss'
  · rintro ⟨hs't, hs₀s'⟩
    exact ⟨hs't, s₀, hs₀, hs₀s'⟩

/-- Graph Minors III, (3.1) (page 56):
"(3.1) *For $t \in V(T)$ and $v \in V(G)$, either $v \in X_t$, or there is a branch of $T$ at $t$
which contains all $t' \in V(T)$ with $v \in X_{t'}$.*" -/
theorem theorem_3_1_proof {α : Type u} {β : Type v} {ι : Type w}
    {G : Graph α β} {T : SimpleGraph ι} {X : ι → Set α}
    (hTD : IsTreeDecomposition G T X) (t : ι) {v : α} (hv : v ∈ V(G)) :
    v ∈ X t ∨
      (IsBranchAt T t (treeBranchAt T X t v) ∧
        ∀ t' : ι, v ∈ X t' → t' ∈ treeBranchAt T X t v) := by
  by_cases hvt : v ∈ X t
  · exact Or.inl hvt
  · right
    have hv_union : v ∈ ⋃ s : ι, X s := hTD.iUnion_bags.symm ▸ hv
    obtain ⟨s₀, hs₀⟩ := mem_iUnion.mp hv_union
    have hs₀t : s₀ ≠ t := fun h ↦ hvt (h ▸ hs₀)
    refine ⟨⟨s₀, hs₀t, treeBranchAt_eq_of_mem_bag hTD hvt hs₀⟩, fun t' ht' ↦ ?_⟩
    have ht't : t' ≠ t := fun h ↦ hvt (h ▸ ht')
    refine ⟨ht't, t', ht', .nil, ?_⟩
    simp [ht't.symm]

/-- Graph Minors III, (3.2) (page 56):
"(3.2) *If $v, v' \notin X_t$ and $v, v'$ are adjacent in $G$ then $T_t(v) = T_t(v')$.*" -/
theorem theorem_3_2_proof {α : Type u} {β : Type v} {ι : Type w}
    {G : Graph α β} {T : SimpleGraph ι} {X : ι → Set α}
    (hTD : IsTreeDecomposition G T X) (t : ι) {v v' : α}
    (hv : v ∉ X t) (hv' : v' ∉ X t) (hadj : G.Adj v v') :
    treeBranchAt T X t v = treeBranchAt T X t v' := by
  obtain ⟨e, hl⟩ := hadj
  obtain ⟨t', hvt', hv't'⟩ := hTD.edge_in_bag hl
  rw [treeBranchAt_eq_of_mem_bag hTD hv hvt', treeBranchAt_eq_of_mem_bag hTD hv' hv't']

/-- Along any walk in `G` avoiding `X t`, all vertices have the same branch `treeBranchAt T X t`. -/
lemma treeBranchAt_eq_of_walk_avoiding {α : Type u} {β : Type v} {ι : Type w}
    {G : Graph α β} {T : SimpleGraph ι} {X : ι → Set α}
    (hTD : IsTreeDecomposition G T X) (t : ι) {v v' : α}
    (W : GraphWalk G v v') (hav : ∀ x ∈ W.support, x ∉ X t) :
    treeBranchAt T X t v = treeBranchAt T X t v' := by
  induction W with
  | nil _ => rfl
  | @cons u w _ e hl rest ih =>
    have hu : u ∉ X t := hav u (List.mem_cons_self)
    have hw : w ∉ X t := hav w (List.mem_cons_of_mem _ rest.start_mem_support)
    have hstep := theorem_3_2_proof hTD t hu hw ⟨e, hl⟩
    exact hstep.trans (ih fun x hx ↦ hav x (List.mem_cons_of_mem _ hx))

/-- Graph Minors III, (3.3) (page 56):
"(3.3) *If $v, v' \notin X_t$ and $v, v'$ are not separated in $G$ by $X_t$, then
$T_t(v) = T_t(v')$.*" -/
theorem theorem_3_3_proof {α : Type u} {β : Type v} {ι : Type w}
    {G : Graph α β} {T : SimpleGraph ι} {X : ι → Set α}
    (hTD : IsTreeDecomposition G T X) (t : ι) {v v' : α}
    (hv : v ∉ X t) (hv' : v' ∉ X t)
    (hnot_sep : ¬ Separates G (X t) {v} {v'}) :
    treeBranchAt T X t v = treeBranchAt T X t v' := by
  unfold Separates at hnot_sep
  push Not at hnot_sep
  obtain ⟨P, ⟨u₀, hu₀, w₀, hw₀, hPG, W, _, hVP, _⟩, hdisj⟩ := hnot_sep
  rw [mem_singleton_iff] at hu₀ hw₀
  subst hu₀ hw₀
  obtain ⟨W_G, hsupp, _⟩ := exists_walk_up_of_le hPG W
  refine treeBranchAt_eq_of_walk_avoiding hTD t W_G fun x hx hxXt ↦ ?_
  have hxP : x ∈ V(P) := by rw [hVP, ← hsupp]; exact hx
  exact disjoint_left.mp hdisj hxP hxXt

/-- If `T.Adj t t'`, then every vertex `n` of `T` lies in `treeEdgeSide T t t'` or
`treeEdgeSide T t' t`. -/
lemma mem_treeEdgeSide_or_symm {ι : Type w} {T : SimpleGraph ι} (hT : T.IsTree) {t t' : ι}
    (hadj : T.Adj t t') (n : ι) :
    n ∈ treeEdgeSide T t t' ∨ n ∈ treeEdgeSide T t' t := by
  rcases onTreePath_adj_dichotomy hT hadj n with ⟨_, h2⟩ | ⟨_, h2⟩
  · exact Or.inl (fun h ↦ h2 (onTreePath_symm h))
  · exact Or.inr (fun h ↦ h2 (onTreePath_symm h))

/-- If `n ∈ treeEdgeSide T t t'` and `n' ∈ treeEdgeSide T t' t`, then both `t` and `t'` lie on the
path of `T` between `n` and `n'`. -/
lemma onTreePath_of_mem_treeEdgeSide {ι : Type w} {T : SimpleGraph ι} (hT : T.IsTree) {t t' n n' : ι}
    (hadj : T.Adj t t') (hn : n ∈ treeEdgeSide T t t') (hn' : n' ∈ treeEdgeSide T t' t) :
    OnTreePath T n n' t ∧ OnTreePath T n n' t' := by
  have hs₁ : OnTreePath T n t' t := by
    rcases onTreePath_adj_dichotomy hT hadj n with ⟨h1, _⟩ | ⟨h1, _⟩
    · exact h1
    · exact (hn (onTreePath_symm h1)).elim
  have hs₂ : OnTreePath T n' t t' := by
    rcases onTreePath_adj_dichotomy hT hadj n' with ⟨h1, _⟩ | ⟨h1, _⟩
    · exact (hn' (onTreePath_symm h1)).elim
    · exact h1
  exact onTreePath_of_sides hT hadj hs₁ hs₂

/-- Graph Minors III, (3.4) (page 57):
"(3.4) *Let $e$ be an edge of $T$ with ends $t, t'$ say, and let $N, N'$ be the vertex sets of the
two components of $T \setminus e$. Then $X_t \cap X_{t'}$ separates $\bigcup(X_n : n \in N)$ and
$\bigcup(X_n : n \in N')$.*" -/
theorem theorem_3_4_proof {α : Type u} {β : Type v} {ι : Type w}
    {G : Graph α β} {T : SimpleGraph ι} {X : ι → Set α}
    (hTD : IsTreeDecomposition G T X) {t t' : ι} (hadj : T.Adj t t') :
    Separates G (X t ∩ X t')
      (⋃ n ∈ treeEdgeSide T t t', X n) (⋃ n ∈ treeEdgeSide T t' t, X n) := by
  have hdisj_sides : ∀ {x : α}, x ∉ X t ∩ X t' →
      x ∈ (⋃ n ∈ treeEdgeSide T t t', X n) → x ∉ (⋃ n' ∈ treeEdgeSide T t' t, X n') := by
    intro x hx hN hN'
    obtain ⟨n, hn, hxn⟩ := mem_iUnion₂.mp hN
    obtain ⟨n', hn', hxn'⟩ := mem_iUnion₂.mp hN'
    obtain ⟨hpt, hpt'⟩ := onTreePath_of_mem_treeEdgeSide hTD.isTree hadj hn hn'
    exact hx ⟨hTD.inter_subset_on_path hpt ⟨hxn, hxn'⟩,
      hTD.inter_subset_on_path hpt' ⟨hxn, hxn'⟩⟩
  have hwalk_side : ∀ {u v : α} (W : GraphWalk G u v),
      (∀ x ∈ W.support, x ∉ X t ∩ X t') →
      u ∈ (⋃ n ∈ treeEdgeSide T t t', X n) →
      v ∈ (⋃ n ∈ treeEdgeSide T t t', X n) := by
    intro u v W
    induction W with
    | nil _ => exact fun _ hu ↦ hu
    | @cons u w v e hl rest ih =>
      intro hav hu
      have hu_not : u ∉ X t ∩ X t' := hav u List.mem_cons_self
      obtain ⟨t'', hut'', hwt''⟩ := hTD.edge_in_bag hl
      have ht''_side : t'' ∈ treeEdgeSide T t t' := by
        rcases mem_treeEdgeSide_or_symm hTD.isTree hadj t'' with h | h
        · exact h
        · exfalso
          exact hdisj_sides hu_not hu (mem_iUnion₂.mpr ⟨t'', h, hut''⟩)
      have hw : w ∈ ⋃ n ∈ treeEdgeSide T t t', X n := mem_iUnion₂.mpr ⟨t'', ht''_side, hwt''⟩
      exact ih (fun x hx ↦ hav x (List.mem_cons_of_mem _ hx)) hw
  intro P ⟨u, hu, v, hv, hPG, W, _, hVP, _⟩ hdisj
  obtain ⟨W_G, hsupp, _⟩ := exists_walk_up_of_le hPG W
  have hav : ∀ x ∈ W_G.support, x ∉ X t ∩ X t' := by
    intro x hx hx_inter
    have hxP : x ∈ V(P) := by rw [hVP, ← hsupp]; exact hx
    exact disjoint_left.mp hdisj hxP hx_inter
  have hv_N : v ∈ ⋃ n ∈ treeEdgeSide T t t', X n := hwalk_side W_G hav hu
  have hv_not : v ∉ X t ∩ X t' := hav v W_G.end_mem_support
  exact hdisj_sides hv_not hv_N hv

/-- In a tree `T`, if `s ≠ t`, there is a neighbor `t'` of `t` such that `t` does not lie on the
path of `T` between `t'` and `s` (`s ∈ treeEdgeSide T t' t`). -/
lemma exists_adj_mem_treeEdgeSide_of_ne {ι : Type w} {T : SimpleGraph ι} (hT : T.IsTree)
    {t s : ι} (hne : s ≠ t) :
    ∃ t' : ι, T.Adj t t' ∧ s ∈ treeEdgeSide T t' t := by
  have hp := treePath_isPath hT t s
  generalize hw : treePath hT t s = w at hp
  cases w with
  | nil => exact (hne rfl).elim
  | @cons _ t' _ hadj rest =>
    refine ⟨t', hadj, ?_⟩
    change ¬ OnTreePath T t' s t
    rw [← exists_walk_avoiding_iff_not_onTreePath]
    exact ⟨rest, ( Walk.cons_isPath_iff hadj rest).mp hp |>.2⟩

/-- Graph Minors III, (3.5) (page 57):
"(3.5) *Let $|V(T)| \ge 2$, and for each $t \in V(T)$ let $G_t$ be a connected subgraph of $G$ with
$V(G_t) \cap X_t = \emptyset$. Then there exist $t, t' \in V(T)$, adjacent in $T$, such that
$X_t \cap X_{t'}$ separates $V(G_t)$ and $V(G_{t'})$ in $G$.*" -/
theorem theorem_3_5_proof {α : Type u} {β : Type v} {ι : Type w} [Fintype ι]
    {G : Graph α β} {T : SimpleGraph ι} {X : ι → Set α}
    (hTD : IsTreeDecomposition G T X) (_hT_card : 2 ≤ Fintype.card ι)
    (G_sub : ι → Graph α β)
    (hsub : ∀ t : ι, G_sub t ≤ G)
    (hconn : ∀ t : ι, IsGraphConnected (G_sub t))
    (hdisj : ∀ t : ι, Disjoint V(G_sub t) (X t)) :
    ∃ t t' : ι, T.Adj t t' ∧ Separates G (X t ∩ X t') V(G_sub t) V(G_sub t') := by
  have hex_next : ∀ t : ι, ∃ t' : ι, T.Adj t t' ∧
      V(G_sub t) ⊆ ⋃ n ∈ treeEdgeSide T t' t, X n := by
    intro t
    obtain ⟨v₀, hv₀⟩ := (hconn t).1
    have hv₀G : v₀ ∈ V(G) := (hsub t).vertexSet_mono hv₀
    have hv₀_not : v₀ ∉ X t := disjoint_left.mp (hdisj t) hv₀
    have hv₀_union : v₀ ∈ ⋃ s : ι, X s := hTD.iUnion_bags.symm ▸ hv₀G
    obtain ⟨s₀, hs₀⟩ := mem_iUnion.mp hv₀_union
    have hs₀t : s₀ ≠ t := fun h ↦ hv₀_not (h ▸ hs₀)
    obtain ⟨t', hadj, hs₀_side⟩ := exists_adj_mem_treeEdgeSide_of_ne hTD.isTree hs₀t
    refine ⟨t', hadj, fun v hv ↦ ?_⟩
    have hvG : v ∈ V(G) := (hsub t).vertexSet_mono hv
    have hv_not : v ∉ X t := disjoint_left.mp (hdisj t) hv
    obtain ⟨W_sub⟩ := (hconn t).2 v₀ hv₀ v hv
    obtain ⟨W_G, hsupp, _⟩ := exists_walk_up_of_le (hsub t) W_sub
    have hav : ∀ x ∈ W_G.support, x ∉ X t := by
      intro x hx
      rw [hsupp] at hx
      exact disjoint_left.mp (hdisj t) (W_sub.mem_vertexSet_of_mem_support hx)
    have hbranch_eq : treeBranchAt T X t v₀ = treeBranchAt T X t v :=
      treeBranchAt_eq_of_walk_avoiding hTD t W_G hav
    have hv_union : v ∈ ⋃ s : ι, X s := hTD.iUnion_bags.symm ▸ hvG
    obtain ⟨s, hs⟩ := mem_iUnion.mp hv_union
    have hs_mem : s ∈ treeBranchAt T X t v₀ := by
      rw [hbranch_eq]
      rcases theorem_3_1_proof hTD t hvG with hvt | ⟨_, hall⟩
      · exact (hv_not hvt).elim
      · exact hall s hs
    rw [treeBranchAt_eq_of_mem_bag hTD hv₀_not hs₀] at hs_mem
    obtain ⟨_, w₀, hw₀⟩ := hs_mem
    have hnot_s₀s : ¬ OnTreePath T s₀ s t :=
      (exists_walk_avoiding_iff_not_onTreePath T s₀ s t).mp ⟨w₀, hw₀⟩
    have hs_side : s ∈ treeEdgeSide T t' t :=
      not_onTreePath_trans hTD.isTree hs₀_side hnot_s₀s
    exact mem_iUnion₂.mpr ⟨s, hs_side, hs⟩
  choose next hadj_next hsub_next using hex_next
  let f : ι → T.edgeSet := fun t ↦ ⟨s(t, next t), hadj_next t⟩
  have hcard_lt : Fintype.card T.edgeSet < Fintype.card ι := by
    have htree_card := hTD.isTree.card_edgeFinset
    rw [SimpleGraph.edgeFinset, Set.toFinset_card] at htree_card
    omega
  obtain ⟨t, t', hne, hfeq⟩ := Fintype.exists_ne_map_eq_of_card_lt f hcard_lt
  have hsym : s(t, next t) = s(t', next t') := Subtype.mk.inj hfeq
  rw [Sym2.eq_iff] at hsym
  rcases hsym with ⟨rfl, _⟩ | ⟨ht_eq, ht'_eq⟩
  · exact (hne rfl).elim
  · refine ⟨t, t', ht'_eq ▸ hadj_next t, ?_⟩
    intro P ⟨u, hu, v, hv, hP⟩
    have hu' : u ∈ ⋃ n ∈ treeEdgeSide T t' t, X n := ht'_eq ▸ hsub_next t hu
    have hv' : v ∈ ⋃ n ∈ treeEdgeSide T t t', X n := ht_eq.symm ▸ hsub_next t' hv
    have hsep := theorem_3_4_proof hTD (ht'_eq ▸ hadj_next t).symm
    have hInter_comm : X t' ∩ X t = X t ∩ X t' := inter_comm _ _
    rw [hInter_comm] at hsep
    exact hsep P ⟨u, hu', v, hv', hP⟩

/-! ## 2. Connected Vertex Sets in Tree-Decompositions and Minor Monotonicity -/

/-- For a connected subgraph `K ≤ G`, the set of tree vertices `{t : ι | (X t ∩ V(K)).Nonempty}`
is convex in `T`: if `t'` lies on the path of `T` between `t₁` and `t₂`, and `X t₁` and `X t₂`
both meet `V(K)`, then `X t'` also meets `V(K)`. -/
lemma nonempty_inter_onTreePath_of_isGraphConnected {α : Type u} {β : Type v} {ι : Type w}
    {G K : Graph α β} {T : SimpleGraph ι} {X : ι → Set α}
    (hTD : IsTreeDecomposition G T X) (hKG : K ≤ G) (hconn : IsGraphConnected K)
    {t₁ t₂ t' : ι} (hp : OnTreePath T t₁ t₂ t')
    (h₁ : (X t₁ ∩ V(K)).Nonempty) (h₂ : (X t₂ ∩ V(K)).Nonempty) :
    (X t' ∩ V(K)).Nonempty := by
  by_contra hnot
  rw [not_nonempty_iff_eq_empty] at hnot
  obtain ⟨v₁, hv₁t₁, hv₁K⟩ := h₁
  obtain ⟨v₂, hv₂t₂, hv₂K⟩ := h₂
  have hv₁_not : v₁ ∉ X t' := fun h ↦ by
    have : v₁ ∈ X t' ∩ V(K) := ⟨h, hv₁K⟩
    rw [hnot] at this
    exact this
  have hv₂_not : v₂ ∉ X t' := fun h ↦ by
    have : v₂ ∈ X t' ∩ V(K) := ⟨h, hv₂K⟩
    rw [hnot] at this
    exact this
  obtain ⟨W_K⟩ := hconn.2 v₁ hv₁K v₂ hv₂K
  obtain ⟨W_G, hsupp, _⟩ := exists_walk_up_of_le hKG W_K
  have hav : ∀ x ∈ W_G.support, x ∉ X t' := by
    intro x hx hx_t'
    rw [hsupp] at hx
    have hxK : x ∈ V(K) := W_K.mem_vertexSet_of_mem_support hx
    have : x ∈ X t' ∩ V(K) := ⟨hx_t', hxK⟩
    rw [hnot] at this
    exact this
  have hbranch_eq : treeBranchAt T X t' v₁ = treeBranchAt T X t' v₂ :=
    treeBranchAt_eq_of_walk_avoiding hTD t' W_G hav
  have ht₂_mem : t₂ ∈ treeBranchAt T X t' v₁ := by
    rw [hbranch_eq, treeBranchAt_eq_of_mem_bag hTD hv₂_not hv₂t₂]
    have ht₂t' : t₂ ≠ t' := fun h ↦ hv₂_not (h ▸ hv₂t₂)
    exact ⟨ht₂t', .nil, by simp [ht₂t'.symm]⟩
  rw [treeBranchAt_eq_of_mem_bag hTD hv₁_not hv₁t₁] at ht₂_mem
  obtain ⟨_, w, hw⟩ := ht₂_mem
  exact ((exists_walk_avoiding_iff_not_onTreePath T t₁ t₂ t').mp ⟨w, hw⟩) hp

/-- Given a tree-decomposition `(T, Y)` of `G` and a family `Z : α₂ → Graph α₁ β₁` assigning to
each `u ∈ V(H)` a connected subgraph `Z u ≤ G` such that the sets `V(Z u)` (`u ∈ V(H)`) are
pairwise disjoint and every edge of `H` between `u` and `w` corresponds to a bag `Y t` meeting both
`V(Z u)` and `V(Z w)`, defining `X t := {u ∈ V(H) | (Y t ∩ V(Z u)).Nonempty}` yields a
tree-decomposition `(T, X)` of `H` whose width does not exceed that of `(T, Y)`. -/
lemma isTreeDecomposition_of_connected_subgraphs
    {α₁ : Type u₁} {β₁ : Type v₁} {α₂ : Type u₂} {β₂ : Type v₂} {ι : Type w}
    {G : Graph α₁ β₁} {H : Graph α₂ β₂} {T : SimpleGraph ι} {Y : ι → Set α₁}
    (hVG : V(G).Finite) (hTD : IsTreeDecomposition G T Y)
    (Z : α₂ → Graph α₁ β₁)
    (hZ_le : ∀ u ∈ V(H), Z u ≤ G)
    (hZ_conn : ∀ u ∈ V(H), IsGraphConnected (Z u))
    (hZ_disj : ∀ u₁ ∈ V(H), ∀ u₂ ∈ V(H), u₁ ≠ u₂ → Disjoint V(Z u₁) V(Z u₂))
    (hZ_edge : ∀ ⦃e : β₂⦄ ⦃u w : α₂⦄, H.IsLink e u w →
      ∃ t : ι, (Y t ∩ V(Z u)).Nonempty ∧ (Y t ∩ V(Z w)).Nonempty) :
    let X : ι → Set α₂ := fun t ↦ {u ∈ V(H) | (Y t ∩ V(Z u)).Nonempty}
    IsTreeDecomposition H T X ∧
      ∀ w : ℕ, TreeDecompHasWidthLE Y w → TreeDecompHasWidthLE X w := by
  intro X
  refine ⟨?_, fun w hw t ↦ ?_⟩
  · refine
      { isTree := hTD.isTree
        bag_subset := fun t u hu ↦ hu.1
        iUnion_bags := ?_
        edge_in_bag := ?_
        inter_subset_on_path := ?_ }
    · ext u
      rw [mem_iUnion]
      constructor
      · rintro ⟨t, huH, _⟩
        exact huH
      · intro huH
        obtain ⟨x, hx⟩ := (hZ_conn u huH).1
        have hxG : x ∈ V(G) := (hZ_le u huH).vertexSet_mono hx
        rw [← hTD.iUnion_bags, mem_iUnion] at hxG
        obtain ⟨t, hxt⟩ := hxG
        exact ⟨t, huH, x, hxt, hx⟩
    · intro e u w hl
      obtain ⟨t, hu, hw⟩ := hZ_edge hl
      exact ⟨t, ⟨hl.left_mem, hu⟩, ⟨hl.right_mem, hw⟩⟩
    · intro t₁ t' t₂ hp u ⟨⟨huH, h₁⟩, ⟨_, h₂⟩⟩
      exact ⟨huH,
        nonempty_inter_onTreePath_of_isGraphConnected hTD (hZ_le u huH) (hZ_conn u huH) hp h₁ h₂⟩
  · have hfinY : (Y t).Finite := hVG.subset (hTD.bag_subset t)
    let f : ↥(X t) → ↥(Y t) := fun u ↦
      ⟨u.2.2.choose, u.2.2.choose_spec.1⟩
    have hf_inj : Function.Injective f := by
      intro u₁ u₂ heq
      by_contra hne
      have hval : u₁.2.2.choose = u₂.2.2.choose := congrArg Subtype.val heq
      have hu₁_ne_u₂ : u₁.1 ≠ u₂.1 := fun h ↦ hne (Subtype.ext h)
      have hdisj := hZ_disj u₁.1 u₁.2.1 u₂.1 u₂.2.1 hu₁_ne_u₂
      exact Set.disjoint_left.mp hdisj u₁.2.2.choose_spec.2 (hval.symm ▸ u₂.2.2.choose_spec.2)
    have : Finite ↥(Y t) := hfinY.to_subtype
    have hle := Nat.card_le_card_of_injective f hf_inj
    rw [Nat.card_coe_set_eq, Nat.card_coe_set_eq] at hle
    exact hle.trans (hw t)

/-- If `H` is isomorphic to a minor of a finite graph `G` and `G` has tree-width `≤ w`, then `H`
has tree-width `≤ w`. (Used in `(2.6)` and `(3.10)`.) -/
theorem treeWidthLE_of_isIsoMinor {α₁ : Type u₁} {β₁ : Type v₁} {α₂ : Type u₂} {β₂ : Type v₂}
    {H : Graph α₁ β₁} {G : Graph α₂ β₂} (hVG : V(G).Finite)
    (hMinor : IsIsoMinor H G) {w : ℕ} (htw : TreeWidthLE G w) :
    TreeWidthLE H w := by
  rw [treeWidthLE_iff_exists_isTreeDecomposition] at htw ⊢
  obtain ⟨ι, hfin, T, Y, hTD, hw⟩ := htw
  let _ : Fintype ι := hfin
  obtain ⟨G', hle, C, _, ⟨φ⟩⟩ := hMinor
  let compRel (x y : α₂) : Prop := ∃ e ∈ C, G'.IsLink e x y
  let compSet (v : α₂) : Set α₂ := {y | Relation.ReflTransGen compRel v y}
  have hcomp_symm : ∀ a b, Relation.ReflTransGen compRel a b →
      Relation.ReflTransGen compRel b a := by
    intro a b hab
    induction hab with
    | refl => exact .refl
    | tail _ hst ih =>
      obtain ⟨e, heC, hl⟩ := hst
      exact Relation.ReflTransGen.head ⟨e, heC, hl.symm⟩ ih
  have hcomp_eq : ∀ {v y : α₂}, y ∈ compSet v → compSet v = compSet y := by
    intro v y hy
    ext z
    exact ⟨fun hvz ↦ (hcomp_symm v y hy).trans hvz, fun hyz ↦ hy.trans hyz⟩
  have hcomp_sub : ∀ {v : α₂}, v ∈ V(G') → compSet v ⊆ V(G') := by
    intro v hv y hy
    induction hy with
    | refl => exact hv
    | tail _ hst _ => obtain ⟨_, _, hl⟩ := hst; exact hl.right_mem
  have hcomp_walk : ∀ {v : α₂} (_hv : v ∈ V(G')) {x y : α₂},
      x ∈ compSet v → Relation.ReflTransGen compRel x y →
      Nonempty (GraphWalk ((G'.restrict C).induce (compSet v)) x y) := by
    intro v _ x y hx hxy
    induction hxy with
    | refl => exact ⟨.nil hx⟩
    | @tail a b hab hst ih =>
      have ha : a ∈ compSet v := hx.trans hab
      have hb : b ∈ compSet v := hx.trans (hab.tail hst)
      obtain ⟨W⟩ := ih
      obtain ⟨e, heC, hl⟩ := hst
      have hl_sub : ((G'.restrict C).induce (compSet v)).IsLink e a b :=
        ⟨⟨heC, hl⟩, ha, hb⟩
      exact ⟨W.append (.cons hl_sub (.nil hb))⟩
  let Z : α₁ → Graph α₂ β₂ := fun u ↦
    if hu : u ∈ V(H) then (G'.restrict C).induce (φ.vertexEquiv ⟨u, hu⟩).1 else ⊥
  have hZ_mem : ∀ u (hu : u ∈ V(H)), ∃ v₀ ∈ V(G'), compSet v₀ = (φ.vertexEquiv ⟨u, hu⟩).1 := by
    intro u hu
    have hmem := (φ.vertexEquiv ⟨u, hu⟩).2
    simpa [contract] using hmem
  have hZ_le : ∀ u ∈ V(H), Z u ≤ G := by
    intro u hu
    dsimp [Z]
    rw [dite_eq_left hu]
    obtain ⟨v₀, hv₀, hcv₀⟩ := hZ_mem u hu
    have hsub : (φ.vertexEquiv ⟨u, hu⟩).1 ⊆ V(G'.restrict C) := hcv₀ ▸ hcomp_sub hv₀
    exact ((G'.restrict C).induce_le hsub).trans (restrict_le.trans hle)
  have hZ_conn : ∀ u ∈ V(H), IsGraphConnected (Z u) := by
    intro u hu
    dsimp [Z]
    rw [dite_eq_left hu]
    obtain ⟨v₀, hv₀, hcv₀⟩ := hZ_mem u hu
    have hv₀_in : v₀ ∈ (φ.vertexEquiv ⟨u, hu⟩).1 := hcv₀ ▸ Relation.ReflTransGen.refl
    refine ⟨⟨v₀, hv₀_in⟩, fun x hx y hy ↦ ?_⟩
    rw [← hcv₀] at hx hy ⊢
    exact hcomp_walk hv₀ hx ((hcomp_symm v₀ x hx).trans hy)
  have hZ_disj : ∀ u₁ ∈ V(H), ∀ u₂ ∈ V(H), u₁ ≠ u₂ → Disjoint V(Z u₁) V(Z u₂) := by
    intro u₁ hu₁ u₂ hu₂ hne
    dsimp [Z]
    rw [dite_eq_left hu₁, dite_eq_left hu₂]
    refine Set.disjoint_left.mpr fun z hz₁ hz₂ ↦ ?_
    obtain ⟨v₁, _, hcv₁⟩ := hZ_mem u₁ hu₁
    obtain ⟨v₂, _, hcv₂⟩ := hZ_mem u₂ hu₂
    have heq₁ : (φ.vertexEquiv ⟨u₁, hu₁⟩).1 = compSet z :=
      hcv₁.symm.trans (hcomp_eq (hcv₁.symm ▸ hz₁))
    have heq₂ : (φ.vertexEquiv ⟨u₂, hu₂⟩).1 = compSet z :=
      hcv₂.symm.trans (hcomp_eq (hcv₂.symm ▸ hz₂))
    have hinj := φ.vertexEquiv.injective (Subtype.ext (heq₁.trans heq₂.symm))
    exact hne (Subtype.mk.inj hinj)
  have hZ_edge : ∀ ⦃e : β₁⦄ ⦃u w : α₁⦄, H.IsLink e u w →
      ∃ t : ι, (Y t ∩ V(Z u)).Nonempty ∧ (Y t ∩ V(Z w)).Nonempty := by
    intro e u w hl
    have hu : u ∈ V(H) := hl.left_mem
    have hw : w ∈ V(H) := hl.right_mem
    have hlc := (φ.isLink_iff ⟨e, hl.edge_mem⟩ ⟨u, hu⟩ ⟨w, hw⟩).mp hl
    simp only [contract, deleteEdges_isLink, map_isLink, Relation.Map] at hlc
    obtain ⟨⟨x, y, hlG', hcx, hcy⟩, _⟩ := hlc
    obtain ⟨t, hxt, hyt⟩ := hTD.edge_in_bag (hlG'.mono hle)
    refine ⟨t, ⟨x, hxt, ?_⟩, ⟨y, hyt, ?_⟩⟩
    · dsimp [Z]; rw [dite_eq_left hu]; exact hcx ▸ Relation.ReflTransGen.refl
    · dsimp [Z]; rw [dite_eq_left hw]; exact hcy ▸ Relation.ReflTransGen.refl
  obtain ⟨hTD_H, hw_H⟩ :=
    isTreeDecomposition_of_connected_subgraphs hVG hTD Z hZ_le hZ_conn hZ_disj hZ_edge
  exact ⟨ι, hfin, T, _, hTD_H, hw_H w hw⟩

/-! ## 3. Menger's Theorem for `Graph α β` -/

/-- Menger's theorem for a finite graph `G : Graph α β`: if every vertex set `Y ⊆ V(G)` separating
`A` and `B` has `k ≤ Y.ncard`, then there exist `k` pairwise vertex-disjoint paths of `G` between
`A` and `B`. -/
theorem exists_disjoint_isPathBetween_of_separates {α : Type u} {β : Type v}
    {G : Graph α β} (hVG : V(G).Finite) {A B : Set α} (hA : A ⊆ V(G)) (hB : B ⊆ V(G))
    (k : ℕ) (hsep : ∀ Y ⊆ V(G), Separates G Y A B → k ≤ Y.ncard) :
    ∃ P : Fin k → Graph α β,
      Pairwise (fun i₁ i₂ : Fin k => Disjoint V(P i₁) V(P i₂)) ∧
      ∀ i : Fin k, IsPathBetween G (P i) A B := by
  let K : SimpleGraph ↥V(G) := SimpleGraph.fromRel (fun u v : ↥V(G) ↦ G.Adj u.1 v.1)
  have hK_adj : ∀ {u v : ↥V(G)}, K.Adj u v ↔ u ≠ v ∧ G.Adj u.1 v.1 := by
    intro u v
    rw [SimpleGraph.fromRel_adj]
    exact and_congr_right fun _ ↦ ⟨fun h ↦ h.elim id (fun ⟨e, hl⟩ ↦ ⟨e, hl.symm⟩), Or.inl⟩
  have hlift_walk : ∀ {u v : ↥V(G)} (p : K.Walk u v), p.IsPath →
      ∃ W : GraphWalk G u.1 v.1, W.IsSimple ∧ W.support = p.support.map Subtype.val := by
    intro u v p
    induction p with
    | @nil u =>
      intro _
      exact ⟨.nil u.2, List.nodup_singleton u.1, rfl⟩
    | @cons u w v hadj rest ih =>
      intro hp
      have hrest_path : rest.IsPath := hp.of_cons
      obtain ⟨W_rest, hW_rest_s, hsupp_rest⟩ := ih hrest_path
      obtain ⟨_, ⟨e, hl⟩⟩ := hK_adj.mp hadj
      refine ⟨.cons hl W_rest, ?_, ?_⟩
      · unfold GraphWalk.IsSimple
        rw [GraphWalk.support_cons, hsupp_rest, ← List.map_cons]
        exact hp.support_nodup.map Subtype.val_injective
      · rw [GraphWalk.support_cons, hsupp_rest, Walk.support_cons, List.map_cons]
  have hdrop_walk : ∀ {a b : α} (W : GraphWalk G a b) (ha : a ∈ V(G)) (hb : b ∈ V(G)),
      W.IsSimple →
      ∃ p : K.Walk ⟨a, ha⟩ ⟨b, hb⟩, ∀ z ∈ p.support, z.1 ∈ W.support := by
    intro a b W
    induction W with
    | @nil a haG =>
      intro ha _ _
      exact ⟨.nil, fun z hz ↦ by
        rw [Walk.support_nil, List.mem_singleton] at hz
        subst hz
        exact List.mem_singleton_self a⟩
    | @cons u w b e hl rest ih =>
      intro hu hb hWs
      have hu_not_rest : u ∉ rest.support := (List.nodup_cons.mp hWs).1
      have hrest_s : rest.IsSimple := (List.nodup_cons.mp hWs).2
      have hw : w ∈ V(G) := hl.right_mem
      have huw_ne : (⟨u, hu⟩ : ↥V(G)) ≠ ⟨w, hw⟩ := by
        intro heq
        have : u = w := Subtype.mk.inj heq
        exact hu_not_rest (this ▸ rest.start_mem_support)
      have hadj : K.Adj ⟨u, hu⟩ ⟨w, hw⟩ := hK_adj.mpr ⟨huw_ne, ⟨e, hl⟩⟩
      obtain ⟨p_rest, hp_rest⟩ := ih hw hb hrest_s
      refine ⟨.cons hadj p_rest, fun z hz ↦ ?_⟩
      rw [Walk.support_cons, List.mem_cons] at hz
      rcases hz with rfl | hz
      · exact List.mem_cons_self
      · exact List.mem_cons_of_mem _ (hp_rest z hz)
  let A₀ : Set ↥V(G) := Subtype.val ⁻¹' A
  let B₀ : Set ↥V(G) := Subtype.val ⁻¹' B
  have hfin₀ : Finite ↥V(G) := hVG.to_subtype
  have hdisj₀ : HasDisjointPaths K A₀ B₀ k := by
    refine Menger.exists_disjointPaths K A₀ B₀ hfin₀ k fun S₀ hS₀ ↦ ?_
    let Y : Set α := Subtype.val '' S₀
    have hY_sub : Y ⊆ V(G) := by rintro _ ⟨z, _, rfl⟩; exact z.2
    have hY_sep : Separates G Y A B := by
      intro P ⟨a, haA, b, hbB, hPG, W_P, hW_Ps, hVP, _⟩
      obtain ⟨W_G, hsupp_G, _⟩ := exists_walk_up_of_le hPG W_P
      have hW_Gs : W_G.IsSimple := by unfold GraphWalk.IsSimple; rw [hsupp_G]; exact hW_Ps
      obtain ⟨p, hp_sub⟩ := hdrop_walk W_G (hA haA) (hB hbB) hW_Gs
      let P₀ : PathFromTo K A₀ B₀ :=
        ⟨⟨a, hA haA⟩, ⟨b, hB hbB⟩, p.bypass, p.bypass_isPath, haA, hbB⟩
      obtain ⟨z, hz_bp, hzS₀⟩ := hS₀ P₀
      have hz_p : z ∈ p.support := p.support_bypass_subset_support hz_bp
      have hz_W : z.1 ∈ W_P.support := hsupp_G ▸ hp_sub z hz_p
      have hz_P : z.1 ∈ V(P) := by rw [hVP]; exact hz_W
      exact Set.not_disjoint_iff.mpr ⟨z.1, hz_P, ⟨z, hzS₀, rfl⟩⟩
    have hle := hsep Y hY_sub hY_sep
    rwa [Set.ncard_image_of_injective S₀ Subtype.val_injective] at hle
  obtain ⟨P₀, hP₀_disj⟩ := hdisj₀
  have hex_P : ∀ i : Fin k, ∃ P_i : Graph α β,
      IsPathBetween G P_i A B ∧ V(P_i) = {x | ∃ z ∈ (P₀ i).walk.support, z.1 = x} := by
    intro i
    obtain ⟨W_i, hW_is, hsupp_i⟩ := hlift_walk (P₀ i).walk (P₀ i).isPath
    refine ⟨walkSubgraph W_i,
      ⟨(P₀ i).first.1, (P₀ i).first_mem, (P₀ i).last.1, (P₀ i).last_mem,
        isGraphPathWithEnds_walkSubgraph hW_is⟩, ?_⟩
    rw [vertexSet_walkSubgraph, hsupp_i]
    ext x
    simp
  choose P hP_path hP_V using hex_P
  refine ⟨P, fun i₁ i₂ hne ↦ ?_, hP_path⟩
  change Disjoint V(P i₁) V(P i₂)
  rw [hP_V i₁, hP_V i₂]
  refine Set.disjoint_left.mpr ?_
  rintro x ⟨z₁, hz₁, rfl⟩ ⟨z₂, hz₂, heq⟩
  have hz₁₂ : z₁ = z₂ := Subtype.ext heq.symm
  exact Set.disjoint_left.mp (hP₀_disj hne) hz₁ (hz₁₂ ▸ hz₂)

/-! ## 4. Paths and Tree-Decompositions of the Cylinder: (3.6)–(3.7) -/

@[simp]
lemma vertexSet_cylinderGraph (r s : ℕ) : V(cylinderGraph r s) = Set.univ := rfl

lemma finite_vertexSet_cylinderGraph (r s : ℕ) : V(cylinderGraph r s).Finite :=
  Set.toFinite _

@[simp]
lemma vertexSet_cylinderCircle (r s : ℕ) (j : Fin s) :
    V(cylinderCircle r s j) = {p : Fin r × Fin s | p.2 = j} := rfl

lemma cylinderCircle_le (r s : ℕ) (j : Fin s) :
    cylinderCircle r s j ≤ cylinderGraph r s :=
  restrict_le.trans ((cylinderGraph r s).induce_le (subset_univ _))

@[simp]
lemma vertexSet_cylinderCentralCircle (r s : ℕ) (hs : 0 < s) :
    V(cylinderCentralCircle r s hs) =
      {p : Fin r × Fin s | p.2 = ⟨s - 1, Nat.sub_lt hs zero_lt_one⟩} := rfl

@[simp]
lemma vertexSet_cylinderRadialLine (r s : ℕ) (i : Fin r) :
    V(cylinderRadialLine r s i) = {p : Fin r × Fin s | p.1 = i} := rfl

lemma cylinderRadialLine_le (r s : ℕ) (i : Fin r) :
    cylinderRadialLine r s i ≤ cylinderGraph r s :=
  restrict_le.trans ((cylinderGraph r s).induce_le (subset_univ _))

/-- Radial walk in `cylinderRadialLine r s i` of length `d` from `(i, j₁)` to `(i, j₂)`. -/
lemma exists_radial_walk (r s : ℕ) (i : Fin r) :
    ∀ (d : ℕ) (j₁ j₂ : Fin s), j₁.1 + d = j₂.1 →
      ∃ W : GraphWalk (cylinderRadialLine r s i) (i, j₁) (i, j₂),
        W.IsSimple ∧
        ∀ p ∈ W.support, p.1 = i ∧ j₁.1 ≤ p.2.1 ∧ p.2.1 ≤ j₂.1 := by
  intro d
  induction d with
  | zero =>
    intro j₁ j₂ hj
    have heq : j₁ = j₂ := Fin.ext (by omega)
    subst heq
    refine ⟨.nil rfl, List.nodup_singleton _, fun p hp ↦ ?_⟩
    change p ∈ [(i, j₁)] at hp
    rw [List.mem_singleton] at hp
    subst hp
    exact ⟨rfl, le_rfl, le_rfl⟩
  | succ d ih =>
    intro j₁ j₂ hj
    have hj1 : j₁.1 + 1 < s := by have := j₂.2; omega
    let j_next : Fin s := ⟨j₁.1 + 1, hj1⟩
    obtain ⟨W_rest, hW_rest_s, hsupp_rest⟩ := ih j_next j₂ (by dsimp [j_next]; omega)
    have hl : (cylinderRadialLine r s i).IsLink (Sum.inr (i, j₁)) (i, j₁) (i, j_next) :=
      ⟨⟨j₁, rfl⟩, ⟨hj1, Or.inl ⟨rfl, rfl⟩⟩, rfl, rfl⟩
    have hnot_mem : (i, j₁) ∉ W_rest.support := by
      intro hmem
      have h := (hsupp_rest _ hmem).2.1
      dsimp [j_next] at h
      omega
    refine ⟨.cons hl W_rest, List.nodup_cons.mpr ⟨hnot_mem, hW_rest_s⟩, fun p hp ↦ ?_⟩
    rcases List.mem_cons.mp hp with rfl | hp'
    · exact ⟨rfl, le_rfl, by dsimp; omega⟩
    · obtain ⟨hp1, hp2, hp3⟩ := hsupp_rest p hp'
      dsimp [j_next] at hp2
      exact ⟨hp1, by omega, hp3⟩

/-- Radial walk in `cylinderRadialLine r s i` from `(i, j₁)` to `(i, j₂)` for `j₁.1 ≤ j₂.1`. -/
lemma exists_radial_walk_between (r s : ℕ) (i : Fin r) (j₁ j₂ : Fin s) (hle : j₁.1 ≤ j₂.1) :
    ∃ W : GraphWalk (cylinderRadialLine r s i) (i, j₁) (i, j₂),
      W.IsSimple ∧
      ∀ p ∈ W.support, p.1 = i ∧ j₁.1 ≤ p.2.1 ∧ p.2.1 ≤ j₂.1 :=
  exists_radial_walk r s i (j₂.1 - j₁.1) j₁ j₂ (by omega)

/-- Every radial line `cylinderRadialLine r s i` (`0 < s`) is a connected graph. -/
lemma isGraphConnected_cylinderRadialLine (r s : ℕ) (hs : 0 < s) (i : Fin r) :
    IsGraphConnected (cylinderRadialLine r s i) := by
  refine ⟨⟨(i, ⟨0, hs⟩), rfl⟩, fun u hu v hv ↦ ?_⟩
  have hu_eq : u = (i, u.2) := Prod.ext hu rfl
  have hv_eq : v = (i, v.2) := Prod.ext hv rfl
  obtain ⟨Wu, _, _⟩ := exists_radial_walk_between r s i ⟨0, hs⟩ u.2 (Nat.zero_le _)
  obtain ⟨Wv, _, _⟩ := exists_radial_walk_between r s i ⟨0, hs⟩ v.2 (Nat.zero_le _)
  rw [hu_eq, hv_eq]
  exact ⟨Wu.reverse.append Wv⟩

/-- Spoke at offset `k` from `i₀` around `Fin r`: `(i₀ + k) mod r`. -/
def spokeAt {r : ℕ} (i₀ : Fin r) (k : ℕ) : Fin r :=
  ⟨(i₀.1 + k) % r, Nat.mod_lt _ i₀.pos⟩

@[simp]
lemma spokeAt_zero {r : ℕ} (i₀ : Fin r) : spokeAt i₀ 0 = i₀ :=
  Fin.ext (by simp [spokeAt, Nat.mod_eq_of_lt i₀.2])

lemma spokeAt_succ {r : ℕ} (i₀ : Fin r) (k : ℕ) :
    spokeAt (nextSpoke i₀) k = spokeAt i₀ (k + 1) := by
  ext
  simp [spokeAt, nextSpoke, Nat.add_assoc, Nat.add_comm 1 k]

lemma spokeAt_add {r : ℕ} (i₀ : Fin r) (a b : ℕ) :
    spokeAt (spokeAt i₀ a) b = spokeAt i₀ (a + b) := by
  ext
  simp [spokeAt, Nat.add_assoc]

@[simp]
lemma spokeAt_self {r : ℕ} (i₀ : Fin r) : spokeAt i₀ r = i₀ :=
  Fin.ext (by simp [spokeAt, Nat.mod_eq_of_lt i₀.2])

private lemma mod_eq_of_lt_two_mul {x r : ℕ} (hx : x < r + r) :
    x % r = if x < r then x else x - r := by
  split_ifs with h
  · exact Nat.mod_eq_of_lt h
  · rw [Nat.mod_eq_sub_mod (not_lt.mp h), Nat.mod_eq_of_lt (by omega)]

lemma spokeAt_inj_of_lt {r : ℕ} (i₀ : Fin r) {a b : ℕ} (ha : a < r) (hb : b < r)
    (heq : spokeAt i₀ a = spokeAt i₀ b) : a = b := by
  have hval : (i₀.1 + a) % r = (i₀.1 + b) % r := congrArg Fin.val heq
  have hi₀ : i₀.1 < r := i₀.2
  rw [mod_eq_of_lt_two_mul (by omega), mod_eq_of_lt_two_mul (by omega)] at hval
  split_ifs at hval <;> omega

/-- Clockwise simple walk of length `k < r` on `cylinderCircle r s j` starting at `(i₀, j)`. -/
lemma exists_circle_walk_from (r s : ℕ) (j : Fin s) :
    ∀ (k : ℕ) (i₀ i₁ : Fin r), k < r → spokeAt i₀ k = i₁ →
      ∃ W : GraphWalk (cylinderCircle r s j) (i₀, j) (i₁, j),
        W.IsSimple ∧
        ∀ p : Fin r × Fin s, p ∈ W.support ↔
          p.2 = j ∧ ∃ t : ℕ, t ≤ k ∧ p.1 = spokeAt i₀ t := by
  intro k
  induction k with
  | zero =>
    intro i₀ i₁ _ hi₁
    rw [spokeAt_zero] at hi₁
    subst hi₁
    refine ⟨.nil rfl, List.nodup_singleton _, fun p ↦ ?_⟩
    change p ∈ [(i₀, j)] ↔ _
    rw [List.mem_singleton]
    constructor
    · rintro rfl
      exact ⟨rfl, 0, le_rfl, (spokeAt_zero i₀).symm⟩
    · rintro ⟨hp2, t, ht0, hp1⟩
      have ht : t = 0 := by omega
      subst ht
      rw [spokeAt_zero] at hp1
      exact Prod.ext hp1 hp2
  | succ k ih =>
    intro i₀ i₁ hk hi₁
    obtain ⟨W_rest, hW_rest_s, hsupp_rest⟩ :=
      ih (nextSpoke i₀) i₁ (by omega) ((spokeAt_succ i₀ k).trans hi₁)
    have hl : (cylinderCircle r s j).IsLink (Sum.inl (i₀, j)) (i₀, j) (nextSpoke i₀, j) :=
      ⟨⟨i₀, rfl⟩, Or.inl ⟨rfl, rfl⟩, rfl, rfl⟩
    have hnot_mem : (i₀, j) ∉ W_rest.support := by
      rw [hsupp_rest]
      rintro ⟨_, t, htk, ht_eq⟩
      rw [spokeAt_succ] at ht_eq
      have h0 : spokeAt i₀ 0 = spokeAt i₀ (t + 1) := by
        rw [spokeAt_zero]
        exact ht_eq
      have := spokeAt_inj_of_lt i₀ (by omega) (by omega) h0
      omega
    refine ⟨.cons hl W_rest, List.nodup_cons.mpr ⟨hnot_mem, hW_rest_s⟩, fun p ↦ ?_⟩
    rw [GraphWalk.support_cons, List.mem_cons, hsupp_rest]
    constructor
    · rintro (rfl | ⟨hp2, t, htk, hp1⟩)
      · exact ⟨rfl, 0, by omega, (spokeAt_zero i₀).symm⟩
      · rw [spokeAt_succ] at hp1
        exact ⟨hp2, t + 1, by omega, hp1⟩
    · rintro ⟨hp2, t, htk1, hp1⟩
      rcases t with _ | t
      · rw [spokeAt_zero] at hp1
        exact Or.inl (Prod.ext hp1 hp2)
      · right
        rw [← spokeAt_succ] at hp1
        exact ⟨hp2, t, by omega, hp1⟩

/-- Between any two distinct vertices `(i₀, j)` and `(i₁, j)` on `cylinderCircle r s j`, there are
two simple walks in `cylinderCircle r s j` whose supports intersect only in `{(i₀, j), (i₁, j)}`. -/
lemma exists_two_circle_walks (r s : ℕ) (j : Fin s) {i₀ i₁ : Fin r} (hne : i₀ ≠ i₁) :
    ∃ W₁ W₂ : GraphWalk (cylinderCircle r s j) (i₀, j) (i₁, j),
      W₁.IsSimple ∧ W₂.IsSimple ∧
      ∀ p : Fin r × Fin s, p ∈ W₁.support → p ∈ W₂.support →
        p = (i₀, j) ∨ p = (i₁, j) := by
  let k : ℕ := (i₁.1 + r - i₀.1) % r
  have hi₀ : i₀.1 < r := i₀.2
  have hi₁ : i₁.1 < r := i₁.2
  have hne_val : i₀.1 ≠ i₁.1 := fun h ↦ hne (Fin.ext h)
  have hk_eq : k = if i₁.1 + r - i₀.1 < r then i₁.1 + r - i₀.1 else i₁.1 + r - i₀.1 - r :=
    mod_eq_of_lt_two_mul (by omega)
  have hk_pos : 0 < k := by rw [hk_eq]; split_ifs <;> omega
  have hk_lt : k < r := Nat.mod_lt _ i₀.pos
  have hspoke_k : spokeAt i₀ k = i₁ := by
    ext
    change (i₀.1 + k) % r = i₁.1
    rw [mod_eq_of_lt_two_mul (by omega), hk_eq]
    split_ifs <;> omega
  have hrk_lt : r - k < r := by omega
  have hspoke_rk : spokeAt i₁ (r - k) = i₀ := by
    rw [← hspoke_k, spokeAt_add, show k + (r - k) = r by omega, spokeAt_self]
  obtain ⟨W₁, hW₁s, hsupp₁⟩ := exists_circle_walk_from r s j k i₀ i₁ hk_lt hspoke_k
  obtain ⟨W₂', hW₂'s, hsupp₂'⟩ := exists_circle_walk_from r s j (r - k) i₁ i₀ hrk_lt hspoke_rk
  refine ⟨W₁, W₂'.reverse, hW₁s, hW₂'s.reverse, fun p hp₁ hp₂ ↦ ?_⟩
  rw [GraphWalk.support_reverse, List.mem_reverse] at hp₂
  obtain ⟨hpj, t₁, ht₁, hp₁_eq⟩ := (hsupp₁ p).mp hp₁
  obtain ⟨_, t₂, ht₂, hp₂_eq⟩ := (hsupp₂' p).mp hp₂
  rw [← hspoke_k, spokeAt_add] at hp₂_eq
  by_cases ht₂_end : t₂ = r - k
  · left
    have hp1 : p.1 = i₀ := by
      rw [hp₂_eq, ht₂_end, show k + (r - k) = r by omega, spokeAt_self]
    exact Prod.ext hp1 hpj
  · right
    have heq_t : t₁ = k + t₂ :=
      spokeAt_inj_of_lt i₀ (by omega) (by omega) (hp₁_eq.symm.trans hp₂_eq)
    have ht₁_k : t₁ = k := by omega
    have hp1 : p.1 = i₁ := by rw [hp₁_eq, ht₁_k, hspoke_k]
    exact Prod.ext hp1 hpj

/-- Graph Minors III, (3.6) (page 57):
"(3.6) *Suppose $X \subseteq V(S)$ and $|X \cap V(C_j)| \ge 2$ $(1 \le j \le s)$. Then there are $r$
vertex-disjoint paths of $S$, each between $X$ and $V(C_s)$.*" -/
theorem theorem_3_6_proof (r s : ℕ) (hs : 0 < s) (hr : r ≤ 2 * s)
    (X : Set (Fin r × Fin s))
    (hX : ∀ j : Fin s, 2 ≤ (X ∩ V(cylinderCircle r s j)).ncard) :
    ∃ P : Fin r → Graph (Fin r × Fin s) ((Fin r × Fin s) ⊕ (Fin r × Fin s)),
      Pairwise (fun i₁ i₂ : Fin r => Disjoint V(P i₁) V(P i₂)) ∧
      ∀ i : Fin r, IsPathBetween (cylinderGraph r s) (P i) X (V(cylinderCentralCircle r s hs)) := by
  refine exists_disjoint_isPathBetween_of_separates (finite_vertexSet_cylinderGraph r s)
    (subset_univ X) (subset_univ _) r fun Y _ hsep ↦ ?_
  by_contra hY_lt
  push Not at hY_lt
  have hex_j : ∃ j : Fin s, (Y ∩ V(cylinderCircle r s j)).ncard ≤ 1 := by
    by_contra hall
    push Not at hall
    have hex_pair : ∀ j : Fin s, ∃ y₁ y₂ : Fin r × Fin s,
        y₁ ∈ Y ∩ V(cylinderCircle r s j) ∧ y₂ ∈ Y ∩ V(cylinderCircle r s j) ∧ y₁ ≠ y₂ :=
      fun j ↦ (Set.one_lt_ncard_iff (Set.toFinite _)).mp (hall j)
    choose y₁ y₂ hy₁ hy₂ hne_y using hex_pair
    let g : Fin s × Bool → ↥Y := fun jb ↦
      if jb.2 then ⟨y₁ jb.1, (hy₁ jb.1).1⟩ else ⟨y₂ jb.1, (hy₂ jb.1).1⟩
    have hg_inj : Function.Injective g := by
      rintro ⟨j₁, b₁⟩ ⟨j₂, b₂⟩ heq
      have hval : (g (j₁, b₁)).1 = (g (j₂, b₂)).1 := congrArg Subtype.val heq
      have hj₁ : (g (j₁, b₁)).1.2 = j₁ := by
        cases b₁ <;> [exact (hy₂ j₁).2; exact (hy₁ j₁).2]
      have hj₂ : (g (j₂, b₂)).1.2 = j₂ := by
        cases b₂ <;> [exact (hy₂ j₂).2; exact (hy₁ j₂).2]
      have hj_eq : j₁ = j₂ := hj₁.symm.trans ((congrArg Prod.snd hval).trans hj₂)
      subst hj_eq
      cases b₁ <;> cases b₂
      · rfl
      · exact (hne_y j₁ hval.symm).elim
      · exact (hne_y j₁ hval).elim
      · rfl
    have : Finite ↥Y := (Set.toFinite Y).to_subtype
    have hcard_le := Nat.card_le_card_of_injective g hg_inj
    have hdom : Nat.card (Fin s × Bool) = 2 * s := by
      rw [Nat.card_prod, Nat.card_fin, Nat.card_eq_fintype_card, Fintype.card_bool]
      omega
    rw [hdom, Nat.card_coe_set_eq] at hcard_le
    omega
  obtain ⟨j, hjY⟩ := hex_j
  have hX_not_sub : ¬ (X ∩ V(cylinderCircle r s j) ⊆ Y ∩ V(cylinderCircle r s j)) := by
    intro hsub
    have hle := Set.ncard_le_ncard hsub (Set.toFinite _)
    have := hX j
    omega
  rw [Set.not_subset] at hX_not_sub
  obtain ⟨x₀, ⟨hx₀X, hx₀C⟩, hx₀_not⟩ := hX_not_sub
  have hx₀Y : x₀ ∉ Y := fun h ↦ hx₀_not ⟨h, hx₀C⟩
  have hex_i₁ : ∃ i₁ : Fin r, Disjoint V(cylinderRadialLine r s i₁) Y := by
    by_contra hall
    push Not at hall
    have hex_z : ∀ i : Fin r, ∃ z : Fin r × Fin s, z ∈ V(cylinderRadialLine r s i) ∧ z ∈ Y :=
      fun i ↦ Set.not_disjoint_iff.mp (hall i)
    choose z hzL hzY using hex_z
    let f : Fin r → ↥Y := fun i ↦ ⟨z i, hzY i⟩
    have hf_inj : Function.Injective f := by
      intro i₁ i₂ heq
      have hval : z i₁ = z i₂ := congrArg Subtype.val heq
      have h1 : (z i₁).1 = i₁ := hzL i₁
      have h2 : (z i₂).1 = i₂ := hzL i₂
      exact h1.symm.trans ((congrArg Prod.fst hval).trans h2)
    have : Finite ↥Y := (Set.toFinite Y).to_subtype
    have hcard_le := Nat.card_le_card_of_injective f hf_inj
    rw [Nat.card_fin, Nat.card_coe_set_eq] at hcard_le
    omega
  obtain ⟨i₁, hi₁Y⟩ := hex_i₁
  let i₀ : Fin r := x₀.1
  have hx₀_eq : x₀ = (i₀, j) := Prod.ext rfl hx₀C
  have hi₁j_Y : (i₁, j) ∉ Y := Set.disjoint_left.mp hi₁Y rfl
  have hex_circ_walk : ∃ Wc : GraphWalk (cylinderCircle r s j) x₀ (i₁, j),
      ∀ p ∈ Wc.support, p ∉ Y := by
    rw [hx₀_eq]
    by_cases hne : i₀ = i₁
    · subst hne
      refine ⟨.nil rfl, fun p hp ↦ ?_⟩
      change p ∈ [(i₀, j)] at hp
      rw [List.mem_singleton] at hp
      subst hp
      exact hi₁j_Y
    · obtain ⟨W₁, W₂, _, _, hinter⟩ := exists_two_circle_walks r s j hne
      by_cases h1 : ∀ p ∈ W₁.support, p ∉ Y
      · exact ⟨W₁, h1⟩
      · push Not at h1
        obtain ⟨y₁, hy₁_supp, hy₁Y⟩ := h1
        refine ⟨W₂, fun y₂ hy₂_supp hy₂Y ↦ ?_⟩
        have hy₁C : y₁ ∈ Y ∩ V(cylinderCircle r s j) :=
          ⟨hy₁Y, W₁.mem_vertexSet_of_mem_support hy₁_supp⟩
        have hy₂C : y₂ ∈ Y ∩ V(cylinderCircle r s j) :=
          ⟨hy₂Y, W₂.mem_vertexSet_of_mem_support hy₂_supp⟩
        have hy_eq : y₁ = y₂ :=
          (Set.ncard_le_one_iff (Set.toFinite _)).mp hjY hy₁C hy₂C
        subst hy_eq
        rcases hinter y₁ hy₁_supp hy₂_supp with rfl | rfl
        · exact hx₀Y (hx₀_eq.symm ▸ hy₁Y)
        · exact hi₁j_Y hy₁Y
  obtain ⟨Wc, hWc_av⟩ := hex_circ_walk
  obtain ⟨Wc_G, hsupp_c, _⟩ := exists_walk_up_of_le (cylinderCircle_le r s j) Wc
  let j_last : Fin s := ⟨s - 1, Nat.sub_lt hs zero_lt_one⟩
  obtain ⟨Wr, _, hsupp_r⟩ := exists_radial_walk_between r s i₁ j j_last
    (by have := j.2; dsimp [j_last]; omega)
  obtain ⟨Wr_G, hsupp_rG, _⟩ := exists_walk_up_of_le (cylinderRadialLine_le r s i₁) Wr
  let W_tot := Wc_G.append Wr_G
  obtain ⟨P, hP_ends, hVP, _⟩ := exists_isGraphPathWithEnds_of_walk W_tot
  have hP_between : IsPathBetween (cylinderGraph r s) P X (V(cylinderCentralCircle r s hs)) :=
    ⟨x₀, hx₀X, (i₁, j_last), rfl, hP_ends⟩
  refine hsep P hP_between (Set.disjoint_left.mpr fun p hpP hpY ↦ ?_)
  have hp_tot : p ∈ W_tot.support := hVP hpP
  rcases (GraphWalk.mem_support_append Wc_G Wr_G).mp hp_tot with hpc | hpr
  · rw [hsupp_c] at hpc
    exact hWc_av p hpc hpY
  · rw [hsupp_rG] at hpr
    have hpL : p ∈ V(cylinderRadialLine r s i₁) := (hsupp_r p hpr).1
    exact Set.disjoint_left.mp hi₁Y hpL hpY

/-- Graph Minors III, (3.7) (page 58):
"(3.7) *Let $(T, \mathcal{X})$ be a tree-decomposition of $S$, where
$\mathcal{X} = (X_t : t \in V(T))$. Then there exist $t_0 \in V(T)$ and $r$ vertex-disjoint paths
of $S$, each between $X_{t_0}$ and $C_s$.*" -/
theorem theorem_3_7_proof {ι : Type w} [Fintype ι]
    (r s : ℕ) (hs : 0 < s) (hr : r ≤ 2 * s)
    {T : SimpleGraph ι} {X : ι → Set (Fin r × Fin s)}
    (hTD : IsTreeDecomposition (cylinderGraph r s) T X) :
    ∃ (t₀ : ι) (P : Fin r → Graph (Fin r × Fin s) ((Fin r × Fin s) ⊕ (Fin r × Fin s))),
      Pairwise (fun i₁ i₂ : Fin r => Disjoint V(P i₁) V(P i₂)) ∧
      ∀ i : Fin r, IsPathBetween (cylinderGraph r s) (P i) (X t₀)
        (V(cylinderCentralCircle r s hs)) := by
  by_cases hall_hit : ∃ t₀ : ι, ∀ i : Fin r, (X t₀ ∩ V(cylinderRadialLine r s i)).Nonempty
  · obtain ⟨t₀, ht₀⟩ := hall_hit
    let j_last : Fin s := ⟨s - 1, Nat.sub_lt hs zero_lt_one⟩
    have hex_P : ∀ i : Fin r, ∃ P_i : Graph (Fin r × Fin s) ((Fin r × Fin s) ⊕ (Fin r × Fin s)),
        IsPathBetween (cylinderGraph r s) P_i (X t₀) (V(cylinderCentralCircle r s hs)) ∧
        V(P_i) ⊆ V(cylinderRadialLine r s i) := by
      intro i
      obtain ⟨p, hpX, hpL⟩ := ht₀ i
      have hp_eq : p = (i, p.2) := Prod.ext hpL rfl
      obtain ⟨Wr, hWr_s, hsupp_r⟩ := exists_radial_walk_between r s i p.2 j_last
        (by have := p.2.2; dsimp [j_last]; omega)
      obtain ⟨Wr_G, hsupp_rG, _⟩ := exists_walk_up_of_le (cylinderRadialLine_le r s i) Wr
      have hWr_Gs : Wr_G.IsSimple := by unfold GraphWalk.IsSimple; rw [hsupp_rG]; exact hWr_s
      refine ⟨walkSubgraph Wr_G,
        ⟨(i, p.2), hp_eq ▸ hpX, (i, j_last), rfl, isGraphPathWithEnds_walkSubgraph hWr_Gs⟩,
        fun q hq ↦ ?_⟩
      rw [vertexSet_walkSubgraph, hsupp_rG] at hq
      exact (hsupp_r q hq).1
    choose P hP_path hP_sub using hex_P
    refine ⟨t₀, P, fun i₁ i₂ hne ↦ ?_, hP_path⟩
    refine Set.disjoint_left.mpr fun q hq₁ hq₂ ↦ hne ?_
    have h1 : q.1 = i₁ := hP_sub i₁ hq₁
    have h2 : q.1 = i₂ := hP_sub i₂ hq₂
    exact h1.symm.trans h2
  · push Not at hall_hit
    have hex_miss : ∀ t : ι, ∃ i : Fin r, Disjoint V(cylinderRadialLine r s i) (X t) := by
      intro t
      obtain ⟨i, hi⟩ := hall_hit t
      rw [Set.inter_comm, ← Set.disjoint_iff_inter_eq_empty] at hi
      exact ⟨i, hi⟩
    choose i_miss hi_miss using hex_miss
    have hT_card : 2 ≤ Fintype.card ι := by
      by_contra hlt2
      have hne_ι : Nonempty ι := hTD.isTree.connected.nonempty
      obtain ⟨t₀⟩ := hne_ι
      have huniq : ∀ t : ι, t = t₀ := by
        intro t
        by_contra hne
        have : 2 ≤ Fintype.card ι := Fintype.one_lt_card_iff.mpr ⟨t, t₀, hne⟩
        omega
      have hXt₀ : X t₀ = Set.univ := by
        have hU : (⋃ t : ι, X t) = Set.univ := hTD.iUnion_bags
        rw [← hU]
        ext p
        rw [mem_iUnion]
        exact ⟨fun hp ↦ ⟨t₀, hp⟩, fun ⟨t, hp⟩ ↦ huniq t ▸ hp⟩
      have hp_mem : (i_miss t₀, ⟨0, hs⟩) ∈ V(cylinderRadialLine r s (i_miss t₀)) := rfl
      have hp_X : (i_miss t₀, ⟨0, hs⟩) ∈ X t₀ := by rw [hXt₀]; trivial
      exact Set.disjoint_left.mp (hi_miss t₀) hp_mem hp_X
    obtain ⟨t, t', _, hsep⟩ :=
      theorem_3_5_proof hTD hT_card (fun s₀ ↦ cylinderRadialLine r s (i_miss s₀))
        (fun s₀ ↦ cylinderRadialLine_le r s (i_miss s₀))
        (fun s₀ ↦ isGraphConnected_cylinderRadialLine r s hs (i_miss s₀))
        hi_miss
    have hne_i : i_miss t ≠ i_miss t' := by
      intro heq
      let p₀ : Fin r × Fin s := (i_miss t, ⟨0, hs⟩)
      have hp₀_t : p₀ ∈ V(cylinderRadialLine r s (i_miss t)) := rfl
      have hp₀_t' : p₀ ∈ V(cylinderRadialLine r s (i_miss t')) := heq ▸ hp₀_t
      let W₀ : GraphWalk (cylinderGraph r s) p₀ p₀ := .nil (mem_univ _)
      have hP₀ : IsPathBetween (cylinderGraph r s) (walkSubgraph W₀)
          V(cylinderRadialLine r s (i_miss t)) V(cylinderRadialLine r s (i_miss t')) :=
        ⟨p₀, hp₀_t, p₀, hp₀_t', isGraphPathWithEnds_walkSubgraph (List.nodup_singleton p₀)⟩
      refine hsep (walkSubgraph W₀) hP₀ (Set.disjoint_left.mpr fun q hq hq_inter ↦ ?_)
      rw [vertexSet_walkSubgraph, mem_ofPred_eq] at hq
      change q ∈ [p₀] at hq
      rw [List.mem_singleton] at hq
      subst hq
      exact Set.disjoint_left.mp (hi_miss t) hp₀_t hq_inter.1
    have hcard_Xt : ∀ j : Fin s, 2 ≤ (X t ∩ V(cylinderCircle r s j)).ncard := by
      intro j
      obtain ⟨W₁, W₂, hW₁s, hW₂s, hinter⟩ := exists_two_circle_walks r s j hne_i
      obtain ⟨W₁_G, hsupp₁, _⟩ := exists_walk_up_of_le (cylinderCircle_le r s j) W₁
      obtain ⟨W₂_G, hsupp₂, _⟩ := exists_walk_up_of_le (cylinderCircle_le r s j) W₂
      have hW₁_Gs : W₁_G.IsSimple := by unfold GraphWalk.IsSimple; rw [hsupp₁]; exact hW₁s
      have hW₂_Gs : W₂_G.IsSimple := by unfold GraphWalk.IsSimple; rw [hsupp₂]; exact hW₂s
      have hP₁ : IsPathBetween (cylinderGraph r s) (walkSubgraph W₁_G)
          V(cylinderRadialLine r s (i_miss t)) V(cylinderRadialLine r s (i_miss t')) :=
        ⟨(i_miss t, j), rfl, (i_miss t', j), rfl, isGraphPathWithEnds_walkSubgraph hW₁_Gs⟩
      have hP₂ : IsPathBetween (cylinderGraph r s) (walkSubgraph W₂_G)
          V(cylinderRadialLine r s (i_miss t)) V(cylinderRadialLine r s (i_miss t')) :=
        ⟨(i_miss t, j), rfl, (i_miss t', j), rfl, isGraphPathWithEnds_walkSubgraph hW₂_Gs⟩
      obtain ⟨z₁, hz₁_W, hz₁_X⟩ := Set.not_disjoint_iff.mp (hsep (walkSubgraph W₁_G) hP₁)
      obtain ⟨z₂, hz₂_W, hz₂_X⟩ := Set.not_disjoint_iff.mp (hsep (walkSubgraph W₂_G) hP₂)
      rw [vertexSet_walkSubgraph, mem_ofPred_eq, hsupp₁] at hz₁_W
      rw [vertexSet_walkSubgraph, mem_ofPred_eq, hsupp₂] at hz₂_W
      have hz₁_C : z₁ ∈ X t ∩ V(cylinderCircle r s j) :=
        ⟨hz₁_X.1, W₁.mem_vertexSet_of_mem_support hz₁_W⟩
      have hz₂_C : z₂ ∈ X t ∩ V(cylinderCircle r s j) :=
        ⟨hz₂_X.1, W₂.mem_vertexSet_of_mem_support hz₂_W⟩
      have hz_ne : z₁ ≠ z₂ := by
        intro heq
        subst heq
        rcases hinter z₁ hz₁_W hz₂_W with rfl | rfl
        · exact Set.disjoint_left.mp (hi_miss t) rfl hz₁_X.1
        · exact Set.disjoint_left.mp (hi_miss t') rfl hz₁_X.2
      exact (Set.one_lt_ncard_iff (Set.toFinite _)).mpr ⟨z₁, z₂, hz₁_C, hz₂_C, hz_ne⟩
    obtain ⟨P, hP_disj, hP_path⟩ := theorem_3_6_proof r s hs hr (X t) hcard_Xt
    exact ⟨t, P, hP_disj, hP_path⟩

end GraphMinor.GM03
