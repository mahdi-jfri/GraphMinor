module

public import GraphMinor.GM22.Section2
public import GraphMinor.GM10.TreeWidthBasic
public import GraphMinor.GM10.Section9

/-!
# Graph Minors XXII, Section 3 (Part 1): Havens, Tree-Width, and Proof of 3.2

This file proves the relationship between havens and tree-decompositions (Seymour and Thomas [8],
Theorem 1.4, lower bound direction) and proves **3.2** (`theorem_3_2`) of
N. Robertson and P. D. Seymour, *Graph Minors. XXII. Irrelevant vertices in linkage problems*,
J. Combin. Theory Ser. B **102** (2012) 530–563 (pages 534–535).
-/

@[expose] public section

namespace GraphMinor.GM22

open Set Function Graph SimpleGraph GraphMinor.Surface GraphMinor.GM06 GraphMinor.GM09
  GraphMinor.GM10

universe u v w

variable {α : Type u} {β : Type v} {ι : Type w} [Fintype ι]

/-! ## 1. Basic Properties of `IsGraphTreeDecomposition` -/

theorem IsGraphTreeDecomposition.nonempty {G : Graph α β} {T : SimpleGraph ι}
    {W : ι → Graph α β} (hTD : IsGraphTreeDecomposition G T W) : Nonempty ι :=
  hTD.isTree.connected.nonempty

theorem IsGraphTreeDecomposition.vertex_mem_iff {G : Graph α β} {T : SimpleGraph ι}
    {W : ι → Graph α β} (hTD : IsGraphTreeDecomposition G T W) {v : α} :
    v ∈ V(G) ↔ ∃ t : ι, v ∈ V(W t) := by
  have h := congr_arg Graph.vertexSet hTD.sUnion_eq
  rw [← h, vertexSet_subgraphSUnion]
  simp

theorem IsGraphTreeDecomposition.edge_mem_iff {G : Graph α β} {T : SimpleGraph ι}
    {W : ι → Graph α β} (hTD : IsGraphTreeDecomposition G T W) {e : β} :
    e ∈ E(G) ↔ ∃ t : ι, e ∈ E(W t) := by
  have hle : ∀ H ∈ range W, H ≤ G := by rintro _ ⟨t, rfl⟩; exact hTD.le t
  have h := congr_arg Graph.edgeSet hTD.sUnion_eq
  rw [← h, edgeSet_subgraphSUnion hle]
  simp

theorem IsGraphTreeDecomposition.ends_mem_of_isLink {G : Graph α β} {T : SimpleGraph ι}
    {W : ι → Graph α β} (hTD : IsGraphTreeDecomposition G T W) {e : β} {x y : α}
    (hl : G.IsLink e x y) : ∃ t : ι, x ∈ V(W t) ∧ y ∈ V(W t) := by
  obtain ⟨t, het⟩ := hTD.edge_mem_iff.mp hl.edge_mem
  have hlt : (W t).IsLink e x y := ((hTD.le t).isLink_iff het).mpr hl
  exact ⟨t, hlt.left_mem, hlt.right_mem⟩

theorem IsGraphTreeDecomposition.vertex_mem_of_onTreePath {G : Graph α β} {T : SimpleGraph ι}
    {W : ι → Graph α β} (hTD : IsGraphTreeDecomposition G T W)
    {t₁ t₂ t : ι} (hon : OnTreePath T t₁ t₂ t) {x : α}
    (hx₁ : x ∈ V(W t₁)) (hx₂ : x ∈ V(W t₂)) : x ∈ V(W t) := by
  have hx_inter : x ∈ V(subgraphInter G (W t₁) (W t₂)) := by
    rw [vertexSet_subgraphInter]
    exact ⟨hx₁, hx₂⟩
  exact (hTD.inter_le hon).vertexSet_mono hx_inter

/-! ## 2. Tree-Decomposition Separation Sides Along a Tree Edge -/

/-- The set of vertices of `G` appearing in bags `W t` on the `u`-side of edge `s(u, v)` in `T`. -/
def treeBagSideVerts (T : SimpleGraph ι) (W : ι → Graph α β) (u v : ι) : Set α :=
  ⋃ t ∈ treeComponent T u s(u, v), V(W t)

theorem mem_W_of_mem_treeBagSideVerts_inter {G : Graph α β} {T : SimpleGraph ι}
    {W : ι → Graph α β} (hTD : IsGraphTreeDecomposition G T W)
    {u v : ι} (hadj : T.Adj u v) {x : α}
    (hxu : x ∈ treeBagSideVerts T W u v) (hxv : x ∈ treeBagSideVerts T W v u) :
    x ∈ V(W u) ∩ V(W v) := by
  unfold treeBagSideVerts at hxu hxv
  rw [mem_iUnion₂] at hxu hxv
  rcases hxu with ⟨t₁, ht₁, hx₁⟩
  rcases hxv with ⟨t₂, ht₂, hx₂⟩
  have hon_u : OnTreePath T t₁ t₂ u :=
    onTreePath_of_mem_treeComponent hTD.isTree hadj ht₁ ht₂
  have hon_v : OnTreePath T t₂ t₁ v :=
    onTreePath_of_mem_treeComponent hTD.isTree hadj.symm ht₂ ht₁
  exact ⟨hTD.vertex_mem_of_onTreePath hon_u hx₁ hx₂,
    hTD.vertex_mem_of_onTreePath hon_v hx₂ hx₁⟩

theorem mem_treeBagSideVerts_or {G : Graph α β} {T : SimpleGraph ι}
    {W : ι → Graph α β} (hTD : IsGraphTreeDecomposition G T W)
    {u v : ι} (hadj : T.Adj u v) {x : α} (hx : x ∈ V(G)) :
    x ∈ treeBagSideVerts T W u v ∨ x ∈ treeBagSideVerts T W v u := by
  obtain ⟨t, hxt⟩ := hTD.vertex_mem_iff.mp hx
  by_cases ht : t ∈ treeComponent T u s(u, v)
  · exact Or.inl (mem_biUnion ht hxt)
  · have ht' : t ∈ treeComponent T v s(v, u) :=
      (notMem_treeComponent_iff hTD.isTree hadj).mp ht
    exact Or.inr (mem_biUnion ht' hxt)

theorem walk_subset_treeBagSideVerts_of_disjoint {G : Graph α β} {T : SimpleGraph ι}
    {W : ι → Graph α β} (hTD : IsGraphTreeDecomposition G T W)
    {u v : ι} (hadj : T.Adj u v) {a b : α}
    (W_walk : GraphWalk (G.deleteVerts (V(W u) ∩ V(W v))) a b)
    (ha : a ∈ treeBagSideVerts T W u v) :
    b ∈ treeBagSideVerts T W u v := by
  induction W_walk with
  | nil _ => exact ha
  | @cons x y z e hl rest ih =>
    have hlG : G.IsLink e x y := hl.mono deleteVerts_le
    have hx_not : x ∉ V(W u) ∩ V(W v) := (vertexSet_deleteVerts G _ ▸ hl.left_mem).2
    obtain ⟨t, hxt, hyt⟩ := hTD.ends_mem_of_isLink hlG
    have ht_u : t ∈ treeComponent T u s(u, v) := by
      by_contra ht_not
      have ht_v : t ∈ treeComponent T v s(v, u) :=
        (notMem_treeComponent_iff hTD.isTree hadj).mp ht_not
      have hx_v : x ∈ treeBagSideVerts T W v u := mem_biUnion ht_v hxt
      exact hx_not (mem_W_of_mem_treeBagSideVerts_inter hTD hadj ha hx_v)
    exact ih (mem_biUnion ht_u hyt)

theorem connected_subset_treeBagSideVerts_or {G H : Graph α β} {T : SimpleGraph ι}
    {W : ι → Graph α β} (hTD : IsGraphTreeDecomposition G T W)
    {u v : ι} (hadj : T.Adj u v)
    (hH_le : H ≤ G.deleteVerts (V(W u) ∩ V(W v))) (hH_conn : IsGraphConnected H) :
    V(H) ⊆ treeBagSideVerts T W u v ∨ V(H) ⊆ treeBagSideVerts T W v u := by
  obtain ⟨a, haH⟩ := hH_conn.1
  have haG : a ∈ V(G) := (hH_le.trans deleteVerts_le).vertexSet_mono haH
  rcases mem_treeBagSideVerts_or hTD hadj haG with ha_u | ha_v
  · left
    intro b hbH
    obtain ⟨W_ab⟩ := hH_conn.2 a haH b hbH
    exact walk_subset_treeBagSideVerts_of_disjoint hTD hadj (W_ab.mono hH_le) ha_u
  · right
    intro b hbH
    obtain ⟨W_ab⟩ := hH_conn.2 a haH b hbH
    have hH_le' : H ≤ G.deleteVerts (V(W v) ∩ V(W u)) := by
      rw [Set.inter_comm]
      exact hH_le
    exact walk_subset_treeBagSideVerts_of_disjoint hTD hadj.symm (W_ab.mono hH_le') ha_v

/-! ## 3. Havens Lower-Bound Tree-Width (Seymour–Thomas [8], Theorem 1.4) -/

/-- If `G` admits a haven `β_haven` of order `h`, then every tree-decomposition `(T, W)` of `G`
has a node `t` with `|V(W t)| ≥ h` (Seymour and Thomas [8], Theorem 1.4, easy direction). -/
theorem exists_node_ncard_ge_of_isHaven {G : Graph α β} (hVG : V(G).Finite)
    {h : ℕ} {β_haven : Set α → Graph α β} (hHaven : IsHaven G h β_haven)
    {T : SimpleGraph ι} {W : ι → Graph α β} (hTD : IsGraphTreeDecomposition G T W) :
    ∃ t : ι, h ≤ V(W t).ncard := by
  by_contra! hlt
  have : Nonempty ι := hTD.nonempty
  let R : ι → ι → Prop := fun u v =>
    V(β_haven (V(W u) ∩ V(W v))) ⊆ treeBagSideVerts T W u v
  have hR : ∀ ⦃u v : ι⦄, T.Adj u v → R u v ∨ R v u := by
    intro u v hadj
    have hsub_G : V(W u) ∩ V(W v) ⊆ V(G) :=
      inter_subset_left.trans (hTD.le u).vertexSet_mono
    have hcard_lt : (V(W u) ∩ V(W v)).ncard < h :=
      (ncard_le_ncard inter_subset_left (hVG.subset (hTD.le u).vertexSet_mono)).trans_lt (hlt u)
    have hcomp := hHaven.isComponent (V(W u) ∩ V(W v)) hsub_G hcard_lt
    rcases connected_subset_treeBagSideVerts_or hTD hadj hcomp.1 hcomp.2.1 with h1 | h2
    · exact Or.inl h1
    · right
      dsimp [R]
      rw [Set.inter_comm]
      exact h2
  obtain ⟨u₀, hu₀⟩ := exists_sink_of_adj_or hTD.isTree hR
  have hWu₀_sub : V(W u₀) ⊆ V(G) := (hTD.le u₀).vertexSet_mono
  have hcomp_u₀ := hHaven.isComponent V(W u₀) hWu₀_sub (hlt u₀)
  obtain ⟨x, hx⟩ := hcomp_u₀.2.1.1
  have hx_del : x ∈ V(G) \ V(W u₀) := by
    rw [← vertexSet_deleteVerts G V(W u₀)]
    exact hcomp_u₀.1.vertexSet_mono hx
  obtain ⟨t, hxt⟩ := hTD.vertex_mem_iff.mp hx_del.1
  have htu₀ : t ≠ u₀ := fun heq => hx_del.2 (heq ▸ hxt)
  obtain ⟨p, hp⟩ := hTD.isTree.connected.exists_isPath u₀ t
  cases p with
  | nil => exact (htu₀ rfl).elim
  | @cons _ w _ hadj q =>
    obtain ⟨hq, hu₀_not_q⟩ := (Walk.cons_isPath_iff hadj q).mp hp
    have ht_w : t ∈ treeComponent T w s(w, u₀) :=
      (mem_treeComponent_iff_notMem_support hTD.isTree hadj.symm hq).mpr hu₀_not_q
    have hx_w : x ∈ treeBagSideVerts T W w u₀ := mem_biUnion ht_w hxt
    have hmono : β_haven V(W u₀) ≤ β_haven (V(W u₀) ∩ V(W w)) :=
      hHaven.mono V(W u₀) (V(W u₀) ∩ V(W w)) inter_subset_left hWu₀_sub (hlt u₀)
    have hx_u₀ : x ∈ treeBagSideVerts T W u₀ w :=
      hu₀ w hadj (hmono.vertexSet_mono hx)
    have hx_inter : x ∈ V(W u₀) ∩ V(W w) :=
      mem_W_of_mem_treeBagSideVerts_inter hTD hadj hx_u₀ hx_w
    exact hx_del.2 hx_inter.1

/-- If `G` admits a haven of order `h`, then for every `w` with `TreeWidthLE G w`, we have
`h ≤ w + 1`. -/
theorem le_succ_of_isHaven_of_treeWidthLE {G : Graph α β} (hVG : V(G).Finite)
    {h w : ℕ} {β_haven : Set α → Graph α β} (hHaven : IsHaven G h β_haven)
    (htw : TreeWidthLE G w) : h ≤ w + 1 := by
  rcases htw with ⟨ι, _, T, W, hTD, hle⟩
  obtain ⟨t, ht⟩ := exists_node_ncard_ge_of_isHaven hVG hHaven hTD
  exact ht.trans (hle t)

/-! ## 4. Proof of 3.2 -/

/-- If `S : Fin h → Set α` is a family of pairwise disjoint sets and `X` is a finite set with
`X.ncard < h`, then there is some `i : Fin h` such that `Disjoint X (S i)`. -/
theorem exists_disjoint_of_ncard_lt {h : ℕ} {S : Fin h → Set α}
    (hdisj : Pairwise fun i j : Fin h => Disjoint (S i) (S j))
    {X : Set α} (hX_fin : X.Finite) (hX_lt : X.ncard < h) :
    ∃ i : Fin h, Disjoint X (S i) := by
  by_contra! hnot
  have hex : ∀ i : Fin h, ∃ x : α, x ∈ X ∧ x ∈ S i := fun i =>
    not_disjoint_iff.mp (hnot i)
  choose f hfX hfS using hex
  have hinj : Function.Injective f := by
    intro i j hij
    by_contra hne
    exact (hdisj hne).le_bot ⟨hfS i, hij ▸ hfS j⟩
  have hsub : range f ⊆ X := by rintro _ ⟨i, rfl⟩; exact hfX i
  have hcard_range : (range f).ncard = h := by
    rw [ncard_range_of_injective hinj, Nat.card_eq_fintype_card, Fintype.card_fin]
  have hle : h ≤ X.ncard := hcard_range ▸ ncard_le_ncard hsub hX_fin
  omega

/-- If `H ≤ G` and `Disjoint X V(H)`, then `H ≤ G.deleteVerts X`. -/
theorem le_deleteVerts_of_disjoint_left {G H : Graph α β} {X : Set α}
    (hHG : H ≤ G) (hdisj : Disjoint X V(H)) : H ≤ G.deleteVerts X := by
  refine ⟨fun v hv => ?_, fun e u v hl => ?_⟩
  · rw [vertexSet_deleteVerts]
    exact ⟨hHG.vertexSet_mono hv, disjoint_left.mp hdisj.symm hv⟩
  · rw [deleteVerts_isLink]
    exact ⟨hl.mono hHG, disjoint_left.mp hdisj.symm hl.left_mem,
      disjoint_left.mp hdisj.symm hl.right_mem⟩

/-- If `Y ⊆ X`, then `G.deleteVerts X ≤ G.deleteVerts Y`. -/
theorem deleteVerts_anti_subset (G : Graph α β) {X Y : Set α} (hYX : Y ⊆ X) :
    G.deleteVerts X ≤ G.deleteVerts Y := by
  refine ⟨fun v hv => ?_, fun e u v hl => ?_⟩
  · rw [vertexSet_deleteVerts] at hv ⊢
    exact ⟨hv.1, fun hvY => hv.2 (hYX hvY)⟩
  · rw [deleteVerts_isLink] at hl ⊢
    exact ⟨hl.1, fun huY => hl.2.1 (hYX huY), fun hvY => hl.2.2 (hYX hvY)⟩

/-- Every connected subgraph `C ≤ G` is contained in a connected component of `G`. -/
theorem exists_isGraphComponent_ge_of_isGraphConnected {G C : Graph α β}
    (hCG : C ≤ G) (hConn : IsGraphConnected C) :
    ∃ H : Graph α β, IsGraphComponent H G ∧ C ≤ H := by
  obtain ⟨x, hxC⟩ := hConn.1
  exact ⟨compOf G x, isGraphComponent_compOf (hCG.vertexSet_mono hxC),
    le_compOf_of_isGraphConnected hCG hConn hxC⟩

/-- Construction of a haven of order `h` from mutually vertex-disjoint connected subgraphs
`C₁, ..., C_h` and `D₁, ..., D_h` such that `V(C i) ∩ V(D j)` is non-empty for all `i, j`
(Graph Minors XXII, Section 3, proof of 3.2, page 535). -/
theorem exists_isHaven_of_cross_subgraphs {G : Graph α β} (hVG : V(G).Finite)
    {h : ℕ} (C D : Fin h → Graph α β)
    (hC_le : ∀ i : Fin h, C i ≤ G) (hC_conn : ∀ i : Fin h, IsGraphConnected (C i))
    (hC_disj : Pairwise fun i j : Fin h => Disjoint V(C i) V(C j))
    (hD_le : ∀ j : Fin h, D j ≤ G) (hD_conn : ∀ j : Fin h, IsGraphConnected (D j))
    (hD_disj : Pairwise fun i j : Fin h => Disjoint V(D i) V(D j))
    (hCD_inter : ∀ i j : Fin h, (V(C i) ∩ V(D j)).Nonempty) :
    ∃ β_haven : Set α → Graph α β, IsHaven G h β_haven := by
  classical
  have hex_comp : ∀ (X : Set α), X ⊆ V(G) → X.ncard < h →
      ∃ H : Graph α β, IsGraphComponent H (G.deleteVerts X) ∧
        (∀ i : Fin h, Disjoint X V(C i) → C i ≤ H) ∧
        (∀ j : Fin h, Disjoint X V(D j) → D j ≤ H) := by
    intro X hX_sub hX_lt
    have hX_fin : X.Finite := hVG.subset hX_sub
    obtain ⟨i₀, hi₀⟩ := exists_disjoint_of_ncard_lt hC_disj hX_fin hX_lt
    have hCi₀_del : C i₀ ≤ G.deleteVerts X :=
      le_deleteVerts_of_disjoint_left (hC_le i₀) hi₀
    obtain ⟨H, hH_comp, hCi₀_H⟩ :=
      exists_isGraphComponent_ge_of_isGraphConnected hCi₀_del (hC_conn i₀)
    have hD_in_H : ∀ j : Fin h, Disjoint X V(D j) → D j ≤ H := by
      intro j hj
      have hDj_del : D j ≤ G.deleteVerts X :=
        le_deleteVerts_of_disjoint_left (hD_le j) hj
      obtain ⟨H', hH'_comp, hDj_H'⟩ :=
        exists_isGraphComponent_ge_of_isGraphConnected hDj_del (hD_conn j)
      obtain ⟨z, hzC, hzD⟩ := hCD_inter i₀ j
      have hHH' : H = H' :=
        hH_comp.eq_of_mem_mem hH'_comp (hCi₀_H.vertexSet_mono hzC) (hDj_H'.vertexSet_mono hzD)
      exact hHH' ▸ hDj_H'
    obtain ⟨j₀, hj₀⟩ := exists_disjoint_of_ncard_lt hD_disj hX_fin hX_lt
    have hDj₀_H : D j₀ ≤ H := hD_in_H j₀ hj₀
    have hC_in_H : ∀ i : Fin h, Disjoint X V(C i) → C i ≤ H := by
      intro i hi
      have hCi_del : C i ≤ G.deleteVerts X :=
        le_deleteVerts_of_disjoint_left (hC_le i) hi
      obtain ⟨H', hH'_comp, hCi_H'⟩ :=
        exists_isGraphComponent_ge_of_isGraphConnected hCi_del (hC_conn i)
      obtain ⟨z, hzC, hzD⟩ := hCD_inter i j₀
      have hHH' : H = H' :=
        hH_comp.eq_of_mem_mem hH'_comp (hDj₀_H.vertexSet_mono hzD) (hCi_H'.vertexSet_mono hzC)
      exact hHH' ▸ hCi_H'
    exact ⟨H, hH_comp, hC_in_H, hD_in_H⟩
  let β_haven : Set α → Graph α β := fun X =>
    if hcond : X ⊆ V(G) ∧ X.ncard < h then (hex_comp X hcond.1 hcond.2).choose else ⊥
  refine ⟨β_haven, ?_, ?_⟩
  · intro X hX_sub hX_lt
    have hcond : X ⊆ V(G) ∧ X.ncard < h := ⟨hX_sub, hX_lt⟩
    simpa [β_haven, hcond] using (hex_comp X hX_sub hX_lt).choose_spec.1
  · intro X Y hYX hX_sub hX_lt
    have hX_fin : X.Finite := hVG.subset hX_sub
    have hY_sub : Y ⊆ V(G) := hYX.trans hX_sub
    have hY_lt : Y.ncard < h := (ncard_le_ncard hYX hX_fin).trans_lt hX_lt
    have hX_cond : X ⊆ V(G) ∧ X.ncard < h := ⟨hX_sub, hX_lt⟩
    have hY_cond : Y ⊆ V(G) ∧ Y.ncard < h := ⟨hY_sub, hY_lt⟩
    have hHX := (hex_comp X hX_sub hX_lt).choose_spec
    have hHY := (hex_comp Y hY_sub hY_lt).choose_spec
    have hβX : β_haven X = (hex_comp X hX_sub hX_lt).choose := by
      simp [β_haven, hX_cond]
    have hβY : β_haven Y = (hex_comp Y hY_sub hY_lt).choose := by
      simp [β_haven, hY_cond]
    rw [hβX, hβY]
    obtain ⟨i₀, hi₀⟩ := exists_disjoint_of_ncard_lt hC_disj hX_fin hX_lt
    have hi₀Y : Disjoint Y V(C i₀) := hi₀.mono_left hYX
    have hCi₀_X : C i₀ ≤ (hex_comp X hX_sub hX_lt).choose := hHX.2.1 i₀ hi₀
    have hCi₀_Y : C i₀ ≤ (hex_comp Y hY_sub hY_lt).choose := hHY.2.1 i₀ hi₀Y
    have hdel_le : G.deleteVerts X ≤ G.deleteVerts Y := deleteVerts_anti_subset G hYX
    have hHX_in_delY : (hex_comp X hX_sub hX_lt).choose ≤ G.deleteVerts Y :=
      hHX.1.1.trans hdel_le
    obtain ⟨H', hH'_comp, hHX_le_H'⟩ :=
      exists_isGraphComponent_ge_of_isGraphConnected hHX_in_delY hHX.1.2.1
    obtain ⟨z, hzC⟩ := (hC_conn i₀).1
    have hH'_eq : H' = (hex_comp Y hY_sub hY_lt).choose :=
      hH'_comp.eq_of_mem_mem hHY.1
        (hHX_le_H'.vertexSet_mono (hCi₀_X.vertexSet_mono hzC))
        (hCi₀_Y.vertexSet_mono hzC)
    exact hH'_eq ▸ hHX_le_H'

/-- **Graph Minors XXII, 3.2** (page 534):
"Let $C_1, \ldots, C_h$ be mutually vertex-disjoint connected subgraphs of a graph $G$, and also
let $D_1, \ldots, D_h$ be mutually vertex-disjoint connected subgraphs of $G$. Suppose that
$C_i \cap D_j$ is non-null for $1 \le i, j \le h$. Then $G$ has tree-width at least $h - 1$." -/
theorem theorem_3_2_proof {G : Graph α β} (hVG : V(G).Finite)
    {h : ℕ} (C D : Fin h → Graph α β)
    (hC_le : ∀ i : Fin h, C i ≤ G) (hC_conn : ∀ i : Fin h, IsGraphConnected (C i))
    (hC_disj : Pairwise fun i j : Fin h => Disjoint V(C i) V(C j))
    (hD_le : ∀ j : Fin h, D j ≤ G) (hD_conn : ∀ j : Fin h, IsGraphConnected (D j))
    (hD_disj : Pairwise fun i j : Fin h => Disjoint V(D i) V(D j))
    (hCD_inter : ∀ i j : Fin h, (V(C i) ∩ V(D j)).Nonempty) :
    (∀ w : ℕ, TreeWidthLE G w → h ≤ w + 1) ∧ (h : ℤ) - 1 ≤ graphTreeWidth G := by
  obtain ⟨β_haven, hHaven⟩ :=
    exists_isHaven_of_cross_subgraphs hVG C D hC_le hC_conn hC_disj hD_le hD_conn hD_disj hCD_inter
  have hle_succ : ∀ w : ℕ, TreeWidthLE G w → h ≤ w + 1 :=
    fun w htw => le_succ_of_isHaven_of_treeWidthLE hVG hHaven htw
  refine ⟨hle_succ, ?_⟩
  unfold graphTreeWidth graphTreeWidthPlusOne
  let S : Set ℕ := {w : ℕ | ∃ (ι : Type) (_ : Fintype ι) (T : SimpleGraph ι) (W : ι → Graph α β),
    IsGraphTreeDecomposition G T W ∧ graphTreeDecompWidthPlusOne W = w}
  have hle_triv : ∀ P ∈ range (fun _ : Fin 1 => G), P ≤ G := by
    rintro _ ⟨_, rfl⟩; exact le_rfl
  have hS_ne : S.Nonempty := by
    refine ⟨V(G).ncard, Fin 1, inferInstance, ⊥, fun _ => G, ?_, ?_⟩
    · refine ⟨?_, fun _ => le_rfl, ?_, fun _ _ _ _ => subgraphInter_le_left le_rfl le_rfl⟩
      · refine ⟨Connected.mk fun u v => Subsingleton.elim u v ▸ Reachable.rfl, ?_⟩
        intro v p hp
        cases p with
        | nil => exact hp.ne_nil rfl
        | cons hadj _ => exact hadj
      · exact le_antisymm (subgraphSUnion_le hle_triv) (le_subgraphSUnion hle_triv ⟨0, rfl⟩)
    · unfold graphTreeDecompWidthPlusOne
      have hrange : (range fun _ : Fin 1 => V(G).ncard) = {V(G).ncard} := by
        ext n; simp
      rw [hrange, csSup_singleton]
  have hsInf_mem : sInf S ∈ S := Nat.sInf_mem hS_ne
  rcases hsInf_mem with ⟨ι₀, _, T₀, W₀, hTD₀, hw₀⟩
  obtain ⟨t₀, ht₀⟩ := exists_node_ncard_ge_of_isHaven hVG hHaven hTD₀
  have ht₀_le : V(W₀ t₀).ncard ≤ graphTreeDecompWidthPlusOne W₀ :=
    le_csSup (finite_range _).bddAbove ⟨t₀, rfl⟩
  have hh_le : h ≤ sInf S := ht₀.trans (hw₀ ▸ ht₀_le)
  have hgoal : (h : ℤ) - 1 ≤ (↑(sInf S) : ℤ) - 1 := by omega
  exact hgoal

end GraphMinor.GM22
