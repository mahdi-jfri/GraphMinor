module

public import GraphMinor.Compute.Specs4
import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Combinatorics.SimpleGraph.Metric

/-!
# Branch-Width Soundness for GM XIII Algorithm (3.3) / (4.4)

This file formalizes **Lemma (3.1)** (page 71), **Lemma (3.2)** (page 72), and the Step (6)
branch-width lower bound (page 74) of Robertson and Seymour,
*Graph Minors. XIII. The Disjoint Paths Problem*, J. Combin. Theory Ser. B 63 (1995), 65–110,
and deduces the soundness bridge for `Alg33Spec`:
`isAlg33HighWidthCase_imp_hasBranchWidthGe : 2 ≤ ω → IsAlg33HighWidthCase ω G G' → HasBranchWidthGe G' ω`.
-/

@[expose] public section

namespace GraphMinor.Compute

open SimpleGraph

/-! ### Section 1: Simple `MultiDigraph` Edge Bijection with `G'.toSimpleGraph.edgeFinset` -/

/-- The undirected edge `s(tail, head) : Sym2 (Fin n)` of edge `e : Fin G.numEdges`. -/
def sym2OfEdge {n : ℕ} (G : MultiDigraph n) (e : Fin G.numEdges) : Sym2 (Fin n) :=
  s((G.edgeEndpoints e).1, (G.edgeEndpoints e).2)

theorem edgeEndpoints_mem_activePairsList {n : ℕ} (G : MultiDigraph n) (e : Fin G.numEdges) :
    G.edgeEndpoints e ∈ G.activePairsList := by
  have hmem : G.edgeEndpoints e ∈ G.edgeListWithMult :=
    List.getElem_mem (by rw [G.length_edgeListWithMult]; exact e.2)
  unfold MultiDigraph.edgeListWithMult at hmem
  rw [List.mem_flatMap] at hmem
  rcases hmem with ⟨p, hp_mem, hp_rep⟩
  rw [List.mem_replicate] at hp_rep
  rcases hp_rep with ⟨_, rfl⟩
  exact hp_mem

theorem edgeMult_edgeEndpoints_pos {n : ℕ} (G : MultiDigraph n) (e : Fin G.numEdges) :
    0 < G.edgeMult (G.edgeEndpoints e).1 (G.edgeEndpoints e).2 := by
  have hmem := edgeEndpoints_mem_activePairsList G e
  rwa [G.mem_activePairsList] at hmem

theorem sym2OfEdge_mem_edgeFinset_of_noLoops {n : ℕ} {G : MultiDigraph n}
    (hloop : ∀ u : Fin n, G.edgeMult u u = 0) (e : Fin G.numEdges) :
    sym2OfEdge G e ∈ G.toSimpleGraph.edgeFinset := by
  unfold sym2OfEdge
  rw [mem_edgeFinset, mem_edgeSet]
  have hpos := edgeMult_edgeEndpoints_pos G e
  have hne : (G.edgeEndpoints e).1 ≠ (G.edgeEndpoints e).2 := by
    intro heq
    rw [heq, hloop] at hpos
    omega
  exact ⟨hne, Or.inl hpos⟩

theorem eq_of_edgeEndpoints_eq_of_simple {n : ℕ} {G : MultiDigraph n}
    (hmult : ∀ u v : Fin n, G.edgeMult u v + G.edgeMult v u ≤ 1)
    {e₁ e₂ : Fin G.numEdges} (h : G.edgeEndpoints e₁ = G.edgeEndpoints e₂) :
    e₁ = e₂ := by
  let x := (G.edgeEndpoints e₁).1
  let y := (G.edgeEndpoints e₁).2
  have hmap : G.edgeListWithMult =
      (List.finRange G.numEdges).map (fun e => G.edgeEndpoints e) := by
    apply List.ext_getElem
    · simp [G.length_edgeListWithMult]
    · intro i h1 h2; simp [MultiDigraph.edgeEndpoints]
  let l := (List.finRange G.numEdges).filter (fun e => decide (G.edgeEndpoints e = (x, y)))
  have hl_nodup : l.Nodup := (List.nodup_finRange G.numEdges).filter _
  have he₁ : e₁ ∈ l := by simp [l, x, y]
  have he₂ : e₂ ∈ l := by simp [l, ← h, x, y]
  have hl_len : l.length ≤ 1 := by
    rw [← List.countP_eq_length_filter]
    have hcount : G.edgeListWithMult.countP (· == (x, y)) =
        (List.finRange G.numEdges).countP (fun e => decide (G.edgeEndpoints e = (x, y))) := by
      conv_lhs => rw [hmap]
      rw [List.countP_map]
      congr 1
    rw [← hcount]
    have hle : G.edgeListWithMult.countP (· == (x, y)) ≤ G.edgeMult x y := by
      unfold MultiDigraph.edgeListWithMult
      have hsub : ∀ (ps : List (Fin n × Fin n)), ps.Nodup →
          (ps.flatMap (fun p => List.replicate (G.edgeMult p.1 p.2) p)).countP (· == (x, y)) ≤
            G.edgeMult x y := by
        intro ps hnd
        induction ps with
        | nil => simp
        | cons p ps ih =>
          rw [List.nodup_cons] at hnd
          rw [List.flatMap_cons, List.countP_append]
          by_cases hp : p = (x, y)
          · subst hp
            have h0 : (ps.flatMap (fun p => List.replicate (G.edgeMult p.1 p.2) p)).countP
                (· == (x, y)) = 0 := by
              rw [List.countP_eq_zero]
              intro q hq
              rw [List.mem_flatMap] at hq
              rcases hq with ⟨p', hp'_mem, hp'_rep⟩
              rw [List.mem_replicate] at hp'_rep
              rcases hp'_rep with ⟨_, rfl⟩
              simp only [beq_iff_eq]
              intro heq
              exact hnd.1 (heq ▸ hp'_mem)
            rw [h0, add_zero, List.countP_eq_length_filter,
              List.filter_eq_self.mpr (by simp), List.length_replicate]
          · have h0 : (List.replicate (G.edgeMult p.1 p.2) p).countP (· == (x, y)) = 0 := by
              rw [List.countP_eq_zero]
              intro q hq
              rw [List.mem_replicate] at hq
              rcases hq with ⟨_, rfl⟩
              simpa using hp
            rw [h0, zero_add]
            exact ih hnd.2
      exact hsub G.activePairsList G.nodup_activePairsList
    have := hmult x y
    omega
  cases hl : l with
  | nil => rw [hl] at he₁; cases he₁
  | cons a rest =>
    cases hrest : rest with
    | nil =>
      rw [hl, hrest] at he₁ he₂
      simp only [List.mem_singleton] at he₁ he₂
      exact he₁.trans he₂.symm
    | cons b rest' =>
      rw [hl, hrest, List.length_cons, List.length_cons] at hl_len
      omega

theorem sym2OfEdge_injective_of_simple {n : ℕ} {G : MultiDigraph n}
    (hmult : ∀ u v : Fin n, G.edgeMult u v + G.edgeMult v u ≤ 1) :
    Function.Injective (sym2OfEdge G) := by
  intro e₁ e₂ heq
  unfold sym2OfEdge at heq
  rcases Sym2.eq_iff.mp heq with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact eq_of_edgeEndpoints_eq_of_simple hmult (Prod.ext h1 h2)
  · exfalso
    have hp₁ := edgeMult_edgeEndpoints_pos G e₁
    have hp₂ := edgeMult_edgeEndpoints_pos G e₂
    rw [← h1, ← h2] at hp₂
    have hle := hmult (G.edgeEndpoints e₁).1 (G.edgeEndpoints e₁).2
    omega

theorem exists_sym2OfEdge_eq_of_mem_edgeFinset {n : ℕ} {G : MultiDigraph n}
    {e : Sym2 (Fin n)} (he : e ∈ G.toSimpleGraph.edgeFinset) :
    ∃ idx : Fin G.numEdges, sym2OfEdge G idx = e := by
  induction e using Sym2.ind with
  | _ u v =>
    rw [mem_edgeFinset, mem_edgeSet] at he
    have hex_pair : ∃ p : Fin n × Fin n, p ∈ G.edgeListWithMult ∧ s(p.1, p.2) = s(u, v) := by
      rcases he.2 with huv | hvu
      · refine ⟨(u, v), ?_, rfl⟩
        unfold MultiDigraph.edgeListWithMult
        rw [List.mem_flatMap]
        exact ⟨(u, v), (G.mem_activePairsList (u, v)).mpr huv,
          List.mem_replicate.mpr ⟨ne_of_gt huv, rfl⟩⟩
      · refine ⟨(v, u), ?_, Sym2.eq_swap⟩
        unfold MultiDigraph.edgeListWithMult
        rw [List.mem_flatMap]
        exact ⟨(v, u), (G.mem_activePairsList (v, u)).mpr hvu,
          List.mem_replicate.mpr ⟨ne_of_gt hvu, rfl⟩⟩
    rcases hex_pair with ⟨p, hp_mem, hp_sym⟩
    rcases List.mem_iff_getElem.mp hp_mem with ⟨i, hi, hp_eq⟩
    have hi' : i < G.numEdges := by rwa [← G.length_edgeListWithMult]
    refine ⟨⟨i, hi'⟩, ?_⟩
    unfold sym2OfEdge MultiDigraph.edgeEndpoints
    rw [hp_eq, hp_sym]

theorem card_edgeFinset_toSimpleGraph_of_simple {n : ℕ} {G : MultiDigraph n}
    (hloop : ∀ u : Fin n, G.edgeMult u u = 0)
    (hmult : ∀ u v : Fin n, G.edgeMult u v + G.edgeMult v u ≤ 1) :
    G.toSimpleGraph.edgeFinset.card = G.numEdges := by
  have heq : G.toSimpleGraph.edgeFinset = Finset.univ.image (sym2OfEdge G) := by
    ext e
    simp only [Finset.mem_image, Finset.mem_univ, true_and]
    exact ⟨exists_sym2OfEdge_eq_of_mem_edgeFinset,
      by rintro ⟨idx, rfl⟩; exact sym2OfEdge_mem_edgeFinset_of_noLoops hloop idx⟩
  rw [heq, Finset.card_image_of_injective _ (sym2OfEdge_injective_of_simple hmult),
    Finset.card_fin]

/-- Convert a branch-decomposition `(T, τ)` of a simple `MultiDigraph` `G` to a branch-decomposition
`(T, τ_sym2)` of `G.toSimpleGraph`. -/
theorem isBranchDecompOfWidthLe_toSimpleGraph_of_simple {n t B : ℕ} {G : MultiDigraph n}
    (hloop : ∀ u : Fin n, G.edgeMult u u = 0)
    (hmult : ∀ u v : Fin n, G.edgeMult u v + G.edgeMult v u ≤ 1)
    {T : SimpleGraph (Fin t)} [DecidableRel T.Adj]
    {τ : Fin G.numEdges → Fin t}
    (hbd : IsMultiBranchDecompOfWidthLe B G T τ) :
    ∃ τ_sym2 : Sym2 (Fin n) → Fin t,
      IsBranchDecompOfWidthLe B G.toSimpleGraph T τ_sym2 := by
  have ht_pos : 0 < t := by
    rcases hbd.1.1.connected.nonempty with ⟨v₀⟩
    exact Nat.zero_lt_of_lt v₀.2
  let τ_sym2 (e : Sym2 (Fin n)) : Fin t :=
    open Classical in
    if h : ∃ idx : Fin G.numEdges, sym2OfEdge G idx = e then τ (Classical.choose h)
    else ⟨0, ht_pos⟩
  have hτ_eq : ∀ idx : Fin G.numEdges, τ_sym2 (sym2OfEdge G idx) = τ idx := by
    intro idx
    have hex : ∃ i : Fin G.numEdges, sym2OfEdge G i = sym2OfEdge G idx := ⟨idx, rfl⟩
    have hchoose : Classical.choose hex = idx :=
      sym2OfEdge_injective_of_simple hmult (Classical.choose_spec hex)
    simp only [τ_sym2, hex, ↓reduceDIte, hchoose]
  refine ⟨τ_sym2, hbd.1, ⟨?_, ?_, ?_⟩, ?_⟩
  · intro e he
    rcases exists_sym2OfEdge_eq_of_mem_edgeFinset he with ⟨idx, rfl⟩
    rw [hτ_eq]
    exact hbd.2.1.mapsTo (Set.mem_univ idx)
  · intro e₁ he₁ e₂ he₂ heq
    rcases exists_sym2OfEdge_eq_of_mem_edgeFinset he₁ with ⟨idx₁, rfl⟩
    rcases exists_sym2OfEdge_eq_of_mem_edgeFinset he₂ with ⟨idx₂, rfl⟩
    rw [hτ_eq, hτ_eq] at heq
    rw [hbd.2.1.injOn (Set.mem_univ idx₁) (Set.mem_univ idx₂) heq]
  · intro v hv
    rcases hbd.2.1.surjOn hv with ⟨idx, _, rfl⟩
    exact ⟨sym2OfEdge G idx,
      Finset.mem_coe.mpr (sym2OfEdge_mem_edgeFinset_of_noLoops hloop idx), hτ_eq idx⟩
  · intro f hf
    have hcut_eq : treeEdgeCutVerts G.toSimpleGraph T τ_sym2 f =
        digraphTreeEdgeCutVerts G.toMultiComputeDigraph T τ f := by
      ext w
      rw [mem_treeEdgeCutVerts]
      unfold digraphTreeEdgeCutVerts
      rw [Finset.mem_filter]
      simp only [Finset.mem_univ, true_and, digraphIncident]
      constructor
      · rintro ⟨e₁, he₁, e₂, he₂, hw₁, hw₂, hnr⟩
        rcases exists_sym2OfEdge_eq_of_mem_edgeFinset he₁ with ⟨idx₁, rfl⟩
        rcases exists_sym2OfEdge_eq_of_mem_edgeFinset he₂ with ⟨idx₂, rfl⟩
        rw [hτ_eq, hτ_eq] at hnr
        simp only [sym2OfEdge, Sym2.mem_iff] at hw₁ hw₂
        exact ⟨idx₁, idx₂, by tauto, by tauto, hnr⟩
      · rintro ⟨idx₁, idx₂, hw₁, hw₂, hnr⟩
        refine ⟨sym2OfEdge G idx₁, sym2OfEdge_mem_edgeFinset_of_noLoops hloop idx₁,
          sym2OfEdge G idx₂, sym2OfEdge_mem_edgeFinset_of_noLoops hloop idx₂, ?_, ?_, ?_⟩
        · simp only [sym2OfEdge, Sym2.mem_iff]; tauto
        · simp only [sym2OfEdge, Sym2.mem_iff]; tauto
        · rwa [hτ_eq, hτ_eq]
    unfold treeEdgeOrder
    rw [hcut_eq]
    exact hbd.2.2 f hf

/-! ### Section 2: Tree Components, `OnTreePath`, and `dist_lt_of_mem_treeComponent` -/

/-- Vertex `t` lies on every path in `T` between `t₁` and `t₂`. -/
def OnTreePath {ι : Type*} (T : SimpleGraph ι) (t₁ t₂ t : ι) : Prop :=
  ∀ ⦃p : T.Walk t₁ t₂⦄, p.IsPath → t ∈ p.support

/-- The vertex set of the component of `T \ {f}` containing `u`. -/
def treeComp {ι : Type*} (T : SimpleGraph ι) (u : ι) (f : Sym2 ι) : Set ι :=
  {x : ι | (T.deleteEdges {f}).Reachable u x}

theorem onTreePath_refl_left {ι : Type*} (T : SimpleGraph ι) (t₁ t₂ : ι) :
    OnTreePath T t₁ t₂ t₁ :=
  fun p _ => p.start_mem_support

theorem onTreePath_refl_right {ι : Type*} (T : SimpleGraph ι) (t₁ t₂ : ι) :
    OnTreePath T t₁ t₂ t₂ :=
  fun p _ => p.end_mem_support

theorem onTreePath_comm {ι : Type*} {T : SimpleGraph ι} {t₁ t₂ t : ι} :
    OnTreePath T t₁ t₂ t ↔ OnTreePath T t₂ t₁ t := by
  constructor <;> intro h p hp
  · have hm := h ((Walk.isPath_reverse_iff p).2 hp)
    rwa [Walk.support_reverse, List.mem_reverse] at hm
  · have hm := h ((Walk.isPath_reverse_iff p).2 hp)
    rwa [Walk.support_reverse, List.mem_reverse] at hm

theorem mem_support_of_onTreePath {ι : Type*} {T : SimpleGraph ι} {t₁ t₂ t : ι}
    (h : OnTreePath T t₁ t₂ t) (w : T.Walk t₁ t₂) : t ∈ w.support := by
  classical
  exact Walk.support_bypass_subset_support w (h (Walk.bypass_isPath w))

theorem onTreePath_iff_of_isPath {ι : Type*} {T : SimpleGraph ι} (hT : T.IsTree)
    {t₁ t₂ t : ι} {p : T.Walk t₁ t₂} (hp : p.IsPath) :
    OnTreePath T t₁ t₂ t ↔ t ∈ p.support := by
  constructor
  · intro h; exact h hp
  · intro ht q hq
    have hqp : q = p :=
      congrArg Subtype.val ((hT.isAcyclic.subsingleton_path t₁ t₂).elim ⟨q, hq⟩ ⟨p, hp⟩)
    rwa [hqp]

theorem eq_or_eq_of_onTreePath_of_unique_adj {ι : Type*} {T : SimpleGraph ι}
    (hconn : T.Connected) {v : ι}
    (huniq : ∀ w₁ w₂, T.Adj v w₁ → T.Adj v w₂ → w₁ = w₂)
    {a b : ι} (h : OnTreePath T a b v) : v = a ∨ v = b := by
  obtain ⟨p, hp⟩ := hconn.exists_isPath a b
  have hv : v ∈ p.support := h hp
  clear h
  induction p with
  | nil => exact Or.inl (by simpa using hv)
  | @cons a x b h₁ q ih =>
    rw [Walk.cons_isPath_iff] at hp
    rw [Walk.support_cons, List.mem_cons] at hv
    rcases hv with rfl | hv_q
    · exact Or.inl rfl
    · rcases ih hp.1 hv_q with rfl | rfl
      · cases q with
        | nil => exact Or.inr rfl
        | @cons _ y _ h₂ r =>
          have hay : a = y := huniq a y h₁.symm h₂
          subst hay
          exact (hp.2 (Walk.support_subset_support_cons r h₂ r.start_mem_support)).elim
      · exact Or.inr rfl

theorem reachable_deleteEdges_iff_notMem_edges {ι : Type*} {T : SimpleGraph ι} (hT : T.IsTree)
    {u w x : ι} {p : T.Walk u x} (hp : p.IsPath) :
    (T.deleteEdges {s(u, w)}).Reachable u x ↔ s(u, w) ∉ p.edges := by
  rw [reachable_deleteEdges_iff_exists_walk]
  constructor
  · rintro ⟨q, hq⟩
    classical
    have hqp : q.toPath.val = p :=
      congrArg Subtype.val ((hT.isAcyclic.subsingleton_path u x).elim q.toPath ⟨p, hp⟩)
    intro hmem
    rw [← hqp] at hmem
    exact hq (Walk.edges_toPath_subset_edges q hmem)
  · intro hnot
    exact ⟨p, hnot⟩

theorem mem_edges_iff_mem_support_of_adj {ι : Type*} {T : SimpleGraph ι} (hT : T.IsTree)
    {u w x : ι} (hadj : T.Adj u w) {p : T.Walk u x} (hp : p.IsPath) :
    s(u, w) ∈ p.edges ↔ w ∈ p.support := by
  constructor
  · intro hmem
    rw [Sym2.eq_swap] at hmem
    exact Walk.fst_mem_support_of_mem_edges p hmem
  · intro hw
    have hwsnd : w = p.snd := hT.isAcyclic.eq_snd_of_adj_start hp hadj hw
    rw [hwsnd]
    cases p with
    | nil =>
      rw [Walk.support_nil, List.mem_singleton] at hw
      exact (hadj.ne hw.symm).elim
    | cons _ _ => simp

theorem mem_treeComp_iff_notMem_support {ι : Type*} {T : SimpleGraph ι} (hT : T.IsTree)
    {u w x : ι} (hadj : T.Adj u w) {p : T.Walk u x} (hp : p.IsPath) :
    x ∈ treeComp T u s(u, w) ↔ w ∉ p.support := by
  change (T.deleteEdges {s(u, w)}).Reachable u x ↔ w ∉ p.support
  rw [reachable_deleteEdges_iff_notMem_edges hT hp,
    mem_edges_iff_mem_support_of_adj hT hadj hp]

theorem notMem_treeComp_iff {ι : Type*} {T : SimpleGraph ι} (hT : T.IsTree)
    {u w x : ι} (hadj : T.Adj u w) :
    x ∉ treeComp T u s(u, w) ↔ x ∈ treeComp T w s(w, u) := by
  constructor
  · intro hnot
    obtain ⟨p, hp⟩ := hT.connected.exists_isPath u x
    have hw : w ∈ p.support := by
      by_contra hwnot
      exact hnot ((mem_treeComp_iff_notMem_support hT hadj hp).2 hwnot)
    have hwsnd : w = p.snd := hT.isAcyclic.eq_snd_of_adj_start hp hadj hw
    cases p with
    | nil =>
      rw [Walk.support_nil, List.mem_singleton] at hw
      exact (hadj.ne hw.symm).elim
    | cons hadj' q =>
      simp only [Walk.snd_cons] at hwsnd
      subst hwsnd
      rw [Walk.cons_isPath_iff] at hp
      exact (mem_treeComp_iff_notMem_support hT hadj.symm hp.1).2 hp.2
  · intro hx_w hx_u
    have hx_w' : (T.deleteEdges {s(u, w)}).Reachable w x := by
      simpa [treeComp, Sym2.eq_swap] using hx_w
    have huw : (T.deleteEdges {s(u, w)}).Reachable u w := hx_u.trans hx_w'.symm
    have hp_edge : (Walk.cons hadj Walk.nil).IsPath := Walk.IsPath.nil.cons (by simp [hadj.ne])
    have hnot_edge := (reachable_deleteEdges_iff_notMem_edges hT hp_edge).1 huw
    exact hnot_edge (by simp)

theorem not_reachable_deleteEdges_iff_treeComp {ι : Type*} {T : SimpleGraph ι} (hT : T.IsTree)
    {u w t₁ t₂ : ι} (hadj : T.Adj u w) :
    ¬ (T.deleteEdges {s(u, w)}).Reachable t₁ t₂ ↔
      (t₁ ∈ treeComp T u s(u, w) ∧ t₂ ∈ treeComp T w s(w, u)) ∨
      (t₁ ∈ treeComp T w s(w, u) ∧ t₂ ∈ treeComp T u s(u, w)) := by
  have h1 := notMem_treeComp_iff hT hadj (x := t₁)
  have h2 := notMem_treeComp_iff hT hadj (x := t₂)
  constructor
  · intro hnot
    by_cases ht₁ : t₁ ∈ treeComp T u s(u, w)
    · refine Or.inl ⟨ht₁, h2.1 fun ht₂ => hnot (ht₁.symm.trans ht₂)⟩
    · refine Or.inr ⟨h1.1 ht₁, ?_⟩
      by_contra ht₂
      have ht₁' : (T.deleteEdges {s(u, w)}).Reachable w t₁ := by
        simpa [treeComp, Sym2.eq_swap] using h1.1 ht₁
      have ht₂' : (T.deleteEdges {s(u, w)}).Reachable w t₂ := by
        simpa [treeComp, Sym2.eq_swap] using h2.1 ht₂
      exact hnot (ht₁'.symm.trans ht₂')
  · rintro (⟨ht₁, ht₂⟩ | ⟨ht₁, ht₂⟩) hreach
    · exact (h2.2 ht₂) (ht₁.trans hreach)
    · exact (h1.2 ht₁) (ht₂.trans hreach.symm)

theorem mem_treeComp_of_onTreePath {ι : Type*} {T : SimpleGraph ι} {u : ι} {e : Sym2 ι}
    {a b x : ι} (ha : a ∈ treeComp T u e) (hb : b ∈ treeComp T u e)
    (h : OnTreePath T a b x) : x ∈ treeComp T u e := by
  classical
  have hab : (T.deleteEdges {e}).Reachable a b := ha.symm.trans hb
  obtain ⟨w⟩ := hab
  have hx_map : x ∈ (w.mapLe (SimpleGraph.deleteEdges_le _)).support :=
    mem_support_of_onTreePath h _
  rw [Walk.support_map, List.mem_map] at hx_map
  obtain ⟨z, hz, rfl⟩ := hx_map
  exact ha.trans (Walk.reachable (w.takeUntil z hz))

theorem mem_treeComp_left_or_right_of_onTreePath {ι : Type*} {T : SimpleGraph ι} (hT : T.IsTree)
    {u w a b x : ι} (hadj : T.Adj u w)
    (hx : x ∈ treeComp T u s(u, w)) (h : OnTreePath T a b x) :
    a ∈ treeComp T u s(u, w) ∨ b ∈ treeComp T u s(u, w) := by
  by_contra! hnot
  have ha' : a ∈ treeComp T w s(w, u) := (notMem_treeComp_iff hT hadj).1 hnot.1
  have hb' : b ∈ treeComp T w s(w, u) := (notMem_treeComp_iff hT hadj).1 hnot.2
  have hx' : x ∈ treeComp T w s(w, u) := mem_treeComp_of_onTreePath ha' hb' h
  exact (notMem_treeComp_iff hT hadj).2 hx' hx

theorem onTreePath_of_mem_treeComp {ι : Type*} {T : SimpleGraph ι} (hT : T.IsTree)
    {u w a b : ι} (hadj : T.Adj u w)
    (ha : a ∈ treeComp T u s(u, w)) (hb : b ∈ treeComp T w s(w, u)) :
    OnTreePath T a b u := by
  intro p _
  have hnot_reach : ¬ (T.deleteEdges {s(u, w)}).Reachable a b :=
    (not_reachable_deleteEdges_iff_treeComp hT hadj).2 (Or.inl ⟨ha, hb⟩)
  have he_mem : s(u, w) ∈ p.edges := by
    by_contra he_not
    apply hnot_reach
    exact ⟨p.toDeleteEdges {s(u, w)} fun e he hmem => by
      rw [Set.mem_singleton_iff] at hmem
      exact he_not (hmem ▸ he)⟩
  exact Walk.fst_mem_support_of_mem_edges p he_mem

theorem isConvex_exists_onTreePath {ι : Type*} {T : SimpleGraph ι} (hT : T.IsTree) {S : Set ι}
    {a b c : ι}
    (ha : ∃ t₁ ∈ S, ∃ t₂ ∈ S, OnTreePath T t₁ t₂ a)
    (hb : ∃ t₁ ∈ S, ∃ t₂ ∈ S, OnTreePath T t₁ t₂ b)
    (hc : OnTreePath T a b c) :
    ∃ t₁ ∈ S, ∃ t₂ ∈ S, OnTreePath T t₁ t₂ c := by
  by_cases hca : c = a
  · subst hca; exact ha
  · obtain ⟨p, hp⟩ := hT.connected.exists_isPath c a
    cases p with
    | nil => exact (hca rfl).elim
    | @cons _ w _ hadj q =>
      obtain ⟨hq, hc_not_q⟩ := (Walk.cons_isPath_iff hadj q).1 hp
      have ha_comp : a ∈ treeComp T w s(w, c) :=
        (mem_treeComp_iff_notMem_support hT hadj.symm hq).2 hc_not_q
      have hb_comp : b ∈ treeComp T c s(c, w) := by
        rw [← notMem_treeComp_iff hT hadj.symm]
        intro hb_w
        have hc_w : c ∈ treeComp T w s(w, c) :=
          mem_treeComp_of_onTreePath ha_comp hb_w hc
        exact (notMem_treeComp_iff hT hadj).2 hc_w Reachable.rfl
      obtain ⟨t₁, ht₁S, t₂, ht₂S, ht12⟩ := ha
      obtain ⟨t₃, ht₃S, t₄, ht₄S, ht34⟩ := hb
      obtain ⟨s₁, hs₁S, hs₁_w⟩ : ∃ s₁ ∈ S, s₁ ∈ treeComp T w s(w, c) := by
        rcases mem_treeComp_left_or_right_of_onTreePath hT hadj.symm ha_comp ht12 with h1 | h2
        · exact ⟨t₁, ht₁S, h1⟩
        · exact ⟨t₂, ht₂S, h2⟩
      obtain ⟨s₂, hs₂S, hs₂_c⟩ : ∃ s₂ ∈ S, s₂ ∈ treeComp T c s(c, w) := by
        rcases mem_treeComp_left_or_right_of_onTreePath hT hadj hb_comp ht34 with h3 | h4
        · exact ⟨t₃, ht₃S, h3⟩
        · exact ⟨t₄, ht₄S, h4⟩
      exact ⟨s₂, hs₂S, s₁, hs₁S, onTreePath_of_mem_treeComp hT hadj hs₂_c hs₁_w⟩

/-- If `r ∈ treeComp T u s(u, w)` and `x ∈ treeComp T w s(w, u)` across an edge `T.Adj u w`,
then `T.dist r u < T.dist r x`. -/
theorem dist_lt_of_mem_treeComp {ι : Type*} [DecidableEq ι] {T : SimpleGraph ι} (hT : T.IsTree)
    {r u w x : ι} (hadj : T.Adj u w)
    (hr : r ∈ treeComp T u s(u, w)) (hx : x ∈ treeComp T w s(w, u)) :
    T.dist r u < T.dist r x := by
  obtain ⟨p, hp, hp_len⟩ := (hT.connected r x).exists_path_of_dist
  have hu_mem : u ∈ p.support := onTreePath_of_mem_treeComp hT hadj hr hx hp
  have hux : u ≠ x := by
    rintro rfl
    exact (notMem_treeComp_iff hT hadj).2 hx Reachable.rfl
  have hlt : (p.takeUntil u hu_mem).length < p.length := Walk.length_takeUntil_lt_length hu_mem hux
  have hle : T.dist r u ≤ (p.takeUntil u hu_mem).length := dist_le (p.takeUntil u hu_mem)
  omega

theorem treeComp_split_of_degree_three {t : ℕ} {T : SimpleGraph (Fin t)} [DecidableRel T.Adj]
    (hT : T.IsTree) {u w u₁ u₂ : Fin t} (hadj : T.Adj u w)
    (hw₁ : w ≠ u₁) (hw₂ : w ≠ u₂) (hu12 : u₁ ≠ u₂)
    (hiff : ∀ x, T.Adj u x ↔ x = w ∨ x = u₁ ∨ x = u₂) :
    treeComp T u s(u, w) =
      {u} ∪ treeComp T u₁ s(u₁, u) ∪ treeComp T u₂ s(u₂, u) := by
  have hadj₁ : T.Adj u u₁ := (hiff u₁).2 (Or.inr (Or.inl rfl))
  have hadj₂ : T.Adj u u₂ := (hiff u₂).2 (Or.inr (Or.inr rfl))
  have hmem_sub : ∀ {v : Fin t} (hadj_v : T.Adj u v) (x : Fin t),
      x ∈ treeComp T v s(v, u) ↔
        ∃ (p : T.Walk v x), p.IsPath ∧ u ∉ p.support := by
    intro v hadj_v x
    obtain ⟨p, hp⟩ := hT.connected.exists_isPath v x
    rw [mem_treeComp_iff_notMem_support hT hadj_v.symm hp]
    exact ⟨fun h => ⟨p, hp, h⟩, fun ⟨q, hq, huq⟩ => by
      have hqp : q = p :=
        congrArg Subtype.val ((hT.isAcyclic.subsingleton_path v x).elim ⟨q, hq⟩ ⟨p, hp⟩)
      rwa [← hqp]⟩
  have hsub₁ : treeComp T u₁ s(u₁, u) ⊆ treeComp T u s(u, w) := by
    intro x hx
    obtain ⟨p₁, hp₁, hu_not⟩ := (hmem_sub hadj₁ x).1 hx
    have hp : (Walk.cons hadj₁ p₁).IsPath := (Walk.cons_isPath_iff hadj₁ p₁).2 ⟨hp₁, hu_not⟩
    rw [mem_treeComp_iff_notMem_support hT hadj hp]
    intro hw_mem
    have hwsnd := hT.isAcyclic.eq_snd_of_adj_start hp hadj hw_mem
    simp only [Walk.snd_cons] at hwsnd
    exact hw₁ hwsnd
  have hsub₂ : treeComp T u₂ s(u₂, u) ⊆ treeComp T u s(u, w) := by
    intro x hx
    obtain ⟨p₂, hp₂, hu_not⟩ := (hmem_sub hadj₂ x).1 hx
    have hp : (Walk.cons hadj₂ p₂).IsPath := (Walk.cons_isPath_iff hadj₂ p₂).2 ⟨hp₂, hu_not⟩
    rw [mem_treeComp_iff_notMem_support hT hadj hp]
    intro hw_mem
    have hwsnd := hT.isAcyclic.eq_snd_of_adj_start hp hadj hw_mem
    simp only [Walk.snd_cons] at hwsnd
    exact hw₂ hwsnd
  ext x
  simp only [Set.mem_union, Set.mem_singleton_iff]
  constructor
  · intro hx
    by_cases hxu : x = u
    · exact Or.inl (Or.inl hxu)
    · obtain ⟨p, hp⟩ := hT.connected.exists_isPath u x
      have hw_not : w ∉ p.support := (mem_treeComp_iff_notMem_support hT hadj hp).1 hx
      cases p with
      | nil => exact (hxu rfl).elim
      | @cons _ v _ hadj_v p' =>
        obtain ⟨hp', hu_not_p'⟩ := (Walk.cons_isPath_iff hadj_v p').1 hp
        rcases (hiff v).1 hadj_v with rfl | rfl | rfl
        · exact (hw_not (List.mem_cons_of_mem u p'.start_mem_support)).elim
        · exact Or.inl (Or.inr ((hmem_sub hadj₁ x).2 ⟨p', hp', hu_not_p'⟩))
        · exact Or.inr ((hmem_sub hadj₂ x).2 ⟨p', hp', hu_not_p'⟩)
  · rintro ((rfl | hx₁) | hx₂)
    · exact Reachable.rfl
    · exact hsub₁ hx₁
    · exact hsub₂ hx₂

/-! ### Section 3: GM XIII Lemma (3.2) (page 72) -/

/-- The vertex bag `χ(x) ⊆ Fin n` at node `x : Fin t` associated to a branch-decomposition
`(T, τ)` of `G : SimpleGraph (Fin n)` (GM X Section 5, proof of (5.1), page 169):
all `v : Fin n` such that there exist edges `e₁, e₂ ∈ G.edgeFinset` incident with `v` for which
`x` lies on the path of `T` between `τ e₁` and `τ e₂`. -/
noncomputable def branchBag {n t : ℕ} (G : SimpleGraph (Fin n))
    (T : SimpleGraph (Fin t)) (τ : Sym2 (Fin n) → Fin t) (x : Fin t) : Finset (Fin n) :=
  open Classical in
  Finset.univ.filter fun v : Fin n =>
    ∃ e₁ ∈ G.edgeFinset, ∃ e₂ ∈ G.edgeFinset,
      v ∈ e₁ ∧ v ∈ e₂ ∧ OnTreePath T (τ e₁) (τ e₂) x

@[simp]
theorem mem_branchBag {n t : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (T : SimpleGraph (Fin t)) (τ : Sym2 (Fin n) → Fin t) (x : Fin t) (v : Fin n) :
    v ∈ branchBag G T τ x ↔
      ∃ e₁ ∈ G.edgeFinset, ∃ e₂ ∈ G.edgeFinset,
        v ∈ e₁ ∧ v ∈ e₂ ∧ OnTreePath T (τ e₁) (τ e₂) x := by
  classical
  unfold branchBag
  convert Finset.mem_filter.trans (and_iff_right (Finset.mem_univ v))

theorem adj_mem_branchBag {n t : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
    (T : SimpleGraph (Fin t)) (τ : Sym2 (Fin n) → Fin t)
    {u v : Fin n} (hadj : G.Adj u v) :
    u ∈ branchBag G T τ (τ s(u, v)) ∧ v ∈ branchBag G T τ (τ s(u, v)) := by
  have he : s(u, v) ∈ G.edgeFinset := by rw [mem_edgeFinset, mem_edgeSet]; exact hadj
  refine ⟨?_, ?_⟩ <;> rw [mem_branchBag]
  · exact ⟨s(u, v), he, s(u, v), he, Sym2.mem_mk_left u v, Sym2.mem_mk_left u v,
      onTreePath_refl_left T _ _⟩
  · exact ⟨s(u, v), he, s(u, v), he, Sym2.mem_mk_right u v, Sym2.mem_mk_right u v,
      onTreePath_refl_left T _ _⟩

theorem branchBag_inter_subset_of_onTreePath {n t : ℕ} {G : SimpleGraph (Fin n)}
    [DecidableRel G.Adj] {T : SimpleGraph (Fin t)} (hT : T.IsTree)
    (τ : Sym2 (Fin n) → Fin t) {t₁ t₂ t₃ : Fin t} (hp : OnTreePath T t₁ t₂ t₃) :
    branchBag G T τ t₁ ∩ branchBag G T τ t₂ ⊆ branchBag G T τ t₃ := by
  intro v hv
  rw [Finset.mem_inter, mem_branchBag, mem_branchBag] at hv
  rw [mem_branchBag]
  let S : Set (Fin t) := {x | ∃ e ∈ G.edgeFinset, v ∈ e ∧ τ e = x}
  rcases hv.1 with ⟨e₁, he₁, e₂, he₂, hv₁, hv₂, hp₁⟩
  rcases hv.2 with ⟨e₃, he₃, e₄, he₄, hv₃, hv₄, hp₂⟩
  have hconv := isConvex_exists_onTreePath hT (S := S)
    ⟨τ e₁, ⟨e₁, he₁, hv₁, rfl⟩, τ e₂, ⟨e₂, he₂, hv₂, rfl⟩, hp₁⟩
    ⟨τ e₃, ⟨e₃, he₃, hv₃, rfl⟩, τ e₄, ⟨e₄, he₄, hv₄, rfl⟩, hp₂⟩
    hp
  rcases hconv with ⟨_, ⟨f₁, hf₁, hvf₁, rfl⟩, _, ⟨f₂, hf₂, hvf₂, rfl⟩, hp₃⟩
  exact ⟨f₁, hf₁, f₂, hf₂, hvf₁, hvf₂, hp₃⟩

theorem card_branchBag_le_two_of_mem_treeLeaves {n t B : ℕ}
    {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
    {T : SimpleGraph (Fin t)} [DecidableRel T.Adj]
    {τ : Sym2 (Fin n) → Fin t}
    (hbd : IsBranchDecompOfWidthLe B G T τ)
    {x : Fin t} (hx : x ∈ treeLeaves T) :
    (branchBag G T τ x).card ≤ 2 := by
  have hdeg : T.degree x = 1 := (mem_treeLeaves T x).mp hx
  obtain ⟨w₀, _, hw₀_uniq⟩ := (degree_eq_one_iff_existsUnique_adj (G := T) (v := x)).mp hdeg
  have huniq : ∀ w₁ w₂, T.Adj x w₁ → T.Adj x w₂ → w₁ = w₂ :=
    fun w₁ w₂ h₁ h₂ => (hw₀_uniq w₁ h₁).trans (hw₀_uniq w₂ h₂).symm
  obtain ⟨e₀, he₀, hτe₀⟩ := hbd.2.1.surjOn hx
  have hsub : branchBag G T τ x ⊆ Finset.univ.filter (fun v : Fin n => v ∈ e₀) := by
    intro v hv
    rw [mem_branchBag] at hv
    rcases hv with ⟨e₁, he₁, e₂, he₂, hv₁, hv₂, hp⟩
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    rcases eq_or_eq_of_onTreePath_of_unique_adj hbd.1.1.connected huniq hp with h1 | h2
    · have he₁_eq : e₁ = e₀ := hbd.2.1.injOn he₁ he₀ (h1.symm.trans hτe₀.symm)
      rwa [← he₁_eq]
    · have he₂_eq : e₂ = e₀ := hbd.2.1.injOn he₂ he₀ (h2.symm.trans hτe₀.symm)
      rwa [← he₂_eq]
  exact (Finset.card_le_card hsub).trans (card_incident_edge_le_two e₀)

theorem two_mul_card_branchBag_le_of_notMem_treeLeaves {n t B : ℕ}
    {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
    {T : SimpleGraph (Fin t)} [DecidableRel T.Adj]
    {τ : Sym2 (Fin n) → Fin t}
    (hbd : IsBranchDecompOfWidthLe B G T τ)
    {x : Fin t} (hx : x ∉ treeLeaves T) :
    2 * (branchBag G T τ x).card ≤ 3 * B := by
  have hdeg1 : T.degree x ≠ 1 := fun h => hx ((mem_treeLeaves T x).mpr h)
  have hdeg3 : T.degree x = 3 := (hbd.1.2 x).resolve_left hdeg1
  have hcard3 : (T.neighborFinset x).card = 3 := by
    rw [card_neighborFinset_eq_degree]; exact hdeg3
  obtain ⟨w₁, w₂, w₃, h12, h13, h23, hneigh⟩ := Finset.card_eq_three.mp hcard3
  have hiff : ∀ w, T.Adj x w ↔ w = w₁ ∨ w = w₂ ∨ w = w₃ := by
    intro w
    rw [← mem_neighborFinset, hneigh]
    simp
  have hadj₁ : T.Adj x w₁ := (hiff w₁).2 (Or.inl rfl)
  have hadj₂ : T.Adj x w₂ := (hiff w₂).2 (Or.inr (Or.inl rfl))
  have hadj₃ : T.Adj x w₃ := (hiff w₃).2 (Or.inr (Or.inr rfl))
  let B₁ := treeEdgeCutVerts G T τ s(x, w₁)
  let B₂ := treeEdgeCutVerts G T τ s(x, w₂)
  let B₃ := treeEdgeCutVerts G T τ s(x, w₃)
  have hB₁_le : B₁.card ≤ B := hbd.2.2 s(x, w₁) (by rw [mem_edgeFinset, mem_edgeSet]; exact hadj₁)
  have hB₂_le : B₂.card ≤ B := hbd.2.2 s(x, w₂) (by rw [mem_edgeFinset, mem_edgeSet]; exact hadj₂)
  have hB₃_le : B₃.card ≤ B := hbd.2.2 s(x, w₃) (by rw [mem_edgeFinset, mem_edgeSet]; exact hadj₃)
  have hsplit₁ := treeComp_split_of_degree_three hbd.1.1 hadj₁ h12 h13 h23 hiff
  have hsplit₂ := treeComp_split_of_degree_three hbd.1.1 hadj₂ h12.symm h23 h13
    (fun z => by rw [hiff]; tauto)
  have hsplit₃ := treeComp_split_of_degree_three hbd.1.1 hadj₃ h13.symm h23.symm h12
    (fun z => by rw [hiff]; tauto)
  have hmem_three : ∀ y : Fin t, y ≠ x →
      y ∈ treeComp T w₁ s(w₁, x) ∨ y ∈ treeComp T w₂ s(w₂, x) ∨ y ∈ treeComp T w₃ s(w₃, x) := by
    intro y hyx
    by_cases hy₁ : y ∈ treeComp T w₁ s(w₁, x)
    · exact Or.inl hy₁
    · have hy_in : y ∈ treeComp T x s(x, w₁) := (notMem_treeComp_iff hbd.1.1 hadj₁.symm).1 hy₁
      rw [hsplit₁] at hy_in
      rcases hy_in with (rfl | hy₂) | hy₃
      · exact (hyx rfl).elim
      · exact Or.inr (Or.inl hy₂)
      · exact Or.inr (Or.inr hy₃)
  have hmem_B : ∀ {w : Fin t} (hadj : T.Adj x w) {v : Fin n} {e₁ e₂ : Sym2 (Fin n)},
      e₁ ∈ G.edgeFinset → e₂ ∈ G.edgeFinset → v ∈ e₁ → v ∈ e₂ →
      τ e₁ ∈ treeComp T w s(w, x) → τ e₂ ∈ treeComp T x s(x, w) →
      v ∈ treeEdgeCutVerts G T τ s(x, w) := by
    intro w hadj v e₁ e₂ he₁ he₂ hv₁ hv₂ hc₁ hc₂
    rw [mem_treeEdgeCutVerts]
    refine ⟨e₁, he₁, e₂, he₂, hv₁, hv₂, ?_⟩
    exact (not_reachable_deleteEdges_iff_treeComp hbd.1.1 hadj).2 (Or.inr ⟨hc₁, hc₂⟩)
  have hc₁_in_2 : treeComp T w₁ s(w₁, x) ⊆ treeComp T x s(x, w₂) := by
    rw [hsplit₂]; exact Set.subset_union_of_subset_left Set.subset_union_right _
  have hc₁_in_3 : treeComp T w₁ s(w₁, x) ⊆ treeComp T x s(x, w₃) := by
    rw [hsplit₃]; exact Set.subset_union_of_subset_left Set.subset_union_right _
  have hc₂_in_1 : treeComp T w₂ s(w₂, x) ⊆ treeComp T x s(x, w₁) := by
    rw [hsplit₁]; exact Set.subset_union_of_subset_left Set.subset_union_right _
  have hc₂_in_3 : treeComp T w₂ s(w₂, x) ⊆ treeComp T x s(x, w₃) := by
    rw [hsplit₃]; exact Set.subset_union_right
  have hc₃_in_1 : treeComp T w₃ s(w₃, x) ⊆ treeComp T x s(x, w₁) := by
    rw [hsplit₁]; exact Set.subset_union_right
  have hc₃_in_2 : treeComp T w₃ s(w₃, x) ⊆ treeComp T x s(x, w₂) := by
    rw [hsplit₂]; exact Set.subset_union_right
  have hsub : branchBag G T τ x ⊆ (B₁ ∩ B₂) ∪ (B₁ ∩ B₃) ∪ (B₂ ∩ B₃) := by
    intro v hv
    rw [mem_branchBag] at hv
    simp only [Finset.mem_union, Finset.mem_inter]
    rcases hv with ⟨e₁, he₁, e₂, he₂, hv₁, hv₂, hp⟩
    have ht₁_ne : τ e₁ ≠ x := fun h => hx (h ▸ hbd.2.1.mapsTo he₁)
    have ht₂_ne : τ e₂ ≠ x := fun h => hx (h ▸ hbd.2.1.mapsTo he₂)
    have hnot_same : ∀ {w : Fin t}, T.Adj x w →
        ¬ (τ e₁ ∈ treeComp T w s(w, x) ∧ τ e₂ ∈ treeComp T w s(w, x)) := by
      rintro w hadj ⟨h1, h2⟩
      have hx_mem : x ∈ treeComp T w s(w, x) := mem_treeComp_of_onTreePath h1 h2 hp
      exact (notMem_treeComp_iff hbd.1.1 hadj).2 hx_mem Reachable.rfl
    rcases hmem_three (τ e₁) ht₁_ne with h1_1 | h1_2 | h1_3 <;>
      rcases hmem_three (τ e₂) ht₂_ne with h2_1 | h2_2 | h2_3
    · exact (hnot_same hadj₁ ⟨h1_1, h2_1⟩).elim
    · exact Or.inl (Or.inl ⟨hmem_B hadj₁ he₁ he₂ hv₁ hv₂ h1_1 (hc₂_in_1 h2_2),
        hmem_B hadj₂ he₂ he₁ hv₂ hv₁ h2_2 (hc₁_in_2 h1_1)⟩)
    · exact Or.inl (Or.inr ⟨hmem_B hadj₁ he₁ he₂ hv₁ hv₂ h1_1 (hc₃_in_1 h2_3),
        hmem_B hadj₃ he₂ he₁ hv₂ hv₁ h2_3 (hc₁_in_3 h1_1)⟩)
    · exact Or.inl (Or.inl ⟨hmem_B hadj₁ he₂ he₁ hv₂ hv₁ h2_1 (hc₂_in_1 h1_2),
        hmem_B hadj₂ he₁ he₂ hv₁ hv₂ h1_2 (hc₁_in_2 h2_1)⟩)
    · exact (hnot_same hadj₂ ⟨h1_2, h2_2⟩).elim
    · exact Or.inr ⟨hmem_B hadj₂ he₁ he₂ hv₁ hv₂ h1_2 (hc₃_in_2 h2_3),
        hmem_B hadj₃ he₂ he₁ hv₂ hv₁ h2_3 (hc₂_in_3 h1_2)⟩
    · exact Or.inl (Or.inr ⟨hmem_B hadj₁ he₂ he₁ hv₂ hv₁ h2_1 (hc₃_in_1 h1_3),
        hmem_B hadj₃ he₁ he₂ hv₁ hv₂ h1_3 (hc₁_in_3 h2_1)⟩)
    · exact Or.inr ⟨hmem_B hadj₂ he₂ he₁ hv₂ hv₁ h2_2 (hc₃_in_2 h1_3),
        hmem_B hadj₃ he₁ he₂ hv₁ hv₂ h1_3 (hc₂_in_3 h2_2)⟩
    · exact (hnot_same hadj₃ ⟨h1_3, h2_3⟩).elim
  let U₂ := (B₁ ∩ B₂) ∪ (B₁ ∩ B₃) ∪ (B₂ ∩ B₃)
  have hbag_le : (branchBag G T τ x).card ≤ U₂.card := Finset.card_le_card hsub
  have h12 := Finset.card_union_add_card_inter B₁ B₂
  have h123 := Finset.card_union_add_card_inter (B₁ ∪ B₂) B₃
  rw [Finset.union_inter_distrib_right] at h123
  have hU₂_split := Finset.card_union_add_card_inter (B₁ ∩ B₂) ((B₁ ∩ B₃) ∪ (B₂ ∩ B₃))
  have hU₂_eq : (B₁ ∩ B₂) ∪ ((B₁ ∩ B₃) ∪ (B₂ ∩ B₃)) = U₂ := (Finset.union_assoc _ _ _).symm
  rw [hU₂_eq] at hU₂_split
  have h3_split := Finset.card_union_add_card_inter (B₁ ∩ B₃) (B₂ ∩ B₃)
  have hsub_union : U₂ ⊆ (B₁ ∪ B₂) ∪ B₃ := by
    intro z hz
    simp only [U₂, Finset.mem_union, Finset.mem_inter] at hz ⊢
    rcases hz with (⟨h1, _⟩ | ⟨h1, _⟩) | ⟨h2, _⟩
    · exact Or.inl (Or.inl h1)
    · exact Or.inl (Or.inl h1)
    · exact Or.inl (Or.inr h2)
  have hU₂_le_union : U₂.card ≤ ((B₁ ∪ B₂) ∪ B₃).card := Finset.card_le_card hsub_union
  omega

theorem two_mul_card_branchBag_le {n t B : ℕ}
    {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
    {T : SimpleGraph (Fin t)} [DecidableRel T.Adj]
    {τ : Sym2 (Fin n) → Fin t}
    (hbd : IsBranchDecompOfWidthLe B G T τ) (x : Fin t) :
    2 * (branchBag G T τ x).card ≤ max (3 * B) 4 := by
  by_cases hx : x ∈ treeLeaves T
  · have hle := card_branchBag_le_two_of_mem_treeLeaves hbd hx
    omega
  · have hle := two_mul_card_branchBag_le_of_notMem_treeLeaves hbd hx
    omega

/-- In any nonempty vertex subset `S ⊆ Fin n`, there is a vertex `v ∈ S` whose neighbors in `S`
all lie in `(branchBag G T τ t₀).erase v` for some `t₀ : Fin t` (when `v` has at least one
neighbor in `S`). -/
theorem exists_vertex_neighbors_subset_branchBag {n t B : ℕ}
    {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
    {T : SimpleGraph (Fin t)} [DecidableRel T.Adj]
    {τ : Sym2 (Fin n) → Fin t}
    (hbd : IsBranchDecompOfWidthLe B G T τ)
    {S : Finset (Fin n)} (hS : S.Nonempty) :
    ∃ v ∈ S,
      (S.filter (G.Adj v)) = ∅ ∨
      ∃ t₀ : Fin t, v ∈ branchBag G T τ t₀ ∧ S.filter (G.Adj v) ⊆ (branchBag G T τ t₀).erase v := by
  classical
  by_cases hiso : ∃ v ∈ S, S.filter (G.Adj v) = ∅
  · rcases hiso with ⟨v, hvS, hemp⟩
    exact ⟨v, hvS, Or.inl hemp⟩
  · push Not at hiso
    obtain ⟨r⟩ := hbd.1.1.connected.nonempty
    let active (v : Fin n) : Finset (Fin t) := Finset.univ.filter (fun x => v ∈ branchBag G T τ x)
    have hact_ne : ∀ v ∈ S, (active v).Nonempty := by
      intro v hvS
      obtain ⟨w, hw⟩ := hiso v hvS
      rw [Finset.mem_filter] at hw
      exact ⟨τ s(v, w), Finset.mem_filter.mpr ⟨Finset.mem_univ _,
        (adj_mem_branchBag T τ hw.2).1⟩⟩
    let minDist (v : Fin n) : ℕ :=
      if h : (active v).Nonempty then (active v).inf' h (T.dist r) else 0
    obtain ⟨v, hvS, hv_max⟩ := S.exists_max_image minDist hS
    have hv_ne := hact_ne v hvS
    obtain ⟨t₀, ht₀_act, ht₀_min⟩ := Finset.exists_mem_eq_inf' hv_ne (T.dist r)
    have hmin_v : minDist v = T.dist r t₀ := by
      simp only [minDist, hv_ne, ↓reduceDIte, ht₀_min]
    have hv_t₀ : v ∈ branchBag G T τ t₀ := (Finset.mem_filter.mp ht₀_act).2
    refine ⟨v, hvS, Or.inr ⟨t₀, hv_t₀, ?_⟩⟩
    intro u hu
    rw [Finset.mem_filter] at hu
    rcases hu with ⟨huS, hadj⟩
    rw [Finset.mem_erase]
    refine ⟨hadj.ne.symm, ?_⟩
    have hu_ne := hact_ne u huS
    obtain ⟨t₂, ht₂_act, ht₂_min⟩ := Finset.exists_mem_eq_inf' hu_ne (T.dist r)
    have hmin_u : minDist u = T.dist r t₂ := by
      simp only [minDist, hu_ne, ↓reduceDIte, ht₂_min]
    have hdist_le : T.dist r t₂ ≤ T.dist r t₀ := by
      rw [← hmin_u, ← hmin_v]
      exact hv_max u huS
    have hu_t₂ : u ∈ branchBag G T τ t₂ := (Finset.mem_filter.mp ht₂_act).2
    obtain ⟨t₁, ht₁_eq⟩ : ∃ t₁, τ s(v, u) = t₁ := ⟨_, rfl⟩
    have hvu_t₁ := adj_mem_branchBag T τ hadj
    rw [ht₁_eq] at hvu_t₁
    have hv_t₁ : v ∈ branchBag G T τ t₁ := hvu_t₁.1
    have hu_t₁ : u ∈ branchBag G T τ t₁ := hvu_t₁.2
    suffices hp : OnTreePath T t₁ t₂ t₀ from
      branchBag_inter_subset_of_onTreePath hbd.1.1 τ hp (Finset.mem_inter.mpr ⟨hu_t₁, hu_t₂⟩)
    by_contra hnot_path
    obtain ⟨p, hp⟩ := hbd.1.1.connected.exists_isPath t₁ t₂
    have ht₀_not_p : t₀ ∉ p.support :=
      fun ht₀_p => hnot_path ((onTreePath_iff_of_isPath hbd.1.1 hp).mpr ht₀_p)
    have ht₀_ne_t₁ : t₀ ≠ t₁ := fun h => ht₀_not_p (h ▸ p.start_mem_support)
    obtain ⟨q, hq⟩ := hbd.1.1.connected.exists_isPath t₀ t₁
    cases q with
    | nil => exact (ht₀_ne_t₁ rfl).elim
    | @cons _ w _ hadj_w q' =>
      obtain ⟨hq', ht₀_not_q'⟩ := (Walk.cons_isPath_iff hadj_w q').1 hq
      have hpath_w : OnTreePath T t₀ t₁ w := by
        rw [onTreePath_iff_of_isPath hbd.1.1 ((Walk.cons_isPath_iff hadj_w q').2 ⟨hq', ht₀_not_q'⟩)]
        simp
      have hv_w : v ∈ branchBag G T τ w :=
        branchBag_inter_subset_of_onTreePath hbd.1.1 τ hpath_w (Finset.mem_inter.mpr ⟨hv_t₀, hv_t₁⟩)
      have hw_act : w ∈ active v := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hv_w⟩
      have hdist_w : T.dist r t₀ ≤ T.dist r w := by
        rw [← ht₀_min]
        exact Finset.inf'_le (T.dist r) hw_act
      have hr_comp : r ∈ treeComp T t₀ s(t₀, w) := by
        by_contra hr_not
        have hr_w : r ∈ treeComp T w s(w, t₀) := (notMem_treeComp_iff hbd.1.1 hadj_w).1 hr_not
        have hlt := dist_lt_of_mem_treeComp hbd.1.1 hadj_w.symm hr_w Reachable.rfl
        omega
      have ht₁_w : t₁ ∈ treeComp T w s(w, t₀) :=
        (mem_treeComp_iff_notMem_support hbd.1.1 hadj_w.symm hq').2 ht₀_not_q'
      have hf_not_p : s(w, t₀) ∉ p.edges :=
        fun he => ht₀_not_p (Walk.snd_mem_support_of_mem_edges p he)
      have ht₁_t₂_reach : (T.deleteEdges {s(w, t₀)}).Reachable t₁ t₂ :=
        (p.toDeleteEdge (s(w, t₀)) hf_not_p).reachable
      have ht₂_w : t₂ ∈ treeComp T w s(w, t₀) := ht₁_w.trans ht₁_t₂_reach
      have hlt := dist_lt_of_mem_treeComp hbd.1.1 hadj_w hr_comp ht₂_w
      omega

/-- Edges of `G` with both endpoints in `S : Finset (Fin n)`. -/
def subEdges {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (S : Finset (Fin n)) : Finset (Sym2 (Fin n)) :=
  G.edgeFinset.filter fun e => ∀ x ∈ e, x ∈ S

theorem subEdges_univ {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] :
    subEdges G Finset.univ = G.edgeFinset := by
  ext e
  simp [subEdges]

theorem card_subEdges_erase_add {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    {S : Finset (Fin n)} {v : Fin n} (hv : v ∈ S) :
    (subEdges G S).card = (subEdges G (S.erase v)).card + (S.filter (G.Adj v)).card := by
  have hdisj : Disjoint (subEdges G (S.erase v))
      ((S.filter (G.Adj v)).image (fun u => s(v, u))) := by
    rw [Finset.disjoint_left]
    intro e he₁ he₂
    rw [subEdges, Finset.mem_filter] at he₁
    rw [Finset.mem_image] at he₂
    rcases he₂ with ⟨u, _, rfl⟩
    exact (Finset.mem_erase.mp (he₁.2 v (Sym2.mem_mk_left v u))).1 rfl
  have hunion : subEdges G S =
      subEdges G (S.erase v) ∪ (S.filter (G.Adj v)).image (fun u => s(v, u)) := by
    ext e
    simp only [subEdges, Finset.mem_union, Finset.mem_filter, Finset.mem_erase, Finset.mem_image]
    constructor
    · rintro ⟨heG, heS⟩
      by_cases hve : v ∈ e
      · right
        induction e using Sym2.ind with
        | _ a b =>
          rw [mem_edgeFinset, mem_edgeSet] at heG
          rcases Sym2.mem_iff.mp hve with rfl | rfl
          · exact ⟨b, ⟨heS b (Sym2.mem_mk_right v b), heG⟩, rfl⟩
          · exact ⟨a, ⟨heS a (Sym2.mem_mk_left a v), heG.symm⟩, Sym2.eq_swap⟩
      · left
        exact ⟨heG, fun x hxe => ⟨fun hxv => hve (hxv ▸ hxe), heS x hxe⟩⟩
    · rintro (⟨heG, heS⟩ | ⟨u, ⟨huS, hadj⟩, rfl⟩)
      · exact ⟨heG, fun x hxe => (heS x hxe).2⟩
      · refine ⟨by rw [mem_edgeFinset, mem_edgeSet]; exact hadj, ?_⟩
        intro x hx
        rcases Sym2.mem_iff.mp hx with rfl | rfl
        · exact hv
        · exact huS
  have hinj : Set.InjOn (fun u : Fin n => s(v, u)) (S.filter (G.Adj v)) := by
    intro u₁ _ u₂ _ heq
    rcases Sym2.eq_iff.mp heq with ⟨_, h⟩ | ⟨h1, h2⟩
    · exact h
    · exact h2.trans h1
  rw [hunion, Finset.card_union_of_disjoint hdisj, Finset.card_image_of_injOn hinj]

/-- **GM XIII Lemma (3.2) (page 72)** in natural-number form:
If `ω ≥ 2` and `G : SimpleGraph (Fin n)` has a branch-decomposition `(T, τ)` of width `≤ ω`, then
`2 * G.edgeFinset.card ≤ (3 * ω - 2) * n`. -/
theorem lemma_3_2_nat {n t ω : ℕ} (hω : 2 ≤ ω)
    {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
    {T : SimpleGraph (Fin t)} [DecidableRel T.Adj]
    {τ : Sym2 (Fin n) → Fin t}
    (hbd : IsBranchDecompOfWidthLe ω G T τ) :
    2 * G.edgeFinset.card ≤ (3 * ω - 2) * n := by
  suffices ∀ (k : ℕ) (S : Finset (Fin n)), S.card = k →
      2 * (subEdges G S).card ≤ (3 * ω - 2) * k by
    have h := this n Finset.univ (Finset.card_fin n)
    rwa [subEdges_univ] at h
  intro k
  induction k with
  | zero =>
    intro S hS0
    have hemp : S = ∅ := Finset.card_eq_zero.mp hS0
    subst hemp
    have hsub0 : subEdges G ∅ = ∅ := by
      ext e
      simp only [subEdges, Finset.mem_filter, Finset.notMem_empty, imp_false,
        Finset.notMem_empty, iff_false, not_and]
      intro _
      induction e using Sym2.ind with
      | _ a b =>
        intro hall
        exact hall a (Sym2.mem_mk_left a b)
    simp [hsub0]
  | succ k ih =>
    intro S hSk
    have hSne : S.Nonempty := Finset.card_pos.mp (by omega)
    rcases exists_vertex_neighbors_subset_branchBag hbd hSne with
      ⟨v, hvS, hemp | ⟨t₀, hv_t₀, hsub_bag⟩⟩
    · have hcard_er : (S.erase v).card = k := by
        rw [Finset.card_erase_of_mem hvS, hSk, Nat.add_sub_cancel]
      have hih := ih (S.erase v) hcard_er
      have hstep := card_subEdges_erase_add G hvS
      rw [hemp, Finset.card_empty, add_zero] at hstep
      rw [hstep, Nat.mul_succ (3 * ω - 2) k]
      omega
    · have hcard_er : (S.erase v).card = k := by
        rw [Finset.card_erase_of_mem hvS, hSk, Nat.add_sub_cancel]
      have hih := ih (S.erase v) hcard_er
      have hstep := card_subEdges_erase_add G hvS
      have hdeg_le : (S.filter (G.Adj v)).card ≤ (branchBag G T τ t₀).card - 1 := by
        have h1 := Finset.card_le_card hsub_bag
        rwa [Finset.card_erase_of_mem hv_t₀] at h1
      have hbag_le := two_mul_card_branchBag_le hbd t₀
      have hpos_bag : 1 ≤ (branchBag G T τ t₀).card := Finset.card_pos.mpr ⟨v, hv_t₀⟩
      have hmax : max (3 * ω) 4 = 3 * ω := Nat.max_eq_left (by omega)
      rw [hmax] at hbag_le
      rw [hstep, Nat.mul_add, Nat.mul_succ (3 * ω - 2) k]
      omega

/-- **GM XIII Lemma (3.2) (page 72)**:
"(3.2) Lemma. *If $\omega \ge 2$ is an integer and $G$ is a simple graph with branch-width
$\le \omega$, then $|E(G)| \le (\frac{3}{2}\omega - 1) |V(G)|$.*" -/
theorem lemma_3_2 {n t ω : ℕ} (hω : 2 ≤ ω)
    {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
    {T : SimpleGraph (Fin t)} [DecidableRel T.Adj]
    {τ : Sym2 (Fin n) → Fin t}
    (hbd : IsBranchDecompOfWidthLe ω G T τ) :
    (G.edgeFinset.card : ℚ) ≤ ((3 : ℚ) / 2 * (ω : ℚ) - 1) * (n : ℚ) := by
  have hnat := lemma_3_2_nat hω hbd
  have hq : (2 : ℚ) * (G.edgeFinset.card : ℚ) ≤ ((3 * ω - 2 : ℕ) : ℚ) * (n : ℚ) := by
    exact_mod_cast hnat
  have hsub : ((3 * ω - 2 : ℕ) : ℚ) = 3 * (ω : ℚ) - 2 := by
    rw [Nat.cast_sub (by omega)]
    push_cast
    ring
  rw [hsub] at hq
  linarith

/-! ### Section 4: GM XIII Lemma (3.1) and Step (6) Edge Deletion (pages 71 & 74) -/

/-- Set of vertices of `Fin n` incident with at least one edge in `E : Finset (Sym2 (Fin n))`. -/
def edgeSpanVerts {n : ℕ} (E : Finset (Sym2 (Fin n))) : Finset (Fin n) :=
  Finset.univ.filter fun w : Fin n => ∃ e ∈ E, w ∈ e

@[simp]
theorem mem_edgeSpanVerts {n : ℕ} (E : Finset (Sym2 (Fin n))) (w : Fin n) :
    w ∈ edgeSpanVerts E ↔ ∃ e ∈ E, w ∈ e := by
  simp [edgeSpanVerts]

theorem edgeSpanVerts_empty {n : ℕ} :
    edgeSpanVerts (∅ : Finset (Sym2 (Fin n))) = ∅ := by
  ext w; simp

theorem edgeSpanVerts_union {n : ℕ} (E₁ E₂ : Finset (Sym2 (Fin n))) :
    edgeSpanVerts (E₁ ∪ E₂) = edgeSpanVerts E₁ ∪ edgeSpanVerts E₂ := by
  ext w
  simp only [mem_edgeSpanVerts, Finset.mem_union]
  exact ⟨by rintro ⟨e, he₁ | he₂, hw⟩; exact Or.inl ⟨e, he₁, hw⟩; exact Or.inr ⟨e, he₂, hw⟩,
    by rintro (⟨e, he₁, hw⟩ | ⟨e, he₂, hw⟩); exact ⟨e, Or.inl he₁, hw⟩; exact ⟨e, Or.inr he₂, hw⟩⟩

theorem edgeSpanVerts_subset {n : ℕ} {E₁ E₂ : Finset (Sym2 (Fin n))} (h : E₁ ⊆ E₂) :
    edgeSpanVerts E₁ ⊆ edgeSpanVerts E₂ := by
  intro w hw
  rw [mem_edgeSpanVerts] at hw ⊢
  rcases hw with ⟨e, he, hw⟩
  exact ⟨e, h he, hw⟩

theorem card_edgeSpanVerts_singleton_le_two {n : ℕ} (e : Sym2 (Fin n)) :
    (edgeSpanVerts {e}).card ≤ 2 := by
  have heq : edgeSpanVerts {e} = Finset.univ.filter (fun w : Fin n => w ∈ e) := by
    ext w; simp
  rw [heq]
  exact card_incident_edge_le_two e

/-- The side `E_A` of an edge bipartition `(E_A, E_B)` of `G` has too many vertices of `Z`
(`|Z ∩ V(A)| + |(Z ∩ V(A)) \ V(B)| > 4ω`, corresponding to `(B, A) ∈ 𝒯` in GM XIII (3.1), page 71). -/
def IsBigZSide {n : ℕ} (ω : ℕ) (Z : Finset (Fin n))
    (E_A E_B : Finset (Sym2 (Fin n))) : Prop :=
  4 * ω < (Z ∩ edgeSpanVerts E_A).card + ((Z ∩ edgeSpanVerts E_A) \ edgeSpanVerts E_B).card

/-- If `E_A ⊎ E_B = G.edgeFinset`, `(edgeSpanVerts E_A ∩ edgeSpanVerts E_B).card ≤ ω`, and neither
`(E_A, E_B)` nor `(E_B, E_A)` is `IsBigZSide`, then `G` has a separation `sep : GraphSeparation G`
of order `≤ ω` satisfying `sep.IsBalancedQ Z` (GM XIII (3.1), page 71). -/
theorem exists_balanced_separation_of_not_isBigZSide {n ω : ℕ} (_hω : 1 ≤ ω)
    {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
    {Z : Finset (Fin n)} (hZ : Z.card = 3 * ω)
    {E_A E_B : Finset (Sym2 (Fin n))}
    (hunion : E_A ∪ E_B = G.edgeFinset)
    (hord : (edgeSpanVerts E_A ∩ edgeSpanVerts E_B).card ≤ ω)
    (hnotA : ¬ IsBigZSide ω Z E_A E_B)
    (hnotB : ¬ IsBigZSide ω Z E_B E_A) :
    ∃ sep : GraphSeparation G, sep.order ≤ ω ∧ sep.IsBalancedQ Z := by
  classical
  unfold IsBigZSide at hnotA hnotB
  push Not at hnotA hnotB
  let A := edgeSpanVerts E_A
  let B := edgeSpanVerts E_B
  let C := A ∩ B
  let ZA_only := (Z ∩ A) \ B
  let ZB_only := (Z ∩ B) \ A
  let ZC := Z ∩ C
  let ZI := Z \ (A ∪ B)
  have hZA_eq : (Z ∩ A).card = ZA_only.card + ZC.card := by
    have heq : ZC = (Z ∩ A) ∩ B := by ext x; simp [ZC, C]
    rw [heq]
    exact (Finset.card_sdiff_add_card_inter (Z ∩ A) B).symm
  have hZB_eq : (Z ∩ B).card = ZB_only.card + ZC.card := by
    have heq : ZC = (Z ∩ B) ∩ A := by ext x; simp [ZC, C, and_comm]
    rw [heq]
    exact (Finset.card_sdiff_add_card_inter (Z ∩ B) A).symm
  change (Z ∩ A).card + ZA_only.card ≤ 4 * ω at hnotA
  change (Z ∩ B).card + ZB_only.card ≤ 4 * ω at hnotB
  have h2a : 2 * ZA_only.card + ZC.card ≤ 4 * ω := by omega
  have h2b : 2 * ZB_only.card + ZC.card ≤ 4 * ω := by omega
  have hZC_le : ZC.card ≤ ω :=
    (Finset.card_le_card Finset.inter_subset_right).trans hord
  have hZ_part : ZA_only.card + ZB_only.card + ZC.card + ZI.card = 3 * ω := by
    have hAB_eq : (Z ∩ (A ∪ B)).card = ZA_only.card + ZB_only.card + ZC.card := by
      have hdisj1 : Disjoint ZA_only ZB_only := by
        rw [Finset.disjoint_left]
        intro x hx₁ hx₂
        exact (Finset.mem_sdiff.mp hx₁).2 (Finset.mem_inter.mp (Finset.mem_sdiff.mp hx₂).1).2
      have hdisj2 : Disjoint (ZA_only ∪ ZB_only) ZC := by
        rw [Finset.disjoint_left]
        intro x hx₁ hx₂
        rw [Finset.mem_union] at hx₁
        have hxC := (Finset.mem_inter.mp hx₂).2
        rcases hx₁ with hx₁ | hx₁
        · exact (Finset.mem_sdiff.mp hx₁).2 (Finset.mem_inter.mp hxC).2
        · exact (Finset.mem_sdiff.mp hx₁).2 (Finset.mem_inter.mp hxC).1
      have hunion_ZAB : ZA_only ∪ ZB_only ∪ ZC = Z ∩ (A ∪ B) := by
        ext x
        simp only [ZA_only, ZB_only, ZC, C, Finset.mem_union, Finset.mem_sdiff, Finset.mem_inter]
        tauto
      rw [← hunion_ZAB, Finset.card_union_of_disjoint hdisj2, Finset.card_union_of_disjoint hdisj1]
    have hI : ZI.card + (Z ∩ (A ∪ B)).card = Z.card :=
      Finset.card_sdiff_add_card_inter Z (A ∪ B)
    rw [← hZ, ← hI, hAB_eq]
    omega
  let k₁ := min ZI.card ((4 * ω - ZC.card) / 2 - ZA_only.card)
  obtain ⟨I_A, hI_A_sub, hI_A_card⟩ :=
    Finset.exists_subset_card_eq (s := ZI) (Nat.min_le_left _ _)
  let I_B := ZI \ I_A
  have hI_B_card : I_B.card = ZI.card - k₁ := by
    change (ZI \ I_A).card = ZI.card - k₁
    rw [Finset.card_sdiff_of_subset hI_A_sub, hI_A_card]
  let rest_I := (Finset.univ \ (A ∪ B)) \ Z
  let VA := A ∪ I_A ∪ rest_I
  let VB := B ∪ I_B
  have hI_A_disj_B : Disjoint I_A B := by
    rw [Finset.disjoint_left]
    intro x hxA hxB
    exact (Finset.mem_sdiff.mp (hI_A_sub hxA)).2 (Finset.mem_union_right A hxB)
  have hI_B_disj_A : Disjoint I_B A := by
    rw [Finset.disjoint_left]
    intro x hxB hxA
    exact (Finset.mem_sdiff.mp (Finset.mem_sdiff.mp hxB).1).2 (Finset.mem_union_left B hxA)
  have hrest_disj_B : Disjoint rest_I B := by
    rw [Finset.disjoint_left]
    intro x hxR hxB
    exact (Finset.mem_sdiff.mp (Finset.mem_sdiff.mp hxR).1).2 (Finset.mem_union_right A hxB)
  have hrest_disj_IB : Disjoint rest_I I_B := by
    rw [Finset.disjoint_left]
    intro x hxR hxIB
    exact (Finset.mem_sdiff.mp hxR).2 (Finset.mem_sdiff.mp (Finset.mem_sdiff.mp hxIB).1).1
  have hIA_disj_IB : Disjoint I_A I_B := Finset.disjoint_sdiff
  have hVA_inter_VB : VA ∩ VB = C := by
    ext x
    simp only [VA, VB, C, Finset.mem_inter, Finset.mem_union]
    constructor
    · rintro ⟨(hxA | hxIA) | hxR, hxB | hxIB⟩
      · exact ⟨hxA, hxB⟩
      · exact (Finset.disjoint_left.mp hI_B_disj_A hxIB hxA).elim
      · exact (Finset.disjoint_left.mp hI_A_disj_B hxIA hxB).elim
      · exact (Finset.disjoint_left.mp hIA_disj_IB hxIA hxIB).elim
      · exact (Finset.disjoint_left.mp hrest_disj_B hxR hxB).elim
      · exact (Finset.disjoint_left.mp hrest_disj_IB hxR hxIB).elim
    · rintro ⟨hxA, hxB⟩
      exact ⟨Or.inl (Or.inl hxA), Or.inl hxB⟩
  let EA : SimpleGraph (Fin n) := {
    Adj u v := G.Adj u v ∧ s(u, v) ∈ E_A
    symm := ⟨fun _ _ ⟨h1, h2⟩ => ⟨h1.symm, by rwa [Sym2.eq_swap]⟩⟩
    loopless := ⟨fun u h => G.loopless.irrefl u h.1⟩
  }
  let EB : SimpleGraph (Fin n) := {
    Adj u v := G.Adj u v ∧ s(u, v) ∉ E_A
    symm := ⟨fun _ _ ⟨h1, h2⟩ => ⟨h1.symm, by rwa [Sym2.eq_swap]⟩⟩
    loopless := ⟨fun u h => G.loopless.irrefl u h.1⟩
  }
  let sep : GraphSeparation G := {
    VA := VA
    VB := VB
    EA := EA
    EB := EB
    union_verts := by
      ext x
      simp only [VA, VB, I_B, ZI, rest_I, Finset.mem_union, Finset.mem_sdiff, Finset.mem_univ,
        iff_true]
      by_cases hxA : x ∈ A
      · exact Or.inl (Or.inl (Or.inl hxA))
      · by_cases hxB : x ∈ B
        · exact Or.inr (Or.inl hxB)
        · by_cases hxZ : x ∈ Z
          · by_cases hxIA : x ∈ I_A
            · exact Or.inl (Or.inl (Or.inr hxIA))
            · exact Or.inr (Or.inr ⟨⟨hxZ, by simp [hxA, hxB]⟩, hxIA⟩)
          · exact Or.inl (Or.inr ⟨⟨trivial, by simp [hxA, hxB]⟩, hxZ⟩)
    EA_le := fun _ _ h => h.1
    EB_le := fun _ _ h => h.1
    union_edges := by
      ext u v
      simp only [EA, EB, sup_adj]
      exact ⟨fun h => h.elim (fun h1 => h1.1) (fun h2 => h2.1),
        fun hadj => by by_cases h : s(u, v) ∈ E_A <;> [exact Or.inl ⟨hadj, h⟩; exact Or.inr ⟨hadj, h⟩]⟩
    disj_edges := by
      ext u v
      simp only [EA, EB, inf_adj, bot_adj]
      exact ⟨fun ⟨h1, h2⟩ => h2.2 h1.2, False.elim⟩
    EA_verts := by
      intro u v ⟨_, heA⟩
      have huA : u ∈ A := (mem_edgeSpanVerts E_A u).mpr ⟨s(u, v), heA, Sym2.mem_mk_left u v⟩
      have hvA : v ∈ A := (mem_edgeSpanVerts E_A v).mpr ⟨s(u, v), heA, Sym2.mem_mk_right u v⟩
      exact ⟨Finset.mem_union_left _ (Finset.mem_union_left _ huA),
        Finset.mem_union_left _ (Finset.mem_union_left _ hvA)⟩
    EB_verts := by
      intro u v ⟨hadj, hnotEA⟩
      have he : s(u, v) ∈ G.edgeFinset := by rw [mem_edgeFinset, mem_edgeSet]; exact hadj
      rw [← hunion, Finset.mem_union] at he
      have heB : s(u, v) ∈ E_B := he.resolve_left hnotEA
      have huB : u ∈ B := (mem_edgeSpanVerts E_B u).mpr ⟨s(u, v), heB, Sym2.mem_mk_left u v⟩
      have hvB : v ∈ B := (mem_edgeSpanVerts E_B v).mpr ⟨s(u, v), heB, Sym2.mem_mk_right u v⟩
      exact ⟨Finset.mem_union_left _ huB, Finset.mem_union_left _ hvB⟩
  }
  refine ⟨sep, ?_, ?_⟩
  · unfold GraphSeparation.order
    change (VA ∩ VB).card ≤ ω
    rw [hVA_inter_VB]
    exact hord
  · rw [sep.isBalancedQ_iff_isBalancedNat]
    have hZ_sdiff_VA : Z \ VA = ZB_only ∪ I_B := by
      ext x
      simp only [VA, ZB_only, I_B, ZI, rest_I, Finset.mem_sdiff, Finset.mem_union,
        Finset.mem_inter]
      constructor
      · rintro ⟨hxZ, hnotVA⟩
        by_cases hxB : x ∈ B
        · exact Or.inl ⟨⟨hxZ, hxB⟩, fun hxA => hnotVA (Or.inl (Or.inl hxA))⟩
        · exact Or.inr ⟨⟨hxZ, fun hxAB => by
            rcases hxAB with hxA | hxB'
            · exact hnotVA (Or.inl (Or.inl hxA))
            · exact hxB hxB'⟩, fun hxIA => hnotVA (Or.inl (Or.inr hxIA))⟩
      · rintro (⟨⟨hxZ, hxB⟩, hxnotA⟩ | ⟨⟨hxZ, hxnotAB⟩, hxnotIA⟩)
        · refine ⟨hxZ, ?_⟩
          rintro ((hxA | hxIA) | ⟨_, hxnotZ⟩)
          · exact hxnotA hxA
          · exact Finset.disjoint_left.mp hI_A_disj_B hxIA hxB
          · exact hxnotZ hxZ
        · refine ⟨hxZ, ?_⟩
          rintro ((hxA | hxIA) | ⟨_, hxnotZ⟩)
          · exact hxnotAB (Or.inl hxA)
          · exact hxnotIA hxIA
          · exact hxnotZ hxZ
    have hZ_sdiff_VB : Z \ VB = ZA_only ∪ I_A := by
      ext x
      simp only [VB, ZA_only, I_B, ZI, Finset.mem_sdiff, Finset.mem_union, Finset.mem_inter]
      constructor
      · rintro ⟨hxZ, hnotVB⟩
        by_cases hxA : x ∈ A
        · exact Or.inl ⟨⟨hxZ, hxA⟩, fun hxB => hnotVB (Or.inl hxB)⟩
        · right
          by_contra hxnotIA
          have hxB : x ∉ B := fun h => hnotVB (Or.inl h)
          exact hnotVB (Or.inr ⟨⟨hxZ, by simp [hxA, hxB]⟩, hxnotIA⟩)
      · rintro (⟨⟨hxZ, hxA⟩, hxnotB⟩ | hxIA)
        · refine ⟨hxZ, ?_⟩
          rintro (hxB | ⟨⟨_, hxnotAB⟩, _⟩)
          · exact hxnotB hxB
          · exact hxnotAB (Or.inl hxA)
        · have hxZI := hI_A_sub hxIA
          rw [Finset.mem_sdiff] at hxZI
          refine ⟨hxZI.1, ?_⟩
          rintro (hxB | ⟨_, hxnotIA⟩)
          · exact hxZI.2 (Finset.mem_union_right A hxB)
          · exact hxnotIA hxIA
    have hdisj_ZB_IB : Disjoint ZB_only I_B := by
      rw [Finset.disjoint_left]
      intro x hxZB hxIB
      exact (Finset.mem_sdiff.mp (Finset.mem_sdiff.mp hxIB).1).2
        (Finset.mem_union_right A (Finset.mem_inter.mp (Finset.mem_sdiff.mp hxZB).1).2)
    have hdisj_ZA_IA : Disjoint ZA_only I_A := by
      rw [Finset.disjoint_left]
      intro x hxZA hxIA
      exact (Finset.mem_sdiff.mp (hI_A_sub hxIA)).2
        (Finset.mem_union_left B (Finset.mem_inter.mp (Finset.mem_sdiff.mp hxZA).1).2)
    have hcard_Z_VA : (Z \ sep.VA).card = ZB_only.card + (ZI.card - k₁) := by
      change (Z \ VA).card = _
      rw [hZ_sdiff_VA, Finset.card_union_of_disjoint hdisj_ZB_IB, hI_B_card]
    have hcard_Z_VB : (Z \ sep.VB).card = ZA_only.card + k₁ := by
      change (Z \ VB).card = _
      rw [hZ_sdiff_VB, Finset.card_union_of_disjoint hdisj_ZA_IA, hI_A_card]
    have hcard_ZC : (Z ∩ (sep.VA ∩ sep.VB)).card = ZC.card := by
      change (Z ∩ (VA ∩ VB)).card = ZC.card
      rw [hVA_inter_VB]
    unfold GraphSeparation.IsBalancedNat
    rw [hcard_Z_VA, hcard_Z_VB, hcard_ZC, hZ]
    dsimp [k₁]
    omega

theorem card_eq_sum_ite_of_subset {α : Type*} [DecidableEq α] (Z S : Finset α)
    (hsub : S ⊆ Z) :
    S.card = ∑ z ∈ Z, if z ∈ S then 1 else 0 := by
  rw [Finset.card_eq_sum_ones, ← Finset.sum_filter]
  congr 1
  ext z
  simp only [Finset.mem_filter]
  exact ⟨fun h => ⟨hsub h, h⟩, fun h => h.2⟩

/-- Opposite sides `(E_A, E_B)` and `(E_B, E_A)` cannot both be `IsBigZSide` when `|Z| = 3ω` and
`1 ≤ ω` (GM XIII (3.1) (1)(ii), page 71). -/
theorem not_isBigZSide_both {n ω : ℕ} (_hω : 1 ≤ ω)
    {Z : Finset (Fin n)} (hZ : Z.card = 3 * ω)
    (E_A E_B : Finset (Sym2 (Fin n))) :
    ¬ (IsBigZSide ω Z E_A E_B ∧ IsBigZSide ω Z E_B E_A) := by
  rintro ⟨hA, hB⟩
  unfold IsBigZSide at hA hB
  let A := edgeSpanVerts E_A
  let B := edgeSpanVerts E_B
  change 4 * ω < (Z ∩ A).card + ((Z ∩ A) \ B).card at hA
  change 4 * ω < (Z ∩ B).card + ((Z ∩ B) \ A).card at hB
  have h1 := card_eq_sum_ite_of_subset Z (Z ∩ A) Finset.inter_subset_left
  have h2 := card_eq_sum_ite_of_subset Z ((Z ∩ A) \ B)
    (Finset.sdiff_subset.trans Finset.inter_subset_left)
  have h3 := card_eq_sum_ite_of_subset Z (Z ∩ B) Finset.inter_subset_left
  have h4 := card_eq_sum_ite_of_subset Z ((Z ∩ B) \ A)
    (Finset.sdiff_subset.trans Finset.inter_subset_left)
  have hsum : (Z ∩ A).card + ((Z ∩ A) \ B).card + ((Z ∩ B).card + ((Z ∩ B) \ A).card) ≤
      2 * Z.card := by
    rw [h1, h2, h3, h4, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib,
      ← Finset.sum_add_distrib]
    have hle : (∑ z ∈ Z, ((if z ∈ Z ∩ A then 1 else 0) + (if z ∈ (Z ∩ A) \ B then 1 else 0) +
        ((if z ∈ Z ∩ B then 1 else 0) + (if z ∈ (Z ∩ B) \ A then 1 else 0)))) ≤ ∑ _z ∈ Z, 2 := by
      apply Finset.sum_le_sum
      intro z hz
      by_cases hza : z ∈ A <;> by_cases hzb : z ∈ B <;> simp [hz, hza, hzb]
    simpa [mul_comm] using hle
  omega

/-- At a degree-3 tree node partitioning `E(G)` into `E₁, E₂, E₃`, not all three pairs
`(E₂ ∪ E₃, E₁)`, `(E₁ ∪ E₃, E₂)`, `(E₁ ∪ E₂, E₃)` can be `IsBigZSide` when `|Z| = 3ω`
(GM XIII (3.1) (1)(iii), page 71). -/
theorem not_isBigZSide_three {n ω : ℕ}
    {Z : Finset (Fin n)} (hZ : Z.card = 3 * ω)
    (E₁ E₂ E₃ : Finset (Sym2 (Fin n))) :
    ¬ (IsBigZSide ω Z (E₂ ∪ E₃) E₁ ∧
       IsBigZSide ω Z (E₁ ∪ E₃) E₂ ∧
       IsBigZSide ω Z (E₁ ∪ E₂) E₃) := by
  rintro ⟨h1, h2, h3⟩
  unfold IsBigZSide at h1 h2 h3
  rw [edgeSpanVerts_union] at h1 h2 h3
  let A₁ := edgeSpanVerts E₁
  let A₂ := edgeSpanVerts E₂
  let A₃ := edgeSpanVerts E₃
  change 4 * ω < (Z ∩ (A₂ ∪ A₃)).card + ((Z ∩ (A₂ ∪ A₃)) \ A₁).card at h1
  change 4 * ω < (Z ∩ (A₁ ∪ A₃)).card + ((Z ∩ (A₁ ∪ A₃)) \ A₂).card at h2
  change 4 * ω < (Z ∩ (A₁ ∪ A₂)).card + ((Z ∩ (A₁ ∪ A₂)) \ A₃).card at h3
  have hs1 := card_eq_sum_ite_of_subset Z (Z ∩ (A₂ ∪ A₃)) Finset.inter_subset_left
  have hd1 := card_eq_sum_ite_of_subset Z ((Z ∩ (A₂ ∪ A₃)) \ A₁)
    (Finset.sdiff_subset.trans Finset.inter_subset_left)
  have hs2 := card_eq_sum_ite_of_subset Z (Z ∩ (A₁ ∪ A₃)) Finset.inter_subset_left
  have hd2 := card_eq_sum_ite_of_subset Z ((Z ∩ (A₁ ∪ A₃)) \ A₂)
    (Finset.sdiff_subset.trans Finset.inter_subset_left)
  have hs3 := card_eq_sum_ite_of_subset Z (Z ∩ (A₁ ∪ A₂)) Finset.inter_subset_left
  have hd3 := card_eq_sum_ite_of_subset Z ((Z ∩ (A₁ ∪ A₂)) \ A₃)
    (Finset.sdiff_subset.trans Finset.inter_subset_left)
  have hsum :
      (Z ∩ (A₂ ∪ A₃)).card + ((Z ∩ (A₂ ∪ A₃)) \ A₁).card +
      ((Z ∩ (A₁ ∪ A₃)).card + ((Z ∩ (A₁ ∪ A₃)) \ A₂).card) +
      ((Z ∩ (A₁ ∪ A₂)).card + ((Z ∩ (A₁ ∪ A₂)) \ A₃).card) ≤ 4 * Z.card := by
    rw [hs1, hd1, hs2, hd2, hs3, hd3, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib,
      ← Finset.sum_add_distrib, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    have hle : (∑ z ∈ Z,
        (((if z ∈ Z ∩ (A₂ ∪ A₃) then 1 else 0) +
          (if z ∈ (Z ∩ (A₂ ∪ A₃)) \ A₁ then 1 else 0)) +
         ((if z ∈ Z ∩ (A₁ ∪ A₃) then 1 else 0) +
          (if z ∈ (Z ∩ (A₁ ∪ A₃)) \ A₂ then 1 else 0)) +
         ((if z ∈ Z ∩ (A₁ ∪ A₂) then 1 else 0) +
          (if z ∈ (Z ∩ (A₁ ∪ A₂)) \ A₃ then 1 else 0)))) ≤ ∑ _z ∈ Z, 4 := by
      apply Finset.sum_le_sum
      intro z hz
      by_cases hz1 : z ∈ A₁ <;> by_cases hz2 : z ∈ A₂ <;> by_cases hz3 : z ∈ A₃ <;>
        simp [hz, hz1, hz2, hz3]
    simpa [mul_comm] using hle
  omega

/-- If `E_A ⊆ {e₁, e₂}` has at most 2 edges and `2 ≤ ω`, then `(E_A, E_B)` is not `IsBigZSide`
(since `|edgeSpanVerts E_A| ≤ 4` and `4 + 4 = 8 ≤ 4ω`). -/
theorem not_isBigZSide_of_subset_pair {n ω : ℕ} (hω : 2 ≤ ω)
    (Z : Finset (Fin n)) {E_A E_B : Finset (Sym2 (Fin n))} (e₁ e₂ : Sym2 (Fin n))
    (hsub : E_A ⊆ {e₁, e₂}) :
    ¬ IsBigZSide ω Z E_A E_B := by
  unfold IsBigZSide
  have hspan : edgeSpanVerts E_A ⊆ edgeSpanVerts {e₁} ∪ edgeSpanVerts {e₂} := by
    rw [← edgeSpanVerts_union]
    apply edgeSpanVerts_subset
    intro e he
    simpa using hsub he
  have hcardA : (edgeSpanVerts E_A).card ≤ 4 := by
    have h1 := (Finset.card_le_card hspan).trans
      (Finset.card_union_le (edgeSpanVerts {e₁}) (edgeSpanVerts {e₂}))
    have h2 := card_edgeSpanVerts_singleton_le_two e₁
    have h3 := card_edgeSpanVerts_singleton_le_two e₂
    omega
  have hc1 : (Z ∩ edgeSpanVerts E_A).card ≤ (edgeSpanVerts E_A).card :=
    Finset.card_le_card Finset.inter_subset_right
  have hc2 : ((Z ∩ edgeSpanVerts E_A) \ edgeSpanVerts E_B).card ≤ (edgeSpanVerts E_A).card :=
    Finset.card_le_card (Finset.sdiff_subset.trans Finset.inter_subset_right)
  omega

/-- In Case 2 of `IsAlg33HighWidthCase` (where `G_step6` has no separation of order `≤ ω` balanced
on `Z` with `|Z| = 3ω` and `G' = G_step6.deleteEdges {g}`), `G'` has `≥ 2` edges. -/
theorem two_le_card_edgeFinset_of_step6 {n ω : ℕ} (hω : 2 ≤ ω)
    {G_step6 : SimpleGraph (Fin n)} [DecidableRel G_step6.Adj]
    {g : Sym2 (Fin n)} (hg : g ∈ G_step6.edgeFinset)
    {Z : Finset (Fin n)} (hZ : Z.card = 3 * ω)
    (hno_sep : ∀ sep : GraphSeparation G_step6, sep.order ≤ ω → ¬ sep.IsBalancedQ Z) :
    2 ≤ (G_step6.deleteEdges {g}).edgeFinset.card := by
  classical
  by_contra hlt
  have hle1 : (G_step6.deleteEdges {g}).edgeFinset.card ≤ 1 := by omega
  let E_A : Finset (Sym2 (Fin n)) := {g}
  let E_B : Finset (Sym2 (Fin n)) := (G_step6.deleteEdges {g}).edgeFinset
  have hunion : E_A ∪ E_B = G_step6.edgeFinset := by
    ext e
    simp only [E_A, E_B, Finset.mem_union, Finset.mem_singleton, mem_edgeFinset,
      edgeSet_deleteEdges, Set.mem_sdiff, Set.mem_singleton_iff]
    constructor
    · rintro (rfl | ⟨he, _⟩)
      · exact mem_edgeFinset.mp hg
      · exact he
    · intro he
      by_cases heg : e = g
      · exact Or.inl heg
      · exact Or.inr ⟨he, heg⟩
  have hcardA : (edgeSpanVerts E_A).card ≤ 2 := card_edgeSpanVerts_singleton_le_two g
  have hord : (edgeSpanVerts E_A ∩ edgeSpanVerts E_B).card ≤ ω := by
    have hsub : (edgeSpanVerts E_A ∩ edgeSpanVerts E_B).card ≤ (edgeSpanVerts E_A).card :=
      Finset.card_le_card Finset.inter_subset_left
    omega
  have hnotA : ¬ IsBigZSide ω Z E_A E_B :=
    not_isBigZSide_of_subset_pair hω Z g g (by intro e he; simp [E_A] at he; simp [he])
  have hnotB : ¬ IsBigZSide ω Z E_B E_A := by
    have hsubB := Finset.card_le_one.mp hle1
    by_cases hneB : E_B.Nonempty
    · obtain ⟨e₀, he₀⟩ := hneB
      exact not_isBigZSide_of_subset_pair hω Z e₀ e₀ (by
        intro e he
        rw [Finset.mem_insert, Finset.mem_singleton]
        exact Or.inl (hsubB e he e₀ he₀))
    · rw [Finset.not_nonempty_iff_eq_empty] at hneB
      exact not_isBigZSide_of_subset_pair hω Z g g (by rw [hneB]; exact Finset.empty_subset _)
  obtain ⟨sep, hsep_ord, hsep_bal⟩ :=
    exists_balanced_separation_of_not_isBigZSide (by omega) hZ hunion hord hnotA hnotB
  exact hno_sep sep hsep_ord hsep_bal

/-- Edges of `G_step6` mapped by `τ'` into `treeComp T u s(u, w)`. -/
noncomputable def compEdges {n t : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (T : SimpleGraph (Fin t)) (τ' : Sym2 (Fin n) → Fin t) (u w : Fin t) :
    Finset (Sym2 (Fin n)) :=
  open Classical in
  G.edgeFinset.filter fun e => τ' e ∈ treeComp T u s(u, w)

@[simp]
theorem mem_compEdges {n t : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (T : SimpleGraph (Fin t)) (τ' : Sym2 (Fin n) → Fin t) (u w : Fin t) (e : Sym2 (Fin n)) :
    e ∈ compEdges G T τ' u w ↔ e ∈ G.edgeFinset ∧ τ' e ∈ treeComp T u s(u, w) := by
  classical
  unfold compEdges
  exact Finset.mem_filter

/-- **GM XIII Lemma (3.1) + Step (6) Soundness (pages 71 & 74)**:
If `ω ≥ 2`, `g ∈ G_step6.edgeFinset`, `Z.card = 3 * ω`, and `G_step6` has no separation of order
`≤ ω` balanced on `Z`, then `G_step6.deleteEdges {g}` has no branch-decomposition of width
`≤ ω - 1`. -/
theorem no_branch_decomp_of_step6 {n t ω : ℕ} (hω : 2 ≤ ω)
    {G_step6 : SimpleGraph (Fin n)} [DecidableRel G_step6.Adj]
    {g : Sym2 (Fin n)} (hg : g ∈ G_step6.edgeFinset)
    {Z : Finset (Fin n)} (hZ : Z.card = 3 * ω)
    (hno_sep : ∀ sep : GraphSeparation G_step6, sep.order ≤ ω → ¬ sep.IsBalancedQ Z)
    {T : SimpleGraph (Fin t)} [DecidableRel T.Adj]
    {τ : Sym2 (Fin n) → Fin t}
    (hbd : IsBranchDecompOfWidthLe (ω - 1) (G_step6.deleteEdges {g}) T τ) :
    False := by
  classical
  let G' := G_step6.deleteEdges {g}
  have h2_edges : 2 ≤ G'.edgeFinset.card :=
    two_le_card_edgeFinset_of_step6 hω hg hZ hno_sep
  have hG'_ne : G'.edgeFinset.Nonempty := Finset.card_pos.mp (by omega)
  -- Choose `e₀ ∈ G'.edgeFinset` sharing an endpoint with `g` if possible, else any edge of `G'`.
  have hex_e₀ : ∃ e₀ ∈ G'.edgeFinset,
      (∃ x₀ : Fin n, x₀ ∈ g ∧ x₀ ∈ e₀) ∨
      (∀ e ∈ G'.edgeFinset, ∀ x : Fin n, ¬ (x ∈ g ∧ x ∈ e)) := by
    by_cases hshare : ∃ e₀ ∈ G'.edgeFinset, ∃ x₀ : Fin n, x₀ ∈ g ∧ x₀ ∈ e₀
    · rcases hshare with ⟨e₀, he₀, x₀, hx₀⟩
      exact ⟨e₀, he₀, Or.inl ⟨x₀, hx₀⟩⟩
    · obtain ⟨e₀, he₀⟩ := hG'_ne
      exact ⟨e₀, he₀, Or.inr fun e he x hx => hshare ⟨e, he, x, hx⟩⟩
  rcases hex_e₀ with ⟨e₀, he₀_G', hcase_e₀⟩
  let τ' (e : Sym2 (Fin n)) : Fin t := if e = g then τ e₀ else τ e
  have hτ'_eq_of_mem_G' : ∀ {e : Sym2 (Fin n)}, e ∈ G'.edgeFinset → τ' e = τ e := by
    intro e he
    have heg : e ≠ g := by
      rw [mem_edgeFinset, edgeSet_deleteEdges, Set.mem_sdiff, Set.mem_singleton_iff] at he
      exact he.2
    simp [τ', heg]
  have hτ'_leaves : ∀ e ∈ G_step6.edgeFinset, τ' e ∈ treeLeaves T := by
    intro e he
    by_cases heg : e = g
    · simp only [τ', heg, ↓reduceIte]
      exact hbd.2.1.mapsTo he₀_G'
    · have he_G' : e ∈ G'.edgeFinset := by
        rw [mem_edgeFinset, edgeSet_deleteEdges, Set.mem_sdiff, Set.mem_singleton_iff]
        exact ⟨mem_edgeFinset.mp he, heg⟩
      rw [hτ'_eq_of_mem_G' he_G']
      exact hbd.2.1.mapsTo he_G'
  -- Every tree edge `f ∈ T.edgeFinset` has `treeEdgeOrder G_step6 T τ' f ≤ ω`.
  have hord_step6 : ∀ f ∈ T.edgeFinset, treeEdgeOrder G_step6 T τ' f ≤ ω := by
    intro f hf
    have hord_G' : treeEdgeOrder G' T τ f ≤ ω - 1 := hbd.2.2 f hf
    rcases hcase_e₀ with ⟨x₀, hx₀_g, hx₀_e₀⟩ | hdisj_g
    · obtain ⟨y₀, hg_eq⟩ : ∃ y₀ : Fin n, g = s(x₀, y₀) := by
        induction g using Sym2.ind with
        | _ a b =>
          rcases Sym2.mem_iff.mp hx₀_g with rfl | rfl
          · exact ⟨b, rfl⟩
          · exact ⟨a, Sym2.eq_swap⟩
      have hsub : treeEdgeCutVerts G_step6 T τ' f ⊆ insert y₀ (treeEdgeCutVerts G' T τ f) := by
        intro w hw
        rw [Finset.mem_insert]
        by_cases hwy : w = y₀
        · exact Or.inl hwy
        · right
          rw [mem_treeEdgeCutVerts] at hw ⊢
          rcases hw with ⟨e₁, he₁, e₂, he₂, hw₁, hw₂, hnr⟩
          let e₁' := if e₁ = g then e₀ else e₁
          let e₂' := if e₂ = g then e₀ else e₂
          have he₁'_G' : e₁' ∈ G'.edgeFinset := by
            dsimp [e₁']
            split_ifs with h1
            · exact he₀_G'
            · rw [mem_edgeFinset, edgeSet_deleteEdges, Set.mem_sdiff, Set.mem_singleton_iff]
              exact ⟨mem_edgeFinset.mp he₁, h1⟩
          have he₂'_G' : e₂' ∈ G'.edgeFinset := by
            dsimp [e₂']
            split_ifs with h2
            · exact he₀_G'
            · rw [mem_edgeFinset, edgeSet_deleteEdges, Set.mem_sdiff, Set.mem_singleton_iff]
              exact ⟨mem_edgeFinset.mp he₂, h2⟩
          have hw₁' : w ∈ e₁' := by
            dsimp [e₁']
            split_ifs with h1
            · rw [h1, hg_eq, Sym2.mem_iff] at hw₁
              rcases hw₁ with rfl | rfl
              · exact hx₀_e₀
              · exact (hwy rfl).elim
            · exact hw₁
          have hw₂' : w ∈ e₂' := by
            dsimp [e₂']
            split_ifs with h2
            · rw [h2, hg_eq, Sym2.mem_iff] at hw₂
              rcases hw₂ with rfl | rfl
              · exact hx₀_e₀
              · exact (hwy rfl).elim
            · exact hw₂
          have hτ₁ : τ e₁' = τ' e₁ := by dsimp [e₁', τ']; split_ifs <;> rfl
          have hτ₂ : τ e₂' = τ' e₂ := by dsimp [e₂', τ']; split_ifs <;> rfl
          rw [← hτ₁, ← hτ₂] at hnr
          exact ⟨e₁', he₁'_G', e₂', he₂'_G', hw₁', hw₂', hnr⟩
      unfold treeEdgeOrder at hord_G' ⊢
      have hcard := (Finset.card_le_card hsub).trans
        (Finset.card_insert_le y₀ (treeEdgeCutVerts G' T τ f))
      omega
    · have hsub : treeEdgeCutVerts G_step6 T τ' f ⊆ treeEdgeCutVerts G' T τ f := by
        intro w hw
        rw [mem_treeEdgeCutVerts] at hw ⊢
        rcases hw with ⟨e₁, he₁, e₂, he₂, hw₁, hw₂, hnr⟩
        have hne12 : e₁ ≠ e₂ := fun h => hnr (h ▸ Reachable.rfl)
        have hnot_g : w ∉ g := by
          by_cases h1 : e₁ = g
          · have he₂_G' : e₂ ∈ G'.edgeFinset := by
              rw [mem_edgeFinset, edgeSet_deleteEdges, Set.mem_sdiff, Set.mem_singleton_iff]
              exact ⟨mem_edgeFinset.mp he₂, fun h2 => hne12 (h1.trans h2.symm)⟩
            exact fun hwg => hdisj_g e₂ he₂_G' w ⟨hwg, hw₂⟩
          · have he₁_G' : e₁ ∈ G'.edgeFinset := by
              rw [mem_edgeFinset, edgeSet_deleteEdges, Set.mem_sdiff, Set.mem_singleton_iff]
              exact ⟨mem_edgeFinset.mp he₁, h1⟩
            exact fun hwg => hdisj_g e₁ he₁_G' w ⟨hwg, hw₁⟩
        have he₁_G' : e₁ ∈ G'.edgeFinset := by
          rw [mem_edgeFinset, edgeSet_deleteEdges, Set.mem_sdiff, Set.mem_singleton_iff]
          exact ⟨mem_edgeFinset.mp he₁, fun h => hnot_g (h ▸ hw₁)⟩
        have he₂_G' : e₂ ∈ G'.edgeFinset := by
          rw [mem_edgeFinset, edgeSet_deleteEdges, Set.mem_sdiff, Set.mem_singleton_iff]
          exact ⟨mem_edgeFinset.mp he₂, fun h => hnot_g (h ▸ hw₂)⟩
        rw [hτ'_eq_of_mem_G' he₁_G', hτ'_eq_of_mem_G' he₂_G'] at hnr
        exact ⟨e₁, he₁_G', e₂, he₂_G', hw₁, hw₂, hnr⟩
      unfold treeEdgeOrder at hord_G' ⊢
      have hcard := Finset.card_le_card hsub
      omega
  -- Orient each adjacent pair `(u, w)` of `T` when the `w`-side is `IsBigZSide`.
  let orient (u w : Fin t) : Prop :=
    T.Adj u w ∧ IsBigZSide ω Z (compEdges G_step6 T τ' w u) (compEdges G_step6 T τ' u w)
  have horient_or : ∀ {u w : Fin t}, T.Adj u w → orient u w ∨ orient w u := by
    intro u w hadj
    by_contra! hnot
    have hnot_w : ¬ IsBigZSide ω Z (compEdges G_step6 T τ' w u) (compEdges G_step6 T τ' u w) :=
      fun h => hnot.1 ⟨hadj, h⟩
    have hnot_u : ¬ IsBigZSide ω Z (compEdges G_step6 T τ' u w) (compEdges G_step6 T τ' w u) :=
      fun h => hnot.2 ⟨hadj.symm, h⟩
    have hunion : compEdges G_step6 T τ' u w ∪ compEdges G_step6 T τ' w u = G_step6.edgeFinset := by
      ext e
      simp only [Finset.mem_union, mem_compEdges]
      refine ⟨by rintro (⟨he, _⟩ | ⟨he, _⟩) <;> exact he, fun he => ?_⟩
      by_cases h : τ' e ∈ treeComp T u s(u, w)
      · exact Or.inl ⟨he, h⟩
      · exact Or.inr ⟨he, (notMem_treeComp_iff hbd.1.1 hadj).1 h⟩
    have hinter_sub : edgeSpanVerts (compEdges G_step6 T τ' u w) ∩
        edgeSpanVerts (compEdges G_step6 T τ' w u) ⊆
        treeEdgeCutVerts G_step6 T τ' s(u, w) := by
      intro v hv
      rw [Finset.mem_inter, mem_edgeSpanVerts, mem_edgeSpanVerts] at hv
      rcases hv with ⟨⟨e₁, he₁, hv₁⟩, ⟨e₂, he₂, hv₂⟩⟩
      rw [mem_compEdges] at he₁ he₂
      rw [mem_treeEdgeCutVerts]
      exact ⟨e₁, he₁.1, e₂, he₂.1, hv₁, hv₂,
        (not_reachable_deleteEdges_iff_treeComp hbd.1.1 hadj).2 (Or.inl ⟨he₁.2, he₂.2⟩)⟩
    have hf_mem : s(u, w) ∈ T.edgeFinset := by rw [mem_edgeFinset, mem_edgeSet]; exact hadj
    have hord_uw :
        (edgeSpanVerts (compEdges G_step6 T τ' u w) ∩
         edgeSpanVerts (compEdges G_step6 T τ' w u)).card ≤ ω :=
      (Finset.card_le_card hinter_sub).trans (hord_step6 s(u, w) hf_mem)
    obtain ⟨sep, hsep_ord, hsep_bal⟩ :=
      exists_balanced_separation_of_not_isBigZSide (by omega) hZ hunion hord_uw hnot_u hnot_w
    exact hno_sep sep hsep_ord hsep_bal
  have horient_not_both : ∀ {u w : Fin t}, ¬ (orient u w ∧ orient w u) := by
    rintro u w ⟨⟨_, h1⟩, ⟨_, h2⟩⟩
    exact not_isBigZSide_both (by omega) hZ
      (compEdges G_step6 T τ' w u) (compEdges G_step6 T τ' u w) ⟨h1, h2⟩
  -- Since `|E(T)| + 1 = |V(T)|`, there is a vertex `x : Fin t` with no outgoing `orient x w`.
  have hex_sink : ∃ x : Fin t, ∀ w : Fin t, T.Adj x w → orient w x := by
    by_contra! hall
    have hex_out : ∀ x : Fin t, ∃ w : Fin t, orient x w := by
      intro x
      rcases hall x with ⟨w, hadj, hnot_wx⟩
      exact ⟨w, (horient_or hadj).resolve_right hnot_wx⟩
    choose f hf using hex_out
    let g_edge : Fin t → {e // e ∈ T.edgeFinset} := fun x =>
      ⟨s(x, f x), by rw [mem_edgeFinset, mem_edgeSet]; exact (hf x).1⟩
    have hg_inj : Function.Injective g_edge := by
      intro x₁ x₂ heq
      have hsym : s(x₁, f x₁) = s(x₂, f x₂) := Subtype.ext_iff.mp heq
      rcases Sym2.eq_iff.mp hsym with ⟨h1, _⟩ | ⟨h1, h2⟩
      · exact h1
      · exfalso
        have ho₁ : orient x₁ x₂ := h2 ▸ hf x₁
        have ho₂ : orient x₂ x₁ := h1.symm ▸ hf x₂
        exact horient_not_both ⟨ho₁, ho₂⟩
    have hcard_le := Fintype.card_le_of_injective g_edge hg_inj
    rw [Fintype.card_coe, Fintype.card_fin] at hcard_le
    have hcard_tree : T.edgeFinset.card + 1 = t := by
      have h := hbd.1.1.card_edgeFinset
      rwa [Fintype.card_fin] at h
    omega
  obtain ⟨x, hx_sink⟩ := hex_sink
  by_cases hx_leaf : x ∈ treeLeaves T
  · -- Leaf case: `compEdges G_step6 T τ' x w ⊆ {e_x, g}` spans at most 4 vertices, contradiction!
    have hdeg1 : T.degree x = 1 := (mem_treeLeaves T x).mp hx_leaf
    obtain ⟨w, hadj_xw, hw_uniq⟩ := (degree_eq_one_iff_existsUnique_adj (G := T) (v := x)).mp hdeg1
    have ho_wx : orient w x := hx_sink w hadj_xw
    obtain ⟨e_x, he_x, hτ_ex⟩ := hbd.2.1.surjOn hx_leaf
    have hcomp_single : treeComp T x s(x, w) = {x} := by
      ext y
      simp only [Set.mem_singleton_iff]
      refine ⟨fun hy => ?_, fun h => h ▸ Reachable.rfl⟩
      by_contra hne
      obtain ⟨p, hp⟩ := hbd.1.1.connected.exists_isPath x y
      have hw_not : w ∉ p.support := (mem_treeComp_iff_notMem_support hbd.1.1 hadj_xw hp).1 hy
      cases p with
      | nil => exact (hne rfl).elim
      | @cons _ z _ hadj_xz q =>
        have hzw : z = w := hw_uniq z hadj_xz
        exact hw_not (hzw ▸ List.mem_cons_of_mem x q.start_mem_support)
    have hsub_pair : compEdges G_step6 T τ' x w ⊆ {e_x, g} := by
      intro e he
      rw [mem_compEdges, hcomp_single, Set.mem_singleton_iff] at he
      rw [Finset.mem_insert, Finset.mem_singleton]
      by_cases heg : e = g
      · exact Or.inr heg
      · left
        have he_G' : e ∈ G'.edgeFinset := by
          rw [mem_edgeFinset, edgeSet_deleteEdges, Set.mem_sdiff, Set.mem_singleton_iff]
          exact ⟨mem_edgeFinset.mp he.1, heg⟩
        have hτ_e : τ e = x := (hτ'_eq_of_mem_G' he_G').symm.trans he.2
        exact hbd.2.1.injOn he_G' he_x (hτ_e.trans hτ_ex.symm)
    exact not_isBigZSide_of_subset_pair hω Z e_x g hsub_pair ho_wx.2
  · -- Degree-3 case: `not_isBigZSide_three` contradicts all three neighbors pointing into `x`.
    have hdeg1 : T.degree x ≠ 1 := fun h => hx_leaf ((mem_treeLeaves T x).mpr h)
    have hdeg3 : T.degree x = 3 := (hbd.1.2 x).resolve_left hdeg1
    have hcard3 : (T.neighborFinset x).card = 3 := by
      rw [card_neighborFinset_eq_degree]; exact hdeg3
    obtain ⟨w₁, w₂, w₃, h12, h13, h23, hneigh⟩ := Finset.card_eq_three.mp hcard3
    have hiff : ∀ w, T.Adj x w ↔ w = w₁ ∨ w = w₂ ∨ w = w₃ := by
      intro w; rw [← mem_neighborFinset, hneigh]; simp
    have hadj₁ : T.Adj x w₁ := (hiff w₁).2 (Or.inl rfl)
    have hadj₂ : T.Adj x w₂ := (hiff w₂).2 (Or.inr (Or.inl rfl))
    have hadj₃ : T.Adj x w₃ := (hiff w₃).2 (Or.inr (Or.inr rfl))
    have hsplit₁ := treeComp_split_of_degree_three hbd.1.1 hadj₁ h12 h13 h23 hiff
    have hsplit₂ := treeComp_split_of_degree_three hbd.1.1 hadj₂ h12.symm h23 h13
      (fun z => by rw [hiff]; tauto)
    have hsplit₃ := treeComp_split_of_degree_three hbd.1.1 hadj₃ h13.symm h23.symm h12
      (fun z => by rw [hiff]; tauto)
    let E₁ := compEdges G_step6 T τ' w₁ x
    let E₂ := compEdges G_step6 T τ' w₂ x
    let E₃ := compEdges G_step6 T τ' w₃ x
    have hE₂₃ : compEdges G_step6 T τ' x w₁ = E₂ ∪ E₃ := by
      ext e
      simp only [E₂, E₃, Finset.mem_union, mem_compEdges]
      rw [hsplit₁]
      simp only [Set.mem_union, Set.mem_singleton_iff]
      refine ⟨fun ⟨he, h⟩ => ?_, fun h => ?_⟩
      · rcases h with (hτx | h₂) | h₃
        · exact (hx_leaf (hτx ▸ hτ'_leaves e he)).elim
        · exact Or.inl ⟨he, h₂⟩
        · exact Or.inr ⟨he, h₃⟩
      · rcases h with ⟨he, h₂⟩ | ⟨he, h₃⟩
        · exact ⟨he, Or.inl (Or.inr h₂)⟩
        · exact ⟨he, Or.inr h₃⟩
    have hE₁₃ : compEdges G_step6 T τ' x w₂ = E₁ ∪ E₃ := by
      ext e
      simp only [E₁, E₃, Finset.mem_union, mem_compEdges]
      rw [hsplit₂]
      simp only [Set.mem_union, Set.mem_singleton_iff]
      refine ⟨fun ⟨he, h⟩ => ?_, fun h => ?_⟩
      · rcases h with (hτx | h₁) | h₃
        · exact (hx_leaf (hτx ▸ hτ'_leaves e he)).elim
        · exact Or.inl ⟨he, h₁⟩
        · exact Or.inr ⟨he, h₃⟩
      · rcases h with ⟨he, h₁⟩ | ⟨he, h₃⟩
        · exact ⟨he, Or.inl (Or.inr h₁)⟩
        · exact ⟨he, Or.inr h₃⟩
    have hE₁₂ : compEdges G_step6 T τ' x w₃ = E₁ ∪ E₂ := by
      ext e
      simp only [E₁, E₂, Finset.mem_union, mem_compEdges]
      rw [hsplit₃]
      simp only [Set.mem_union, Set.mem_singleton_iff]
      refine ⟨fun ⟨he, h⟩ => ?_, fun h => ?_⟩
      · rcases h with (hτx | h₁) | h₂
        · exact (hx_leaf (hτx ▸ hτ'_leaves e he)).elim
        · exact Or.inl ⟨he, h₁⟩
        · exact Or.inr ⟨he, h₂⟩
      · rcases h with ⟨he, h₁⟩ | ⟨he, h₂⟩
        · exact ⟨he, Or.inl (Or.inr h₁)⟩
        · exact ⟨he, Or.inr h₂⟩
    have ho₁ := (hx_sink w₁ hadj₁).2
    have ho₂ := (hx_sink w₂ hadj₂).2
    have ho₃ := (hx_sink w₃ hadj₃).2
    rw [hE₂₃] at ho₁
    rw [hE₁₃] at ho₂
    rw [hE₁₂] at ho₃
    exact not_isBigZSide_three hZ E₁ E₂ E₃ ⟨ho₁, ho₂, ho₃⟩

/-! ### Section 5: Main Theorem `isAlg33HighWidthCase_imp_hasBranchWidthGe` -/

/-- **Soundness of the high-branch-width case of Algorithm (3.3) (GM XIII, pages 72–74)**:
When `ω ≥ 2`, `IsAlg33HighWidthCase ω G G'` implies `HasBranchWidthGe G' ω`. -/
theorem isAlg33HighWidthCase_imp_hasBranchWidthGe {n ω : ℕ} (hω : 2 ≤ ω)
    {G G' : MultiDigraph n} (hhigh : IsAlg33HighWidthCase ω G G') :
    HasBranchWidthGe G' ω := by
  rcases hhigh with ⟨hloop, hmult, hcase⟩
  have hcard_eq : G'.toSimpleGraph.edgeFinset.card = G'.numEdges :=
    card_edgeFinset_toSimpleGraph_of_simple hloop hmult
  have hge2 : 2 ≤ G'.numEdges := by
    rw [← hcard_eq]
    rcases hcase with ⟨_, hgt⟩ | ⟨G_step6, g, Z, _, hg, hZ, _, heq_G', hno_sep⟩
    · have hgt' : (G'.toSimpleGraph.edgeFinset.card : ℚ) >
          ((3 : ℚ) / 2 * (ω : ℚ) - 1) * (n : ℚ) := by
        convert hgt using 3
        ext; simp
      by_contra hlt
      have hle1 : G'.toSimpleGraph.edgeFinset.card ≤ 1 := by omega
      have hn_ge2 : (2 : ℚ) ≤ (n : ℚ) := by
        have hpos : 0 < G'.toSimpleGraph.edgeFinset.card := by
          by_contra h0
          have hc0 : G'.toSimpleGraph.edgeFinset.card = 0 := by omega
          rw [hc0, Nat.cast_zero] at hgt'
          have hω_q : (2 : ℚ) ≤ (ω : ℚ) := by exact_mod_cast hω
          have hn_q : (0 : ℚ) ≤ (n : ℚ) := Nat.cast_nonneg n
          nlinarith
        obtain ⟨e, he⟩ := Finset.card_pos.mp hpos
        induction e using Sym2.ind with
        | _ u v =>
          rw [mem_edgeFinset, mem_edgeSet] at he
          have hne : u ≠ v := he.1
          have hn2 : 2 ≤ n := by omega
          exact_mod_cast hn2
      have hω_q : (2 : ℚ) ≤ (ω : ℚ) := by exact_mod_cast hω
      have hc_q : (G'.toSimpleGraph.edgeFinset.card : ℚ) ≤ 1 := by exact_mod_cast hle1
      nlinarith
    · classical
      have h2 := two_le_card_edgeFinset_of_step6 hω hg hZ hno_sep
      have hcard_congr :
          G'.toSimpleGraph.edgeFinset.card = (G_step6.deleteEdges {g}).edgeFinset.card := by
        congr 1
        ext e
        simp [heq_G']
      omega
  refine ⟨hge2, fun w_bd hw_lt hbd => ?_⟩
  rcases hbd with hle1 | ⟨t, T, _hdec, τ, hmulti⟩
  · omega
  · have hmulti' : IsMultiBranchDecompOfWidthLe (ω - 1) G' T τ :=
      ⟨hmulti.1, hmulti.2.1, fun f hf => le_trans (hmulti.2.2 f hf) (by omega)⟩
    obtain ⟨τ_sym2, hbd_simple⟩ :=
      isBranchDecompOfWidthLe_toSimpleGraph_of_simple hloop hmult hmulti'
    rcases hcase with ⟨_, hgt⟩ | ⟨G_step6, g, Z, _, hg, hZ, _, heq_G', hno_sep⟩
    · have hgt' : (G'.toSimpleGraph.edgeFinset.card : ℚ) >
          ((3 : ℚ) / 2 * (ω : ℚ) - 1) * (n : ℚ) := by
        convert hgt using 3
        ext; simp
      have hbd_ω : IsBranchDecompOfWidthLe ω G'.toSimpleGraph T τ_sym2 :=
        ⟨hbd_simple.1, hbd_simple.2.1, fun f hf => le_trans (hbd_simple.2.2 f hf) (by omega)⟩
      have hle_q := lemma_3_2 hω hbd_ω
      linarith
    · classical
      have hbd_step6 : IsBranchDecompOfWidthLe (ω - 1) (G_step6.deleteEdges {g}) T τ_sym2 := by
        have hcongr_edge :
            G'.toSimpleGraph.edgeFinset = (G_step6.deleteEdges {g}).edgeFinset := by
          ext e; simp [heq_G']
        have hcongr_cut : ∀ f : Sym2 (Fin t),
            treeEdgeOrder G'.toSimpleGraph T τ_sym2 f =
            treeEdgeOrder (G_step6.deleteEdges {g}) T τ_sym2 f := by
          intro f
          unfold treeEdgeOrder treeEdgeCutVerts
          congr 1; ext w; simp [heq_G']
        refine ⟨hbd_simple.1, ?_, fun f hf => ?_⟩
        · rw [← hcongr_edge]; exact hbd_simple.2.1
        · rw [← hcongr_cut f]; exact hbd_simple.2.2 f hf
      exact no_branch_decomp_of_step6 hω hg hZ hno_sep hbd_step6

end GraphMinor.Compute
