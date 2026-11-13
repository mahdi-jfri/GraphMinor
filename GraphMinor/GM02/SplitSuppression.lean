module

public import GraphMinor.GM02.SplitSource
public import GraphMinor.GM02.UnmarkedSuppression
import GraphMinor.GM02.SuppressionReduction
import GraphMinor.GM02.SuppressionValency
import GraphMinor.GM02.SuppressedBranches

/-!
# Suppressing the vertices of valency two in the branch trees

This file does the middle step of II (4.8). We start from a graph `J` with a
model `ν` of `H` as in `IsSplitSource H J ν ηe 2`: the branch sets span trees,
all other edges represent edges of `H`, and every vertex in a branch set with
at least two vertices has valency at least two. We suppress vertices of
valency two in such branch sets, one at a time, until none is left
(`IsSplitSource.reduce`). Then every such vertex has valency at least three,
which is what `IsSplitSource.isSplitOf` needs.

Let `x` be a vertex of valency two in a branch set `ν u` with at least two
vertices. Since `ν u` spans a connected graph, `x` has an edge `t` inside
`ν u` to another vertex `z`. There are two cases.

- No representing edge is incident with `x`. Then both edges at `x` lie in
  `ν u`, and suppressing `x` keeps the model
  (`exists_model_suppression_at_unmarked_vertex`).
- Some representing edge `e` is incident with `x`. Then the edges at `x` are
  `t` and `e`. We suppress `x` and give the new edge the name `e`, so `e`
  now joins `z` to the other end of `e` (`IsMinorModel.suppress_into_edge`).
  Since `z` and `x` lie in the same branch set, the model is kept.

In both cases the branch set loses one vertex and one edge inside it, so it
still spans a tree.
-/

@[expose] public section

namespace GraphMinor.GM02

open Graph Set Classical Relation

universe u v u' v'

variable {α : Type u} {β : Type v} {α' : Type u'} {β' : Type v'}

/-- A connected subgraph avoiding a set `F` of edges stays connected after a
suppression whose second edge lies in `F`. Such a subgraph never uses the
second edge, so every edge step keeps its edge. -/
theorem SuppressionData.connected_image_of_second_mem {G : Graph α β}
    (d : SuppressionData G) {F : Set β} (hsecond : d.second ∈ F) {K : Graph α β}
    (hKG : K ≤ G.deleteEdges F) (hK : GraphConnected K) :
    GraphConnected ((d.result.deleteEdges F).induce (suppressionVertexMap d '' V(K))) := by
  let L := (d.result.deleteEdges F).induce (suppressionVertexMap d '' V(K))
  have hmap : ∀ {a b}, K.Adj a b →
      ReflTransGen L.Adj (suppressionVertexMap d a) (suppressionVertexMap d b) := by
    rintro a b ⟨e, hab⟩
    have hG := hKG.isLink_mono hab
    have hlink : G.IsLink e a b := hG.1
    have hnot : e ∉ F := hG.2
    have hne : e ≠ d.second := fun h => hnot (h ▸ hsecond)
    have hfw : suppressionForwardEdgeMap d e = e := by
      simp only [suppressionForwardEdgeMap, hne, ↓reduceIte]
    rcases d.map_link hlink with heq | hstep
    · rw [heq]
    · rw [hfw] at hstep
      exact ReflTransGen.single ⟨e, ⟨⟨hstep, hnot⟩,
        ⟨a, hab.left_mem, rfl⟩, ⟨b, hab.right_mem, rfl⟩⟩⟩
  have hwalk : ∀ {a b}, ReflTransGen K.Adj a b →
      ReflTransGen L.Adj (suppressionVertexMap d a) (suppressionVertexMap d b) := by
    intro a b h
    induction h with
    | refl => exact ReflTransGen.refl
    | tail _ hstep ih => exact ih.trans (hmap hstep)
  obtain ⟨a, ha⟩ := hK.1
  refine ⟨⟨suppressionVertexMap d a, a, ha, rfl⟩, ?_⟩
  rintro x ⟨a, ha, rfl⟩ y ⟨b, hb, rfl⟩
  exact hwalk (hK.2 a ha b hb)

/-- Suppressing a vertex whose second edge represents an edge of `H`, and
giving the new edge the name of that second edge, keeps a model of `H`. The
first edge must lie in the branch set of the removed vertex. -/
theorem IsMinorModel.suppress_into_edge {G : Graph α β} {H : Graph α' β'}
    {ηv : α' → Set α} {ηe : β' → β}
    (hm : IsMinorModel H G ηv ηe) (d : SuppressionData G)
    (hfirst : d.first ∉ ηe '' E(H)) (hsecond : d.second ∈ ηe '' E(H))
    (hfresh : d.fresh = d.second)
    (hsame : ∀ u ∈ V(H), d.vertex ∈ ηv u ↔ d.left ∈ ηv u) :
    IsMinorModel H d.result (fun u => ηv u \ {d.vertex}) ηe := by
  have hne1 : ∀ e ∈ E(H), ηe e ≠ d.first := fun e he h => hfirst (h ▸ ⟨e, he, rfl⟩)
  -- Incidence of a representing edge other than the second edge is unchanged.
  have hinc : ∀ e ∈ E(H), ηe e ≠ d.second → ∀ y,
      d.result.Inc (ηe e) y ↔ G.Inc (ηe e) y := by
    intro e he h2 y
    rw [d.inc_iff]
    constructor
    · rintro (⟨h, -⟩ | ⟨h, -, -⟩)
      · exact (h2 (h.trans hfresh)).elim
      · exact h
    · exact fun h => Or.inr ⟨h, hne1 e he, h2⟩
  have havoid : ∀ e ∈ E(H), ηe e ≠ d.second → ∀ y, G.Inc (ηe e) y → y ≠ d.vertex :=
    fun e he h2 y hy h => d.retained_not_inc (hne1 e he) h2 (h ▸ hy)
  have hinc2 : ∀ y, d.result.Inc d.second y ↔ y = d.left ∨ y = d.right := by
    intro y
    rw [d.inc_iff]
    constructor
    · rintro (⟨-, h⟩ | ⟨-, -, h⟩)
      · exact h
      · exact (h rfl).elim
    · exact fun h => Or.inl ⟨hfresh.symm, h⟩
  have hlv : d.left ≠ d.vertex := d.vertex_ne_left.symm
  have hrv : d.right ≠ d.vertex := d.vertex_ne_right.symm
  have hmemE : ∀ e ∈ E(H), ηe e ∈ E(d.result) := by
    intro e he
    by_cases h2 : ηe e = d.second
    · rw [h2, ← hfresh]
      exact Or.inr rfl
    · exact Or.inl ⟨hm.edge_mem e he, fun h => h.elim (hne1 e he) h2⟩
  have himage : ∀ u ∈ V(H), suppressionVertexMap d '' ηv u = ηv u \ {d.vertex} := by
    intro u hu
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      by_cases hyv : y = d.vertex
      · simp only [suppressionVertexMap, hyv, ↓reduceIte]
        exact ⟨(hsame u hu).1 (hyv ▸ hy), hlv⟩
      · simp only [suppressionVertexMap, hyv, ↓reduceIte]
        exact ⟨hy, hyv⟩
    · intro hx
      have hxv : x ≠ d.vertex := hx.2
      exact ⟨x, hx.1, by simp only [suppressionVertexMap, hxv, ↓reduceIte]⟩
  refine ⟨?_, ?_, hmemE, ?_, hm.edge_injOn, ?_, ?_, ?_⟩
  · intro u hu
    obtain ⟨x, hx⟩ := hm.vertex_nonempty u hu
    by_cases hxv : x = d.vertex
    · exact ⟨d.left, (hsame u hu).1 (hxv ▸ hx), hlv⟩
    · exact ⟨x, hx, hxv⟩
  · intro u hu x hx
    exact ⟨hm.vertex_subset u hu hx.1, hx.2⟩
  · intro a ha b hb hab
    exact (hm.vertex_disjoint a ha b hb hab).mono sdiff_subset sdiff_subset
  · intro u hu e he
    rw [hm.inc_iff u hu e he]
    by_cases h2 : ηe e = d.second
    · rw [h2]
      simp only [hinc2, d.second_inc_iff]
      constructor
      · rintro ⟨y, hy, rfl | rfl⟩
        · exact ⟨d.left, ⟨(hsame u hu).1 hy, hlv⟩, Or.inl rfl⟩
        · exact ⟨d.right, ⟨hy, hrv⟩, Or.inr rfl⟩
      · rintro ⟨y, hy, rfl | rfl⟩
        · exact ⟨d.vertex, (hsame u hu).2 hy.1, Or.inl rfl⟩
        · exact ⟨d.right, hy.1, Or.inr rfl⟩
    · constructor
      · rintro ⟨x, hx, hxe⟩
        exact ⟨x, ⟨hx, havoid e he h2 x hxe⟩, (hinc e he h2 x).2 hxe⟩
      · rintro ⟨x, hx, hxe⟩
        exact ⟨x, hx.1, (hinc e he h2 x).1 hxe⟩
  · intro u hu e he
    rw [hm.isLoopAt_iff u hu e he]
    by_cases h2 : ηe e = d.second
    · rw [h2]
      simp only [hinc2, d.second_inc_iff]
      constructor
      · intro hall y hy
        rcases hy with rfl | rfl
        · exact ⟨(hsame u hu).1 (hall _ (Or.inl rfl)), hlv⟩
        · exact ⟨hall _ (Or.inr rfl), hrv⟩
      · intro hall y hy
        rcases hy with rfl | rfl
        · exact (hsame u hu).2 (hall _ (Or.inl rfl)).1
        · exact (hall _ (Or.inr rfl)).1
    · constructor
      · intro hall x hx
        have hxG := (hinc e he h2 x).1 hx
        exact ⟨hall x hxG, havoid e he h2 x hxG⟩
      · intro hall x hx
        exact (hall x ((hinc e he h2 x).2 hx)).1
  · intro u hu
    obtain ⟨K, hK, hKv, hconn⟩ := hm.connected u hu
    let L := (d.result.deleteEdges (ηe '' E(H))).induce (ηv u \ {d.vertex})
    have hsub : ηv u \ {d.vertex} ⊆ V(d.result.deleteEdges (ηe '' E(H))) :=
      fun x hx => ⟨hm.vertex_subset u hu hx.1, hx.2⟩
    refine ⟨L, Graph.induce_le hsub, rfl, ?_⟩
    have hc := d.connected_image_of_second_mem hsecond hK hconn
    simpa only [hKv, himage u hu] using hc

/-- A vertex `x` of a branch set with another vertex `b` has an edge inside
the branch set to a vertex other than `x`. -/
theorem IsMinorModel.exists_branch_edge_at {H : Graph α' β'} {J : Graph α β}
    {ν : α' → Set α} {ηe : β' → β} (hm : IsMinorModel H J ν ηe) {u : α'}
    (hu : u ∈ V(H)) {x b : α} (hx : x ∈ ν u) (hb : b ∈ ν u) (hxb : x ≠ b) :
    ∃ t z, J.IsLink t x z ∧ x ≠ z ∧ t ∉ ηe '' E(H) ∧ z ∈ ν u := by
  obtain ⟨K, hK, hKv, hconn⟩ := hm.connected u hu
  obtain ⟨z, ⟨t, ht⟩, hxz⟩ :=
    exists_step_ne_of_reflTransGen (hconn.2 x (hKv ▸ hx) b (hKv ▸ hb)) hxb
  have hG := hK.isLink_mono ht
  rw [deleteEdges_isLink] at hG
  exact ⟨t, z, hG.1, hxz, hG.2, hKv ▸ ht.right_mem⟩

section Suppress

variable {H : Graph α' β'} {J : Graph α β} {ν : α' → Set α} {ηe : β' → β}

/-- The common part of both cases: if the branch edges after the suppression
lie in the old branch edges minus an edge `g` of the branch set of the
removed vertex, then `IsSplitSource` with bound two is kept. -/
theorem IsSplitSource.of_suppression (hs : IsSplitSource H J ν ηe 2)
    (hVJ : V(J).Finite) (hEJ : E(J).Finite) (d : SuppressionData J)
    {u : α'} (hu : u ∈ V(H)) (hxu : d.vertex ∈ ν u)
    (hmodel : IsMinorModel H d.result (fun w => ν w \ {d.vertex}) ηe)
    (hinternal : ∀ e ∈ E(d.result), e ∉ ηe '' E(H) →
      ∃ w ∈ V(H), ∀ y, d.result.Inc e y → y ∈ ν w \ {d.vertex})
    {g : β} (hg : g ∈ branchEdges H J ν ηe u)
    (hbranch : ∀ w ∈ V(H), branchEdges H d.result (fun w => ν w \ {d.vertex}) ηe w ⊆
      branchEdges H J ν ηe w \ {g}) :
    IsSplitSource H d.result (fun w => ν w \ {d.vertex}) ηe 2 := by
  have hm := hs.model
  have hνfin : ∀ w ∈ V(H), (ν w).Finite := fun w hw => hVJ.subset (hm.vertex_subset w hw)
  have hBfin : ∀ w, (branchEdges H J ν ηe w).Finite := fun w => hEJ.subset fun e he => he.1
  refine ⟨hmodel, ?_, hinternal, ?_, ?_⟩
  · intro y hy
    obtain ⟨w, hw, hyw⟩ := hs.cover y hy.1
    exact ⟨w, hw, hyw, hy.2⟩
  · intro w hw
    have hle := Set.ncard_le_ncard (hbranch w hw) ((hBfin w).sdiff)
    have hcount := hs.count w hw
    show (branchEdges H d.result (fun w => ν w \ {d.vertex}) ηe w).ncard + 1 ≤
      (ν w \ {d.vertex}).ncard
    by_cases hwu : w = u
    · subst hwu
      have h1 := Set.ncard_sdiff_singleton_add_one hg (hBfin w)
      have h2 := Set.ncard_sdiff_singleton_add_one hxu (hνfin w hw)
      omega
    · have hxw : d.vertex ∉ ν w := fun h =>
        Set.disjoint_left.1 (hm.vertex_disjoint w hw u hu hwu) h hxu
      have h1 := Set.ncard_le_ncard (sdiff_subset (t := {g})) (hBfin w)
      rw [Set.sdiff_singleton_eq_self hxw]
      omega
  · intro w hw y hy h2
    have h2' : 2 ≤ (ν w).ncard :=
      h2.trans (Set.ncard_le_ncard sdiff_subset (hνfin w hw))
    rw [d.valency_eq hEJ hy.2]
    exact hs.high w hw y hy.1 h2'

/-- An edge kept by a suppression that lies in a branch set afterwards lay in
the same branch set before. -/
theorem SuppressionData.mem_branchEdges_of_retained (d : SuppressionData J)
    {w : α'} {e : β} (he : e ∈ E(J)) (h1 : e ≠ d.first) (h2 : e ≠ d.second)
    (hmem : e ∈ branchEdges H d.result (fun w => ν w \ {d.vertex}) ηe w) :
    e ∈ branchEdges H J ν ηe w :=
  ⟨he, hmem.2.1, fun y hy => (hmem.2.2 y ((d.inc_iff e y).2 (Or.inr ⟨hy, h1, h2⟩))).1⟩

/-- A vertex of valency two in a branch set with at least two vertices can be
suppressed so that `IsSplitSource` with bound two is kept. -/
theorem IsSplitSource.exists_suppression (hs : IsSplitSource H J ν ηe 2)
    (hVJ : V(J).Finite) (hEJ : E(J).Finite) {u : α'} (hu : u ∈ V(H)) {x : α}
    (hx : x ∈ ν u) (h2 : 2 ≤ (ν u).ncard) (hval : valency J x = 2) :
    ∃ d : SuppressionData J, IsSplitSource H d.result (fun w => ν w \ {d.vertex}) ηe 2 := by
  have hm := hs.model
  have hνfin : (ν u).Finite := hVJ.subset (hm.vertex_subset u hu)
  obtain ⟨b, hb, hxb⟩ : ∃ b ∈ ν u, x ≠ b := by
    obtain ⟨a, a', ha, ha', haa⟩ := (Set.one_lt_ncard_iff hνfin).1 (by omega)
    by_cases hxa : x = a
    · exact ⟨a', ha', hxa ▸ haa⟩
    · exact ⟨a, ha, hxa⟩
  obtain ⟨t, z, ht, hxz, htF, hz⟩ :=
    GraphMinor.GM02.IsMinorModel.exists_branch_edge_at hm hu hx hb hxb
  have hloop : ∀ e, ¬ J.IsLoopAt e x := by
    intro e he
    have hte := incident_eq_of_loop_of_valency_two hEJ hval he ht.inc_left
    subst hte
    exact hxz (ht.right_unique he).symm
  have htB : t ∈ branchEdges H J ν ηe u := by
    refine ⟨ht.edge_mem, htF, fun y hy => ?_⟩
    rcases hy.eq_or_eq_of_isLink ht with rfl | rfl
    · exact hx
    · exact hz
  -- A vertex of `ν u` lies in no other branch set.
  have honly : ∀ w ∈ V(H), ∀ y ∈ ν u, y ∈ ν w → w = u := by
    intro w hw y hy hyw
    by_contra hne
    exact Set.disjoint_left.1 (hm.vertex_disjoint w hw u hu hne) hyw hy
  by_cases hrep : ∃ e ∈ E(H), J.Inc (ηe e) x
  · -- The second case: a representing edge `ηe e` is incident with `x`.
    obtain ⟨e, he, w, hw⟩ := hrep
    have hxw : x ≠ w := by
      rintro rfl
      exact hloop _ hw
    have heF : ηe e ∈ ηe '' E(H) := ⟨e, he, rfl⟩
    have hte : t ≠ ηe e := fun h => htF (h ▸ heF)
    have hset : incidentEdges J x = {t, ηe e} := by
      have hsub : ({t, ηe e} : Set β) ⊆ incidentEdges J x := by
        rintro g (rfl | rfl)
        · exact ht.inc_left
        · exact hw.inc_left
      have hc : (incidentEdges J x).ncard = 2 := by
        rwa [valency_eq_incidentEdges_of_not_loop hloop] at hval
      exact (Set.eq_of_subset_of_ncard_le hsub (by rw [hc, Set.ncard_pair hte])
        (incidentEdges_finite hEJ x)).symm
    let d : SuppressionData J := {
      vertex := x
      left := z
      right := w
      first := t
      second := ηe e
      fresh := ηe e
      first_ne_second := hte
      first_link := ht
      second_link := hw
      vertex_ne_left := hxz
      vertex_ne_right := hxw
      incident := by
        intro g hg
        change g ∈ incidentEdges J x at hg
        rwa [hset] at hg
      fresh_notMem := fun h => h.2 (Or.inr rfl) }
    have hsame : ∀ w' ∈ V(H), d.vertex ∈ ν w' ↔ d.left ∈ ν w' := by
      intro w' hw'
      constructor
      · intro h
        exact (honly w' hw' x hx h) ▸ hz
      · intro h
        exact (honly w' hw' z hz h) ▸ hx
    have hmodel := GraphMinor.GM02.IsMinorModel.suppress_into_edge hm d htF heF rfl hsame
    refine ⟨d, hs.of_suppression hVJ hEJ d hu hx hmodel ?_ htB ?_⟩
    · intro g hg hgF
      rcases d.edge_cases hg with rfl | ⟨hgJ, h1, h2⟩
      · exact (hgF heF).elim
      · obtain ⟨w', hw', hall⟩ := hs.internal g hgJ hgF
        refine ⟨w', hw', fun y hy => ?_⟩
        rcases (d.inc_iff g y).1 hy with ⟨hf, -⟩ | ⟨hyJ, -, -⟩
        · exact (hgF (hf ▸ heF)).elim
        · exact ⟨hall y hyJ, fun h => d.retained_not_inc h1 h2 (h ▸ hyJ)⟩
    · intro w' hw' g hg
      rcases d.edge_cases hg.1 with hgf | ⟨hgJ, h1, h2⟩
      · exact (hg.2.1 (hgf ▸ heF)).elim
      · exact ⟨d.mem_branchEdges_of_retained hgJ h1 h2 hg, h1⟩
  · -- The first case: no representing edge is incident with `x`.
    push Not at hrep
    have hroot : ∀ w ∈ V(H), ∃ r ∈ ν w, r ∈ {y | y ≠ x} := by
      intro w hw
      obtain ⟨r, hr⟩ := hm.vertex_nonempty w hw
      by_cases hrx : r = x
      · have hwu := honly w hw x hx (hrx ▸ hr)
        exact ⟨b, hwu ▸ hb, fun h => hxb h.symm⟩
      · exact ⟨r, hr, hrx⟩
    have hattach : ∀ e ∈ E(H), ∀ y, J.Inc (ηe e) y → y ∈ {y | y ≠ x} :=
      fun e he y hy h => hrep e he (h ▸ hy)
    have hxA : x ∈ V(J) \ {y | y ≠ x} := ⟨hm.vertex_subset u hu hx, fun h => h rfl⟩
    obtain ⟨d, hdx, hdf, hd1, hd2, hsame, hmodel⟩ :=
      exists_model_suppression_at_unmarked_vertex hm hEJ {y | y ≠ x} hs.cover hroot hattach
        hs.internal hxA hval
    subst hdx
    -- Both edges at the removed vertex lie in its branch set.
    have hinB : ∀ g, J.Inc g d.vertex → g ∉ ηe '' E(H) → g ∈ branchEdges H J ν ηe u := by
      intro g hg hgF
      obtain ⟨w', hw', hall⟩ := hs.internal g hg.edge_mem hgF
      have := honly w' hw' _ hx (hall _ hg)
      subst this
      exact ⟨hg.edge_mem, hgF, hall⟩
    have h2B := hinB _ d.second_link.inc_left hd2
    have h1B := hinB _ d.first_link.inc_left hd1
    refine ⟨d, hs.of_suppression hVJ hEJ d hu hx hmodel
      (internal_edges_after_suppression hm d hd1 hd2 hs.internal) h2B ?_⟩
    intro w' hw' g hg
    rcases d.edge_cases hg.1 with rfl | ⟨hgJ, h1, h2⟩
    · rw [hdf] at hg ⊢
      have hleft : d.left ∈ ν w' \ {d.vertex} :=
        hg.2.2 d.left ((d.inc_iff _ _).2 (Or.inl ⟨hdf.symm, Or.inl rfl⟩))
      have := honly w' hw' _ (hsame u hu hx) hleft.1
      subst this
      exact ⟨h1B, d.first_ne_second⟩
    · exact ⟨d.mem_branchEdges_of_retained hgJ h1 h2 hg, h2⟩

/-- Suppressing vertices of valency two in branch sets, as long as possible,
gives a graph topologically contained in `J` in which every vertex of a branch
set with at least two vertices has valency at least three. -/
theorem IsSplitSource.reduce (hs : IsSplitSource H J ν ηe 2)
    (hVJ : V(J).Finite) (hEJ : E(J).Finite) :
    ∃ L : Graph α β, ReflTransGen IsSuppression J L ∧ V(L).Finite ∧ E(L).Finite ∧
      ∃ ν' : α' → Set α, IsSplitSource H L ν' ηe 3 := by
  obtain ⟨L, hsL, hVL, hEL, ⟨ν', hs'⟩, hstop⟩ :=
    exists_suppression_minimal (fun K => ∃ ν', IsSplitSource H K ν' ηe 2) J hVJ hEJ ⟨ν, hs⟩
  refine ⟨L, hsL, hVL, hEL, ν', hs'.model, hs'.cover, hs'.internal, hs'.count, ?_⟩
  intro u hu x hx h2
  by_contra hlt
  have hval : valency L x = 2 := by
    have := hs'.high u hu x hx h2
    omega
  obtain ⟨d, hd⟩ := hs'.exists_suppression hVL hEL hu hx h2 hval
  exact hstop d ⟨_, hd⟩

end Suppress

end GraphMinor.GM02
