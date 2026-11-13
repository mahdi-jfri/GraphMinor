module

public import GraphMinor.GM21.Defs
public import GraphMinor.GM21.LinkageLemmas
public import GraphMinor.GM21.PortraitDefs

/-!
# Path Components of Linkages and Chordless Vital Linkages (Graph Minors XXI, Section 9)

This file develops the structural properties of connected components of linkages (`IsComponentOf`,
`IsPathGraph`, `IsIndexedPath`) and proves that if `M` is a vital linkage in a graph `H` whose
terminals all lie in a subset `X ⊆ V(H)` with `|X| ≤ 3`, then `CanBeDrawnInDisc21 H X` holds.
This is the core combinatorial engine of Graph Minors XXI, `(9.1)` (page 38 of the preprint).
-/

@[expose] public section

namespace GraphMinor.GM21

open Set Function Classical Hypergraph

universe u v

variable {α : Type u} {β : Type v}

/-! ## 1. Connected Components of a Graph (`componentOf`) -/

/-- The vertex set of the connected component of `M` containing `w`. -/
def reachSet (M : Hypergraph α β) (w : α) : Set α :=
  {x ∈ M.vertexSet | M.skeleton.Reachable w x}

lemma mem_reachSet_self {M : Hypergraph α β} {w : α} (hw : w ∈ M.vertexSet) :
    w ∈ reachSet M w :=
  ⟨hw, SimpleGraph.Reachable.refl w⟩

lemma reachSet_subset_vertexSet (M : Hypergraph α β) (w : α) :
    reachSet M w ⊆ M.vertexSet :=
  fun _ hx => hx.1

lemma reachSet_closed_inc {M : Hypergraph α β} {w x y : α} {e : β}
    (hx : x ∈ reachSet M w) (hinc_x : M.Inc e x) (hinc_y : M.Inc e y) :
    y ∈ reachSet M w := by
  have hyM : y ∈ M.vertexSet := M.vertex_mem_of_inc hinc_y
  rcases eq_or_ne x y with rfl | hne
  · exact hx
  · have hadj : M.skeleton.Adj x y := ⟨hne, e, hinc_x, hinc_y⟩
    exact ⟨hyM, hx.2.trans hadj.reachable⟩

/-- The connected component of `M` containing `w`. -/
def componentOf (M : Hypergraph α β) (w : α) : Hypergraph α β where
  vertexSet := reachSet M w
  edgeSet := {e ∈ M.edgeSet | ∃ x ∈ reachSet M w, M.Inc e x}
  Inc e y := (e ∈ M.edgeSet ∧ ∃ x ∈ reachSet M w, M.Inc e x) ∧ M.Inc e y
  vertex_mem_of_inc := by
    rintro e y ⟨⟨_, x, hx, hinc_x⟩, hinc_y⟩
    exact reachSet_closed_inc hx hinc_x hinc_y
  edge_mem_of_inc _ _ h := h.1
  vertexSet_finite := M.vertexSet_finite.subset (reachSet_subset_vertexSet M w)
  edgeSet_finite := M.edgeSet_finite.subset fun _ h => h.1

lemma componentOf_le (M : Hypergraph α β) (w : α) : componentOf M w ≤ M where
  vertexSet_subset := reachSet_subset_vertexSet M w
  edgeSet_subset _ h := h.1
  ends_eq e he := by
    ext y
    simp only [Hypergraph.ends, componentOf, mem_ofPred_eq]
    exact ⟨fun h => ⟨he, h⟩, fun h => h.2⟩

lemma adj_componentOf_iff {M : Hypergraph α β} {w x y : α}
    (hx : x ∈ reachSet M w) :
    (componentOf M w).skeleton.Adj x y ↔ M.skeleton.Adj x y := by
  constructor
  · rintro ⟨hne, e, h1, h2⟩
    exact ⟨hne, e, h1.2, h2.2⟩
  · rintro ⟨hne, e, hinc_x, hinc_y⟩
    have he : e ∈ (componentOf M w).edgeSet := ⟨M.edge_mem_of_inc hinc_x, x, hx, hinc_x⟩
    exact ⟨hne, e, ⟨he, hinc_x⟩, ⟨he, hinc_y⟩⟩

lemma reachable_componentOf_of_mem_reachSet {M : Hypergraph α β} {w x : α}
    (hw : w ∈ M.vertexSet) (hx : x ∈ reachSet M w) :
    (componentOf M w).skeleton.Reachable w x := by
  obtain ⟨_, ⟨p⟩⟩ := hx
  have hwalk : ∀ {a b : α} (q : M.skeleton.Walk a b),
      a ∈ reachSet M w → (componentOf M w).skeleton.Reachable a b := by
    intro a b q ha
    induction q with
    | nil => exact SimpleGraph.Reachable.refl _
    | @cons a c b hadj q' ih =>
      have hc : c ∈ reachSet M w := by
        rcases hadj with ⟨_, e, ha_inc, hc_inc⟩
        exact reachSet_closed_inc ha ha_inc hc_inc
      have hadj' : (componentOf M w).skeleton.Adj a c := (adj_componentOf_iff ha).mpr hadj
      exact hadj'.reachable.trans (ih hc)
  exact hwalk p (mem_reachSet_self hw)

lemma isComponentOf_componentOf {M : Hypergraph α β} (hM : M.IsGraph)
    {w : α} (hw : w ∈ M.vertexSet) :
    IsComponentOf M (componentOf M w) ∧ w ∈ (componentOf M w).vertexSet := by
  have hw_mem : w ∈ reachSet M w := mem_reachSet_self hw
  refine ⟨⟨componentOf_le M w, ⟨w, hw_mem⟩, ?_, ?_⟩, hw_mem⟩
  · intro x hx y hy
    exact (reachable_componentOf_of_mem_reachSet hw hx).symm.trans
      (reachable_componentOf_of_mem_reachSet hw hy)
  · intro C' hC'M _ hC'_conn hle
    have hV_sub : C'.vertexSet ⊆ reachSet M w := by
      intro x hx
      have hwC' : w ∈ C'.vertexSet := hle.vertexSet_subset hw_mem
      rcases hC'_conn w hwC' x hx with ⟨p⟩
      have hwalk : ∀ {a b : α} (q : C'.skeleton.Walk a b), M.skeleton.Reachable a b := by
        intro a b q
        induction q with
        | nil => exact SimpleGraph.Reachable.refl _
        | @cons a c b hadj q' ih =>
          rcases hadj with ⟨hne, e, ha, hc⟩
          have heC' : e ∈ C'.edgeSet := C'.edge_mem_of_inc ha
          have hadjM : M.skeleton.Adj a c :=
            ⟨hne, e, (GM10.inc_iff_of_le hC'M heC').mp ha, (GM10.inc_iff_of_le hC'M heC').mp hc⟩
          exact hadjM.reachable.trans ih
      exact ⟨hC'M.vertexSet_subset hx, hwalk p⟩
    have hE_sub : C'.edgeSet ⊆ (componentOf M w).edgeSet := by
      intro e he
      have heM : e ∈ M.edgeSet := hC'M.edgeSet_subset he
      obtain ⟨⟨x, hx_end⟩, _⟩ := hM e heM
      have hxC' : C'.Inc e x := (GM10.inc_iff_of_le hC'M he).mpr hx_end
      exact ⟨heM, x, hV_sub (C'.vertex_mem_of_inc hxC'), hx_end⟩
    exact GM10.eq_of_le_of_vertexSet_eq_of_edgeSet_eq hC'M (componentOf_le M w)
      (Subset.antisymm hV_sub hle.vertexSet_subset)
      (Subset.antisymm hE_sub hle.edgeSet_subset)

lemma eq_componentOf_of_isComponentOf {M Q : Hypergraph α β}
    (hM : M.IsGraph) (hQ : IsComponentOf M Q) {w : α} (hw : w ∈ Q.vertexSet) :
    Q = componentOf M w := by
  have hwM : w ∈ M.vertexSet := hQ.1.vertexSet_subset hw
  have hcomp := (isComponentOf_componentOf hM hwM).1
  have hV_sub : Q.vertexSet ⊆ (componentOf M w).vertexSet := by
    intro x hx
    rcases hQ.2.2.1 w hw x hx with ⟨p⟩
    have hwalk : ∀ {a b : α} (q : Q.skeleton.Walk a b), M.skeleton.Reachable a b := by
      intro a b q
      induction q with
      | nil => exact SimpleGraph.Reachable.refl _
      | @cons a c b hadj q' ih =>
        rcases hadj with ⟨hne, e, ha, hc⟩
        have heQ : e ∈ Q.edgeSet := Q.edge_mem_of_inc ha
        have hadjM : M.skeleton.Adj a c :=
          ⟨hne, e, (GM10.inc_iff_of_le hQ.1 heQ).mp ha, (GM10.inc_iff_of_le hQ.1 heQ).mp hc⟩
        exact hadjM.reachable.trans ih
    exact ⟨hQ.1.vertexSet_subset hx, hwalk p⟩
  have hE_sub : Q.edgeSet ⊆ (componentOf M w).edgeSet := by
    intro e he
    have heM : e ∈ M.edgeSet := hQ.1.edgeSet_subset he
    obtain ⟨⟨x, hx_end⟩, _⟩ := hM e heM
    have hxQ : Q.Inc e x := (GM10.inc_iff_of_le hQ.1 he).mpr hx_end
    exact ⟨heM, x, hV_sub (Q.vertex_mem_of_inc hxQ), hx_end⟩
  have hle : Q ≤ componentOf M w :=
    ⟨hV_sub, hE_sub, fun e he => ((componentOf_le M w).ends_eq e (hE_sub he)).symm.trans
      (hQ.1.ends_eq e he)⟩
  exact (hQ.2.2.2 (componentOf M w) hcomp.1 hcomp.2.1 hcomp.2.2.1 hle).symm

lemma incidentEdges_eq_of_isComponentOf {M Q : Hypergraph α β}
    (hM : M.IsGraph) (hQ : IsComponentOf M Q) {x : α} (hx : x ∈ Q.vertexSet) :
    incidentEdges M x = incidentEdges Q x := by
  have h_eq := eq_componentOf_of_isComponentOf hM hQ hx
  subst h_eq
  ext e
  simp only [incidentEdges, componentOf, mem_ofPred_eq]
  exact ⟨fun ⟨he, hinc⟩ => ⟨⟨he, x, hx, hinc⟩, ⟨he, x, hx, hinc⟩, hinc⟩,
    fun ⟨⟨he, _⟩, _, hinc⟩ => ⟨he, hinc⟩⟩

lemma vertexDegree_eq_ncard_incidentEdges_of_isComponentOf {M Q : Hypergraph α β}
    (hM : M.IsGraph) (hQ : IsComponentOf M Q) (hP : IsPathGraph Q) {x : α} (hx : x ∈ Q.vertexSet) :
    vertexDegree M x = (incidentEdges Q x).ncard := by
  unfold vertexDegree
  rw [incidentEdges_eq_of_isComponentOf hM hQ hx]
  have hemp : {e ∈ incidentEdges Q x | (M.ends e).Subsingleton} = ∅ := by
    ext e
    simp only [mem_ofPred_eq, mem_empty_iff_false, iff_false, not_and]
    intro he hsub
    have heQ : e ∈ Q.edgeSet := he.1
    have hends_eq : M.ends e = Q.ends e := hQ.1.ends_eq e heQ
    rw [hends_eq] at hsub
    have hcard2 : (Q.ends e).ncard = 2 := hP.2.2.2.1 e heQ
    have hcard_le1 : (Q.ends e).ncard ≤ 1 := by
      rcases hsub.eq_empty_or_singleton with h0 | ⟨a, ha⟩
      · rw [h0, ncard_empty]; omega
      · rw [ha, ncard_singleton]
    omega
  rw [hemp, ncard_empty, add_zero]

lemma mem_terminals_iff_of_isComponentOf {M Q : Hypergraph α β}
    (hM : M.IsGraph) (hQ : IsComponentOf M Q) (hP : IsPathGraph Q) {x : α} (hx : x ∈ Q.vertexSet) :
    x ∈ terminals M ↔ (incidentEdges Q x).ncard ≤ 1 := by
  simp only [terminals, IsTerminal, mem_ofPred_eq]
  rw [vertexDegree_eq_ncard_incidentEdges_of_isComponentOf hM hQ hP hx]
  exact ⟨fun h => h.2, fun h => ⟨hQ.1.vertexSet_subset hx, h⟩⟩

/-! ## 2. Characterization of `IsPathGraph` via `IsIndexedPath` -/

lemma mem_vertexSet_of_mem_walk_support {M : Hypergraph α β} {a b z : α}
    (ha : a ∈ M.vertexSet) (p : M.skeleton.Walk a b) (hz : z ∈ p.support) :
    z ∈ M.vertexSet := by
  induction p with
  | nil =>
    simp only [SimpleGraph.Walk.support_nil, List.mem_singleton] at hz
    exact hz ▸ ha
  | @cons a c b hadj q ih =>
    simp only [SimpleGraph.Walk.support_cons, List.mem_cons] at hz
    rcases hz with rfl | hz'
    · exact ha
    · have hc : c ∈ M.vertexSet := by
        rcases hadj with ⟨_, e, _, hc_inc⟩
        exact M.vertex_mem_of_inc hc_inc
      exact ih hc hz'

/-- If `Q` is an edgeless path graph, its vertex set is a singleton `{v}` with `0` incident edges. -/
lemma isPathGraph_empty_edgeSet {Q : Hypergraph α β}
    (hP : IsPathGraph Q) (hemp : Q.edgeSet = ∅) :
    ∃ v : α, Q.vertexSet = {v} ∧ (incidentEdges Q v).ncard = 0 := by
  rcases hP.2.1 with ⟨v, hv⟩
  refine ⟨v, Subset.antisymm ?_ (singleton_subset_iff.mpr hv), ?_⟩
  · intro x hx
    rcases hP.2.2.1 x hx v hv with ⟨p⟩
    cases p with
    | nil => rfl
    | @cons _ b _ hadj _ =>
      rcases hadj with ⟨_, e, ha, _⟩
      have he : e ∈ Q.edgeSet := Q.edge_mem_of_inc ha
      rw [hemp] at he
      exact he.elim
  · have hinc_emp : incidentEdges Q v = ∅ := by
      ext e; simp [incidentEdges, hemp]
    rw [hinc_emp, ncard_empty]

/-- In a graph `Q` where every edge has `2` ends and no two distinct edges have the same ends,
for any `x ∈ Q.vertexSet`, the map taking a neighbor `y` of `x` in `Q.skeleton` to the unique
edge with ends `{x, y}` is a bijection onto `incidentEdges Q x`. -/
lemma ncard_neighbors_eq_ncard_incidentEdges {Q : Hypergraph α β}
    (h2 : ∀ e ∈ Q.edgeSet, (Q.ends e).ncard = 2)
    (hinj : ∀ e₁ ∈ Q.edgeSet, ∀ e₂ ∈ Q.edgeSet, Q.ends e₁ = Q.ends e₂ → e₁ = e₂)
    (x : α) :
    {y : α | Q.skeleton.Adj x y}.ncard = (incidentEdges Q x).ncard := by
  have hex_other : ∀ e ∈ incidentEdges Q x, ∃ y : α, Q.skeleton.Adj x y ∧ Q.ends e = {x, y} := by
    rintro e ⟨heQ, hx_inc⟩
    have hfin_ends : (Q.ends e).Finite :=
      Q.vertexSet_finite.subset fun _ hw => Q.vertex_mem_of_inc hw
    have hcard : (Q.ends e).ncard = 2 := h2 e heQ
    have hne_sing : Q.ends e ≠ {x} := by
      intro h_eq
      rw [h_eq, ncard_singleton] at hcard
      omega
    have hsub_ne : ¬ Q.ends e ⊆ {x} := by
      intro hsub
      exact hne_sing (Subset.antisymm hsub (singleton_subset_iff.mpr hx_inc))
    rw [not_subset] at hsub_ne
    rcases hsub_ne with ⟨y, hy_inc, hy_ne⟩
    have hxy : x ≠ y := Ne.symm (mem_singleton_iff.not.mp hy_ne)
    have hends_eq : Q.ends e = {x, y} :=
      eq_pair_of_mem_of_ncard_le_two hfin_ends hcard.le hx_inc hy_inc hxy
    exact ⟨y, ⟨hxy, e, hx_inc, hy_inc⟩, hends_eq⟩
  choose f hf using hex_other
  let g : β → α := fun e => if h : e ∈ incidentEdges Q x then f e h else x
  have hg_on : ∀ e (he : e ∈ incidentEdges Q x), g e = f e he := by
    intro e he
    dsimp [g]; split_ifs; rfl
  have hg_img : g '' incidentEdges Q x = {y : α | Q.skeleton.Adj x y} := by
    ext y
    simp only [mem_image, mem_ofPred_eq]
    constructor
    · rintro ⟨e, he, rfl⟩
      rw [hg_on e he]
      exact (hf e he).1
    · rintro ⟨hxy, e, hx_inc, hy_inc⟩
      have he : e ∈ incidentEdges Q x := ⟨Q.edge_mem_of_inc hx_inc, hx_inc⟩
      refine ⟨e, he, ?_⟩
      rw [hg_on e he]
      have hfin_ends : (Q.ends e).Finite :=
        Q.vertexSet_finite.subset fun _ hw => Q.vertex_mem_of_inc hw
      have hends_eq : Q.ends e = {x, y} :=
        eq_pair_of_mem_of_ncard_le_two hfin_ends (h2 e he.1).le hx_inc hy_inc hxy
      have hpair_eq : ({x, f e he} : Set α) = {x, y} := (hf e he).2.symm.trans hends_eq
      have hy_mem : y ∈ ({x, f e he} : Set α) := by rw [hpair_eq]; exact Or.inr rfl
      rcases hy_mem with rfl | h_eq
      · exact (hxy rfl).elim
      · exact h_eq.symm
  have hg_inj : Set.InjOn g (incidentEdges Q x) := by
    intro e₁ he₁ e₂ he₂ h_eq
    rw [hg_on e₁ he₁, hg_on e₂ he₂] at h_eq
    apply hinj e₁ he₁.1 e₂ he₂.1
    rw [(hf e₁ he₁).2, (hf e₂ he₂).2, h_eq]
  rw [← hg_img, hg_inj.ncard_image]

/-- If a vertex `z` in `Q` has `(incidentEdges Q z).ncard ≤ 2` and two distinct neighbors `a ≠ b`
in `Q.skeleton`, then every neighbor `w` of `z` in `Q.skeleton` is equal to `a` or `b`. -/
lemma neighbor_eq_of_deg_le_two {Q : Hypergraph α β}
    (h2 : ∀ e ∈ Q.edgeSet, (Q.ends e).ncard = 2)
    (hinj : ∀ e₁ ∈ Q.edgeSet, ∀ e₂ ∈ Q.edgeSet, Q.ends e₁ = Q.ends e₂ → e₁ = e₂)
    {z a b w : α} (hdeg : (incidentEdges Q z).ncard ≤ 2)
    (ha : Q.skeleton.Adj z a) (hb : Q.skeleton.Adj z b) (hab : a ≠ b)
    (hw : Q.skeleton.Adj z w) : w = a ∨ w = b := by
  have hcard_nb : {y : α | Q.skeleton.Adj z y}.ncard ≤ 2 := by
    rw [ncard_neighbors_eq_ncard_incidentEdges h2 hinj z]
    exact hdeg
  have hfin_nb : {y : α | Q.skeleton.Adj z y}.Finite := by
    refine Q.vertexSet_finite.subset fun y hy => ?_
    rcases hy with ⟨_, e, _, hy_inc⟩
    exact Q.vertex_mem_of_inc hy_inc
  have h_eq : {y : α | Q.skeleton.Adj z y} = {a, b} :=
    eq_pair_of_mem_of_ncard_le_two hfin_nb hcard_nb ha hb hab
  have hw_mem : w ∈ ({a, b} : Set α) := h_eq ▸ hw
  exact hw_mem

/-- If `z` has `(incidentEdges Q z).ncard = 1` and `Q.skeleton.Adj z a`, then `a` is the unique
neighbor of `z` in `Q.skeleton`. -/
lemma neighbor_eq_of_deg_eq_one {Q : Hypergraph α β}
    (h2 : ∀ e ∈ Q.edgeSet, (Q.ends e).ncard = 2)
    (hinj : ∀ e₁ ∈ Q.edgeSet, ∀ e₂ ∈ Q.edgeSet, Q.ends e₁ = Q.ends e₂ → e₁ = e₂)
    {z a w : α} (hdeg : (incidentEdges Q z).ncard = 1)
    (ha : Q.skeleton.Adj z a) (hw : Q.skeleton.Adj z w) : w = a := by
  have hcard_nb : {y : α | Q.skeleton.Adj z y}.ncard = 1 := by
    rw [ncard_neighbors_eq_ncard_incidentEdges h2 hinj z]
    exact hdeg
  have hfin_nb : {y : α | Q.skeleton.Adj z y}.Finite := by
    refine Q.vertexSet_finite.subset fun y hy => ?_
    rcases hy with ⟨_, e, _, hy_inc⟩
    exact Q.vertex_mem_of_inc hy_inc
  have hsub : {a, w} ⊆ {y : α | Q.skeleton.Adj z y} := by
    rintro y (rfl | rfl) <;> assumption
  have hle := ncard_le_ncard hsub hfin_nb
  rw [hcard_nb] at hle
  by_contra hne
  rw [ncard_pair (Ne.symm hne)] at hle
  omega

/-- Every path graph `Q` with `Q.edgeSet.Nonempty` is an indexed path between two distinct
degree-1 vertices `x₁ ≠ x₂`, and all other vertices of `Q` have degree `2`. -/
theorem exists_isIndexedPath_of_isPathGraph {Q : Hypergraph α β}
    (hP : IsPathGraph Q) (hne_E : Q.edgeSet.Nonempty) :
    ∃ x₁ ∈ Q.vertexSet, ∃ x₂ ∈ Q.vertexSet,
      x₁ ≠ x₂ ∧
      IsIndexedPath Q x₁ x₂ ∧
      ∀ x ∈ Q.vertexSet, ((incidentEdges Q x).ncard ≤ 1 ↔ (x = x₁ ∨ x = x₂)) := by
  obtain ⟨_, _, hconn, h2, hinj_E, hdeg_le2, hex_deg1⟩ := hP
  obtain ⟨x₁, hx₁_V, hx₁_deg1⟩ := hex_deg1 Q le_rfl hne_E
  -- Every simple path in `Q.skeleton` starting at `x₁` has length `< Q.vertexSet.ncard`.
  have hlen_lt : ∀ (y : α) (p : Q.skeleton.Walk x₁ y), p.IsPath → p.length < Q.vertexSet.ncard := by
    intro y p hp
    have hsub : {z : α | z ∈ p.support} ⊆ Q.vertexSet :=
      fun z hz => mem_vertexSet_of_mem_walk_support hx₁_V p hz
    have hcard_supp : {z : α | z ∈ p.support}.ncard = p.length + 1 := by
      have hnodup : p.support.Nodup := hp.support_nodup
      have hsupp_eq : {z : α | z ∈ p.support} = (p.support.toFinset : Set α) := by ext z; simp
      rw [hsupp_eq, ncard_coe_finset, List.toFinset_card_of_nodup hnodup,
        SimpleGraph.Walk.length_support]
    have hle := ncard_le_ncard hsub Q.vertexSet_finite
    omega
  -- Since `(incidentEdges Q x₁).ncard = 1`, `x₁` has a neighbor in `Q.skeleton`.
  have hnb₁_nonempty : {y : α | Q.skeleton.Adj x₁ y}.Nonempty := by
    rw [← ncard_pos (by
      refine Q.vertexSet_finite.subset fun y hy => ?_
      rcases hy with ⟨_, e, _, hy_inc⟩
      exact Q.vertex_mem_of_inc hy_inc)]
    rw [ncard_neighbors_eq_ncard_incidentEdges h2 hinj_E x₁, hx₁_deg1]
    exact Nat.one_pos
  let S_len : Set ℕ := {k : ℕ | ∃ (y : α) (p : Q.skeleton.Walk x₁ y), p.IsPath ∧ p.length = k}
  have hS_fin : S_len.Finite :=
    (finite_Iio Q.vertexSet.ncard).subset fun k ⟨y, p, hp, hk⟩ => hk ▸ hlen_lt y p hp
  have hS_ne : S_len.Nonempty := by
    rcases hnb₁_nonempty with ⟨y₁, hadj₁⟩
    change Q.skeleton.Adj x₁ y₁ at hadj₁
    exact ⟨1, y₁, SimpleGraph.Walk.cons hadj₁ SimpleGraph.Walk.nil,
      SimpleGraph.Walk.IsPath.cons SimpleGraph.Walk.IsPath.nil (by simp [hadj₁.ne]), rfl⟩
  let m : ℕ := hS_fin.toFinset.max' (hS_fin.toFinset_nonempty.mpr hS_ne)
  have hm_mem : m ∈ S_len := hS_fin.mem_toFinset.mp (Finset.max'_mem _ _)
  have hm_max : ∀ k ∈ S_len, k ≤ m :=
    fun k hk => Finset.le_max' _ k (hS_fin.mem_toFinset.mpr hk)
  have hm_ge1 : 1 ≤ m := by
    rcases hnb₁_nonempty with ⟨y₁, hadj₁⟩
    change Q.skeleton.Adj x₁ y₁ at hadj₁
    exact hm_max 1 ⟨y₁, SimpleGraph.Walk.cons hadj₁ SimpleGraph.Walk.nil,
      SimpleGraph.Walk.IsPath.cons SimpleGraph.Walk.IsPath.nil (by simp [hadj₁.ne]), rfl⟩
  rcases hm_mem with ⟨x₂, p, hp, hplen⟩
  let v : Fin (m + 1) → α := fun i => p.getVert i.1
  have hv_inj : Function.Injective v := by
    intro i j hij
    ext
    have hi : i.1 ≤ p.length := by omega
    have hj : j.1 ≤ p.length := by omega
    exact hp.getVert_injOn hi hj hij
  have hv0 : v 0 = x₁ := p.getVert_zero
  have hvm : v ⟨m, Nat.lt_succ_self m⟩ = x₂ := by
    dsimp [v]; rw [← hplen]; exact p.getVert_length
  have hv_mem_V : ∀ i : Fin (m + 1), v i ∈ Q.vertexSet :=
    fun i => mem_vertexSet_of_mem_walk_support hx₁_V p (p.getVert_mem_support i.1)
  have hv_adj_succ : ∀ (k : ℕ) (hk : k < m),
      Q.skeleton.Adj (v ⟨k, by omega⟩) (v ⟨k + 1, by omega⟩) := by
    intro k hk
    change Q.skeleton.Adj (p.getVert k) (p.getVert (k + 1))
    exact p.adj_getVert_succ (by omega)
  have hv0_nb : ∀ w : α, Q.skeleton.Adj (v 0) w → w = v ⟨1, by omega⟩ := by
    intro w hw
    rw [hv0] at hw
    have hadj01 : Q.skeleton.Adj x₁ (v ⟨1, by omega⟩) := by
      convert hv_adj_succ 0 hm_ge1 using 2
      exact hv0.symm
    exact neighbor_eq_of_deg_eq_one h2 hinj_E hx₁_deg1 hadj01 hw
  have hvi_nb : ∀ (k : ℕ) (hk0 : 0 < k) (hkm : k < m) (w : α),
      Q.skeleton.Adj (v ⟨k, by omega⟩) w →
      w = v ⟨k - 1, by omega⟩ ∨ w = v ⟨k + 1, by omega⟩ := by
    intro k hk0 hkm w hw
    have hadj_prev : Q.skeleton.Adj (v ⟨k, by omega⟩) (v ⟨k - 1, by omega⟩) := by
      have h := hv_adj_succ (k - 1) (by omega)
      have h1 : (⟨k - 1 + 1, by omega⟩ : Fin (m + 1)) = ⟨k, by omega⟩ := by
        ext; change k - 1 + 1 = k; omega
      rw [h1] at h
      exact h.symm
    have hadj_next : Q.skeleton.Adj (v ⟨k, by omega⟩) (v ⟨k + 1, by omega⟩) :=
      hv_adj_succ k hkm
    have hne_pn : v ⟨k - 1, by omega⟩ ≠ v ⟨k + 1, by omega⟩ := by
      intro h_eq
      have := congrArg Fin.val (hv_inj h_eq)
      dsimp at this; omega
    exact neighbor_eq_of_deg_le_two h2 hinj_E (hdeg_le2 _ (hv_mem_V _))
      hadj_prev hadj_next hne_pn hw
  have hvm_nb : ∀ w : α, Q.skeleton.Adj (v ⟨m, Nat.lt_succ_self m⟩) w →
      w = v ⟨m - 1, by omega⟩ := by
    intro w hw
    by_cases hw_supp : w ∈ p.support
    · obtain ⟨k, rfl, hk_le⟩ := SimpleGraph.Walk.mem_support_iff_exists_getVert.mp hw_supp
      let ik : Fin (m + 1) := ⟨k, by omega⟩
      change Q.skeleton.Adj (v ⟨m, Nat.lt_succ_self m⟩) (v ik) at hw
      have hik_ne_m : k ≠ m := fun h_eq => hw.ne (congrArg v (Fin.ext h_eq.symm))
      have hik_lt_m : k < m := lt_of_le_of_ne (by omega) hik_ne_m
      rcases Nat.eq_zero_or_pos k with rfl | hk_pos
      · have h1 := hv0_nb (v ⟨m, Nat.lt_succ_self m⟩) hw.symm
        have hm1 : m = 1 := congrArg Fin.val (hv_inj h1)
        change v ik = v ⟨m - 1, by omega⟩
        congr 1; ext; dsimp [ik]; omega
      · rcases hvi_nb k hk_pos hik_lt_m (v ⟨m, Nat.lt_succ_self m⟩) hw.symm with h1 | h1
        · have := congrArg Fin.val (hv_inj h1); dsimp at this; omega
        · have := congrArg Fin.val (hv_inj h1); dsimp at this
          change v ik = v ⟨m - 1, by omega⟩
          congr 1; ext; dsimp [ik]; omega
    · exfalso
      rw [hvm] at hw
      let p' : Q.skeleton.Walk x₁ w := p.concat hw
      have hp' : p'.IsPath := hp.concat hw_supp hw
      have hlen' : p'.length = m + 1 := by simp [p', hplen]
      have hle := hm_max (m + 1) ⟨w, p', hp', hlen'⟩
      omega
  have hadj_iff : ∀ i j : Fin (m + 1),
      Q.skeleton.Adj (v i) (v j) ↔ (i.1 + 1 = j.1 ∨ j.1 + 1 = i.1) := by
    intro i j
    constructor
    · intro hadj
      rcases Nat.eq_zero_or_pos i.1 with hi0 | hi_pos
      · have hi_eq : i = 0 := Fin.ext hi0
        subst hi_eq
        have hj_eq := hv_inj (hv0_nb (v j) hadj)
        left; rw [hj_eq]; rfl
      · rcases eq_or_lt_of_le (Nat.le_of_lt_succ i.2) with him | hi_lt
        · have hi_eq : i = ⟨m, Nat.lt_succ_self m⟩ := Fin.ext him
          subst hi_eq
          have hj_eq := hv_inj (hvm_nb (v j) hadj)
          right; rw [hj_eq]; dsimp; omega
        · rcases hvi_nb i.1 hi_pos hi_lt (v j) hadj with hj_eq | hj_eq
          · right; have := congrArg Fin.val (hv_inj hj_eq); dsimp at this; omega
          · left; have := congrArg Fin.val (hv_inj hj_eq); dsimp at this; omega
    · rintro (h_eq | h_eq)
      · have hj : j = ⟨i.1 + 1, by omega⟩ := Fin.ext h_eq.symm
        rw [hj]
        exact hv_adj_succ i.1 (by omega)
      · have hi : i = ⟨j.1 + 1, by omega⟩ := Fin.ext h_eq.symm
        rw [hi]
        exact (hv_adj_succ j.1 (by omega)).symm
  have hrange_eq : Q.vertexSet = Set.range v := by
    refine Subset.antisymm ?_ ?_
    · intro x hx
      rcases hconn x₁ hx₁_V x hx with ⟨q⟩
      have hwalk : ∀ {a b : α} (w : Q.skeleton.Walk a b),
          a ∈ Set.range v → b ∈ Set.range v := by
        intro a b w ha
        induction w with
        | nil => exact ha
        | @cons a c b hadj w' ih =>
          rcases ha with ⟨i, rfl⟩
          have hc_range : c ∈ Set.range v := by
            rcases Nat.eq_zero_or_pos i.1 with hi0 | hi_pos
            · have hi_eq : i = 0 := Fin.ext hi0
              subst hi_eq
              exact ⟨⟨1, by omega⟩, (hv0_nb c hadj).symm⟩
            · rcases eq_or_lt_of_le (Nat.le_of_lt_succ i.2) with him | hi_lt
              · have hi_eq : i = ⟨m, Nat.lt_succ_self m⟩ := Fin.ext him
                subst hi_eq
                exact ⟨⟨m - 1, by omega⟩, (hvm_nb c hadj).symm⟩
              · rcases hvi_nb i.1 hi_pos hi_lt c hadj with rfl | rfl
                · exact ⟨⟨i.1 - 1, by omega⟩, rfl⟩
                · exact ⟨⟨i.1 + 1, by omega⟩, rfl⟩
          exact ih hc_range
      exact hwalk q ⟨0, hv0⟩
    · rintro _ ⟨i, rfl⟩
      exact hv_mem_V i
  have hx₁_ne_x₂ : x₁ ≠ x₂ := by
    rw [← hv0, ← hvm]
    intro h_eq
    have := congrArg Fin.val (hv_inj h_eq)
    simp only [Fin.val_zero] at this; omega
  refine ⟨x₁, hx₁_V, x₂, hvm ▸ hv_mem_V ⟨m, Nat.lt_succ_self m⟩,
    hx₁_ne_x₂, ⟨m, hm_ge1, v, hv_inj, hv0, hvm, hrange_eq, hadj_iff⟩, ?_⟩
  intro x hx
  rw [hrange_eq] at hx
  rcases hx with ⟨i, rfl⟩
  rw [← ncard_neighbors_eq_ncard_incidentEdges h2 hinj_E (v i)]
  constructor
  · intro hcard_le1
    by_contra hnot_ends
    push Not at hnot_ends
    have hi_ne0 : i.1 ≠ 0 := fun h0 => hnot_ends.1 (hv0 ▸ congrArg v (Fin.ext h0))
    have hi_nem : i.1 ≠ m := fun hm => hnot_ends.2 (hvm ▸ congrArg v (Fin.ext hm))
    have hi_pos : 0 < i.1 := Nat.pos_of_ne_zero hi_ne0
    have hi_lt : i.1 < m := lt_of_le_of_ne (Nat.le_of_lt_succ i.2) hi_nem
    let u₁ := v ⟨i.1 - 1, by omega⟩
    let u₂ := v ⟨i.1 + 1, by omega⟩
    have hu₁ : Q.skeleton.Adj (v i) u₁ := (hadj_iff i ⟨i.1 - 1, by omega⟩).mpr (Or.inr (by dsimp; omega))
    have hu₂ : Q.skeleton.Adj (v i) u₂ := (hadj_iff i ⟨i.1 + 1, by omega⟩).mpr (Or.inl rfl)
    have hne_u : u₁ ≠ u₂ := fun h_eq => by
      have := congrArg Fin.val (hv_inj h_eq); dsimp at this; omega
    have hsub : {u₁, u₂} ⊆ {y : α | Q.skeleton.Adj (v i) y} := by
      rintro y (rfl | rfl) <;> assumption
    have hfin_nb : {y : α | Q.skeleton.Adj (v i) y}.Finite :=
      Q.vertexSet_finite.subset (hrange_eq ▸ fun y hy => by
        rcases hvi_nb i.1 hi_pos hi_lt y hy with rfl | rfl <;> exact mem_range_self _)
    have hle := ncard_le_ncard hsub hfin_nb
    rw [ncard_pair hne_u] at hle
    omega
  · rintro (h_eq | h_eq)
    · rw [h_eq, ncard_neighbors_eq_ncard_incidentEdges h2 hinj_E x₁, hx₁_deg1]
    · have hi_eq : i = ⟨m, Nat.lt_succ_self m⟩ := hv_inj (h_eq.trans hvm.symm)
      subst hi_eq
      have hsub : {y : α | Q.skeleton.Adj (v ⟨m, Nat.lt_succ_self m⟩) y} ⊆ {v ⟨m - 1, by omega⟩} :=
        fun y hy => hvm_nb y hy
      exact (ncard_le_ncard hsub (finite_singleton _)).trans (by rw [ncard_singleton])

/-- Conversely, if `Q` is a graph with `2`-element edge ends, no parallel edges, and satisfies
`IsIndexedPath Q x₁ x₂`, then `Q` is a path graph (`IsPathGraph Q`) and its vertices of degree `≤ 1`
are `{x₁, x₂}`. -/
theorem isPathGraph_of_isIndexedPath {Q : Hypergraph α β} {x₁ x₂ : α}
    (hG : Q.IsGraph)
    (h2 : ∀ e ∈ Q.edgeSet, (Q.ends e).ncard = 2)
    (hinj_E : ∀ e₁ ∈ Q.edgeSet, ∀ e₂ ∈ Q.edgeSet, Q.ends e₁ = Q.ends e₂ → e₁ = e₂)
    (hpath : IsIndexedPath Q x₁ x₂) :
    IsPathGraph Q ∧
    ∀ x ∈ Q.vertexSet, ((incidentEdges Q x).ncard ≤ 1 ↔ (x = x₁ ∨ x = x₂)) := by
  rcases hpath with ⟨m, hm_ge1, v, hv_inj, hv0, hvm, hV_eq, hadj_iff⟩
  have hreach_from_0 : ∀ k : ℕ, (hk : k ≤ m) → Q.skeleton.Reachable (v 0) (v ⟨k, by omega⟩) := by
    intro k
    induction k with
    | zero => intro _; exact SimpleGraph.Reachable.refl (v 0)
    | succ k ih =>
      intro hk
      have hadj : Q.skeleton.Adj (v ⟨k, by omega⟩) (v ⟨k + 1, by omega⟩) :=
        (hadj_iff ⟨k, by omega⟩ ⟨k + 1, by omega⟩).mpr (Or.inl rfl)
      exact (ih (by omega)).trans hadj.reachable
  have hconn : ∀ x ∈ Q.vertexSet, ∀ y ∈ Q.vertexSet, Q.skeleton.Reachable x y := by
    rw [hV_eq]
    rintro _ ⟨i, rfl⟩ _ ⟨j, rfl⟩
    exact (hreach_from_0 i.1 (Nat.le_of_lt_succ i.2)).symm.trans
      (hreach_from_0 j.1 (Nat.le_of_lt_succ j.2))
  have hnb_0 : {y : α | Q.skeleton.Adj (v 0) y} = {v ⟨1, by omega⟩} := by
    ext y
    simp only [mem_ofPred_eq, mem_singleton_iff]
    constructor
    · intro hy
      have hy_V : y ∈ Q.vertexSet := by
        rcases hy with ⟨_, e, _, hy_inc⟩; exact Q.vertex_mem_of_inc hy_inc
      rw [hV_eq] at hy_V
      rcases hy_V with ⟨j, rfl⟩
      rcases (hadj_iff 0 j).mp hy with h1 | h1
      · congr 1; ext; exact h1.symm
      · change j.1 + 1 = 0 at h1; omega
    · rintro rfl
      exact (hadj_iff 0 ⟨1, by omega⟩).mpr (Or.inl rfl)
  have hnb_m : {y : α | Q.skeleton.Adj (v ⟨m, Nat.lt_succ_self m⟩) y} = {v ⟨m - 1, by omega⟩} := by
    ext y
    simp only [mem_ofPred_eq, mem_singleton_iff]
    constructor
    · intro hy
      have hy_V : y ∈ Q.vertexSet := by
        rcases hy with ⟨_, e, _, hy_inc⟩; exact Q.vertex_mem_of_inc hy_inc
      rw [hV_eq] at hy_V
      rcases hy_V with ⟨j, rfl⟩
      rcases (hadj_iff ⟨m, Nat.lt_succ_self m⟩ j).mp hy with h1 | h1
      · change m + 1 = j.1 at h1; omega
      · change j.1 + 1 = m at h1
        congr 1; ext; change j.1 = m - 1; omega
    · rintro rfl
      exact (hadj_iff ⟨m, Nat.lt_succ_self m⟩ ⟨m - 1, by omega⟩).mpr (Or.inr (by dsimp; omega))
  have hnb_mid : ∀ (i : Fin (m + 1)) (hi0 : 0 < i.1) (him : i.1 < m),
      {y : α | Q.skeleton.Adj (v i) y} = {v ⟨i.1 - 1, by omega⟩, v ⟨i.1 + 1, by omega⟩} := by
    intro i hi0 him
    ext y
    simp only [mem_ofPred_eq, mem_insert_iff, mem_singleton_iff]
    constructor
    · intro hy
      have hy_V : y ∈ Q.vertexSet := by
        rcases hy with ⟨_, e, _, hy_inc⟩; exact Q.vertex_mem_of_inc hy_inc
      rw [hV_eq] at hy_V
      rcases hy_V with ⟨j, rfl⟩
      rcases (hadj_iff i j).mp hy with h1 | h1
      · right; congr 1; ext; exact h1.symm
      · left; congr 1; ext; change j.1 = i.1 - 1; omega
    · rintro (rfl | rfl)
      · exact (hadj_iff i ⟨i.1 - 1, by omega⟩).mpr (Or.inr (by dsimp; omega))
      · exact (hadj_iff i ⟨i.1 + 1, by omega⟩).mpr (Or.inl rfl)
  have hdeg_le2 : ∀ x ∈ Q.vertexSet, (incidentEdges Q x).ncard ≤ 2 := by
    rw [hV_eq]
    rintro _ ⟨i, rfl⟩
    rw [← ncard_neighbors_eq_ncard_incidentEdges h2 hinj_E (v i)]
    rcases Nat.eq_zero_or_pos i.1 with hi0 | hi_pos
    · have hi_eq : i = 0 := Fin.ext hi0
      rw [hi_eq, hnb_0, ncard_singleton]; omega
    · rcases eq_or_lt_of_le (Nat.le_of_lt_succ i.2) with him | hi_lt
      · have hi_eq : i = ⟨m, Nat.lt_succ_self m⟩ := Fin.ext him
        rw [hi_eq, hnb_m, ncard_singleton]; omega
      · rw [hnb_mid i hi_pos hi_lt]
        exact (ncard_insert_le _ _).trans (by rw [ncard_singleton])
  have hdeg_0 : (incidentEdges Q x₁).ncard = 1 := by
    rw [← hv0, ← ncard_neighbors_eq_ncard_incidentEdges h2 hinj_E (v 0), hnb_0, ncard_singleton]
  have hdeg_m : (incidentEdges Q x₂).ncard = 1 := by
    rw [← hvm, ← ncard_neighbors_eq_ncard_incidentEdges h2 hinj_E (v ⟨m, Nat.lt_succ_self m⟩),
      hnb_m, ncard_singleton]
  have hx₁_V : x₁ ∈ Q.vertexSet := by rw [hV_eq, ← hv0]; exact mem_range_self 0
  have hacyc : ∀ H : Hypergraph α β, H ≤ Q → H.edgeSet.Nonempty →
      ∃ x ∈ H.vertexSet, (incidentEdges H x).ncard = 1 := by
    intro H hHQ ⟨e₀, he₀H⟩
    have he₀Q : e₀ ∈ Q.edgeSet := hHQ.edgeSet_subset he₀H
    obtain ⟨w₀, hw₀⟩ := (hG e₀ he₀Q).1
    have hw₀V : w₀ ∈ Q.vertexSet := Q.vertex_mem_of_inc hw₀
    rw [hV_eq] at hw₀V
    rcases hw₀V with ⟨i₀, rfl⟩
    let S_idx : Set (Fin (m + 1)) := {i : Fin (m + 1) | (incidentEdges H (v i)).Nonempty}
    have hS_fin : S_idx.Finite := Set.toFinite S_idx
    have hi₀_S : i₀ ∈ S_idx := ⟨e₀, he₀H, (GM10.inc_iff_of_le hHQ he₀H).mpr hw₀⟩
    let k₀ : Fin (m + 1) := hS_fin.toFinset.min' (hS_fin.toFinset_nonempty.mpr ⟨i₀, hi₀_S⟩)
    have hk₀_S : k₀ ∈ S_idx := hS_fin.mem_toFinset.mp (Finset.min'_mem _ _)
    have hk₀_min : ∀ i ∈ S_idx, k₀ ≤ i :=
      fun i hi => Finset.min'_le _ i (hS_fin.mem_toFinset.mpr hi)
    rcases hk₀_S with ⟨e₁, he₁_inc⟩
    have hvk₀_H : v k₀ ∈ H.vertexSet := H.vertex_mem_of_inc he₁_inc.2
    have hends_of_inc : ∀ e ∈ incidentEdges H (v k₀),
        ∃ hk_lt : k₀.1 + 1 < m + 1, Q.ends e = {v k₀, v ⟨k₀.1 + 1, hk_lt⟩} := by
      rintro e ⟨heH, hincH⟩
      have heQ : e ∈ Q.edgeSet := hHQ.edgeSet_subset heH
      have hincQ : Q.Inc e (v k₀) := (GM10.inc_iff_of_le hHQ heH).mp hincH
      obtain ⟨u, huV, hu_ne, hends_e⟩ := exists_other_end_of_ncard_eq_two (h2 e heQ) hincQ
      rw [hV_eq] at huV
      rcases huV with ⟨j, rfl⟩
      have hj_incQ : Q.Inc e (v j) := by
        change v j ∈ Q.ends e; rw [hends_e]; exact Or.inr rfl
      have hj_S : j ∈ S_idx := ⟨e, heH, (GM10.inc_iff_of_le hHQ heH).mpr hj_incQ⟩
      have hk₀_le_j : k₀.1 ≤ j.1 := hk₀_min j hj_S
      have hadj_kj : Q.skeleton.Adj (v k₀) (v j) := ⟨hu_ne.symm, e, hincQ, hj_incQ⟩
      rcases (hadj_iff k₀ j).mp hadj_kj with h_eq | h_eq
      · refine ⟨h_eq ▸ j.2, ?_⟩
        have hj_eq : j = ⟨k₀.1 + 1, h_eq ▸ j.2⟩ := Fin.ext h_eq.symm
        rwa [← hj_eq]
      · omega
    obtain ⟨hk_lt, hends_e₁⟩ := hends_of_inc e₁ he₁_inc
    have hinc_eq_sing : incidentEdges H (v k₀) = {e₁} := by
      refine Subset.antisymm (fun e he => ?_) (singleton_subset_iff.mpr he₁_inc)
      obtain ⟨_, hends_e⟩ := hends_of_inc e he
      exact mem_singleton_iff.mpr
        (hinj_E e (hHQ.edgeSet_subset he.1) e₁ (hHQ.edgeSet_subset he₁_inc.1)
          (hends_e.trans hends_e₁.symm))
    exact ⟨v k₀, hvk₀_H, by rw [hinc_eq_sing, ncard_singleton]⟩
  refine ⟨⟨hG, ⟨x₁, hx₁_V⟩, hconn, h2, hinj_E, hdeg_le2, hacyc⟩, ?_⟩
  rw [hV_eq]
  rintro _ ⟨i, rfl⟩
  rw [← ncard_neighbors_eq_ncard_incidentEdges h2 hinj_E (v i)]
  rcases Nat.eq_zero_or_pos i.1 with hi0 | hi_pos
  · have hi_eq : i = 0 := Fin.ext hi0
    rw [hi_eq, hnb_0, ncard_singleton, hv0]
    exact ⟨fun _ => Or.inl rfl, fun _ => le_rfl⟩
  · rcases eq_or_lt_of_le (Nat.le_of_lt_succ i.2) with him | hi_lt
    · have hi_eq : i = ⟨m, Nat.lt_succ_self m⟩ := Fin.ext him
      rw [hi_eq, hnb_m, ncard_singleton, hvm]
      exact ⟨fun _ => Or.inr rfl, fun _ => le_rfl⟩
    · rw [hnb_mid i hi_pos hi_lt]
      have hne_nb : v ⟨i.1 - 1, by omega⟩ ≠ v ⟨i.1 + 1, by omega⟩ := fun h_eq => by
        have := congrArg Fin.val (hv_inj h_eq)
        change i.1 - 1 = i.1 + 1 at this; omega
      rw [ncard_pair hne_nb]
      have hne1 : v i ≠ x₁ := by
        rw [← hv0]; intro h_eq; have := congrArg Fin.val (hv_inj h_eq)
        change i.1 = 0 at this; omega
      have hne2 : v i ≠ x₂ := by
        rw [← hvm]; intro h_eq; have := congrArg Fin.val (hv_inj h_eq)
        change i.1 = m at this; omega
      exact ⟨fun h => by omega, fun h => (h.elim hne1 hne2).elim⟩

/-! ## 3. Excluding Chords by Vitality of `M` -/

/-- Shortcutting a path component `Q₀` of a vital linkage `M ≤ H` along a non-consecutive chord
`e₀ ∈ H.edgeSet` between `v i₀` and `v j₀` (`i₀.1 + 1 < j₀.1`) yields a distinct linkage `M' ≤ H`
with the same pattern as `M`, contradicting `IsVitalLinkage H M`. -/
theorem no_chord_of_isVitalLinkage {H M Q₀ : Hypergraph α β} {x₁ x₂ : α}
    (hH : H.IsGraph) (hM : IsVitalLinkage H M)
    (hQ₀ : IsComponentOf M Q₀)
    {m : ℕ} (hm_ge1 : 1 ≤ m) {v : Fin (m + 1) → α}
    (hv_inj : Function.Injective v)
    (hv0 : v 0 = x₁) (hvm : v ⟨m, Nat.lt_succ_self m⟩ = x₂)
    (hV_Q₀ : Q₀.vertexSet = Set.range v)
    (hadj_Q₀ : ∀ i j : Fin (m + 1),
      Q₀.skeleton.Adj (v i) (v j) ↔ (i.1 + 1 = j.1 ∨ j.1 + 1 = i.1))
    {i₀ j₀ : Fin (m + 1)} (hij : i₀.1 + 1 < j₀.1) :
    ¬ H.skeleton.Adj (v i₀) (v j₀) := by
  rintro ⟨hne_ij, e₀, hinc_i₀, hinc_j₀⟩
  have hM_graph : M.IsGraph := fun e he => by
    rw [← hM.1.1.ends_eq e he]
    exact hH e (hM.1.1.edgeSet_subset he)
  have he₀_H : e₀ ∈ H.edgeSet := H.edge_mem_of_inc hinc_i₀
  have hfin_ends₀ : (H.ends e₀).Finite :=
    H.vertexSet_finite.subset fun _ hw => H.vertex_mem_of_inc hw
  have hends_e₀ : H.ends e₀ = {v i₀, v j₀} :=
    eq_pair_of_mem_of_ncard_le_two hfin_ends₀ (hH e₀ he₀_H).2 hinc_i₀ hinc_j₀ hne_ij
  -- The set of bypassed internal vertices `S_mid = {v k | i₀ < k < j₀}`.
  let S_mid : Set α := {w : α | ∃ k : Fin (m + 1), i₀.1 < k.1 ∧ k.1 < j₀.1 ∧ v k = w}
  have hvi₀_not_mid : v i₀ ∉ S_mid := by
    rintro ⟨k, hk1, _, hk_eq⟩
    have := congrArg Fin.val (hv_inj hk_eq); omega
  have hvj₀_not_mid : v j₀ ∉ S_mid := by
    rintro ⟨k, _, hk2, hk_eq⟩
    have := congrArg Fin.val (hv_inj hk_eq); omega
  have hS_mid_sub_Q₀ : S_mid ⊆ Q₀.vertexSet := by
    rintro _ ⟨k, _, _, rfl⟩
    rw [hV_Q₀]; exact mem_range_self k
  -- Construct `M'` by deleting `S_mid` from `M` and adding the chord `e₀`.
  let M_del := M.deleteVertices S_mid
  let M' : Hypergraph α β :=
    { vertexSet := M_del.vertexSet
      edgeSet := insert e₀ M_del.edgeSet
      Inc := fun e w => (e = e₀ ∧ H.Inc e₀ w) ∨ (e ∈ M_del.edgeSet ∧ M_del.Inc e w)
      vertex_mem_of_inc := by
        rintro e w (⟨_, hinc⟩ | ⟨_, hinc⟩)
        · have hw_ends : w ∈ H.ends e₀ := hinc
          rw [hends_e₀] at hw_ends
          rcases hw_ends with rfl | rfl
          · exact ⟨hM.2.1.symm ▸ H.vertex_mem_of_inc hinc_i₀, hvi₀_not_mid⟩
          · exact ⟨hM.2.1.symm ▸ H.vertex_mem_of_inc hinc_j₀, hvj₀_not_mid⟩
        · exact M_del.vertex_mem_of_inc hinc
      edge_mem_of_inc := by
        rintro e w (⟨he_eq, _⟩ | ⟨he, _⟩)
        · exact Or.inl he_eq
        · exact Or.inr he
      vertexSet_finite := M_del.vertexSet_finite
      edgeSet_finite := M_del.edgeSet_finite.insert e₀ }
  have hM'_le_H : M' ≤ H := by
    have hdel_le : M_del ≤ H := (GM10.deleteVertices_le M S_mid).trans hM.1.1
    refine ⟨hdel_le.vertexSet_subset, ?_, ?_⟩
    · rintro e (he_eq | he)
      · exact he_eq ▸ he₀_H
      · exact hdel_le.edgeSet_subset he
    · rintro e (he_eq | he)
      · subst he_eq
        ext w
        simp only [Hypergraph.ends, M', mem_ofPred_eq, true_and]
        constructor
        · intro h
          exact Or.inl h
        · rintro (h | ⟨he_del, hinc_del⟩)
          · exact h
          · exact (GM10.inc_iff_of_le hdel_le he_del).mp hinc_del
      · ext w
        simp only [Hypergraph.ends, M', mem_ofPred_eq]
        constructor
        · intro hinc
          exact Or.inr ⟨he, (GM10.inc_iff_of_le hdel_le he).mpr hinc⟩
        · rintro (⟨he_eq, hinc⟩ | ⟨_, hinc⟩)
          · exact he_eq ▸ hinc
          · exact (GM10.inc_iff_of_le hdel_le he).mp hinc
  have hM'_graph : M'.IsGraph := fun e he => by
    rw [← hM'_le_H.ends_eq e he]
    exact hH e (hM'_le_H.edgeSet_subset he)
  -- No edge in `M_del` has ends `{v i₀, v j₀}`.
  have he₀_not_M_del : ∀ e ∈ M_del.edgeSet, M'.ends e ≠ {v i₀, v j₀} := by
    intro e he h_eq
    have heM : e ∈ M.edgeSet := he.1
    have hends_M : M.ends e = {v i₀, v j₀} := by
      rw [← hM.1.1.ends_eq e heM, hM'_le_H.ends_eq e (Or.inr he), h_eq]
    have hinc_M_i₀ : M.Inc e (v i₀) := by change v i₀ ∈ M.ends e; rw [hends_M]; exact Or.inl rfl
    have hinc_M_j₀ : M.Inc e (v j₀) := by change v j₀ ∈ M.ends e; rw [hends_M]; exact Or.inr rfl
    have hvi₀_Q₀ : v i₀ ∈ Q₀.vertexSet := by rw [hV_Q₀]; exact mem_range_self i₀
    have he_Q₀ : e ∈ Q₀.edgeSet := by
      have hinc_eq := incidentEdges_eq_of_isComponentOf hM_graph hQ₀ hvi₀_Q₀
      have he_inc : e ∈ incidentEdges M (v i₀) := ⟨heM, hinc_M_i₀⟩
      rw [hinc_eq] at he_inc
      exact he_inc.1
    have hadj : Q₀.skeleton.Adj (v i₀) (v j₀) :=
      ⟨hne_ij, e, (GM10.inc_iff_of_le hQ₀.1 he_Q₀).mpr hinc_M_i₀,
        (GM10.inc_iff_of_le hQ₀.1 he_Q₀).mpr hinc_M_j₀⟩
    rcases (hadj_Q₀ i₀ j₀).mp hadj with h1 | h1 <;> omega
  -- Define the shortened sequence `v' : Fin (m' + 1) → α`.
  let d : ℕ := j₀.1 - i₀.1 - 1
  have hd_def : d = j₀.1 - i₀.1 - 1 := rfl
  have hi₀_lt : i₀.1 < m + 1 := i₀.2
  have hj₀_lt : j₀.1 < m + 1 := j₀.2
  have hd_pos : 0 < d := by omega
  let m' : ℕ := m - d
  have hm'_def : m' = m - d := rfl
  have hm'_ge1 : 1 ≤ m' := by omega
  let idxMap : Fin (m' + 1) → Fin (m + 1) := fun r =>
    if hr : r.1 ≤ i₀.1 then ⟨r.1, by omega⟩ else ⟨r.1 + d, by omega⟩
  have hidx_val : ∀ r : Fin (m' + 1),
      (idxMap r).1 = if r.1 ≤ i₀.1 then r.1 else r.1 + d := by
    intro r
    dsimp [idxMap]
    split_ifs <;> rfl
  have hidx_inj : Function.Injective idxMap := by
    intro r₁ r₂ h_eq
    have hr₁_lt : r₁.1 < m' + 1 := r₁.2
    have hr₂_lt : r₂.1 < m' + 1 := r₂.2
    have hval := congrArg Fin.val h_eq
    rw [hidx_val r₁, hidx_val r₂] at hval
    ext
    split_ifs at hval <;> omega
  let v' : Fin (m' + 1) → α := v ∘ idxMap
  have hv'_inj : Function.Injective v' := hv_inj.comp hidx_inj
  have hv'0 : v' 0 = x₁ := by
    change v (idxMap 0) = x₁
    have h0 : idxMap 0 = 0 := by
      ext; rw [hidx_val]; simp
    rw [h0, hv0]
  have hv'm' : v' ⟨m', Nat.lt_succ_self m'⟩ = x₂ := by
    change v (idxMap ⟨m', Nat.lt_succ_self m'⟩) = x₂
    have hm_eq : idxMap ⟨m', Nat.lt_succ_self m'⟩ = ⟨m, Nat.lt_succ_self m⟩ := by
      ext; rw [hidx_val]
      change (if m' ≤ i₀.1 then m' else m' + d) = m
      split_ifs <;> omega
    rw [hm_eq, hvm]
  have hrange_v' : Set.range v' = Q₀.vertexSet \ S_mid := by
    ext w
    simp only [mem_range, hV_Q₀, mem_sdiff]
    constructor
    · rintro ⟨r, rfl⟩
      have hr_lt : r.1 < m' + 1 := r.2
      refine ⟨⟨idxMap r, rfl⟩, ?_⟩
      rintro ⟨k, hk1, hk2, hk_eq⟩
      have h_eq := congrArg Fin.val (hv_inj hk_eq)
      rw [hidx_val r] at h_eq
      split_ifs at h_eq <;> omega
    · rintro ⟨⟨k, rfl⟩, hnot_mid⟩
      have hk_lt : k.1 < m + 1 := k.2
      by_cases hk1 : k.1 ≤ i₀.1
      · refine ⟨⟨k.1, by omega⟩, ?_⟩
        change v (idxMap ⟨k.1, by omega⟩) = v k
        congr 1; ext; rw [hidx_val]
        change (if k.1 ≤ i₀.1 then k.1 else k.1 + d) = k.1
        split_ifs; omega
      · have hk2 : j₀.1 ≤ k.1 := by
          by_contra hlt
          exact hnot_mid ⟨k, by omega, by omega, rfl⟩
        refine ⟨⟨k.1 - d, by omega⟩, ?_⟩
        change v (idxMap ⟨k.1 - d, by omega⟩) = v k
        congr 1; ext; rw [hidx_val]
        change (if k.1 - d ≤ i₀.1 then k.1 - d else k.1 - d + d) = k.1
        split_ifs <;> omega
  -- For any component `Q ≠ Q₀` of `M`, `Q` is disjoint from `Q₀.vertexSet` and unaffected in `M'`.
  have hQ_other : ∀ Q : Hypergraph α β, IsComponentOf M Q → Q ≠ Q₀ →
      Q ≤ M' ∧ ∀ e ∈ M'.edgeSet, ∀ w ∈ Q.vertexSet, (M'.Inc e w ↔ Q.Inc e w) := by
    intro Q hQ hne
    obtain ⟨hdisjV, _⟩ := disjoint_of_isComponentOf_ne hM_graph hQ hQ₀ hne
    have hdisj_mid : Disjoint Q.vertexSet S_mid :=
      hdisjV.mono_right hS_mid_sub_Q₀
    have hV_sub : Q.vertexSet ⊆ M'.vertexSet :=
      fun w hw => ⟨hQ.1.vertexSet_subset hw, Set.disjoint_left.mp hdisj_mid hw⟩
    have hE_sub_del : Q.edgeSet ⊆ M_del.edgeSet := by
      intro e he
      refine ⟨hQ.1.edgeSet_subset he, fun w hw_mid hincM => ?_⟩
      have hincQ : Q.Inc e w := (GM10.inc_iff_of_le hQ.1 he).mpr hincM
      exact Set.disjoint_left.mp hdisj_mid (Q.vertex_mem_of_inc hincQ) hw_mid
    have hE_sub : Q.edgeSet ⊆ M'.edgeSet := fun e he => Or.inr (hE_sub_del he)
    have hnot_inc_e₀ : ∀ w ∈ Q.vertexSet, ¬ H.Inc e₀ w := by
      intro w hw hinc
      have hw_ends : w ∈ H.ends e₀ := hinc
      rw [hends_e₀] at hw_ends
      have hw_Q₀ : w ∈ Q₀.vertexSet := by
        rw [hV_Q₀]
        rcases hw_ends with rfl | rfl <;> exact mem_range_self _
      exact Set.disjoint_left.mp hdisjV hw hw_Q₀
    have hle : Q ≤ M' := by
      refine ⟨hV_sub, hE_sub, fun e he => ?_⟩
      rw [← hM'_le_H.ends_eq e (hE_sub he)]
      exact (hQ.1.trans hM.1.1).ends_eq e he
    refine ⟨hle, fun e heM' w hwQ => ?_⟩
    constructor
    · rintro (⟨_, hinc₀⟩ | ⟨he_del, hinc_del⟩)
      · exact (hnot_inc_e₀ w hwQ hinc₀).elim
      · have hincM : M.Inc e w := hinc_del.1
        have he_inc : e ∈ incidentEdges M w := ⟨he_del.1, hincM⟩
        rw [incidentEdges_eq_of_isComponentOf hM_graph hQ hwQ] at he_inc
        exact he_inc.2
    · intro hincQ
      have heQ : e ∈ Q.edgeSet := Q.edge_mem_of_inc hincQ
      exact Or.inr ⟨hE_sub_del heQ,
        ⟨(GM10.inc_iff_of_le hQ.1 heQ).mp hincQ, (hE_sub_del heQ).2⟩⟩
  -- Consequently, for every component `Q ≠ Q₀` of `M`, `IsComponentOf M' Q` holds!
  have hQ_other_comp : ∀ Q : Hypergraph α β, IsComponentOf M Q → Q ≠ Q₀ →
      IsComponentOf M' Q := by
    intro Q hQ hne
    obtain ⟨hle, hinc_iff⟩ := hQ_other Q hQ hne
    rcases hQ.2.1 with ⟨w₀, hw₀⟩
    have h_eq : Q = componentOf M' w₀ := by
      have hcomp' := (isComponentOf_componentOf hM'_graph (hle.vertexSet_subset hw₀)).1
      have hadj_eq : ∀ x ∈ Q.vertexSet, ∀ y : α,
          M'.skeleton.Adj x y ↔ Q.skeleton.Adj x y := by
        intro x hx y
        constructor
        · rintro ⟨hxy, e, hx_inc, hy_inc⟩
          have heM' : e ∈ M'.edgeSet := M'.edge_mem_of_inc hx_inc
          have hxQ : Q.Inc e x := (hinc_iff e heM' x hx).mp hx_inc
          have heQ : e ∈ Q.edgeSet := Q.edge_mem_of_inc hxQ
          have hyQ : Q.Inc e y := (GM10.inc_iff_of_le hle heQ).mpr hy_inc
          exact ⟨hxy, e, hxQ, hyQ⟩
        · rintro ⟨hxy, e, hxQ, hyQ⟩
          have heQ : e ∈ Q.edgeSet := Q.edge_mem_of_inc hxQ
          exact ⟨hxy, e, (GM10.inc_iff_of_le hle heQ).mp hxQ, (GM10.inc_iff_of_le hle heQ).mp hyQ⟩
      have hV_eq : Q.vertexSet = (componentOf M' w₀).vertexSet := by
        refine Subset.antisymm ?_ ?_
        · intro x hx
          rcases hQ.2.2.1 w₀ hw₀ x hx with ⟨p⟩
          have hwalk : ∀ {a b : α} (q : Q.skeleton.Walk a b),
              a ∈ Q.vertexSet → M'.skeleton.Reachable a b := by
            intro a b q haQ
            induction q with
            | nil => exact SimpleGraph.Reachable.refl _
            | @cons a c b hadj q' ih =>
              have hcQ : c ∈ Q.vertexSet := by
                rcases hadj with ⟨_, e, _, hc⟩; exact Q.vertex_mem_of_inc hc
              exact ((hadj_eq a haQ c).mpr hadj).reachable.trans (ih hcQ)
          exact ⟨hle.vertexSet_subset hx, hwalk p hw₀⟩
        · rintro x ⟨_, ⟨p⟩⟩
          have hwalk : ∀ {a b : α} (q : M'.skeleton.Walk a b),
              a ∈ Q.vertexSet → b ∈ Q.vertexSet := by
            intro a b q haQ
            induction q with
            | nil => exact haQ
            | @cons a c b hadj q' ih =>
              have hadjQ : Q.skeleton.Adj a c := (hadj_eq a haQ c).mp hadj
              have hcQ : c ∈ Q.vertexSet := by
                rcases hadjQ with ⟨_, e, _, hc⟩; exact Q.vertex_mem_of_inc hc
              exact ih hcQ
          exact hwalk p hw₀
      have hE_eq : Q.edgeSet = (componentOf M' w₀).edgeSet := by
        ext e
        simp only [componentOf, mem_ofPred_eq]
        constructor
        · intro heQ
          obtain ⟨⟨x, hx_end⟩, _⟩ := hM_graph e (hQ.1.edgeSet_subset heQ)
          have hxQ : Q.Inc e x := (GM10.inc_iff_of_le hQ.1 heQ).mpr hx_end
          have hx_reach : x ∈ reachSet M' w₀ := by
            change x ∈ (componentOf M' w₀).vertexSet
            rw [← hV_eq]
            exact Q.vertex_mem_of_inc hxQ
          exact ⟨hle.edgeSet_subset heQ, x, hx_reach, (GM10.inc_iff_of_le hle heQ).mp hxQ⟩
        · rintro ⟨heM', x, hx_reach, hincM'⟩
          have hxQ : x ∈ Q.vertexSet := by
            rw [hV_eq]; exact hx_reach
          exact Q.edge_mem_of_inc ((hinc_iff e heM' x hxQ).mp hincM')
      exact GM10.eq_of_le_of_vertexSet_eq_of_edgeSet_eq hle hcomp'.1 hV_eq hE_eq
    rw [h_eq]
    exact (isComponentOf_componentOf hM'_graph (hle.vertexSet_subset hw₀)).1
  -- And the component `Q₀' := componentOf M' x₁` is an indexed path between `x₁` and `x₂` with
  -- vertex set `Q₀.vertexSet \ S_mid`.
  have hx₁_Q₀ : x₁ ∈ Q₀.vertexSet := by rw [hV_Q₀, ← hv0]; exact mem_range_self 0
  have hx₁_not_mid : x₁ ∉ S_mid := by
    rw [← hv0]
    rintro ⟨k, hk1, _, hk_eq⟩
    have := congrArg Fin.val (hv_inj hk_eq)
    simp only [Fin.val_zero] at this; omega
  have hx₁_M' : x₁ ∈ M'.vertexSet := ⟨hQ₀.1.vertexSet_subset hx₁_Q₀, hx₁_not_mid⟩
  let Q₀' := componentOf M' x₁
  have hQ₀'_comp : IsComponentOf M' Q₀' := (isComponentOf_componentOf hM'_graph hx₁_M').1
  have hreach_step : ∀ (k : ℕ) (hk : k < m'),
      M'.skeleton.Adj (v' ⟨k, by omega⟩) (v' ⟨k + 1, by omega⟩) := by
    intro k hk
    by_cases hk_eq : k = i₀.1
    · -- Step across the chord `e₀`!
      have h1 : v' ⟨k, by omega⟩ = v i₀ := by
        change v (idxMap ⟨k, by omega⟩) = v i₀
        congr 1; ext; rw [hidx_val]
        change (if k ≤ i₀.1 then k else k + d) = i₀.1
        split_ifs <;> omega
      have h2 : v' ⟨k + 1, by omega⟩ = v j₀ := by
        change v (idxMap ⟨k + 1, by omega⟩) = v j₀
        congr 1; ext; rw [hidx_val]
        change (if k + 1 ≤ i₀.1 then k + 1 else k + 1 + d) = j₀.1
        split_ifs <;> omega
      rw [h1, h2]
      exact ⟨hne_ij, e₀, Or.inl ⟨rfl, hinc_i₀⟩, Or.inl ⟨rfl, hinc_j₀⟩⟩
    · -- Original edge of `Q₀` outside `S_mid`!
      have hadj_orig : Q₀.skeleton.Adj (v (idxMap ⟨k, by omega⟩)) (v (idxMap ⟨k + 1, by omega⟩)) := by
        rw [hadj_Q₀]; left
        rw [hidx_val, hidx_val]
        change (if k ≤ i₀.1 then k else k + d) + 1 = (if k + 1 ≤ i₀.1 then k + 1 else k + 1 + d)
        split_ifs <;> omega
      rcases hadj_orig with ⟨hne_v, e, ha_inc, hb_inc⟩
      have heQ₀ : e ∈ Q₀.edgeSet := Q₀.edge_mem_of_inc ha_inc
      have heM : e ∈ M.edgeSet := hQ₀.1.edgeSet_subset heQ₀
      have ha_M : M.Inc e (v (idxMap ⟨k, by omega⟩)) := (GM10.inc_iff_of_le hQ₀.1 heQ₀).mp ha_inc
      have hb_M : M.Inc e (v (idxMap ⟨k + 1, by omega⟩)) := (GM10.inc_iff_of_le hQ₀.1 heQ₀).mp hb_inc
      have hP_Q₀ : IsPathGraph Q₀ := hM.1.2.2 Q₀ hQ₀
      have hfin_ends : (M.ends e).Finite :=
        M.vertexSet_finite.subset fun _ hw => M.vertex_mem_of_inc hw
      have hcard_M : (M.ends e).ncard = 2 := by
        rw [hQ₀.1.ends_eq e heQ₀]; exact hP_Q₀.2.2.2.1 e heQ₀
      have hends_M : M.ends e = {v (idxMap ⟨k, by omega⟩), v (idxMap ⟨k + 1, by omega⟩)} :=
        eq_pair_of_mem_of_ncard_le_two hfin_ends hcard_M.le ha_M hb_M hne_v
      have he_del : e ∈ M_del.edgeSet := by
        refine ⟨heM, fun w hw_mid hinc_w => ?_⟩
        have hw_ends : w ∈ M.ends e := hinc_w
        rw [hends_M] at hw_ends
        have hnot1 : v (idxMap ⟨k, by omega⟩) ∉ S_mid := by
          have hmem : v' ⟨k, by omega⟩ ∈ Set.range v' := mem_range_self _
          rw [hrange_v'] at hmem; exact hmem.2
        have hnot2 : v (idxMap ⟨k + 1, by omega⟩) ∉ S_mid := by
          have hmem : v' ⟨k + 1, by omega⟩ ∈ Set.range v' := mem_range_self _
          rw [hrange_v'] at hmem; exact hmem.2
        rcases hw_ends with rfl | rfl
        · exact hnot1 hw_mid
        · exact hnot2 hw_mid
      exact ⟨hne_v, e, Or.inr ⟨he_del, ha_M, he_del.2⟩, Or.inr ⟨he_del, hb_M, he_del.2⟩⟩
  have hV_Q₀'_eq : Q₀'.vertexSet = Set.range v' := by
    refine Subset.antisymm ?_ ?_
    · intro w hw
      have hwM' : w ∈ M'.vertexSet := hQ₀'_comp.1.vertexSet_subset hw
      have hwM : w ∈ M.vertexSet := hwM'.1
      by_cases hwQ₀ : w ∈ Q₀.vertexSet
      · rw [hrange_v']; exact ⟨hwQ₀, hwM'.2⟩
      · exfalso
        let Q := componentOf M w
        have hQ : IsComponentOf M Q := (isComponentOf_componentOf hM_graph hwM).1
        have hwQ : w ∈ Q.vertexSet := (isComponentOf_componentOf hM_graph hwM).2
        have hne : Q ≠ Q₀ := fun h_eq => hwQ₀ (h_eq ▸ hwQ)
        have hQ_M' : IsComponentOf M' Q := hQ_other_comp Q hQ hne
        have hQ₀'_ne_Q : Q₀' ≠ Q := by
          intro h_eq
          have hx₁_Q : x₁ ∈ Q.vertexSet := h_eq ▸ (isComponentOf_componentOf hM'_graph hx₁_M').2
          exact Set.disjoint_left.mp (disjoint_of_isComponentOf_ne hM_graph hQ hQ₀ hne).1 hx₁_Q hx₁_Q₀
        exact Set.disjoint_left.mp (disjoint_of_isComponentOf_ne hM'_graph hQ₀'_comp hQ_M' hQ₀'_ne_Q).1 hw hwQ
    · have hreach_v' : ∀ k : ℕ, (hk : k ≤ m') → M'.skeleton.Reachable (v' 0) (v' ⟨k, by omega⟩) := by
        intro k
        induction k with
        | zero => intro _; exact SimpleGraph.Reachable.refl (v' 0)
        | succ k ih =>
          intro hk
          exact (ih (by omega)).trans (hreach_step k (by omega)).reachable
      rintro _ ⟨r, rfl⟩
      have hvr_M' : v' r ∈ M'.vertexSet := by
        have hmem : v' r ∈ Set.range v' := mem_range_self r
        rw [hrange_v'] at hmem
        exact ⟨hQ₀.1.vertexSet_subset hmem.1, hmem.2⟩
      have hreach : M'.skeleton.Reachable x₁ (v' r) := by
        rw [← hv'0]; exact hreach_v' r.1 (Nat.le_of_lt_succ r.2)
      exact ⟨hvr_M', hreach⟩
  have hadj_Q₀'_iff : ∀ r₁ r₂ : Fin (m' + 1),
      Q₀'.skeleton.Adj (v' r₁) (v' r₂) ↔ (r₁.1 + 1 = r₂.1 ∨ r₂.1 + 1 = r₁.1) := by
    intro r₁ r₂
    have hr₁_lt : r₁.1 < m' + 1 := r₁.2
    have hr₂_lt : r₂.1 < m' + 1 := r₂.2
    have hr₁_mem : v' r₁ ∈ reachSet M' x₁ := by
      change v' r₁ ∈ Q₀'.vertexSet; rw [hV_Q₀'_eq]; exact mem_range_self r₁
    rw [adj_componentOf_iff hr₁_mem]
    constructor
    · rintro ⟨hne, e, hinc1, hinc2⟩
      rcases hinc1 with ⟨he_eq, hinc1₀⟩ | ⟨he_del, hinc1_del⟩
      · have hinc2₀ : H.Inc e₀ (v' r₂) := by
          rcases hinc2 with ⟨_, h⟩ | ⟨he_del, hinc2_del⟩
          · exact h
          · exact he_eq ▸ (GM10.inc_iff_of_le ((GM10.deleteVertices_le M S_mid).trans hM.1.1) he_del).mp hinc2_del
        have h1_ends : v' r₁ ∈ H.ends e₀ := hinc1₀
        have h2_ends : v' r₂ ∈ H.ends e₀ := hinc2₀
        rw [hends_e₀] at h1_ends h2_ends
        rcases h1_ends with h1 | h1 <;> rcases h2_ends with h2 | h2
        · exact (hne (h1.trans h2.symm)).elim
        · left
          have hi_eq := congrArg Fin.val (hv_inj h1)
          have hj_eq := congrArg Fin.val (hv_inj h2)
          rw [hidx_val r₁] at hi_eq
          rw [hidx_val r₂] at hj_eq
          split_ifs at hi_eq hj_eq <;> omega
        · right
          have hi_eq := congrArg Fin.val (hv_inj h2)
          have hj_eq := congrArg Fin.val (hv_inj h1)
          rw [hidx_val r₂] at hi_eq
          rw [hidx_val r₁] at hj_eq
          split_ifs at hi_eq hj_eq <;> omega
        · exact (hne (h1.trans h2.symm)).elim
      · have hinc2_del : M_del.Inc e (v' r₂) := by
          rcases hinc2 with ⟨he_eq, hinc2₀⟩ | ⟨_, hinc2_del⟩
          · have hincM : M.Inc e (v' r₂) :=
              (GM10.inc_iff_of_le hM.1.1 he_del.1).mpr (he_eq ▸ hinc2₀)
            exact ⟨hincM, he_del.2⟩
          · exact hinc2_del
        have hvr₁_Q₀ : v' r₁ ∈ Q₀.vertexSet := by
          rw [hV_Q₀]; exact mem_range_self (idxMap r₁)
        have he_Q₀ : e ∈ Q₀.edgeSet := by
          have he_inc : e ∈ incidentEdges M (v' r₁) := ⟨he_del.1, hinc1_del.1⟩
          rw [incidentEdges_eq_of_isComponentOf hM_graph hQ₀ hvr₁_Q₀] at he_inc
          exact he_inc.1
        have hadj_orig : Q₀.skeleton.Adj (v (idxMap r₁)) (v (idxMap r₂)) :=
          ⟨hne, e, (GM10.inc_iff_of_le hQ₀.1 he_Q₀).mpr hinc1_del.1,
            (GM10.inc_iff_of_le hQ₀.1 he_Q₀).mpr hinc2_del.1⟩
        rcases (hadj_Q₀ (idxMap r₁) (idxMap r₂)).mp hadj_orig with h1 | h1
        · rw [hidx_val r₁, hidx_val r₂] at h1
          left; split_ifs at h1 <;> omega
        · rw [hidx_val r₁, hidx_val r₂] at h1
          right; split_ifs at h1 <;> omega
    · rintro (h1 | h1)
      · have hr₂ : r₂ = ⟨r₁.1 + 1, by omega⟩ := Fin.ext h1.symm
        rw [hr₂]; exact hreach_step r₁.1 (by omega)
      · have hr₁ : r₁ = ⟨r₂.1 + 1, by omega⟩ := Fin.ext h1.symm
        rw [hr₁]; exact (hreach_step r₂.1 (by omega)).symm
  have hQ₀'_indexed : IsIndexedPath Q₀' x₁ x₂ :=
    ⟨m', hm'_ge1, v', hv'_inj, hv'0, hv'm', hV_Q₀'_eq, hadj_Q₀'_iff⟩
  -- Check that `Q₀'` has `2`-element ends and no parallel edges.
  have hP_Q₀ : IsPathGraph Q₀ := hM.1.2.2 Q₀ hQ₀
  have hQ₀'_2 : ∀ e ∈ Q₀'.edgeSet, (Q₀'.ends e).ncard = 2 := by
    intro e he
    have heM' : e ∈ M'.edgeSet := hQ₀'_comp.1.edgeSet_subset he
    have hends_eq : H.ends e = Q₀'.ends e :=
      (hQ₀'_comp.1.trans hM'_le_H).ends_eq e he
    rw [← hends_eq]
    rcases heM' with he_eq | he_del
    · rw [he_eq, hends_e₀, ncard_pair hne_ij]
    · rw [hM.1.1.ends_eq e he_del.1]
      -- `e` has ends in `Q₀'.vertexSet ⊆ Q₀.vertexSet`, so `e ∈ Q₀.edgeSet`!
      obtain ⟨⟨w, hw⟩, _⟩ := hQ₀'_comp.1.ends_eq e he ▸ hM'_graph e (Or.inr he_del)
      have hwQ₀ : w ∈ Q₀.vertexSet := by
        have hwQ₀' : w ∈ Q₀'.vertexSet := Q₀'.vertex_mem_of_inc hw
        rw [hV_Q₀'_eq, hrange_v'] at hwQ₀'; exact hwQ₀'.1
      have hincM : M.Inc e w := (GM10.inc_iff_of_le (componentOf_le M' x₁) he).mp hw |>.elim
        (fun ⟨he_eq, hinc₀⟩ => (GM10.inc_iff_of_le hM.1.1 he_del.1).mpr (he_eq ▸ hinc₀))
        (fun ⟨_, hinc_del⟩ => hinc_del.1)
      have he_inc : e ∈ incidentEdges M w := ⟨he_del.1, hincM⟩
      rw [incidentEdges_eq_of_isComponentOf hM_graph hQ₀ hwQ₀] at he_inc
      rw [hQ₀.1.ends_eq e he_inc.1]
      exact hP_Q₀.2.2.2.1 e he_inc.1
  have hQ₀'_inj_E : ∀ e₁ ∈ Q₀'.edgeSet, ∀ e₂ ∈ Q₀'.edgeSet,
      Q₀'.ends e₁ = Q₀'.ends e₂ → e₁ = e₂ := by
    intro e₁ he₁ e₂ he₂ hends_eq
    have he₁M' : e₁ ∈ M'.edgeSet := hQ₀'_comp.1.edgeSet_subset he₁
    have he₂M' : e₂ ∈ M'.edgeSet := hQ₀'_comp.1.edgeSet_subset he₂
    have hM'_ends : M'.ends e₁ = M'.ends e₂ := by
      rw [hQ₀'_comp.1.ends_eq e₁ he₁, hQ₀'_comp.1.ends_eq e₂ he₂, hends_eq]
    have hM'_e₀ : M'.ends e₀ = {v i₀, v j₀} := by
      rw [← hM'_le_H.ends_eq e₀ (Or.inl rfl), hends_e₀]
    rcases he₁M' with he₁_eq | he₁_del <;> rcases he₂M' with he₂_eq | he₂_del
    · exact he₁_eq.trans he₂_eq.symm
    · exfalso; subst he₁_eq; exact he₀_not_M_del e₂ he₂_del (hM'_ends.symm.trans hM'_e₀)
    · exfalso; subst he₂_eq; exact he₀_not_M_del e₁ he₁_del (hM'_ends.trans hM'_e₀)
    · have h1_Q₀ : e₁ ∈ Q₀.edgeSet := by
        obtain ⟨⟨w, hw⟩, _⟩ := hM'_graph e₁ (Or.inr he₁_del)
        have hwQ₀' : w ∈ Q₀'.vertexSet :=
          Q₀'.vertex_mem_of_inc ((GM10.inc_iff_of_le hQ₀'_comp.1 he₁).mpr hw)
        have hwQ₀ : w ∈ Q₀.vertexSet := by rw [hV_Q₀'_eq, hrange_v'] at hwQ₀'; exact hwQ₀'.1
        have hincM : M.Inc e₁ w :=
          (GM10.inc_iff_of_le (GM10.deleteVertices_le M S_mid) he₁_del).mp
            ((GM10.inc_iff_of_le hM'_le_H (Or.inr he₁_del)).mp hw |>
              (GM10.inc_iff_of_le ((GM10.deleteVertices_le M S_mid).trans hM.1.1) he₁_del).mpr)
        have he_inc : e₁ ∈ incidentEdges M w := ⟨he₁_del.1, hincM⟩
        rw [incidentEdges_eq_of_isComponentOf hM_graph hQ₀ hwQ₀] at he_inc
        exact he_inc.1
      have h2_Q₀ : e₂ ∈ Q₀.edgeSet := by
        obtain ⟨⟨w, hw⟩, _⟩ := hM'_graph e₂ (Or.inr he₂_del)
        have hwQ₀' : w ∈ Q₀'.vertexSet :=
          Q₀'.vertex_mem_of_inc ((GM10.inc_iff_of_le hQ₀'_comp.1 he₂).mpr hw)
        have hwQ₀ : w ∈ Q₀.vertexSet := by rw [hV_Q₀'_eq, hrange_v'] at hwQ₀'; exact hwQ₀'.1
        have hincM : M.Inc e₂ w :=
          (GM10.inc_iff_of_le (GM10.deleteVertices_le M S_mid) he₂_del).mp
            ((GM10.inc_iff_of_le hM'_le_H (Or.inr he₂_del)).mp hw |>
              (GM10.inc_iff_of_le ((GM10.deleteVertices_le M S_mid).trans hM.1.1) he₂_del).mpr)
        have he_inc : e₂ ∈ incidentEdges M w := ⟨he₂_del.1, hincM⟩
        rw [incidentEdges_eq_of_isComponentOf hM_graph hQ₀ hwQ₀] at he_inc
        exact he_inc.1
      apply hP_Q₀.2.2.2.2.1 e₁ h1_Q₀ e₂ h2_Q₀
      rw [← hQ₀.1.ends_eq e₁ h1_Q₀, ← hQ₀.1.ends_eq e₂ h2_Q₀,
        ← hM.1.1.ends_eq e₁ he₁_del.1, ← hM.1.1.ends_eq e₂ he₂_del.1,
        hM'_le_H.ends_eq e₁ (Or.inr he₁_del), hM'_le_H.ends_eq e₂ (Or.inr he₂_del), hM'_ends]
  have hQ₀'_path_and_deg := isPathGraph_of_isIndexedPath
    (fun e he => by rw [← hQ₀'_comp.1.ends_eq e he]; exact hM'_graph e (hQ₀'_comp.1.edgeSet_subset he))
    hQ₀'_2 hQ₀'_inj_E hQ₀'_indexed
  -- Every component `C` of `M'` is either `Q₀'` or a component `Q ≠ Q₀` of `M`.
  have hM'_components : ∀ C : Hypergraph α β, IsComponentOf M' C →
      C = Q₀' ∨ (IsComponentOf M C ∧ C ≠ Q₀) := by
    intro C hC
    rcases hC.2.1 with ⟨w, hwC⟩
    have hwM' : w ∈ M'.vertexSet := hC.1.vertexSet_subset hwC
    by_cases hwQ₀ : w ∈ Q₀.vertexSet
    · left
      have hwQ₀' : w ∈ Q₀'.vertexSet := by
        rw [hV_Q₀'_eq, hrange_v']; exact ⟨hwQ₀, hwM'.2⟩
      by_contra hne
      exact Set.disjoint_left.mp (disjoint_of_isComponentOf_ne hM'_graph hC hQ₀'_comp hne).1 hwC hwQ₀'
    · right
      let Q := componentOf M w
      have hQ : IsComponentOf M Q := (isComponentOf_componentOf hM_graph hwM'.1).1
      have hwQ : w ∈ Q.vertexSet := (isComponentOf_componentOf hM_graph hwM'.1).2
      have hne : Q ≠ Q₀ := fun h_eq => hwQ₀ (h_eq ▸ hwQ)
      have hQ_M' : IsComponentOf M' Q := hQ_other_comp Q hQ hne
      have hC_eq_Q : C = Q := by
        by_contra hne_CQ
        exact Set.disjoint_left.mp (disjoint_of_isComponentOf_ne hM'_graph hC hQ_M' hne_CQ).1 hwC hwQ
      subst hC_eq_Q
      exact ⟨hQ, hne⟩
  have hM'_isLinkage : IsLinkage H M' := by
    refine ⟨hM'_le_H, hM'_graph, fun C hC => ?_⟩
    rcases hM'_components C hC with rfl | ⟨hCM, _⟩
    · exact hQ₀'_path_and_deg.1
    · exact hM.1.2.2 C hCM
  -- Check that `terminals M' ∩ Q₀'.vertexSet = {x₁, x₂} = terminals M ∩ Q₀.vertexSet`.
  have hQ₀_path_and_deg := isPathGraph_of_isIndexedPath hP_Q₀.1 hP_Q₀.2.2.2.1 hP_Q₀.2.2.2.2.1
    ⟨m, hm_ge1, v, hv_inj, hv0, hvm, hV_Q₀, hadj_Q₀⟩
  have hterm_Q₀' : terminals M' ∩ Q₀'.vertexSet = {x₁, x₂} := by
    ext w
    simp only [mem_inter_iff, mem_insert_iff, mem_singleton_iff]
    constructor
    · rintro ⟨hw_term, hwQ₀'⟩
      rw [mem_terminals_iff_of_isComponentOf hM'_graph hQ₀'_comp hQ₀'_path_and_deg.1 hwQ₀'] at hw_term
      exact (hQ₀'_path_and_deg.2 w hwQ₀').mp hw_term
    · rintro (hw_eq | hw_eq)
      · subst hw_eq
        have hx₁_Q₀' : w ∈ Q₀'.vertexSet := by rw [hV_Q₀'_eq, ← hv'0]; exact mem_range_self 0
        exact ⟨(mem_terminals_iff_of_isComponentOf hM'_graph hQ₀'_comp hQ₀'_path_and_deg.1 hx₁_Q₀').mpr
          ((hQ₀'_path_and_deg.2 w hx₁_Q₀').mpr (Or.inl rfl)), hx₁_Q₀'⟩
      · subst hw_eq
        have hx₂_Q₀' : w ∈ Q₀'.vertexSet := by
          rw [hV_Q₀'_eq, ← hv'm']; exact mem_range_self (⟨m', Nat.lt_succ_self m'⟩ : Fin (m' + 1))
        exact ⟨(mem_terminals_iff_of_isComponentOf hM'_graph hQ₀'_comp hQ₀'_path_and_deg.1 hx₂_Q₀').mpr
          ((hQ₀'_path_and_deg.2 w hx₂_Q₀').mpr (Or.inr rfl)), hx₂_Q₀'⟩
  have hterm_Q₀ : terminals M ∩ Q₀.vertexSet = {x₁, x₂} := by
    ext w
    simp only [mem_inter_iff, mem_insert_iff, mem_singleton_iff]
    constructor
    · rintro ⟨hw_term, hwQ₀⟩
      rw [mem_terminals_iff_of_isComponentOf hM_graph hQ₀ hP_Q₀ hwQ₀] at hw_term
      exact (hQ₀_path_and_deg.2 w hwQ₀).mp hw_term
    · rintro (hw_eq | hw_eq)
      · subst hw_eq
        exact ⟨(mem_terminals_iff_of_isComponentOf hM_graph hQ₀ hP_Q₀ hx₁_Q₀).mpr
          ((hQ₀_path_and_deg.2 w hx₁_Q₀).mpr (Or.inl rfl)), hx₁_Q₀⟩
      · subst hw_eq
        have hx₂_Q₀ : w ∈ Q₀.vertexSet := by
          rw [hV_Q₀, ← hvm]; exact mem_range_self (⟨m, Nat.lt_succ_self m⟩ : Fin (m + 1))
        exact ⟨(mem_terminals_iff_of_isComponentOf hM_graph hQ₀ hP_Q₀ hx₂_Q₀).mpr
          ((hQ₀_path_and_deg.2 w hx₂_Q₀).mpr (Or.inr rfl)), hx₂_Q₀⟩
  have hterm_other : ∀ Q : Hypergraph α β, IsComponentOf M Q → Q ≠ Q₀ →
      terminals M' ∩ Q.vertexSet = terminals M ∩ Q.vertexSet := by
    intro Q hQ hne
    have hQ_M' : IsComponentOf M' Q := hQ_other_comp Q hQ hne
    have hP_Q : IsPathGraph Q := hM.1.2.2 Q hQ
    ext w
    simp only [mem_inter_iff]
    refine and_congr_left fun hwQ => ?_
    rw [mem_terminals_iff_of_isComponentOf hM'_graph hQ_M' hP_Q hwQ,
      mem_terminals_iff_of_isComponentOf hM_graph hQ hP_Q hwQ]
  have hpattern_eq : linkagePattern M' = linkagePattern M := by
    ext B
    simp only [linkagePattern, mem_ofPred_eq]
    constructor
    · rintro ⟨C, hC, rfl⟩
      rcases hM'_components C hC with rfl | ⟨hCM, hne⟩
      · exact ⟨Q₀, hQ₀, hterm_Q₀'.trans hterm_Q₀.symm⟩
      · exact ⟨C, hCM, hterm_other C hCM hne⟩
    · rintro ⟨C, hC, rfl⟩
      by_cases h_eq : C = Q₀
      · subst h_eq
        exact ⟨Q₀', hQ₀'_comp, hterm_Q₀.trans hterm_Q₀'.symm⟩
      · exact ⟨C, hQ_other_comp C hC h_eq, (hterm_other C hC h_eq).symm⟩
  -- By vitality of `M`, `M' = M`, contradicting that `v ⟨i₀.1 + 1, ...⟩ ∈ M.vertexSet \ M'.vertexSet`!
  have hM'_eq_M : M' = M := hM.2.2 M' hM'_isLinkage hpattern_eq
  let k_mid : Fin (m + 1) := ⟨i₀.1 + 1, by omega⟩
  have hk_mid_S : v k_mid ∈ S_mid := ⟨k_mid, by dsimp [k_mid]; omega, by dsimp [k_mid]; omega, rfl⟩
  have hk_mid_M : v k_mid ∈ M.vertexSet :=
    hQ₀.1.vertexSet_subset (by rw [hV_Q₀]; exact mem_range_self k_mid)
  have hk_mid_M' : v k_mid ∈ M'.vertexSet := by rwa [hM'_eq_M]
  exact hk_mid_M'.2 hk_mid_S

/-! ## 4. Vital Linkage in `H` with `≤ 3` Boundary Terminals Implies `CanBeDrawnInDisc21` -/

/-- If `M` is a vital linkage in a graph `H`, `X ⊆ V(H)` has `|X| ≤ 3`, and `terminals M ⊆ X`,
then `CanBeDrawnInDisc21 H X` holds. -/
theorem canBeDrawnInDisc21_of_isVitalLinkage {H M : Hypergraph α β} {X : Set α}
    (hH : H.IsGraph) (hM : IsVitalLinkage H M)
    (hX_sub : X ⊆ H.vertexSet) (hX_card : X.ncard ≤ 3)
    (hterm_sub : terminals M ⊆ X) :
    CanBeDrawnInDisc21 H X := by
  have hM_graph : M.IsGraph := fun e he => by
    rw [← hM.1.1.ends_eq e he]
    exact hH e (hM.1.1.edgeSet_subset he)
  have hX_fin : X.Finite := H.vertexSet_finite.subset hX_sub
  by_cases hex_edge : ∃ Q : Hypergraph α β, IsComponentOf M Q ∧ Q.edgeSet.Nonempty
  · -- Some component `Q₀` of `M` has edges.
    rcases hex_edge with ⟨Q₀, hQ₀, hQ₀_ne⟩
    have hP₀ : IsPathGraph Q₀ := hM.1.2.2 Q₀ hQ₀
    obtain ⟨x₁, hx₁_Q₀, x₂, hx₂_Q₀, hx₁_ne_x₂, hQ₀_path, hQ₀_deg⟩ :=
      exists_isIndexedPath_of_isPathGraph hP₀ hQ₀_ne
    have hx₁_term : x₁ ∈ terminals M :=
      (mem_terminals_iff_of_isComponentOf hM_graph hQ₀ hP₀ hx₁_Q₀).mpr
        ((hQ₀_deg x₁ hx₁_Q₀).mpr (Or.inl rfl))
    have hx₂_term : x₂ ∈ terminals M :=
      (mem_terminals_iff_of_isComponentOf hM_graph hQ₀ hP₀ hx₂_Q₀).mpr
        ((hQ₀_deg x₂ hx₂_Q₀).mpr (Or.inr rfl))
    have hx₁_X : x₁ ∈ X := hterm_sub hx₁_term
    have hx₂_X : x₂ ∈ X := hterm_sub hx₂_term
    -- Every vertex `w ∈ H.vertexSet \ Q₀.vertexSet` belongs to `X \ Q₀.vertexSet`.
    have hdiff_sub_X : H.vertexSet \ Q₀.vertexSet ⊆ X \ Q₀.vertexSet := by
      rintro w ⟨hwH, hw_not_Q₀⟩
      have hwM : w ∈ M.vertexSet := hM.2.1.symm ▸ hwH
      let Q := componentOf M w
      have hQ : IsComponentOf M Q := (isComponentOf_componentOf hM_graph hwM).1
      have hwQ : w ∈ Q.vertexSet := (isComponentOf_componentOf hM_graph hwM).2
      have hne_Q : Q ≠ Q₀ := fun h_eq => hw_not_Q₀ (h_eq ▸ hwQ)
      have hdisj : Disjoint Q.vertexSet Q₀.vertexSet :=
        (disjoint_of_isComponentOf_ne hM_graph hQ hQ₀ hne_Q).1
      have hP_Q : IsPathGraph Q := hM.1.2.2 Q hQ
      by_cases hQ_E : Q.edgeSet.Nonempty
      · exfalso
        obtain ⟨y₁, hy₁_Q, y₂, hy₂_Q, hy₁_ne_y₂, _, hQ_deg⟩ :=
          exists_isIndexedPath_of_isPathGraph hP_Q hQ_E
        have hy₁_X : y₁ ∈ X := hterm_sub
          ((mem_terminals_iff_of_isComponentOf hM_graph hQ hP_Q hy₁_Q).mpr
            ((hQ_deg y₁ hy₁_Q).mpr (Or.inl rfl)))
        have hy₂_X : y₂ ∈ X := hterm_sub
          ((mem_terminals_iff_of_isComponentOf hM_graph hQ hP_Q hy₂_Q).mpr
            ((hQ_deg y₂ hy₂_Q).mpr (Or.inr rfl)))
        have hsub4 : ({x₁, x₂, y₁, y₂} : Set α) ⊆ X := by
          rintro z (rfl | rfl | rfl | rfl) <;> assumption
        have hx₁_not_y : x₁ ∉ ({y₁, y₂} : Set α) := by
          rintro (rfl | rfl)
          · exact Set.disjoint_left.mp hdisj hy₁_Q hx₁_Q₀
          · exact Set.disjoint_left.mp hdisj hy₂_Q hx₁_Q₀
        have hx₂_not_y : x₂ ∉ ({y₁, y₂} : Set α) := by
          rintro (rfl | rfl)
          · exact Set.disjoint_left.mp hdisj hy₁_Q hx₂_Q₀
          · exact Set.disjoint_left.mp hdisj hy₂_Q hx₂_Q₀
        have hcard4 : ({x₁, x₂, y₁, y₂} : Set α).ncard = 4 := by
          rw [ncard_insert_of_notMem (by simp [hx₁_ne_x₂, hx₁_not_y]),
              ncard_insert_of_notMem hx₂_not_y,
              ncard_pair hy₁_ne_y₂]
        have hle := ncard_le_ncard hsub4 hX_fin
        omega
      · rw [not_nonempty_iff_eq_empty] at hQ_E
        obtain ⟨v_iso, hv_iso_eq, hdeg0⟩ := isPathGraph_empty_edgeSet hP_Q hQ_E
        have hw_eq : w = v_iso := mem_singleton_iff.mp (hv_iso_eq ▸ hwQ)
        subst hw_eq
        have hv_term : w ∈ terminals M :=
          (mem_terminals_iff_of_isComponentOf hM_graph hQ hP_Q hwQ).mpr (by omega)
        exact ⟨hterm_sub hv_term, hw_not_Q₀⟩
    have hX_diff_le1 : (X \ Q₀.vertexSet).ncard ≤ 1 := by
      have hpair_sub : ({x₁, x₂} : Set α) ⊆ X ∩ Q₀.vertexSet := by
        rintro z (rfl | rfl)
        · exact ⟨hx₁_X, hx₁_Q₀⟩
        · exact ⟨hx₂_X, hx₂_Q₀⟩
      have hcard_inter : 2 ≤ (X ∩ Q₀.vertexSet).ncard := by
        rw [← ncard_pair hx₁_ne_x₂]
        exact ncard_le_ncard hpair_sub (hX_fin.subset inter_subset_left)
      have h_add := ncard_inter_add_ncard_sdiff_eq_ncard X Q₀.vertexSet hX_fin
      omega
    have hH_diff_le1 : (H.vertexSet \ Q₀.vertexSet).ncard ≤ 1 :=
      (ncard_le_ncard hdiff_sub_X (hX_fin.subset sdiff_subset)).trans hX_diff_le1
    rcases hQ₀_path with ⟨m, hm_ge1, v, hv_inj, hv0, hvm, hV_Q₀, hadj_Q₀⟩
    have hadj_H_on_Q₀ : ∀ i j : Fin (m + 1),
        H.skeleton.Adj (v i) (v j) ↔ (i.1 + 1 = j.1 ∨ j.1 + 1 = i.1) := by
      intro i j
      constructor
      · intro hadj_H
        by_contra hnot
        have hne_ij : i.1 ≠ j.1 := fun h_eq => hadj_H.ne (congrArg v (Fin.ext h_eq))
        rcases lt_or_gt_of_ne hne_ij with hlt | hgt
        · have hij : i.1 + 1 < j.1 := by omega
          exact no_chord_of_isVitalLinkage hH hM hQ₀ hm_ge1 hv_inj hv0 hvm hV_Q₀ hadj_Q₀ hij hadj_H
        · have hji : j.1 + 1 < i.1 := by omega
          exact no_chord_of_isVitalLinkage hH hM hQ₀ hm_ge1 hv_inj hv0 hvm hV_Q₀ hadj_Q₀ hji hadj_H.symm
      · intro h_consec
        rcases (hadj_Q₀ i j).mpr h_consec with ⟨hne, e, ha, hb⟩
        have heQ₀ : e ∈ Q₀.edgeSet := Q₀.edge_mem_of_inc ha
        have hle_Q₀_H : Q₀ ≤ H := hQ₀.1.trans hM.1.1
        exact ⟨hne, e, (GM10.inc_iff_of_le hle_Q₀_H heQ₀).mp ha,
          (GM10.inc_iff_of_le hle_Q₀_H heQ₀).mp hb⟩
    by_cases hdiff_emp : H.vertexSet \ Q₀.vertexSet = ∅
    · -- Subcase 2a: `H.vertexSet = Q₀.vertexSet`.
      right; left
      have hV_H_eq : H.vertexSet = Set.range v := by
        rw [← hV_Q₀]
        refine Subset.antisymm (fun w hw => ?_)
          (hQ₀.1.vertexSet_subset.trans hM.1.1.vertexSet_subset)
        by_contra hnot
        have : w ∈ (∅ : Set α) := hdiff_emp ▸ ⟨hw, hnot⟩
        exact this
      exact ⟨hX_sub, x₁, hx₁_X, x₂, hx₂_X, hx₁_ne_x₂,
        m, hm_ge1, v, hv_inj, hv0, hvm, hV_H_eq, hadj_H_on_Q₀⟩
    · -- Subcase 2b: `H.vertexSet \ Q₀.vertexSet = {v_iso}` for some `v_iso ∈ X \ Q₀.vertexSet`.
      right; right
      obtain ⟨v_iso, hv_iso_mem⟩ := nonempty_iff_ne_empty.mpr hdiff_emp
      have hdiff_eq : H.vertexSet \ Q₀.vertexSet = {v_iso} := by
        refine Subset.antisymm ?_ (singleton_subset_iff.mpr hv_iso_mem)
        intro w hw
        by_contra hne_w
        have hsub2 : ({v_iso, w} : Set α) ⊆ H.vertexSet \ Q₀.vertexSet := by
          rintro z (rfl | rfl) <;> assumption
        have hle2 := ncard_le_ncard hsub2 (H.vertexSet_finite.subset sdiff_subset)
        rw [ncard_pair (Ne.symm hne_w)] at hle2
        omega
      have hv_iso_X : v_iso ∈ X \ Q₀.vertexSet := hdiff_sub_X hv_iso_mem
      have hx₁_X_diff : x₁ ∈ X \ {v_iso} :=
        ⟨hx₁_X, fun h => hv_iso_X.2 (mem_singleton_iff.mp h ▸ hx₁_Q₀)⟩
      have hx₂_X_diff : x₂ ∈ X \ {v_iso} :=
        ⟨hx₂_X, fun h => hv_iso_X.2 (mem_singleton_iff.mp h ▸ hx₂_Q₀)⟩
      have hV_del_eq : (H.deleteVertices {v_iso}).vertexSet = Set.range v := by
        rw [← hV_Q₀]
        ext w
        simp only [deleteVertices, mem_sdiff, mem_singleton_iff]
        constructor
        · rintro ⟨hwH, hw_ne⟩
          by_contra hw_not_Q₀
          have : w ∈ ({v_iso} : Set α) := hdiff_eq ▸ ⟨hwH, hw_not_Q₀⟩
          exact hw_ne this
        · intro hwQ₀
          exact ⟨(hQ₀.1.trans hM.1.1).vertexSet_subset hwQ₀,
            fun h_eq => hv_iso_X.2 (h_eq ▸ hwQ₀)⟩
      have hadj_del_iff : ∀ i j : Fin (m + 1),
          (H.deleteVertices {v_iso}).skeleton.Adj (v i) (v j) ↔ (i.1 + 1 = j.1 ∨ j.1 + 1 = i.1) := by
        intro i j
        rw [← hadj_H_on_Q₀ i j]
        constructor
        · rintro ⟨hne, e, ha, hb⟩
          exact ⟨hne, e, ha.1, hb.1⟩
        · rintro ⟨hne, e, ha, hb⟩
          have heH : e ∈ H.edgeSet := H.edge_mem_of_inc ha
          have hfin_ends : (H.ends e).Finite :=
            H.vertexSet_finite.subset fun _ hw => H.vertex_mem_of_inc hw
          have hends_eq : H.ends e = {v i, v j} :=
            eq_pair_of_mem_of_ncard_le_two hfin_ends (hH e heH).2 ha hb hne
          have hno_viso : ∀ w ∈ ({v_iso} : Set α), ¬ H.Inc e w := by
            intro w hw_eq hinc_w
            have hw_ends : w ∈ H.ends e := hinc_w
            rw [hends_eq] at hw_ends
            have hw_Q₀ : w ∈ Q₀.vertexSet := by
              rw [hV_Q₀]; rcases hw_ends with rfl | rfl <;> exact mem_range_self _
            exact hv_iso_X.2 (mem_singleton_iff.mp hw_eq ▸ hw_Q₀)
          exact ⟨hne, e, ⟨ha, hno_viso⟩, ⟨hb, hno_viso⟩⟩
      exact ⟨hX_sub, v_iso, hv_iso_X.1, x₁, hx₁_X_diff, x₂, hx₂_X_diff, hx₁_ne_x₂,
        m, hm_ge1, v, hv_inj, hv0, hvm, hV_del_eq, hadj_del_iff⟩
  · -- Case 1: No component of `M` has edges.
    left
    push Not at hex_edge
    refine Subset.antisymm ?_ hX_sub
    intro w hwH
    have hwM : w ∈ M.vertexSet := hM.2.1.symm ▸ hwH
    let Q := componentOf M w
    have hQ : IsComponentOf M Q := (isComponentOf_componentOf hM_graph hwM).1
    have hwQ : w ∈ Q.vertexSet := (isComponentOf_componentOf hM_graph hwM).2
    have hP_Q : IsPathGraph Q := hM.1.2.2 Q hQ
    have hQ_emp : Q.edgeSet = ∅ := hex_edge Q hQ
    obtain ⟨v_iso, hv_iso_eq, hdeg0⟩ := isPathGraph_empty_edgeSet hP_Q hQ_emp
    have hw_eq : w = v_iso := mem_singleton_iff.mp (hv_iso_eq ▸ hwQ)
    subst hw_eq
    have hw_term : w ∈ terminals M :=
      (mem_terminals_iff_of_isComponentOf hM_graph hQ hP_Q hwQ).mpr (by omega)
    exact hterm_sub hw_term

end GraphMinor.GM21
