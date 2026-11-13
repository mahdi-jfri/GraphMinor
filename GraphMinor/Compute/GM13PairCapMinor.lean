module

public import GraphMinor.Compute.GM13PairCap
public import GraphMinor.Compute.Bridge13
public import GraphMinor.Minor.Model
import GraphMinor.Minor.Basic

/-!
# Step (1) of Graph Minors XIII, (4.3): the cap keeps every small minor

Step (1) of (4.3), page 77, replaces the input graph `G` by a maximal subgraph `G₁` with few
loops and few parallel edges, and says "Then $G_1 \in \mathcal{F}$ if and only if
$G \in \mathcal{F}$, as is easily seen." This file gives the argument behind "as is easily seen",
for the subgraph `G.capPair δ` (at most `δ` loops at each vertex and at most `δ + 1` edges between
two distinct vertices; see the correction to (4.3), Step (1), in `corrections/GM13.md`).

The argument. Let `H` be a graph with at most `δ` edges, and take a model of `H` in `G`. The
model uses the edges that represent the edges of `H`, at most `δ` of them, and inside each branch
set it needs only one edge between two adjacent vertices to keep the branch set connected. So it
uses at most `δ` loops at each vertex and at most `δ + 1` edges between two distinct vertices.
Since `G.capPair δ` keeps `min(m, δ)` loops at each vertex and `min(m, δ + 1)` edges between two
distinct vertices joined by `m` edges of `G`, we can send the edges used by the model one-to-one
to edges of `G.capPair δ` with the same ends. This gives a model of `H` in `G.capPair δ`
(`isIsoMinor_capPair`). Since `G.capPair δ` is a subgraph of `G`, the converse is clear, and
membership in a class defined by excluded minors with at most `δ` edges is the same for `G` and
`G.capPair δ` (`membership_capPair43`).
-/

@[expose] public section

namespace GraphMinor.Compute

open GraphMinor Graph Set

namespace PairCapMinor

theorem ite_pos' {c : Prop} [Decidable c] {γ : Type*} {a b : γ} (h : c) :
    (if c then a else b) = a := by simp [h]

theorem ite_neg' {c : Prop} [Decidable c] {γ : Type*} {a b : γ} (h : ¬ c) :
    (if c then a else b) = b := by simp [h]

/-- The multiplicity of `G` between two natural numbers, `0` outside `Fin n`. -/
def mult {n : ℕ} (G : MultiDigraph n) (a b : ℕ) : ℕ :=
  if h : a < n ∧ b < n then G.edgeMult ⟨a, h.1⟩ ⟨b, h.2⟩ else 0

/-- The smaller end of an edge `(u, v, k)` of `G.toGMDigraph.toGraph`. -/
def lo (e : ℕ × ℕ × ℕ) : ℕ := min e.1 e.2.1

/-- The larger end of an edge `(u, v, k)` of `G.toGMDigraph.toGraph`. -/
def hi (e : ℕ × ℕ × ℕ) : ℕ := max e.1 e.2.1

/-- An injective numbering of the triples, used to choose and to rank edges. -/
def key (e : ℕ × ℕ × ℕ) : ℕ := Nat.pair e.1 (Nat.pair e.2.1 e.2.2)

theorem key_injective : Function.Injective key := by
  intro e f h
  simp only [key, Nat.pair_eq_pair] at h
  exact Prod.ext h.1 (Prod.ext h.2.1 h.2.2)

theorem mult_of_lt {n : ℕ} (G : MultiDigraph n) {a b : ℕ} (ha : a < n) (hb : b < n) :
    mult G a b = G.edgeMult ⟨a, ha⟩ ⟨b, hb⟩ := by
  unfold mult
  split_ifs with h
  · rfl
  · exact absurd ⟨ha, hb⟩ h

theorem mult_of_not {n : ℕ} (G : MultiDigraph n) {a b : ℕ} (h : ¬ (a < n ∧ b < n)) :
    mult G a b = 0 := by
  unfold mult
  split_ifs
  rfl

theorem mem_edgeSet_iff {n : ℕ} (G : MultiDigraph n) (e : ℕ × ℕ × ℕ) :
    e ∈ E(G.toGMDigraph.toGraph) ↔ e.2.2 < mult G e.1 e.2.1 := by
  change e ∈ G.toGMDigraph.edgeSet ↔ _
  simp only [MultiDigraph.toGMDigraph, mem_ofPred_eq]
  constructor
  · rintro ⟨hu, hv, hk⟩
    rw [mult_of_lt G hu hv]
    exact hk
  · intro h
    by_cases hc : e.1 < n ∧ e.2.1 < n
    · rw [mult_of_lt G hc.1 hc.2] at h
      exact ⟨hc.1, hc.2, h⟩
    · rw [mult_of_not G hc] at h
      exact absurd h (Nat.not_lt_zero _)

theorem vertexSet_eq {n : ℕ} (G : MultiDigraph n) :
    V(G.toGMDigraph.toGraph) = {u : ℕ | u < n} := rfl

theorem isLink_iff {n : ℕ} (G : MultiDigraph n) (e : ℕ × ℕ × ℕ) (x y : ℕ) :
    G.toGMDigraph.toGraph.IsLink e x y ↔
      e ∈ E(G.toGMDigraph.toGraph) ∧ ((x = lo e ∧ y = hi e) ∨ (x = hi e ∧ y = lo e)) := by
  change (e ∈ G.toGMDigraph.edgeSet ∧ ((e.2.1 = x ∧ e.1 = y) ∨ (e.2.1 = y ∧ e.1 = x))) ↔
    (e ∈ G.toGMDigraph.edgeSet ∧ _)
  simp only [lo, hi, MultiDigraph.toGMDigraph]
  refine and_congr_right fun _ => ?_
  constructor
  · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩) <;> omega
  · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩) <;> omega

/-- Two edges with the same ends link the same pairs of vertices. -/
theorem isLink_iff_of_ends {n n' : ℕ} {G : MultiDigraph n} {G' : MultiDigraph n'}
    {e e' : ℕ × ℕ × ℕ} (he : e ∈ E(G.toGMDigraph.toGraph))
    (he' : e' ∈ E(G'.toGMDigraph.toGraph)) (hlo : lo e' = lo e) (hhi : hi e' = hi e)
    (x y : ℕ) :
    G.toGMDigraph.toGraph.IsLink e x y ↔ G'.toGMDigraph.toGraph.IsLink e' x y := by
  rw [isLink_iff, isLink_iff, hlo, hhi]
  exact ⟨fun h => ⟨he', h.2⟩, fun h => ⟨he, h.2⟩⟩

theorem lo_le_hi (e : ℕ × ℕ × ℕ) : lo e ≤ hi e := by
  simp only [lo, hi]; omega

theorem mult_capPair_loop {n : ℕ} (δ : ℕ) (G : MultiDigraph n) (a : ℕ) :
    mult (G.capPair δ) a a = min (mult G a a) δ := by
  by_cases ha : a < n
  · rw [mult_of_lt _ ha ha, mult_of_lt _ ha ha, MultiDigraph.capPair_loop]
  · rw [mult_of_not _ (fun h => ha h.1), mult_of_not _ (fun h => ha h.1)]; simp

theorem mult_capPair_of_lt {n : ℕ} (δ : ℕ) (G : MultiDigraph n) {a b : ℕ} (hab : a < b) :
    mult (G.capPair δ) a b = min (mult G a b) (δ + 1) := by
  by_cases h : a < n ∧ b < n
  · rw [mult_of_lt _ h.1 h.2, mult_of_lt _ h.1 h.2,
      MultiDigraph.capPair_of_lt δ G (u := ⟨a, h.1⟩) (v := ⟨b, h.2⟩) hab]
  · rw [mult_of_not _ h, mult_of_not _ h]; simp

theorem mult_capPair_add {n : ℕ} (δ : ℕ) (G : MultiDigraph n) {a b : ℕ} (hab : a < b) :
    mult (G.capPair δ) a b + mult (G.capPair δ) b a = min (mult G a b + mult G b a) (δ + 1) := by
  by_cases h : a < n ∧ b < n
  · rw [mult_of_lt _ h.1 h.2, mult_of_lt _ h.1 h.2, mult_of_lt _ h.2 h.1, mult_of_lt _ h.2 h.1]
    exact MultiDigraph.capPair_add δ G (u := ⟨a, h.1⟩) (v := ⟨b, h.2⟩) hab
  · have h' : ¬ (b < n ∧ a < n) := fun h' => h ⟨h'.2, h'.1⟩
    rw [mult_of_not _ h, mult_of_not _ h, mult_of_not _ h', mult_of_not _ h']; simp

/-- The edges of `G` with ends `a ≤ b` number at most `mult G a b + mult G b a`, and at most
`mult G a a` when `a = b`. -/
theorem ncard_ends_le {n : ℕ} (G : MultiDigraph n) (a b : ℕ) :
    {f | f ∈ E(G.toGMDigraph.toGraph) ∧ lo f = a ∧ hi f = b}.ncard ≤
      if a = b then mult G a a else mult G a b + mult G b a := by
  have hsub : {f | f ∈ E(G.toGMDigraph.toGraph) ∧ lo f = a ∧ hi f = b} ⊆
      ↑(((Finset.range (mult G a b)).image fun k => (a, b, k)) ∪
        ((Finset.range (mult G b a)).image fun k => (b, a, k))) := by
    rintro ⟨u, v, k⟩ ⟨he, hlo, hhi⟩
    rw [mem_edgeSet_iff] at he
    simp only [lo, hi] at hlo hhi he
    simp only [Finset.coe_union, Finset.coe_image, Finset.coe_range, mem_union, mem_image,
      mem_Iio, Prod.mk.injEq]
    rcases le_total u v with huv | huv
    · left
      have hu : u = a := by omega
      have hv : v = b := by omega
      subst hu hv
      exact ⟨k, he, rfl, rfl, rfl⟩
    · right
      have hu : u = b := by omega
      have hv : v = a := by omega
      subst hu hv
      exact ⟨k, he, rfl, rfl, rfl⟩
  have h1 := Set.ncard_le_ncard hsub (Finset.finite_toSet _)
  rw [Set.ncard_coe_finset] at h1
  split_ifs with hab
  · subst hab
    have hsub' : {f | f ∈ E(G.toGMDigraph.toGraph) ∧ lo f = a ∧ hi f = a} ⊆
        ↑((Finset.range (mult G a a)).image fun k => (a, a, k)) := by
      rintro ⟨u, v, k⟩ ⟨he, hlo, hhi⟩
      rw [mem_edgeSet_iff] at he
      simp only [lo, hi] at hlo hhi he
      have hu : u = a := by omega
      have hv : v = a := by omega
      subst hu hv
      simp only [Finset.coe_image, Finset.coe_range, mem_image, mem_Iio]
      exact ⟨k, he, rfl⟩
    have h2 := Set.ncard_le_ncard hsub' (Finset.finite_toSet _)
    rw [Set.ncard_coe_finset] at h2
    exact h2.trans (Finset.card_image_le.trans (by simp))
  · refine h1.trans ((Finset.card_union_le _ _).trans ?_)
    exact Nat.add_le_add (Finset.card_image_le.trans (by simp))
      (Finset.card_image_le.trans (by simp))

section Model

variable {n : ℕ} (G : MultiDigraph n) (δ : ℕ) (I : Set (ℕ × ℕ × ℕ))

/-- The edges kept for connectivity: for each pair of distinct vertices joined by an edge of `G`
outside `I`, the one such edge with the least `key`. -/
def tree : Set (ℕ × ℕ × ℕ) :=
  {e | e ∈ E(G.toGMDigraph.toGraph) ∧ e ∉ I ∧ lo e < hi e ∧
    ∀ f, f ∈ E(G.toGMDigraph.toGraph) → f ∉ I → lo f = lo e → hi f = hi e → key e ≤ key f}

/-- The edges used by the model: those in `I` and the chosen edges of `tree`. -/
def used : Set (ℕ × ℕ × ℕ) := I ∪ tree G I

/-- The used edges with the same ends as `e`. -/
def cls (e : ℕ × ℕ × ℕ) : Set (ℕ × ℕ × ℕ) := {f | f ∈ used G I ∧ lo f = lo e ∧ hi f = hi e}

/-- The position of `e` among the used edges with the same ends, ordered by `key`. -/
noncomputable def rank (e : ℕ × ℕ × ℕ) : ℕ :=
  {f | f ∈ used G I ∧ lo f = lo e ∧ hi f = hi e ∧ key f < key e}.ncard

/-- The edge of `G.capPair δ` that replaces the used edge `e`: the edge with the same ends whose
position among the edges of `G.capPair δ` with these ends is `rank e`. -/
noncomputable def φ (e : ℕ × ℕ × ℕ) : ℕ × ℕ × ℕ :=
  if rank G I e < mult (G.capPair δ) (lo e) (hi e) then (lo e, hi e, rank G I e)
  else (hi e, lo e, rank G I e - mult (G.capPair δ) (lo e) (hi e))

theorem lo_φ (e : ℕ × ℕ × ℕ) : lo (φ G δ I e) = lo e := by
  have := lo_le_hi e
  unfold φ; split_ifs <;> simp only [lo, hi] at * <;> omega

theorem hi_φ (e : ℕ × ℕ × ℕ) : hi (φ G δ I e) = hi e := by
  have := lo_le_hi e
  unfold φ; split_ifs <;> simp only [lo, hi] at * <;> omega

/-- Two chosen edges with the same ends are equal. -/
theorem tree_eq {t t' : ℕ × ℕ × ℕ} (ht : t ∈ tree G I) (ht' : t' ∈ tree G I)
    (hlo : lo t' = lo t) (hhi : hi t' = hi t) : t = t' :=
  key_injective (le_antisymm (ht.2.2.2 t' ht'.1 ht'.2.1 hlo hhi)
    (ht'.2.2.2 t ht.1 ht.2.1 hlo.symm hhi.symm))

/-- An edge outside `I` between distinct vertices gives a chosen edge with the same ends. -/
theorem exists_tree {f : ℕ × ℕ × ℕ} (hf : f ∈ E(G.toGMDigraph.toGraph)) (hfI : f ∉ I)
    (hlt : lo f < hi f) : ∃ t ∈ tree G I, lo t = lo f ∧ hi t = hi f := by
  classical
  let P : ℕ → Prop := fun k => ∃ g, g ∈ E(G.toGMDigraph.toGraph) ∧ g ∉ I ∧ lo g = lo f ∧
    hi g = hi f ∧ key g = k
  have hP : ∃ k, P k := ⟨key f, f, hf, hfI, rfl, rfl, rfl⟩
  obtain ⟨t, ht, htI, htlo, hthi, htk⟩ := Nat.find_spec hP
  refine ⟨t, ⟨ht, htI, by omega, fun g hg hgI hglo hghi => ?_⟩, htlo, hthi⟩
  rw [htk]
  exact Nat.find_min' hP ⟨g, hg, hgI, hglo.trans htlo, hghi.trans hthi, rfl⟩

variable (hIE : I ⊆ E(G.toGMDigraph.toGraph))
include hIE

theorem used_subset : used G I ⊆ E(G.toGMDigraph.toGraph) :=
  union_subset hIE fun _ he => he.1

theorem used_finite : (used G I).Finite :=
  G.isFinite_toGMDigraph.finite_E.subset (used_subset G I hIE)

theorem cls_finite (e : ℕ × ℕ × ℕ) : (cls G I e).Finite :=
  (used_finite G I hIE).subset fun _ hf => hf.1

/-- The rank of a used edge is less than the number of used edges with its ends. -/
theorem rank_lt_ncard_cls {e : ℕ × ℕ × ℕ} (he : e ∈ used G I) :
    rank G I e < (cls G I e).ncard := by
  apply Set.ncard_lt_ncard _ (cls_finite G I hIE e)
  refine ⟨fun f hf => ⟨hf.1, hf.2.1, hf.2.2.1⟩, fun hsub => ?_⟩
  have := (hsub ⟨he, rfl, rfl⟩).2.2.2
  exact Nat.lt_irrefl _ this

/-- A strictly smaller key gives a strictly smaller rank, among edges with the same ends. -/
theorem rank_lt_rank {e e' : ℕ × ℕ × ℕ} (he : e ∈ used G I) (hlo : lo e = lo e')
    (hhi : hi e = hi e') (hk : key e < key e') : rank G I e < rank G I e' := by
  apply Set.ncard_lt_ncard _ ((used_finite G I hIE).subset fun _ hf => hf.1)
  refine ⟨fun f hf => ⟨hf.1, hf.2.1.trans hlo, hf.2.2.1.trans hhi, hf.2.2.2.trans hk⟩,
    fun hsub => ?_⟩
  have := (hsub ⟨he, hlo, hhi, hk⟩).2.2.2
  exact Nat.lt_irrefl _ this

/-- At most one chosen edge has given ends, and none is a loop, so the used edges with the ends of
`e` number at most `I.ncard + 1`, and at most `I.ncard` when `e` is a loop. -/
theorem ncard_cls_le (e : ℕ × ℕ × ℕ) (hIfin : I.Finite) :
    (cls G I e).ncard ≤ if lo e = hi e then I.ncard else I.ncard + 1 := by
  have hsplit : cls G I e ⊆ I ∪ {f | f ∈ tree G I ∧ lo f = lo e ∧ hi f = hi e} := by
    rintro f ⟨hf | hf, hlo, hhi⟩
    · exact Or.inl hf
    · exact Or.inr ⟨hf, hlo, hhi⟩
  have hTfin : {f | f ∈ tree G I ∧ lo f = lo e ∧ hi f = hi e}.Finite :=
    (used_finite G I hIE).subset fun f hf => Or.inr hf.1
  have hT : {f | f ∈ tree G I ∧ lo f = lo e ∧ hi f = hi e}.ncard ≤
      if lo e = hi e then 0 else 1 := by
    split_ifs with hl
    · have hempty : {f | f ∈ tree G I ∧ lo f = lo e ∧ hi f = hi e} = ∅ := by
        ext f
        simp only [mem_ofPred_eq, mem_empty_iff_false, iff_false]
        rintro ⟨hf, hlo, hhi⟩
        have := hf.2.2.1
        omega
      rw [hempty, Set.ncard_empty]
    · apply (Set.ncard_le_one hTfin).mpr
      rintro f ⟨hf, hflo, hfhi⟩ g ⟨hg, hglo, hghi⟩
      exact tree_eq G I hf hg (hglo.trans hflo.symm) (hghi.trans hfhi.symm)
  have h := (Set.ncard_le_ncard hsplit (hIfin.union hTfin)).trans
    (Set.ncard_union_le _ _)
  split_ifs at hT ⊢ <;> omega

/-- The used edges with the ends of `e` number at most the edges of `G` with these ends. -/
theorem ncard_cls_le_mult (e : ℕ × ℕ × ℕ) :
    (cls G I e).ncard ≤
      if lo e = hi e then mult G (lo e) (lo e) else mult G (lo e) (hi e) + mult G (hi e) (lo e) := by
  have hsub : cls G I e ⊆ {f | f ∈ E(G.toGMDigraph.toGraph) ∧ lo f = lo e ∧ hi f = hi e} :=
    fun f hf => ⟨used_subset G I hIE hf.1, hf.2.1, hf.2.2⟩
  refine (Set.ncard_le_ncard hsub ?_).trans ?_
  · exact G.isFinite_toGMDigraph.finite_E.subset fun f hf => hf.1
  · have h := ncard_ends_le G (lo e) (hi e)
    split_ifs at h ⊢ with hl
    · exact hl ▸ h
    · exact h

variable (hIδ : I.ncard ≤ δ) (hIfin : I.Finite)
include hIδ hIfin

/-- Every used edge is sent to an edge of `G.capPair δ`. -/
theorem φ_mem {e : ℕ × ℕ × ℕ} (he : e ∈ used G I) :
    φ G δ I e ∈ E((G.capPair δ).toGMDigraph.toGraph) := by
  have hr := rank_lt_ncard_cls G I hIE he
  have h1 := ncard_cls_le G I hIE e hIfin
  have h2 := ncard_cls_le_mult G I hIE e
  have hle := lo_le_hi e
  rw [mem_edgeSet_iff]
  unfold φ
  by_cases hl : lo e = hi e
  · rw [ite_pos' hl] at h1 h2
    have hc := mult_capPair_loop δ G (lo e)
    have hlt : rank G I e < mult (G.capPair δ) (lo e) (lo e) := by rw [hc]; omega
    rw [← hl, ite_pos' hlt]
    exact hlt
  · rw [ite_neg' hl] at h1 h2
    have hlt : lo e < hi e := lt_of_le_of_ne hle hl
    have hc := mult_capPair_add δ G hlt
    split_ifs with hrk
    · exact hrk
    · simp only
      omega

/-- The map `φ` is one-to-one on the used edges. -/
theorem φ_injOn : InjOn (φ G δ I) (used G I) := by
  intro e he e' he' heq
  have hlo : lo e = lo e' := by rw [← lo_φ G δ I e, heq, lo_φ]
  have hhi : hi e = hi e' := by rw [← hi_φ G δ I e, heq, hi_φ]
  have hr := rank_lt_ncard_cls G I hIE he
  have h1 := ncard_cls_le G I hIE e hIfin
  have h2 := ncard_cls_le_mult G I hIE e
  have hr' := rank_lt_ncard_cls G I hIE he'
  have h1' := ncard_cls_le G I hIE e' hIfin
  have h2' := ncard_cls_le_mult G I hIE e'
  rw [← hlo, ← hhi] at h1' h2'
  have hrank : rank G I e = rank G I e' := by
    unfold φ at heq
    rw [← hlo, ← hhi] at heq
    by_cases hl : lo e = hi e
    · rw [ite_pos' hl] at h1 h2 h1' h2'
      have hc := mult_capPair_loop δ G (lo e)
      have hlt : rank G I e < mult (G.capPair δ) (lo e) (hi e) := by rw [← hl, hc]; omega
      have hlt' : rank G I e' < mult (G.capPair δ) (lo e) (hi e) := by rw [← hl, hc]; omega
      rw [ite_pos' hlt] at heq
      rw [ite_pos' hlt'] at heq
      simp only [Prod.mk.injEq] at heq; exact heq.2.2
    · split_ifs at heq with ha hb hb <;> simp only [Prod.mk.injEq] at heq <;> omega
  rcases lt_trichotomy (key e) (key e') with hk | hk | hk
  · exact absurd hrank (Nat.ne_of_lt (rank_lt_rank G I hIE he hlo hhi hk))
  · exact key_injective hk
  · exact absurd hrank.symm (Nat.ne_of_lt (rank_lt_rank G I hIE he' hlo.symm hhi.symm hk))

end Model

end PairCapMinor

open PairCapMinor in
/-- The argument behind "as is easily seen" in Step (1) of Graph Minors XIII, (4.3), page 77:
a graph with at most `δ` edges that is a minor of `G` is a minor of `G.capPair δ`. -/
theorem isIsoMinor_capPair {α' β' : Type*} {n : ℕ} (δ : ℕ) (G : MultiDigraph n)
    (H : Graph α' β') (hVH : V(H).Finite) (hEH : E(H).Finite) (hδ : E(H).ncard ≤ δ)
    (h : IsIsoMinor H G.toGMDigraph.toGraph) :
    IsIsoMinor H (G.capPair δ).toGMDigraph.toGraph := by
  classical
  obtain ⟨ηv, ηe, hm⟩ := exists_isMinorModel_of_isIsoMinor G.isFinite_toGMDigraph.finite_V
    G.isFinite_toGMDigraph.finite_E h
  set G₀ := G.toGMDigraph.toGraph with hG₀
  set G₁ := (G.capPair δ).toGMDigraph.toGraph with hG₁
  let I := ηe '' E(H)
  have hIE : I ⊆ E(G₀) := by rintro _ ⟨e, he, rfl⟩; exact hm.edge_mem e he
  have hIfin : I.Finite := hEH.image _
  have hIδ : I.ncard ≤ δ := (Set.ncard_image_le hEH).trans hδ
  let ψ := φ G δ I
  have hIused : I ⊆ used G I := subset_union_left
  -- links are preserved by `ψ` on the used edges
  have hlink : ∀ e ∈ used G I, ∀ x y, G₀.IsLink e x y ↔ G₁.IsLink (ψ e) x y := fun e he x y =>
    isLink_iff_of_ends (used_subset G I hIE he) (φ_mem G δ I hIE hIδ hIfin he)
      (lo_φ G δ I e) (hi_φ G δ I e) x y
  have hinc : ∀ e ∈ used G I, ∀ x, G₀.Inc e x ↔ G₁.Inc (ψ e) x := fun e he x =>
    ⟨fun ⟨y, hy⟩ => ⟨y, (hlink e he x y).mp hy⟩, fun ⟨y, hy⟩ => ⟨y, (hlink e he x y).mpr hy⟩⟩
  have hV : V(G₁) = V(G₀) := rfl
  refine isIsoMinor_of_isMinorModel H G₁ hVH hEH (G.capPair δ).isFinite_toGMDigraph.finite_V
    (G.capPair δ).isFinite_toGMDigraph.finite_E ηv (ψ ∘ ηe) ?_
  refine
    { vertex_nonempty := hm.vertex_nonempty
      vertex_subset := fun v hv => hV ▸ hm.vertex_subset v hv
      edge_mem := fun e he => φ_mem G δ I hIE hIδ hIfin (hIused ⟨e, he, rfl⟩)
      vertex_disjoint := hm.vertex_disjoint
      edge_injOn := fun e he e' he' heq =>
        hm.edge_injOn he he' (φ_injOn G δ I hIE hIδ hIfin (hIused ⟨e, he, rfl⟩)
          (hIused ⟨e', he', rfl⟩) heq)
      inc_iff := fun v hv e he => by
        rw [hm.inc_iff v hv e he]
        simp only [Function.comp_apply]
        exact exists_congr fun x => and_congr_right fun _ =>
          hinc (ηe e) (hIused ⟨e, he, rfl⟩) x
      isLoopAt_iff := fun v hv e he => by
        rw [hm.isLoopAt_iff v hv e he]
        simp only [Function.comp_apply]
        exact forall_congr' fun x => imp_congr_left (hinc (ηe e) (hIused ⟨e, he, rfl⟩) x)
      connected := fun v hv => ?_ }
  obtain ⟨K, hK, hVK, hKc⟩ := hm.connected v hv
  refine ⟨(G₁.induce (ηv v)).deleteEdges ((ψ ∘ ηe) '' E(H)), ?_, rfl, ?_⟩
  · exact deleteEdges_mono_left (induce_le (hV ▸ hm.vertex_subset v hv)) _
  · refine ⟨hm.vertex_nonempty v hv, fun x hx y hy => ?_⟩
    have hx' : x ∈ V(K) := hVK ▸ hx
    have hy' : y ∈ V(K) := hVK ▸ hy
    -- each step of a walk of `K` is replaced by a chosen edge
    have hstep : ∀ a b, K.Adj a b →
        Relation.ReflTransGen ((G₁.induce (ηv v)).deleteEdges ((ψ ∘ ηe) '' E(H))).Adj a b := by
      intro a b hadj
      obtain ⟨f, hf⟩ := hadj
      have hf : K.IsLink f a b := hf
      have ha : a ∈ V(K) := hf.left_mem
      have hb : b ∈ V(K) := hf.right_mem
      by_cases hab : a = b
      · rw [hab]
      · have hf₀ : (G₀.deleteEdges I).IsLink f a b := hf.mono hK
        have hfE : f ∈ E(G₀) := hf₀.edge_mem.1
        have hfI : f ∉ I := hf₀.edge_mem.2
        have hfl : G₀.IsLink f a b := hf₀.1
        have hfl' := (isLink_iff G f a b).mp hfl
        have hlt : lo f < hi f := by
          have := lo_le_hi f
          rcases hfl'.2 with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> omega
        obtain ⟨t, ht, htlo, hthi⟩ := exists_tree G I hfE hfI hlt
        have htu : t ∈ used G I := subset_union_right ht
        have htl : G₀.IsLink t a b := by
          rw [isLink_iff, htlo, hthi]; exact ⟨ht.1, hfl'.2⟩
        have hψl : G₁.IsLink (ψ t) a b := (hlink t htu a b).mp htl
        have hnot : ψ t ∉ (ψ ∘ ηe) '' E(H) := by
          rintro ⟨e, he, heq⟩
          have := φ_injOn G δ I hIE hIδ hIfin (hIused ⟨e, he, rfl⟩) htu heq
          exact ht.2.1 (this ▸ ⟨e, he, rfl⟩)
        refine Relation.ReflTransGen.single ⟨ψ t, ?_⟩
        exact ⟨⟨hψl, hVK ▸ ha, hVK ▸ hb⟩, hnot⟩
    have hall : ∀ z, Relation.ReflTransGen K.Adj x z →
        Relation.ReflTransGen ((G₁.induce (ηv v)).deleteEdges ((ψ ∘ ηe) '' E(H))).Adj x z := by
      intro z hz
      induction hz with
      | refl => exact Relation.ReflTransGen.refl
      | tail _ hab ih => exact ih.trans (hstep _ _ hab)
    exact hall y (hKc.2 x hx' y hy')

/-- Step (1) of Graph Minors XIII, (4.3), page 77: "Then $G_1 \in \mathcal{F}$ if and only if
$G \in \mathcal{F}$, as is easily seen", for `G₁ = G.capPair δ` (the corrected cutoff; see the
correction to (4.3), Step (1), in
`corrections/GM13.md`). The class is given by a finite list of excluded minors with at most `δ`
edges, as in
the proof of (4.3). -/
theorem membership_capPair43
    (ℱ : Set (Graph ℕ (ℕ × ℕ × ℕ))) (B : Finset (Graph ℕ (ℕ × ℕ × ℕ))) (δ : ℕ)
    (hB : ∀ H ∈ B, V(H).Finite ∧ E(H).Finite ∧ V(H).ncard ≤ δ ∧ E(H).ncard ≤ δ)
    (hclass : ∀ G : Graph ℕ (ℕ × ℕ × ℕ), V(G).Finite → E(G).Finite →
      (G ∈ ℱ ↔ ∀ H ∈ B, ¬ IsIsoMinor H G))
    {n : ℕ} (G : MultiDigraph n) :
    G.toGMDigraph.toGraph ∈ ℱ ↔ (G.capPair δ).toGMDigraph.toGraph ∈ ℱ := by
  rw [hclass _ G.isFinite_toGMDigraph.finite_V G.isFinite_toGMDigraph.finite_E,
    hclass _ (G.capPair δ).isFinite_toGMDigraph.finite_V
      (G.capPair δ).isFinite_toGMDigraph.finite_E]
  apply forall₂_congr
  intro H hHB
  have hh := hB H hHB
  refine not_congr ⟨isIsoMinor_capPair δ G H hh.1 hh.2.1 hh.2.2.2, fun h => h.trans ?_⟩
  -- `G.capPair δ` is a subgraph of `G`
  have hgraph : (G.capPair δ).toGMDigraph.toGraph ≤ G.toGMDigraph.toGraph := by
    refine ⟨Subset.rfl, ?_⟩
    intro e x y he
    rcases he with ⟨⟨hu, hv, he⟩, hends⟩
    exact ⟨⟨hu, hv, he.trans_le (G.capPair_le δ _ _)⟩, hends⟩
  obtain ⟨K, hK, C, hC, hIso⟩ := IsIsoMinor.refl (G.capPair δ).toGMDigraph.toGraph
  exact ⟨K, hK.trans hgraph, C, hC, hIso⟩

end GraphMinor.Compute
