module

public import GraphMinor.Compute.BitSet
public import GraphMinor.Compute.BFS
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Subgraph

/-!
# Vertex Neighborhoods, Degrees into a Subset, and Edge-Meeting Bounds

This file develops reusable combinatorics and Word RAM subroutines for maintaining a vertex subset
`X : Finset (Fin n)`, its external neighborhood `extNeighborhood G X`, and vertex degrees into a
subset `degInto G S u`:

1. `extNeighborhood G X`: vertices in `V(G) \ X` adjacent in `G` to at least one vertex of `X`.
2. `degInto G S u`: number of neighbors of `u` in `G` that belong to `S`.
3. `edgesMetBy G X`: edges of `G` with at least one endpoint in `X`, together with the exact
   recurrence when `X` is expanded by a vertex `v ∈ extNeighborhood G X`.
4. Connectedness preservation for induced subgraphs `G.induce (X : Set (Fin n))` when starting from
   a singleton `{v₀}` and repeatedly adding vertices from `extNeighborhood G X`.
5. Word RAM programs `initSingletonNeighborhoodProg`, `expandNeighborhoodProg`,
   `computeDegIntoProg`, and `findLowDegVertexProg`.
-/

@[expose] public section

namespace GraphMinor.Compute

open scoped BigOperators

/-! ### Section 1: Pure Definitions and Combinatorial Lemmas -/

/-- The external neighborhood `N(X)` of `X ⊆ V(G)`: the set of vertices in `V(G) \ X` that have at
least one neighbor in `X`. -/
noncomputable def extNeighborhood {n : ℕ} (G : SimpleGraph (Fin n))
    (X : Finset (Fin n)) : Finset (Fin n) :=
  haveI := Classical.decRel G.Adj
  Finset.univ.filter (fun v => v ∉ X ∧ ∃ u ∈ X, G.Adj u v)

@[simp]
theorem mem_extNeighborhood {n : ℕ} (G : SimpleGraph (Fin n))
    (X : Finset (Fin n)) (v : Fin n) :
    v ∈ extNeighborhood G X ↔ v ∉ X ∧ ∃ u ∈ X, G.Adj u v := by
  classical
  simp [extNeighborhood]

theorem disjoint_extNeighborhood {n : ℕ} (G : SimpleGraph (Fin n)) (X : Finset (Fin n)) :
    Disjoint X (extNeighborhood G X) := by
  rw [Finset.disjoint_left]
  intro u hu hN
  exact (mem_extNeighborhood G X u).mp hN |>.1 hu

/-- Number of neighbors of `u` in `G` that lie in `S`. -/
noncomputable def degInto {n : ℕ} (G : SimpleGraph (Fin n))
    (S : Finset (Fin n)) (u : Fin n) : ℕ :=
  haveI := Classical.decRel G.Adj
  (Finset.univ.filter (fun w : Fin n => w ∈ S ∧ G.Adj u w)).card

theorem degInto_le_n {n : ℕ} (G : SimpleGraph (Fin n)) (S : Finset (Fin n)) (u : Fin n) :
    degInto G S u ≤ n := by
  classical
  unfold degInto
  calc (Finset.univ.filter (fun w : Fin n => w ∈ S ∧ G.Adj u w)).card
      ≤ (Finset.univ : Finset (Fin n)).card := Finset.card_filter_le _ _
    _ = n := Fintype.card_fin n

/-- The set of edges of `G` with at least one endpoint in `X`. -/
noncomputable def edgesMetBy {n : ℕ} (G : SimpleGraph (Fin n))
    (X : Finset (Fin n)) : Finset (Sym2 (Fin n)) :=
  haveI := Classical.decRel G.Adj
  haveI := Classical.decPred (fun e : Sym2 (Fin n) => ∃ u ∈ X, u ∈ e)
  G.edgeFinset.filter (fun e => ∃ u ∈ X, u ∈ e)

@[simp]
theorem mem_edgesMetBy {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (X : Finset (Fin n)) (e : Sym2 (Fin n)) :
    e ∈ edgesMetBy G X ↔ e ∈ G.edgeFinset ∧ ∃ u ∈ X, u ∈ e := by
  classical
   unfold edgesMetBy
  convert Finset.mem_filter

/-- The set of edges of `G` with both endpoints in `Y`. -/
noncomputable def edgesInSet {n : ℕ} (G : SimpleGraph (Fin n))
    (Y : Finset (Fin n)) : Finset (Sym2 (Fin n)) :=
  haveI := Classical.decRel G.Adj
  haveI := Classical.decPred (fun e : Sym2 (Fin n) => ∀ u ∈ e, u ∈ Y)
  G.edgeFinset.filter (fun e => ∀ u ∈ e, u ∈ Y)

@[simp]
theorem mem_edgesInSet {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (Y : Finset (Fin n)) (e : Sym2 (Fin n)) :
    e ∈ edgesInSet G Y ↔ e ∈ G.edgeFinset ∧ ∀ u ∈ e, u ∈ Y := by
  classical
  unfold edgesInSet
  convert Finset.mem_filter

/-- The induced subgraph of `G` on a singleton `{v₀}` is connected. -/
theorem connected_induce_singleton {n : ℕ} (G : SimpleGraph (Fin n)) (v₀ : Fin n) :
    (G.induce (({v₀} : Finset (Fin n)) : Set (Fin n))).Connected := by
  rw [SimpleGraph.connected_iff]
  refine ⟨?_, ⟨⟨v₀, by simp⟩⟩⟩
  rintro ⟨u, hu⟩ ⟨w, hw⟩
  simp only [Finset.coe_singleton, Set.mem_singleton_iff] at hu hw
  subst hu hw
  exact SimpleGraph.Reachable.refl _

/-- Expanding a connected vertex set `X` by a vertex `v ∈ extNeighborhood G X` preserves
connectedness of the induced subgraph `G.induce (X : Set (Fin n))`. -/
theorem connected_induce_insert_of_mem_extNeighborhood {n : ℕ}
    {G : SimpleGraph (Fin n)} {X : Finset (Fin n)} {v : Fin n}
    (hconn : (G.induce (X : Set (Fin n))).Connected)
    (hv : v ∈ extNeighborhood G X) :
    (G.induce ((insert v X : Finset (Fin n)) : Set (Fin n))).Connected := by
  rcases (mem_extNeighborhood G X v).mp hv with ⟨_, u, huX, hadj⟩
  have hsingle : (G.induce ({v} : Set (Fin n))).Connected := by
    simp
  have hunion : (G.induce ((X : Set (Fin n)) ∪ {v})).Connected :=
    G.connected_induce_union hconn.preconnected hsingle.preconnected huX (Set.mem_singleton v) hadj
  have hset : ((insert v X : Finset (Fin n)) : Set (Fin n)) = (X : Set (Fin n)) ∪ {v} := by
    ext x
    simp
  rwa [hset]

/-- Exact set decomposition of `extNeighborhood G (insert v X)` when `v ∈ extNeighborhood G X`:
it is the disjoint union of `extNeighborhood G X \ {v}` and the neighbors of `v` outside
`X ∪ extNeighborhood G X`. -/
theorem extNeighborhood_insert_eq_union {n : ℕ} (G : SimpleGraph (Fin n))
    (X : Finset (Fin n)) {v : Fin n} (hv : v ∈ extNeighborhood G X) :
    haveI := Classical.decRel G.Adj
    extNeighborhood G (insert v X) =
      (extNeighborhood G X).erase v ∪
        Finset.univ.filter (fun w => w ∈ Finset.univ \ (X ∪ extNeighborhood G X) ∧ G.Adj v w) := by
  classical
  ext w
  rw [mem_extNeighborhood]
  simp only [Finset.mem_insert, not_or, Finset.mem_union,
    Finset.mem_erase, Finset.mem_filter, Finset.mem_univ, Finset.mem_sdiff, true_and]
  constructor
  · rintro ⟨⟨hw_ne_v, hw_not_X⟩, u, rfl | huX, hadj⟩
    · by_cases hw_N : w ∈ extNeighborhood G X
      · exact Or.inl ⟨hw_ne_v, hw_N⟩
      · exact Or.inr ⟨⟨hw_not_X, hw_N⟩, hadj⟩
    · exact Or.inl ⟨hw_ne_v, (mem_extNeighborhood G X w).mpr ⟨hw_not_X, u, huX, hadj⟩⟩
  · rintro (⟨hw_ne_v, hw_N⟩ | ⟨⟨hw_not_X, hw_not_N⟩, hadj⟩)
    · rcases (mem_extNeighborhood G X w).mp hw_N with ⟨hw_not_X, u, huX, hadj⟩
      exact ⟨⟨hw_ne_v, hw_not_X⟩, u, Or.inr huX, hadj⟩
    · have hw_ne_v : w ≠ v := fun h => G.loopless.irrefl v (h ▸ hadj)
      exact ⟨⟨hw_ne_v, hw_not_X⟩, v, Or.inl rfl, hadj⟩

/-- Cardinality recurrence for `extNeighborhood G (insert v X)` when `v ∈ extNeighborhood G X`:
`|N(X ∪ {v})| + 1 = |N(X)| + d₂`, where `d₂` is the number of neighbors of `v` outside
`X ∪ N(X)`. -/
theorem card_extNeighborhood_insert {n : ℕ} (G : SimpleGraph (Fin n))
    (X : Finset (Fin n)) {v : Fin n} (hv : v ∈ extNeighborhood G X) :
    (extNeighborhood G (insert v X)).card + 1 =
      (extNeighborhood G X).card + degInto G (Finset.univ \ (X ∪ extNeighborhood G X)) v := by
  classical
  have heq := extNeighborhood_insert_eq_union G X hv
  have hdisj : Disjoint ((extNeighborhood G X).erase v)
      (Finset.univ.filter (fun w => w ∈ Finset.univ \ (X ∪ extNeighborhood G X) ∧ G.Adj v w)) := by
    rw [Finset.disjoint_left]
    intro w hw₁ hw₂
    have hwN : w ∈ extNeighborhood G X := Finset.mem_of_mem_erase hw₁
    simp only [Finset.mem_filter, Finset.mem_univ, Finset.mem_sdiff, Finset.mem_union,
      true_and, not_or] at hw₂
    exact hw₂.1.2 hwN
  rw [heq, Finset.card_union_of_disjoint hdisj]
  have herase : ((extNeighborhood G X).erase v).card + 1 = (extNeighborhood G X).card :=
    Finset.card_erase_add_one hv
  unfold degInto
  omega

/-- For a singleton `{v₀}`, the edges met by `{v₀}` are in bijection with `extNeighborhood G {v₀}`. -/
theorem card_edgesMetBy_singleton {n : ℕ} (G : SimpleGraph (Fin n)) (v₀ : Fin n) :
    (edgesMetBy G {v₀}).card = (extNeighborhood G {v₀}).card := by
  classical
  unfold edgesMetBy
  symm
  refine Finset.card_bij (fun w _ => s(v₀, w)) ?_ ?_ ?_
  · intro w hw
    rcases (mem_extNeighborhood G {v₀} w).mp hw with ⟨_, u, hu, hadj⟩
    rw [Finset.mem_singleton] at hu
    subst u
    simp only [Finset.mem_filter, SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet]
    exact ⟨hadj, v₀, Finset.mem_singleton_self v₀, Sym2.mem_mk_left v₀ w⟩
  · intro w₁ _ w₂ _ heq
    rcases Sym2.eq_iff.mp heq with ⟨_, h⟩ | ⟨h1, h2⟩
    · exact h
    · exact h2.trans h1
  · intro e he
    simp only [Finset.mem_filter, SimpleGraph.mem_edgeFinset,
      Finset.mem_singleton, exists_eq_left] at he
    rcases he with ⟨he_edge, hv₀_mem⟩
    let w := Sym2.Mem.other hv₀_mem
    have he_eq : s(v₀, w) = e := Sym2.other_spec hv₀_mem
    rw [← he_eq, SimpleGraph.mem_edgeSet] at he_edge
    have hw_ne : w ≠ v₀ := G.ne_of_adj he_edge.symm
    refine ⟨w, ?_, he_eq⟩
    rw [mem_extNeighborhood]
    exact ⟨by simpa using hw_ne, v₀, Finset.mem_singleton_self v₀, he_edge⟩

/-- The set of edges met by `insert v X` but not by `X` is in bijection with the neighbors of `v`
outside `X`. -/
theorem card_edgesMetBy_sdiff {n : ℕ} (G : SimpleGraph (Fin n))
    (X : Finset (Fin n)) {v : Fin n} (hv : v ∉ X) :
    (edgesMetBy G (insert v X) \ edgesMetBy G X).card =
      degInto G (Finset.univ \ X) v := by
  classical
  unfold degInto edgesMetBy
  symm
  refine Finset.card_bij (fun w _ => s(v, w)) ?_ ?_ ?_
  · intro w hw
    simp only [Finset.mem_filter, Finset.mem_univ, Finset.mem_sdiff, true_and] at hw
    rcases hw with ⟨hw_not_X, hadj⟩
    simp only [Finset.mem_sdiff, Finset.mem_filter, SimpleGraph.mem_edgeFinset,
      SimpleGraph.mem_edgeSet, Finset.mem_insert]
    refine ⟨⟨hadj, v, Or.inl rfl, Sym2.mem_mk_left v w⟩, ?_⟩
    rintro ⟨_, u, huX, hu_mem⟩
    rcases Sym2.mem_iff.mp hu_mem with rfl | rfl
    · exact hv huX
    · exact hw_not_X huX
  · intro w₁ _ w₂ _ heq
    rcases Sym2.eq_iff.mp heq with ⟨_, h⟩ | ⟨h1, h2⟩
    · exact h
    · exact h2.trans h1
  · intro e he
    simp only [Finset.mem_sdiff, Finset.mem_filter, SimpleGraph.mem_edgeFinset,
      Finset.mem_insert, not_and] at he
    rcases he with ⟨⟨he_edge, u, rfl | huX, hu_mem⟩, hnot_X⟩
    · let w := Sym2.Mem.other hu_mem
      have he_eq : s(u, w) = e := Sym2.other_spec hu_mem
      rw [← he_eq, SimpleGraph.mem_edgeSet] at he_edge
      have hw_not_X : w ∉ X := by
        intro hwX
        rw [← he_eq] at hnot_X
        exact hnot_X he_edge ⟨w, hwX, Sym2.mem_mk_right u w⟩
      refine ⟨w, ?_, he_eq⟩
      simp [hw_not_X, he_edge]
    · exact False.elim (hnot_X he_edge ⟨u, huX, hu_mem⟩)

/-- For `v ∉ X`, the neighbors of `v` outside `X` partition into those in `extNeighborhood G X`
(`d₁`) and those outside `X ∪ extNeighborhood G X` (`d₂`). -/
theorem degInto_sdiff_eq_add {n : ℕ} (G : SimpleGraph (Fin n))
    (X : Finset (Fin n)) (v : Fin n) :
    degInto G (Finset.univ \ X) v =
      degInto G (extNeighborhood G X) v +
        degInto G (Finset.univ \ (X ∪ extNeighborhood G X)) v := by
  classical
  unfold degInto
  have hunion :
      Finset.univ.filter (fun w : Fin n => w ∈ Finset.univ \ X ∧ G.Adj v w) =
        Finset.univ.filter (fun w : Fin n => w ∈ extNeighborhood G X ∧ G.Adj v w) ∪
          Finset.univ.filter (fun w : Fin n =>
            w ∈ Finset.univ \ (X ∪ extNeighborhood G X) ∧ G.Adj v w) := by
    ext w
    simp only [Finset.mem_filter, Finset.mem_univ, Finset.mem_sdiff, Finset.mem_union,
      true_and, not_or]
    constructor
    · rintro ⟨hwX, hadj⟩
      by_cases hwN : w ∈ extNeighborhood G X
      · exact Or.inl ⟨hwN, hadj⟩
      · exact Or.inr ⟨⟨hwX, hwN⟩, hadj⟩
    · rintro (⟨hwN, hadj⟩ | ⟨⟨hwX, _⟩, hadj⟩)
      · exact ⟨(mem_extNeighborhood G X w).mp hwN |>.1, hadj⟩
      · exact ⟨hwX, hadj⟩
  have hdisj :
      Disjoint (Finset.univ.filter (fun w : Fin n => w ∈ extNeighborhood G X ∧ G.Adj v w))
        (Finset.univ.filter (fun w : Fin n =>
          w ∈ Finset.univ \ (X ∪ extNeighborhood G X) ∧ G.Adj v w)) := by
    rw [Finset.disjoint_left]
    intro w hw₁ hw₂
    simp only [Finset.mem_filter, Finset.mem_univ, Finset.mem_sdiff, Finset.mem_union,
      true_and, not_or] at hw₁ hw₂
    exact hw₂.1.2 hw₁.1
  rw [hunion, Finset.card_union_of_disjoint hdisj]

/-- Exact recurrence for the number of edges met by `insert v X` when `v ∉ X`:
`|edgesMetBy G (insert v X)| = |edgesMetBy G X| + d₁ + d₂`. -/
theorem card_edgesMetBy_insert {n : ℕ} (G : SimpleGraph (Fin n))
    (X : Finset (Fin n)) {v : Fin n} (hv : v ∉ X) :
    (edgesMetBy G (insert v X)).card =
      (edgesMetBy G X).card +
        degInto G (extNeighborhood G X) v +
        degInto G (Finset.univ \ (X ∪ extNeighborhood G X)) v := by
  classical
  have hsub : edgesMetBy G X ⊆ edgesMetBy G (insert v X) := by
    intro e he
    unfold edgesMetBy at he ⊢
    simp only [Finset.mem_filter, Finset.mem_insert] at he ⊢
    rcases he with ⟨he_edge, u, huX, hu_e⟩
    exact ⟨he_edge, u, Or.inr huX, hu_e⟩
  have hcard : (edgesMetBy G (insert v X)).card =
      (edgesMetBy G X).card + (edgesMetBy G (insert v X) \ edgesMetBy G X).card := by
    have := Finset.card_sdiff_add_card_eq_card hsub
    omega
  rw [hcard, card_edgesMetBy_sdiff G X hv, degInto_sdiff_eq_add G X v]
  omega

/-- Inductive step for the edge-meeting bound when adding `v ∈ extNeighborhood G X` with
`degInto G (extNeighborhood G X) v < k`:
if `|edgesMetBy G X| ≤ |N(X)| + k(i - 1)`, then
`|edgesMetBy G (insert v X)| ≤ |N(insert v X)| + k i`. -/
theorem card_edgesMetBy_insert_le {n : ℕ} (G : SimpleGraph (Fin n))
    (X : Finset (Fin n)) {v : Fin n} {k i : ℕ}
    (hi : 1 ≤ i)
    (hinv : (edgesMetBy G X).card ≤ (extNeighborhood G X).card + k * (i - 1))
    (hv : v ∈ extNeighborhood G X)
    (hdeg : degInto G (extNeighborhood G X) v < k) :
    (edgesMetBy G (insert v X)).card ≤ (extNeighborhood G (insert v X)).card + k * i := by
  have hv_not_X : v ∉ X := (mem_extNeighborhood G X v).mp hv |>.1
  have h1 := card_edgesMetBy_insert G X hv_not_X
  have h2 := card_extNeighborhood_insert G X hv
  have hmul : k * i = k * (i - 1) + k := by
    have : i = (i - 1) + 1 := by omega
    conv_lhs => rw [this]
    rw [Nat.mul_add, Nat.mul_one]
  omega

/-! ### Section 2: Word RAM Programs for Maintaining `X`, `N(X)`, and `degInto` -/

/-- State predicate stating that array `a_deg` of length `n` stores `degInto G S u` for every
`u : Fin n`. -/
def IsDegIntoArr {n : ℕ} (G : SimpleGraph (Fin n)) (S : Finset (Fin n))
    (a_deg : Arr) (s : State) : Prop :=
  ∃ hlen : (s.arrs a_deg).length = n,
    ∀ u : Fin n, (s.arrs a_deg)[u.1]'(by rw [hlen]; exact u.2) = degInto G S u

theorem IsDegIntoArr.of_arr_eq {n : ℕ} {G : SimpleGraph (Fin n)} {S : Finset (Fin n)}
    {a_deg : Arr} {s s' : State}
    (h : IsDegIntoArr G S a_deg s) (heq : s'.arrs a_deg = s.arrs a_deg) :
    IsDegIntoArr G S a_deg s' := by
  rcases h with ⟨hlen, hget⟩
  refine ⟨by rw [heq, hlen], fun u => ?_⟩
  simpa [heq] using hget u

/-- Pure list-prefix version of external neighborhood update: given a list `l` of neighbors of `v`,
`expandNeighborSet X N₀ v l k` inserts every `l[j]` (`j < k`) that is not in `insert v X` into `N₀`. -/
def expandNeighborSet {n : ℕ} (X N₀ : Finset (Fin n)) (v : Fin n) (l : List ℕ) (k : ℕ) :
    Finset (Fin n) :=
  N₀ ∪ Finset.univ.filter (fun w : Fin n => w.1 ∈ l.take k ∧ w ∉ insert v X)

@[simp]
theorem expandNeighborSet_zero {n : ℕ} (X N₀ : Finset (Fin n)) (v : Fin n) (l : List ℕ) :
    expandNeighborSet X N₀ v l 0 = N₀ := by
  ext w
  simp [expandNeighborSet]

theorem expandNeighborSet_succ {n : ℕ} (X N₀ : Finset (Fin n)) (v : Fin n) (l : List ℕ)
    {k : ℕ} (hk : k < l.length) (hw_lt : l[k] < n) :
    expandNeighborSet X N₀ v l (k + 1) =
      if (⟨l[k], hw_lt⟩ : Fin n) ∈ insert v X then
        expandNeighborSet X N₀ v l k
      else
        insert ⟨l[k], hw_lt⟩ (expandNeighborSet X N₀ v l k) := by
  split_ifs with hmem
  · ext u
    simp only [expandNeighborSet, take_add_one_eq_append_getElem l k hk, Finset.mem_union,
      Finset.mem_filter, Finset.mem_univ, List.mem_append, List.mem_singleton, true_and]
    constructor
    · rintro (huN | ⟨hu_take | hu_eq, hu_not⟩)
      · exact Or.inl huN
      · exact Or.inr ⟨hu_take, hu_not⟩
      · exfalso
        have : u = ⟨l[k], hw_lt⟩ := Fin.ext hu_eq
        exact hu_not (this ▸ hmem)
    · rintro (huN | ⟨hu_take, hu_not⟩)
      · exact Or.inl huN
      · exact Or.inr ⟨Or.inl hu_take, hu_not⟩
  · ext u
    rw [Finset.mem_insert]
    simp only [expandNeighborSet, take_add_one_eq_append_getElem l k hk,
      Finset.mem_union, Finset.mem_filter, Finset.mem_univ, List.mem_append, List.mem_singleton,
      true_and, Fin.ext_iff]
    constructor
    · rintro (huN | ⟨hu_take | hu_eq, hu_not⟩)
      · exact Or.inr (Or.inl huN)
      · exact Or.inr (Or.inr ⟨hu_take, hu_not⟩)
      · exact Or.inl hu_eq
    · rintro (hu_eq | huN | ⟨hu_take, hu_not⟩)
      · have hu_fin : u = ⟨l[k], hw_lt⟩ := Fin.ext hu_eq
        exact Or.inr ⟨Or.inr hu_eq, hu_fin ▸ hmem⟩
      · exact Or.inl huN
      · exact Or.inr ⟨Or.inl hu_take, hu_not⟩

theorem expandNeighborSet_full_eq_extNeighborhood_insert {n : ℕ}
    {G : SimpleGraph (Fin n)} {lists : Fin n → List ℕ}
    (hlists : IsAdjListFamily G lists)
    (X : Finset (Fin n)) {v : Fin n} (hv : v ∈ extNeighborhood G X) :
    expandNeighborSet X ((extNeighborhood G X).erase v) v (lists v) (lists v).length =
      extNeighborhood G (insert v X) := by
  have htake : (lists v).take (lists v).length = lists v := List.take_length
  ext u
  simp only [expandNeighborSet, htake, Finset.mem_union, Finset.mem_erase, Finset.mem_filter,
    Finset.mem_univ, true_and, (hlists v).2.2.2 u, mem_extNeighborhood, Finset.mem_insert, not_or]
  constructor
  · rintro (⟨hu_ne, hu_not_X, x, hxX, hadj⟩ | ⟨hadj, hu_ne, hu_not_X⟩)
    · exact ⟨⟨hu_ne, hu_not_X⟩, x, Or.inr hxX, hadj⟩
    · exact ⟨⟨hu_ne, hu_not_X⟩, v, Or.inl rfl, hadj⟩
  · rintro ⟨⟨hu_ne, hu_not_X⟩, x, rfl | hxX, hadj⟩
    · exact Or.inr ⟨hadj, hu_ne, hu_not_X⟩
    · exact Or.inl ⟨hu_ne, hu_not_X, x, hxX, hadj⟩

theorem expandNeighborSet_full_singleton {n : ℕ}
    {G : SimpleGraph (Fin n)} {lists : Fin n → List ℕ}
    (hlists : IsAdjListFamily G lists) (v₀ : Fin n) :
    expandNeighborSet ∅ ∅ v₀ (lists v₀) (lists v₀).length =
      extNeighborhood G {v₀} := by
  have htake : (lists v₀).take (lists v₀).length = lists v₀ := List.take_length
  ext u
  simp only [expandNeighborSet, htake, Finset.empty_union, Finset.mem_filter,
    Finset.mem_univ, true_and, (hlists v₀).2.2.2 u, mem_extNeighborhood, Finset.mem_singleton,
    exists_eq_left, Finset.insert_empty]
  exact and_comm

/-- Inner loop body for `expandNeighborhoodProg`: given neighbor `r_w = w` of `v`, reads
`r_xw := a_X[r_w]`; if `r_xw == 0`, sets `a_N[r_w] := 1`. -/
def expandNeighborhoodBody (a_X a_N : Arr) (r_w r_xw : Reg) : Cmd :=
  .seq (.assign r_xw (.read a_X (.reg r_w)))
    (.ite (.reg r_xw) .skip (.write a_N (.reg r_w) (.const 1)))

/-- Expand `(a_X, a_N)` when adding `r_v = v` to `X`:
1. Sets `a_X[r_v] := 1` and `a_N[r_v] := 0`.
2. Iterates over all neighbors `w ∈ lists v` via `forList` and sets `a_N[w] := 1` whenever
   `a_X[w] == 0`. -/
def expandNeighborhoodProg (a_start a_end a_entries a_X a_N : Arr)
    (r_v r_k r_hi r_w r_xw : Reg) : Cmd :=
  .seq (.write a_X (.reg r_v) (.const 1))
    (.seq (.write a_N (.reg r_v) (.const 0))
      (forList a_start a_end a_entries r_v r_k r_hi r_w
        (expandNeighborhoodBody a_X a_N r_w r_xw)))

/-- Initialize `a_X` to `{v₀}` (`v₀ = s.regs r_v`) and `a_N` to `extNeighborhood G {v₀}`. -/
def initSingletonNeighborhoodProg (a_start a_end a_entries a_X a_N : Arr)
    (r_n r_v r_k r_hi r_w r_xw : Reg) : Cmd :=
  .seq (.alloc a_X (.reg r_n))
    (.seq (.alloc a_N (.reg r_n))
      (expandNeighborhoodProg a_start a_end a_entries a_X a_N r_v r_k r_hi r_w r_xw))

theorem expandNeighborhoodForList_exec {w n : ℕ} (G : SimpleGraph (Fin n))
    (lists : Fin n → List ℕ) (X N₀ : Finset (Fin n)) (v : Fin n)
    (a_start a_end a_entries a_X a_N : ℕ)
    (r_v r_k r_hi r_w r_xw : ℕ)
    (hne_XN : a_X ≠ a_N)
    (hne_stN : a_start ≠ a_N) (hne_enN : a_end ≠ a_N) (hne_entN : a_entries ≠ a_N)
    (hne_kh : r_k ≠ r_hi) (hne_vk : r_v ≠ r_k) (hne_vh : r_v ≠ r_hi)
    (hne_vw : r_v ≠ r_w) (hne_vx : r_v ≠ r_xw)
    (hne_kw : r_k ≠ r_w) (hne_kx : r_k ≠ r_xw)
    (hne_hw : r_hi ≠ r_w) (hne_hx : r_hi ≠ r_xw)
    (hne_wx : r_w ≠ r_xw)
    (hw : 1 < 2 ^ w) (hn_w : n < 2 ^ w)
    (hlists : IsAdjListFamily G lists)
    {s : State}
    (hadj : IsAdjList G a_start a_end a_entries lists s)
    (hent_w : (s.arrs a_entries).length < 2 ^ w)
    (hX : IsBitSet (insert v X) a_X s)
    (hN₀ : IsBitSet N₀ a_N s)
    (hrv : s.regs r_v = v.1) :
    ∃ s' t,
      Exec w (forList a_start a_end a_entries r_v r_k r_hi r_w
        (expandNeighborhoodBody a_X a_N r_w r_xw)) s s' t ∧
      t ≤ 9 + 18 * (lists v).length ∧
      IsBitSet (insert v X) a_X s' ∧
      IsBitSet (expandNeighborSet X N₀ v (lists v) (lists v).length) a_N s' ∧
      (∀ a : Arr, a ≠ a_N → s'.arrs a = s.arrs a) ∧
      (∀ r : Reg, r ≠ r_k → r ≠ r_hi → r ≠ r_w → r ≠ r_xw → s'.regs r = s.regs r) := by
  have h0_w : 0 < 2 ^ w := by omega
  have hv_w : v.1 < 2 ^ w := by omega
  rcases hadj.1.2.2 v with ⟨st, en, hlist_v⟩
  have hen_le : en ≤ (s.arrs a_entries).length := hlist_v.2.2.1
  have hen_w : en < 2 ^ w := by omega
  have hwords : ∀ x ∈ lists v, x < 2 ^ w := by
    intro x hx
    have := (hlists v).1 x hx
    omega
  let Inv : ℕ → State → Prop := fun j st_j =>
    IsListAt a_start a_end a_entries v.1 st en (lists v) st_j ∧
    IsBitSet (insert v X) a_X st_j ∧
    IsBitSet (expandNeighborSet X N₀ v (lists v) j) a_N st_j ∧
    st_j.regs r_v = v.1 ∧
    (∀ a : Arr, a ≠ a_N → st_j.arrs a = s.arrs a) ∧
    (∀ r : Reg, r ≠ r_k → r ≠ r_hi → r ≠ r_w → r ≠ r_xw → st_j.regs r = s.regs r)
  have hspec :
      ⦃Inv 0⦄[w]
        forList a_start a_end a_entries r_v r_k r_hi r_w
          (expandNeighborhoodBody a_X a_N r_w r_xw)
      ⦃Inv (lists v).length⦄ ≤ fun _ => 9 + (lists v).length * (10 + 8) := by
    apply Triple.forList_const a_start a_end a_entries r_v r_k r_hi r_w
      v.1 st en (lists v) Inv 8 _ hne_kh hne_vk hw hv_w hen_w hwords
    · intro st₀ ⟨hlist₀, hX₀, hN₀', hrv₀, harr₀, hreg₀⟩
      refine ⟨hlist₀, hrv₀, hlist₀, hX₀, hN₀',
        by simp [State.setReg, show (r_v : Reg) ≠ r_hi by omega,
          show (r_v : Reg) ≠ r_k by omega, hrv₀],
        harr₀, ?_⟩
      intro r h1 h2 h3 h4
      simp [State.setReg, h1, h2, hreg₀ r h1 h2 h3 h4]
    · intro j _ st_j ⟨hlist_j, _⟩
      exact hlist_j
    · intro j hj st_w ⟨st_j, ⟨hlist_j, hX_j, hN_j, hrv_j, harr_j, hreg_j⟩, hst_w, hrk_j, hrhi_j⟩
      subst hst_w
      let w_val := (lists v)[j]
      have hw_lt : w_val < n := (hlists v).1 w_val (List.getElem_mem hj)
      have hw_w : w_val < 2 ^ w := by omega
      let wFin : Fin n := ⟨w_val, hw_lt⟩
      rcases hX_j with ⟨hX_len, hX_le, hX_mem⟩
      have hw_X_len : w_val < (st_j.arrs a_X).length := by rw [hX_len]; exact hw_lt
      let xw_val := (st_j.arrs a_X)[w_val]'hw_X_len
      have hxw_le : xw_val ≤ 1 := hX_le wFin
      have hxw_w : xw_val < 2 ^ w := by omega
      let s₁ := (st_j.setReg r_w w_val).setReg r_xw xw_val
      have hex₁ : Exec w (.assign r_xw (.read a_X (.reg r_w))) (st_j.setReg r_w w_val) s₁ 3 :=
        .assign (by simp [Expr.eval, checkWord, hw_w, hw_X_len, xw_val, hxw_w])
      have hcond_xw : (Expr.reg r_xw).eval w s₁ = some xw_val := by
        simp [s₁, Expr.eval, checkWord, hxw_w]
      have hstep_set := expandNeighborSet_succ X N₀ v (lists v) hj hw_lt
      by_cases hw_in_X : wFin ∈ insert v X
      · have hxw_ne : xw_val ≠ 0 := (hX_mem wFin).mpr hw_in_X
        have hex₂ : Exec w (.ite (.reg r_xw) .skip (.write a_N (.reg r_w) (.const 1)))
            s₁ s₁ (1 + 1) :=
          .ite_true hcond_xw hxw_ne (.skip s₁)
        refine ⟨s₁, 3 + (1 + 1), .seq hex₁ hex₂, by dsimp only; omega, ?_,
          by simp [s₁, State.setReg, show (r_k : Reg) ≠ r_xw by omega,
            show (r_k : Reg) ≠ r_w by omega, hrk_j],
          by simp [s₁, State.setReg, show (r_hi : Reg) ≠ r_xw by omega,
            show (r_hi : Reg) ≠ r_w by omega, hrhi_j]⟩
        dsimp only [Inv]
        have hw_in_X' : (⟨(lists v)[j], hw_lt⟩ : Fin n) ∈ insert v X := hw_in_X
        rw [hstep_set]
        simp only [hw_in_X', ↓reduceIte]
        refine ⟨hlist_j, ⟨hX_len, hX_le, hX_mem⟩, hN_j,
          by simp [s₁, State.setReg, show (r_v : Reg) ≠ r_k by omega,
            show (r_v : Reg) ≠ r_xw by omega, show (r_v : Reg) ≠ r_w by omega, hrv_j],
          harr_j, ?_⟩
        intro r h1 h2 h3 h4
        simp [s₁, State.setReg, h1, h3, h4, hreg_j r h1 h2 h3 h4]
      · have hxw_eq0 : xw_val = 0 := not_ne_iff.mp ((hX_mem wFin).not.mpr hw_in_X)
        have hcond0 : (Expr.reg r_xw).eval w s₁ = some 0 := by simpa [hxw_eq0] using hcond_xw
        have hw_N_len : w_val < (s₁.arrs a_N).length := by
          simp [s₁, hN_j.1, hw_lt]
        let s₂ := s₁.writeArr a_N w_val 1
        have hex_wr : Exec w (.write a_N (.reg r_w) (.const 1)) s₁ s₂ 3 :=
          .write
            (by simp [s₁, State.setReg, show (r_w : Reg) ≠ r_xw by omega,
              Expr.eval, checkWord, hw_w])
            (by simp [Expr.eval, checkWord, hw])
            hw_N_len
        have hex₂ : Exec w (.ite (.reg r_xw) .skip (.write a_N (.reg r_w) (.const 1)))
            s₁ s₂ (1 + 3) :=
          .ite_false hcond0 hex_wr
        have hN₂ : IsBitSet (insert wFin (expandNeighborSet X N₀ v (lists v) j)) a_N s₂ :=
          hN_j.write_one wFin
        refine ⟨s₂, 3 + (1 + 3), .seq hex₁ hex₂, by dsimp only; omega, ?_,
          by simp [s₂, s₁, State.setReg, show (r_k : Reg) ≠ r_xw by omega,
            show (r_k : Reg) ≠ r_w by omega, hrk_j],
          by simp [s₂, s₁, State.setReg, show (r_hi : Reg) ≠ r_xw by omega,
            show (r_hi : Reg) ≠ r_w by omega, hrhi_j]⟩
        dsimp only [Inv]
        have hw_in_X' : (⟨(lists v)[j], hw_lt⟩ : Fin n) ∉ insert v X := hw_in_X
        rw [hstep_set]
        simp only [hw_in_X', ↓reduceIte]
        have hne_stN' : (a_start : Arr) ≠ a_N := hne_stN
        have hne_enN' : (a_end : Arr) ≠ a_N := hne_enN
        have hne_entN' : (a_entries : Arr) ≠ a_N := hne_entN
        have hne_XN' : (a_X : Arr) ≠ a_N := hne_XN
        refine ⟨hlist_j.of_arrs_eq
            (by simp [s₂, s₁, hne_stN'])
            (by simp [s₂, s₁, hne_enN'])
            (by simp [s₂, s₁, hne_entN']),
          IsBitSet.of_arr_eq ⟨hX_len, hX_le, hX_mem⟩ (by simp [s₂, s₁, hne_XN']),
          hN₂,
          by simp [s₂, s₁, State.setReg, show (r_v : Reg) ≠ r_k by omega,
            show (r_v : Reg) ≠ r_xw by omega, show (r_v : Reg) ≠ r_w by omega, hrv_j],
          fun a ha => by simp [s₂, s₁, ha, harr_j a ha],
          ?_⟩
        intro r h1 h2 h3 h4
        simp [s₂, s₁, State.setReg, h1, h3, h4, hreg_j r h1 h2 h3 h4]
  have hinit : Inv 0 s := by
    refine ⟨hlist_v, hX, by simpa using hN₀, hrv, fun _ _ => rfl, fun _ _ _ _ _ => rfl⟩
  rcases hspec s hinit with ⟨s', t, hex, ht, _, hX', hN', _, harr', hreg'⟩
  dsimp only at ht
  exact ⟨s', t, hex, by omega, hX', hN', harr', hreg'⟩

/-- Execution theorem for `expandNeighborhoodProg`: given `X` in `a_X`, `extNeighborhood G X` in
`a_N`, and `v ∈ extNeighborhood G X` in `r_v`, updates `a_X` to `insert v X` and `a_N` to
`extNeighborhood G (insert v X)` in `O(1 + (lists v).length)` steps. -/
theorem expandNeighborhoodProg_exec {w n : ℕ} (G : SimpleGraph (Fin n))
    (lists : Fin n → List ℕ) (X : Finset (Fin n)) (v : Fin n)
    (a_start a_end a_entries a_X a_N : ℕ)
    (r_v r_k r_hi r_w r_xw : ℕ)
    (hne_XN : a_X ≠ a_N)
    (hne_stX : a_start ≠ a_X) (hne_enX : a_end ≠ a_X) (hne_entX : a_entries ≠ a_X)
    (hne_stN : a_start ≠ a_N) (hne_enN : a_end ≠ a_N) (hne_entN : a_entries ≠ a_N)
    (hne_kh : r_k ≠ r_hi) (hne_vk : r_v ≠ r_k) (hne_vh : r_v ≠ r_hi)
    (hne_vw : r_v ≠ r_w) (hne_vx : r_v ≠ r_xw)
    (hne_kw : r_k ≠ r_w) (hne_kx : r_k ≠ r_xw)
    (hne_hw : r_hi ≠ r_w) (hne_hx : r_hi ≠ r_xw)
    (hne_wx : r_w ≠ r_xw)
    (hw : 1 < 2 ^ w) (hn_w : n < 2 ^ w)
    (hv : v ∈ extNeighborhood G X)
    {s : State}
    (hadj : IsAdjList G a_start a_end a_entries lists s)
    (hent_w : (s.arrs a_entries).length < 2 ^ w)
    (hX : IsBitSet X a_X s)
    (hN : IsBitSet (extNeighborhood G X) a_N s)
    (hrv : s.regs r_v = v.1) :
    ∃ s' t,
      Exec w (expandNeighborhoodProg a_start a_end a_entries a_X a_N r_v r_k r_hi r_w r_xw) s s' t ∧
      t ≤ 15 + 18 * (lists v).length ∧
      IsBitSet (insert v X) a_X s' ∧
      IsBitSet (extNeighborhood G (insert v X)) a_N s' ∧
      (∀ a : Arr, a ≠ a_X → a ≠ a_N → s'.arrs a = s.arrs a) ∧
      (∀ r : Reg, r ≠ r_k → r ≠ r_hi → r ≠ r_w → r ≠ r_xw → s'.regs r = s.regs r) := by
  have h0_w : 0 < 2 ^ w := by omega
  have hv_w : v.1 < 2 ^ w := by omega
  let s₁ := s.writeArr a_X v.1 1
  have hex₁ : Exec w (.write a_X (.reg r_v) (.const 1)) s s₁ 3 :=
    .write (by simp [Expr.eval, checkWord, hrv, hv_w]) (by simp [Expr.eval, checkWord, hw])
      (by rw [hX.1]; exact v.2)
  let s₂ := s₁.writeArr a_N v.1 0
  have hex₂ : Exec w (.write a_N (.reg r_v) (.const 0)) s₁ s₂ 3 :=
    .write (by simp [s₁, Expr.eval, checkWord, hrv, hv_w]) (by simp [Expr.eval, checkWord, h0_w])
      (by simp [s₁, show (a_N : Arr) ≠ a_X from hne_XN.symm, hN.1, v.2])
  have hX₂ : IsBitSet (insert v X) a_X s₂ :=
    (hX.write_one v).of_arr_eq (by simp [s₂, s₁, show (a_X : Arr) ≠ a_N from hne_XN])
  have hN₂ : IsBitSet ((extNeighborhood G X).erase v) a_N s₂ :=
    (hN.of_arr_eq (by simp [s₁, show (a_N : Arr) ≠ a_X from hne_XN.symm])).write_zero v
  have harr₂ : ∀ a : Arr, a ≠ a_X → a ≠ a_N → s₂.arrs a = s.arrs a := by
    intro a haX haN
    simp [s₂, s₁, haX, haN]
  have hadj₂ : IsAdjList G a_start a_end a_entries lists s₂ :=
    hadj.of_arrs_eq (harr₂ _ hne_stX hne_stN) (harr₂ _ hne_enX hne_enN) (harr₂ _ hne_entX hne_entN)
  have hent₂ : (s₂.arrs a_entries).length < 2 ^ w := by
    rw [harr₂ _ hne_entX hne_entN]; exact hent_w
  rcases expandNeighborhoodForList_exec G lists X ((extNeighborhood G X).erase v) v
      a_start a_end a_entries a_X a_N r_v r_k r_hi r_w r_xw
      hne_XN hne_stN hne_enN hne_entN
      hne_kh hne_vk hne_vh hne_vw hne_vx hne_kw hne_kx hne_hw hne_hx hne_wx
      hw hn_w hadj.2 hadj₂ hent₂ hX₂ hN₂ hrv with
    ⟨s₃, t₃, hex₃, ht₃, hX₃, hN₃, harr₃, hreg₃⟩
  rw [expandNeighborSet_full_eq_extNeighborhood_insert hadj.2 X hv] at hN₃
  refine ⟨s₃, 3 + (3 + t₃), .seq hex₁ (.seq hex₂ hex₃), by omega, hX₃, hN₃,
    fun a haX haN => by rw [harr₃ a haN, harr₂ a haX haN],
    hreg₃⟩

/-- Execution theorem for `initSingletonNeighborhoodProg`: initializes `a_X` to `{v₀}` and `a_N` to
`extNeighborhood G {v₀}` in `O(n + (lists v₀).length)` steps. -/
theorem initSingletonNeighborhoodProg_exec {w n : ℕ} (G : SimpleGraph (Fin n))
    (lists : Fin n → List ℕ) (v₀ : Fin n)
    (a_start a_end a_entries a_X a_N : ℕ)
    (r_n r_v r_k r_hi r_w r_xw : ℕ)
    (hne_XN : a_X ≠ a_N)
    (hne_stX : a_start ≠ a_X) (hne_enX : a_end ≠ a_X) (hne_entX : a_entries ≠ a_X)
    (hne_stN : a_start ≠ a_N) (hne_enN : a_end ≠ a_N) (hne_entN : a_entries ≠ a_N)
    (hne_kh : r_k ≠ r_hi) (hne_vk : r_v ≠ r_k) (hne_vh : r_v ≠ r_hi)
    (hne_vw : r_v ≠ r_w) (hne_vx : r_v ≠ r_xw)
    (hne_kw : r_k ≠ r_w) (hne_kx : r_k ≠ r_xw)
    (hne_hw : r_hi ≠ r_w) (hne_hx : r_hi ≠ r_xw)
    (hne_wx : r_w ≠ r_xw)
    (hw : 1 < 2 ^ w) (hn_w : n < 2 ^ w)
    {s : State}
    (hadj : IsAdjList G a_start a_end a_entries lists s)
    (hent_w : (s.arrs a_entries).length < 2 ^ w)
    (hrn : s.regs r_n = n)
    (hrv : s.regs r_v = v₀.1) :
    ∃ s' t,
      Exec w (initSingletonNeighborhoodProg a_start a_end a_entries a_X a_N
        r_n r_v r_k r_hi r_w r_xw) s s' t ∧
      t ≤ 17 + 2 * n + 18 * (lists v₀).length ∧
      IsBitSet {v₀} a_X s' ∧
      IsBitSet (extNeighborhood G {v₀}) a_N s' ∧
      (∀ a : Arr, a ≠ a_X → a ≠ a_N → s'.arrs a = s.arrs a) ∧
      (∀ r : Reg, r ≠ r_k → r ≠ r_hi → r ≠ r_w → r ≠ r_xw → s'.regs r = s.regs r) := by
  have h0_w : 0 < 2 ^ w := by omega
  have hv₀_w : v₀.1 < 2 ^ w := by omega
  let s₁ := s.setArr a_X (List.replicate n 0)
  have hex₁ : Exec w (.alloc a_X (.reg r_n)) s s₁ (1 + n) :=
    .alloc (by simp [Expr.eval, checkWord, hrn, hn_w])
  let s₂ := s₁.setArr a_N (List.replicate n 0)
  have hex₂ : Exec w (.alloc a_N (.reg r_n)) s₁ s₂ (1 + n) :=
    .alloc (by simp [s₁, Expr.eval, checkWord, hrn, hn_w])
  let s₃ := s₂.writeArr a_X v₀.1 1
  have hex₃ : Exec w (.write a_X (.reg r_v) (.const 1)) s₂ s₃ 3 :=
    .write (by simp [s₂, s₁, Expr.eval, checkWord, hrv, hv₀_w])
      (by simp [Expr.eval, checkWord, hw])
      (by simp [s₂, s₁, show (a_X : Arr) ≠ a_N from hne_XN, v₀.2])
  let s₄ := s₃.writeArr a_N v₀.1 0
  have hex₄ : Exec w (.write a_N (.reg r_v) (.const 0)) s₃ s₄ 3 :=
    .write (by simp [s₃, s₂, s₁, Expr.eval, checkWord, hrv, hv₀_w])
      (by simp [Expr.eval, checkWord, h0_w])
      (by simp [s₃, s₂, show (a_N : Arr) ≠ a_X from hne_XN.symm, v₀.2])
  have hX₄ : IsBitSet (insert v₀ ∅) a_X s₄ := by
    have hX₂ : IsBitSet (∅ : Finset (Fin n)) a_X s₂ :=
      IsBitSet.empty_of_replicate (by simp [s₂, s₁, show (a_X : Arr) ≠ a_N from hne_XN])
    exact (hX₂.write_one v₀).of_arr_eq (by simp [s₄, s₃, show (a_X : Arr) ≠ a_N from hne_XN])
  have hN₄ : IsBitSet (∅ : Finset (Fin n)) a_N s₄ := by
    have hN₃ : IsBitSet (∅ : Finset (Fin n)) a_N s₃ :=
      IsBitSet.empty_of_replicate (by simp [s₃, s₂, show (a_N : Arr) ≠ a_X from hne_XN.symm])
    simpa using hN₃.write_zero v₀
  have harr₄ : ∀ a : Arr, a ≠ a_X → a ≠ a_N → s₄.arrs a = s.arrs a := by
    intro a haX haN
    simp [s₄, s₃, s₂, s₁, haX, haN]
  have hadj₄ : IsAdjList G a_start a_end a_entries lists s₄ :=
    hadj.of_arrs_eq (harr₄ _ hne_stX hne_stN) (harr₄ _ hne_enX hne_enN) (harr₄ _ hne_entX hne_entN)
  have hent₄ : (s₄.arrs a_entries).length < 2 ^ w := by
    rw [harr₄ _ hne_entX hne_entN]; exact hent_w
  rcases expandNeighborhoodForList_exec G lists ∅ ∅ v₀
      a_start a_end a_entries a_X a_N r_v r_k r_hi r_w r_xw
      hne_XN hne_stN hne_enN hne_entN
      hne_kh hne_vk hne_vh hne_vw hne_vx hne_kw hne_kx hne_hw hne_hx hne_wx
      hw hn_w hadj.2 hadj₄ hent₄ hX₄ hN₄ hrv with
    ⟨s₅, t₅, hex₅, ht₅, hX₅, hN₅, harr₅, hreg₅⟩
  rw [expandNeighborSet_full_singleton hadj.2 v₀] at hN₅
  rw [Finset.insert_empty] at hX₅
  refine ⟨s₅, (1 + n) + ((1 + n) + (3 + (3 + t₅))),
    .seq hex₁ (.seq hex₂ (.seq hex₃ (.seq hex₄ hex₅))),
    by omega, hX₅, hN₅,
    fun a haX haN => by rw [harr₅ a haN, harr₄ a haX haN],
    hreg₅⟩

/-! ### Section 3: Computing Degrees into a BitSet (`computeDegIntoProg`) -/

/-- Count how many of the first `j` elements of `l` belong to `S`. -/
def countInBitSet {n : ℕ} (S : Finset (Fin n)) (l : List ℕ) : ℕ → ℕ
  | 0 => 0
  | j + 1 =>
    countInBitSet S l j +
      if h : j < l.length then
        if hlt : l[j] < n then
          if (⟨l[j], hlt⟩ : Fin n) ∈ S then 1 else 0
        else 0
      else 0

theorem countInBitSet_le {n : ℕ} (S : Finset (Fin n)) (l : List ℕ) (j : ℕ) :
    countInBitSet S l j ≤ j := by
  induction j with
  | zero => simp [countInBitSet]
  | succ j ih =>
    unfold countInBitSet
    split_ifs <;> omega

theorem countInBitSet_eq_card_filter {n : ℕ} (S : Finset (Fin n)) (l : List ℕ)
    (hlt : ∀ x ∈ l, x < n) (hnodup : l.Nodup) (j : ℕ) (hj : j ≤ l.length) :
    countInBitSet S l j =
      (S.filter (fun w : Fin n => w.1 ∈ l.take j)).card := by
  induction j with
  | zero => simp [countInBitSet]
  | succ j ih =>
    have hj_lt : j < l.length := by omega
    have hw_lt : l[j] < n := hlt l[j] (List.getElem_mem hj_lt)
    let w₀ : Fin n := ⟨l[j], hw_lt⟩
    have hw₀_not : w₀.1 ∉ l.take j := by
      rw [List.mem_iff_getElem]
      rintro ⟨i, hi, heq⟩
      rw [List.length_take] at hi
      rw [List.getElem_take] at heq
      have hne : i ≠ j := by omega
      exact hne ((List.Nodup.getElem_inj_iff hnodup).mp heq)
    rw [countInBitSet, ih (by omega), take_add_one_eq_append_getElem l j hj_lt]
    simp only [hj_lt, hw_lt, ↓reduceDIte]
    by_cases hwS : w₀ ∈ S
    · have hwS' : (⟨l[j], hw_lt⟩ : Fin n) ∈ S := hwS
      simp only [hwS', ↓reduceIte]
      have hset :
          S.filter (fun w : Fin n => w.1 ∈ l.take j ++ [l[j]]) =
            insert w₀ (S.filter (fun w : Fin n => w.1 ∈ l.take j)) := by
        ext u
        simp only [Finset.mem_filter, List.mem_append, List.mem_singleton,
          Finset.mem_insert, Fin.ext_iff, w₀]
        constructor
        · rintro ⟨huS, hu_take | hu_eq⟩
          · exact Or.inr ⟨huS, hu_take⟩
          · exact Or.inl hu_eq
        · rintro (hu_eq | ⟨huS, hu_take⟩)
          · have hu_fin : u = w₀ := Fin.ext hu_eq
            exact ⟨hu_fin ▸ hwS, Or.inr hu_eq⟩
          · exact ⟨huS, Or.inl hu_take⟩
      have hnot_mem : w₀ ∉ S.filter (fun w : Fin n => w.1 ∈ l.take j) := by
        simp [hw₀_not]
      rw [hset, Finset.card_insert_of_notMem hnot_mem]
    · have hwS' : (⟨l[j], hw_lt⟩ : Fin n) ∉ S := hwS
      simp only [hwS', ↓reduceIte]
      have hset :
          S.filter (fun w : Fin n => w.1 ∈ l.take j ++ [l[j]]) =
            S.filter (fun w : Fin n => w.1 ∈ l.take j) := by
        ext u
        simp only [Finset.mem_filter, List.mem_append, List.mem_singleton]
        constructor
        · rintro ⟨huS, hu_take | hu_eq⟩
          · exact ⟨huS, hu_take⟩
          · exfalso
            have : u = w₀ := Fin.ext hu_eq
            exact hwS (this ▸ huS)
        · rintro ⟨huS, hu_take⟩
          exact ⟨huS, Or.inl hu_take⟩
      rw [hset, Nat.add_zero]

theorem countInBitSet_full_eq_degInto {n : ℕ} {G : SimpleGraph (Fin n)} {lists : Fin n → List ℕ}
    (hlists : IsAdjListFamily G lists) (S : Finset (Fin n)) (u : Fin n) :
    countInBitSet S (lists u) (lists u).length = degInto G S u := by
  classical
  rw [countInBitSet_eq_card_filter S (lists u) (hlists u).1 (hlists u).2.1
    (lists u).length le_rfl, List.take_length]
  unfold degInto
  congr 1
  ext w
  simp [(hlists u).2.2.2 w]

/-- Inner loop body for `computeDegIntoProg`: reads `r_sw := a_S[r_w]`; if `r_sw != 0`, increments
`r_cnt`. -/
def computeDegIntoInnerBody (a_S : Arr) (r_w r_sw r_cnt : Reg) : Cmd :=
  .seq (.assign r_sw (.read a_S (.reg r_w)))
    (.ite (.reg r_sw) (.assign r_cnt (.op .add (.reg r_cnt) (.const 1))) .skip)

/-- Compute `degInto G S u` for vertex `u = s.regs r_u` into `r_cnt` and write it to `a_deg[r_u]`. -/
def computeDegIntoVertexBody (a_start a_end a_entries a_S a_deg : Arr)
    (r_u r_k r_hi r_w r_sw r_cnt : Reg) : Cmd :=
  .seq (.assign r_cnt (.const 0))
    (.seq (forList a_start a_end a_entries r_u r_k r_hi r_w
        (computeDegIntoInnerBody a_S r_w r_sw r_cnt))
      (.write a_deg (.reg r_u) (.reg r_cnt)))

/-- Compute `degInto G S u` for all `u : Fin n` and store the results in `a_deg`. -/
def computeDegIntoProg (a_start a_end a_entries a_S a_deg : Arr)
    (r_n r_u r_k r_hi r_w r_sw r_cnt : Reg) : Cmd :=
  .seq (.alloc a_deg (.reg r_n))
    (.seq (.assign r_u (.const 0))
      (forUp r_u (.reg r_n)
        (computeDegIntoVertexBody a_start a_end a_entries a_S a_deg r_u r_k r_hi r_w r_sw r_cnt)))

theorem computeDegIntoVertex_exec {w n : ℕ} (G : SimpleGraph (Fin n))
    (lists : Fin n → List ℕ) (S : Finset (Fin n)) (u : Fin n)
    (a_start a_end a_entries a_S a_deg : ℕ)
    (r_u r_k r_hi r_w r_sw r_cnt : ℕ)
    (_hne_st_deg : a_start ≠ a_deg) (_hne_en_deg : a_end ≠ a_deg)
    (_hne_ent_deg : a_entries ≠ a_deg) (_hne_S_deg : a_S ≠ a_deg)
    (hne_kh : r_k ≠ r_hi) (hne_uk : r_u ≠ r_k) (hne_uh : r_u ≠ r_hi)
    (hne_uw : r_u ≠ r_w) (hne_usw : r_u ≠ r_sw) (hne_ucnt : r_u ≠ r_cnt)
    (hne_kw : r_k ≠ r_w) (hne_ksw : r_k ≠ r_sw) (hne_kcnt : r_k ≠ r_cnt)
    (hne_hw : r_hi ≠ r_w) (hne_hsw : r_hi ≠ r_sw) (hne_hcnt : r_hi ≠ r_cnt)
    (hne_wsw : r_w ≠ r_sw) (hne_wcnt : r_w ≠ r_cnt) (hne_swcnt : r_sw ≠ r_cnt)
    (hw : 1 < 2 ^ w) (hn_w : n < 2 ^ w)
    {s : State}
    (hadj : IsAdjList G a_start a_end a_entries lists s)
    (hent_w : (s.arrs a_entries).length < 2 ^ w)
    (hS : IsBitSet S a_S s)
    (hdeg_len : (s.arrs a_deg).length = n)
    (hru : s.regs r_u = u.1) :
    ∃ s' t,
      Exec w (computeDegIntoVertexBody a_start a_end a_entries a_S a_deg
        r_u r_k r_hi r_w r_sw r_cnt) s s' t ∧
      t ≤ 14 + 19 * (lists u).length ∧
      s'.arrs a_deg = (s.arrs a_deg).set u.1 (degInto G S u) ∧
      (∀ a : Arr, a ≠ a_deg → s'.arrs a = s.arrs a) ∧
      (∀ r : Reg, r ≠ r_k → r ≠ r_hi → r ≠ r_w → r ≠ r_sw → r ≠ r_cnt → s'.regs r = s.regs r) := by
  have h0_w : 0 < 2 ^ w := by omega
  have hu_w : u.1 < 2 ^ w := by omega
  let s₁ := s.setReg r_cnt 0
  have hex₁ : Exec w (.assign r_cnt (.const 0)) s s₁ 2 :=
    .assign (by simp [Expr.eval, checkWord, h0_w])
  rcases hadj.1.2.2 u with ⟨st, en, hlist_u⟩
  have hen_le : en ≤ (s.arrs a_entries).length := hlist_u.2.2.1
  have hen_w : en < 2 ^ w := by omega
  have hwords : ∀ x ∈ lists u, x < 2 ^ w := by
    intro x hx
    have := (hadj.2 u).1 x hx
    omega
  let Inv : ℕ → State → Prop := fun j st_j =>
    IsListAt a_start a_end a_entries u.1 st en (lists u) st_j ∧
    IsBitSet S a_S st_j ∧
    st_j.regs r_u = u.1 ∧
    st_j.regs r_cnt = countInBitSet S (lists u) j ∧
    (∀ a : Arr, st_j.arrs a = s.arrs a) ∧
    (∀ r : Reg, r ≠ r_k → r ≠ r_hi → r ≠ r_w → r ≠ r_sw → r ≠ r_cnt → st_j.regs r = s.regs r)
  have hspec :
      ⦃Inv 0⦄[w]
        forList a_start a_end a_entries r_u r_k r_hi r_w
          (computeDegIntoInnerBody a_S r_w r_sw r_cnt)
      ⦃Inv (lists u).length⦄ ≤ fun _ => 9 + (lists u).length * (10 + 9) := by
    apply Triple.forList_const a_start a_end a_entries r_u r_k r_hi r_w
      u.1 st en (lists u) Inv 9 _ hne_kh hne_uk hw hu_w hen_w hwords
    · intro st₀ ⟨hlist₀, hS₀, hru₀, hcnt₀, harr₀, hreg₀⟩
      refine ⟨hlist₀, hru₀, hlist₀, hS₀,
        by simp [State.setReg, show (r_u : Reg) ≠ r_hi by omega,
          show (r_u : Reg) ≠ r_k by omega, hru₀],
        by simp [State.setReg, show (r_cnt : Reg) ≠ r_hi by omega,
          show (r_cnt : Reg) ≠ r_k by omega, hcnt₀],
        harr₀, ?_⟩
      intro r h1 h2 h3 h4 h5
      simp [State.setReg, h1, h2, hreg₀ r h1 h2 h3 h4 h5]
    · intro j _ st_j ⟨hlist_j, _⟩
      exact hlist_j
    · intro j hj st_w ⟨st_j, ⟨hlist_j, hS_j, hru_j, hcnt_j, harr_j, hreg_j⟩, hst_w, hrk_j, hrhi_j⟩
      subst hst_w
      let w_val := (lists u)[j]
      have hw_lt : w_val < n := (hadj.2 u).1 w_val (List.getElem_mem hj)
      have hw_w : w_val < 2 ^ w := by omega
      let wFin : Fin n := ⟨w_val, hw_lt⟩
      rcases hS_j with ⟨hS_len, hS_le, hS_mem⟩
      have hw_S_len : w_val < (st_j.arrs a_S).length := by rw [hS_len]; exact hw_lt
      let sw_val := (st_j.arrs a_S)[w_val]'hw_S_len
      have hsw_le : sw_val ≤ 1 := hS_le wFin
      have hsw_w : sw_val < 2 ^ w := by omega
      let sb₁ := (st_j.setReg r_w w_val).setReg r_sw sw_val
      have hexb₁ : Exec w (.assign r_sw (.read a_S (.reg r_w))) (st_j.setReg r_w w_val) sb₁ 3 :=
        .assign (by simp [Expr.eval, checkWord, hw_w, hw_S_len, sw_val, hsw_w])
      have hcond_sw : (Expr.reg r_sw).eval w sb₁ = some sw_val := by
        simp [sb₁, Expr.eval, checkWord, hsw_w]
      have hcnt_le_n : countInBitSet S (lists u) j < n := by
        have h1 := countInBitSet_le S (lists u) j
        have h2 := (hadj.2 u).2.2.1
        omega
      have hcnt_w : countInBitSet S (lists u) j < 2 ^ w := by omega
      by_cases hw_in_S : wFin ∈ S
      · have hsw_ne : sw_val ≠ 0 := (hS_mem wFin).mpr hw_in_S
        let sb₂ := sb₁.setReg r_cnt (countInBitSet S (lists u) j + 1)
        have hex_inc : Exec w (.assign r_cnt (.op .add (.reg r_cnt) (.const 1))) sb₁ sb₂ 4 :=
          .assign (by
            simp [sb₁, State.setReg, show (r_cnt : Reg) ≠ r_sw by omega,
              show (r_cnt : Reg) ≠ r_w by omega,
              Expr.eval, BinOp.eval, BinOp.raw, checkWord, hcnt_j, hcnt_w, hw,
              show countInBitSet S (lists u) j + 1 < 2 ^ w by omega])
        have hex_ite : Exec w
            (.ite (.reg r_sw) (.assign r_cnt (.op .add (.reg r_cnt) (.const 1))) .skip)
            sb₁ sb₂ (1 + 4) :=
          .ite_true hcond_sw hsw_ne hex_inc
        refine ⟨sb₂, 3 + (1 + 4), .seq hexb₁ hex_ite, by dsimp only; omega, ?_,
          by simp [sb₂, sb₁, State.setReg, show (r_k : Reg) ≠ r_cnt by omega,
            show (r_k : Reg) ≠ r_sw by omega, show (r_k : Reg) ≠ r_w by omega, hrk_j],
          by simp [sb₂, sb₁, State.setReg, show (r_hi : Reg) ≠ r_cnt by omega,
            show (r_hi : Reg) ≠ r_sw by omega, show (r_hi : Reg) ≠ r_w by omega, hrhi_j]⟩
        refine ⟨hlist_j, ⟨hS_len, hS_le, hS_mem⟩,
          by simp [sb₂, sb₁, State.setReg, show (r_u : Reg) ≠ r_k by omega,
            show (r_u : Reg) ≠ r_cnt by omega, show (r_u : Reg) ≠ r_sw by omega,
            show (r_u : Reg) ≠ r_w by omega, hru_j],
          ?_, harr_j, ?_⟩
        · have hw_in_S' : (⟨(lists u)[j], hw_lt⟩ : Fin n) ∈ S := hw_in_S
          have hw_lt' : (lists u)[j] < n := hw_lt
          simp [sb₂, State.setReg, show (r_cnt : Reg) ≠ r_k by omega,
            countInBitSet, hj, hw_lt', hw_in_S']
        · intro r h1 h2 h3 h4 h5
          simp [sb₂, sb₁, State.setReg, h1, h3, h4, h5, hreg_j r h1 h2 h3 h4 h5]
      · have hsw_eq0 : sw_val = 0 := not_ne_iff.mp ((hS_mem wFin).not.mpr hw_in_S)
        have hcond0 : (Expr.reg r_sw).eval w sb₁ = some 0 := by simpa [hsw_eq0] using hcond_sw
        have hex_ite : Exec w
            (.ite (.reg r_sw) (.assign r_cnt (.op .add (.reg r_cnt) (.const 1))) .skip)
            sb₁ sb₁ (1 + 1) :=
          .ite_false hcond0 (.skip sb₁)
        refine ⟨sb₁, 3 + (1 + 1), .seq hexb₁ hex_ite, by dsimp only; omega, ?_,
          by simp [sb₁, State.setReg, show (r_k : Reg) ≠ r_sw by omega,
            show (r_k : Reg) ≠ r_w by omega, hrk_j],
          by simp [sb₁, State.setReg, show (r_hi : Reg) ≠ r_sw by omega,
            show (r_hi : Reg) ≠ r_w by omega, hrhi_j]⟩
        refine ⟨hlist_j, ⟨hS_len, hS_le, hS_mem⟩,
          by simp [sb₁, State.setReg, show (r_u : Reg) ≠ r_k by omega,
            show (r_u : Reg) ≠ r_sw by omega, show (r_u : Reg) ≠ r_w by omega, hru_j],
          ?_, harr_j, ?_⟩
        · have hw_in_S' : (⟨(lists u)[j], hw_lt⟩ : Fin n) ∉ S := hw_in_S
          have hw_lt' : (lists u)[j] < n := hw_lt
          simp [sb₁, State.setReg, show (r_cnt : Reg) ≠ r_k by omega,
            show (r_cnt : Reg) ≠ r_sw by omega, show (r_cnt : Reg) ≠ r_w by omega,
            hcnt_j, countInBitSet, hj, hw_lt', hw_in_S']
        · intro r h1 h2 h3 h4 h5
          simp [sb₁, State.setReg, h1, h3, h4, hreg_j r h1 h2 h3 h4 h5]
  have hinit : Inv 0 s₁ := by
    refine ⟨hlist_u, hS,
      by simp [s₁, State.setReg, show (r_u : Reg) ≠ r_cnt by omega, hru],
      by simp [s₁, countInBitSet],
      fun _ => rfl,
      fun r _ _ _ _ h5 => by simp [s₁, State.setReg, h5]⟩
  rcases hspec s₁ hinit with ⟨s₂, t₂, hex₂, ht₂, _, _, hru₂, hcnt₂, harr₂, hreg₂⟩
  dsimp only at ht₂
  rw [countInBitSet_full_eq_degInto hadj.2 S u] at hcnt₂
  have hdeg_w : degInto G S u < 2 ^ w := by
    have := degInto_le_n G S u
    omega
  have hu_deg_len : u.1 < (s₂.arrs a_deg).length := by
    rw [harr₂ a_deg, hdeg_len]; exact u.2
  let s₃ := s₂.writeArr a_deg u.1 (degInto G S u)
  have hex₃ : Exec w (.write a_deg (.reg r_u) (.reg r_cnt)) s₂ s₃ 3 :=
    .write (by simp [Expr.eval, checkWord, hru₂, hu_w])
      (by simp [Expr.eval, checkWord, hcnt₂, hdeg_w]) hu_deg_len
  refine ⟨s₃, 2 + (t₂ + 3), .seq hex₁ (.seq hex₂ hex₃), by omega,
    by simp [s₃, harr₂ a_deg],
    fun a ha => by simp [s₃, ha, harr₂ a],
    hreg₂⟩

theorem computeDegIntoLoop_exec {w n : ℕ} (G : SimpleGraph (Fin n))
    (lists : Fin n → List ℕ) (S : Finset (Fin n))
    (a_start a_end a_entries a_S a_deg : ℕ)
    (r_n r_u r_k r_hi r_w r_sw r_cnt : ℕ)
    (hne_st_deg : a_start ≠ a_deg) (hne_en_deg : a_end ≠ a_deg)
    (hne_ent_deg : a_entries ≠ a_deg) (hne_S_deg : a_S ≠ a_deg)
    (hne_un : r_u ≠ r_n) (hne_kn : r_k ≠ r_n) (hne_hn : r_hi ≠ r_n)
    (hne_wn : r_w ≠ r_n) (hne_swn : r_sw ≠ r_n) (hne_cntn : r_cnt ≠ r_n)
    (hne_kh : r_k ≠ r_hi) (hne_uk : r_u ≠ r_k) (hne_uh : r_u ≠ r_hi)
    (hne_uw : r_u ≠ r_w) (hne_usw : r_u ≠ r_sw) (hne_ucnt : r_u ≠ r_cnt)
    (hne_kw : r_k ≠ r_w) (hne_ksw : r_k ≠ r_sw) (hne_kcnt : r_k ≠ r_cnt)
    (hne_hw : r_hi ≠ r_w) (hne_hsw : r_hi ≠ r_sw) (hne_hcnt : r_hi ≠ r_cnt)
    (hne_wsw : r_w ≠ r_sw) (hne_wcnt : r_w ≠ r_cnt) (hne_swcnt : r_sw ≠ r_cnt)
    (hw : 1 < 2 ^ w) (hn_w : n < 2 ^ w)
    (rem k : ℕ) (hrem : k + rem = n) {s : State}
    (hadj : IsAdjList G a_start a_end a_entries lists s)
    (hent_w : (s.arrs a_entries).length < 2 ^ w)
    (hS : IsBitSet S a_S s)
    (hdeg_len : (s.arrs a_deg).length = n)
    (hdeg_pre : ∀ u : Fin n, u.1 < k →
      (s.arrs a_deg)[u.1]'(by rw [hdeg_len]; exact u.2) = degInto G S u)
    (hrn : s.regs r_n = n)
    (hru : s.regs r_u = k) :
    ∃ s' t,
      Exec w (forUp r_u (.reg r_n)
        (computeDegIntoVertexBody a_start a_end a_entries a_S a_deg
          r_u r_k r_hi r_w r_sw r_cnt)) s s' t ∧
      t ≤ 3 + (∑ u ∈ Finset.univ.filter (fun u : Fin n => k ≤ u.1), (21 + 19 * (lists u).length)) ∧
      IsDegIntoArr G S a_deg s' ∧
      (∀ a : Arr, a ≠ a_deg → s'.arrs a = s.arrs a) ∧
      (∀ r : Reg, r ≠ r_u → r ≠ r_k → r ≠ r_hi → r ≠ r_w → r ≠ r_sw → r ≠ r_cnt →
        s'.regs r = s.regs r) := by
  have h0_w : 0 < 2 ^ w := by omega
  induction rem generalizing k s with
  | zero =>
    have hk_eq : k = n := by omega
    rw [hk_eq] at hru hdeg_pre
    have hcond : (Expr.op .lt (.reg r_u) (.reg r_n)).eval w s = some 0 := by
      simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hru, hrn, hn_w, h0_w]
    refine ⟨s, 3, .while_false hcond, by omega, ⟨hdeg_len, fun u => hdeg_pre u u.2⟩,
      fun _ _ => rfl, fun _ _ _ _ _ _ _ => rfl⟩
  | succ rem ih =>
    have hk_lt : k < n := by omega
    have hk_w : k < 2 ^ w := by omega
    let uFin : Fin n := ⟨k, hk_lt⟩
    have hcond : (Expr.op .lt (.reg r_u) (.reg r_n)).eval w s = some 1 := by
      simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hru, hrn, hk_w, hn_w, hk_lt, hw]
    rcases computeDegIntoVertex_exec G lists S uFin
        a_start a_end a_entries a_S a_deg r_u r_k r_hi r_w r_sw r_cnt
        hne_st_deg hne_en_deg hne_ent_deg hne_S_deg
        hne_kh hne_uk hne_uh hne_uw hne_usw hne_ucnt
        hne_kw hne_ksw hne_kcnt hne_hw hne_hsw hne_hcnt
        hne_wsw hne_wcnt hne_swcnt hw hn_w
        hadj hent_w hS hdeg_len hru with
      ⟨s₁, t₁, hex₁, ht₁, hdeg₁, harr₁, hreg₁⟩
    have hru₁ : s₁.regs r_u = k := by
      rw [hreg₁ r_u hne_uk hne_uh hne_uw hne_usw hne_ucnt, hru]
    let s₂ := s₁.setReg r_u (k + 1)
    have hex_inc : Exec w (.assign r_u (.op .add (.reg r_u) (.const 1))) s₁ s₂ 4 :=
      .assign (by
        simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hru₁, hk_w, hw,
          show k + 1 < 2 ^ w by omega])
    have harr₂ : ∀ a : Arr, a ≠ a_deg → s₂.arrs a = s.arrs a := by
      intro a ha
      simp [s₂, harr₁ a ha]
    have hadj₂ : IsAdjList G a_start a_end a_entries lists s₂ :=
      hadj.of_arrs_eq (harr₂ _ hne_st_deg) (harr₂ _ hne_en_deg) (harr₂ _ hne_ent_deg)
    have hent₂ : (s₂.arrs a_entries).length < 2 ^ w := by
      rw [harr₂ _ hne_ent_deg]; exact hent_w
    have hS₂ : IsBitSet S a_S s₂ := hS.of_arr_eq (harr₂ _ hne_S_deg)
    have hdeg_len₂ : (s₂.arrs a_deg).length = n := by
      simp [s₂, hdeg₁, hdeg_len]
    have hdeg_pre₂ : ∀ u : Fin n, u.1 < k + 1 →
        (s₂.arrs a_deg)[u.1]'(by rw [hdeg_len₂]; exact u.2) = degInto G S u := by
      intro u hu
      simp only [s₂, State.setReg_arrs, hdeg₁]
      by_cases hueq : u.1 = k
      · have hu_eq : u = uFin := Fin.ext hueq
        subst hu_eq
        exact List.getElem_set_self (by rw [List.length_set, hdeg_len]; exact hk_lt)
      · rw [List.getElem_set_ne (by dsimp [uFin]; omega)]
        exact hdeg_pre u (by omega)
    have hrn₂ : s₂.regs r_n = n := by
      simp [s₂, State.setReg, show (r_n : Reg) ≠ r_u from hne_un.symm,
        hreg₁ r_n hne_kn.symm hne_hn.symm hne_wn.symm hne_swn.symm hne_cntn.symm, hrn]
    rcases ih (k + 1) (by omega) hadj₂ hent₂ hS₂ hdeg_len₂ hdeg_pre₂ hrn₂ (by simp [s₂]) with
      ⟨s₃, t₃, hex₃, ht₃, hdeg₃, harr₃, hreg₃⟩
    have hsum_split :
        (21 + 19 * (lists uFin).length) +
          (∑ u ∈ Finset.univ.filter (fun u : Fin n => k + 1 ≤ u.1), (21 + 19 * (lists u).length)) =
          ∑ u ∈ Finset.univ.filter (fun u : Fin n => k ≤ u.1), (21 + 19 * (lists u).length) := by
      have hset :
          Finset.univ.filter (fun u : Fin n => k ≤ u.1) =
            insert uFin (Finset.univ.filter (fun u : Fin n => k + 1 ≤ u.1)) := by
        ext u
        simp only [Finset.mem_filter, Finset.mem_univ, Finset.mem_insert, Fin.ext_iff,
          true_and, uFin]
        omega
      have hnot_mem : uFin ∉ Finset.univ.filter (fun u : Fin n => k + 1 ≤ u.1) := by
        simp [uFin]
      rw [hset, Finset.sum_insert hnot_mem]
    refine ⟨s₃, 3 + (t₁ + 4) + t₃,
      .while_true hcond (by omega) (.seq hex₁ hex_inc) hex₃,
      by omega, hdeg₃,
      fun a ha => by rw [harr₃ a ha, harr₂ a ha],
      fun r h1 h2 h3 h4 h5 h6 => by
        rw [hreg₃ r h1 h2 h3 h4 h5 h6]
        simp [s₂, State.setReg, h1, hreg₁ r h2 h3 h4 h5 h6]⟩

/-- Execution theorem for `computeDegIntoProg`: computes `degInto G S u` for all `u : Fin n` into
`a_deg` in `O(n + totalAdjEntries lists)` steps. -/
theorem computeDegIntoProg_exec {w n : ℕ} (G : SimpleGraph (Fin n))
    (lists : Fin n → List ℕ) (S : Finset (Fin n))
    (a_start a_end a_entries a_S a_deg : ℕ)
    (r_n r_u r_k r_hi r_w r_sw r_cnt : ℕ)
    (hne_st_deg : a_start ≠ a_deg) (hne_en_deg : a_end ≠ a_deg)
    (hne_ent_deg : a_entries ≠ a_deg) (hne_S_deg : a_S ≠ a_deg)
    (hne_un : r_u ≠ r_n) (hne_kn : r_k ≠ r_n) (hne_hn : r_hi ≠ r_n)
    (hne_wn : r_w ≠ r_n) (hne_swn : r_sw ≠ r_n) (hne_cntn : r_cnt ≠ r_n)
    (hne_kh : r_k ≠ r_hi) (hne_uk : r_u ≠ r_k) (hne_uh : r_u ≠ r_hi)
    (hne_uw : r_u ≠ r_w) (hne_usw : r_u ≠ r_sw) (hne_ucnt : r_u ≠ r_cnt)
    (hne_kw : r_k ≠ r_w) (hne_ksw : r_k ≠ r_sw) (hne_kcnt : r_k ≠ r_cnt)
    (hne_hw : r_hi ≠ r_w) (hne_hsw : r_hi ≠ r_sw) (hne_hcnt : r_hi ≠ r_cnt)
    (hne_wsw : r_w ≠ r_sw) (hne_wcnt : r_w ≠ r_cnt) (hne_swcnt : r_sw ≠ r_cnt)
    (hw : 1 < 2 ^ w) (hn_w : n < 2 ^ w)
    {s : State}
    (hadj : IsAdjList G a_start a_end a_entries lists s)
    (hent_w : (s.arrs a_entries).length < 2 ^ w)
    (hS : IsBitSet S a_S s)
    (hrn : s.regs r_n = n) :
    ∃ s' t,
      Exec w (computeDegIntoProg a_start a_end a_entries a_S a_deg
        r_n r_u r_k r_hi r_w r_sw r_cnt) s s' t ∧
      t ≤ 6 + 22 * n + 19 * totalAdjEntries lists ∧
      IsDegIntoArr G S a_deg s' ∧
      (∀ a : Arr, a ≠ a_deg → s'.arrs a = s.arrs a) ∧
      (∀ r : Reg, r ≠ r_u → r ≠ r_k → r ≠ r_hi → r ≠ r_w → r ≠ r_sw → r ≠ r_cnt →
        s'.regs r = s.regs r) := by
  have h0_w : 0 < 2 ^ w := by omega
  let s₁ := s.setArr a_deg (List.replicate n 0)
  have hex₁ : Exec w (.alloc a_deg (.reg r_n)) s s₁ (1 + n) :=
    .alloc (by simp [Expr.eval, checkWord, hrn, hn_w])
  let s₂ := s₁.setReg r_u 0
  have hex₂ : Exec w (.assign r_u (.const 0)) s₁ s₂ 2 :=
    .assign (by simp [Expr.eval, checkWord, h0_w])
  have harr₂ : ∀ a : Arr, a ≠ a_deg → s₂.arrs a = s.arrs a := by
    intro a ha
    simp [s₂, s₁, ha]
  have hadj₂ : IsAdjList G a_start a_end a_entries lists s₂ :=
    hadj.of_arrs_eq (harr₂ _ hne_st_deg) (harr₂ _ hne_en_deg) (harr₂ _ hne_ent_deg)
  have hent₂ : (s₂.arrs a_entries).length < 2 ^ w := by
    rw [harr₂ _ hne_ent_deg]; exact hent_w
  have hS₂ : IsBitSet S a_S s₂ := hS.of_arr_eq (harr₂ _ hne_S_deg)
  rcases computeDegIntoLoop_exec G lists S
      a_start a_end a_entries a_S a_deg r_n r_u r_k r_hi r_w r_sw r_cnt
      hne_st_deg hne_en_deg hne_ent_deg hne_S_deg
      hne_un hne_kn hne_hn hne_wn hne_swn hne_cntn
      hne_kh hne_uk hne_uh hne_uw hne_usw hne_ucnt
      hne_kw hne_ksw hne_kcnt hne_hw hne_hsw hne_hcnt
      hne_wsw hne_wcnt hne_swcnt hw hn_w n 0 (by omega)
      hadj₂ hent₂ hS₂ (by simp [s₂, s₁]) (fun _ h => by omega)
      (by simp [s₂, s₁, State.setReg, show (r_n : Reg) ≠ r_u from hne_un.symm, hrn])
      (by simp [s₂]) with
    ⟨s₃, t₃, hex₃, ht₃, hdeg₃, harr₃, hreg₃⟩
  have hsum_univ :
      (∑ u ∈ Finset.univ.filter (fun u : Fin n => 0 ≤ u.1), (21 + 19 * (lists u).length)) =
        21 * n + 19 * totalAdjEntries lists := by
    have hfilter : Finset.univ.filter (fun u : Fin n => 0 ≤ u.1) = Finset.univ := by
      ext u; simp
    rw [hfilter]
    simp only [totalAdjEntries, Finset.sum_add_distrib, Finset.sum_const,
      Finset.card_univ, Fintype.card_fin, smul_eq_mul, ← Finset.mul_sum]
    omega
  refine ⟨s₃, (1 + n) + (2 + t₃), .seq hex₁ (.seq hex₂ hex₃), by omega, hdeg₃,
    fun a ha => by rw [harr₃ a ha, harr₂ a ha],
    fun r h1 h2 h3 h4 h5 h6 => by
      rw [hreg₃ r h1 h2 h3 h4 h5 h6]
      simp [s₂, s₁, State.setReg, h1]⟩

/-! ### Section 4: Finding a Vertex in `S` with Degree `< k` (`findLowDegVertexProg`) -/

/-- Loop body for `findLowDegVertexProg`: for vertex `u = s.regs r_u`, reads `r_su := a_S[r_u]` and
`r_du := a_deg[r_u]`; if `r_su != 0` and `r_du < r_k_thr`, sets `r_found := r_u`. -/
def findLowDegVertexBody (a_S a_deg : Arr) (r_k_thr r_u r_su r_du r_found : Reg) : Cmd :=
  .seq (.assign r_su (.read a_S (.reg r_u)))
    (.seq (.assign r_du (.read a_deg (.reg r_u)))
      (.ite (.reg r_su)
        (.ite (.op .lt (.reg r_du) (.reg r_k_thr))
          (.assign r_found (.reg r_u))
          .skip)
        .skip))

/-- Scan `u = 0 .. n - 1` to find a vertex `v ∈ S` with `degInto G S v < k_thr`, setting `r_found`
to `v.1 < n` if one exists and leaving `r_found = n` otherwise. -/
def findLowDegVertexProg (a_S a_deg : Arr) (r_n r_k_thr r_u r_su r_du r_found : Reg) : Cmd :=
  .seq (.assign r_found (.reg r_n))
    (.seq (.assign r_u (.const 0))
      (forUp r_u (.reg r_n)
        (findLowDegVertexBody a_S a_deg r_k_thr r_u r_su r_du r_found)))

theorem findLowDegVertexLoop_exec {w n k_thr : ℕ} (G : SimpleGraph (Fin n)) (S : Finset (Fin n))
    (a_S a_deg : ℕ) (r_n r_k_thr r_u r_su r_du r_found : ℕ)
    (hne_un : r_u ≠ r_n) (hne_sun : r_su ≠ r_n) (hne_dun : r_du ≠ r_n) (hne_fn : r_found ≠ r_n)
    (hne_uk : r_u ≠ r_k_thr) (hne_suk : r_su ≠ r_k_thr) (hne_duk : r_du ≠ r_k_thr)
    (hne_fk : r_found ≠ r_k_thr)
    (hne_usu : r_u ≠ r_su) (hne_udu : r_u ≠ r_du) (hne_uf : r_u ≠ r_found)
    (hne_sudu : r_su ≠ r_du) (hne_suf : r_su ≠ r_found) (hne_duf : r_du ≠ r_found)
    (hw : 1 < 2 ^ w) (hn_w : n < 2 ^ w) (hk_w : k_thr < 2 ^ w)
    (rem k : ℕ) (hrem : k + rem = n) {s : State}
    (hS : IsBitSet S a_S s)
    (hdeg : IsDegIntoArr G S a_deg s)
    (hrn : s.regs r_n = n)
    (hrk_thr : s.regs r_k_thr = k_thr)
    (hru : s.regs r_u = k)
    (hf_le : s.regs r_found ≤ n)
    (hf_sound : ∀ v : Fin n, s.regs r_found = v.1 → v ∈ S ∧ degInto G S v < k_thr)
    (hf_comp : s.regs r_found = n → ∀ v : Fin n, v.1 < k → v ∈ S → k_thr ≤ degInto G S v) :
    ∃ s' t,
      Exec w (forUp r_u (.reg r_n)
        (findLowDegVertexBody a_S a_deg r_k_thr r_u r_su r_du r_found)) s s' t ∧
      t ≤ 3 + 19 * rem ∧
      s'.regs r_found ≤ n ∧
      (∀ v : Fin n, s'.regs r_found = v.1 → v ∈ S ∧ degInto G S v < k_thr) ∧
      (s'.regs r_found = n → ∀ v ∈ S, k_thr ≤ degInto G S v) ∧
      (∀ a : Arr, s'.arrs a = s.arrs a) ∧
      (∀ r : Reg, r ≠ r_u → r ≠ r_su → r ≠ r_du → r ≠ r_found → s'.regs r = s.regs r) := by
  have h0_w : 0 < 2 ^ w := by omega
  induction rem generalizing k s with
  | zero =>
    have hk_eq : k = n := by omega
    rw [hk_eq] at hru hf_comp
    have hcond : (Expr.op .lt (.reg r_u) (.reg r_n)).eval w s = some 0 := by
      simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hru, hrn, hn_w, h0_w]
    refine ⟨s, 3, .while_false hcond, by omega, hf_le, hf_sound,
      fun h v hv => hf_comp h v v.2 hv, fun _ => rfl, fun _ _ _ _ _ => rfl⟩
  | succ rem ih =>
    have hk_lt : k < n := by omega
    have hk_w : k < 2 ^ w := by omega
    let uFin : Fin n := ⟨k, hk_lt⟩
    have hcond : (Expr.op .lt (.reg r_u) (.reg r_n)).eval w s = some 1 := by
      simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hru, hrn, hk_w, hn_w, hk_lt, hw]
    rcases hS with ⟨hS_len, hS_le, hS_mem⟩
    rcases hdeg with ⟨hdeg_len, hdeg_get⟩
    have hk_S_len : k < (s.arrs a_S).length := by rw [hS_len]; exact hk_lt
    let su_val := (s.arrs a_S)[k]'hk_S_len
    have hsu_le : su_val ≤ 1 := hS_le uFin
    have hsu_w : su_val < 2 ^ w := by omega
    let s₁ := s.setReg r_su su_val
    have hex₁ : Exec w (.assign r_su (.read a_S (.reg r_u))) s s₁ 3 :=
      .assign (by simp [Expr.eval, checkWord, hru, hk_w, hk_S_len, su_val, hsu_w])
    have hk_deg_len₀ : k < (s.arrs a_deg).length := by rw [hdeg_len]; exact hk_lt
    let du_val := degInto G S uFin
    have hdu_eq₀ : (s.arrs a_deg)[k]'hk_deg_len₀ = du_val := hdeg_get uFin
    have hdu_w : du_val < 2 ^ w := by
      have := degInto_le_n G S uFin
      omega
    let s₂ := s₁.setReg r_du du_val
    have hex₂ : Exec w (.assign r_du (.read a_deg (.reg r_u))) s₁ s₂ 3 :=
      .assign (by
        simp [s₁, State.setReg, show (r_u : Reg) ≠ r_su from hne_usu,
          Expr.eval, checkWord, hru, hk_w, hk_deg_len₀, hdu_eq₀, hdu_w])
    have hcond_su : (Expr.reg r_su).eval w s₂ = some su_val := by
      simp [s₂, s₁, State.setReg, show (r_su : Reg) ≠ r_du from hne_sudu,
        Expr.eval, checkWord, hsu_w]
    by_cases hu_in_S : uFin ∈ S
    · have hsu_ne : su_val ≠ 0 := (hS_mem uFin).mpr hu_in_S
      by_cases hdu_lt : du_val < k_thr
      · have hcond_lt : (Expr.op .lt (.reg r_du) (.reg r_k_thr)).eval w s₂ = some 1 := by
          simp [s₂, s₁, State.setReg, show (r_k_thr : Reg) ≠ r_du from hne_duk.symm,
            show (r_k_thr : Reg) ≠ r_su from hne_suk.symm,
            Expr.eval, BinOp.eval, BinOp.raw, checkWord, hrk_thr, hdu_w, ‹k_thr < 2 ^ w›,
            hdu_lt, hw]
        let s₃ := s₂.setReg r_found k
        have hex_set : Exec w (.assign r_found (.reg r_u)) s₂ s₃ 2 :=
          .assign (by
            simp [s₂, s₁, State.setReg, show (r_u : Reg) ≠ r_du from hne_udu,
              show (r_u : Reg) ≠ r_su from hne_usu, Expr.eval, checkWord, hru, hk_w])
        have hex_inner : Exec w
            (.ite (.op .lt (.reg r_du) (.reg r_k_thr)) (.assign r_found (.reg r_u)) .skip)
            s₂ s₃ (3 + 2) :=
          .ite_true hcond_lt (by omega) hex_set
        have hex_ite : Exec w
            (.ite (.reg r_su)
              (.ite (.op .lt (.reg r_du) (.reg r_k_thr)) (.assign r_found (.reg r_u)) .skip)
              .skip)
            s₂ s₃ (1 + (3 + 2)) :=
          .ite_true hcond_su hsu_ne hex_inner
        let s₄ := s₃.setReg r_u (k + 1)
        have hex_inc : Exec w (.assign r_u (.op .add (.reg r_u) (.const 1))) s₃ s₄ 4 :=
          .assign (by
            simp [s₃, s₂, s₁, State.setReg, show (r_u : Reg) ≠ r_found from hne_uf,
              show (r_u : Reg) ≠ r_du from hne_udu, show (r_u : Reg) ≠ r_su from hne_usu,
              Expr.eval, BinOp.eval, BinOp.raw, checkWord, hru, hk_w, hw,
              show k + 1 < 2 ^ w by omega])
        have hf₄ : s₄.regs r_found = k := by
          simp [s₄, s₃, State.setReg, show (r_found : Reg) ≠ r_u from hne_uf.symm]
        rcases ih (k + 1) (by omega) (s := s₄) ⟨hS_len, hS_le, hS_mem⟩ ⟨hdeg_len, hdeg_get⟩
            (by simp [s₄, s₃, s₂, s₁, State.setReg,
              show (r_n : Reg) ≠ r_u from hne_un.symm,
              show (r_n : Reg) ≠ r_found from hne_fn.symm,
              show (r_n : Reg) ≠ r_du from hne_dun.symm,
              show (r_n : Reg) ≠ r_su from hne_sun.symm, hrn])
            (by simp [s₄, s₃, s₂, s₁, State.setReg,
              show (r_k_thr : Reg) ≠ r_u from hne_uk.symm,
              show (r_k_thr : Reg) ≠ r_found from hne_fk.symm,
              show (r_k_thr : Reg) ≠ r_du from hne_duk.symm,
              show (r_k_thr : Reg) ≠ r_su from hne_suk.symm, hrk_thr])
            (by simp [s₄])
            (by omega)
            (fun v hv => by
              rw [hf₄] at hv
              have hv_eq : v = uFin := Fin.ext hv.symm
              subst hv_eq
              exact ⟨hu_in_S, hdu_lt⟩)
            (fun h => by omega) with
          ⟨s₅, t₅, hex₅, ht₅, hf_le₅, hf_sound₅, hf_comp₅, harr₅, hreg₅⟩
        refine ⟨s₅, 3 + ((3 + (3 + (1 + (3 + 2)))) + 4) + t₅,
          .while_true hcond (by omega) (.seq (.seq hex₁ (.seq hex₂ hex_ite)) hex_inc) hex₅,
          by omega, hf_le₅, hf_sound₅, hf_comp₅, harr₅,
          fun r h1 h2 h3 h4 => by
            rw [hreg₅ r h1 h2 h3 h4]
            simp [s₄, s₃, s₂, s₁, State.setReg, h1, h2, h3, h4]⟩
      · have hcond_lt : (Expr.op .lt (.reg r_du) (.reg r_k_thr)).eval w s₂ = some 0 := by
          simp [s₂, s₁, State.setReg, show (r_k_thr : Reg) ≠ r_du from hne_duk.symm,
            show (r_k_thr : Reg) ≠ r_su from hne_suk.symm,
            Expr.eval, BinOp.eval, BinOp.raw, checkWord, hrk_thr, hdu_w, ‹k_thr < 2 ^ w›,
            hdu_lt, h0_w]
        have hex_inner : Exec w
            (.ite (.op .lt (.reg r_du) (.reg r_k_thr)) (.assign r_found (.reg r_u)) .skip)
            s₂ s₂ (3 + 1) :=
          .ite_false hcond_lt (.skip s₂)
        have hex_ite : Exec w
            (.ite (.reg r_su)
              (.ite (.op .lt (.reg r_du) (.reg r_k_thr)) (.assign r_found (.reg r_u)) .skip)
              .skip)
            s₂ s₂ (1 + (3 + 1)) :=
          .ite_true hcond_su hsu_ne hex_inner
        let s₄ := s₂.setReg r_u (k + 1)
        have hex_inc : Exec w (.assign r_u (.op .add (.reg r_u) (.const 1))) s₂ s₄ 4 :=
          .assign (by
            simp [s₂, s₁, State.setReg, show (r_u : Reg) ≠ r_du from hne_udu,
              show (r_u : Reg) ≠ r_su from hne_usu,
              Expr.eval, BinOp.eval, BinOp.raw, checkWord, hru, hk_w, hw,
              show k + 1 < 2 ^ w by omega])
        have hf₄ : s₄.regs r_found = s.regs r_found := by
          simp [s₄, s₂, s₁, State.setReg,
            show (r_found : Reg) ≠ r_u from hne_uf.symm,
            show (r_found : Reg) ≠ r_du from hne_duf.symm,
            show (r_found : Reg) ≠ r_su from hne_suf.symm]
        rcases ih (k + 1) (by omega) (s := s₄) ⟨hS_len, hS_le, hS_mem⟩ ⟨hdeg_len, hdeg_get⟩
            (by simp [s₄, s₂, s₁, State.setReg,
              show (r_n : Reg) ≠ r_u from hne_un.symm,
              show (r_n : Reg) ≠ r_du from hne_dun.symm,
              show (r_n : Reg) ≠ r_su from hne_sun.symm, hrn])
            (by simp [s₄, s₂, s₁, State.setReg,
              show (r_k_thr : Reg) ≠ r_u from hne_uk.symm,
              show (r_k_thr : Reg) ≠ r_du from hne_duk.symm,
              show (r_k_thr : Reg) ≠ r_su from hne_suk.symm, hrk_thr])
            (by simp [s₄])
            (by rw [hf₄]; exact hf_le)
            (fun v hv => hf_sound v (by rwa [← hf₄]))
            (fun h v hv_lt hvS => by
              rw [hf₄] at h
              by_cases hveq : v.1 = k
              · have hv_eq : v = uFin := Fin.ext hveq
                subst hv_eq
                omega
              · exact hf_comp h v (by omega) hvS) with
          ⟨s₅, t₅, hex₅, ht₅, hf_le₅, hf_sound₅, hf_comp₅, harr₅, hreg₅⟩
        refine ⟨s₅, 3 + ((3 + (3 + (1 + (3 + 1)))) + 4) + t₅,
          .while_true hcond (by omega) (.seq (.seq hex₁ (.seq hex₂ hex_ite)) hex_inc) hex₅,
          by omega, hf_le₅, hf_sound₅, hf_comp₅, harr₅,
          fun r h1 h2 h3 h4 => by
            rw [hreg₅ r h1 h2 h3 h4]
            simp [s₄, s₂, s₁, State.setReg, h1, h2, h3]⟩
    · have hsu_eq0 : su_val = 0 := not_ne_iff.mp ((hS_mem uFin).not.mpr hu_in_S)
      have hcond0 : (Expr.reg r_su).eval w s₂ = some 0 := by simpa [hsu_eq0] using hcond_su
      have hex_ite : Exec w
          (.ite (.reg r_su)
            (.ite (.op .lt (.reg r_du) (.reg r_k_thr)) (.assign r_found (.reg r_u)) .skip)
            .skip)
          s₂ s₂ (1 + 1) :=
        .ite_false hcond0 (.skip s₂)
      let s₄ := s₂.setReg r_u (k + 1)
      have hex_inc : Exec w (.assign r_u (.op .add (.reg r_u) (.const 1))) s₂ s₄ 4 :=
        .assign (by
          simp [s₂, s₁, State.setReg, show (r_u : Reg) ≠ r_du from hne_udu,
            show (r_u : Reg) ≠ r_su from hne_usu,
            Expr.eval, BinOp.eval, BinOp.raw, checkWord, hru, hk_w, hw,
            show k + 1 < 2 ^ w by omega])
      have hf₄ : s₄.regs r_found = s.regs r_found := by
        simp [s₄, s₂, s₁, State.setReg,
          show (r_found : Reg) ≠ r_u from hne_uf.symm,
          show (r_found : Reg) ≠ r_du from hne_duf.symm,
          show (r_found : Reg) ≠ r_su from hne_suf.symm]
      rcases ih (k + 1) (by omega) (s := s₄) ⟨hS_len, hS_le, hS_mem⟩ ⟨hdeg_len, hdeg_get⟩
          (by simp [s₄, s₂, s₁, State.setReg,
            show (r_n : Reg) ≠ r_u from hne_un.symm,
            show (r_n : Reg) ≠ r_du from hne_dun.symm,
            show (r_n : Reg) ≠ r_su from hne_sun.symm, hrn])
          (by simp [s₄, s₂, s₁, State.setReg,
            show (r_k_thr : Reg) ≠ r_u from hne_uk.symm,
            show (r_k_thr : Reg) ≠ r_du from hne_duk.symm,
            show (r_k_thr : Reg) ≠ r_su from hne_suk.symm, hrk_thr])
          (by simp [s₄])
          (by rw [hf₄]; exact hf_le)
          (fun v hv => hf_sound v (by rwa [← hf₄]))
          (fun h v hv_lt hvS => by
            rw [hf₄] at h
            by_cases hveq : v.1 = k
            · have hv_eq : v = uFin := Fin.ext hveq
              subst hv_eq
              exact False.elim (hu_in_S hvS)
            · exact hf_comp h v (by omega) hvS) with
        ⟨s₅, t₅, hex₅, ht₅, hf_le₅, hf_sound₅, hf_comp₅, harr₅, hreg₅⟩
      refine ⟨s₅, 3 + ((3 + (3 + (1 + 1))) + 4) + t₅,
        .while_true hcond (by omega) (.seq (.seq hex₁ (.seq hex₂ hex_ite)) hex_inc) hex₅,
        by omega, hf_le₅, hf_sound₅, hf_comp₅, harr₅,
        fun r h1 h2 h3 h4 => by
          rw [hreg₅ r h1 h2 h3 h4]
          simp [s₄, s₂, s₁, State.setReg, h1, h2, h3]⟩

/-- Execution theorem for `findLowDegVertexProg`: in `O(n)` steps, sets `r_found ≤ n` to either
some `v.1 < n` with `v ∈ S ∧ degInto G S v < k_thr` or `n` when every `v ∈ S` satisfies
`k_thr ≤ degInto G S v`. -/
theorem findLowDegVertexProg_exec {w n k_thr : ℕ} (G : SimpleGraph (Fin n)) (S : Finset (Fin n))
    (a_S a_deg : ℕ) (r_n r_k_thr r_u r_su r_du r_found : ℕ)
    (hne_un : r_u ≠ r_n) (hne_sun : r_su ≠ r_n) (hne_dun : r_du ≠ r_n) (hne_fn : r_found ≠ r_n)
    (hne_uk : r_u ≠ r_k_thr) (hne_suk : r_su ≠ r_k_thr) (hne_duk : r_du ≠ r_k_thr)
    (hne_fk : r_found ≠ r_k_thr)
    (hne_usu : r_u ≠ r_su) (hne_udu : r_u ≠ r_du) (hne_uf : r_u ≠ r_found)
    (hne_sudu : r_su ≠ r_du) (hne_suf : r_su ≠ r_found) (hne_duf : r_du ≠ r_found)
    (hw : 1 < 2 ^ w) (hn_w : n < 2 ^ w) (hk_w : k_thr < 2 ^ w)
    {s : State}
    (hS : IsBitSet S a_S s)
    (hdeg : IsDegIntoArr G S a_deg s)
    (hrn : s.regs r_n = n)
    (hrk_thr : s.regs r_k_thr = k_thr) :
    ∃ s' t,
      Exec w (findLowDegVertexProg a_S a_deg r_n r_k_thr r_u r_su r_du r_found) s s' t ∧
      t ≤ 7 + 19 * n ∧
      s'.regs r_found ≤ n ∧
      (∀ v : Fin n, s'.regs r_found = v.1 → v ∈ S ∧ degInto G S v < k_thr) ∧
      (s'.regs r_found = n → ∀ v ∈ S, k_thr ≤ degInto G S v) ∧
      (∀ a : Arr, s'.arrs a = s.arrs a) ∧
      (∀ r : Reg, r ≠ r_u → r ≠ r_su → r ≠ r_du → r ≠ r_found → s'.regs r = s.regs r) := by
  have h0_w : 0 < 2 ^ w := by omega
  let s₁ := s.setReg r_found n
  have hex₁ : Exec w (.assign r_found (.reg r_n)) s s₁ 2 :=
    .assign (by simp [Expr.eval, checkWord, hrn, hn_w])
  let s₂ := s₁.setReg r_u 0
  have hex₂ : Exec w (.assign r_u (.const 0)) s₁ s₂ 2 :=
    .assign (by simp [Expr.eval, checkWord, h0_w])
  rcases findLowDegVertexLoop_exec G S a_S a_deg r_n r_k_thr r_u r_su r_du r_found
      hne_un hne_sun hne_dun hne_fn hne_uk hne_suk hne_duk hne_fk
      hne_usu hne_udu hne_uf hne_sudu hne_suf hne_duf
      hw hn_w hk_w n 0 (by omega) (s := s₂) hS hdeg
      (by simp [s₂, s₁, State.setReg, show (r_n : Reg) ≠ r_u from hne_un.symm,
        show (r_n : Reg) ≠ r_found from hne_fn.symm, hrn])
      (by simp [s₂, s₁, State.setReg, show (r_k_thr : Reg) ≠ r_u from hne_uk.symm,
        show (r_k_thr : Reg) ≠ r_found from hne_fk.symm, hrk_thr])
      (by simp [s₂])
      (by simp [s₂, s₁, State.setReg, show (r_found : Reg) ≠ r_u from hne_uf.symm])
      (fun v hv => by
        simp [s₂, s₁, State.setReg, show (r_found : Reg) ≠ r_u from hne_uf.symm] at hv
        omega)
      (fun _ _ h => by omega) with
    ⟨s₃, t₃, hex₃, ht₃, hf_le₃, hf_sound₃, hf_comp₃, harr₃, hreg₃⟩
  refine ⟨s₃, 2 + (2 + t₃), .seq hex₁ (.seq hex₂ hex₃), by omega,
    hf_le₃, hf_sound₃, hf_comp₃, harr₃,
    fun r h1 h2 h3 h4 => by
      rw [hreg₃ r h1 h2 h3 h4]
      simp [s₂, s₁, State.setReg, h1, h4]⟩

end GraphMinor.Compute
