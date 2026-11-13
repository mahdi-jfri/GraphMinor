module

public import GraphMinor.Compute.Neighborhood
public import GraphMinor.Compute.Parse
public import Mathlib.Combinatorics.SimpleGraph.DegreeSum

/-!
# Restricting a Graph to a Vertex Subset on the Word RAM

This file defines the restriction of a simple graph `G : SimpleGraph (Fin n)` to a vertex subset
`Y : Finset (Fin n)` as a spanning subgraph `restrictGraph G Y : SimpleGraph (Fin n)`, proves its
combinatorial relationships with induced subgraphs, external neighborhoods, degrees into a subset,
and edge counts, and implements a linear-time Word RAM CSR builder `restrictGraphProg`.

## Main definitions and theorems

* `GraphMinor.Compute.restrictGraph`: the simple graph on `Fin n` whose edges are the edges of `G`
  with both endpoints in `Y`.
* `GraphMinor.Compute.restrictGraph_induce_eq_of_subset`: for `X ⊆ Y`, the induced subgraph of
  `restrictGraph G Y` on `X` coincides with `G.induce X`.
* `GraphMinor.Compute.extNeighborhood_restrictGraph_eq`: for `X ⊆ Y`,
  `extNeighborhood (restrictGraph G Y) X = extNeighborhood G X ∩ Y`.
* `GraphMinor.Compute.degInto_restrictGraph_eq`: for `S ⊆ Y` and `u ∈ Y`,
  `degInto (restrictGraph G Y) S u = degInto G S u`.
* `GraphMinor.Compute.totalAdjEntries_eq_two_mul_card_edgeFinset`: for any `IsAdjListFamily G lists`,
  `totalAdjEntries lists = 2 * G.edgeFinset.card`.
* `GraphMinor.Compute.restrictGraphProg` and `GraphMinor.Compute.restrictGraphProg_exec`: builds CSR
  adjacency lists `(a_rstart, a_rend, a_rentries)` for `restrictGraph G Y` in `O(n + m)` steps and
  leaves `2 * (edgesInSet G Y).card` in the cursor register `r_cnt`.
-/

@[expose] public section

namespace GraphMinor.Compute

open SimpleGraph

/-! ### Section 1: Pure Graph Restriction on `Fin n` -/

/-- The restriction of `G : SimpleGraph (Fin n)` to a vertex subset `Y : Finset (Fin n)`, viewed as
a simple graph on `Fin n` in which vertices outside `Y` are isolated. -/
def restrictGraph {n : ℕ} (G : SimpleGraph (Fin n)) (Y : Finset (Fin n)) : SimpleGraph (Fin n) where
  Adj u v := u ∈ Y ∧ v ∈ Y ∧ G.Adj u v
  symm := ⟨fun _ _ ⟨hu, hv, hadj⟩ => ⟨hv, hu, hadj.symm⟩⟩
  loopless := ⟨fun _ ⟨_, _, hadj⟩ => G.loopless.irrefl _ hadj⟩

instance instDecidableRelRestrictGraphAdj {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (Y : Finset (Fin n)) : DecidableRel (restrictGraph G Y).Adj :=
  fun u v => inferInstanceAs (Decidable (u ∈ Y ∧ v ∈ Y ∧ G.Adj u v))

@[simp]
theorem restrictGraph_adj {n : ℕ} (G : SimpleGraph (Fin n)) (Y : Finset (Fin n)) (u v : Fin n) :
    (restrictGraph G Y).Adj u v ↔ u ∈ Y ∧ v ∈ Y ∧ G.Adj u v :=
  Iff.rfl

@[simp]
theorem restrictGraph_univ {n : ℕ} (G : SimpleGraph (Fin n)) :
    restrictGraph G Finset.univ = G := by
  ext u v
  simp

@[simp]
theorem restrictGraph_idem {n : ℕ} (G : SimpleGraph (Fin n)) (Y : Finset (Fin n)) :
    restrictGraph (restrictGraph G Y) Y = restrictGraph G Y := by
  ext u v
  simp
  tauto

/-- If `X ⊆ Y`, the induced subgraph of `restrictGraph G Y` on `X` is identical to the induced
subgraph of `G` on `X`. -/
theorem restrictGraph_induce_eq_of_subset {n : ℕ} (G : SimpleGraph (Fin n))
    {X Y : Finset (Fin n)} (hXY : X ⊆ Y) :
    (restrictGraph G Y).induce (X : Set (Fin n)) = G.induce (X : Set (Fin n)) := by
  ext ⟨u, hu⟩ ⟨v, hv⟩
  simp only [comap_adj, Function.Embedding.coe_subtype, restrictGraph_adj]
  have huX : u ∈ X := Finset.mem_coe.mp hu
  have hvX : v ∈ X := Finset.mem_coe.mp hv
  exact ⟨fun ⟨_, _, hadj⟩ => hadj, fun hadj => ⟨hXY huX, hXY hvX, hadj⟩⟩

theorem connected_induce_restrictGraph_iff {n : ℕ} (G : SimpleGraph (Fin n))
    {X Y : Finset (Fin n)} (hXY : X ⊆ Y) :
    ((restrictGraph G Y).induce (X : Set (Fin n))).Connected ↔
      (G.induce (X : Set (Fin n))).Connected := by
  rw [restrictGraph_induce_eq_of_subset G hXY]

/-- The edge finset of `restrictGraph G Y` is `edgesInSet G Y`. -/
theorem edgeFinset_restrictGraph {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (Y : Finset (Fin n)) [DecidableRel (restrictGraph G Y).Adj] :
    (restrictGraph G Y).edgeFinset = edgesInSet G Y := by
  ext e
  induction e using Sym2.ind with
  | _ u v =>
    rw [mem_edgeFinset, mem_edgesInSet, mem_edgeFinset]
    simp only [mem_edgeSet, restrictGraph_adj, Sym2.mem_iff, forall_eq_or_imp, forall_eq]
    tauto

theorem card_edgeFinset_restrictGraph {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (Y : Finset (Fin n)) [DecidableRel (restrictGraph G Y).Adj] :
    (restrictGraph G Y).edgeFinset.card = (edgesInSet G Y).card := by
  rw [edgeFinset_restrictGraph]

theorem card_edgesInSet_le_card_edgeFinset {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (Y : Finset (Fin n)) :
    (edgesInSet G Y).card ≤ G.edgeFinset.card := by
  apply Finset.card_le_card
  intro e he
  exact (mem_edgesInSet G Y e).mp he |>.1

theorem edgesInSet_univ {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] :
    edgesInSet G Finset.univ = G.edgeFinset := by
  ext e
  simp [edgesInSet]

theorem edgesInSet_restrictGraph_of_subset {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    {Y Z : Finset (Fin n)} (hZY : Z ⊆ Y) :
    edgesInSet (restrictGraph G Y) Z = edgesInSet G Z := by
  ext e
  induction e using Sym2.ind with
  | _ u v =>
    rw [mem_edgesInSet, mem_edgesInSet, mem_edgeFinset, mem_edgeFinset]
    simp only [mem_edgeSet, restrictGraph_adj, Sym2.mem_iff, forall_eq_or_imp, forall_eq]
    constructor
    · rintro ⟨⟨_, _, hadj⟩, huZ, hvZ⟩
      exact ⟨hadj, huZ, hvZ⟩
    · rintro ⟨hadj, huZ, hvZ⟩
      exact ⟨⟨hZY huZ, hZY hvZ, hadj⟩, huZ, hvZ⟩

/-- External neighborhood in `restrictGraph G Y` when `X ⊆ Y`. -/
theorem extNeighborhood_restrictGraph_eq {n : ℕ} (G : SimpleGraph (Fin n))
    {X Y : Finset (Fin n)} (hXY : X ⊆ Y) :
    extNeighborhood (restrictGraph G Y) X = extNeighborhood G X ∩ Y := by
  ext w
  simp only [mem_extNeighborhood, Finset.mem_inter, restrictGraph_adj]
  constructor
  · rintro ⟨hwX, u, huX, _, hwY, hadj⟩
    exact ⟨⟨hwX, u, huX, hadj⟩, hwY⟩
  · rintro ⟨⟨hwX, u, huX, hadj⟩, hwY⟩
    exact ⟨hwX, u, huX, hXY huX, hwY, hadj⟩

theorem extNeighborhood_restrictGraph_subset {n : ℕ} (G : SimpleGraph (Fin n))
    (Y X : Finset (Fin n)) :
    extNeighborhood (restrictGraph G Y) X ⊆ Y := by
  intro w hw
  rcases (mem_extNeighborhood (restrictGraph G Y) X w).mp hw with ⟨_, _, _, _, hwY, _⟩
  exact hwY

/-- Degree into a subset `S ⊆ Y` in `restrictGraph G Y` for a vertex `u ∈ Y`. -/
theorem degInto_restrictGraph_eq {n : ℕ} (G : SimpleGraph (Fin n))
    {Y S : Finset (Fin n)} (hSY : S ⊆ Y) {u : Fin n} (huY : u ∈ Y) :
    degInto (restrictGraph G Y) S u = degInto G S u := by
  classical
  unfold degInto
  congr 1
  apply Finset.ext
  intro w
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, restrictGraph_adj]
  exact ⟨fun ⟨hwS, _, _, hadj⟩ => ⟨hwS, hadj⟩, fun ⟨hwS, hadj⟩ => ⟨hwS, huY, hSY hwS, hadj⟩⟩

theorem degInto_restrictGraph_of_notMem {n : ℕ} (G : SimpleGraph (Fin n))
    (Y S : Finset (Fin n)) {u : Fin n} (huY : u ∉ Y) :
    degInto (restrictGraph G Y) S u = 0 := by
  unfold degInto
  rw [Finset.card_eq_zero, Finset.ext_iff]
  intro w
  simp [huY]

/-- For `u : Fin n`, `degInto G Finset.univ u` equals `G.degree u`. -/
theorem degInto_univ_eq_degree {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (u : Fin n) :
    degInto G Finset.univ u = G.degree u := by
  classical
  unfold degInto
  rw [← card_neighborFinset_eq_degree]
  congr 1
  apply Finset.ext
  intro w
  simp [mem_neighborFinset]

theorem countInBitSet_univ {n : ℕ} (l : List ℕ) (hlt : ∀ x ∈ l, x < n) (j : ℕ) (hj : j ≤ l.length) :
    countInBitSet (Finset.univ : Finset (Fin n)) l j = j := by
  induction j with
  | zero => simp [countInBitSet]
  | succ j ih =>
    have hj_lt : j < l.length := by omega
    have hw_lt : l[j] < n := hlt l[j] (List.getElem_mem hj_lt)
    rw [countInBitSet, ih (by omega)]
    simp [hj_lt, hw_lt]

/-- In any adjacency-list representation `lists` of `G`, `(lists u).length = G.degree u`. -/
theorem length_eq_degree_of_isAdjListFamily {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
    {lists : Fin n → List ℕ} (hlists : IsAdjListFamily G lists) (u : Fin n) :
    (lists u).length = G.degree u := by
  have h1 := countInBitSet_full_eq_degInto hlists (Finset.univ : Finset (Fin n)) u
  have h2 := countInBitSet_univ (lists u) (hlists u).1 (lists u).length le_rfl
  rw [h2, degInto_univ_eq_degree] at h1
  exact h1

/-- Total number of directed entries in any adjacency-list representation of `G` equals
`2 * G.edgeFinset.card`. -/
theorem totalAdjEntries_eq_two_mul_card_edgeFinset {n : ℕ} {G : SimpleGraph (Fin n)}
    [DecidableRel G.Adj] {lists : Fin n → List ℕ} (hlists : IsAdjListFamily G lists) :
    totalAdjEntries lists = 2 * G.edgeFinset.card := by
  unfold totalAdjEntries
  have hdeg : ∀ u : Fin n, (lists u).length = G.degree u :=
    length_eq_degree_of_isAdjListFamily hlists
  simp_rw [hdeg]
  exact G.sum_degrees_eq_twice_card_edges

/-- Handshaking identity on an induced vertex set `Y`:
`∑ u ∈ Y, degInto G Y u = 2 * (edgesInSet G Y).card`. -/
theorem sum_degInto_eq_two_mul_card_edgesInSet {n : ℕ} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (Y : Finset (Fin n)) :
    (∑ u ∈ Y, degInto G Y u) = 2 * (edgesInSet G Y).card := by
  have hhand := (restrictGraph G Y).sum_degrees_eq_twice_card_edges
  rw [card_edgeFinset_restrictGraph] at hhand
  rw [← hhand]
  have hsplit :
      (∑ u : Fin n, (restrictGraph G Y).degree u) =
        (∑ u ∈ Y, (restrictGraph G Y).degree u) +
          (∑ u ∈ Finset.univ \ Y, (restrictGraph G Y).degree u) := by
    rw [← Finset.sum_union Finset.disjoint_sdiff]
    congr 1
    ext u
    simp
  rw [hsplit]
  have hzero : (∑ u ∈ Finset.univ \ Y, (restrictGraph G Y).degree u) = 0 := by
    apply Finset.sum_eq_zero
    intro u hu
    rw [Finset.mem_sdiff] at hu
    rw [← degInto_univ_eq_degree]
    exact degInto_restrictGraph_of_notMem G Y Finset.univ hu.2
  rw [hzero, Nat.add_zero]
  apply Finset.sum_congr rfl
  intro u huY
  rw [← degInto_univ_eq_degree]
  have hdeg_eq : degInto (restrictGraph G Y) Finset.univ u = degInto G Y u := by
    classical
    unfold degInto
    congr 1
    apply Finset.ext
    intro w
    simp [huY]
  exact hdeg_eq.symm

/-! ### Section 2: Filtered Adjacency Lists (`restrictList`) -/

/-- Filter the first `j` elements of `l` (the adjacency list of `u`), keeping `l[i]` if and only if
both `u ∈ Y` and `l[i] ∈ Y`. -/
def restrictListUpTo {n : ℕ} (Y : Finset (Fin n)) (u : Fin n) (l : List ℕ) : ℕ → List ℕ
  | 0 => []
  | j + 1 =>
    restrictListUpTo Y u l j ++
      if h : j < l.length then
        if hlt : l[j] < n then
          if u ∈ Y ∧ (⟨l[j], hlt⟩ : Fin n) ∈ Y then [l[j]] else []
        else []
      else []

/-- Full restricted adjacency list for vertex `u`. -/
def restrictList {n : ℕ} (Y : Finset (Fin n)) (u : Fin n) (l : List ℕ) : List ℕ :=
  restrictListUpTo Y u l l.length

/-- Family of restricted adjacency lists for `restrictGraph G Y`. -/
def restrictListFamily {n : ℕ} (Y : Finset (Fin n)) (lists : Fin n → List ℕ) (u : Fin n) : List ℕ :=
  restrictList Y u (lists u)

theorem mem_restrictListUpTo_iff {n : ℕ} (Y : Finset (Fin n)) (u : Fin n) (l : List ℕ)
    (hlt : ∀ x ∈ l, x < n) (j : ℕ) (hj : j ≤ l.length) (x : ℕ) :
    x ∈ restrictListUpTo Y u l j ↔
      x ∈ l.take j ∧ u ∈ Y ∧ ∃ hx : x < n, (⟨x, hx⟩ : Fin n) ∈ Y := by
  induction j with
  | zero => simp [restrictListUpTo]
  | succ j ih =>
    have hj_lt : j < l.length := by omega
    have hw_lt : l[j] < n := hlt l[j] (List.getElem_mem hj_lt)
    rw [restrictListUpTo, take_add_one_eq_append_getElem l j hj_lt]
    simp only [hj_lt, hw_lt, ↓reduceDIte]
    split_ifs with hcond
    · simp only [List.mem_append, List.mem_singleton, ih (by omega)]
      constructor
      · rintro (⟨hx_take, huY, hx_lt, hxY⟩ | rfl)
        · exact ⟨Or.inl hx_take, huY, hx_lt, hxY⟩
        · exact ⟨Or.inr rfl, hcond.1, hw_lt, hcond.2⟩
      · rintro ⟨hx_take | rfl, huY, hx_lt, hxY⟩
        · exact Or.inl ⟨hx_take, huY, hx_lt, hxY⟩
        · exact Or.inr rfl
    · simp only [List.append_nil, List.mem_append, List.mem_singleton, ih (by omega)]
      constructor
      · rintro ⟨hx_take, huY, hx_lt, hxY⟩
        exact ⟨Or.inl hx_take, huY, hx_lt, hxY⟩
      · rintro ⟨hx_take | rfl, huY, hx_lt, hxY⟩
        · exact ⟨hx_take, huY, hx_lt, hxY⟩
        · exfalso
          exact hcond ⟨huY, hxY⟩

theorem restrictListUpTo_nodup {n : ℕ} (Y : Finset (Fin n)) (u : Fin n) (l : List ℕ)
    (hlt : ∀ x ∈ l, x < n) (hnodup : l.Nodup) (j : ℕ) (hj : j ≤ l.length) :
    (restrictListUpTo Y u l j).Nodup := by
  induction j with
  | zero => simp [restrictListUpTo]
  | succ j ih =>
    have hj_lt : j < l.length := by omega
    have hw_lt : l[j] < n := hlt l[j] (List.getElem_mem hj_lt)
    rw [restrictListUpTo]
    simp only [hj_lt, hw_lt, ↓reduceDIte]
    split_ifs with hcond
    · rw [List.nodup_append]
      refine ⟨ih (by omega), List.nodup_singleton _, ?_⟩
      intro x hx y hy hxy
      rw [List.mem_singleton] at hy
      have hxj : x = l[j] := hxy.trans hy
      have hx_take := (mem_restrictListUpTo_iff Y u l hlt j (by omega) x).mp hx |>.1
      rw [hxj, List.mem_iff_getElem] at hx_take
      rcases hx_take with ⟨i, hi, heq⟩
      rw [List.length_take] at hi
      rw [List.getElem_take] at heq
      have hne : i ≠ j := by omega
      exact hne ((List.Nodup.getElem_inj_iff hnodup).mp heq)
    · simp [ih (by omega)]

theorem restrictListUpTo_length_mono {n : ℕ} (Y : Finset (Fin n)) (u : Fin n) (l : List ℕ)
    {a b : ℕ} (hab : a ≤ b) :
    (restrictListUpTo Y u l a).length ≤ (restrictListUpTo Y u l b).length := by
  induction hab with
  | refl => exact le_rfl
  | step _ ih =>
    rw [restrictListUpTo]
    split_ifs <;> simp <;> omega

theorem restrictListUpTo_length_le {n : ℕ} (Y : Finset (Fin n)) (u : Fin n) (l : List ℕ) (j : ℕ) :
    (restrictListUpTo Y u l j).length ≤ j := by
  induction j with
  | zero => simp [restrictListUpTo]
  | succ j ih =>
    unfold restrictListUpTo
    split_ifs <;> simp <;> omega

theorem isAdjListFamily_restrictListFamily {n : ℕ} {G : SimpleGraph (Fin n)}
    {lists : Fin n → List ℕ} (hlists : IsAdjListFamily G lists) (Y : Finset (Fin n)) :
    IsAdjListFamily (restrictGraph G Y) (restrictListFamily Y lists) := by
  intro u
  rcases hlists u with ⟨hlt, hnodup, hlen_le, hadj_iff⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro x hx
    rcases (mem_restrictListUpTo_iff Y u (lists u) hlt (lists u).length le_rfl x).mp hx with
      ⟨_, _, hx_lt, _⟩
    exact hx_lt
  · exact restrictListUpTo_nodup Y u (lists u) hlt hnodup (lists u).length le_rfl
  · exact Nat.le_trans (restrictListUpTo_length_le Y u (lists u) (lists u).length) hlen_le
  · intro v
    rw [restrictListFamily, restrictList,
      mem_restrictListUpTo_iff Y u (lists u) hlt (lists u).length le_rfl v.1]
    rw [List.take_length, hadj_iff v]
    simp only [v.2, exists_true_left, restrictGraph_adj]
    tauto

theorem totalAdjEntries_restrictListFamily {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
    {lists : Fin n → List ℕ} (hlists : IsAdjListFamily G lists) (Y : Finset (Fin n)) :
    totalAdjEntries (restrictListFamily Y lists) = 2 * (edgesInSet G Y).card := by
  have h1 := totalAdjEntries_eq_two_mul_card_edgeFinset (isAdjListFamily_restrictListFamily hlists Y)
  rw [card_edgeFinset_restrictGraph] at h1
  exact h1

/-- Prefix sum of lengths of `restrictListFamily Y lists u'` for `u' < k`. -/
def prefixRestrictedLen {n : ℕ} (Y : Finset (Fin n)) (lists : Fin n → List ℕ) (k : ℕ) : ℕ :=
  ∑ u ∈ Finset.univ.filter (fun u : Fin n => u.1 < k), (restrictListFamily Y lists u).length

@[simp]
theorem prefixRestrictedLen_zero {n : ℕ} (Y : Finset (Fin n)) (lists : Fin n → List ℕ) :
    prefixRestrictedLen Y lists 0 = 0 := by
  simp [prefixRestrictedLen]

theorem prefixRestrictedLen_succ {n : ℕ} (Y : Finset (Fin n)) (lists : Fin n → List ℕ)
    (u : Fin n) :
    prefixRestrictedLen Y lists (u.1 + 1) =
      prefixRestrictedLen Y lists u.1 + (restrictListFamily Y lists u).length := by
  unfold prefixRestrictedLen
  have hset :
      Finset.univ.filter (fun x : Fin n => x.1 < u.1 + 1) =
        insert u (Finset.univ.filter (fun x : Fin n => x.1 < u.1)) := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_univ, Finset.mem_insert, Fin.ext_iff, true_and]
    omega
  have hnot_mem : u ∉ Finset.univ.filter (fun x : Fin n => x.1 < u.1) := by
    simp
  rw [hset, Finset.sum_insert hnot_mem, Nat.add_comm]

theorem prefixRestrictedLen_mono {n : ℕ} (Y : Finset (Fin n)) (lists : Fin n → List ℕ)
    {a b : ℕ} (hab : a ≤ b) :
    prefixRestrictedLen Y lists a ≤ prefixRestrictedLen Y lists b := by
  apply Finset.sum_le_sum_of_subset
  intro u hu
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hu ⊢
  omega

theorem prefixRestrictedLen_full {n : ℕ} (Y : Finset (Fin n)) (lists : Fin n → List ℕ) :
    prefixRestrictedLen Y lists n = totalAdjEntries (restrictListFamily Y lists) := by
  unfold prefixRestrictedLen totalAdjEntries
  congr 1
  ext u
  simp

theorem prefixRestrictedLen_add_lt {n : ℕ} (Y : Finset (Fin n)) (lists : Fin n → List ℕ)
    {u' : Fin n} {u : ℕ} (hu' : u'.1 < u) {k : ℕ}
    (hk : k < (restrictListFamily Y lists u').length) :
    prefixRestrictedLen Y lists u'.1 + k < prefixRestrictedLen Y lists u := by
  have h1 := prefixRestrictedLen_succ Y lists u'
  have h2 := prefixRestrictedLen_mono Y lists (show u'.1 + 1 ≤ u by omega)
  omega

/-! ### Section 3: Word RAM Program `restrictGraphProg` -/

/-- Inner body for `restrictGraphProg`: if `r_yu != 0`, reads `r_yw := a_Y[r_w]`; if `r_yw != 0`,
appends `r_w` to vertex `r_u`'s list in `(a_rend, a_rentries)` at cursor `r_cnt`. -/
def restrictNeighborBody (a_Y a_rend a_rentries : Arr) (r_u r_yu r_cnt r_w r_yw : Reg) : Cmd :=
  .ite (.reg r_yu)
    (.seq (.assign r_yw (.read a_Y (.reg r_w)))
      (.ite (.reg r_yw)
        (listAppend a_rend a_rentries r_u r_cnt (.reg r_w))
        .skip))
    .skip

/-- Per-vertex body for `restrictGraphProg`: sets `a_rstart[r_u] := r_cnt`, `a_rend[r_u] := r_cnt`,
reads `r_yu := a_Y[r_u]`, and iterates over `r_u`'s adjacency list in `(a_start, a_end, a_entries)`. -/
def restrictVertexCmd (a_start a_end a_entries a_Y a_rstart a_rend a_rentries : Arr)
    (r_u r_yu r_cnt r_k r_hi r_w r_yw : Reg) : Cmd :=
  .seq (.write a_rstart (.reg r_u) (.reg r_cnt))
    (.seq (.write a_rend (.reg r_u) (.reg r_cnt))
      (.seq (.assign r_yu (.read a_Y (.reg r_u)))
        (forList a_start a_end a_entries r_u r_k r_hi r_w
          (restrictNeighborBody a_Y a_rend a_rentries r_u r_yu r_cnt r_w r_yw))))

/-- Build CSR adjacency lists `(a_rstart, a_rend, a_rentries)` for `restrictGraph G Y` from
CSR adjacency lists `(a_start, a_end, a_entries)` of `G` and bit-set `a_Y` for `Y`, allocating
`a_rentries` to capacity `r_cap`. Leaves `2 * (edgesInSet G Y).card` in `r_cnt`. -/
def restrictGraphProg (a_start a_end a_entries a_Y a_rstart a_rend a_rentries : Arr)
    (r_n r_cap r_u r_yu r_cnt r_k r_hi r_w r_yw : Reg) : Cmd :=
  .seq (.alloc a_rstart (.reg r_n))
    (.seq (.alloc a_rend (.reg r_n))
      (.seq (.alloc a_rentries (.reg r_cap))
        (.seq (.assign r_cnt (.const 0))
          (.seq (.assign r_u (.const 0))
            (forUp r_u (.reg r_n)
              (restrictVertexCmd a_start a_end a_entries a_Y a_rstart a_rend a_rentries
                r_u r_yu r_cnt r_k r_hi r_w r_yw))))))

private lemma isListAt_preserve_prev_restrict {a_rstart a_rend a_rentries : ℕ}
    (hne_se : a_rstart ≠ a_rend) (hne_sent : a_rstart ≠ a_rentries) (hne_eent : a_rend ≠ a_rentries)
    {u' u st' cnt val_end val_ent : ℕ} {l' : List ℕ} {s : State}
    (hu'_ne : u' ≠ u) (hbound : st' + l'.length ≤ cnt)
    (hlist : IsListAt a_rstart a_rend a_rentries u' st' (st' + l'.length) l' s) :
    IsListAt a_rstart a_rend a_rentries u' st' (st' + l'.length) l'
      ((s.writeArr a_rentries cnt val_ent).writeArr a_rend u val_end) := by
  have hne_se' : (a_rstart : Arr) ≠ a_rend := hne_se
  have hne_sent' : (a_rstart : Arr) ≠ a_rentries := hne_sent
  have hne_eent' : (a_rend : Arr) ≠ a_rentries := hne_eent
  rcases hlist with ⟨hu'_st, hu'_en, hen_ent, hdiff, hst, hen, hle, helem⟩
  refine ⟨by simpa using hu'_st,
    by simpa using hu'_en,
    by simpa using hen_ent,
    hdiff,
    by simpa [hne_se', hne_sent'] using hst,
    ?_, hle, ?_⟩
  · simp only [State.writeArr_arrs_self, State.writeArr_arrs_ne _ _ _ hne_eent']
    rw [List.getElem_set_ne hu'_ne.symm]
    exact hen
  · intro k hk
    simp only [State.writeArr_arrs_ne _ _ _ hne_eent'.symm, State.writeArr_arrs_self]
    rw [List.getElem_set_ne (by omega)]
    exact helem k hk

theorem restrictVertexCmd_exec {w n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (lists : Fin n → List ℕ) (Y : Finset (Fin n)) (u : Fin n) (cap : ℕ)
    (a_start a_end a_entries a_Y a_rstart a_rend a_rentries : ℕ)
    (r_u r_yu r_cnt r_k r_hi r_w r_yw : ℕ)
    (hne_st_rs : a_start ≠ a_rstart) (hne_st_re : a_start ≠ a_rend) (hne_st_rent : a_start ≠ a_rentries)
    (hne_en_rs : a_end ≠ a_rstart) (hne_en_re : a_end ≠ a_rend) (hne_en_rent : a_end ≠ a_rentries)
    (hne_ent_rs : a_entries ≠ a_rstart) (hne_ent_re : a_entries ≠ a_rend) (hne_ent_rent : a_entries ≠ a_rentries)
    (hne_Y_rs : a_Y ≠ a_rstart) (hne_Y_re : a_Y ≠ a_rend) (hne_Y_rent : a_Y ≠ a_rentries)
    (hne_rs_re : a_rstart ≠ a_rend) (hne_rs_rent : a_rstart ≠ a_rentries) (hne_re_rent : a_rend ≠ a_rentries)
    (hne_kh : r_k ≠ r_hi) (hne_uk : r_u ≠ r_k) (hne_uh : r_u ≠ r_hi)
    (hne_uyu : r_u ≠ r_yu) (hne_ucnt : r_u ≠ r_cnt) (hne_uw : r_u ≠ r_w) (hne_uyw : r_u ≠ r_yw)
    (hne_yuk : r_yu ≠ r_k) (hne_yuh : r_yu ≠ r_hi) (hne_yucnt : r_yu ≠ r_cnt)
    (hne_yuw : r_yu ≠ r_w) (hne_yuyw : r_yu ≠ r_yw)
    (hne_cntk : r_cnt ≠ r_k) (hne_cnth : r_cnt ≠ r_hi) (hne_cntw : r_cnt ≠ r_w) (hne_cntyw : r_cnt ≠ r_yw)
    (hne_kw : r_k ≠ r_w) (hne_kyw : r_k ≠ r_yw) (hne_hw : r_hi ≠ r_w) (hne_hyw : r_hi ≠ r_yw)
    (hne_wyw : r_w ≠ r_yw)
    (hw : 1 < 2 ^ w) (hn_w : n < 2 ^ w) (hcap_w : cap < 2 ^ w)
    (hcap_bound : totalAdjEntries (restrictListFamily Y lists) ≤ cap)
    {s : State}
    (hadj : IsAdjList G a_start a_end a_entries lists s)
    (hent_w : (s.arrs a_entries).length < 2 ^ w)
    (hY : IsBitSet Y a_Y s)
    (hrs_len : (s.arrs a_rstart).length = n)
    (hre_len : (s.arrs a_rend).length = n)
    (hrent_len : (s.arrs a_rentries).length = cap)
    (hru : s.regs r_u = u.1)
    (hrcnt : s.regs r_cnt = prefixRestrictedLen Y lists u.1)
    (hprev : ∀ u' : Fin n, u'.1 < u.1 →
      IsListAt a_rstart a_rend a_rentries u'.1 (prefixRestrictedLen Y lists u'.1)
        (prefixRestrictedLen Y lists u'.1 + (restrictListFamily Y lists u').length)
        (restrictListFamily Y lists u') s) :
    ∃ s' t,
      Exec w (restrictVertexCmd a_start a_end a_entries a_Y a_rstart a_rend a_rentries
        r_u r_yu r_cnt r_k r_hi r_w r_yw) s s' t ∧
      t ≤ 18 + 25 * (lists u).length ∧
      s'.regs r_u = u.1 ∧
      s'.regs r_cnt = prefixRestrictedLen Y lists (u.1 + 1) ∧
      (s'.arrs a_rstart).length = n ∧
      (s'.arrs a_rend).length = n ∧
      (s'.arrs a_rentries).length = cap ∧
      (∀ u' : Fin n, u'.1 < u.1 + 1 →
        IsListAt a_rstart a_rend a_rentries u'.1 (prefixRestrictedLen Y lists u'.1)
          (prefixRestrictedLen Y lists u'.1 + (restrictListFamily Y lists u').length)
          (restrictListFamily Y lists u') s') ∧
      (∀ a : Arr, a ≠ a_rstart → a ≠ a_rend → a ≠ a_rentries → s'.arrs a = s.arrs a) ∧
      (∀ r : Reg, r ≠ r_yu → r ≠ r_cnt → r ≠ r_k → r ≠ r_hi → r ≠ r_w → r ≠ r_yw →
        s'.regs r = s.regs r) := by
  let st_u := prefixRestrictedLen Y lists u.1
  have hst_u_end_le : st_u + (restrictListFamily Y lists u).length ≤ cap := by
    have h1 := prefixRestrictedLen_succ Y lists u
    have h2 := prefixRestrictedLen_mono Y lists (show u.1 + 1 ≤ n by omega)
    rw [prefixRestrictedLen_full] at h2
    dsimp [st_u]
    omega
  have hu_w : u.1 < 2 ^ w := by omega
  have hst_u_w : prefixRestrictedLen Y lists u.1 < 2 ^ w := by dsimp [st_u] at hst_u_end_le; omega
  -- 1. a_rstart[r_u] := r_cnt (cost 3)
  let s₁ := s.writeArr a_rstart u.1 st_u
  have hex₁ : Exec w (.write a_rstart (.reg r_u) (.reg r_cnt)) s s₁ 3 :=
    .write (by simp [Expr.eval, checkWord, hru, hu_w])
      (by simp [Expr.eval, checkWord, hrcnt, hst_u_w, st_u])
      (by rw [hrs_len]; exact u.2)
  -- 2. a_rend[r_u] := r_cnt (cost 3)
  let s₂ := s₁.writeArr a_rend u.1 st_u
  have hex₂ : Exec w (.write a_rend (.reg r_u) (.reg r_cnt)) s₁ s₂ 3 :=
    .write (by simp [s₁, Expr.eval, checkWord, hru, hu_w])
      (by simp [s₁, Expr.eval, checkWord, hrcnt, hst_u_w, st_u])
      (by simp [s₁, hre_len, u.2])
  -- 3. r_yu := a_Y[r_u] (cost 3)
  have hY₂ : IsBitSet Y a_Y s₂ :=
    hY.of_arr_eq (by simp [s₂, s₁, show (a_Y : Arr) ≠ a_rend from hne_Y_re,
      show (a_Y : Arr) ≠ a_rstart from hne_Y_rs])
  rcases hY₂ with ⟨hY_len₂, hY_le₂, hY_mem₂⟩
  have hu_Y_len : u.1 < (s₂.arrs a_Y).length := by rw [hY_len₂]; exact u.2
  let yu_val := (s₂.arrs a_Y)[u.1]'hu_Y_len
  have hyu_le : yu_val ≤ 1 := hY_le₂ u
  have hyu_w : yu_val < 2 ^ w := by omega
  have hru₂ : s₂.regs r_u = u.1 := by simp [s₂, s₁, hru]
  let s₃ := s₂.setReg r_yu yu_val
  have hex₃ : Exec w (.assign r_yu (.read a_Y (.reg r_u))) s₂ s₃ 3 :=
    .assign (by simp [Expr.eval, checkWord, hru₂, hu_w, hu_Y_len, yu_val, hyu_w])
  -- 4. Prepare forList over lists u
  have hadj₃ : IsAdjList G a_start a_end a_entries lists s₃ :=
    hadj.of_arrs_eq
      (by simp [s₃, s₂, s₁, show (a_start : Arr) ≠ a_rend from hne_st_re,
        show (a_start : Arr) ≠ a_rstart from hne_st_rs])
      (by simp [s₃, s₂, s₁, show (a_end : Arr) ≠ a_rend from hne_en_re,
        show (a_end : Arr) ≠ a_rstart from hne_en_rs])
      (by simp [s₃, s₂, s₁, show (a_entries : Arr) ≠ a_rend from hne_ent_re,
        show (a_entries : Arr) ≠ a_rstart from hne_ent_rs])
  obtain ⟨st_g, en_g, hlist_g⟩ := hadj₃.1.2.2 u
  have hen_g_w : en_g < 2 ^ w := by
    rcases hlist_g with ⟨_, _, hen_ent, _, _, _, _, _⟩
    have hent₃ : (s₃.arrs a_entries).length < 2 ^ w := by
      simpa [s₃, s₂, s₁, show (a_entries : Arr) ≠ a_rend from hne_ent_re,
        show (a_entries : Arr) ≠ a_rstart from hne_ent_rs] using hent_w
    omega
  have hwords_g : ∀ x ∈ lists u, x < 2 ^ w := by
    intro x hx
    have := (hadj.2 u).1 x hx
    omega
  let Inv (j : ℕ) (st_j : State) : Prop :=
    IsListAt a_start a_end a_entries u.1 st_g en_g (lists u) st_j ∧
    IsBitSet Y a_Y st_j ∧
    st_j.regs r_u = u.1 ∧
    st_j.regs r_yu = yu_val ∧
    st_j.regs r_cnt = st_u + (restrictListUpTo Y u (lists u) j).length ∧
    (st_j.arrs a_rstart).length = n ∧
    (st_j.arrs a_rend).length = n ∧
    (st_j.arrs a_rentries).length = cap ∧
    IsListAt a_rstart a_rend a_rentries u.1 st_u
      (st_u + (restrictListUpTo Y u (lists u) j).length) (restrictListUpTo Y u (lists u) j) st_j ∧
    (∀ u' : Fin n, u'.1 < u.1 →
      IsListAt a_rstart a_rend a_rentries u'.1 (prefixRestrictedLen Y lists u'.1)
        (prefixRestrictedLen Y lists u'.1 + (restrictListFamily Y lists u').length)
        (restrictListFamily Y lists u') st_j) ∧
    (∀ a : Arr, a ≠ a_rstart → a ≠ a_rend → a ≠ a_rentries → st_j.arrs a = s.arrs a) ∧
    (∀ r : Reg, r ≠ r_yu → r ≠ r_cnt → r ≠ r_k → r ≠ r_hi → r ≠ r_w → r ≠ r_yw →
      st_j.regs r = s.regs r)
  have hspec :
      ⦃Inv 0⦄[w]
        forList a_start a_end a_entries r_u r_k r_hi r_w
          (restrictNeighborBody a_Y a_rend a_rentries r_u r_yu r_cnt r_w r_yw)
      ⦃Inv (lists u).length⦄ ≤
        fun _ => 9 + (lists u).length * (10 + 15) := by
    apply Triple.forList_const a_start a_end a_entries r_u r_k r_hi r_w
      u.1 st_g en_g (lists u) Inv 15 _ hne_kh hne_uk hw hu_w hen_g_w hwords_g
    · intro st₀ ⟨hlist₀, hY₀, hru₀, hryu₀, hrcnt₀, hrs₀, hre₀, hrent₀, hcur₀, hprev₀, harr₀, hreg₀⟩
      refine ⟨hlist₀, hru₀, hlist₀, hY₀,
        by simp [State.setReg, show (r_u : Reg) ≠ r_hi by omega,
          show (r_u : Reg) ≠ r_k by omega, hru₀],
        by simp [State.setReg, show (r_yu : Reg) ≠ r_hi by omega,
          show (r_yu : Reg) ≠ r_k by omega, hryu₀],
        by simp [State.setReg, show (r_cnt : Reg) ≠ r_hi by omega,
          show (r_cnt : Reg) ≠ r_k by omega, hrcnt₀],
        hrs₀, hre₀, hrent₀, hcur₀, hprev₀, harr₀, ?_⟩
      intro r h1 h2 h3 h4 h5 h6
      simp [State.setReg, h3, h4, hreg₀ r h1 h2 h3 h4 h5 h6]
    · intro j _ st_j ⟨hlist_j, _⟩
      exact hlist_j
    · intro j hj st_w ⟨st_j, ⟨hlist_j, hY_j, hru_j, hryu_j, hrcnt_j, hrs_j, hre_j, hrent_j,
        hcur_j, hprev_j, harr_j, hreg_j⟩, hst_w, hrk_j, hrhi_j⟩
      subst hst_w
      let w_val := (lists u)[j]
      have hw_lt : w_val < n := (hadj.2 u).1 w_val (List.getElem_mem hj)
      have hw_w : w_val < 2 ^ w := by omega
      let wFin : Fin n := ⟨w_val, hw_lt⟩
      have hcond_yu : (Expr.reg r_yu).eval w (st_j.setReg r_w w_val) = some yu_val := by
        simp [State.setReg, show (r_yu : Reg) ≠ r_w by omega, Expr.eval, checkWord, hryu_j, hyu_w]
      have hlen_j_lt : (restrictListUpTo Y u (lists u) j).length ≤ (restrictListFamily Y lists u).length :=
        restrictListUpTo_length_mono Y u (lists u) (by omega)
      by_cases huY : u ∈ Y
      · have hyu_ne : yu_val ≠ 0 := (hY_mem₂ u).mpr huY
        rcases hY_j with ⟨hY_len_j, hY_le_j, hY_mem_j⟩
        have hw_Y_len : w_val < (st_j.arrs a_Y).length := by rw [hY_len_j]; exact hw_lt
        let yw_val := (st_j.arrs a_Y)[w_val]'hw_Y_len
        have hyw_le : yw_val ≤ 1 := hY_le_j wFin
        have hyw_w : yw_val < 2 ^ w := by omega
        let sb₁ := (st_j.setReg r_w w_val).setReg r_yw yw_val
        have hexb₁ : Exec w (.assign r_yw (.read a_Y (.reg r_w))) (st_j.setReg r_w w_val) sb₁ 3 :=
          .assign (by simp [Expr.eval, checkWord, hw_w, hw_Y_len, yw_val, hyw_w])
        have hcond_yw : (Expr.reg r_yw).eval w sb₁ = some yw_val := by
          simp [sb₁, Expr.eval, checkWord, hyw_w]
        by_cases hwY : wFin ∈ Y
        · have hyw_ne : yw_val ≠ 0 := (hY_mem_j wFin).mpr hwY
          -- When both u ∈ Y and wFin ∈ Y, restrictListUpTo (j + 1) = restrictListUpTo j ++ [w_val]
          have hstep_list :
              restrictListUpTo Y u (lists u) (j + 1) =
                restrictListUpTo Y u (lists u) j ++ [w_val] := by
            have hwY' : (⟨(lists u)[j], hw_lt⟩ : Fin n) ∈ Y := hwY
            have hw_lt' : (lists u)[j] < n := hw_lt
            simp [restrictListUpTo, hj, hw_lt', huY, hwY', w_val]
          have hlen_succ : (restrictListUpTo Y u (lists u) j).length + 1 ≤
              (restrictListFamily Y lists u).length := by
            have hle := restrictListUpTo_length_mono Y u (lists u) (show j + 1 ≤ (lists u).length by omega)
            rw [hstep_list, List.length_append, List.length_singleton] at hle
            exact hle
          -- Execute listAppend manually for clean state tracking
          let cnt_j := st_u + (restrictListUpTo Y u (lists u) j).length
          have hcnt_lt_cap : cnt_j < cap := by dsimp [cnt_j, st_u] at *; omega
          have hcnt_succ_w : cnt_j + 1 < 2 ^ w := by omega
          have hcnt_j_w : cnt_j < 2 ^ w := by omega
          have hrcnt_sb₁ : sb₁.regs r_cnt = cnt_j := by
            simp [sb₁, State.setReg, show (r_cnt : Reg) ≠ r_yw by omega,
              show (r_cnt : Reg) ≠ r_w by omega, hrcnt_j, cnt_j]
          let sb₂ := sb₁.writeArr a_rentries cnt_j w_val
          have hex_la₁ : Exec w (.write a_rentries (.reg r_cnt) (.reg r_w)) sb₁ sb₂ 3 :=
            .write (by simp [Expr.eval, checkWord, hrcnt_sb₁, hcnt_j_w])
              (by simp [sb₁, State.setReg, show (r_w : Reg) ≠ r_yw by omega,
                Expr.eval, checkWord, hw_w])
              (by simp [sb₁, hrent_j, hcnt_lt_cap])
          let sb₃ := sb₂.setReg r_cnt (cnt_j + 1)
          have hex_la₂ : Exec w (.assign r_cnt (.op .add (.reg r_cnt) (.const 1))) sb₂ sb₃ 4 :=
            .assign (by simp [sb₂, Expr.eval, BinOp.eval, BinOp.raw, checkWord, hrcnt_sb₁,
              hcnt_j_w, hw, hcnt_succ_w])
          have hru_sb₃ : sb₃.regs r_u = u.1 := by
            simp [sb₃, sb₂, sb₁, State.setReg, show (r_u : Reg) ≠ r_cnt by omega,
              show (r_u : Reg) ≠ r_yw by omega, show (r_u : Reg) ≠ r_w by omega, hru_j]
          let sb₄ := sb₃.writeArr a_rend u.1 (cnt_j + 1)
          have hex_la₃ : Exec w (.write a_rend (.reg r_u) (.reg r_cnt)) sb₃ sb₄ 3 :=
            .write (by simp [Expr.eval, checkWord, hru_sb₃, hu_w])
              (by simp [sb₃, Expr.eval, checkWord, hcnt_succ_w])
              (by simp [sb₃, sb₂, sb₁, show (a_rend : Arr) ≠ a_rentries from hne_re_rent, hre_j, u.2])
          have hex_la : Exec w (listAppend a_rend a_rentries r_u r_cnt (.reg r_w)) sb₁ sb₄ (3 + (4 + 3)) :=
            .seq hex_la₁ (.seq hex_la₂ hex_la₃)
          have hex_in : Exec w
              (.ite (.reg r_yw) (listAppend a_rend a_rentries r_u r_cnt (.reg r_w)) .skip)
              sb₁ sb₄ (1 + (3 + (4 + 3))) :=
            .ite_true hcond_yw hyw_ne hex_la
          have hex_out : Exec w (restrictNeighborBody a_Y a_rend a_rentries r_u r_yu r_cnt r_w r_yw)
              (st_j.setReg r_w w_val) sb₄ (1 + (3 + (1 + (3 + (4 + 3))))) :=
            .ite_true hcond_yu hyu_ne (.seq hexb₁ hex_in)
          refine ⟨sb₄, 1 + (3 + (1 + (3 + (4 + 3)))), hex_out, by dsimp only; omega, ?_,
            by simp [sb₄, sb₃, sb₂, sb₁, State.setReg, show (r_k : Reg) ≠ r_cnt by omega,
              show (r_k : Reg) ≠ r_yw by omega, show (r_k : Reg) ≠ r_w by omega, hrk_j],
            by simp [sb₄, sb₃, sb₂, sb₁, State.setReg, show (r_hi : Reg) ≠ r_cnt by omega,
              show (r_hi : Reg) ≠ r_yw by omega, show (r_hi : Reg) ≠ r_w by omega, hrhi_j]⟩
          -- Prove Inv (j + 1) (sb₄.setReg r_k (st_g + (j + 1)))
          have hne_st_re' : (a_start : Arr) ≠ a_rend := hne_st_re
          have hne_st_rent' : (a_start : Arr) ≠ a_rentries := hne_st_rent
          have hne_en_re' : (a_end : Arr) ≠ a_rend := hne_en_re
          have hne_en_rent' : (a_end : Arr) ≠ a_rentries := hne_en_rent
          have hne_ent_re' : (a_entries : Arr) ≠ a_rend := hne_ent_re
          have hne_ent_rent' : (a_entries : Arr) ≠ a_rentries := hne_ent_rent
          have hne_Y_re' : (a_Y : Arr) ≠ a_rend := hne_Y_re
          have hne_Y_rent' : (a_Y : Arr) ≠ a_rentries := hne_Y_rent
          have hne_rs_re' : (a_rstart : Arr) ≠ a_rend := hne_rs_re
          have hne_rs_rent' : (a_rstart : Arr) ≠ a_rentries := hne_rs_rent
          have hne_re_rent' : (a_rend : Arr) ≠ a_rentries := hne_re_rent
          refine ⟨hlist_j.of_arrs_eq
              (by simp [sb₄, sb₃, sb₂, sb₁, hne_st_re', hne_st_rent'])
              (by simp [sb₄, sb₃, sb₂, sb₁, hne_en_re', hne_en_rent'])
              (by simp [sb₄, sb₃, sb₂, sb₁, hne_ent_re', hne_ent_rent']),
            IsBitSet.of_arr_eq ⟨hY_len_j, hY_le_j, hY_mem_j⟩
              (by simp [sb₄, sb₃, sb₂, sb₁, hne_Y_re', hne_Y_rent']),
            by simp [sb₄, sb₃, sb₂, sb₁, State.setReg, show (r_u : Reg) ≠ r_k by omega,
              show (r_u : Reg) ≠ r_cnt by omega, show (r_u : Reg) ≠ r_yw by omega,
              show (r_u : Reg) ≠ r_w by omega, hru_j],
            by simp [sb₄, sb₃, sb₂, sb₁, State.setReg, show (r_yu : Reg) ≠ r_k by omega,
              show (r_yu : Reg) ≠ r_cnt by omega, show (r_yu : Reg) ≠ r_yw by omega,
              show (r_yu : Reg) ≠ r_w by omega, hryu_j],
            by simp [sb₄, sb₃, State.setReg, show (r_cnt : Reg) ≠ r_k by omega,
              hstep_list, cnt_j, Nat.add_assoc],
            by simp [sb₄, sb₃, sb₂, sb₁, hne_rs_re', hne_rs_rent', hrs_j],
            by simp [sb₄, sb₃, sb₂, sb₁, hne_re_rent', hre_j],
            by simp [sb₄, sb₃, sb₂, sb₁, hne_re_rent'.symm, hrent_j],
            ?_, ?_,
            fun a ha1 ha2 ha3 => by simp [sb₄, sb₃, sb₂, sb₁, ha2, ha3, harr_j a ha1 ha2 ha3],
            ?_⟩
          · rw [hstep_list]
            rcases hcur_j with ⟨hu_st, hu_en, _, _, hst_c, _, _, helem_c⟩
            have hlen_app : st_u + (restrictListUpTo Y u (lists u) j ++ [w_val]).length = cnt_j + 1 := by
              simp [cnt_j]; omega
            rw [hlen_app]
            refine ⟨by simpa [sb₄, sb₃, sb₂, sb₁, hne_rs_re', hne_rs_rent'] using hu_st,
              by simpa [sb₄, sb₃, sb₂, sb₁, hne_re_rent'] using hu_en,
              by simp [sb₄, sb₃, sb₂, sb₁, hne_re_rent'.symm, hrent_j]; omega,
              by simp [cnt_j]; omega,
              by simpa [sb₄, sb₃, sb₂, sb₁, hne_rs_re', hne_rs_rent'] using hst_c,
              ?_, by omega, ?_⟩
            · simp only [sb₄, sb₃, sb₂, sb₁, State.setReg_arrs, State.writeArr_arrs_self,
                State.writeArr_arrs_ne _ _ _ hne_re_rent']
              exact List.getElem_set_self (by rw [List.length_set]; exact hu_en)
            · intro k hk
              simp only [List.length_append, List.length_singleton] at hk
              simp only [sb₄, sb₃, sb₂, sb₁, State.setReg_arrs,
                State.writeArr_arrs_ne _ _ _ hne_re_rent'.symm, State.writeArr_arrs_self]
              by_cases hkeq : k = (restrictListUpTo Y u (lists u) j).length
              · subst hkeq
                rw [List.getElem_set_self (by rw [List.length_set, hrent_j]; exact hcnt_lt_cap)]
                simp
              · have hklt : k < (restrictListUpTo Y u (lists u) j).length := by omega
                rw [List.getElem_set_ne (by dsimp [cnt_j]; omega), List.getElem_append_left hklt]
                exact helem_c k hklt
          · intro u' hu'
            have hbound_u' :
                prefixRestrictedLen Y lists u'.1 + (restrictListFamily Y lists u').length ≤ cnt_j := by
              have h1 := prefixRestrictedLen_succ Y lists u'
              have h2 := prefixRestrictedLen_mono Y lists (show u'.1 + 1 ≤ u.1 by omega)
              dsimp [cnt_j, st_u]
              omega
            have hprev_u' := hprev_j u' hu'
            exact (isListAt_preserve_prev_restrict hne_rs_re hne_rs_rent hne_re_rent
              (by omega) hbound_u' hprev_u').of_arrs_eq rfl rfl rfl
          · intro r h1 h2 h3 h4 h5 h6
            simp [sb₄, sb₃, sb₂, sb₁, State.setReg, h2, h3, h5, h6, hreg_j r h1 h2 h3 h4 h5 h6]
        · have hyw_eq0 : yw_val = 0 := not_ne_iff.mp ((hY_mem_j wFin).not.mpr hwY)
          have hcond_yw0 : (Expr.reg r_yw).eval w sb₁ = some 0 := by simpa [hyw_eq0] using hcond_yw
          have hstep_list :
              restrictListUpTo Y u (lists u) (j + 1) =
                restrictListUpTo Y u (lists u) j := by
            have hwY' : (⟨(lists u)[j], hw_lt⟩ : Fin n) ∉ Y := hwY
            have hw_lt' : (lists u)[j] < n := hw_lt
            simp [restrictListUpTo, hj, hw_lt', huY, hwY']
          have hex_in : Exec w
              (.ite (.reg r_yw) (listAppend a_rend a_rentries r_u r_cnt (.reg r_w)) .skip)
              sb₁ sb₁ (1 + 1) :=
            .ite_false hcond_yw0 (.skip sb₁)
          have hex_out : Exec w (restrictNeighborBody a_Y a_rend a_rentries r_u r_yu r_cnt r_w r_yw)
              (st_j.setReg r_w w_val) sb₁ (1 + (3 + (1 + 1))) :=
            .ite_true hcond_yu hyu_ne (.seq hexb₁ hex_in)
          refine ⟨sb₁, 1 + (3 + (1 + 1)), hex_out, by dsimp only; omega, ?_,
            by simp [sb₁, State.setReg, show (r_k : Reg) ≠ r_yw by omega,
              show (r_k : Reg) ≠ r_w by omega, hrk_j],
            by simp [sb₁, State.setReg, show (r_hi : Reg) ≠ r_yw by omega,
              show (r_hi : Reg) ≠ r_w by omega, hrhi_j]⟩
          dsimp only [Inv]
          rw [hstep_list]
          refine ⟨hlist_j, ⟨hY_len_j, hY_le_j, hY_mem_j⟩,
            by simp [sb₁, State.setReg, show (r_u : Reg) ≠ r_k by omega,
              show (r_u : Reg) ≠ r_yw by omega, show (r_u : Reg) ≠ r_w by omega, hru_j],
            by simp [sb₁, State.setReg, show (r_yu : Reg) ≠ r_k by omega,
              show (r_yu : Reg) ≠ r_yw by omega, show (r_yu : Reg) ≠ r_w by omega, hryu_j],
            by simp [sb₁, State.setReg, show (r_cnt : Reg) ≠ r_k by omega,
              show (r_cnt : Reg) ≠ r_yw by omega, show (r_cnt : Reg) ≠ r_w by omega, hrcnt_j],
            hrs_j, hre_j, hrent_j, hcur_j, hprev_j, harr_j, ?_⟩
          intro r h1 h2 h3 h4 h5 h6
          simp [sb₁, State.setReg, h3, h5, h6, hreg_j r h1 h2 h3 h4 h5 h6]
      · have hyu_eq0 : yu_val = 0 := not_ne_iff.mp ((hY_mem₂ u).not.mpr huY)
        have hcond_yu0 : (Expr.reg r_yu).eval w (st_j.setReg r_w w_val) = some 0 := by
          simpa [hyu_eq0] using hcond_yu
        have hstep_list :
            restrictListUpTo Y u (lists u) (j + 1) =
              restrictListUpTo Y u (lists u) j := by
          have hw_lt' : (lists u)[j] < n := hw_lt
          simp [restrictListUpTo, hj, hw_lt', huY]
        have hex_out : Exec w (restrictNeighborBody a_Y a_rend a_rentries r_u r_yu r_cnt r_w r_yw)
            (st_j.setReg r_w w_val) (st_j.setReg r_w w_val) (1 + 1) :=
          .ite_false hcond_yu0 (.skip _)
        refine ⟨st_j.setReg r_w w_val, 1 + 1, hex_out, by dsimp only; omega, ?_,
          by simp [State.setReg, show (r_k : Reg) ≠ r_w by omega, hrk_j],
          by simp [State.setReg, show (r_hi : Reg) ≠ r_w by omega, hrhi_j]⟩
        dsimp only [Inv]
        rw [hstep_list]
        refine ⟨hlist_j, hY_j,
          by simp [State.setReg, show (r_u : Reg) ≠ r_k by omega,
            show (r_u : Reg) ≠ r_w by omega, hru_j],
          by simp [State.setReg, show (r_yu : Reg) ≠ r_k by omega,
            show (r_yu : Reg) ≠ r_w by omega, hryu_j],
          by simp [State.setReg, show (r_cnt : Reg) ≠ r_k by omega,
            show (r_cnt : Reg) ≠ r_w by omega, hrcnt_j],
          hrs_j, hre_j, hrent_j, hcur_j, hprev_j, harr_j, ?_⟩
        intro r h1 h2 h3 h4 h5 h6
        simp [State.setReg, h3, h5, hreg_j r h1 h2 h3 h4 h5 h6]
  have hinit : Inv 0 s₃ := by
    have hne_rs_re' : (a_rstart : Arr) ≠ a_rend := hne_rs_re
    have hne_rs_rent' : (a_rstart : Arr) ≠ a_rentries := hne_rs_rent
    have hne_re_rent' : (a_rend : Arr) ≠ a_rentries := hne_re_rent
    refine ⟨hlist_g, ⟨hY_len₂, hY_le₂, hY_mem₂⟩,
      by simp [s₃, s₂, s₁, State.setReg, show (r_u : Reg) ≠ r_yu by omega, hru],
      by simp [s₃],
      by simp [s₃, s₂, s₁, State.setReg, show (r_cnt : Reg) ≠ r_yu by omega,
        hrcnt, restrictListUpTo, st_u],
      by simp [s₃, s₂, s₁, hne_rs_re', hrs_len],
      by simp [s₃, s₂, s₁, hre_len],
      by simp [s₃, s₂, s₁, hne_re_rent'.symm, hne_rs_rent'.symm, hrent_len],
      ?_, ?_,
      fun a ha1 ha2 ha3 => by simp [s₃, s₂, s₁, ha1, ha2],
      fun r h1 _ _ _ _ _ => by simp [s₃, s₂, s₁, State.setReg, h1]⟩
    · simp only [restrictListUpTo, List.length_nil, Nat.add_zero]
      refine ⟨by simp [s₃, s₂, s₁, hne_rs_re', hrs_len, u.2],
        by simp [s₃, s₂, s₁, hre_len, u.2],
        by simp [s₃, s₂, s₁, hne_re_rent'.symm, hne_rs_rent'.symm, hrent_len]; dsimp [st_u] at hst_u_end_le; omega,
        by simp,
        ?_, ?_, le_rfl, fun k hk => by simp at hk⟩
      · simp only [s₃, s₂, s₁, State.setReg_arrs, State.writeArr_arrs_ne _ _ _ hne_rs_re',
          State.writeArr_arrs_self]
        exact List.getElem_set_self (by rw [List.length_set, hrs_len]; exact u.2)
      · simp only [s₃, s₂, s₁, State.setReg_arrs, State.writeArr_arrs_self]
        exact List.getElem_set_self (by rw [List.length_set, State.writeArr_arrs_length, hre_len]; exact u.2)
    · intro u' hu'
      rcases hprev u' hu' with ⟨hu'_st, hu'_en, hen_ent, hdiff, hst_u', hen_u', hle_u', helem_u'⟩
      have hne_u' : u.1 ≠ u'.1 := by omega
      refine ⟨by simpa [s₃, s₂, s₁, hne_rs_re'] using hu'_st,
        by simpa [s₃, s₂, s₁] using hu'_en,
        by simpa [s₃, s₂, s₁, hne_re_rent'.symm, hne_rs_rent'.symm] using hen_ent,
        hdiff, ?_, ?_, hle_u', ?_⟩
      · simp only [s₃, s₂, s₁, State.setReg_arrs, State.writeArr_arrs_ne _ _ _ hne_rs_re',
          State.writeArr_arrs_self]
        rw [List.getElem_set_ne hne_u']
        exact hst_u'
      · simp only [s₃, s₂, s₁, State.setReg_arrs, State.writeArr_arrs_self,
          State.writeArr_arrs_ne _ _ _ hne_rs_re'.symm]
        rw [List.getElem_set_ne hne_u']
        exact hen_u'
      · intro k hk
        simpa [s₃, s₂, s₁, hne_re_rent'.symm, hne_rs_rent'.symm] using helem_u' k hk
  rcases hspec s₃ hinit with ⟨s₄, t₄, hex₄, ht₄, _, _, hru₄, _, hrcnt₄, hrs₄, hre₄, hrent₄,
    hcur₄, hprev₄, harr₄, hreg₄⟩
  dsimp only at ht₄
  have hcur₄_full :
      IsListAt a_rstart a_rend a_rentries u.1 st_u
        (st_u + (restrictListFamily Y lists u).length) (restrictListFamily Y lists u) s₄ :=
    hcur₄
  have hrcnt₄_full : s₄.regs r_cnt = prefixRestrictedLen Y lists (u.1 + 1) := by
    rw [prefixRestrictedLen_succ Y lists u]
    exact hrcnt₄
  refine ⟨s₄, 3 + (3 + (3 + t₄)), .seq hex₁ (.seq hex₂ (.seq hex₃ hex₄)), by omega,
    hru₄, hrcnt₄_full, hrs₄, hre₄, hrent₄,
    fun u' hu' => by
      by_cases hu'_eq : u'.1 = u.1
      · have hfin : u' = u := Fin.ext hu'_eq
        subst hfin
        exact hcur₄_full
      · exact hprev₄ u' (by omega),
    harr₄, hreg₄⟩

theorem restrictGraphLoop_exec {w n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (lists : Fin n → List ℕ) (Y : Finset (Fin n)) (cap : ℕ)
    (a_start a_end a_entries a_Y a_rstart a_rend a_rentries : ℕ)
    (r_n r_u r_yu r_cnt r_k r_hi r_w r_yw : ℕ)
    (hne_st_rs : a_start ≠ a_rstart) (hne_st_re : a_start ≠ a_rend) (hne_st_rent : a_start ≠ a_rentries)
    (hne_en_rs : a_end ≠ a_rstart) (hne_en_re : a_end ≠ a_rend) (hne_en_rent : a_end ≠ a_rentries)
    (hne_ent_rs : a_entries ≠ a_rstart) (hne_ent_re : a_entries ≠ a_rend) (hne_ent_rent : a_entries ≠ a_rentries)
    (hne_Y_rs : a_Y ≠ a_rstart) (hne_Y_re : a_Y ≠ a_rend) (hne_Y_rent : a_Y ≠ a_rentries)
    (hne_rs_re : a_rstart ≠ a_rend) (hne_rs_rent : a_rstart ≠ a_rentries) (hne_re_rent : a_rend ≠ a_rentries)
    (hne_un : r_u ≠ r_n) (hne_yun : r_yu ≠ r_n) (hne_cntn : r_cnt ≠ r_n)
    (hne_kn : r_k ≠ r_n) (hne_hn : r_hi ≠ r_n) (hne_wn : r_w ≠ r_n) (hne_ywn : r_yw ≠ r_n)
    (hne_kh : r_k ≠ r_hi) (hne_uk : r_u ≠ r_k) (hne_uh : r_u ≠ r_hi)
    (hne_uyu : r_u ≠ r_yu) (hne_ucnt : r_u ≠ r_cnt) (hne_uw : r_u ≠ r_w) (hne_uyw : r_u ≠ r_yw)
    (hne_yuk : r_yu ≠ r_k) (hne_yuh : r_yu ≠ r_hi) (hne_yucnt : r_yu ≠ r_cnt)
    (hne_yuw : r_yu ≠ r_w) (hne_yuyw : r_yu ≠ r_yw)
    (hne_cntk : r_cnt ≠ r_k) (hne_cnth : r_cnt ≠ r_hi) (hne_cntw : r_cnt ≠ r_w) (hne_cntyw : r_cnt ≠ r_yw)
    (hne_kw : r_k ≠ r_w) (hne_kyw : r_k ≠ r_yw) (hne_hw : r_hi ≠ r_w) (hne_hyw : r_hi ≠ r_yw)
    (hne_wyw : r_w ≠ r_yw)
    (hw : 1 < 2 ^ w) (hn_w : n < 2 ^ w) (hcap_w : cap < 2 ^ w)
    (hcap_bound : totalAdjEntries (restrictListFamily Y lists) ≤ cap)
    (rem k : ℕ) (hrem : k + rem = n) {s : State}
    (hadj : IsAdjList G a_start a_end a_entries lists s)
    (hent_w : (s.arrs a_entries).length < 2 ^ w)
    (hY : IsBitSet Y a_Y s)
    (hrs_len : (s.arrs a_rstart).length = n)
    (hre_len : (s.arrs a_rend).length = n)
    (hrent_len : (s.arrs a_rentries).length = cap)
    (hrn : s.regs r_n = n)
    (hru : s.regs r_u = k)
    (hrcnt : s.regs r_cnt = prefixRestrictedLen Y lists k)
    (hprev : ∀ u' : Fin n, u'.1 < k →
      IsListAt a_rstart a_rend a_rentries u'.1 (prefixRestrictedLen Y lists u'.1)
        (prefixRestrictedLen Y lists u'.1 + (restrictListFamily Y lists u').length)
        (restrictListFamily Y lists u') s) :
    ∃ s' t,
      Exec w (forUp r_u (.reg r_n)
        (restrictVertexCmd a_start a_end a_entries a_Y a_rstart a_rend a_rentries
          r_u r_yu r_cnt r_k r_hi r_w r_yw)) s s' t ∧
      t ≤ 3 + (∑ u ∈ Finset.univ.filter (fun u : Fin n => k ≤ u.1), (25 + 25 * (lists u).length)) ∧
      IsAdjList (restrictGraph G Y) a_rstart a_rend a_rentries (restrictListFamily Y lists) s' ∧
      (s'.arrs a_rentries).length = cap ∧
      s'.regs r_cnt = totalAdjEntries (restrictListFamily Y lists) ∧
      (∀ a : Arr, a ≠ a_rstart → a ≠ a_rend → a ≠ a_rentries → s'.arrs a = s.arrs a) ∧
      (∀ r : Reg, r ≠ r_u → r ≠ r_yu → r ≠ r_cnt → r ≠ r_k → r ≠ r_hi → r ≠ r_w → r ≠ r_yw →
        s'.regs r = s.regs r) := by
  have h0_w : 0 < 2 ^ w := by omega
  induction rem generalizing k s with
  | zero =>
    have hk_eq : k = n := by omega
    rw [hk_eq] at hru hrcnt hprev
    have hcond : (Expr.op .lt (.reg r_u) (.reg r_n)).eval w s = some 0 := by
      simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hru, hrn, hn_w, h0_w]
    refine ⟨s, 3, .while_false hcond, by omega,
      ⟨⟨hrs_len, hre_len, fun u => ⟨_, _, hprev u u.2⟩⟩,
        isAdjListFamily_restrictListFamily hadj.2 Y⟩,
      hrent_len,
      by rw [hrcnt, prefixRestrictedLen_full],
      fun _ _ _ _ => rfl,
      fun _ _ _ _ _ _ _ _ => rfl⟩
  | succ rem ih =>
    have hk_lt : k < n := by omega
    have hk_w : k < 2 ^ w := by omega
    let uFin : Fin n := ⟨k, hk_lt⟩
    have hcond : (Expr.op .lt (.reg r_u) (.reg r_n)).eval w s = some 1 := by
      simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hru, hrn, hk_w, hn_w, hk_lt, hw]
    rcases restrictVertexCmd_exec G lists Y uFin cap
        a_start a_end a_entries a_Y a_rstart a_rend a_rentries
        r_u r_yu r_cnt r_k r_hi r_w r_yw
        hne_st_rs hne_st_re hne_st_rent
        hne_en_rs hne_en_re hne_en_rent
        hne_ent_rs hne_ent_re hne_ent_rent
        hne_Y_rs hne_Y_re hne_Y_rent
        hne_rs_re hne_rs_rent hne_re_rent
        hne_kh hne_uk hne_uh hne_uyu hne_ucnt hne_uw hne_uyw
        hne_yuk hne_yuh hne_yucnt hne_yuw hne_yuyw
        hne_cntk hne_cnth hne_cntw hne_cntyw
        hne_kw hne_kyw hne_hw hne_hyw hne_wyw
        hw hn_w hcap_w hcap_bound
        hadj hent_w hY hrs_len hre_len hrent_len hru hrcnt hprev with
      ⟨s₁, t₁, hex₁, ht₁, hru₁, hrcnt₁, hrs₁, hre₁, hrent₁, hprev₁, harr₁, hreg₁⟩
    let s₂ := s₁.setReg r_u (k + 1)
    have hex_inc : Exec w (.assign r_u (.op .add (.reg r_u) (.const 1))) s₁ s₂ 4 :=
      .assign (by
        simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hru₁, uFin, hk_w, hw,
          show k + 1 < 2 ^ w by omega])
    have harr₂ : ∀ a : Arr, a ≠ a_rstart → a ≠ a_rend → a ≠ a_rentries → s₂.arrs a = s.arrs a := by
      intro a ha1 ha2 ha3
      simp [s₂, harr₁ a ha1 ha2 ha3]
    have hadj₂ : IsAdjList G a_start a_end a_entries lists s₂ :=
      hadj.of_arrs_eq
        (harr₂ _ hne_st_rs hne_st_re hne_st_rent)
        (harr₂ _ hne_en_rs hne_en_re hne_en_rent)
        (harr₂ _ hne_ent_rs hne_ent_re hne_ent_rent)
    have hent₂ : (s₂.arrs a_entries).length < 2 ^ w := by
      rw [harr₂ _ hne_ent_rs hne_ent_re hne_ent_rent]; exact hent_w
    have hY₂ : IsBitSet Y a_Y s₂ :=
      hY.of_arr_eq (harr₂ _ hne_Y_rs hne_Y_re hne_Y_rent)
    have hrn₂ : s₂.regs r_n = n := by
      simp [s₂, State.setReg, show (r_n : Reg) ≠ r_u from hne_un.symm,
        hreg₁ r_n hne_yun.symm hne_cntn.symm hne_kn.symm hne_hn.symm hne_wn.symm hne_ywn.symm, hrn]
    have hrcnt₂ : s₂.regs r_cnt = prefixRestrictedLen Y lists (k + 1) := by
      simp [s₂, State.setReg, show (r_cnt : Reg) ≠ r_u from hne_ucnt.symm, hrcnt₁, uFin]
    rcases ih (k + 1) (by omega) (s := s₂) hadj₂ hent₂ hY₂ hrs₁ hre₁ hrent₁ hrn₂ (by simp [s₂])
        hrcnt₂ (fun u' hu' => (hprev₁ u' hu').of_arrs_eq rfl rfl rfl) with
      ⟨s₃, t₃, hex₃, ht₃, hadj_r₃, hrent₃, hrcnt₃, harr₃, hreg₃⟩
    have hsum_split :
        (25 + 25 * (lists uFin).length) +
          (∑ u ∈ Finset.univ.filter (fun u : Fin n => k + 1 ≤ u.1), (25 + 25 * (lists u).length)) =
          ∑ u ∈ Finset.univ.filter (fun u : Fin n => k ≤ u.1), (25 + 25 * (lists u).length) := by
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
    refine ⟨s₃, 3 + (t₁ + 4) + t₃, .while_true hcond (by omega) (.seq hex₁ hex_inc) hex₃,
      by omega, hadj_r₃, hrent₃, hrcnt₃,
      fun a ha1 ha2 ha3 => by rw [harr₃ a ha1 ha2 ha3, harr₂ a ha1 ha2 ha3],
      fun r h1 h2 h3 h4 h5 h6 h7 => by
        rw [hreg₃ r h1 h2 h3 h4 h5 h6 h7]
        simp [s₂, State.setReg, h1, hreg₁ r h2 h3 h4 h5 h6 h7]⟩

/-- Specification for `restrictGraphProg`: builds CSR adjacency lists `(a_rstart, a_rend, a_rentries)`
for `restrictGraph G Y` in `O(n + cap + totalAdjEntries lists)` steps and leaves
`2 * (edgesInSet G Y).card` in `r_cnt`. -/
theorem restrictGraphProg_exec {w n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (lists : Fin n → List ℕ) (Y : Finset (Fin n)) (cap : ℕ)
    (a_start a_end a_entries a_Y a_rstart a_rend a_rentries : ℕ)
    (r_n r_cap r_u r_yu r_cnt r_k r_hi r_w r_yw : ℕ)
    (hne_st_rs : a_start ≠ a_rstart) (hne_st_re : a_start ≠ a_rend) (hne_st_rent : a_start ≠ a_rentries)
    (hne_en_rs : a_end ≠ a_rstart) (hne_en_re : a_end ≠ a_rend) (hne_en_rent : a_end ≠ a_rentries)
    (hne_ent_rs : a_entries ≠ a_rstart) (hne_ent_re : a_entries ≠ a_rend) (hne_ent_rent : a_entries ≠ a_rentries)
    (hne_Y_rs : a_Y ≠ a_rstart) (hne_Y_re : a_Y ≠ a_rend) (hne_Y_rent : a_Y ≠ a_rentries)
    (hne_rs_re : a_rstart ≠ a_rend) (hne_rs_rent : a_rstart ≠ a_rentries) (hne_re_rent : a_rend ≠ a_rentries)
    (hne_un : r_u ≠ r_n) (hne_yun : r_yu ≠ r_n) (hne_cntn : r_cnt ≠ r_n)
    (hne_kn : r_k ≠ r_n) (hne_hn : r_hi ≠ r_n) (hne_wn : r_w ≠ r_n) (hne_ywn : r_yw ≠ r_n)
    (hne_kh : r_k ≠ r_hi) (hne_uk : r_u ≠ r_k) (hne_uh : r_u ≠ r_hi)
    (hne_uyu : r_u ≠ r_yu) (hne_ucnt : r_u ≠ r_cnt) (hne_uw : r_u ≠ r_w) (hne_uyw : r_u ≠ r_yw)
    (hne_yuk : r_yu ≠ r_k) (hne_yuh : r_yu ≠ r_hi) (hne_yucnt : r_yu ≠ r_cnt)
    (hne_yuw : r_yu ≠ r_w) (hne_yuyw : r_yu ≠ r_yw)
    (hne_cntk : r_cnt ≠ r_k) (hne_cnth : r_cnt ≠ r_hi) (hne_cntw : r_cnt ≠ r_w) (hne_cntyw : r_cnt ≠ r_yw)
    (hne_kw : r_k ≠ r_w) (hne_kyw : r_k ≠ r_yw) (hne_hw : r_hi ≠ r_w) (hne_hyw : r_hi ≠ r_yw)
    (hne_wyw : r_w ≠ r_yw)
    (hw : 1 < 2 ^ w) (hn_w : n < 2 ^ w) (hcap_w : cap < 2 ^ w)
    (hcap_bound : 2 * (edgesInSet G Y).card ≤ cap)
    {s : State}
    (hadj : IsAdjList G a_start a_end a_entries lists s)
    (hent_w : (s.arrs a_entries).length < 2 ^ w)
    (hY : IsBitSet Y a_Y s)
    (hrn : s.regs r_n = n)
    (hrcap : s.regs r_cap = cap) :
    ∃ s' t,
      Exec w (restrictGraphProg a_start a_end a_entries a_Y a_rstart a_rend a_rentries
        r_n r_cap r_u r_yu r_cnt r_k r_hi r_w r_yw) s s' t ∧
      t ≤ 10 + 27 * n + cap + 25 * totalAdjEntries lists ∧
      IsAdjList (restrictGraph G Y) a_rstart a_rend a_rentries (restrictListFamily Y lists) s' ∧
      (s'.arrs a_rentries).length = cap ∧
      s'.regs r_cnt = 2 * (edgesInSet G Y).card ∧
      (∀ a : Arr, a ≠ a_rstart → a ≠ a_rend → a ≠ a_rentries → s'.arrs a = s.arrs a) ∧
      (∀ r : Reg, r ≠ r_u → r ≠ r_yu → r ≠ r_cnt → r ≠ r_k → r ≠ r_hi → r ≠ r_w → r ≠ r_yw →
        s'.regs r = s.regs r) := by
  have h0_w : 0 < 2 ^ w := by omega
  have htot_eq := totalAdjEntries_restrictListFamily hadj.2 Y
  have hcap_bound' : totalAdjEntries (restrictListFamily Y lists) ≤ cap := by omega
  -- 1. alloc a_rstart (.reg r_n)
  let s₁ := s.setArr a_rstart (List.replicate n 0)
  have hex₁ : Exec w (.alloc a_rstart (.reg r_n)) s s₁ (1 + n) :=
    .alloc (by simp [Expr.eval, checkWord, hrn, hn_w])
  -- 2. alloc a_rend (.reg r_n)
  let s₂ := s₁.setArr a_rend (List.replicate n 0)
  have hex₂ : Exec w (.alloc a_rend (.reg r_n)) s₁ s₂ (1 + n) :=
    .alloc (by simp [s₁, Expr.eval, checkWord, hrn, hn_w])
  -- 3. alloc a_rentries (.reg r_cap)
  let s₃ := s₂.setArr a_rentries (List.replicate cap 0)
  have hex₃ : Exec w (.alloc a_rentries (.reg r_cap)) s₂ s₃ (1 + cap) :=
    .alloc (by simp [s₂, s₁, Expr.eval, checkWord, hrcap, hcap_w])
  -- 4. r_cnt := 0
  let s₄ := s₃.setReg r_cnt 0
  have hex₄ : Exec w (.assign r_cnt (.const 0)) s₃ s₄ 2 :=
    .assign (by simp [Expr.eval, checkWord, h0_w])
  -- 5. r_u := 0
  let s₅ := s₄.setReg r_u 0
  have hex₅ : Exec w (.assign r_u (.const 0)) s₄ s₅ 2 :=
    .assign (by simp [Expr.eval, checkWord, h0_w])
  have harr₅ : ∀ a : Arr, a ≠ a_rstart → a ≠ a_rend → a ≠ a_rentries → s₅.arrs a = s.arrs a := by
    intro a ha1 ha2 ha3
    simp [s₅, s₄, s₃, s₂, s₁, State.setArr, ha1, ha2, ha3]
  have hadj₅ : IsAdjList G a_start a_end a_entries lists s₅ :=
    hadj.of_arrs_eq
      (harr₅ _ hne_st_rs hne_st_re hne_st_rent)
      (harr₅ _ hne_en_rs hne_en_re hne_en_rent)
      (harr₅ _ hne_ent_rs hne_ent_re hne_ent_rent)
  have hent₅ : (s₅.arrs a_entries).length < 2 ^ w := by
    rw [harr₅ _ hne_ent_rs hne_ent_re hne_ent_rent]; exact hent_w
  have hY₅ : IsBitSet Y a_Y s₅ :=
    hY.of_arr_eq (harr₅ _ hne_Y_rs hne_Y_re hne_Y_rent)
  have hne_rs_re' : (a_rstart : Arr) ≠ a_rend := hne_rs_re
  have hne_rs_rent' : (a_rstart : Arr) ≠ a_rentries := hne_rs_rent
  have hne_re_rent' : (a_rend : Arr) ≠ a_rentries := hne_re_rent
  have hrs_len₅ : (s₅.arrs a_rstart).length = n := by
    simp [s₅, s₄, s₃, s₂, s₁, State.setArr, hne_rs_re', hne_rs_rent']
  have hre_len₅ : (s₅.arrs a_rend).length = n := by
    simp [s₅, s₄, s₃, s₂, s₁, State.setArr, hne_re_rent']
  have hrent_len₅ : (s₅.arrs a_rentries).length = cap := by
    simp [s₅, s₄, s₃, State.setArr]
  have hrn₅ : s₅.regs r_n = n := by
    simp [s₅, s₄, s₃, s₂, s₁, State.setReg, State.setArr,
      show (r_n : Reg) ≠ r_u from hne_un.symm,
      show (r_n : Reg) ≠ r_cnt from hne_cntn.symm, hrn]
  have hrcnt₅ : s₅.regs r_cnt = prefixRestrictedLen Y lists 0 := by
    simp [s₅, s₄, State.setReg, show (r_cnt : Reg) ≠ r_u from hne_ucnt.symm]
  rcases restrictGraphLoop_exec G lists Y cap
      a_start a_end a_entries a_Y a_rstart a_rend a_rentries
      r_n r_u r_yu r_cnt r_k r_hi r_w r_yw
      hne_st_rs hne_st_re hne_st_rent
      hne_en_rs hne_en_re hne_en_rent
      hne_ent_rs hne_ent_re hne_ent_rent
      hne_Y_rs hne_Y_re hne_Y_rent
      hne_rs_re hne_rs_rent hne_re_rent
      hne_un hne_yun hne_cntn hne_kn hne_hn hne_wn hne_ywn
      hne_kh hne_uk hne_uh hne_uyu hne_ucnt hne_uw hne_uyw
      hne_yuk hne_yuh hne_yucnt hne_yuw hne_yuyw
      hne_cntk hne_cnth hne_cntw hne_cntyw
      hne_kw hne_kyw hne_hw hne_hyw hne_wyw
      hw hn_w hcap_w hcap_bound'
      n 0 (by omega) hadj₅ hent₅ hY₅ hrs_len₅ hre_len₅ hrent_len₅
      hrn₅ (by simp [s₅]) hrcnt₅ (fun _ hu' => by omega) with
    ⟨s₆, t₆, hex₆, ht₆, hadj_r₆, hrent₆, hrcnt₆, harr₆, hreg₆⟩
  have hsum_eq :
      (∑ u ∈ Finset.univ.filter (fun u : Fin n => 0 ≤ u.1), (25 + 25 * (lists u).length)) =
        25 * n + 25 * totalAdjEntries lists := by
    have hfilter : Finset.univ.filter (fun u : Fin n => 0 ≤ u.1) = Finset.univ := by
      ext u; simp
    rw [hfilter, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      smul_eq_mul, ← Finset.mul_sum, Nat.mul_comm n 25]
    rfl
  rw [hsum_eq] at ht₆
  rw [htot_eq] at hrcnt₆
  refine ⟨s₆, (1 + n) + ((1 + n) + ((1 + cap) + (2 + (2 + t₆)))),
    .seq hex₁ (.seq hex₂ (.seq hex₃ (.seq hex₄ (.seq hex₅ hex₆)))),
    by omega, hadj_r₆, hrent₆, hrcnt₆,
    fun a ha1 ha2 ha3 => by rw [harr₆ a ha1 ha2 ha3, harr₅ a ha1 ha2 ha3],
    fun r h1 h2 h3 h4 h5 h6 h7 => by
      rw [hreg₆ r h1 h2 h3 h4 h5 h6 h7]
      simp [s₅, s₄, s₃, s₂, s₁, State.setReg, State.setArr, h1, h3]⟩

end GraphMinor.Compute
