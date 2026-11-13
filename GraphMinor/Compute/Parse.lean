module

public import GraphMinor.Compute.BFS
public import Mathlib.Combinatorics.SimpleGraph.Finite

/-!
# Flat Input Encoding and `O(n + m)` Adjacency-List Builder for Finite Graphs

This file fixes the canonical flat word-RAM input format for a finite simple graph
`G : SimpleGraph (Fin n)` in `inArr` and implements an `O(n + m)` two-pass CSR adjacency-list
builder `parseGraphProg`.

## Input format in `inArr`

A graph `G : SimpleGraph (Fin n)` with `m = G.edgeFinset.card` undirected edges is encoded as a
flat list of natural numbers of length `2 + 2 * m`:
`[n, m, u_0, v_0, u_1, v_1, ..., u_{m-1}, v_{m-1}]`,
where `(u_k, v_k)` (`0 ≤ k < m`) are the `m` undirected edges of `G` in canonical lexicographic
order (`u_k < v_k`). When a problem takes additional input parameters (such as a BFS source vertex
`s₀`, a parameter `k`, or terminal sets `A, B`), those parameters are appended immediately after the
graph prefix at index `2 + 2 * m`.

On an arbitrary list in `inArr` that is not a valid encoding of a graph (for example if the list is
shorter than `2 + 2 * m`, or contains an endpoint `≥ n`, or a word `≥ 2 ^ w`), a program either
fails a bounds/word-size check and has no `Exec` transition or produces an unspecified state; all
correctness theorems (`ComputesInTime`, `ComputesArrInTime`, `ComputesRelInTime`) quantify over
valid problem inputs via `encIn`.
-/

@[expose] public section

namespace GraphMinor.Compute

open scoped BigOperators

/-! ### Valid Edge Lists and Canonical Graph Encoding -/

/-- A list of directed endpoint pairs `edges : List (Fin n × Fin n)` is a valid simple edge list
for `G : SimpleGraph (Fin n)` if it has no self-loops, no duplicate undirected edges, and its pairs
(up to orientation) are exactly the edges of `G`. -/
def IsSimpleEdgeList {n : ℕ} (G : SimpleGraph (Fin n)) (edges : List (Fin n × Fin n)) : Prop :=
  (∀ k (hk : k < edges.length), (edges[k]).1 ≠ (edges[k]).2) ∧
  (∀ i j (hi : i < j) (hj : j < edges.length),
    ¬(((edges[i]).1 = (edges[j]).1 ∧ (edges[i]).2 = (edges[j]).2) ∨
      ((edges[i]).1 = (edges[j]).2 ∧ (edges[i]).2 = (edges[j]).1))) ∧
  (∀ u v : Fin n, G.Adj u v ↔
    ∃ (k : ℕ) (hk : k < edges.length),
      ((edges[k]).1 = u ∧ (edges[k]).2 = v) ∨ ((edges[k]).1 = v ∧ (edges[k]).2 = u))

/-- All ordered pairs `(u, v) : Fin n × Fin n` in row-major order. -/
def allPairs (n : ℕ) : List (Fin n × Fin n) :=
  (List.finRange n).flatMap (fun u => (List.finRange n).map (fun v => (u, v)))

@[simp]
theorem mem_allPairs {n : ℕ} (p : Fin n × Fin n) : p ∈ allPairs n := by
  simp [allPairs]

theorem nodup_allPairs (n : ℕ) : (allPairs n).Nodup := by
  unfold allPairs
  rw [List.nodup_flatMap]
  refine ⟨fun u _ => (List.nodup_finRange n).map (fun v₁ v₂ h => by injection h), ?_⟩
  refine (List.nodup_finRange n).pairwise_of_forall_ne fun u₁ _ u₂ _ hne => ?_
  dsimp [Function.onFun]
  rw [List.disjoint_left]
  intro p hp₁ hp₂
  rw [List.mem_map] at hp₁ hp₂
  rcases hp₁ with ⟨v₁, _, rfl⟩
  rcases hp₂ with ⟨v₂, _, heq⟩
  exact hne (congrArg Prod.fst heq).symm

/-- Canonical list of undirected edges of `G : SimpleGraph (Fin n)` as pairs `(u, v)` with
`u.1 < v.1` in lexicographic order. -/
def edgeListOf {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] : List (Fin n × Fin n) :=
  (allPairs n).filter (fun e => decide (e.1.1 < e.2.1 ∧ G.Adj e.1 e.2))

@[simp]
theorem mem_edgeListOf {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (e : Fin n × Fin n) :
    e ∈ edgeListOf G ↔ e.1.1 < e.2.1 ∧ G.Adj e.1 e.2 := by
  simp [edgeListOf]

theorem nodup_edgeListOf {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] :
    (edgeListOf G).Nodup :=
  (nodup_allPairs n).filter _

theorem isSimpleEdgeList_edgeListOf {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] :
    IsSimpleEdgeList G (edgeListOf G) := by
  refine ⟨?_, ?_, ?_⟩
  · intro k hk
    have hmem : (edgeListOf G)[k] ∈ edgeListOf G := List.getElem_mem hk
    rw [mem_edgeListOf] at hmem
    intro heq
    rw [heq] at hmem
    exact Nat.lt_irrefl _ hmem.1
  · intro i j hi hj
    have hmem_i : (edgeListOf G)[i] ∈ edgeListOf G := List.getElem_mem (Nat.lt_trans hi hj)
    have hmem_j : (edgeListOf G)[j] ∈ edgeListOf G := List.getElem_mem hj
    rw [mem_edgeListOf] at hmem_i hmem_j
    rintro (⟨h1, h2⟩ | ⟨h1, h2⟩)
    · have heq : (edgeListOf G)[i] = (edgeListOf G)[j] := Prod.ext h1 h2
      have hij : i = j := ((nodup_edgeListOf G).getElem_inj_iff).mp heq
      omega
    · have h1' : ((edgeListOf G)[i]).1.1 = ((edgeListOf G)[j]).2.1 := congrArg Fin.val h1
      have h2' : ((edgeListOf G)[i]).2.1 = ((edgeListOf G)[j]).1.1 := congrArg Fin.val h2
      omega
  · intro u v
    constructor
    · intro hadj
      have hne : u ≠ v := G.ne_of_adj hadj
      rcases Nat.lt_trichotomy u.1 v.1 with hlt | heq | hgt
      · have hmem : (u, v) ∈ edgeListOf G := (mem_edgeListOf G (u, v)).mpr ⟨hlt, hadj⟩
        rcases List.mem_iff_getElem.mp hmem with ⟨k, hk, heq⟩
        exact ⟨k, hk, Or.inl ⟨congrArg Prod.fst heq, congrArg Prod.snd heq⟩⟩
      · exact absurd (Fin.ext heq) hne
      · have hmem : (v, u) ∈ edgeListOf G := (mem_edgeListOf G (v, u)).mpr ⟨hgt, hadj.symm⟩
        rcases List.mem_iff_getElem.mp hmem with ⟨k, hk, heq⟩
        exact ⟨k, hk, Or.inr ⟨congrArg Prod.fst heq, congrArg Prod.snd heq⟩⟩
    · rintro ⟨k, hk, ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩⟩
      · exact ((mem_edgeListOf G _).mp (List.getElem_mem hk)).2
      · exact ((mem_edgeListOf G _).mp (List.getElem_mem hk)).2.symm

/-- The number of pairs in `edgeListOf G` equals `G.edgeFinset.card`. -/
theorem length_edgeListOf_eq_card_edgeFinset {n : ℕ} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] :
    (edgeListOf G).length = G.edgeFinset.card := by
  rw [← List.toFinset_card_of_nodup (nodup_edgeListOf G)]
  refine Finset.card_bij (fun e _ => s(e.1, e.2)) ?_ ?_ ?_
  · intro e he
    rw [List.mem_toFinset, mem_edgeListOf] at he
    rw [SimpleGraph.mem_edgeFinset]
    exact he.2
  · intro e₁ he₁ e₂ he₂ heq
    rw [List.mem_toFinset, mem_edgeListOf] at he₁ he₂
    rw [Sym2.eq_iff] at heq
    rcases heq with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact Prod.ext h1 h2
    · have h1' : e₁.1.1 = e₂.2.1 := congrArg Fin.val h1
      have h2' : e₁.2.1 = e₂.1.1 := congrArg Fin.val h2
      omega
  · intro e he
    rw [SimpleGraph.mem_edgeFinset] at he
    induction e using Sym2.ind with
    | _ u v =>
      rw [SimpleGraph.mem_edgeSet] at he
      have hne : u ≠ v := G.ne_of_adj he
      rcases Nat.lt_trichotomy u.1 v.1 with hlt | heq | hgt
      · refine ⟨(u, v), ?_, rfl⟩
        rw [List.mem_toFinset, mem_edgeListOf]
        exact ⟨hlt, he⟩
      · exact absurd (Fin.ext heq) hne
      · refine ⟨(v, u), ?_, Sym2.eq_swap⟩
        rw [List.mem_toFinset, mem_edgeListOf]
        exact ⟨hgt, he.symm⟩

/-- Flatten a list of vertex pairs `[(u_0, v_0), ..., (u_{m-1}, v_{m-1})]` into
`[u_0.1, v_0.1, ..., u_{m-1}.1, v_{m-1}.1]`. -/
def flatEdges {n : ℕ} (edges : List (Fin n × Fin n)) : List ℕ :=
  edges.flatMap (fun e => [e.1.1, e.2.1])

@[simp]
theorem length_flatEdges {n : ℕ} (edges : List (Fin n × Fin n)) :
    (flatEdges edges).length = 2 * edges.length := by
  induction edges with
  | nil => rfl
  | cons e es ih =>
    simp only [flatEdges, List.flatMap_cons, List.length_append, List.length_cons, List.length_nil]
    rw [ ← flatEdges, ih]
    omega

theorem getElem_flatEdges_even {n : ℕ} (edges : List (Fin n × Fin n)) {k : ℕ}
    (hk : k < edges.length) :
    (flatEdges edges)[2 * k]'(by rw [length_flatEdges]; omega) = (edges[k]).1.1 := by
  induction edges generalizing k with
  | nil => simp at hk
  | cons e es ih =>
    cases k with
    | zero => rfl
    | succ k' =>
      have hk' : k' < es.length := by simpa using hk
      change ([e.1.1, e.2.1] ++ flatEdges es)[2 * (k' + 1)]'(by
        simp [length_flatEdges]; omega) = (es[k']).1.1
      rw [List.getElem_append_right (by simp)]
      have hidx : 2 * (k' + 1) - [e.1.1, e.2.1].length = 2 * k' := by
        simp only [List.length_cons, List.length_nil]
        omega
      simp only [hidx]
      exact ih hk'

theorem getElem_flatEdges_odd {n : ℕ} (edges : List (Fin n × Fin n)) {k : ℕ}
    (hk : k < edges.length) :
    (flatEdges edges)[2 * k + 1]'(by rw [length_flatEdges]; omega) = (edges[k]).2.1 := by
  induction edges generalizing k with
  | nil => simp at hk
  | cons e es ih =>
    cases k with
    | zero => rfl
    | succ k' =>
      have hk' : k' < es.length := by simpa using hk
      change ([e.1.1, e.2.1] ++ flatEdges es)[2 * (k' + 1) + 1]'(by
        simp [length_flatEdges]; omega) = (es[k']).2.1
      rw [List.getElem_append_right (by simp; omega)]
      have hidx : 2 * (k' + 1) + 1 - [e.1.1, e.2.1].length = 2 * k' + 1 := by
        simp only [List.length_cons, List.length_nil]
        omega
      simp only [hidx]
      exact ih hk'

/-- Canonical flat encoding of a finite simple graph `G : SimpleGraph (Fin n)` as a `List ℕ`:
`[n, m, u_0, v_0, ..., u_{m-1}, v_{m-1}]` where `m = (edgeListOf G).length = G.edgeFinset.card`. -/
def encGraph {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] : List ℕ :=
  [n, (edgeListOf G).length] ++ flatEdges (edgeListOf G)

@[simp]
theorem length_encGraph {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] :
    (encGraph G).length = 2 + 2 * (edgeListOf G).length := by
  simp [encGraph]
  omega

/-! ### Incremental Neighbor Lists from an Edge List -/

/-- The list of neighbors of vertex `u : Fin n` accumulated from the first `k` edges of `edges`. -/
def edgeNeighborsUpTo {n : ℕ} (edges : List (Fin n × Fin n)) (u : Fin n) : ℕ → List ℕ
  | 0 => []
  | k + 1 =>
    if hk : k < edges.length then
      let e := edges[k]
      let prev := edgeNeighborsUpTo edges u k
      if u = e.1 then prev ++ [e.2.1]
      else if u = e.2 then prev ++ [e.1.1]
      else prev
    else
      edgeNeighborsUpTo edges u k

/-- The full neighbor list of vertex `u : Fin n` accumulated from `edges`. -/
def edgeNeighbors {n : ℕ} (edges : List (Fin n × Fin n)) (u : Fin n) : List ℕ :=
  edgeNeighborsUpTo edges u edges.length

theorem edgeNeighborsUpTo_succ_fst {n : ℕ} (edges : List (Fin n × Fin n)) {k : ℕ}
    (hk : k < edges.length) :
    edgeNeighborsUpTo edges (edges[k]).1 (k + 1) =
      edgeNeighborsUpTo edges (edges[k]).1 k ++ [(edges[k]).2.1] := by
  simp [edgeNeighborsUpTo, hk]

theorem edgeNeighborsUpTo_succ_snd {n : ℕ} (edges : List (Fin n × Fin n)) {k : ℕ}
    (hk : k < edges.length) (hne : (edges[k]).1 ≠ (edges[k]).2) :
    edgeNeighborsUpTo edges (edges[k]).2 (k + 1) =
      edgeNeighborsUpTo edges (edges[k]).2 k ++ [(edges[k]).1.1] := by
  simp [edgeNeighborsUpTo, hk, hne.symm]

theorem edgeNeighborsUpTo_succ_other {n : ℕ} (edges : List (Fin n × Fin n)) {k : ℕ}
    (hk : k < edges.length) {u : Fin n} (h1 : u ≠ (edges[k]).1) (h2 : u ≠ (edges[k]).2) :
    edgeNeighborsUpTo edges u (k + 1) = edgeNeighborsUpTo edges u k := by
  simp [edgeNeighborsUpTo, hk, h1, h2]

theorem length_edgeNeighborsUpTo_succ {n : ℕ} (edges : List (Fin n × Fin n)) {k : ℕ}
    (hk : k < edges.length) (hne : (edges[k]).1 ≠ (edges[k]).2) (u : Fin n) :
    (edgeNeighborsUpTo edges u (k + 1)).length =
      (edgeNeighborsUpTo edges u k).length +
        (if u = (edges[k]).1 then 1 else 0) +
        (if u = (edges[k]).2 then 1 else 0) := by
  by_cases h1 : u = (edges[k]).1
  · subst h1
    rw [edgeNeighborsUpTo_succ_fst edges hk]
    simp [hne]
  · by_cases h2 : u = (edges[k]).2
    · subst h2
      rw [edgeNeighborsUpTo_succ_snd edges hk hne]
      simp [h1]
    · rw [edgeNeighborsUpTo_succ_other edges hk h1 h2]
      simp [h1, h2]

theorem length_edgeNeighborsUpTo_mono {n : ℕ} (edges : List (Fin n × Fin n)) (u : Fin n)
    {k₁ k₂ : ℕ} (hle : k₁ ≤ k₂) :
    (edgeNeighborsUpTo edges u k₁).length ≤ (edgeNeighborsUpTo edges u k₂).length := by
  induction hle with
  | refl => exact le_rfl
  | @step m _ ih =>
    dsimp [edgeNeighborsUpTo]
    split_ifs with h1 h2 h3
    · rw [List.length_append, List.length_singleton]; omega
    · rw [List.length_append, List.length_singleton]; omega
    · exact ih
    · exact ih

theorem length_edgeNeighborsUpTo_le_edgeNeighbors {n : ℕ} (edges : List (Fin n × Fin n))
    (u : Fin n) {k : ℕ} (hk : k ≤ edges.length) :
    (edgeNeighborsUpTo edges u k).length ≤ (edgeNeighbors edges u).length :=
  length_edgeNeighborsUpTo_mono edges u hk

theorem length_edgeNeighborsUpTo_lt_of_fst {n : ℕ} (edges : List (Fin n × Fin n))
    {k : ℕ} (hk : k < edges.length) :
    (edgeNeighborsUpTo edges (edges[k]).1 k).length <
      (edgeNeighbors edges (edges[k]).1).length := by
  have h1 : (edgeNeighborsUpTo edges (edges[k]).1 (k + 1)).length =
      (edgeNeighborsUpTo edges (edges[k]).1 k).length + 1 := by
    rw [edgeNeighborsUpTo_succ_fst edges hk, List.length_append, List.length_singleton]
  have h2 := length_edgeNeighborsUpTo_le_edgeNeighbors edges (edges[k]).1 (k := k + 1) hk
  omega

theorem length_edgeNeighborsUpTo_lt_of_snd {n : ℕ} (edges : List (Fin n × Fin n))
    {k : ℕ} (hk : k < edges.length) (hne : (edges[k]).1 ≠ (edges[k]).2) :
    (edgeNeighborsUpTo edges (edges[k]).2 k).length <
      (edgeNeighbors edges (edges[k]).2).length := by
  have h1 : (edgeNeighborsUpTo edges (edges[k]).2 (k + 1)).length =
      (edgeNeighborsUpTo edges (edges[k]).2 k).length + 1 := by
    rw [edgeNeighborsUpTo_succ_snd edges hk hne, List.length_append, List.length_singleton]
  have h2 := length_edgeNeighborsUpTo_le_edgeNeighbors edges (edges[k]).2 (k := k + 1) hk
  omega

theorem mem_edgeNeighborsUpTo_iff {n : ℕ} (edges : List (Fin n × Fin n))
    (hloop : ∀ k (hk : k < edges.length), (edges[k]).1 ≠ (edges[k]).2)
    (u : Fin n) :
    ∀ {k : ℕ} (hk : k ≤ edges.length) (x : ℕ),
      x ∈ edgeNeighborsUpTo edges u k ↔
        ∃ (i : ℕ) (hi : i < k),
          ((edges[i]'(Nat.lt_of_lt_of_le hi hk)).1 = u ∧
            (edges[i]'(Nat.lt_of_lt_of_le hi hk)).2.1 = x) ∨
          ((edges[i]'(Nat.lt_of_lt_of_le hi hk)).2 = u ∧
            (edges[i]'(Nat.lt_of_lt_of_le hi hk)).1.1 = x)
  | 0, _, x => by simp [edgeNeighborsUpTo]
  | k + 1, hk, x => by
    have hk_lt : k < edges.length := by omega
    have hne := hloop k hk_lt
    have ih := @mem_edgeNeighborsUpTo_iff n edges hloop u k (by omega) x
    by_cases h1 : u = (edges[k]).1
    · subst h1
      rw [edgeNeighborsUpTo_succ_fst edges hk_lt, List.mem_append, List.mem_singleton, ih]
      constructor
      · rintro (⟨i, hi, hmatch⟩ | rfl)
        · exact ⟨i, Nat.lt_succ_of_lt hi, hmatch⟩
        · exact ⟨k, Nat.lt_succ_self k, Or.inl ⟨rfl, rfl⟩⟩
      · rintro ⟨i, hi, hmatch⟩
        rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hlt | rfl
        · exact Or.inl ⟨i, hlt, hmatch⟩
        · rcases hmatch with ⟨_, rfl⟩ | ⟨heq, _⟩
          · exact Or.inr rfl
          · exact absurd heq.symm hne
    · by_cases h2 : u = (edges[k]).2
      · subst h2
        rw [edgeNeighborsUpTo_succ_snd edges hk_lt hne, List.mem_append, List.mem_singleton, ih]
        constructor
        · rintro (⟨i, hi, hmatch⟩ | rfl)
          · exact ⟨i, Nat.lt_succ_of_lt hi, hmatch⟩
          · exact ⟨k, Nat.lt_succ_self k, Or.inr ⟨rfl, rfl⟩⟩
        · rintro ⟨i, hi, hmatch⟩
          rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hlt | rfl
          · exact Or.inl ⟨i, hlt, hmatch⟩
          · rcases hmatch with ⟨heq, _⟩ | ⟨_, rfl⟩
            · exact absurd heq hne
            · exact Or.inr rfl
      · rw [edgeNeighborsUpTo_succ_other edges hk_lt h1 h2, ih]
        constructor
        · rintro ⟨i, hi, hmatch⟩
          exact ⟨i, Nat.lt_succ_of_lt hi, hmatch⟩
        · rintro ⟨i, hi, hmatch⟩
          rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hlt | rfl
          · exact ⟨i, hlt, hmatch⟩
          · rcases hmatch with ⟨heq, _⟩ | ⟨heq, _⟩
            · exact absurd heq.symm h1
            · exact absurd heq.symm h2

theorem nodup_edgeNeighborsUpTo {n : ℕ} {G : SimpleGraph (Fin n)} {edges : List (Fin n × Fin n)}
    (hedges : IsSimpleEdgeList G edges) (u : Fin n) :
    ∀ k (_hk : k ≤ edges.length), (edgeNeighborsUpTo edges u k).Nodup
  | 0, _ => List.nodup_nil
  | k + 1, hk => by
    rcases hedges with ⟨hloop, hnodup_edges, _⟩
    have hk_lt : k < edges.length := by omega
    have hne := hloop k hk_lt
    have ih := nodup_edgeNeighborsUpTo ⟨hloop, hnodup_edges, ‹_›⟩ u k (by omega)
    by_cases h1 : u = (edges[k]).1
    · subst h1
      rw [edgeNeighborsUpTo_succ_fst edges hk_lt, List.nodup_append]
      refine ⟨ih, List.nodup_singleton _, ?_⟩
      intro x hx y hy hxy
      rw [List.mem_singleton] at hy
      subst hy; subst hxy
      rw [mem_edgeNeighborsUpTo_iff edges hloop (edges[k]).1 (by omega)] at hx
      rcases hx with ⟨i, hi, ⟨he1, he2⟩ | ⟨he1, he2⟩⟩
      · exact hnodup_edges i k hi hk_lt (Or.inl ⟨he1, Fin.ext he2⟩)
      · exact hnodup_edges i k hi hk_lt (Or.inr ⟨Fin.ext he2, he1⟩)
    · by_cases h2 : u = (edges[k]).2
      · subst h2
        rw [edgeNeighborsUpTo_succ_snd edges hk_lt hne, List.nodup_append]
        refine ⟨ih, List.nodup_singleton _, ?_⟩
        intro x hx y hy hxy
        rw [List.mem_singleton] at hy
        subst hy; subst hxy
        rw [mem_edgeNeighborsUpTo_iff edges hloop (edges[k]).2 (by omega)] at hx
        rcases hx with ⟨i, hi, ⟨he1, he2⟩ | ⟨he1, he2⟩⟩
        · exact hnodup_edges i k hi hk_lt (Or.inr ⟨he1, Fin.ext he2⟩)
        · exact hnodup_edges i k hi hk_lt (Or.inl ⟨Fin.ext he2, he1⟩)
      · rw [edgeNeighborsUpTo_succ_other edges hk_lt h1 h2]
        exact ih

/-- If `IsSimpleEdgeList G edges`, then `edgeNeighbors edges` is a valid adjacency-list family
for `G`. -/
theorem isAdjListFamily_edgeNeighbors {n : ℕ} {G : SimpleGraph (Fin n)}
    {edges : List (Fin n × Fin n)} (hedges : IsSimpleEdgeList G edges) :
    IsAdjListFamily G (edgeNeighbors edges) := by
  intro u
  have hno : (edgeNeighbors edges u).Nodup := nodup_edgeNeighborsUpTo hedges u edges.length le_rfl
  have hlt : ∀ x ∈ edgeNeighbors edges u, x < n := by
    intro x hx
    rw [edgeNeighbors, mem_edgeNeighborsUpTo_iff edges hedges.1 u le_rfl] at hx
    rcases hx with ⟨i, _, ⟨_, rfl⟩ | ⟨_, rfl⟩⟩
    · exact (edges[i]).2.2
    · exact (edges[i]).1.2
  have hlen : (edgeNeighbors edges u).length ≤ n := by
    have hsub : (edgeNeighbors edges u).toFinset ⊆ Finset.range n := by
      intro x hx
      rw [List.mem_toFinset] at hx
      exact Finset.mem_range.mpr (hlt x hx)
    have hcard := Finset.card_le_card hsub
    rwa [List.toFinset_card_of_nodup hno, Finset.card_range] at hcard
  refine ⟨hlt, hno, hlen, fun v => ?_⟩
  rw [edgeNeighbors, mem_edgeNeighborsUpTo_iff edges hedges.1 u le_rfl, hedges.2.2 u v]
  constructor
  · rintro ⟨i, hi, ⟨h1, h2⟩ | ⟨h1, h2⟩⟩
    · exact ⟨i, hi, Or.inl ⟨h1, Fin.ext h2⟩⟩
    · exact ⟨i, hi, Or.inr ⟨Fin.ext h2, h1⟩⟩
  · rintro ⟨i, hi, ⟨h1, h2⟩ | ⟨h1, h2⟩⟩
    · exact ⟨i, hi, Or.inl ⟨h1, congrArg Fin.val h2⟩⟩
    · exact ⟨i, hi, Or.inr ⟨h2, congrArg Fin.val h1⟩⟩

/-- Prefix degree sum `∑ u : Fin n with u.1 < idx, (edgeNeighbors edges u).length`. -/
def prefixDeg {n : ℕ} (edges : List (Fin n × Fin n)) (idx : ℕ) : ℕ :=
  ∑ u ∈ Finset.univ.filter (fun u : Fin n => u.1 < idx), (edgeNeighbors edges u).length

@[simp]
theorem prefixDeg_zero {n : ℕ} (edges : List (Fin n × Fin n)) :
    prefixDeg edges 0 = 0 := by
  simp [prefixDeg]

theorem prefixDeg_mono {n : ℕ} (edges : List (Fin n × Fin n)) {i j : ℕ} (hij : i ≤ j) :
    prefixDeg edges i ≤ prefixDeg edges j := by
  apply Finset.sum_le_sum_of_subset
  intro u hu
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hu ⊢
  omega

theorem prefixDeg_succ {n : ℕ} (edges : List (Fin n × Fin n)) (u : Fin n) :
    prefixDeg edges (u.1 + 1) = prefixDeg edges u.1 + (edgeNeighbors edges u).length := by
  unfold prefixDeg
  have hfilter : Finset.univ.filter (fun x : Fin n => x.1 < u.1 + 1) =
      insert u (Finset.univ.filter (fun x : Fin n => x.1 < u.1)) := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert, Fin.ext_iff]
    omega
  have hnot : u ∉ Finset.univ.filter (fun x : Fin n => x.1 < u.1) := by
    simp
  rw [hfilter, Finset.sum_insert hnot, Nat.add_comm]

theorem sum_length_edgeNeighborsUpTo {n : ℕ} (edges : List (Fin n × Fin n))
    (hloop : ∀ k (hk : k < edges.length), (edges[k]).1 ≠ (edges[k]).2) :
    ∀ k (_hk : k ≤ edges.length),
      (∑ u : Fin n, (edgeNeighborsUpTo edges u k).length) = 2 * k
  | 0, _ => by simp [edgeNeighborsUpTo]
  | k + 1, hk => by
    have hk_lt : k < edges.length := by omega
    have ih := sum_length_edgeNeighborsUpTo edges hloop k (by omega)
    have hstep : ∀ u : Fin n,
        (edgeNeighborsUpTo edges u (k + 1)).length =
          (edgeNeighborsUpTo edges u k).length +
            (if u = (edges[k]).1 then 1 else 0) +
            (if u = (edges[k]).2 then 1 else 0) :=
      length_edgeNeighborsUpTo_succ edges hk_lt (hloop k hk_lt)
    simp_rw [hstep, Finset.sum_add_distrib, ih]
    simp
    omega

theorem prefixDeg_self {n : ℕ} (edges : List (Fin n × Fin n))
    (hloop : ∀ k (hk : k < edges.length), (edges[k]).1 ≠ (edges[k]).2) :
    prefixDeg edges n = 2 * edges.length := by
  unfold prefixDeg
  have hfilter : Finset.univ.filter (fun u : Fin n => u.1 < n) = Finset.univ := by
    ext u
    simp
  rw [hfilter]
  exact sum_length_edgeNeighborsUpTo edges hloop edges.length le_rfl

theorem totalAdjEntries_edgeNeighbors {n : ℕ} (edges : List (Fin n × Fin n))
    (hloop : ∀ k (hk : k < edges.length), (edges[k]).1 ≠ (edges[k]).2) :
    totalAdjEntries (edgeNeighbors edges) = 2 * edges.length :=
  sum_length_edgeNeighborsUpTo edges hloop edges.length le_rfl

/-! ### Helper Commands for Two-Pass CSR Construction -/

/-- Increment `a[r_idx]` by `1` using scratch register `r_tmp`. -/
def incArrAt (a : Arr) (r_idx r_tmp : Reg) : Cmd :=
  .seq (.assign r_tmp (.read a (.reg r_idx)))
    (.write a (.reg r_idx) (.op .add (.reg r_tmp) (.const 1)))

/-- Specification for `incArrAt`: increments `a[u.1]` by `1` in `9` steps while preserving all
other entries of `a`, all arrays `≠ a`, and all registers `≠ r_tmp`. -/
theorem incArrAt_exec {w n : ℕ} (a : Arr) (r_idx r_tmp : Reg)
    (deg : Fin n → ℕ) (u : Fin n) (s : State)
    (hne_it : r_idx ≠ r_tmp)
    (hw : 1 < 2 ^ w) (hn_w : n < 2 ^ w) (hdeg_w : deg u + 1 < 2 ^ w)
    (hlen : (s.arrs a).length = n)
    (hidx : s.regs r_idx = u.1)
    (hdeg : ∀ x : Fin n, (s.arrs a)[x.1]'(by rw [hlen]; exact x.2) = deg x) :
    ∃ s' t,
      Exec w (incArrAt a r_idx r_tmp) s s' t ∧
      t ≤ 9 ∧
      (∃ (hlen' : (s'.arrs a).length = n),
        ∀ x : Fin n, (s'.arrs a)[x.1]'(by rw [hlen']; exact x.2) =
          if x = u then deg u + 1 else deg x) ∧
      (∀ a' ≠ a, s'.arrs a' = s.arrs a') ∧
      (∀ r ≠ r_tmp, s'.regs r = s.regs r) := by
  have hu_w : u.1 < 2 ^ w := by omega
  have hdu_w : deg u < 2 ^ w := by omega
  have hread : (Expr.read a (.reg r_idx)).eval w s = some (deg u) := by
    have hu_len : u.1 < (s.arrs a).length := by rw [hlen]; exact u.2
    have hval := hdeg u
    simp [Expr.eval, checkWord, hidx, hu_w, hu_len, hval, hdu_w]
  let s₁ := s.setReg r_tmp (deg u)
  have hex₁ : Exec w (.assign r_tmp (.read a (.reg r_idx))) s s₁ 3 := .assign hread
  have hidx₁ : (Expr.reg r_idx).eval w s₁ = some u.1 := by
    simp [s₁, Expr.eval, checkWord, hne_it, hidx, hu_w]
  have hval₁ : (Expr.op .add (.reg r_tmp) (.const 1)).eval w s₁ = some (deg u + 1) := by
    simp [s₁, Expr.eval, BinOp.eval, BinOp.raw, checkWord, hdu_w, hw, hdeg_w]
  let s₂ := s₁.writeArr a u.1 (deg u + 1)
  have hex₂ : Exec w (.write a (.reg r_idx) (.op .add (.reg r_tmp) (.const 1))) s₁ s₂ 5 :=
    .write hidx₁ hval₁ (by rw [State.setReg_arrs, hlen]; exact u.2)
  refine ⟨s₂, 3 + 5, .seq hex₁ hex₂, by omega, ⟨by simp [s₂, s₁, hlen], ?_⟩,
    fun a' ha' => by simp [s₂, s₁, ha'],
    fun r hr => by simp [s₂, s₁, hr]⟩
  intro x
  simp only [s₂, s₁, State.writeArr_arrs_self, State.setReg_arrs]
  by_cases hxu : x = u
  · subst hxu
    simp only [↓reduceIte]
    exact List.getElem_set_self (by rw [List.length_set, hlen]; exact x.2)
  · have hne_val : u.1 ≠ x.1 := fun h => hxu (Fin.ext h.symm)
    simp only [hxu, ↓reduceIte]
    rw [List.getElem_set_ne hne_val]
    exact hdeg x

/-- Append `val` to the CSR list of vertex `r_u` by reading `r_cnt := a_end[r_u]` and invoking
`listAppend`. -/
def csrAppend (a_end a_entries : Arr) (r_u r_cnt : Reg) (val : Expr) : Cmd :=
  .seq (.assign r_cnt (.read a_end (.reg r_u)))
    (listAppend a_end a_entries r_u r_cnt val)

/-- Disjointness of slice intervals in `prefixDeg`: if `w ≠ u` and `k_u < (edgeNeighbors edges u).length`
and `k_w < (edgeNeighbors edges w).length`, then `prefixDeg edges u.1 + k_u ≠ prefixDeg edges w.1 + k_w`. -/
theorem prefixDeg_add_ne_of_ne {n : ℕ} (edges : List (Fin n × Fin n))
    {u w : Fin n} (hne : w ≠ u)
    {k_u k_w : ℕ} (hku : k_u < (edgeNeighbors edges u).length)
    (hkw : k_w < (edgeNeighbors edges w).length) :
    prefixDeg edges u.1 + k_u ≠ prefixDeg edges w.1 + k_w := by
  rcases Nat.lt_trichotomy u.1 w.1 with hlt | heq | hgt
  · have h1 := prefixDeg_succ edges u
    have h2 : prefixDeg edges (u.1 + 1) ≤ prefixDeg edges w.1 := prefixDeg_mono edges hlt
    omega
  · exact absurd (Fin.ext heq.symm) hne
  · have h1 := prefixDeg_succ edges w
    have h2 : prefixDeg edges (w.1 + 1) ≤ prefixDeg edges u.1 := prefixDeg_mono edges hgt
    omega

/-- Specification for `csrAppend`: appends `v` to vertex `u`'s partial CSR slice while preserving
all other vertices' CSR slices in `prefixDeg`. -/
theorem csrAppend_exec {n : ℕ} {w_sz : ℕ} (edges : List (Fin n × Fin n))
    (a_start a_end a_entries : ℕ) (r_u r_cnt : ℕ) (val : Expr)
    (cur : Fin n → List ℕ) (u : Fin n) (v : ℕ) (s : State)
    (hne_se : a_start ≠ a_end) (hne_sent : a_start ≠ a_entries) (hne_eent : a_end ≠ a_entries)
    (hne_uc : r_u ≠ r_cnt)
    (hw : 1 < 2 ^ w_sz) (hn_w : n < 2 ^ w_sz)
    (hent_w : 2 * edges.length < 2 ^ w_sz)
    (hloop : ∀ k (hk : k < edges.length), (edges[k]).1 ≠ (edges[k]).2)
    (hlen_ent : (s.arrs a_entries).length = 2 * edges.length)
    (hcur_le : ∀ x : Fin n, (cur x).length ≤ (edgeNeighbors edges x).length)
    (hcur_u : (cur u).length < (edgeNeighbors edges u).length)
    (hlists : ∀ x : Fin n,
      IsListAt a_start a_end a_entries x.1 (prefixDeg edges x.1)
        (prefixDeg edges x.1 + (cur x).length) (cur x) s)
    (hru : s.regs r_u = u.1)
    (hval : ∀ s' : State, (∀ r ≠ (r_cnt : Reg), s'.regs r = s.regs r) →
      (∀ a, s'.arrs a = s.arrs a) → val.eval w_sz s' = some v) :
    ∃ s' t,
      Exec w_sz (csrAppend a_end a_entries r_u r_cnt val) s s' t ∧
      t ≤ val.cost + 12 ∧
      (s'.arrs a_end).length = (s.arrs a_end).length ∧
      (s'.arrs a_entries).length = 2 * edges.length ∧
      (∀ x : Fin n,
        let next := if x = u then cur u ++ [v] else cur x
        IsListAt a_start a_end a_entries x.1 (prefixDeg edges x.1)
          (prefixDeg edges x.1 + next.length) next s') ∧
      (∀ a' : Arr, a' ≠ a_end → a' ≠ a_entries → s'.arrs a' = s.arrs a') ∧
      (∀ r : Reg, r ≠ r_cnt → s'.regs r = s.regs r) := by
  have hu_w : u.1 < 2 ^ w_sz := by omega
  have hst_bound : prefixDeg edges u.1 + (cur u).length + 1 ≤ 2 * edges.length := by
    have h1 := prefixDeg_succ edges u
    have h2 : prefixDeg edges (u.1 + 1) ≤ prefixDeg edges n := prefixDeg_mono edges u.2
    have h3 := prefixDeg_self edges hloop
    omega
  have hcnt_w : prefixDeg edges u.1 + (cur u).length < 2 ^ w_sz := by omega
  have hcnt1_w : prefixDeg edges u.1 + (cur u).length + 1 < 2 ^ w_sz := by omega
  rcases hlists u with ⟨hu_st, hu_en, hen_ent, hdiff, hst_u, hen_u, hle_u, helem_u⟩
  have hread_end : (Expr.read a_end (.reg r_u)).eval w_sz s =
      some (prefixDeg edges u.1 + (cur u).length) := by
    simp [Expr.eval, checkWord, hru, hu_w, hu_en, hen_u, hcnt_w]
  let s₁ := s.setReg r_cnt (prefixDeg edges u.1 + (cur u).length)
  have hex₁ : Exec w_sz (.assign r_cnt (.read a_end (.reg r_u))) s s₁ 3 := .assign hread_end
  have hne_uc' : (r_u : Reg) ≠ r_cnt := by omega
  have hne_se' : (a_start : Arr) ≠ a_end := by omega
  have hne_sent' : (a_start : Arr) ≠ a_entries := by omega
  have hne_eent' : (a_end : Arr) ≠ a_entries := by omega
  have hidx_cnt : (Expr.reg r_cnt).eval w_sz s₁ = some (prefixDeg edges u.1 + (cur u).length) := by
    simp [s₁, Expr.eval, checkWord, hcnt_w]
  have hval₁ : val.eval w_sz s₁ = some v :=
    hval s₁ (fun r hr => by simp [s₁, hr]) (fun _ => rfl)
  let s₂ := s₁.writeArr a_entries (prefixDeg edges u.1 + (cur u).length) v
  have hex₂ : Exec w_sz (.write a_entries (.reg r_cnt) val) s₁ s₂ (1 + val.cost + 1) :=
    .write hidx_cnt hval₁ (by simp [s₁, hlen_ent]; omega)
  have hinc : (Expr.op .add (.reg r_cnt) (.const 1)).eval w_sz s₂ =
      some (prefixDeg edges u.1 + (cur u).length + 1) := by
    simp [s₂, s₁, Expr.eval, BinOp.eval, BinOp.raw, checkWord, hcnt_w, hw, hcnt1_w]
  let s₃ := s₂.setReg r_cnt (prefixDeg edges u.1 + (cur u).length + 1)
  have hex₃ : Exec w_sz (.assign r_cnt (.op .add (.reg r_cnt) (.const 1))) s₂ s₃ 4 :=
    .assign hinc
  have hidx_u : (Expr.reg r_u).eval w_sz s₃ = some u.1 := by
    simp [s₃, s₂, s₁, Expr.eval, checkWord, hne_uc', hru, hu_w]
  have hval_cnt : (Expr.reg r_cnt).eval w_sz s₃ =
      some (prefixDeg edges u.1 + (cur u).length + 1) := by
    simp [s₃, Expr.eval, checkWord, hcnt1_w]
  let s₄ := s₃.writeArr a_end u.1 (prefixDeg edges u.1 + (cur u).length + 1)
  have hex₄ : Exec w_sz (.write a_end (.reg r_u) (.reg r_cnt)) s₃ s₄ 3 :=
    .write hidx_u hval_cnt (by simpa [s₃, s₂, s₁, hne_eent'] using hu_en)
  refine ⟨s₄, 3 + ((1 + val.cost + 1) + (4 + 3)),
    .seq hex₁ (.seq hex₂ (.seq hex₃ hex₄)), by omega,
    by simp [s₄, s₃, s₂, s₁, hne_eent'],
    by simp [s₄, s₃, s₂, s₁, hne_eent'.symm, hlen_ent], ?_,
    fun a' ha1 ha2 => by simp [s₄, s₃, s₂, s₁, ha1, ha2],
    fun r hr => by simp [s₄, s₃, s₂, s₁, hr]⟩
  intro x
  by_cases hxu : x = u
  · subst hxu
    simp only [↓reduceIte, List.length_append, List.length_singleton]
    have hlen_app : prefixDeg edges x.1 + ((cur x).length + 1) =
        prefixDeg edges x.1 + (cur x).length + 1 := by omega
    rw [hlen_app]
    refine ⟨by simpa [s₄, s₃, s₂, s₁, hne_se', hne_sent'] using hu_st,
      by simpa [s₄, s₃, s₂, s₁, hne_eent'] using hu_en,
      by simp [s₄, s₃, s₂, s₁, hne_eent'.symm, hlen_ent]; omega,
      by simp; omega,
      by simpa [s₄, s₃, s₂, s₁, hne_se', hne_sent'] using hst_u,
      ?_, by omega, ?_⟩
    · simp only [s₄, s₃, s₂, s₁, State.writeArr_arrs_self, State.setReg_arrs,
        State.writeArr_arrs_ne _ _ _ hne_eent']
      exact List.getElem_set_self (by rw [List.length_set]; exact hu_en)
    · intro k hk
      simp only [List.length_append, List.length_singleton] at hk
      simp only [s₄, s₃, s₂, s₁, State.writeArr_arrs_ne _ _ _ hne_eent'.symm,
        State.setReg_arrs, State.writeArr_arrs_self]
      by_cases hkeq : k = (cur x).length
      · subst hkeq
        rw [List.getElem_set_self (by rw [List.length_set, hlen_ent]; omega)]
        simp
      · have hklt : k < (cur x).length := by omega
        rw [List.getElem_set_ne (by omega), List.getElem_append_left hklt]
        exact helem_u k hklt
  · simp only [hxu, ↓reduceIte]
    rcases hlists x with ⟨hx_st, hx_en, hxen_ent, hxdiff, hst_x, hen_x, hle_x, helem_x⟩
    have hne_val : u.1 ≠ x.1 := fun h => hxu (Fin.ext h.symm)
    refine ⟨by simpa [s₄, s₃, s₂, s₁, hne_se', hne_sent'] using hx_st,
      by simpa [s₄, s₃, s₂, s₁, hne_eent'] using hx_en,
      by simpa [s₄, s₃, s₂, s₁, hne_eent'.symm] using hxen_ent,
      hxdiff,
      by simpa [s₄, s₃, s₂, s₁, hne_se', hne_sent'] using hst_x,
      ?_, hle_x, ?_⟩
    · simp only [s₄, s₃, s₂, s₁, State.writeArr_arrs_self, State.setReg_arrs,
        State.writeArr_arrs_ne _ _ _ hne_eent']
      rw [List.getElem_set_ne hne_val]
      exact hen_x
    · intro k hk
      simp only [s₄, s₃, s₂, s₁, State.writeArr_arrs_ne _ _ _ hne_eent'.symm,
        State.setReg_arrs, State.writeArr_arrs_self]
      have hne_idx : prefixDeg edges u.1 + (cur u).length ≠ prefixDeg edges x.1 + k :=
        prefixDeg_add_ne_of_ne edges hxu hcur_u (Nat.lt_of_lt_of_le hk (hcur_le x))
      rw [List.getElem_set_ne hne_idx]
      exact helem_x k hk

/-! ### Reading Edge Endpoints and Two-Pass CSR Graph Parser (`parseGraphProg`) -/

theorem inArr_getElem_zero {n : ℕ} (edges : List (Fin n × Fin n)) (extra : List ℕ)
    {arr : List ℕ} (harr : arr = [n, edges.length] ++ flatEdges edges ++ extra) :
    ∃ (h0 : 0 < arr.length), arr[0]'h0 = n := by
  refine ⟨by simp [harr], ?_⟩
  simp [harr]

theorem inArr_getElem_one {n : ℕ} (edges : List (Fin n × Fin n)) (extra : List ℕ)
    {arr : List ℕ} (harr : arr = [n, edges.length] ++ flatEdges edges ++ extra) :
    ∃ (h1 : 1 < arr.length), arr[1]'h1 = edges.length := by
  refine ⟨by simp [harr], ?_⟩
  simp [harr]

theorem inArr_getElem_edge_fst {n : ℕ} (edges : List (Fin n × Fin n)) (extra : List ℕ)
    {arr : List ℕ} (harr : arr = [n, edges.length] ++ flatEdges edges ++ extra)
    {k : ℕ} (hk : k < edges.length) :
    ∃ (hidx : 2 + 2 * k < arr.length), arr[2 + 2 * k]'hidx = (edges[k]).1.1 := by
  have hlen : 2 + 2 * k < arr.length := by
    simp [harr, length_flatEdges]; omega
  refine ⟨hlen, ?_⟩
  have h1 : arr[2 + 2 * k]'hlen =
      (([n, edges.length] ++ flatEdges edges)[2 + 2 * k]'(by simp [length_flatEdges]; omega)) := by
    simp only [harr]
    exact List.getElem_append_left (by simp [length_flatEdges]; omega)
  rw [h1, List.getElem_append_right (by simp)]
  have hsub : 2 + 2 * k - [n, edges.length].length = 2 * k := by simp
  simp only [hsub]
  exact getElem_flatEdges_even edges hk

theorem inArr_getElem_edge_snd {n : ℕ} (edges : List (Fin n × Fin n)) (extra : List ℕ)
    {arr : List ℕ} (harr : arr = [n, edges.length] ++ flatEdges edges ++ extra)
    {k : ℕ} (hk : k < edges.length) :
    ∃ (hidx : 2 + 2 * k + 1 < arr.length), arr[2 + 2 * k + 1]'hidx = (edges[k]).2.1 := by
  have hlen : 2 + 2 * k + 1 < arr.length := by
    simp [harr, length_flatEdges]; omega
  refine ⟨hlen, ?_⟩
  have h1 : arr[2 + 2 * k + 1]'hlen =
      (([n, edges.length] ++ flatEdges edges)[2 + 2 * k + 1]'(by simp [length_flatEdges]; omega)) := by
    simp only [harr]
    exact List.getElem_append_left (by simp [length_flatEdges]; omega)
  rw [h1, List.getElem_append_right (by simp; omega)]
  have hsub : 2 + 2 * k + 1 - [n, edges.length].length = 2 * k + 1 := by
    simp only [List.length_cons, List.length_nil]; omega
  simp only [hsub]
  exact getElem_flatEdges_odd edges hk

/-- Read the `k`-th edge endpoints `(u_k, v_k)` from `inArr[2 + 2 * r_k]` and
`inArr[2 + 2 * r_k + 1]` into `r_u` and `r_v`, using `r_idx` for `2 + 2 * r_k`. -/
def readEdgeEndpoints (r_k r_u r_v r_idx : Reg) : Cmd :=
  .seq (.assign r_idx (.op .add (.const 2) (.op .mul (.const 2) (.reg r_k))))
    (.seq (.assign r_u (.read inArr (.reg r_idx)))
      (.assign r_v (.read inArr (.op .add (.reg r_idx) (.const 1)))))

theorem readEdgeEndpoints_exec {w n : ℕ} (edges : List (Fin n × Fin n)) (extra : List ℕ)
    (r_k r_u r_v r_idx : Reg) (k : ℕ) (s : State)
    (hne_ui : r_u ≠ r_idx) (hne_uv : r_u ≠ r_v)
    (hw2 : 2 < 2 ^ w) (hn_w : n < 2 ^ w) (hm2_w : 2 + 2 * edges.length < 2 ^ w)
    (hk : k < edges.length)
    (hin : s.arrs inArr = [n, edges.length] ++ flatEdges edges ++ extra)
    (hrk : s.regs r_k = k) :
    ∃ s' t,
      Exec w (readEdgeEndpoints r_k r_u r_v r_idx) s s' t ∧
      t ≤ 14 ∧
      s'.regs r_u = (edges[k]).1.1 ∧
      s'.regs r_v = (edges[k]).2.1 ∧
      (∀ a, s'.arrs a = s.arrs a) ∧
      (∀ r, r ≠ r_u → r ≠ r_v → r ≠ r_idx → s'.regs r = s.regs r) := by
  have hw : 1 < 2 ^ w := by omega
  have hk_w : k < 2 ^ w := by omega
  have h2k_w : 2 * k < 2 ^ w := by omega
  have hidx_w : 2 + 2 * k < 2 ^ w := by omega
  have hidx1_w : 2 + 2 * k + 1 < 2 ^ w := by omega
  have hu_w : (edges[k]).1.1 < 2 ^ w := by have := (edges[k]).1.2; omega
  have hv_w : (edges[k]).2.1 < 2 ^ w := by have := (edges[k]).2.2; omega
  have heval_idx :
      (Expr.op .add (.const 2) (.op .mul (.const 2) (.reg r_k))).eval w s =
        some (2 + 2 * k) := by
    simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hrk, hw2, hk_w, h2k_w, hidx_w]
  let s₁ := s.setReg r_idx (2 + 2 * k)
  have hex₁ : Exec w (.assign r_idx (.op .add (.const 2) (.op .mul (.const 2) (.reg r_k))))
      s s₁ 6 := .assign heval_idx
  obtain ⟨hlen_u, hget_u⟩ := inArr_getElem_edge_fst edges extra hin hk
  have heval_u : (Expr.read inArr (.reg r_idx)).eval w s₁ = some (edges[k]).1.1 := by
    simp [s₁, Expr.eval, checkWord, hidx_w, hlen_u, hget_u, hu_w]
  let s₂ := s₁.setReg r_u (edges[k]).1.1
  have hex₂ : Exec w (.assign r_u (.read inArr (.reg r_idx))) s₁ s₂ 3 := .assign heval_u
  obtain ⟨hlen_v, hget_v⟩ := inArr_getElem_edge_snd edges extra hin hk
  have heval_v : (Expr.read inArr (.op .add (.reg r_idx) (.const 1))).eval w s₂ =
      some (edges[k]).2.1 := by
    simp [s₂, s₁, Expr.eval, BinOp.eval, BinOp.raw, checkWord, hne_ui.symm,
      hidx_w, hw, hidx1_w, hlen_v, hget_v, hv_w]
  let s₃ := s₂.setReg r_v (edges[k]).2.1
  have hex₃ : Exec w (.assign r_v (.read inArr (.op .add (.reg r_idx) (.const 1)))) s₂ s₃ 5 :=
    .assign heval_v
  refine ⟨s₃, 6 + (3 + 5), .seq hex₁ (.seq hex₂ hex₃), by omega,
    by simp [s₃, s₂, hne_uv],
    by simp [s₃],
    fun _ => rfl,
    fun r hru hrv hri => by simp [s₃, s₂, s₁, hru, hrv, hri]⟩

/-- Body of Pass 1 (degree counting) in `parseGraphProg`. -/
def parsePass1Body (a_deg : Arr) (r_base : Reg) : Cmd :=
  .seq (readEdgeEndpoints (r_base + 2) (r_base + 3) (r_base + 4) (r_base + 5))
    (.seq (incArrAt a_deg (r_base + 3) (r_base + 6))
      (incArrAt a_deg (r_base + 4) (r_base + 6)))

/-- Body of the prefix-sum loop in `parseGraphProg`. -/
def parsePrefixBody (a_deg a_start a_end : Arr) (r_base : Reg) : Cmd :=
  .seq (.write a_start (.reg (r_base + 3)) (.reg (r_base + 6)))
    (.seq (.write a_end (.reg (r_base + 3)) (.reg (r_base + 6)))
      (.seq (.assign (r_base + 4) (.read a_deg (.reg (r_base + 3))))
        (.assign (r_base + 6) (.op .add (.reg (r_base + 6)) (.reg (r_base + 4))))))

/-- Body of Pass 2 (edge scattering) in `parseGraphProg`. -/
def parsePass2Body (a_end a_entries : Arr) (r_base : Reg) : Cmd :=
  .seq (readEdgeEndpoints (r_base + 2) (r_base + 3) (r_base + 4) (r_base + 5))
    (.seq (csrAppend a_end a_entries (r_base + 3) (r_base + 6) (.reg (r_base + 4)))
      (csrAppend a_end a_entries (r_base + 4) (r_base + 6) (.reg (r_base + 3))))

/-- Invariant for Pass 1 of `parseGraphProg`. -/
def ParsePass1Inv {n : ℕ} (edges : List (Fin n × Fin n)) (extra : List ℕ)
    (a_deg : Arr) (r_base : Reg) (k : ℕ) (s : State) : Prop :=
  s.arrs inArr = [n, edges.length] ++ flatEdges edges ++ extra ∧
  s.regs r_base = n ∧
  s.regs (r_base + 1) = edges.length ∧
  s.regs (r_base + 2) = k ∧
  ∃ (hd : (s.arrs a_deg).length = n),
    ∀ x : Fin n, (s.arrs a_deg)[x.1]'(by rw [hd]; exact x.2) =
      (edgeNeighborsUpTo edges x k).length

theorem parsePass1Loop_exec {w n : ℕ} (G : SimpleGraph (Fin n))
    (edges : List (Fin n × Fin n)) (extra : List ℕ)
    (a_deg : ℕ) (r_base : ℕ)
    (hedges : IsSimpleEdgeList G edges)
    (hne_in_deg : (inArr : Arr) ≠ a_deg)
    (hw2 : 2 < 2 ^ w) (hn_w : n < 2 ^ w) (hm2_w : 2 + 2 * edges.length < 2 ^ w) :
    ⦃ParsePass1Inv edges extra a_deg r_base 0⦄[w]
      forUp (r_base + 2) (.reg (r_base + 1)) (parsePass1Body a_deg r_base)
    ⦃ParsePass1Inv edges extra a_deg r_base edges.length⦄ ≤
      fun _ => 3 + edges.length * (32 + 7) := by
  have hw : 1 < 2 ^ w := by omega
  have hm_w : edges.length < 2 ^ w := by omega
  have hne_35 : (r_base + 3 : Reg) ≠ r_base + 5 := by omega
  have hne_34 : (r_base + 3 : Reg) ≠ r_base + 4 := by omega
  have hne_36 : (r_base + 3 : Reg) ≠ r_base + 6 := by omega
  have hne_46 : (r_base + 4 : Reg) ≠ r_base + 6 := by omega
  apply Triple.forUp_const (ParsePass1Inv edges extra a_deg r_base) edges.length 32 hw hm_w
  · intro k _ s ⟨_, _, hrm, hrk, _⟩
    exact ⟨hrk, by simp [Expr.eval, checkWord, hrm, hm_w]⟩
  · intro k hk s ⟨hin_s, hrn_s, hrm_s, hrk_s, hd_len, hd_val⟩
    rcases readEdgeEndpoints_exec edges extra (r_base + 2) (r_base + 3) (r_base + 4) (r_base + 5)
        k s hne_35 hne_34 hw2 hn_w hm2_w hk hin_s hrk_s with
      ⟨sa, ta, hexa, hta, hru_a, hrv_a, harr_a, hreg_a⟩
    have hd_len_a : (sa.arrs a_deg).length = n := by rw [harr_a]; exact hd_len
    have hd_val_a : ∀ x : Fin n, (sa.arrs a_deg)[x.1]'(by rw [hd_len_a]; exact x.2) =
        (edgeNeighborsUpTo edges x k).length := by
      intro x; simp only [harr_a]; exact hd_val x
    have hdeg_u_w : (edgeNeighborsUpTo edges (edges[k]).1 k).length + 1 < 2 ^ w := by
      have hlt := length_edgeNeighborsUpTo_lt_of_fst edges hk
      have hle := (isAdjListFamily_edgeNeighbors hedges (edges[k]).1).2.2.1
      omega
    rcases incArrAt_exec a_deg (r_base + 3) (r_base + 6)
        (fun x => (edgeNeighborsUpTo edges x k).length)
        (edges[k]).1 sa hne_36 hw hn_w hdeg_u_w hd_len_a hru_a hd_val_a with
      ⟨sb, tb, hexb, htb, ⟨hd_len_b, hd_val_b⟩, harr_b, hreg_b⟩
    have hrv_b : sb.regs (r_base + 4) = (edges[k]).2.1 := by
      rw [hreg_b (r_base + 4) hne_46]; exact hrv_a
    have hne_e : (edges[k]).1 ≠ (edges[k]).2 := hedges.1 k hk
    have hdeg_v_w : (if (edges[k]).2 = (edges[k]).1 then
        (edgeNeighborsUpTo edges (edges[k]).1 k).length + 1
        else (edgeNeighborsUpTo edges (edges[k]).2 k).length) + 1 < 2 ^ w := by
      simp only [hne_e.symm, ↓reduceIte]
      have hlt := length_edgeNeighborsUpTo_lt_of_snd edges hk hne_e
      have hle := (isAdjListFamily_edgeNeighbors hedges (edges[k]).2).2.2.1
      omega
    rcases incArrAt_exec a_deg (r_base + 4) (r_base + 6)
        (fun x => if x = (edges[k]).1 then (edgeNeighborsUpTo edges (edges[k]).1 k).length + 1
          else (edgeNeighborsUpTo edges x k).length)
        (edges[k]).2 sb hne_46 hw hn_w hdeg_v_w hd_len_b hrv_b hd_val_b with
      ⟨sc, tc, hexc, htc, ⟨hd_len_c, hd_val_c⟩, harr_c, hreg_c⟩
    have hrk_c : sc.regs (r_base + 2) = k := by
      rw [hreg_c (r_base + 2) (by simp), hreg_b (r_base + 2) (by simp),
        hreg_a (r_base + 2) (by simp) (by simp) (by simp), hrk_s]
    refine ⟨sc, ta + (tb + tc), .seq hexa (.seq hexb hexc), by dsimp only; omega, ?_, hrk_c⟩
    refine ⟨?_, ?_, ?_, by simp, ⟨by simpa using hd_len_c, ?_⟩⟩
    · simp only [State.setReg_arrs]
      rw [harr_c inArr hne_in_deg, harr_b inArr hne_in_deg, harr_a inArr, hin_s]
    · simp only [State.setReg, Function.update_of_ne (by simp : (r_base : Reg) ≠ r_base + 2)]
      rw [hreg_c r_base (by simp), hreg_b r_base (by simp),
        hreg_a r_base (by simp) (by simp) (by simp), hrn_s]
    · simp only [State.setReg, Function.update_of_ne (by simp : (r_base + 1 : Reg) ≠ r_base + 2)]
      rw [hreg_c (r_base + 1) (by simp), hreg_b (r_base + 1) (by simp),
        hreg_a (r_base + 1) (by simp) (by simp) (by simp), hrm_s]
    · intro x
      simp only [State.setReg_arrs]
      rw [hd_val_c x, length_edgeNeighborsUpTo_succ edges hk hne_e x]
      by_cases hx1 : x = (edges[k]).1
      · subst hx1; simp [hne_e]
      · by_cases hx2 : x = (edges[k]).2
        · subst hx2; simp [hx1]
        · simp [hx1, hx2]

/-- Invariant for the prefix-sum loop of `parseGraphProg`. -/
def ParsePrefixInv {n : ℕ} (edges : List (Fin n × Fin n)) (extra : List ℕ)
    (a_deg a_start a_end : Arr) (r_base : Reg) (idx : ℕ) (s : State) : Prop :=
  s.arrs inArr = [n, edges.length] ++ flatEdges edges ++ extra ∧
  s.regs r_base = n ∧
  s.regs (r_base + 1) = edges.length ∧
  s.regs (r_base + 3) = idx ∧
  s.regs (r_base + 6) = prefixDeg edges idx ∧
  (∃ (hd : (s.arrs a_deg).length = n),
    ∀ x : Fin n, (s.arrs a_deg)[x.1]'(by rw [hd]; exact x.2) =
      (edgeNeighbors edges x).length) ∧
  (∃ (hs : (s.arrs a_start).length = n) (he : (s.arrs a_end).length = n),
    ∀ x : Fin n, x.1 < idx →
      (s.arrs a_start)[x.1]'(by rw [hs]; exact x.2) = prefixDeg edges x.1 ∧
      (s.arrs a_end)[x.1]'(by rw [he]; exact x.2) = prefixDeg edges x.1)

theorem parsePrefixLoop_exec {w n : ℕ} (G : SimpleGraph (Fin n))
    (edges : List (Fin n × Fin n)) (extra : List ℕ)
    (a_deg a_start a_end : ℕ) (r_base : ℕ)
    (hedges : IsSimpleEdgeList G edges)
    (hne_in_st : (inArr : Arr) ≠ a_start) (hne_in_en : (inArr : Arr) ≠ a_end)
    (hne_deg_st : (a_deg : Arr) ≠ a_start) (hne_deg_en : (a_deg : Arr) ≠ a_end)
    (hne_se : (a_start : Arr) ≠ a_end)
    (hw2 : 2 < 2 ^ w) (hn_w : n < 2 ^ w) (hm2_w : 2 + 2 * edges.length < 2 ^ w) :
    ⦃ParsePrefixInv edges extra a_deg a_start a_end r_base 0⦄[w]
      forUp (r_base + 3) (.reg r_base) (parsePrefixBody a_deg a_start a_end r_base)
    ⦃ParsePrefixInv edges extra a_deg a_start a_end r_base n⦄ ≤
      fun _ => 3 + n * (13 + 7) := by
  have hw : 1 < 2 ^ w := by omega
  apply Triple.forUp_const (ParsePrefixInv edges extra a_deg a_start a_end r_base) n 13 hw hn_w
  · intro idx _ s ⟨_, hrn, _, hru, _⟩
    exact ⟨hru, by simp [Expr.eval, checkWord, hrn, hn_w]⟩
  · intro idx hidx s ⟨hin_s, hrn_s, hrm_s, hru_s, hracc_s, ⟨hd_len, hd_val⟩, hs_len, he_len, hprev⟩
    let u_fin : Fin n := ⟨idx, hidx⟩
    have hidx_w : idx < 2 ^ w := by omega
    have hsucc : prefixDeg edges idx + (edgeNeighbors edges u_fin).length =
        prefixDeg edges (idx + 1) := (prefixDeg_succ edges u_fin).symm
    have hpref_le : prefixDeg edges idx + (edgeNeighbors edges u_fin).length ≤ 2 * edges.length := by
      rw [hsucc, ← prefixDeg_self edges hedges.1]
      exact prefixDeg_mono edges hidx
    have hpref_w : prefixDeg edges idx < 2 ^ w := by omega
    have hpref1_w : prefixDeg edges (idx + 1) < 2 ^ w := by omega
    have hdeg_w : (edgeNeighbors edges u_fin).length < 2 ^ w := by omega
    have heval_u₀ : (Expr.reg (r_base + 3)).eval w s = some idx := by
      simp [Expr.eval, checkWord, hru_s, hidx_w]
    have heval_acc₀ : (Expr.reg (r_base + 6)).eval w s = some (prefixDeg edges idx) := by
      simp [Expr.eval, checkWord, hracc_s, hpref_w]
    let sa := s.writeArr a_start idx (prefixDeg edges idx)
    have hexa : Exec w (.write a_start (.reg (r_base + 3)) (.reg (r_base + 6))) s sa 3 :=
      .write heval_u₀ heval_acc₀ (by rw [hs_len]; exact hidx)
    have heval_u₁ : (Expr.reg (r_base + 3)).eval w sa = some idx := by
      simp [sa, Expr.eval, checkWord, hru_s, hidx_w]
    have heval_acc₁ : (Expr.reg (r_base + 6)).eval w sa = some (prefixDeg edges idx) := by
      simp [sa, Expr.eval, checkWord, hracc_s, hpref_w]
    let sb := sa.writeArr a_end idx (prefixDeg edges idx)
    have hexb : Exec w (.write a_end (.reg (r_base + 3)) (.reg (r_base + 6))) sa sb 3 :=
      .write heval_u₁ heval_acc₁ (by simp [sa, hne_se.symm, he_len, hidx])
    have heval_deg : (Expr.read a_deg (.reg (r_base + 3))).eval w sb =
        some (edgeNeighbors edges u_fin).length := by
      have hlen_b : idx < (sb.arrs a_deg).length := by
        simp [sb, sa, hne_deg_st, hne_deg_en, hd_len, hidx]
      have hval_b : (sb.arrs a_deg)[idx]'hlen_b = (edgeNeighbors edges u_fin).length := by
        simpa [sb, sa, hne_deg_st, hne_deg_en] using hd_val u_fin
      have hru_b : sb.regs (r_base + 3) = idx := by simp [sb, sa, hru_s]
      simp only [Expr.eval, checkWord, hru_b, hidx_w, ↓reduceIte, hlen_b, ↓reduceDIte, hval_b,
        hdeg_w]
    let sc := sb.setReg (r_base + 4) (edgeNeighbors edges u_fin).length
    have hexc : Exec w (.assign (r_base + 4) (.read a_deg (.reg (r_base + 3)))) sb sc 3 :=
      .assign heval_deg
    have heval_sum : (Expr.op .add (.reg (r_base + 6)) (.reg (r_base + 4))).eval w sc =
        some (prefixDeg edges (idx + 1)) := by
      have hr6_c : sc.regs (r_base + 6) = prefixDeg edges idx := by simp [sc, sb, sa, hracc_s]
      have hr4_c : sc.regs (r_base + 4) = (edgeNeighbors edges u_fin).length := by simp [sc]
      simp only [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hr6_c, hr4_c, hpref_w, hdeg_w,
        ↓reduceIte, hsucc, hpref1_w]
    let sd := sc.setReg (r_base + 6) (prefixDeg edges (idx + 1))
    have hexd : Exec w (.assign (r_base + 6) (.op .add (.reg (r_base + 6)) (.reg (r_base + 4))))
        sc sd 4 := .assign heval_sum
    refine ⟨sd, 3 + (3 + (3 + 4)), .seq hexa (.seq hexb (.seq hexc hexd)), by dsimp only; omega, ?_,
      by simp [sd, sc, sb, sa, hru_s]⟩
    refine ⟨by simp [sd, sc, sb, sa, hne_in_st, hne_in_en, hin_s],
      by simp [sd, sc, sb, sa, hrn_s],
      by simp [sd, sc, sb, sa, hrm_s],
      by simp,
      by simp [sd],
      ⟨by simp [sd, sc, sb, sa, hne_deg_st, hne_deg_en, hd_len],
        fun x => by simpa [sd, sc, sb, sa, hne_deg_st, hne_deg_en] using hd_val x⟩,
      ⟨by simp [sd, sc, sb, sa, hne_se, hs_len],
        by simp [sd, sc, sb, sa, he_len],
        fun x hx => ?_⟩⟩
    simp only [sd, sc, sb, sa, State.setReg_arrs, State.writeArr_arrs_self,
      State.writeArr_arrs_ne _ _ _ hne_se, State.writeArr_arrs_ne _ _ _ hne_se.symm]
    rcases Nat.lt_succ_iff_lt_or_eq.mp hx with hlt | heq
    · have hne_idx : idx ≠ x.1 := by omega
      rw [List.getElem_set_ne hne_idx, List.getElem_set_ne hne_idx]
      exact hprev x hlt
    · subst heq
      exact ⟨List.getElem_set_self (by rw [List.length_set, hs_len]; exact x.2),
        List.getElem_set_self (by rw [List.length_set, he_len]; exact x.2)⟩

/-- Invariant for Pass 2 of `parseGraphProg`. -/
def ParsePass2Inv {n : ℕ} (edges : List (Fin n × Fin n)) (extra : List ℕ)
    (a_deg a_start a_end a_entries : Arr) (r_base : Reg) (k : ℕ) (s : State) : Prop :=
  s.arrs inArr = [n, edges.length] ++ flatEdges edges ++ extra ∧
  s.regs r_base = n ∧
  s.regs (r_base + 1) = edges.length ∧
  s.regs (r_base + 2) = k ∧
  (s.arrs a_start).length = n ∧
  (s.arrs a_end).length = n ∧
  (s.arrs a_entries).length = 2 * edges.length ∧
  (∃ (hd : (s.arrs a_deg).length = n),
    ∀ x : Fin n, (s.arrs a_deg)[x.1]'(by rw [hd]; exact x.2) =
      (edgeNeighbors edges x).length) ∧
  (∀ x : Fin n,
    IsListAt a_start a_end a_entries x.1 (prefixDeg edges x.1)
      (prefixDeg edges x.1 + (edgeNeighborsUpTo edges x k).length)
      (edgeNeighborsUpTo edges x k) s)

theorem parsePass2Loop_exec {w n : ℕ} (G : SimpleGraph (Fin n))
    (edges : List (Fin n × Fin n)) (extra : List ℕ)
    (a_deg a_start a_end a_entries : ℕ) (r_base : ℕ)
    (hedges : IsSimpleEdgeList G edges)
    (hne_in_en : (inArr : Arr) ≠ a_end) (hne_in_ent : (inArr : Arr) ≠ a_entries)
    (hne_deg_en : (a_deg : Arr) ≠ a_end) (hne_deg_ent : (a_deg : Arr) ≠ a_entries)
    (hne_se : a_start ≠ a_end) (hne_sent : a_start ≠ a_entries) (hne_eent : a_end ≠ a_entries)
    (hw2 : 2 < 2 ^ w) (hn_w : n < 2 ^ w) (hm2_w : 2 + 2 * edges.length < 2 ^ w) :
    ⦃ParsePass2Inv edges extra a_deg a_start a_end a_entries r_base 0⦄[w]
      forUp (r_base + 2) (.reg (r_base + 1)) (parsePass2Body a_end a_entries r_base)
    ⦃ParsePass2Inv edges extra a_deg a_start a_end a_entries r_base edges.length⦄ ≤
      fun _ => 3 + edges.length * (40 + 7) := by
  have hw : 1 < 2 ^ w := by omega
  have hm_w : edges.length < 2 ^ w := by omega
  have h2m_w : 2 * edges.length < 2 ^ w := by omega
  have hne_34 : (r_base + 3 : Reg) ≠ r_base + 4 := by omega
  have hne_35 : (r_base + 3 : Reg) ≠ r_base + 5 := by omega
  have hne_36 : r_base + 3 ≠ r_base + 6 := by omega
  have hne_46 : r_base + 4 ≠ r_base + 6 := by omega
  have hne_se' : (a_start : Arr) ≠ a_end := by omega
  have hne_sent' : (a_start : Arr) ≠ a_entries := by omega
  apply Triple.forUp_const (ParsePass2Inv edges extra a_deg a_start a_end a_entries r_base)
      edges.length 40 hw hm_w
  · intro k _ s ⟨_, _, hrm, hrk, _⟩
    exact ⟨hrk, by simp [Expr.eval, checkWord, hrm, hm_w]⟩
  · intro k hk s ⟨hin_s, hrn_s, hrm_s, hrk_s, hst_len, hen_len, hent_len, ⟨hd_len, hd_val⟩, hlists_s⟩
    rcases readEdgeEndpoints_exec edges extra (r_base + 2) (r_base + 3) (r_base + 4) (r_base + 5)
        k s hne_35 hne_34 hw2 hn_w hm2_w hk hin_s hrk_s with
      ⟨sa, ta, hexa, hta, hru_a, hrv_a, harr_a, hreg_a⟩
    have hlists_a : ∀ x : Fin n,
        IsListAt a_start a_end a_entries x.1 (prefixDeg edges x.1)
          (prefixDeg edges x.1 + (edgeNeighborsUpTo edges x k).length)
          (edgeNeighborsUpTo edges x k) sa :=
      fun x => (hlists_s x).of_arrs_eq (harr_a a_start) (harr_a a_end) (harr_a a_entries)
    have hent_a : (sa.arrs a_entries).length = 2 * edges.length := by
      rw [harr_a]; exact hent_len
    have hcur_le : ∀ x : Fin n,
        (edgeNeighborsUpTo edges x k).length ≤ (edgeNeighbors edges x).length :=
      fun x => length_edgeNeighborsUpTo_le_edgeNeighbors edges x (Nat.le_of_lt hk)
    have hcur_u : (edgeNeighborsUpTo edges (edges[k]).1 k).length <
        (edgeNeighbors edges (edges[k]).1).length :=
      length_edgeNeighborsUpTo_lt_of_fst edges hk
    have hv_w : (edges[k]).2.1 < 2 ^ w := by have := (edges[k]).2.2; omega
    have hu_w : (edges[k]).1.1 < 2 ^ w := by have := (edges[k]).1.2; omega
    rcases csrAppend_exec edges a_start a_end a_entries (r_base + 3) (r_base + 6) (.reg (r_base + 4))
        (fun x => edgeNeighborsUpTo edges x k) (edges[k]).1 (edges[k]).2.1 sa
        hne_se hne_sent hne_eent hne_36 hw hn_w h2m_w hedges.1 hent_a hcur_le hcur_u
        hlists_a hru_a
        (fun s' hreg _ => by
          simp [Expr.eval, checkWord, hreg (r_base + 4) (by simp), hrv_a, hv_w]) with
      ⟨sb, tb, hexb, htb, hen_b, hent_b, hlists_b, harr_b, hreg_b⟩
    dsimp [Expr.cost] at htb
    have hne_e : (edges[k]).1 ≠ (edges[k]).2 := hedges.1 k hk
    let cur_b (x : Fin n) : List ℕ :=
      if x = (edges[k]).1 then edgeNeighborsUpTo edges (edges[k]).1 k ++ [(edges[k]).2.1]
      else edgeNeighborsUpTo edges x k
    have hcur_b_le : ∀ x : Fin n, (cur_b x).length ≤ (edgeNeighbors edges x).length := by
      intro x
      dsimp [cur_b]
      split_ifs with hx
      · subst hx
        rw [List.length_append, List.length_singleton]
        exact hcur_u
      · exact hcur_le x
    have hcur_b_v : (cur_b (edges[k]).2).length < (edgeNeighbors edges (edges[k]).2).length := by
      dsimp [cur_b]
      simp only [hne_e.symm, ↓reduceIte]
      exact length_edgeNeighborsUpTo_lt_of_snd edges hk hne_e
    have hrv_b : sb.regs (r_base + 4) = (edges[k]).2.1 := by
      rw [hreg_b (r_base + 4) (by simp)]; exact hrv_a
    have hru_b : sb.regs (r_base + 3) = (edges[k]).1.1 := by
      rw [hreg_b (r_base + 3) (by simp)]; exact hru_a
    rcases csrAppend_exec edges a_start a_end a_entries (r_base + 4) (r_base + 6) (.reg (r_base + 3))
        cur_b (edges[k]).2 (edges[k]).1.1 sb
        hne_se hne_sent hne_eent hne_46 hw hn_w h2m_w hedges.1 hent_b hcur_b_le hcur_b_v
        hlists_b hrv_b
        (fun s' hreg _ => by
          simp [Expr.eval, checkWord, hreg (r_base + 3) (by simp), hru_b, hu_w]) with
      ⟨sc, tc, hexc, htc, hen_c, hent_c, hlists_c, harr_c, hreg_c⟩
    dsimp [Expr.cost] at htc
    have hrk_c : sc.regs (r_base + 2) = k := by
      rw [hreg_c (r_base + 2) (by simp), hreg_b (r_base + 2) (by simp),
        hreg_a (r_base + 2) (by simp) (by simp) (by simp), hrk_s]
    refine ⟨sc, ta + (tb + tc), .seq hexa (.seq hexb hexc), by dsimp only; omega, ?_, hrk_c⟩
    have hin_c : sc.arrs inArr = [n, edges.length] ++ flatEdges edges ++ extra := by
      rw [harr_c inArr hne_in_en hne_in_ent, harr_b inArr hne_in_en hne_in_ent,
        harr_a inArr, hin_s]
    have hdeg_arr_c : sc.arrs a_deg = s.arrs a_deg := by
      rw [harr_c a_deg hne_deg_en hne_deg_ent, harr_b a_deg hne_deg_en hne_deg_ent,
        harr_a a_deg]
    have hst_arr_c : sc.arrs a_start = s.arrs a_start := by
      rw [harr_c a_start hne_se' hne_sent', harr_b a_start hne_se' hne_sent',
        harr_a a_start]
    have hen_len_c : (sc.arrs a_end).length = n := by
      rw [hen_c, hen_b, harr_a a_end, hen_len]
    refine ⟨by simpa using hin_c,
      by
        simp only [State.setReg, Function.update_of_ne (by simp : (r_base : Reg) ≠ r_base + 2)]
        rw [hreg_c r_base (by simp), hreg_b r_base (by simp),
          hreg_a r_base (by simp) (by simp) (by simp), hrn_s],
      by
        simp only [State.setReg, Function.update_of_ne (by simp : (r_base + 1 : Reg) ≠ r_base + 2)]
        rw [hreg_c (r_base + 1) (by simp), hreg_b (r_base + 1) (by simp),
          hreg_a (r_base + 1) (by simp) (by simp) (by simp), hrm_s],
      by simp,
      by simpa [hst_arr_c] using hst_len,
      by simpa using hen_len_c,
      by simpa using hent_c,
      ⟨by simpa [hdeg_arr_c] using hd_len,
        fun x => by simpa [hdeg_arr_c] using hd_val x⟩,
      fun x => ?_⟩
    have hlist_x := (hlists_c x).of_arrs_eq rfl rfl rfl (s' := sc.setReg (r_base + 2) (k + 1))
    have heq_next :
        (if x = (edges[k]).2 then cur_b (edges[k]).2 ++ [(edges[k]).1.1] else cur_b x) =
          edgeNeighborsUpTo edges x (k + 1) := by
      dsimp [cur_b]
      by_cases hx1 : x = (edges[k]).1
      · subst hx1
        simp only [hne_e, ↓reduceIte]
        exact (edgeNeighborsUpTo_succ_fst edges hk).symm
      · by_cases hx2 : x = (edges[k]).2
        · subst hx2
          simp only [↓reduceIte, hne_e.symm]
          exact (edgeNeighborsUpTo_succ_snd edges hk hne_e).symm
        · simp only [hx1, hx2, ↓reduceIte]
          exact (edgeNeighborsUpTo_succ_other edges hk hx1 hx2).symm
    simpa only [heq_next] using hlist_x

/-- Two-pass `O(n + m)` CSR adjacency-list builder from `inArr`.
Uses scratch registers `r_base .. r_base + 6`:
- `r_base`: `n := inArr[0]`
- `r_base + 1`: `m := inArr[1]`
- `r_base + 2`: edge loop index `k`
- `r_base + 3`: vertex `u` / prefix-sum loop index
- `r_base + 4`: vertex `v` / degree scratch
- `r_base + 5`: flat edge array index `2 + 2 * k`
- `r_base + 6`: accumulator / prefix sum / CSR append scratch -/
def parseGraphProg (a_deg a_start a_end a_entries : Arr) (r_base : Reg) : Cmd :=
  .seq (.assign r_base (.read inArr (.const 0)))
    (.seq (.assign (r_base + 1) (.read inArr (.const 1)))
      (.seq (.alloc a_deg (.reg r_base))
        (.seq (.assign (r_base + 2) (.const 0))
          (.seq (forUp (r_base + 2) (.reg (r_base + 1)) (parsePass1Body a_deg r_base))
            (.seq (.alloc a_start (.reg r_base))
              (.seq (.alloc a_end (.reg r_base))
                (.seq (.assign (r_base + 6) (.const 0))
                  (.seq (.assign (r_base + 3) (.const 0))
                    (.seq (forUp (r_base + 3) (.reg r_base) (parsePrefixBody a_deg a_start a_end r_base))
                      (.seq (.alloc a_entries (.reg (r_base + 6)))
                        (.seq (.assign (r_base + 2) (.const 0))
                          (forUp (r_base + 2) (.reg (r_base + 1))
                            (parsePass2Body a_end a_entries r_base)))))))))))))

/-- Specification for `parseGraphProg`: given any state `s` where `s.arrs inArr` begins with
`[n, edges.length] ++ flatEdges edges` for a simple edge list `edges` of `G : SimpleGraph (Fin n)`,
`parseGraphProg` runs in at most `23 * n + 88 * edges.length + 27` steps and builds
`IsAdjList G a_start a_end a_entries (edgeNeighbors edges) s'` with
`(s'.arrs a_entries).length = 2 * edges.length`, `s'.regs r_base = n`, and
`s'.regs (r_base + 1) = edges.length`. -/
theorem Triple.parseGraphProg_spec {w n : ℕ} (G : SimpleGraph (Fin n))
    (edges : List (Fin n × Fin n)) (extra : List ℕ)
    (a_deg a_start a_end a_entries : ℕ) (r_base : ℕ)
    (hedges : IsSimpleEdgeList G edges)
    (hne_in_deg : (inArr : Arr) ≠ a_deg)
    (hne_in_st : (inArr : Arr) ≠ a_start)
    (hne_in_en : (inArr : Arr) ≠ a_end)
    (hne_in_ent : (inArr : Arr) ≠ a_entries)
    (hne_deg_st : a_deg ≠ a_start) (hne_deg_en : a_deg ≠ a_end) (hne_deg_ent : a_deg ≠ a_entries)
    (hne_se : a_start ≠ a_end) (hne_sent : a_start ≠ a_entries) (hne_eent : a_end ≠ a_entries)
    (hw2 : 2 < 2 ^ w) (hn_w : n < 2 ^ w) (hm2_w : 2 + 2 * edges.length < 2 ^ w) :
    ⦃fun s => s.arrs inArr = [n, edges.length] ++ flatEdges edges ++ extra⦄[w]
      parseGraphProg a_deg a_start a_end a_entries r_base
    ⦃fun s' =>
      s'.arrs inArr = [n, edges.length] ++ flatEdges edges ++ extra ∧
      s'.regs r_base = n ∧
      s'.regs (r_base + 1) = edges.length ∧
      IsAdjList G a_start a_end a_entries (edgeNeighbors edges) s' ∧
      (s'.arrs a_entries).length = 2 * edges.length ∧
      (∃ (hd : (s'.arrs a_deg).length = n),
        ∀ x : Fin n, (s'.arrs a_deg)[x.1]'(by rw [hd]; exact x.2) =
          (edgeNeighbors edges x).length)⦄ ≤
      fun _ => 23 * n + 88 * edges.length + 27 := by
  have hw : 1 < 2 ^ w := by omega
  have h0_w : 0 < 2 ^ w := by omega
  have hm_w : edges.length < 2 ^ w := by omega
  have h2m_w : 2 * edges.length < 2 ^ w := by omega
  have hne_deg_st' : (a_deg : Arr) ≠ a_start := by omega
  have hne_deg_en' : (a_deg : Arr) ≠ a_end := by omega
  have hne_deg_ent' : (a_deg : Arr) ≠ a_entries := by omega
  have hne_se' : (a_start : Arr) ≠ a_end := by omega
  have hne_sent' : (a_start : Arr) ≠ a_entries := by omega
  have hne_eent' : (a_end : Arr) ≠ a_entries := by omega
  intro s₀ hs₀
  -- Step 1: r_base := inArr[0]
  obtain ⟨h0_len, h0_val⟩ := inArr_getElem_zero edges extra hs₀
  have heval_n : (Expr.read inArr (.const 0)).eval w s₀ = some n := by
    simp [Expr.eval, checkWord, h0_w, h0_len, h0_val, hn_w]
  let s₁ := s₀.setReg r_base n
  have hex₁ : Exec w (.assign r_base (.read inArr (.const 0))) s₀ s₁ 3 := .assign heval_n
  -- Step 2: r_base + 1 := inArr[1]
  obtain ⟨h1_len, h1_val⟩ := inArr_getElem_one edges extra hs₀
  have heval_m : (Expr.read inArr (.const 1)).eval w s₁ = some edges.length := by
    simp [s₁, Expr.eval, checkWord, hw, h1_len, h1_val, hm_w]
  let s₂ := s₁.setReg (r_base + 1) edges.length
  have hex₂ : Exec w (.assign (r_base + 1) (.read inArr (.const 1))) s₁ s₂ 3 := .assign heval_m
  -- Step 3: alloc a_deg (.reg r_base)
  have heval_rn₂ : (Expr.reg r_base).eval w s₂ = some n := by
    simp [s₂, s₁, Expr.eval, checkWord, hn_w]
  let s₃ := s₂.setArr a_deg (List.replicate n 0)
  have hex₃ : Exec w (.alloc a_deg (.reg r_base)) s₂ s₃ (1 + n) := .alloc heval_rn₂
  -- Step 4: r_base + 2 := 0
  have heval_0₃ : (Expr.const 0).eval w s₃ = some 0 := by simp [checkWord, h0_w]
  let s₄ := s₃.setReg (r_base + 2) 0
  have hex₄ : Exec w (.assign (r_base + 2) (.const 0)) s₃ s₄ 2 := .assign heval_0₃
  -- Step 5: Pass 1 loop
  have hPass1₀ : ParsePass1Inv edges extra a_deg r_base 0 s₄ := by
    refine ⟨by simp [s₄, s₃, s₂, s₁, hne_in_deg, hs₀],
      by simp [s₄, s₃, s₂, s₁],
      by simp [s₄, s₃, s₂],
      by simp [s₄],
      ⟨by simp [s₄, s₃], fun x => by simp [s₄, s₃, edgeNeighborsUpTo]⟩⟩
  rcases parsePass1Loop_exec G edges extra a_deg r_base hedges hne_in_deg hw2 hn_w hm2_w s₄ hPass1₀ with
    ⟨s₅, t₅, hex₅, ht₅, hin₅, hrn₅, hrm₅, _, hd_len₅, hd_val₅⟩
  dsimp only at ht₅
  -- Step 6: alloc a_start, alloc a_end, r_acc := 0, r_u := 0
  have heval_rn₅ : (Expr.reg r_base).eval w s₅ = some n := by
    simp [Expr.eval, checkWord, hrn₅, hn_w]
  let s₆ := s₅.setArr a_start (List.replicate n 0)
  have hex₆ : Exec w (.alloc a_start (.reg r_base)) s₅ s₆ (1 + n) := .alloc heval_rn₅
  have heval_rn₆ : (Expr.reg r_base).eval w s₆ = some n := by
    simp [s₆, Expr.eval, checkWord, hrn₅, hn_w]
  let s₇ := s₆.setArr a_end (List.replicate n 0)
  have hex₇ : Exec w (.alloc a_end (.reg r_base)) s₆ s₇ (1 + n) := .alloc heval_rn₆
  have heval_0₇ : (Expr.const 0).eval w s₇ = some 0 := by simp [checkWord, h0_w]
  let s₈ := s₇.setReg (r_base + 6) 0
  have hex₈ : Exec w (.assign (r_base + 6) (.const 0)) s₇ s₈ 2 := .assign heval_0₇
  have heval_0₈ : (Expr.const 0).eval w s₈ = some 0 := by simp [checkWord, h0_w]
  let s₉ := s₈.setReg (r_base + 3) 0
  have hex₉ : Exec w (.assign (r_base + 3) (.const 0)) s₈ s₉ 2 := .assign heval_0₈
  -- Step 7: Prefix sum loop
  have hPrefix₀ : ParsePrefixInv edges extra a_deg a_start a_end r_base 0 s₉ := by
    refine ⟨by simp [s₉, s₈, s₇, s₆, hne_in_st, hne_in_en, hin₅],
      by simp [s₉, s₈, s₇, s₆, hrn₅],
      by simp [s₉, s₈, s₇, s₆, hrm₅],
      by simp [s₉],
      by simp [s₉, s₈],
      ⟨by simp [s₉, s₈, s₇, s₆, hne_deg_st', hne_deg_en', hd_len₅],
        fun x => by simpa [s₉, s₈, s₇, s₆, hne_deg_st', hne_deg_en', edgeNeighbors] using hd_val₅ x⟩,
      ⟨by simp [s₉, s₈, s₇, s₆, hne_se'], by simp [s₉, s₈, s₇], fun x hx => by omega⟩⟩
  rcases parsePrefixLoop_exec G edges extra a_deg a_start a_end r_base hedges
      hne_in_st hne_in_en hne_deg_st' hne_deg_en' hne_se' hw2 hn_w hm2_w s₉ hPrefix₀ with
    ⟨s₁₀, t₁₀, hex₁₀, ht₁₀, hin₁₀, hrn₁₀, hrm₁₀, _, hracc₁₀, ⟨hd_len₁₀, hd_val₁₀⟩,
      hs_len₁₀, he_len₁₀, hpref₁₀⟩
  dsimp only at ht₁₀
  -- Step 8: alloc a_entries, r_k := 0
  have hpref_n : prefixDeg edges n = 2 * edges.length := prefixDeg_self edges hedges.1
  have heval_acc₁₀ : (Expr.reg (r_base + 6)).eval w s₁₀ = some (2 * edges.length) := by
    simp [Expr.eval, checkWord, hracc₁₀, hpref_n, h2m_w]
  let s₁₁ := s₁₀.setArr a_entries (List.replicate (2 * edges.length) 0)
  have hex₁₁ : Exec w (.alloc a_entries (.reg (r_base + 6))) s₁₀ s₁₁ (1 + 2 * edges.length) :=
    .alloc heval_acc₁₀
  have heval_0₁₁ : (Expr.const 0).eval w s₁₁ = some 0 := by simp [checkWord, h0_w]
  let s₁₂ := s₁₁.setReg (r_base + 2) 0
  have hex₁₂ : Exec w (.assign (r_base + 2) (.const 0)) s₁₁ s₁₂ 2 := .assign heval_0₁₁
  -- Step 9: Pass 2 loop
  have hPass2₀ : ParsePass2Inv edges extra a_deg a_start a_end a_entries r_base 0 s₁₂ := by
    refine ⟨by simp [s₁₂, s₁₁, hne_in_ent, hin₁₀],
      by simp [s₁₂, s₁₁, hrn₁₀],
      by simp [s₁₂, s₁₁, hrm₁₀],
      by simp [s₁₂],
      by simp [s₁₂, s₁₁, hne_sent', hs_len₁₀],
      by simp [s₁₂, s₁₁, hne_eent', he_len₁₀],
      by simp [s₁₂, s₁₁],
      ⟨by simp [s₁₂, s₁₁, hne_deg_ent', hd_len₁₀],
        fun x => by simpa [s₁₂, s₁₁, hne_deg_ent'] using hd_val₁₀ x⟩,
      fun x => ?_⟩
    obtain ⟨hst_x, hen_x⟩ := hpref₁₀ x x.2
    have hle_x : prefixDeg edges x.1 ≤ 2 * edges.length := by
      rw [← hpref_n]
      exact prefixDeg_mono edges (Nat.le_of_lt x.2)
    refine ⟨by simp [s₁₂, s₁₁, hne_sent', hs_len₁₀, x.2],
      by simp [s₁₂, s₁₁, hne_eent', he_len₁₀, x.2],
      by simp [s₁₂, s₁₁, edgeNeighborsUpTo, hle_x],
      by simp [edgeNeighborsUpTo],
      by simpa [s₁₂, s₁₁, hne_sent'] using hst_x,
      by simpa [s₁₂, s₁₁, hne_eent', edgeNeighborsUpTo] using hen_x,
      by simp [edgeNeighborsUpTo],
      fun j hj => by simp [edgeNeighborsUpTo] at hj⟩
  rcases parsePass2Loop_exec G edges extra a_deg a_start a_end a_entries r_base hedges
      hne_in_en hne_in_ent hne_deg_en' hne_deg_ent' hne_se hne_sent hne_eent hw2 hn_w hm2_w s₁₂ hPass2₀ with
    ⟨s₁₃, t₁₃, hex₁₃, ht₁₃, hin₁₃, hrn₁₃, hrm₁₃, _, hs_len₁₃, he_len₁₃, hent₁₃, hdeg₁₃, hlists₁₃⟩
  dsimp only at ht₁₃
  refine ⟨s₁₃, _,
    .seq hex₁ (.seq hex₂ (.seq hex₃ (.seq hex₄ (.seq hex₅
      (.seq hex₆ (.seq hex₇ (.seq hex₈ (.seq hex₉ (.seq hex₁₀
        (.seq hex₁₁ (.seq hex₁₂ hex₁₃))))))))))),
    by dsimp only; omega,
    hin₁₃, hrn₁₃, hrm₁₃, ?_, hent₁₃, hdeg₁₃⟩
  refine ⟨⟨hs_len₁₃, he_len₁₃, fun u => ?_⟩, isAdjListFamily_edgeNeighbors hedges⟩
  exact ⟨prefixDeg edges u.1, prefixDeg edges u.1 + (edgeNeighbors edges u).length, hlists₁₃ u⟩

/-! ### Register-Parameterized BFS and End-to-End `bfs_computesInTime` -/

/-- Register-parameterized BFS: given `n` in `r_n` and `s₀` in `r_s0`, allocates `a_vis` of length
`n`, initializes queue `(a_q, r_head, r_tail)` of capacity `n`, marks `s₀` visited, pushes `s₀`,
and runs `bfsLoopProg`. No problem-instance constants (`n` or `s₀`) are hardcoded in the AST. -/
def bfsRegProg (r_n r_s0 : Reg) (a_start a_end a_entries a_vis a_q : Arr)
    (r_head r_tail r_u r_k r_hi r_v r_vis : Reg) : Cmd :=
  .seq (.alloc a_vis (.reg r_n))
    (.seq (queueInit a_q r_head r_tail (.reg r_n))
      (.seq (.write a_vis (.reg r_s0) (.const 1))
        (.seq (queuePush a_q r_tail (.reg r_s0))
          (bfsLoopProg a_start a_end a_entries a_vis a_q
            r_head r_tail r_u r_k r_hi r_v r_vis (.const 1)))))

/-- Specification for `bfsRegProg`: starting from a state where `s.regs r_n = n`,
`s.regs r_s0 = s₀.1`, and `(a_start, a_end, a_entries)` stores `lists` for `G`, computes the
`0`/`1` reachability indicator list `List.ofFn (fun v : Fin n => if G.Reachable s₀ v then 1 else 0)`
in `a_vis` in at most `23 * n + 26 * totalAdjEntries lists + 26` steps. -/
theorem Triple.bfsRegProg_spec {w n : ℕ} (G : SimpleGraph (Fin n)) (lists : Fin n → List ℕ)
    (s₀ : Fin n) (r_n r_s0 : ℕ) (a_start a_end a_entries a_vis a_q : ℕ)
    (r_head r_tail r_u r_k r_hi r_v r_vis : ℕ)
    (hne_sv : a_start ≠ a_vis) (hne_ev : a_end ≠ a_vis) (hne_entv : a_entries ≠ a_vis)
    (hne_sq : a_start ≠ a_q) (hne_eq : a_end ≠ a_q) (hne_entq : a_entries ≠ a_q)
    (hne_vq : a_vis ≠ a_q)
    (hne_s0h : r_s0 ≠ r_head) (hne_s0t : r_s0 ≠ r_tail)
    (hne_ht : r_head ≠ r_tail) (hne_hu : r_head ≠ r_u) (hne_hk : r_head ≠ r_k)
    (hne_hhi : r_head ≠ r_hi) (hne_hv : r_head ≠ r_v) (hne_hvis : r_head ≠ r_vis)
    (hne_tu : r_tail ≠ r_u) (hne_tk : r_tail ≠ r_k) (hne_thi : r_tail ≠ r_hi)
    (hne_tv : r_tail ≠ r_v) (hne_tvis : r_tail ≠ r_vis)
    (hne_uk : r_u ≠ r_k) (hne_uhi : r_u ≠ r_hi) (hne_uv : r_u ≠ r_v) (hne_uvis : r_u ≠ r_vis)
    (hne_khi : r_k ≠ r_hi) (hne_kv : r_k ≠ r_v) (hne_kvis : r_k ≠ r_vis)
    (hne_hiv : r_hi ≠ r_v) (hne_hivis : r_hi ≠ r_vis) (hne_vvis : r_v ≠ r_vis)
    (hw : 1 < 2 ^ w) (hn_w : n < 2 ^ w) :
    ⦃fun s =>
      s.regs r_n = n ∧
      s.regs r_s0 = s₀.1 ∧
      IsAdjList G a_start a_end a_entries lists s ∧
      (s.arrs a_entries).length < 2 ^ w⦄[w]
      bfsRegProg r_n r_s0 a_start a_end a_entries a_vis a_q
        r_head r_tail r_u r_k r_hi r_v r_vis
    ⦃fun s' =>
      s'.arrs a_vis =
        (open Classical in List.ofFn (fun v : Fin n => if G.Reachable s₀ v then 1 else 0))⦄ ≤
      fun _ => 23 * n + 26 * totalAdjEntries lists + 26 := by
  have h0_w : 0 < 2 ^ w := by omega
  have hs₀_w : s₀.1 < 2 ^ w := by omega
  have hne_sv' : (a_start : Arr) ≠ a_vis := by omega
  have hne_ev' : (a_end : Arr) ≠ a_vis := by omega
  have hne_entv' : (a_entries : Arr) ≠ a_vis := by omega
  have hne_sq' : (a_start : Arr) ≠ a_q := by omega
  have hne_eq' : (a_end : Arr) ≠ a_q := by omega
  have hne_entq' : (a_entries : Arr) ≠ a_q := by omega
  have hne_vq' : (a_vis : Arr) ≠ a_q := by omega
  have hne_ht' : (r_head : Reg) ≠ r_tail := by omega
  have hne_s0h' : (r_s0 : Reg) ≠ r_head := by omega
  have hne_s0t' : (r_s0 : Reg) ≠ r_tail := by omega
  intro st₀ ⟨hrn₀, hrs0₀, hadj₀, hent₀⟩
  -- 1. alloc a_vis (.reg r_n)
  have heval_rn₀ : (Expr.reg r_n).eval w st₀ = some n := by
    simp [Expr.eval, checkWord, hrn₀, hn_w]
  let st₁ := st₀.setArr a_vis (List.replicate n 0)
  have hex₁ : Exec w (.alloc a_vis (.reg r_n)) st₀ st₁ (1 + n) := .alloc heval_rn₀
  -- 2. queueInit a_q r_head r_tail (.reg r_n)
  have heval_rn₁ : (Expr.reg r_n).eval w st₁ = some n := by
    simp [st₁, Expr.eval, checkWord, hrn₀, hn_w]
  let st₂a := st₁.setArr a_q (List.replicate n 0)
  have hex₂a : Exec w (.alloc a_q (.reg r_n)) st₁ st₂a (1 + n) := .alloc heval_rn₁
  have heval_0_2a : (Expr.const 0).eval w st₂a = some 0 := by simp [checkWord, h0_w]
  let st₂b := st₂a.setReg r_head 0
  have hex₂b : Exec w (.assign r_head (.const 0)) st₂a st₂b 2 := .assign heval_0_2a
  have heval_0_2b : (Expr.const 0).eval w st₂b = some 0 := by simp [checkWord, h0_w]
  let st₂ := st₂b.setReg r_tail 0
  have hex₂c : Exec w (.assign r_tail (.const 0)) st₂b st₂ 2 := .assign heval_0_2b
  have hex₂ : Exec w (queueInit a_q r_head r_tail (.reg r_n)) st₁ st₂ ((1 + n) + (2 + 2)) :=
    .seq hex₂a (.seq hex₂b hex₂c)
  have hq₂ : IsQueueHistory a_q r_head r_tail n [] 0 st₂ :=
    ⟨by simp [st₂, st₂b, st₂a], Nat.zero_le n, by simp [st₂, st₂b, hne_ht'], by simp [st₂],
      le_rfl, fun i hi => by simp at hi⟩
  have hadj₂ : IsAdjList G a_start a_end a_entries lists st₂ :=
    hadj₀.of_arrs_eq
      (by simp [st₂, st₂b, st₂a, st₁, hne_sq', hne_sv'])
      (by simp [st₂, st₂b, st₂a, st₁, hne_eq', hne_ev'])
      (by simp [st₂, st₂b, st₂a, st₁, hne_entq', hne_entv'])
  have hent₂ : (st₂.arrs a_entries).length < 2 ^ w := by
    simpa [st₂, st₂b, st₂a, st₁, hne_entq', hne_entv'] using hent₀
  have harr_vis₂ : st₂.arrs a_vis = List.replicate n 0 := by
    simp [st₂, st₂b, st₂a, st₁, hne_vq']
  have hrs0₂ : st₂.regs r_s0 = s₀.1 := by
    simp [st₂, st₂b, st₂a, st₁, hne_s0t', hne_s0h', hrs0₀]
  -- 3. .write a_vis (.reg r_s0) (.const 1)
  have heval_s₀ : (Expr.reg r_s0).eval w st₂ = some s₀.1 := by
    simp [Expr.eval, checkWord, hrs0₂, hs₀_w]
  have heval_1 : (Expr.const 1).eval w st₂ = some 1 := by simp [checkWord, hw]
  let st₃ := st₂.writeArr a_vis s₀.1 1
  have hex₃ : Exec w (.write a_vis (.reg r_s0) (.const 1)) st₂ st₃ 3 :=
    .write heval_s₀ heval_1 (by simp [harr_vis₂, s₀.2])
  have hq₃ : IsQueueHistory a_q r_head r_tail n [] 0 st₃ :=
    hq₂.of_eq (by simp [st₃, hne_vq'.symm]) rfl rfl
  -- 4. queuePush a_q r_tail (.reg r_s0)
  rcases Triple.queuePush_spec a_q r_head r_tail (.reg r_s0) n [] 0 s₀.1
      hne_ht hw hn_w (show ([] : List ℕ).length < n from Nat.zero_lt_of_lt s₀.2) st₃
      ⟨hq₃, by simp [st₃, Expr.eval, checkWord, hrs0₂, hs₀_w]⟩ with
    ⟨st₄, t₄, hex₄, ht₄, hq₄⟩
  dsimp [Expr.cost] at ht₄
  have hnot4_s : (a_start : Arr) ∉ (queuePush a_q r_tail (.reg r_s0)).writtenArrs := by
    simp [queuePush, Cmd.writtenArrs, hne_sq']
  have hnot4_e : (a_end : Arr) ∉ (queuePush a_q r_tail (.reg r_s0)).writtenArrs := by
    simp [queuePush, Cmd.writtenArrs, hne_eq']
  have hnot4_ent : (a_entries : Arr) ∉ (queuePush a_q r_tail (.reg r_s0)).writtenArrs := by
    simp [queuePush, Cmd.writtenArrs, hne_entq']
  have hnot4_vis : (a_vis : Arr) ∉ (queuePush a_q r_tail (.reg r_s0)).writtenArrs := by
    simp [queuePush, Cmd.writtenArrs, hne_vq']
  have hadj₄ : IsAdjList G a_start a_end a_entries lists st₄ :=
    (hadj₂.of_arrs_eq (by simp [st₃, hne_sv']) (by simp [st₃, hne_ev']) (by simp [st₃, hne_entv'])).of_arrs_eq
      (Exec.arrs_eq_of_not_mem_writtenArrs hex₄ hnot4_s)
      (Exec.arrs_eq_of_not_mem_writtenArrs hex₄ hnot4_e)
      (Exec.arrs_eq_of_not_mem_writtenArrs hex₄ hnot4_ent)
  have hent₄ : (st₄.arrs a_entries).length < 2 ^ w := by
    rw [Exec.arrs_eq_of_not_mem_writtenArrs hex₄ hnot4_ent]
    simpa [st₃, hne_entv'] using hent₂
  have hvis_eq₄ : st₄.arrs a_vis = (List.replicate n 0).set s₀.1 1 := by
    rw [Exec.arrs_eq_of_not_mem_writtenArrs hex₄ hnot4_vis]
    simp [st₃, harr_vis₂]
  -- 5. Verify BfsQueueInv on st₄ and invoke bfsLoopProg_exec_closed
  have hinv₄ : BfsQueueInv (w := w) G lists a_start a_end a_entries a_vis a_q
      r_head r_tail r_u r_k r_hi r_v r_vis ∅ (fun _ => 0) s₀ 1 st₄ [s₀.1] 0 st₄ := by
    refine ⟨hadj₄, hent₄, fun _ _ _ _ _ _ _ _ => rfl,
      hq₄, List.nodup_singleton s₀.1, by simp,
      fun x hx => by rw [List.mem_singleton] at hx; subst hx; exact s₀.2,
      fun x hx => by simp at hx,
      fun x hx => by
        rw [List.mem_singleton] at hx
        have hxeq : x = s₀ := Fin.ext hx
        rw [hxeq],
      fun u hu => by simp at hu,
      by simp [hvis_eq₄],
      fun x hx => by simp at hx,
      fun x hx => ?_,
      fun x _ hx_not => ?_⟩
    · rw [List.mem_singleton] at hx
      simp only [hvis_eq₄, hx]
      exact List.getElem_set_self (by simp [s₀.2])
    · rw [List.mem_singleton] at hx_not
      simp only [hvis_eq₄]
      rw [List.getElem_set_ne (Ne.symm hx_not), List.getElem_replicate]
  rcases bfsLoopProg_exec_closed G lists a_start a_end a_entries a_vis a_q
      r_head r_tail r_u r_k r_hi r_v r_vis (.const 1) ∅ (fun _ => 0) s₀ 1 st₄
      hne_sv hne_ev hne_entv hne_sq hne_eq hne_entq hne_vq
      hne_ht hne_hu hne_hk hne_hhi hne_hv hne_hvis
      hne_tu hne_tk hne_thi hne_tv hne_tvis
      hne_uk hne_uhi hne_uv hne_uvis
      hne_khi hne_kv hne_kvis hne_hiv hne_hivis hne_vvis
      hw hn_w (by omega) hw (fun x hx => by simp at hx) (fun x hx => by simp at hx)
      (fun x hx => by simp at hx) (by simp) (by simp [Expr.cost])
      (fun s _ => by simp [Expr.eval, checkWord, hw]) hinv₄ with
    ⟨st₅, t₅, hex₅, ht₅, _, _, _, _, hvis_len₅, _, hv2₅, hv3₅⟩
  have hsum_le := sum_bfsVertexWeight_le_univ lists (reachSet G s₀)
  refine ⟨st₅, (1 + n) + (((1 + n) + (2 + 2)) + (3 + (t₄ + t₅))),
    .seq hex₁ (.seq hex₂ (.seq hex₃ (.seq hex₄ hex₅))),
    by dsimp only; omega, ?_⟩
  classical
  apply List.ext_getElem
  · simp [hvis_len₅]
  · intro i h1 h2
    have hi_lt : i < n := by simpa [hvis_len₅] using h1
    let v : Fin n := ⟨i, hi_lt⟩
    rw [List.getElem_ofFn]
    by_cases hreach_v : G.Reachable s₀ v
    · have hv_eq1 := hv2₅ v ((mem_reachSet G s₀ v).mpr hreach_v)
      simpa [v, hreach_v] using hv_eq1
    · have hv_eq0 := hv3₅ v (by simp) (by simpa [mem_reachSet] using hreach_v)
      simpa [v, hreach_v] using hv_eq0

/-- Problem input for single-source reachability: a finite simple graph `G : SimpleGraph (Fin n)`
with `DecidableRel G.Adj` and a source vertex `s₀ : Fin n`. -/
structure BfsInput where
  /-- Number of vertices. -/
  n : ℕ
  /-- The input simple graph on `Fin n`. -/
  G : SimpleGraph (Fin n)
  /-- Decidability of adjacency in `G`. -/
  [decAdj : DecidableRel G.Adj]
  /-- Source vertex for reachability. -/
  s₀ : Fin n

attribute [instance] BfsInput.decAdj

/-- Size of a BFS problem instance `(G, s₀)`: `n + m`, where `m = G.edgeFinset.card`.
Note: the flat list encoding `encBfsIn x` has length `2 * m + 3`, which can be smaller than `n`
when `G` has isolated vertices (`m < n`). We define `bfsSize x = n + m` (which is `n + m + 2` up to
the additive constant `2`) so that `O(n + m)` time is linear in `bfsSize x` and the word size
`w = wordSize c (bfsSize x)` is large enough to hold vertex indices `< n` even when `m = 0`. -/
def bfsSize (x : BfsInput) : ℕ :=
  x.n + x.G.edgeFinset.card

/-- Flat input encoding of a BFS instance `(G, s₀)` in `inArr`:
`[n, m, u_0, v_0, ..., u_{m-1}, v_{m-1}, s₀]`. -/
def encBfsIn (x : BfsInput) : List ℕ :=
  encGraph x.G ++ [x.s₀.1]

/-- Mathematical output of single-source reachability: the length-`n` list whose `v`-th entry is
`1` if `v` is reachable from `s₀` in `G` and `0` otherwise. -/
noncomputable def bfsReachList (x : BfsInput) : List ℕ :=
  open Classical in
  List.ofFn (fun v : Fin x.n => if x.G.Reachable x.s₀ v then 1 else 0)

/-- Fixed end-to-end Word RAM program for single-source reachability:
1. Parses `G` from `inArr` into CSR arrays `(a_start = 3, a_end = 4, a_entries = 5)` using degree
   scratch array `a_deg = 2` and registers `0..6` (`r_0 := n`, `r_1 := m`).
2. Reads `s₀` from `inArr[2 + 2 * m]` into register `2`.
3. Runs `bfsRegProg` with `r_n = 0`, `r_s0 = 2`, writing the `0`/`1` reachability indicator list
   directly to `outArr = 1` using queue array `a_q = 6` and scratch registers `3..9`. -/
def bfsEndToEndProg : Cmd :=
  .seq (parseGraphProg 2 3 4 5 0)
    (.seq (.assign 2 (.read inArr (.op .add (.const 2) (.op .mul (.const 2) (.reg 1)))))
      (bfsRegProg 0 2 3 4 5 outArr 6 3 4 5 6 7 8 9))

theorem inArr_getElem_after_edges {n : ℕ} (edges : List (Fin n × Fin n)) (s₀_val : ℕ)
    {arr : List ℕ} (harr : arr = [n, edges.length] ++ flatEdges edges ++ [s₀_val]) :
    ∃ (hidx : 2 + 2 * edges.length < arr.length), arr[2 + 2 * edges.length]'hidx = s₀_val := by
  have hlen : 2 + 2 * edges.length < arr.length := by
    simp [harr, length_flatEdges]; omega
  refine ⟨hlen, ?_⟩
  simp only [harr]
  rw [List.getElem_append_right (by simp [length_flatEdges]; omega)]
  have hsub : 2 + 2 * edges.length - ([n, edges.length] ++ flatEdges edges).length = 0 := by
    simp [length_flatEdges]; omega
  simp only [hsub, List.getElem_cons_zero]

/-- End-to-end `O(n + m)` complexity theorem for single-source reachability (`bfsEndToEndProg`):
from any initial state whose `inArr` holds `encBfsIn x`, `bfsEndToEndProg` terminates in at most
`140 * (bfsSize x + 1)` steps and leaves `bfsReachList x` in `outArr`. -/
theorem bfs_computesInTime :
    ComputesArrInTime bfsSize encBfsIn id bfsReachList bfsEndToEndProg (fun k => k + 1) := by
  unfold ComputesArrInTime ComputesInTime
  refine ⟨140, 2, by omega, by omega, fun x s₀ hs₀ => ?_⟩
  let edges := edgeListOf x.G
  have hedges : IsSimpleEdgeList x.G edges := isSimpleEdgeList_edgeListOf x.G
  have hm_eq : edges.length = x.G.edgeFinset.card := length_edgeListOf_eq_card_edgeFinset x.G
  have htot_eq : totalAdjEntries (edgeNeighbors edges) = 2 * edges.length :=
    totalAdjEntries_edgeNeighbors edges hedges.1
  let w := wordSize 2 (bfsSize x)
  have hw_bound : 2 * (bfsSize x + 2) < 2 ^ w :=
    two_mul_lt_two_pow_wordSize (c := 2) (n := bfsSize x) (by omega)
  have hbfs_eq : bfsSize x = x.n + edges.length := by simp [bfsSize, hm_eq]
  have hw2 : 2 < 2 ^ w := by omega
  have hw : 1 < 2 ^ w := by omega
  have hn_w : x.n < 2 ^ w := by omega
  have hm2_w : 2 + 2 * edges.length < 2 ^ w := by omega
  have hm_w : edges.length < 2 ^ w := by omega
  have h2m_w : 2 * edges.length < 2 ^ w := by omega
  have hs₀_w : x.s₀.1 < 2 ^ w := by have := x.s₀.2; omega
  have hin₀ : s₀.arrs inArr = [x.n, edges.length] ++ flatEdges edges ++ [x.s₀.1] := by
    simpa [encBfsIn, encGraph, edges] using hs₀
  -- 1. Run parseGraphProg 2 3 4 5 0
  rcases Triple.parseGraphProg_spec (w := w) x.G edges [x.s₀.1] 2 3 4 5 0 hedges
      (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      hw2 hn_w hm2_w s₀ hin₀ with
    ⟨s₁, t₁, hex₁, ht₁, hin₁, hrn₁, hrm₁, hadj₁, hent₁, _⟩
  dsimp only at ht₁
  -- 2. Read s₀ from inArr[2 + 2 * r_1] into r_2
  obtain ⟨hlen_s₀, hget_s₀⟩ := inArr_getElem_after_edges edges x.s₀.1 hin₁
  have heval_s₀ :
      (Expr.read inArr (.op .add (.const 2) (.op .mul (.const 2) (.reg 1)))).eval w s₁ =
        some x.s₀.1 := by
    simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hrm₁, hw2, hm_w, h2m_w, hm2_w,
      hlen_s₀, hget_s₀, hs₀_w]
  let s₂ := s₁.setReg 2 x.s₀.1
  have hex₂ :
      Exec w (.assign 2 (.read inArr (.op .add (.const 2) (.op .mul (.const 2) (.reg 1)))))
        s₁ s₂ 7 := .assign heval_s₀
  -- 3. Run bfsRegProg 0 2 3 4 5 outArr 6 3 4 5 6 7 8 9
  have hadj₂ : IsAdjList x.G 3 4 5 (edgeNeighbors edges) s₂ :=
    hadj₁.of_arrs_eq rfl rfl rfl
  have hent₂_w : (s₂.arrs 5).length < 2 ^ w := by
    simp [s₂, hent₁, h2m_w]
  rcases Triple.bfsRegProg_spec (w := w) x.G (edgeNeighbors edges) x.s₀ 0 2 3 4 5 outArr 6
      3 4 5 6 7 8 9
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      hw hn_w s₂
      ⟨by simp [s₂, hrn₁], by simp [s₂], hadj₂, hent₂_w⟩ with
    ⟨s₃, t₃, hex₃, ht₃, hout₃⟩
  dsimp only at ht₃
  refine ⟨s₃, t₁ + (7 + t₃), .seq hex₁ (.seq hex₂ hex₃), by dsimp only; omega, ?_⟩
  simpa [bfsReachList] using hout₃

end GraphMinor.Compute
