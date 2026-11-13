module

public import GraphMinor.Compute.Restrict

/-!
# Directed Multigraphs with Loops and Parallel Edges on the Word RAM

This file formalizes directed multigraphs `MultiDigraph n` on `Fin n` (allowing loops and arbitrary
parallel edge multiplicities) and implements the input format and primitive graph operations assumed
by Robertson and Seymour in *Graph Minors XIII. The Disjoint Paths Problem*, Section 1, page 67:

"We would like to be able to construct the underlying simple graph $H$ of a graph $G$ in time
which depends only on $|E(H)|$, not on $|E(G)|$. This can of course be done if our graphs are
presented with an appropriate data structure, and we assume this is so. Similarly, we shall
always assume that we can decide, for a graph $G$ and vertices $u, v$ of $G$, whether there are
at least $k$ edges of $G$ joining $u$ and $v$, in time only dependent on $k$."

## Where the paper's data-structure assumption enters

A directed multigraph `G : MultiDigraph n` is defined by its multiplicity function
`G.edgeMult : Fin n → Fin n → ℕ`, where `G.edgeMult u v` is the number of directed edges with tail
`u` and head `v` (loops `u = v` allowed). In `inArr` (or any working array `a_md`), `G` is encoded
by `MultiDigraph.enc G`:
`[n, m', u_0, v_0, mult_0, ..., u_{m'-1}, v_{m'-1}, mult_{m'-1}]`,
where `m' = G.numActivePairs ≤ n²` is the number of distinct ordered pairs `(u, v)` with
`0 < G.edgeMult u v`, listed in canonical pair order `allDirectedPairs n` (for each `0 ≤ u ≤ v < n`,
`(u, u)` when `u = v`, and `(u, v)` followed by `(v, u)` when `u < v`), and
`mult_k = G.edgeMult u_k v_k` is stored in a single array cell.

The input size of `G` is `G.size = n + G.numActivePairs` (`n + m'`), not the total number of edges
`G.numEdges = |E(G)|`. Because `G.edgeMult u v` is an arbitrary natural number while the machine
word size `w = wordSize c (size x)` depends only on `n + m'`, reading an uncapped multiplicity cell
 needs clamping before word-size check. This is where the paper's assumption enters the model:
`Expr.readMin a idx cap` reads `min a[idx] cap` at cost `idx.cost + cap.cost + 2`, allowing a
program to test `k ≤ G.edgeMult u v` (when `k < 2 ^ w`) or cap `G.edgeMult u v` at `δ` or `δ + 1`
(in Step (1) of Algorithm (6.5)) in `O(1)` time per active pair without requiring
`G.edgeMult u v < 2 ^ w`.

## Main definitions and specifications

* `GraphMinor.Compute.MultiDigraph`: directed multigraph on `Fin n` with multiplicity function
  `edgeMult : Fin n → Fin n → ℕ`.
* `GraphMinor.Compute.MultiDigraph.cap`: the maximal subdigraph of `G` with at most `δ` loops at
  each vertex and at most `δ + 1` edges with tail `u` and head `v` for all distinct `u, v`
  (GM XIII (6.5) Step (1)).
* `GraphMinor.Compute.MultiDigraph.toSimpleGraph`: the underlying loopless undirected simple graph
  `SimpleGraph (Fin n)` of `G`.
* `GraphMinor.Compute.MultiDigraph.deleteVertex`: the induced subdigraph on `Fin n'` obtained from
  `G : MultiDigraph (n' + 1)` by deleting vertex `v₀ : Fin (n' + 1)` via `v₀.succAbove`.
* `GraphMinor.Compute.capMultiDigraphProg`: Word RAM implementation of GM XIII (6.5) Step (1) in
  `O(m' + 1)` steps.
* `GraphMinor.Compute.toSimpleGraphProg`: Word RAM construction of both the canonical simple edge
  list `encGraph G.toSimpleGraph` and the CSR representation `IsAdjList G.toSimpleGraph` in
  `O(n + m')` steps.
* `GraphMinor.Compute.deleteVertexMultiDigraphProg`: Word RAM deletion of one vertex in `O(n + m')`
  steps, maintaining the renaming array `orig` back to the original vertex names.
-/

@[expose] public section

namespace GraphMinor.Compute

open SimpleGraph
open scoped BigOperators

/-! ### Section 1: Directed Multigraphs and Combinatorial Operations -/

/-- A directed multigraph on `Fin n`, specified by the multiplicity `edgeMult u v : ℕ` of directed
edges from `u` to `v` (loops `u = v` allowed). -/
@[ext]
structure MultiDigraph (n : ℕ) where
  /-- Number of directed edges with tail `u` and head `v`. -/
  edgeMult : Fin n → Fin n → ℕ

namespace MultiDigraph

/-- Total number of directed edges `|E(G)| = ∑ u, ∑ v, G.edgeMult u v`. -/
def numEdges {n : ℕ} (G : MultiDigraph n) : ℕ :=
  ∑ u : Fin n, ∑ v : Fin n, G.edgeMult u v

/-- `H` is a subdigraph of `G` (`H ≤ G`) if `H.edgeMult u v ≤ G.edgeMult u v` for all `u, v`. -/
instance instLE (n : ℕ) : LE (MultiDigraph n) where
  le H G := ∀ u v : Fin n, H.edgeMult u v ≤ G.edgeMult u v

theorem le_def {n : ℕ} {H G : MultiDigraph n} :
    H ≤ G ↔ ∀ u v : Fin n, H.edgeMult u v ≤ G.edgeMult u v :=
  Iff.rfl

instance instPartialOrder (n : ℕ) : PartialOrder (MultiDigraph n) where
  le_refl _ _ _ := le_rfl
  le_trans _ _ _ h₁ h₂ u v := le_trans (h₁ u v) (h₂ u v)
  le_antisymm _ _ h₁ h₂ := MultiDigraph.ext (funext fun u => funext fun v => le_antisymm (h₁ u v) (h₂ u v))

theorem numEdges_mono {n : ℕ} {H G : MultiDigraph n} (h : H ≤ G) :
    H.numEdges ≤ G.numEdges :=
  Finset.sum_le_sum fun u _ => Finset.sum_le_sum fun v _ => h u v

/-- The maximal subdigraph of `G` with at most `δ` loops at each vertex and at most `δ + 1`
directed edges from `u` to `v` for all distinct `u, v` (GM XIII (6.5), Step (1)). -/
def cap {n : ℕ} (δ : ℕ) (G : MultiDigraph n) : MultiDigraph n where
  edgeMult u v := Nat.min (G.edgeMult u v) (if u = v then δ else δ + 1)

@[simp]
theorem cap_edgeMult {n : ℕ} (δ : ℕ) (G : MultiDigraph n) (u v : Fin n) :
    (G.cap δ).edgeMult u v = Nat.min (G.edgeMult u v) (if u = v then δ else δ + 1) :=
  rfl

theorem cap_le {n : ℕ} (δ : ℕ) (G : MultiDigraph n) : G.cap δ ≤ G :=
  fun _ _ => Nat.min_le_left _ _

theorem cap_loop_le {n : ℕ} (δ : ℕ) (G : MultiDigraph n) (u : Fin n) :
    (G.cap δ).edgeMult u u ≤ δ := by
  simp [cap]

theorem cap_nonloop_le {n : ℕ} (δ : ℕ) (G : MultiDigraph n) {u v : Fin n} (hne : u ≠ v) :
    (G.cap δ).edgeMult u v ≤ δ + 1 := by
  simp [cap, hne]

theorem cap_edgeMult_le_succ {n : ℕ} (δ : ℕ) (G : MultiDigraph n) (u v : Fin n) :
    (G.cap δ).edgeMult u v ≤ δ + 1 := by
  by_cases h : u = v
  · subst h; exact le_trans (G.cap_loop_le δ u) (Nat.le_succ δ)
  · exact G.cap_nonloop_le δ h

/-- Universal property of `G.cap δ`: `H ≤ G.cap δ` if and only if `H ≤ G`, `H` has at most `δ`
loops at each vertex, and `H` has at most `δ + 1` edges from `u` to `v` for all `u ≠ v`. -/
theorem le_cap_iff {n : ℕ} (δ : ℕ) (G H : MultiDigraph n) :
    H ≤ G.cap δ ↔
      H ≤ G ∧ (∀ u : Fin n, H.edgeMult u u ≤ δ) ∧
        (∀ u v : Fin n, u ≠ v → H.edgeMult u v ≤ δ + 1) := by
  refine ⟨fun h => ⟨le_trans h (G.cap_le δ), fun u => le_trans (h u u) (G.cap_loop_le δ u),
    fun u v hne => le_trans (h u v) (G.cap_nonloop_le δ hne)⟩, ?_⟩
  rintro ⟨hle, hloop, hnonloop⟩ u v
  rw [cap_edgeMult]
  refine le_min (hle u v) ?_
  by_cases huv : u = v
  · subst huv; simp [hloop u]
  · simp [huv, hnonloop u v huv]

/-- The underlying loopless undirected simple graph of `G : MultiDigraph n`. -/
def toSimpleGraph {n : ℕ} (G : MultiDigraph n) : SimpleGraph (Fin n) where
  Adj u v := u ≠ v ∧ (0 < G.edgeMult u v ∨ 0 < G.edgeMult v u)
  symm := ⟨fun _ _ ⟨hne, h⟩ => ⟨hne.symm, h.symm⟩⟩
  loopless := ⟨fun _ ⟨hne, _⟩ => hne rfl⟩

instance instDecidableRelToSimpleGraphAdj {n : ℕ} (G : MultiDigraph n) :
    DecidableRel G.toSimpleGraph.Adj :=
  fun u v => inferInstanceAs (Decidable (u ≠ v ∧ (0 < G.edgeMult u v ∨ 0 < G.edgeMult v u)))

@[simp]
theorem toSimpleGraph_adj {n : ℕ} (G : MultiDigraph n) (u v : Fin n) :
    G.toSimpleGraph.Adj u v ↔ u ≠ v ∧ (0 < G.edgeMult u v ∨ 0 < G.edgeMult v u) :=
  Iff.rfl

/-- Capping edge multiplicities with `G.cap δ` preserves the underlying simple graph for every
`δ : ℕ` (including `δ = 0`, since distinct vertices keep capacity `δ + 1 ≥ 1`). -/
@[simp]
theorem toSimpleGraph_cap {n : ℕ} (δ : ℕ) (G : MultiDigraph n) :
    (G.cap δ).toSimpleGraph = G.toSimpleGraph := by
  ext _u _v
  simp only [toSimpleGraph_adj, cap_edgeMult]
  by_cases huv : _u = _v
  · simp [huv]
  · have hvu : _v ≠ _u := Ne.symm huv
    simp only [huv, hvu, ↓reduceIte, Nat.lt_min]
    omega

/-- Key edge-count bound for GM XIII (6.5) Step (2): if `G` has at most `δ` loops at each vertex
and at most `δ + 1` edges between any distinct `u, v`, then
`G.numEdges ≤ δ * n + 2 * (δ + 1) * G.toSimpleGraph.edgeFinset.card`. -/
theorem numEdges_le_of_loop_and_nonloop_le {n δ : ℕ} (G : MultiDigraph n)
    (hloop : ∀ u : Fin n, G.edgeMult u u ≤ δ)
    (hnonloop : ∀ u v : Fin n, u ≠ v → G.edgeMult u v ≤ δ + 1) :
    G.numEdges ≤ δ * n + 2 * (δ + 1) * G.toSimpleGraph.edgeFinset.card := by
  have hpoint : ∀ u v : Fin n,
      G.edgeMult u v ≤
        (if u = v then δ else 0) + (if G.toSimpleGraph.Adj u v then δ + 1 else 0) := by
    intro u v
    by_cases huv : u = v
    · subst huv
      simp [hloop u]
    · simp only [huv, ↓reduceIte, Nat.zero_add]
      by_cases hadj : G.toSimpleGraph.Adj u v
      · simp only [hadj, ↓reduceIte]
        exact hnonloop u v huv
      · simp only [hadj, ↓reduceIte]
        rw [toSimpleGraph_adj] at hadj
        omega
  have hsum_le :
      G.numEdges ≤
        (∑ u : Fin n, ∑ v : Fin n, if u = v then δ else 0) +
        (∑ u : Fin n, ∑ v : Fin n, if G.toSimpleGraph.Adj u v then δ + 1 else 0) := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_le_sum fun u _ => ?_
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_le_sum fun v _ => hpoint u v
  have hdiag : (∑ u : Fin n, ∑ v : Fin n, if u = v then δ else 0) = δ * n := by
    simp [Nat.mul_comm]
  have hoff :
      (∑ u : Fin n, ∑ v : Fin n, if G.toSimpleGraph.Adj u v then δ + 1 else 0) =
        2 * (δ + 1) * G.toSimpleGraph.edgeFinset.card := by
    have h1 : ∀ u : Fin n,
        (∑ v : Fin n, if G.toSimpleGraph.Adj u v then δ + 1 else 0) =
          (δ + 1) * G.toSimpleGraph.degree u := by
      intro u
      rw [← G.toSimpleGraph.card_neighborFinset_eq_degree u, Finset.card_eq_sum_ones,
        Finset.mul_sum, ← Finset.sum_filter]
      refine Finset.sum_congr ?_ (fun _ _ => by simp)
      ext v
      simp [G.toSimpleGraph.mem_neighborFinset]
    simp_rw [h1, ← Finset.mul_sum, G.toSimpleGraph.sum_degrees_eq_twice_card_edges]
    rw [← Nat.mul_assoc, Nat.mul_comm (δ + 1) 2]
  rw [hdiag, hoff] at hsum_le
  exact hsum_le

/-- Induced subdigraph of `G : MultiDigraph n` along a vertex map `f : Fin n' → Fin n`. -/
def induce {n n' : ℕ} (G : MultiDigraph n) (f : Fin n' → Fin n) : MultiDigraph n' where
  edgeMult i j := G.edgeMult (f i) (f j)

@[simp]
theorem induce_edgeMult {n n' : ℕ} (G : MultiDigraph n) (f : Fin n' → Fin n) (i j : Fin n') :
    (G.induce f).edgeMult i j = G.edgeMult (f i) (f j) :=
  rfl

theorem induce_comp {n n' n'' : ℕ} (G : MultiDigraph n) (f : Fin n' → Fin n)
    (g : Fin n'' → Fin n') :
    (G.induce f).induce g = G.induce (f ∘ g) :=
  rfl

theorem toSimpleGraph_induce {n n' : ℕ} (G : MultiDigraph n) {f : Fin n' → Fin n}
    (hf : Function.Injective f) (i j : Fin n') :
    (G.induce f).toSimpleGraph.Adj i j ↔ G.toSimpleGraph.Adj (f i) (f j) := by
  simp [toSimpleGraph_adj, hf.ne_iff]

/-- Delete one vertex `v₀ : Fin (n' + 1)` from `G : MultiDigraph (n' + 1)`, reindexing the
remaining `n'` vertices in order via `v₀.succAbove : Fin n' → Fin (n' + 1)`. -/
def deleteVertex {n' : ℕ} (G : MultiDigraph (n' + 1)) (v₀ : Fin (n' + 1)) : MultiDigraph n' :=
  G.induce v₀.succAbove

@[simp]
theorem deleteVertex_edgeMult {n' : ℕ} (G : MultiDigraph (n' + 1)) (v₀ : Fin (n' + 1))
    (i j : Fin n') :
    (G.deleteVertex v₀).edgeMult i j = G.edgeMult (v₀.succAbove i) (v₀.succAbove j) :=
  rfl

theorem induce_deleteVertex {n n' : ℕ} (G : MultiDigraph n) (orig : Fin (n' + 1) → Fin n)
    (v₀ : Fin (n' + 1)) :
    (G.induce orig).deleteVertex v₀ = G.induce (orig ∘ v₀.succAbove) :=
  rfl

end MultiDigraph

/-! ### Section 2: Canonical Triple Encoding of `MultiDigraph` -/

/-- Upper-triangular pairs `(u, v) : Fin n × Fin n` with `u.1 ≤ v.1` in lexicographic order. -/
def upperPairs (n : ℕ) : List (Fin n × Fin n) :=
  (allPairs n).filter (fun e => decide (e.1.1 ≤ e.2.1))

@[simp]
theorem mem_upperPairs {n : ℕ} (e : Fin n × Fin n) :
    e ∈ upperPairs n ↔ e.1.1 ≤ e.2.1 := by
  simp [upperPairs]

theorem nodup_upperPairs (n : ℕ) : (upperPairs n).Nodup :=
  (nodup_allPairs n).filter _

/-- Canonical ordering of all `n²` directed pairs `(u, v) : Fin n × Fin n` grouping `{u, v}`:
for each `(u, v) ∈ upperPairs n`, `[(u, u)]` if `u = v`, and `[(u, v), (v, u)]` if `u < v`. -/
def allDirectedPairs (n : ℕ) : List (Fin n × Fin n) :=
  (upperPairs n).flatMap (fun e => if e.1 = e.2 then [(e.1, e.1)] else [(e.1, e.2), (e.2, e.1)])

@[simp]
theorem mem_allDirectedPairs {n : ℕ} (p : Fin n × Fin n) :
    p ∈ allDirectedPairs n := by
  unfold allDirectedPairs
  rw [List.mem_flatMap]
  rcases le_total p.1.1 p.2.1 with hle | hle
  · refine ⟨(p.1, p.2), (mem_upperPairs _).mpr hle, ?_⟩
    by_cases heq : p.1 = p.2
    · simp only [heq, ↓reduceIte, List.mem_singleton]
      exact Prod.ext heq rfl
    · simp [heq]
  · refine ⟨(p.2, p.1), (mem_upperPairs _).mpr hle, ?_⟩
    by_cases heq : p.2 = p.1
    · simp only [heq, ↓reduceIte, List.mem_singleton]
      exact Prod.ext rfl heq
    · simp [heq]

theorem nodup_allDirectedPairs (n : ℕ) : (allDirectedPairs n).Nodup := by
  unfold allDirectedPairs
  rw [List.nodup_flatMap]
  refine ⟨?_, ?_⟩
  · rintro ⟨u, v⟩ _
    by_cases heq : u = v
    · simp [heq]
    · simp [heq]
  · refine (nodup_upperPairs n).pairwise_of_forall_ne fun e₁ he₁ e₂ he₂ hne => ?_
    rw [mem_upperPairs] at he₁ he₂
    dsimp [Function.onFun]
    rw [List.disjoint_left]
    intro p hp₁ hp₂
    have hset₁ : p = (e₁.1, e₁.2) ∨ p = (e₁.2, e₁.1) := by
      by_cases h : e₁.1 = e₁.2
      · simp only [h, ↓reduceIte, List.mem_singleton] at hp₁
        exact Or.inl (hp₁.trans (by rw [h]))
      · simpa [h] using hp₁
    have hset₂ : p = (e₂.1, e₂.2) ∨ p = (e₂.2, e₂.1) := by
      by_cases h : e₂.1 = e₂.2
      · simp only [h, ↓reduceIte, List.mem_singleton] at hp₂
        exact Or.inl (hp₂.trans (by rw [h]))
      · simpa [h] using hp₂
    rcases hset₁ with rfl | rfl <;> rcases hset₂ with heq | heq
    · exact hne heq
    · simp only [Prod.mk.injEq] at heq
      rcases heq with ⟨h1, h2⟩
      have h1' : e₁.1.1 = e₂.2.1 := congrArg Fin.val h1
      have h2' : e₁.2.1 = e₂.1.1 := congrArg Fin.val h2
      have h12 : e₁.1 = e₁.2 := Fin.ext (by omega)
      have h21 : e₂.1 = e₂.2 := Fin.ext (by omega)
      exact hne (Prod.ext (by rw [h1, ← h21]) (by rw [h2, h21]))
    · simp only [Prod.mk.injEq] at heq
      rcases heq with ⟨h1, h2⟩
      have h1' : e₁.2.1 = e₂.1.1 := congrArg Fin.val h1
      have h2' : e₁.1.1 = e₂.2.1 := congrArg Fin.val h2
      have h12 : e₁.1 = e₁.2 := Fin.ext (by omega)
      have h21 : e₂.1 = e₂.2 := Fin.ext (by omega)
      exact hne (Prod.ext (by rw [h2, ← h21]) (by rw [h1, h21]))
    · simp only [Prod.mk.injEq] at heq
      exact hne (Prod.ext heq.2 heq.1)

namespace MultiDigraph

/-- Canonical list of active ordered pairs `(u, v)` (`0 < G.edgeMult u v`). -/
def activePairsList {n : ℕ} (G : MultiDigraph n) : List (Fin n × Fin n) :=
  (allDirectedPairs n).filter (fun p => decide (0 < G.edgeMult p.1 p.2))

@[simp]
theorem mem_activePairsList {n : ℕ} (G : MultiDigraph n) (p : Fin n × Fin n) :
    p ∈ G.activePairsList ↔ 0 < G.edgeMult p.1 p.2 := by
  simp [activePairsList]

theorem nodup_activePairsList {n : ℕ} (G : MultiDigraph n) :
    G.activePairsList.Nodup :=
  (nodup_allDirectedPairs n).filter _

/-- Number `m'` of active ordered pairs `(u, v)` with `0 < G.edgeMult u v`. -/
def numActivePairs {n : ℕ} (G : MultiDigraph n) : ℕ :=
  G.activePairsList.length

theorem numActivePairs_le_sq {n : ℕ} (G : MultiDigraph n) :
    G.numActivePairs ≤ n * n := by
  have hsub : G.activePairsList.toFinset ⊆ (Finset.univ : Finset (Fin n × Fin n)) :=
    Finset.subset_univ _
  have hcard := Finset.card_le_card hsub
  rw [List.toFinset_card_of_nodup G.nodup_activePairsList] at hcard
  simpa [numActivePairs, Fintype.card_prod] using hcard

/-- Input size `n + m'` of `G : MultiDigraph n` under the GM XIII page 67 assumption. -/
def size {n : ℕ} (G : MultiDigraph n) : ℕ :=
  n + G.numActivePairs

/-- Flat list of triples `[u_0, v_0, mult_0, ..., u_{m'-1}, v_{m'-1}, mult_{m'-1}]` for a list of
ordered pairs `pairs : List (Fin n × Fin n)`. -/
def flatTriples {n : ℕ} (G : MultiDigraph n) : List (Fin n × Fin n) → List ℕ
  | [] => []
  | p :: ps => p.1.1 :: p.2.1 :: G.edgeMult p.1 p.2 :: flatTriples G ps

@[simp]
theorem length_flatTriples {n : ℕ} (G : MultiDigraph n) (pairs : List (Fin n × Fin n)) :
    (flatTriples G pairs).length = 3 * pairs.length := by
  induction pairs with
  | nil => simp [flatTriples]
  | cons p ps ih => simp [flatTriples, ih]; omega

theorem flatTriples_append {n : ℕ} (G : MultiDigraph n) (l₁ l₂ : List (Fin n × Fin n)) :
    flatTriples G (l₁ ++ l₂) = flatTriples G l₁ ++ flatTriples G l₂ := by
  induction l₁ with
  | nil => rfl
  | cons p ps ih => simp [flatTriples, ih]

theorem getElem_flatTriples_fst {n : ℕ} (G : MultiDigraph n) (pairs : List (Fin n × Fin n))
    (k : ℕ) (hk : k < pairs.length) :
    (flatTriples G pairs)[3 * k]'(by rw [length_flatTriples]; omega) = (pairs[k]).1.1 := by
  induction pairs generalizing k with
  | nil => simp at hk
  | cons p ps ih =>
    cases k with
    | zero => rfl
    | succ k =>
      have hidx : 3 * (k + 1) = (3 * k) + 3 := by omega
      simpa [flatTriples, hidx] using ih k (Nat.lt_of_succ_lt_succ hk)

theorem getElem_flatTriples_snd {n : ℕ} (G : MultiDigraph n) (pairs : List (Fin n × Fin n))
    (k : ℕ) (hk : k < pairs.length) :
    (flatTriples G pairs)[3 * k + 1]'(by rw [length_flatTriples]; omega) = (pairs[k]).2.1 := by
  induction pairs generalizing k with
  | nil => simp at hk
  | cons p ps ih =>
    cases k with
    | zero => rfl
    | succ k =>
      have hidx : 3 * (k + 1) + 1 = (3 * k + 1) + 3 := by omega
      simpa [flatTriples, hidx] using ih k (Nat.lt_of_succ_lt_succ hk)

theorem getElem_flatTriples_mult {n : ℕ} (G : MultiDigraph n) (pairs : List (Fin n × Fin n))
    (k : ℕ) (hk : k < pairs.length) :
    (flatTriples G pairs)[3 * k + 2]'(by rw [length_flatTriples]; omega) =
      G.edgeMult (pairs[k]).1 (pairs[k]).2 := by
  induction pairs generalizing k with
  | nil => simp at hk
  | cons p ps ih =>
    cases k with
    | zero => rfl
    | succ k =>
      have hidx : 3 * (k + 1) + 2 = (3 * k + 2) + 3 := by omega
      simpa [flatTriples, hidx] using ih k (Nat.lt_of_succ_lt_succ hk)

/-- Canonical flat Word RAM encoding of `G : MultiDigraph n`:
`[n, m', u_0, v_0, mult_0, ..., u_{m'-1}, v_{m'-1}, mult_{m'-1}]`. -/
def enc {n : ℕ} (G : MultiDigraph n) : List ℕ :=
  [n, G.numActivePairs] ++ flatTriples G G.activePairsList

@[simp]
theorem length_enc {n : ℕ} (G : MultiDigraph n) :
    G.enc.length = 2 + 3 * G.numActivePairs := by
  simp [enc, numActivePairs]
  omega

/-- Active directed pairs of `G` corresponding to a single upper-triangular pair `e = (u, v)`. -/
def activeBlock {n : ℕ} (G : MultiDigraph n) (e : Fin n × Fin n) : List (Fin n × Fin n) :=
  (if e.1 = e.2 then [(e.1, e.1)] else [(e.1, e.2), (e.2, e.1)]).filter
    (fun p => decide (0 < G.edgeMult p.1 p.2))

theorem activePairsList_eq_flatMap_upperPairs {n : ℕ} (G : MultiDigraph n) :
    G.activePairsList = (upperPairs n).flatMap (activeBlock G) := by
  rw [activePairsList, allDirectedPairs, List.filter_flatMap]
  rfl

/-- One-pass deduplication of active directed pairs into undirected simple edges `(u, v)` with
`u.1 < v.1`, tracking the previously emitted pair `(prev_u, prev_v)`. -/
def toSimplePairsAux {n : ℕ} (prev_u prev_v : ℕ) : List (Fin n × Fin n) → List (Fin n × Fin n)
  | [] => []
  | (u, v) :: ps =>
    if u.1 < v.1 then
      (u, v) :: toSimplePairsAux u.1 v.1 ps
    else if v.1 < u.1 then
      if prev_u = v.1 ∧ prev_v = u.1 then
        toSimplePairsAux prev_u prev_v ps
      else
        (v, u) :: toSimplePairsAux v.1 u.1 ps
    else
      toSimplePairsAux prev_u prev_v ps

theorem toSimplePairsAux_activeBlock {n : ℕ} (G : MultiDigraph n) (u v : Fin n)
    (hle : u.1 ≤ v.1) (prev_u prev_v : ℕ) (hprev : ¬(prev_u = u.1 ∧ prev_v = v.1))
    (rest : List (Fin n × Fin n)) :
    toSimplePairsAux prev_u prev_v (activeBlock G (u, v) ++ rest) =
      if decide (u.1 < v.1 ∧ G.toSimpleGraph.Adj u v) then
        (u, v) :: toSimplePairsAux u.1 v.1 rest
      else
        toSimplePairsAux prev_u prev_v rest := by
  by_cases huv : u = v
  · subst huv
    have hnot : decide (u.1 < u.1 ∧ G.toSimpleGraph.Adj u u) = false :=
      decide_eq_false (fun h => Nat.lt_irrefl _ h.1)
    rw [hnot]
    simp only [activeBlock, ↓reduceIte, Bool.false_eq_true]
    by_cases hm : 0 < G.edgeMult u u <;> simp [hm, toSimplePairsAux]
  · have hlt : u.1 < v.1 := Nat.lt_of_le_of_ne hle (fun h => huv (Fin.ext h))
    have hlt_fin : u < v := hlt
    have hnot_gt : ¬(v.1 < u.1) := by omega
    have hnot_gt_fin : ¬(v < u) := hnot_gt
    simp only [activeBlock, huv, ↓reduceIte]
    by_cases hm1 : 0 < G.edgeMult u v <;> by_cases hm2 : 0 < G.edgeMult v u
    · have hadj : decide (u.1 < v.1 ∧ G.toSimpleGraph.Adj u v) = true :=
        decide_eq_true ⟨hlt, huv, Or.inl hm1⟩
      rw [hadj]
      simp [hm1, hm2, toSimplePairsAux, hlt_fin, hnot_gt_fin]
    · have hadj : decide (u.1 < v.1 ∧ G.toSimpleGraph.Adj u v) = true :=
        decide_eq_true ⟨hlt, huv, Or.inl hm1⟩
      rw [hadj]
      simp [hm1, hm2, toSimplePairsAux, hlt_fin]
    · have hadj : decide (u.1 < v.1 ∧ G.toSimpleGraph.Adj u v) = true :=
        decide_eq_true ⟨hlt, huv, Or.inr hm2⟩
      rw [hadj]
      simp [hm1, hm2, toSimplePairsAux, hlt_fin, hnot_gt_fin, hprev]
    · have hnot_adj : decide (u.1 < v.1 ∧ G.toSimpleGraph.Adj u v) = false := by
        refine decide_eq_false ?_
        rintro ⟨_, _, h | h⟩
        · exact hm1 h
        · exact hm2 h
      rw [hnot_adj]
      simp [hm1, hm2]

theorem toSimplePairsAux_flatMap_activeBlock {n : ℕ} (G : MultiDigraph n) :
    ∀ (es : List (Fin n × Fin n)) (_hnodup : es.Nodup)
      (_hupper : ∀ e ∈ es, e.1.1 ≤ e.2.1) (prev_u prev_v : ℕ)
      (_hprev : ∀ e ∈ es, ¬(prev_u = e.1.1 ∧ prev_v = e.2.1)),
      toSimplePairsAux prev_u prev_v (es.flatMap (activeBlock G)) =
        es.filter (fun e => decide (e.1.1 < e.2.1 ∧ G.toSimpleGraph.Adj e.1 e.2))
  | [], _, _, _, _, _ => rfl
  | (u, v) :: es, hnodup, hupper, prev_u, prev_v, hprev => by
    rw [List.nodup_cons] at hnodup
    have hle : u.1 ≤ v.1 := hupper (u, v) (by simp)
    have hprev_uv : ¬(prev_u = u.1 ∧ prev_v = v.1) := hprev (u, v) (by simp)
    have hprev_es_uv : ∀ e ∈ es, ¬(u.1 = e.1.1 ∧ v.1 = e.2.1) := by
      rintro ⟨u', v'⟩ he ⟨h1, h2⟩
      have heq : (u, v) = (u', v') := Prod.ext (Fin.ext h1) (Fin.ext h2)
      exact hnodup.1 (heq ▸ he)
    have hprev_es_old : ∀ e ∈ es, ¬(prev_u = e.1.1 ∧ prev_v = e.2.1) :=
      fun e he => hprev e (List.mem_cons_of_mem _ he)
    have hupper_es : ∀ e ∈ es, e.1.1 ≤ e.2.1 :=
      fun e he => hupper e (List.mem_cons_of_mem _ he)
    simp only [List.flatMap_cons, List.filter_cons]
    rw [toSimplePairsAux_activeBlock G u v hle prev_u prev_v hprev_uv]
    split_ifs with hcond
    · rw [toSimplePairsAux_flatMap_activeBlock G es hnodup.2 hupper_es u.1 v.1 hprev_es_uv]
    · rw [toSimplePairsAux_flatMap_activeBlock G es hnodup.2 hupper_es prev_u prev_v hprev_es_old]

/-- `toSimplePairsAux n n G.activePairsList` equals the canonical simple edge list
`edgeListOf G.toSimpleGraph`. -/
theorem toSimplePairsAux_activePairsList {n : ℕ} (G : MultiDigraph n) :
    toSimplePairsAux n n G.activePairsList = edgeListOf G.toSimpleGraph := by
  rw [activePairsList_eq_flatMap_upperPairs]
  rw [toSimplePairsAux_flatMap_activeBlock G (upperPairs n) (nodup_upperPairs n)
    (fun e he => (mem_upperPairs e).mp he) n n
    (fun e _ ⟨h1, _⟩ => Nat.ne_of_gt e.1.2 h1)]
  unfold upperPairs edgeListOf
  rw [List.filter_filter]
  refine List.filter_congr fun e _ => ?_
  rw [Bool.and_eq_left_iff_imp]
  intro h
  have h' : e.1.1 < e.2.1 ∧ G.toSimpleGraph.Adj e.1 e.2 := of_decide_eq_true h
  exact decide_eq_true (Nat.le_of_lt h'.1)

/-! ### List-level specifications for `cap` and `deleteVertex` -/

theorem activePairsList_cap {n : ℕ} (G : MultiDigraph n) (δ : ℕ) :
    (G.cap δ).activePairsList =
      G.activePairsList.filter (fun p => decide (0 < (G.cap δ).edgeMult p.1 p.2)) := by
  unfold activePairsList
  rw [List.filter_filter]
  refine List.filter_congr fun p _ => ?_
  symm
  rw [Bool.and_eq_left_iff_imp]
  intro h
  have h' : 0 < (G.cap δ).edgeMult p.1 p.2 := of_decide_eq_true h
  exact decide_eq_true (Nat.lt_of_lt_of_le h' (G.cap_le δ p.1 p.2))

/-- Cap edge multiplicities along a list of active directed pairs of `G`. -/
def capTriplesAux {n : ℕ} (G : MultiDigraph n) (δ : ℕ) :
    List (Fin n × Fin n) → List ℕ
  | [] => []
  | (u, v) :: ps =>
    let m := (G.cap δ).edgeMult u v
    if 0 < m then
      [u.1, v.1, m] ++ capTriplesAux G δ ps
    else
      capTriplesAux G δ ps

theorem capTriplesAux_eq_flatTriples_filter {n : ℕ} (G : MultiDigraph n) (δ : ℕ) :
    ∀ (ps : List (Fin n × Fin n)),
      capTriplesAux G δ ps =
        flatTriples (G.cap δ) (ps.filter (fun p => decide (0 < (G.cap δ).edgeMult p.1 p.2)))
  | [] => rfl
  | (u, v) :: ps => by
    simp only [capTriplesAux, List.filter_cons]
    by_cases hm : 0 < (G.cap δ).edgeMult u v
    · simp only [hm, ↓reduceIte, decide_true, flatTriples,
        capTriplesAux_eq_flatTriples_filter G δ ps, List.cons_append, List.nil_append]
    · simp only [hm, ↓reduceIte, decide_false, Bool.false_eq_true,
        capTriplesAux_eq_flatTriples_filter G δ ps]

theorem flatTriples_cap {n : ℕ} (G : MultiDigraph n) (δ : ℕ) :
    flatTriples (G.cap δ) (G.cap δ).activePairsList =
      capTriplesAux G δ G.activePairsList := by
  rw [activePairsList_cap, capTriplesAux_eq_flatTriples_filter]

/-- Numerical index in `Fin n` corresponding to `x : Fin (n + 1)` after deleting `v₀`. -/
def shiftIdx (v₀_val x_val : ℕ) : ℕ :=
  if x_val < v₀_val then x_val else x_val - 1

@[simp]
theorem shiftIdx_succAbove {n : ℕ} (v₀ : Fin (n + 1)) (u : Fin n) :
    shiftIdx v₀.1 (v₀.succAbove u).1 = u.1 := by
  unfold shiftIdx Fin.succAbove
  split_ifs with h1 h2 h2
  · rfl
  · exact absurd h1 h2
  · exact absurd (Nat.lt_of_succ_lt h2) h1
  · exact Nat.add_sub_cancel u.1 1

theorem map_succAbove_finRange :
    ∀ {n : ℕ} (v₀ : Fin (n + 1)),
      (List.finRange n).map v₀.succAbove =
        (List.finRange (n + 1)).filter (fun u => decide (u ≠ v₀))
  | 0, v₀ => by
    rw [List.finRange_zero, List.finRange_succ, List.finRange_zero]
    simp [Fin.eq_zero v₀]
  | n + 1, v₀ => by
    refine Fin.cases ?_ (fun v' => ?_) v₀
    · rw [List.finRange_succ (n := n + 1)]
      simp only [Fin.succAbove_zero, List.filter_cons, ne_eq, not_true_eq_false, decide_false,
        Bool.false_eq_true, ↓reduceIte]
      symm
      rw [List.filter_eq_self]
      intro u hu
      rw [List.mem_map] at hu
      rcases hu with ⟨j, _, rfl⟩
      exact decide_eq_true (Fin.succ_ne_zero j)
    · rw [List.finRange_succ (n := n), List.finRange_succ (n := n + 1)]
      simp only [List.map_cons, Fin.succ_succAbove_zero, List.map_map, List.filter_cons,
        ne_eq, (Fin.succ_ne_zero v').symm, not_false_eq_true, decide_true, ↓reduceIte,
        List.cons.injEq, true_and]
      have hcomp : v'.succ.succAbove ∘ Fin.succ = Fin.succ ∘ v'.succAbove := by
        funext j; exact Fin.succ_succAbove_succ v' j
      rw [hcomp, ← List.map_map, map_succAbove_finRange v', List.filter_map]
      congr 2

theorem filter_flatMap_pair {α : Type*} (p : α → Bool) (xs ys : List α) :
    (xs.filter p).flatMap (fun u => (ys.filter p).map (fun v => (u, v))) =
      (xs.flatMap (fun u => ys.map (fun v => (u, v)))).filter (fun e => p e.1 && p e.2) := by
  induction xs with
  | nil => rfl
  | cons u us ih =>
    simp only [List.filter_cons, List.flatMap_cons, List.filter_append]
    cases hu : p u
    · simp only [Bool.false_eq_true, ↓reduceIte, ih]
      symm
      rw [List.append_left_eq_self, List.filter_eq_nil_iff]
      intro e he
      rw [List.mem_map] at he
      rcases he with ⟨v, _, rfl⟩
      simp [hu]
    · simp only [↓reduceIte, List.flatMap_cons, ih, List.append_cancel_right_eq]
      rw [List.filter_map]
      congr 2
      funext v
      simp [hu]

theorem map_succAbove_allPairs {n : ℕ} (v₀ : Fin (n + 1)) :
    (allPairs n).map (Prod.map v₀.succAbove v₀.succAbove) =
      (allPairs (n + 1)).filter (fun e => decide (e.1 ≠ v₀ ∧ e.2 ≠ v₀)) := by
  unfold allPairs
  rw [List.map_flatMap]
  have h1 :
      (List.finRange n).flatMap (fun u =>
        ((List.finRange n).map (fun v => (u, v))).map (Prod.map v₀.succAbove v₀.succAbove)) =
      ((List.finRange n).map v₀.succAbove).flatMap (fun u =>
        ((List.finRange n).map v₀.succAbove).map (fun v => (u, v))) := by
    rw [List.flatMap_map]
    refine List.flatMap_congr fun u _ => ?_
    simp [List.map_map, Prod.map]
  rw [h1, map_succAbove_finRange v₀, filter_flatMap_pair]
  congr 2

theorem map_succAbove_upperPairs {n : ℕ} (v₀ : Fin (n + 1)) :
    (upperPairs n).map (Prod.map v₀.succAbove v₀.succAbove) =
      (upperPairs (n + 1)).filter (fun e => decide (e.1 ≠ v₀ ∧ e.2 ≠ v₀)) := by
  unfold upperPairs
  rw [List.filter_comm, ← map_succAbove_allPairs v₀, List.filter_map]
  congr 2
  funext ⟨u, v⟩
  simp [Prod.map, Fin.val_fin_le, Fin.succAbove_le_succAbove_iff]

private theorem filter_ne_dirBlock {n : ℕ} (v₀ u v : Fin (n + 1)) :
    (if u = v then [(u, u)] else [(u, v), (v, u)]).filter
      (fun e => decide (e.1 ≠ v₀ ∧ e.2 ≠ v₀)) =
      if decide (u ≠ v₀ ∧ v ≠ v₀) then
        (if u = v then [(u, u)] else [(u, v), (v, u)])
      else [] := by
  by_cases huv : u = v
  · subst huv
    by_cases hu : u ≠ v₀ <;> simp [hu]
  · by_cases hu : u ≠ v₀ <;> by_cases hv : v ≠ v₀ <;> simp [huv, hu, hv]

theorem map_succAbove_allDirectedPairs {n : ℕ} (v₀ : Fin (n + 1)) :
    (allDirectedPairs n).map (Prod.map v₀.succAbove v₀.succAbove) =
      (allDirectedPairs (n + 1)).filter (fun e => decide (e.1 ≠ v₀ ∧ e.2 ≠ v₀)) := by
  unfold allDirectedPairs
  rw [List.map_flatMap, List.filter_flatMap]
  have h1 :
      (upperPairs n).flatMap (fun e =>
        (if e.1 = e.2 then [(e.1, e.1)] else [(e.1, e.2), (e.2, e.1)]).map
          (Prod.map v₀.succAbove v₀.succAbove)) =
      ((upperPairs n).map (Prod.map v₀.succAbove v₀.succAbove)).flatMap (fun e =>
        if e.1 = e.2 then [(e.1, e.1)] else [(e.1, e.2), (e.2, e.1)]) := by
    rw [List.flatMap_map]
    refine List.flatMap_congr fun ⟨u, v⟩ _ => ?_
    by_cases huv : u = v <;> simp [huv, Prod.map, v₀.succAbove_right_inj]
  rw [h1, map_succAbove_upperPairs v₀]
  clear h1
  induction (upperPairs (n + 1)) with
  | nil => rfl
  | cons e es ih =>
    rcases e with ⟨u, v⟩
    simp only [List.filter_cons, List.flatMap_cons, filter_ne_dirBlock v₀ u v]
    cases he : decide (u ≠ v₀ ∧ v ≠ v₀)
    · simp only [Bool.false_eq_true, ↓reduceIte, List.nil_append, ih]
    · simp only [↓reduceIte, List.flatMap_cons, ih]

theorem map_succAbove_activePairsList_deleteVertex {n : ℕ}
    (G : MultiDigraph (n + 1)) (v₀ : Fin (n + 1)) :
    (G.deleteVertex v₀).activePairsList.map (Prod.map v₀.succAbove v₀.succAbove) =
      G.activePairsList.filter (fun e => decide (e.1 ≠ v₀ ∧ e.2 ≠ v₀)) := by
  unfold activePairsList
  rw [List.filter_comm, ← map_succAbove_allDirectedPairs v₀, List.filter_map]
  rfl

/-- Filter and reindex a list of active directed pairs of `G : MultiDigraph (n + 1)` when
deleting vertex `v₀`. -/
def deleteTriplesAux {n : ℕ} (G : MultiDigraph (n + 1)) (v₀ : Fin (n + 1)) :
    List (Fin (n + 1) × Fin (n + 1)) → List ℕ
  | [] => []
  | (u, v) :: ps =>
    if decide (u ≠ v₀ ∧ v ≠ v₀) then
      [shiftIdx v₀.1 u.1, shiftIdx v₀.1 v.1, G.edgeMult u v] ++ deleteTriplesAux G v₀ ps
    else
      deleteTriplesAux G v₀ ps

theorem deleteTriplesAux_filter {n : ℕ} (G : MultiDigraph (n + 1)) (v₀ : Fin (n + 1)) :
    ∀ (ps : List (Fin (n + 1) × Fin (n + 1))),
      deleteTriplesAux G v₀ (ps.filter (fun e => decide (e.1 ≠ v₀ ∧ e.2 ≠ v₀))) =
        deleteTriplesAux G v₀ ps
  | [] => rfl
  | (u, v) :: ps => by
    simp only [List.filter_cons, deleteTriplesAux]
    split_ifs with h
    · simp only [deleteTriplesAux, h, ↓reduceIte, deleteTriplesAux_filter G v₀ ps]
    · exact deleteTriplesAux_filter G v₀ ps

theorem flatTriples_deleteVertex_eq_deleteTriplesAux_map {n : ℕ}
    (G : MultiDigraph (n + 1)) (v₀ : Fin (n + 1)) :
    ∀ (ps : List (Fin n × Fin n)),
      flatTriples (G.deleteVertex v₀) ps =
        deleteTriplesAux G v₀ (ps.map (Prod.map v₀.succAbove v₀.succAbove))
  | [] => rfl
  | (u, v) :: ps => by
    have hne : v₀.succAbove u ≠ v₀ ∧ v₀.succAbove v ≠ v₀ :=
      ⟨v₀.succAbove_ne u, v₀.succAbove_ne v⟩
    simp [flatTriples, deleteTriplesAux, Prod.map, hne,
      flatTriples_deleteVertex_eq_deleteTriplesAux_map G v₀ ps]

theorem flatTriples_deleteVertex {n : ℕ} (G : MultiDigraph (n + 1)) (v₀ : Fin (n + 1)) :
    flatTriples (G.deleteVertex v₀) (G.deleteVertex v₀).activePairsList =
      deleteTriplesAux G v₀ G.activePairsList := by
  rw [flatTriples_deleteVertex_eq_deleteTriplesAux_map,
    map_succAbove_activePairsList_deleteVertex, deleteTriplesAux_filter]

/-- Sum of `G.edgeMult u v` over a list of directed pairs. -/
def sumEdgeMult {n : ℕ} (G : MultiDigraph n) : List (Fin n × Fin n) → ℕ
  | [] => 0
  | (u, v) :: ps => G.edgeMult u v + sumEdgeMult G ps

theorem sumEdgeMult_eq_map_sum {n : ℕ} (G : MultiDigraph n) (ps : List (Fin n × Fin n)) :
    sumEdgeMult G ps = (ps.map (fun p => G.edgeMult p.1 p.2)).sum := by
  induction ps with
  | nil => rfl
  | cons p ps ih => simp [sumEdgeMult, ih]

theorem sumEdgeMult_filter_pos {n : ℕ} (G : MultiDigraph n) :
    ∀ (ps : List (Fin n × Fin n)),
      sumEdgeMult G (ps.filter (fun p => decide (0 < G.edgeMult p.1 p.2))) =
        sumEdgeMult G ps
  | [] => rfl
  | (u, v) :: ps => by
    simp only [List.filter_cons, sumEdgeMult]
    by_cases hm : 0 < G.edgeMult u v
    · simp [hm, sumEdgeMult, sumEdgeMult_filter_pos G ps]
    · have hz : G.edgeMult u v = 0 := by omega
      simp [hz, sumEdgeMult_filter_pos G ps]

theorem toFinset_allDirectedPairs (n : ℕ) :
    (allDirectedPairs n).toFinset = Finset.univ := by
  ext e
  simp [mem_allDirectedPairs]

theorem sumEdgeMult_activePairsList {n : ℕ} (G : MultiDigraph n) :
    sumEdgeMult G G.activePairsList = G.numEdges := by
  unfold activePairsList
  rw [sumEdgeMult_filter_pos, sumEdgeMult_eq_map_sum,
    ← List.sum_toFinset _ (nodup_allDirectedPairs n), toFinset_allDirectedPairs,
    numEdges, ← Finset.sum_product']
  rfl

theorem sumEdgeMult_cap_activePairsList {n : ℕ} (G : MultiDigraph n) (δ : ℕ) :
    sumEdgeMult (G.cap δ) G.activePairsList = (G.cap δ).numEdges := by
  rw [← sumEdgeMult_activePairsList (G.cap δ), activePairsList_cap, sumEdgeMult_filter_pos]

/-- Sum of `G.edgeMult u v` over pairs `(u, v)` in `ps` that avoid `v₀`. -/
def sumEdgeMultAvoiding {n : ℕ} (G : MultiDigraph (n + 1)) (v₀ : Fin (n + 1)) :
    List (Fin (n + 1) × Fin (n + 1)) → ℕ
  | [] => 0
  | (u, v) :: ps =>
    (if decide (u ≠ v₀ ∧ v ≠ v₀) then G.edgeMult u v else 0) +
      sumEdgeMultAvoiding G v₀ ps

theorem sumEdgeMultAvoiding_filter {n : ℕ} (G : MultiDigraph (n + 1)) (v₀ : Fin (n + 1)) :
    ∀ (ps : List (Fin (n + 1) × Fin (n + 1))),
      sumEdgeMultAvoiding G v₀ (ps.filter (fun e => decide (e.1 ≠ v₀ ∧ e.2 ≠ v₀))) =
        sumEdgeMultAvoiding G v₀ ps
  | [] => rfl
  | (u, v) :: ps => by
    simp only [List.filter_cons, sumEdgeMultAvoiding]
    split_ifs with h
    · simp only [sumEdgeMultAvoiding, h, ↓reduceIte, sumEdgeMultAvoiding_filter G v₀ ps]
    · rw [Nat.zero_add, sumEdgeMultAvoiding_filter G v₀ ps]

theorem sumEdgeMult_deleteVertex_eq_sumEdgeMultAvoiding_map {n : ℕ}
    (G : MultiDigraph (n + 1)) (v₀ : Fin (n + 1)) :
    ∀ (ps : List (Fin n × Fin n)),
      sumEdgeMult (G.deleteVertex v₀) ps =
        sumEdgeMultAvoiding G v₀ (ps.map (Prod.map v₀.succAbove v₀.succAbove))
  | [] => rfl
  | (u, v) :: ps => by
    have hne : v₀.succAbove u ≠ v₀ ∧ v₀.succAbove v ≠ v₀ :=
      ⟨v₀.succAbove_ne u, v₀.succAbove_ne v⟩
    simp [sumEdgeMult, sumEdgeMultAvoiding, Prod.map, hne,
      sumEdgeMult_deleteVertex_eq_sumEdgeMultAvoiding_map G v₀ ps]

theorem sumEdgeMultAvoiding_activePairsList {n : ℕ}
    (G : MultiDigraph (n + 1)) (v₀ : Fin (n + 1)) :
    sumEdgeMultAvoiding G v₀ G.activePairsList = (G.deleteVertex v₀).numEdges := by
  rw [← sumEdgeMult_activePairsList (G.deleteVertex v₀),
    sumEdgeMult_deleteVertex_eq_sumEdgeMultAvoiding_map,
    map_succAbove_activePairsList_deleteVertex, sumEdgeMultAvoiding_filter]

end MultiDigraph

/-! ## Section 3: Word RAM Programs for `MultiDigraph` Operations -/

theorem getElem_of_eq_append_cons {α : Type*} {l pref suff : List α} {x : α}
    (h : l = pref ++ x :: suff) :
    ∃ (hk : pref.length < l.length), l[pref.length]'hk = x := by
  refine ⟨by simp [h], by simp [h]⟩

theorem enc_getElem_zero {n : ℕ} (G : MultiDigraph n) (extra : List ℕ)
    {l : List ℕ} (hl : l = G.enc ++ extra) :
    ∃ (h0 : 0 < l.length), l[0]'h0 = n := by
  refine ⟨by simp [hl, MultiDigraph.enc], by simp [hl, MultiDigraph.enc]⟩

theorem enc_getElem_one {n : ℕ} (G : MultiDigraph n) (extra : List ℕ)
    {l : List ℕ} (hl : l = G.enc ++ extra) :
    ∃ (h1 : 1 < l.length), l[1]'h1 = G.numActivePairs := by
  refine ⟨by simp [hl, MultiDigraph.enc], by simp [hl, MultiDigraph.enc]⟩

theorem enc_getElem_triple_fst {n : ℕ} (G : MultiDigraph n) (extra : List ℕ)
    {l : List ℕ} (hl : l = G.enc ++ extra) {k : ℕ} (hk : k < G.numActivePairs) :
    ∃ (hidx : 2 + 3 * k < l.length),
      l[2 + 3 * k]'hidx = (G.activePairsList[k]'hk).1.1 := by
  have hk' : k < G.activePairsList.length := hk
  have hlen : 2 + 3 * k < l.length := by
    rw [hl, List.length_append, G.length_enc]; omega
  refine ⟨hlen, ?_⟩
  have h1 : l[2 + 3 * k]'hlen =
      (([n, G.numActivePairs] ++ G.flatTriples G.activePairsList)[2 + 3 * k]'(by simp; omega)) := by
    simp only [hl, MultiDigraph.enc]
    exact List.getElem_append_left (by simp; omega)
  rw [h1, List.getElem_append_right (by simp)]
  have hsub : 2 + 3 * k - [n, G.numActivePairs].length = 3 * k := by simp
  simp only [hsub]
  exact MultiDigraph.getElem_flatTriples_fst G G.activePairsList k hk

theorem enc_getElem_triple_snd {n : ℕ} (G : MultiDigraph n) (extra : List ℕ)
    {l : List ℕ} (hl : l = G.enc ++ extra) {k : ℕ} (hk : k < G.numActivePairs) :
    ∃ (hidx : 2 + 3 * k + 1 < l.length),
      l[2 + 3 * k + 1]'hidx = (G.activePairsList[k]'hk).2.1 := by
  have hk' : k < G.activePairsList.length := hk
  have hlen : 2 + 3 * k + 1 < l.length := by
    rw [hl, List.length_append, G.length_enc]; omega
  refine ⟨hlen, ?_⟩
  have h1 : l[2 + 3 * k + 1]'hlen =
      (([n, G.numActivePairs] ++ G.flatTriples G.activePairsList)[2 + 3 * k + 1]'(by simp; omega)) := by
    simp only [hl, MultiDigraph.enc]
    exact List.getElem_append_left (by simp; omega)
  rw [h1, List.getElem_append_right (by simp; omega)]
  have hsub : 2 + 3 * k + 1 - [n, G.numActivePairs].length = 3 * k + 1 := by
    simp only [List.length_cons, List.length_nil]; omega
  simp only [hsub]
  exact MultiDigraph.getElem_flatTriples_snd G G.activePairsList k hk

theorem enc_getElem_triple_mult {n : ℕ} (G : MultiDigraph n) (extra : List ℕ)
    {l : List ℕ} (hl : l = G.enc ++ extra) {k : ℕ} (hk : k < G.numActivePairs) :
    ∃ (hidx : 2 + 3 * k + 2 < l.length),
      l[2 + 3 * k + 2]'hidx =
        G.edgeMult (G.activePairsList[k]'hk).1 (G.activePairsList[k]'hk).2 := by
  have hk' : k < G.activePairsList.length := hk
  have hlen : 2 + 3 * k + 2 < l.length := by
    rw [hl, List.length_append, G.length_enc]; omega
  refine ⟨hlen, ?_⟩
  have h1 : l[2 + 3 * k + 2]'hlen =
      (([n, G.numActivePairs] ++ G.flatTriples G.activePairsList)[2 + 3 * k + 2]'(by simp; omega)) := by
    simp only [hl, MultiDigraph.enc]
    exact List.getElem_append_left (by simp; omega)
  rw [h1, List.getElem_append_right (by simp)]
  have hsub : 2 + 3 * k + 2 - [n, G.numActivePairs].length = 3 * k + 2 := by
    simp only [List.length_cons, List.length_nil]; omega
  simp only [hsub]
  exact MultiDigraph.getElem_flatTriples_mult G G.activePairsList k hk

/-- Read the `k`-th active pair endpoints `(u_k, v_k)` from `a_src[2 + 3 * r_k]` and
`a_src[2 + 3 * r_k + 1]` into `r_u` and `r_v`, storing `2 + 3 * r_k` in `r_idx`. -/
def readTripleEndpoints (a_src : Arr) (r_k r_idx r_u r_v : Reg) : Cmd :=
  .seq (.assign r_idx (.op .add (.const 2) (.op .mul (.const 3) (.reg r_k))))
    (.seq (.assign r_u (.read a_src (.reg r_idx)))
      (.assign r_v (.read a_src (.op .add (.reg r_idx) (.const 1)))))

theorem readTripleEndpoints_exec {w n : ℕ} (G : MultiDigraph n) (extra : List ℕ)
    (a_src : ℕ) (r_k r_idx r_u r_v : ℕ) (k : ℕ) (s : State)
    (hne_iu : r_idx ≠ r_u) (hne_iv : r_idx ≠ r_v) (hne_uv : r_u ≠ r_v)
    (hw3 : 3 < 2 ^ w) (hn_w : n < 2 ^ w) (hm3_w : 2 + 3 * G.numActivePairs < 2 ^ w)
    (hk : k < G.numActivePairs)
    (hsrc : s.arrs a_src = G.enc ++ extra)
    (hrk : s.regs r_k = k) :
    ∃ s' t,
      Exec w (readTripleEndpoints a_src r_k r_idx r_u r_v) s s' t ∧
      t ≤ 14 ∧
      s'.regs r_idx = 2 + 3 * k ∧
      s'.regs r_u = (G.activePairsList[k]'hk).1.1 ∧
      s'.regs r_v = (G.activePairsList[k]'hk).2.1 ∧
      (∀ a : ℕ, s'.arrs a = s.arrs a) ∧
      (∀ r : ℕ, r ≠ r_idx → r ≠ r_u → r ≠ r_v → s'.regs r = s.regs r) := by
  have hw : 1 < 2 ^ w := by omega
  have hw2 : 2 < 2 ^ w := by omega
  have hk_w : k < 2 ^ w := by omega
  have h3k_w : 3 * k < 2 ^ w := by omega
  have hidx_w : 2 + 3 * k < 2 ^ w := by omega
  have hidx1_w : 2 + 3 * k + 1 < 2 ^ w := by omega
  have hu_w : (G.activePairsList[k]'hk).1.1 < 2 ^ w := by
    have := (G.activePairsList[k]'hk).1.2; omega
  have hv_w : (G.activePairsList[k]'hk).2.1 < 2 ^ w := by
    have := (G.activePairsList[k]'hk).2.2; omega
  have heval_idx :
      (Expr.op .add (.const 2) (.op .mul (.const 3) (.reg r_k))).eval w s =
        some (2 + 3 * k) := by
    simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hrk, hw2, hw3, hk_w, h3k_w, hidx_w]
  let s₁ := s.setReg r_idx (2 + 3 * k)
  have hex₁ : Exec w (.assign r_idx (.op .add (.const 2) (.op .mul (.const 3) (.reg r_k))))
      s s₁ 6 := .assign heval_idx
  obtain ⟨hlen_u, hget_u⟩ := enc_getElem_triple_fst G extra hsrc hk
  have heval_u : (Expr.read a_src (.reg r_idx)).eval w s₁ =
      some (G.activePairsList[k]'hk).1.1 := by
    simp [s₁, Expr.eval, checkWord, hidx_w, hlen_u, hget_u, hu_w]
  let s₂ := s₁.setReg r_u (G.activePairsList[k]'hk).1.1
  have hex₂ : Exec w (.assign r_u (.read a_src (.reg r_idx))) s₁ s₂ 3 := .assign heval_u
  obtain ⟨hlen_v, hget_v⟩ := enc_getElem_triple_snd G extra hsrc hk
  have heval_v : (Expr.read a_src (.op .add (.reg r_idx) (.const 1))).eval w s₂ =
      some (G.activePairsList[k]'hk).2.1 := by
    simp [s₂, s₁, Expr.eval, BinOp.eval, BinOp.raw, checkWord,
      show (r_idx : Reg) ≠ r_u from hne_iu,
      hidx_w, hw, hidx1_w, hlen_v, hget_v, hv_w]
  let s₃ := s₂.setReg r_v (G.activePairsList[k]'hk).2.1
  have hex₃ : Exec w (.assign r_v (.read a_src (.op .add (.reg r_idx) (.const 1)))) s₂ s₃ 5 :=
    .assign heval_v
  refine ⟨s₃, 6 + (3 + 5), .seq hex₁ (.seq hex₂ hex₃), by omega,
    by simp [s₃, s₂, s₁, show (r_idx : Reg) ≠ r_u from hne_iu,
      show (r_idx : Reg) ≠ r_v from hne_iv],
    by simp [s₃, s₂, show (r_u : Reg) ≠ r_v from hne_uv],
    by simp [s₃],
    fun _ => rfl,
    fun r hri hru hrv => by
      simp [s₃, s₂, s₁, show (r : Reg) ≠ r_idx from hri,
        show (r : Reg) ≠ r_u from hru, show (r : Reg) ≠ r_v from hrv]⟩

/-! ### Section 3.1: Deciding Whether There Are at Least `k` Edges Between `u` and `v` -/

/-- Decide in `O(1)` time (independent of `G.edgeMult u v`) whether the active pair at offset
`r_off = 2 + 3 * idx` in `a_src` has multiplicity at least `r_k`, storing `1` or `0` in `r_ans`.
Uses `Expr.readMin` to clamp the read multiplicity at `r_k` before checking the word bound. -/
def hasAtLeastKEdgesAtOffsetProg (a_src : Arr) (r_off r_k r_ans : Reg) : Cmd :=
  .seq (.assign r_ans (.readMin a_src (.op .add (.reg r_off) (.const 2)) (.reg r_k)))
    (.ite (.op .le (.reg r_k) (.reg r_ans))
      (.assign r_ans (.const 1))
      (.assign r_ans (.const 0)))

/-- Specification for `hasAtLeastKEdgesAtOffsetProg`: decides whether
`k ≤ G.edgeMult (G.activePairsList[idx]).1 (G.activePairsList[idx]).2` in `12` steps, even when
`G.edgeMult u v ≥ 2 ^ w`. -/
theorem hasAtLeastKEdgesAtOffsetProg_exec {w n : ℕ} (G : MultiDigraph n) (extra : List ℕ)
    (a_src : ℕ) (r_off r_k r_ans : ℕ)
    (hne_ka : (r_k : Reg) ≠ r_ans)
    {idx k : ℕ} (hidx : idx < G.numActivePairs)
    (hw2 : 2 < 2 ^ w) (hoff_w : 2 + 3 * idx + 2 < 2 ^ w) (hk_w : k < 2 ^ w)
    {s : State}
    (hsrc : s.arrs a_src = G.enc ++ extra)
    (hroff : s.regs r_off = 2 + 3 * idx)
    (hrk : s.regs r_k = k) :
    let u := (G.activePairsList[idx]'hidx).1
    let v := (G.activePairsList[idx]'hidx).2
    ∃ s' t,
      Exec w (hasAtLeastKEdgesAtOffsetProg a_src r_off r_k r_ans) s s' t ∧
      t ≤ 12 ∧
      s'.regs r_ans = (if k ≤ G.edgeMult u v then 1 else 0) ∧
      (∀ a, s'.arrs a = s.arrs a) ∧
      (∀ r, r ≠ r_ans → s'.regs r = s.regs r) := by
  intro u v
  have hw : 1 < 2 ^ w := by omega
  have h0_w : 0 < 2 ^ w := by omega
  have hoff0_w : 2 + 3 * idx < 2 ^ w := by omega
  obtain ⟨hlen_m, hget_m⟩ := enc_getElem_triple_mult G extra hsrc hidx
  let m_cap := Nat.min (G.edgeMult u v) k
  have hm_cap_w : m_cap < 2 ^ w := Nat.lt_of_le_of_lt (Nat.min_le_right _ _) hk_w
  have heval_rd :
      (Expr.readMin a_src (.op .add (.reg r_off) (.const 2)) (.reg r_k)).eval w s =
        some m_cap := by
    simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hroff, hrk, hoff0_w, hw2, hoff_w,
      hk_w, hlen_m, hget_m, u, v, m_cap, hm_cap_w]
  let s₁ := s.setReg r_ans m_cap
  have hex₁ :
      Exec w (.assign r_ans (.readMin a_src (.op .add (.reg r_off) (.const 2)) (.reg r_k)))
        s s₁ 7 := .assign heval_rd
  by_cases hle : k ≤ G.edgeMult u v
  · have hm_eq : m_cap = k := Nat.min_eq_right hle
    have hcond : (Expr.op .le (.reg r_k) (.reg r_ans)).eval w s₁ = some 1 := by
      simp [s₁, Expr.eval, BinOp.eval, BinOp.raw, checkWord, hne_ka, hrk, hm_eq, hk_w, hw]
    let s₂ := s₁.setReg r_ans 1
    have hex₂ : Exec w (.assign r_ans (.const 1)) s₁ s₂ 2 :=
      .assign (by simp [Expr.eval, checkWord, hw])
    refine ⟨s₂, 7 + (3 + 2), .seq hex₁ (.ite_true hcond (by omega) hex₂), by omega,
      by simp [s₂, hle], fun _ => rfl, fun r hr => by simp [s₂, s₁, hr]⟩
  · have hm_lt : m_cap < k := by
      have : G.edgeMult u v < k := by omega
      simpa [m_cap, Nat.min_eq_left (Nat.le_of_lt this)] using this
    have hnot_le : ¬(k ≤ m_cap) := by omega
    have hcond : (Expr.op .le (.reg r_k) (.reg r_ans)).eval w s₁ = some 0 := by
      simp [s₁, Expr.eval, BinOp.eval, BinOp.raw, checkWord, hne_ka, hrk,
        hm_cap_w, hk_w, hnot_le, h0_w]
    let s₂ := s₁.setReg r_ans 0
    have hex₂ : Exec w (.assign r_ans (.const 0)) s₁ s₂ 2 :=
      .assign (by simp [Expr.eval, checkWord, h0_w])
    refine ⟨s₂, 7 + (3 + 2), .seq hex₁ (.ite_false hcond hex₂), by omega,
      by simp [s₂, hle], fun _ => rfl, fun r hr => by simp [s₂, s₁, hr]⟩

/-! ### Section 3.2: Buffer Append Helpers (`bufPush2`, `bufPush3`) -/

theorem set_append_replicate_succ (pfx : List ℕ) (rem val : ℕ) :
    (pfx ++ List.replicate (rem + 1) 0).set pfx.length val =
      (pfx ++ [val]) ++ List.replicate rem 0 := by
  rw [List.set_append_right _ _ le_rfl]
  simp [List.replicate_succ]

/-- Write `(r_u, r_v)` at `a_buf[r_pos]` and `a_buf[r_pos + 1]`, and increment `r_pos` by `2`. -/
def bufPush2 (a_buf : Arr) (r_pos r_u r_v : Reg) : Cmd :=
  .seq (.write a_buf (.reg r_pos) (.reg r_u))
    (.seq (.write a_buf (.op .add (.reg r_pos) (.const 1)) (.reg r_v))
      (.assign r_pos (.op .add (.reg r_pos) (.const 2))))

theorem bufPush2_exec {w : ℕ} (a_buf : ℕ) (r_pos r_u r_v : ℕ)
    (pfx : List ℕ) (rem u v : ℕ)
    (hw2 : 2 < 2 ^ w) (hpos_w : pfx.length + 2 < 2 ^ w)
    (hu_w : u < 2 ^ w) (hv_w : v < 2 ^ w)
    {s : State}
    (hbuf : s.arrs a_buf = pfx ++ List.replicate (rem + 2) 0)
    (hrpos : s.regs r_pos = pfx.length)
    (hru : s.regs r_u = u)
    (hrv : s.regs r_v = v) :
    ∃ s' t,
      Exec w (bufPush2 a_buf r_pos r_u r_v) s s' t ∧
      t ≤ 14 ∧
      s'.arrs a_buf = (pfx ++ [u, v]) ++ List.replicate rem 0 ∧
      s'.regs r_pos = (pfx ++ [u, v]).length ∧
      (∀ a : ℕ, a ≠ a_buf → s'.arrs a = s.arrs a) ∧
      (∀ r : ℕ, r ≠ r_pos → s'.regs r = s.regs r) := by
  have hw : 1 < 2 ^ w := by omega
  have hp0_w : pfx.length < 2 ^ w := by omega
  have hp1_w : pfx.length + 1 < 2 ^ w := by omega
  have hlen1 : pfx.length < (s.arrs a_buf).length := by simp [hbuf]
  let s₁ := s.writeArr a_buf pfx.length u
  have hex₁ : Exec w (.write a_buf (.reg r_pos) (.reg r_u)) s s₁ 3 :=
    .write (by simp [Expr.eval, checkWord, hrpos, hp0_w])
      (by simp [Expr.eval, checkWord, hru, hu_w]) hlen1
  have hbuf₁ : s₁.arrs a_buf = (pfx ++ [u]) ++ List.replicate (rem + 1) 0 := by
    simp only [s₁, State.writeArr_arrs_self, hbuf]
    exact set_append_replicate_succ pfx (rem + 1) u
  have hlen2 : pfx.length + 1 < (s₁.arrs a_buf).length := by simp [hbuf₁]
  let s₂ := s₁.writeArr a_buf (pfx.length + 1) v
  have hex₂ : Exec w (.write a_buf (.op .add (.reg r_pos) (.const 1)) (.reg r_v)) s₁ s₂ 5 :=
    .write (by simp [s₁, Expr.eval, BinOp.eval, BinOp.raw, checkWord, hrpos, hp0_w, hw, hp1_w])
      (by simp [s₁, Expr.eval, checkWord, hrv, hv_w]) hlen2
  have hbuf₂ : s₂.arrs a_buf = (pfx ++ [u, v]) ++ List.replicate rem 0 := by
    simp only [s₂, State.writeArr_arrs_self, hbuf₁]
    have hlen_u : (pfx ++ [u]).length = pfx.length + 1 := by simp
    rw [← hlen_u, set_append_replicate_succ (pfx ++ [u]) rem v]
    simp [List.append_assoc]
  let s₃ := s₂.setReg r_pos (pfx.length + 2)
  have hex₃ : Exec w (.assign r_pos (.op .add (.reg r_pos) (.const 2))) s₂ s₃ 4 :=
    .assign (by simp [s₂, s₁, Expr.eval, BinOp.eval, BinOp.raw, checkWord, hrpos, hp0_w, hw2, hpos_w])
  refine ⟨s₃, 3 + (5 + 4), .seq hex₁ (.seq hex₂ hex₃), by omega,
    by simpa [s₃] using hbuf₂,
    by simp [s₃],
    fun a ha => by simp [s₃, s₂, s₁, show (a : Arr) ≠ a_buf from ha],
    fun r hr => by simp [s₃, s₂, s₁, show (r : Reg) ≠ r_pos from hr]⟩

/-- Write `(r_u, r_v, r_m)` at `a_buf[r_pos .. r_pos + 2]`, and increment `r_pos` by `3`. -/
def bufPush3 (a_buf : Arr) (r_pos r_u r_v r_m : Reg) : Cmd :=
  .seq (.write a_buf (.reg r_pos) (.reg r_u))
    (.seq (.write a_buf (.op .add (.reg r_pos) (.const 1)) (.reg r_v))
      (.seq (.write a_buf (.op .add (.reg r_pos) (.const 2)) (.reg r_m))
        (.assign r_pos (.op .add (.reg r_pos) (.const 3)))))

theorem bufPush3_exec {w : ℕ} (a_buf : ℕ) (r_pos r_u r_v r_m : ℕ)
    (pfx : List ℕ) (rem u v m : ℕ)
    (hw3 : 3 < 2 ^ w) (hpos_w : pfx.length + 3 < 2 ^ w)
    (hu_w : u < 2 ^ w) (hv_w : v < 2 ^ w) (hm_w : m < 2 ^ w)
    {s : State}
    (hbuf : s.arrs a_buf = pfx ++ List.replicate (rem + 3) 0)
    (hrpos : s.regs r_pos = pfx.length)
    (hru : s.regs r_u = u)
    (hrv : s.regs r_v = v)
    (hrm : s.regs r_m = m) :
    ∃ s' t,
      Exec w (bufPush3 a_buf r_pos r_u r_v r_m) s s' t ∧
      t ≤ 19 ∧
      s'.arrs a_buf = (pfx ++ [u, v, m]) ++ List.replicate rem 0 ∧
      s'.regs r_pos = (pfx ++ [u, v, m]).length ∧
      (∀ a : ℕ, a ≠ a_buf → s'.arrs a = s.arrs a) ∧
      (∀ r : ℕ, r ≠ r_pos → s'.regs r = s.regs r) := by
  have hw : 1 < 2 ^ w := by omega
  have hw2 : 2 < 2 ^ w := by omega
  have hp0_w : pfx.length < 2 ^ w := by omega
  have hp1_w : pfx.length + 1 < 2 ^ w := by omega
  have hp2_w : pfx.length + 2 < 2 ^ w := by omega
  have hlen1 : pfx.length < (s.arrs a_buf).length := by simp [hbuf]
  let s₁ := s.writeArr a_buf pfx.length u
  have hex₁ : Exec w (.write a_buf (.reg r_pos) (.reg r_u)) s s₁ 3 :=
    .write (by simp [Expr.eval, checkWord, hrpos, hp0_w])
      (by simp [Expr.eval, checkWord, hru, hu_w]) hlen1
  have hbuf₁ : s₁.arrs a_buf = (pfx ++ [u]) ++ List.replicate (rem + 2) 0 := by
    simp only [s₁, State.writeArr_arrs_self, hbuf]
    exact set_append_replicate_succ pfx (rem + 2) u
  have hlen2 : pfx.length + 1 < (s₁.arrs a_buf).length := by simp [hbuf₁]
  let s₂ := s₁.writeArr a_buf (pfx.length + 1) v
  have hex₂ : Exec w (.write a_buf (.op .add (.reg r_pos) (.const 1)) (.reg r_v)) s₁ s₂ 5 :=
    .write (by simp [s₁, Expr.eval, BinOp.eval, BinOp.raw, checkWord, hrpos, hp0_w, hw, hp1_w])
      (by simp [s₁, Expr.eval, checkWord, hrv, hv_w]) hlen2
  have hbuf₂ : s₂.arrs a_buf = (pfx ++ [u, v]) ++ List.replicate (rem + 1) 0 := by
    simp only [s₂, State.writeArr_arrs_self, hbuf₁]
    have hlen_u : (pfx ++ [u]).length = pfx.length + 1 := by simp
    rw [← hlen_u, set_append_replicate_succ (pfx ++ [u]) (rem + 1) v]
    simp [List.append_assoc]
  have hlen3 : pfx.length + 2 < (s₂.arrs a_buf).length := by simp [hbuf₂]
  let s₃ := s₂.writeArr a_buf (pfx.length + 2) m
  have hex₃ : Exec w (.write a_buf (.op .add (.reg r_pos) (.const 2)) (.reg r_m)) s₂ s₃ 5 :=
    .write (by simp [s₂, s₁, Expr.eval, BinOp.eval, BinOp.raw, checkWord, hrpos, hp0_w, hw2, hp2_w])
      (by simp [s₂, s₁, Expr.eval, checkWord, hrm, hm_w]) hlen3
  have hbuf₃ : s₃.arrs a_buf = (pfx ++ [u, v, m]) ++ List.replicate rem 0 := by
    simp only [s₃, State.writeArr_arrs_self, hbuf₂]
    have hlen_uv : (pfx ++ [u, v]).length = pfx.length + 2 := by simp
    rw [← hlen_uv, set_append_replicate_succ (pfx ++ [u, v]) rem m]
    simp [List.append_assoc]
  let s₄ := s₃.setReg r_pos (pfx.length + 3)
  have hex₄ : Exec w (.assign r_pos (.op .add (.reg r_pos) (.const 3))) s₃ s₄ 4 :=
    .assign (by simp [s₃, s₂, s₁, Expr.eval, BinOp.eval, BinOp.raw, checkWord, hrpos, hp0_w, hw3, hpos_w])
  refine ⟨s₄, 3 + (5 + (5 + 4)), .seq hex₁ (.seq hex₂ (.seq hex₃ hex₄)), by omega,
    by simpa [s₄] using hbuf₃,
    by simp [s₄],
    fun a ha => by simp [s₄, s₃, s₂, s₁, show (a : Arr) ≠ a_buf from ha],
    fun r hr => by simp [s₄, s₃, s₂, s₁, show (r : Reg) ≠ r_pos from hr]⟩

/-! ### Section 3.3: Capping Multiplicities (`capMultiDigraphProg`) -/

theorem all_lt_flatTriples {n w : ℕ} (G : MultiDigraph n) (pairs : List (Fin n × Fin n))
    (hn_w : n < 2 ^ w) (hm_w : ∀ p ∈ pairs, G.edgeMult p.1 p.2 < 2 ^ w) :
    ∀ x ∈ G.flatTriples pairs, x < 2 ^ w := by
  induction pairs with
  | nil => simp [MultiDigraph.flatTriples]
  | cons p ps ih =>
    rcases p with ⟨u, v⟩
    intro x hx
    simp only [MultiDigraph.flatTriples, List.mem_cons] at hx
    rcases hx with rfl | rfl | rfl | hx
    · exact Nat.lt_trans u.2 hn_w
    · exact Nat.lt_trans v.2 hn_w
    · exact hm_w (u, v) (by simp)
    · exact ih (fun p hp => hm_w p (List.mem_cons_of_mem _ hp)) x hx

/-- Loop body of `capMultiDigraphProg`: reads `(u_k, v_k)` from `a_src`, reads the capped
multiplicity `m = min mult_k (if u_k = v_k then δ else δ + 1)` via `Expr.readMin`, and if `0 < m`
appends `(u_k, v_k, m)` to `a_buf` and updates `m'_out` (`r_base + 1`) and `numEdges_out`
(`r_base + 2`). -/
def capMultiDigraphBody (δ : ℕ) (a_src a_buf : Arr) (r_base : Reg) : Cmd :=
  .seq (readTripleEndpoints a_src (r_base + 4) (r_base + 6) (r_base + 7) (r_base + 8))
    (.seq
      (.ite (.op .eq (.reg (r_base + 7)) (.reg (r_base + 8)))
        (.assign (r_base + 9)
          (.readMin a_src (.op .add (.reg (r_base + 6)) (.const 2)) (.const δ)))
        (.assign (r_base + 9)
          (.readMin a_src (.op .add (.reg (r_base + 6)) (.const 2)) (.const (δ + 1)))))
      (.ite (.op .lt (.const 0) (.reg (r_base + 9)))
        (.seq (bufPush3 a_buf (r_base + 5) (r_base + 7) (r_base + 8) (r_base + 9))
          (.seq (.assign (r_base + 1) (.op .add (.reg (r_base + 1)) (.const 1)))
            (.assign (r_base + 2) (.op .add (.reg (r_base + 2)) (.reg (r_base + 9))))))
        .skip))

/-- Cap edge multiplicities of `G` in `a_src` (`≤ δ` loops, `≤ δ + 1` non-loops, GM XIII (6.5)
step (1)), writing `(G.cap δ).enc` into `a_dst` using scratch buffer `a_buf` and registers
`r_base .. r_base + 9`. At termination:
- `s'.arrs a_dst = (G.cap δ).enc`
- `s'.regs r_base = n`
- `s'.regs (r_base + 1) = (G.cap δ).numActivePairs`
- `s'.regs (r_base + 2) = (G.cap δ).numEdges`. -/
def capMultiDigraphProg (δ : ℕ) (a_src a_buf a_dst : Arr) (r_base : Reg) : Cmd :=
  .seq (.assign r_base (.read a_src (.const 0)))
    (.seq (.assign (r_base + 3) (.read a_src (.const 1)))
      (.seq (.assign (r_base + 1) (.const 0))
        (.seq (.assign (r_base + 2) (.const 0))
          (.seq (.assign (r_base + 5)
              (.op .add (.const 2) (.op .mul (.const 3) (.reg (r_base + 3)))))
            (.seq (.alloc a_buf (.reg (r_base + 5)))
              (.seq (.write a_buf (.const 0) (.reg r_base))
                (.seq (.assign (r_base + 5) (.const 2))
                  (.seq (.assign (r_base + 4) (.const 0))
                    (.seq (forUp (r_base + 4) (.reg (r_base + 3))
                        (capMultiDigraphBody δ a_src a_buf r_base))
                      (.seq (.write a_buf (.const 1) (.reg (r_base + 1)))
                        (readSliceProg a_buf (.const 0) a_dst
                          (.reg (r_base + 5)) (r_base + 6))))))))))))

theorem capMultiDigraphLoop_exec {w n : ℕ} (G : MultiDigraph n) (δ : ℕ) (extra : List ℕ)
    (a_src a_buf : ℕ) (r_base : ℕ)
    (hne_sb : a_src ≠ a_buf)
    (hw3 : 3 < 2 ^ w) (hn_w : n < 2 ^ w) (hδ_w : δ + 1 < 2 ^ w)
    (hm3_w : 2 + 3 * G.numActivePairs < 2 ^ w)
    (suff pref : List (Fin n × Fin n))
    (hsplit : G.activePairsList = pref ++ suff)
    (pfx : List ℕ) (extra_buf m_acc e_acc : ℕ)
    (hpfx_len : pfx.length = 2 + 3 * m_acc)
    (hm_bound :
      m_acc + (suff.filter (fun p => decide (0 < (G.cap δ).edgeMult p.1 p.2))).length ≤
        G.numActivePairs)
    (he_bound : e_acc + MultiDigraph.sumEdgeMult (G.cap δ) suff < 2 ^ w)
    {s : State}
    (hsrc : s.arrs a_src = G.enc ++ extra)
    (hbuf : s.arrs a_buf = pfx ++ List.replicate (3 * suff.length + extra_buf) 0)
    (hr0 : s.regs r_base = n)
    (hr1 : s.regs (r_base + 1) = m_acc)
    (hr2 : s.regs (r_base + 2) = e_acc)
    (hr3 : s.regs (r_base + 3) = G.numActivePairs)
    (hr4 : s.regs (r_base + 4) = pref.length)
    (hr5 : s.regs (r_base + 5) = pfx.length) :
    ∃ s' t extra_buf',
      Exec w (forUp (r_base + 4) (.reg (r_base + 3)) (capMultiDigraphBody δ a_src a_buf r_base))
        s s' t ∧
      t ≤ 3 + 62 * suff.length ∧
      s'.arrs a_buf = (pfx ++ MultiDigraph.capTriplesAux G δ suff) ++ List.replicate extra_buf' 0 ∧
      s'.regs r_base = n ∧
      s'.regs (r_base + 1) =
        m_acc + (suff.filter (fun p => decide (0 < (G.cap δ).edgeMult p.1 p.2))).length ∧
      s'.regs (r_base + 2) = e_acc + MultiDigraph.sumEdgeMult (G.cap δ) suff ∧
      s'.regs (r_base + 5) = (pfx ++ MultiDigraph.capTriplesAux G δ suff).length ∧
      (∀ a : ℕ, a ≠ a_buf → s'.arrs a = s.arrs a) ∧
      (∀ r < r_base, s'.regs r = s.regs r) := by
  have hw : 1 < 2 ^ w := by omega
  have hw2 : 2 < 2 ^ w := by omega
  have h0_w : 0 < 2 ^ w := by omega
  have hδ0_w : δ < 2 ^ w := by omega
  have hm'_w : G.numActivePairs < 2 ^ w := by omega
  induction suff generalizing pref pfx extra_buf m_acc e_acc s with
  | nil =>
    have hk_eq : pref.length = G.numActivePairs := by
      have := congrArg List.length hsplit
      simp [MultiDigraph.numActivePairs] at this ⊢
      omega
    have hcond : (Expr.op .lt (.reg (r_base + 4)) (.reg (r_base + 3))).eval w s = some 0 := by
      simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hr4, hr3, hk_eq, hm'_w, h0_w]
    refine ⟨s, 3, extra_buf, .while_false hcond, by omega,
      by simpa [MultiDigraph.capTriplesAux] using hbuf,
      hr0, by simpa using hr1, by simpa [MultiDigraph.sumEdgeMult] using hr2,
      by simpa [MultiDigraph.capTriplesAux] using hr5,
      fun _ _ => rfl, fun _ _ => rfl⟩
  | cons p ps ih =>
    rcases p with ⟨u, v⟩
    let k := pref.length
    obtain ⟨hk_lt, hget_k⟩ := getElem_of_eq_append_cons hsplit
    have hk_m' : k < G.numActivePairs := hk_lt
    have hk_w : k < 2 ^ w := by omega
    have hcond : (Expr.op .lt (.reg (r_base + 4)) (.reg (r_base + 3))).eval w s = some 1 := by
      simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hr4, hr3, k, hk_m', hk_w, hm'_w, hw]
    -- 1. readTripleEndpoints
    rcases readTripleEndpoints_exec G extra a_src (r_base + 4) (r_base + 6) (r_base + 7) (r_base + 8)
        k s (by omega) (by omega) (by omega) hw3 hn_w hm3_w hk_m' hsrc hr4 with
      ⟨s₁, t₁, hex₁, ht₁, hr6_1, hr7_1, hr8_1, harr₁, hreg₁⟩
    have hget_u : (G.activePairsList[k]'hk_m').1 = u := congrArg Prod.fst hget_k
    have hget_v : (G.activePairsList[k]'hk_m').2 = v := congrArg Prod.snd hget_k
    rw [hget_u] at hr7_1
    rw [hget_v] at hr8_1
    have hu_w : u.1 < 2 ^ w := Nat.lt_trans u.2 hn_w
    have hv_w : v.1 < 2 ^ w := Nat.lt_trans v.2 hn_w
    have hidx_w : 2 + 3 * k < 2 ^ w := by omega
    have hidx2_w : 2 + 3 * k + 2 < 2 ^ w := by omega
    obtain ⟨hlen_m, hget_m⟩ := enc_getElem_triple_mult G extra hsrc hk_m'
    rw [hget_u, hget_v] at hget_m
    have hlen_m₁ : 2 + 3 * k + 2 < (s₁.arrs a_src).length := by rw [harr₁]; exact hlen_m
    have hget_m₁ : (s₁.arrs a_src)[2 + 3 * k + 2]'hlen_m₁ = G.edgeMult u v := by
      simp only [harr₁]; exact hget_m
    -- 2. ite on r_u = r_v to read capped multiplicity into r_base + 9
    let m := (G.cap δ).edgeMult u v
    have hm_w : m < 2 ^ w := by
      have := G.cap_edgeMult_le_succ δ u v; omega
    have hex_read_m :
        ∃ t_m ≤ 11,
          Exec w
            (.ite (.op .eq (.reg (r_base + 7)) (.reg (r_base + 8)))
              (.assign (r_base + 9)
                (.readMin a_src (.op .add (.reg (r_base + 6)) (.const 2)) (.const δ)))
              (.assign (r_base + 9)
                (.readMin a_src (.op .add (.reg (r_base + 6)) (.const 2)) (.const (δ + 1)))))
            s₁ (s₁.setReg (r_base + 9) m) t_m := by
      by_cases huv : u = v
      · have huv_val : u.1 = v.1 := congrArg Fin.val huv
        have hcond_uv : (Expr.op .eq (.reg (r_base + 7)) (.reg (r_base + 8))).eval w s₁ = some 1 := by
          simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hr7_1, hr8_1, huv_val, hv_w, hw]
        have hm_eq : m = Nat.min (G.edgeMult u v) δ := by simp [m, huv]
        have heval_rd :
            (Expr.readMin a_src (.op .add (.reg (r_base + 6)) (.const 2)) (.const δ)).eval w s₁ =
              some m := by
          simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hr6_1, hidx_w, hw2, hidx2_w,
            hδ0_w, hlen_m₁, hget_m₁, ← hm_eq, hm_w]
        exact ⟨3 + 7, by omega, .ite_true hcond_uv (by omega) (.assign heval_rd)⟩
      · have huv_val : u.1 ≠ v.1 := fun h => huv (Fin.ext h)
        have hcond_uv : (Expr.op .eq (.reg (r_base + 7)) (.reg (r_base + 8))).eval w s₁ = some 0 := by
          simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hr7_1, hr8_1, huv_val, hu_w, hv_w, h0_w]
        have hm_eq : m = Nat.min (G.edgeMult u v) (δ + 1) := by simp [m, huv]
        have heval_rd :
            (Expr.readMin a_src (.op .add (.reg (r_base + 6)) (.const 2)) (.const (δ + 1))).eval w s₁ =
              some m := by
          simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hr6_1, hidx_w, hw2, hidx2_w,
            hδ_w, hlen_m₁, hget_m₁, ← hm_eq, hm_w]
        exact ⟨3 + 7, by omega, .ite_false hcond_uv (.assign heval_rd)⟩
    rcases hex_read_m with ⟨t₂, ht₂, hex₂⟩
    let s₂ := s₁.setReg (r_base + 9) m
    have hsplit' : G.activePairsList = (pref ++ [(u, v)]) ++ ps := by
      simp [hsplit, List.append_assoc]
    -- 3. ite on 0 < (G.cap δ).edgeMult u v
    by_cases hm_pos : 0 < (G.cap δ).edgeMult u v
    · have hm_pos' : 0 < m := hm_pos
      have hcond_m : (Expr.op .lt (.const 0) (.reg (r_base + 9))).eval w s₂ = some 1 := by
        simp [s₂, Expr.eval, BinOp.eval, BinOp.raw, checkWord, h0_w, hm_w, hm_pos', hw]
      have hbuf₂ : s₂.arrs a_buf = pfx ++ List.replicate ((3 * ps.length + extra_buf) + 3) 0 := by
        have hlen_eq : 3 * ((u, v) :: ps).length + extra_buf = (3 * ps.length + extra_buf) + 3 := by
          simp; omega
        rw [← hlen_eq]
        simpa [s₂, harr₁] using hbuf
      have hr5_2 : s₂.regs (r_base + 5) = pfx.length := by
        simp [s₂, hreg₁ (r_base + 5) (by omega) (by omega) (by omega), hr5]
      have hr7_2 : s₂.regs (r_base + 7) = u.1 := by simp [s₂, hr7_1]
      have hr8_2 : s₂.regs (r_base + 8) = v.1 := by simp [s₂, hr8_1]
      have hr9_2 : s₂.regs (r_base + 9) = m := by simp [s₂]
      have hm_acc_lt : m_acc + 1 ≤ G.numActivePairs := by
        have hflt :
            (List.filter (fun p => decide (0 < (G.cap δ).edgeMult p.1 p.2)) ((u, v) :: ps)).length =
              (List.filter (fun p => decide (0 < (G.cap δ).edgeMult p.1 p.2)) ps).length + 1 := by
          simp only [List.filter_cons, hm_pos, decide_true, ↓reduceIte, List.length_cons]
        omega
      have hpos_w : pfx.length + 3 < 2 ^ w := by omega
      rcases bufPush3_exec a_buf (r_base + 5) (r_base + 7) (r_base + 8) (r_base + 9)
          pfx (3 * ps.length + extra_buf) u.1 v.1 m hw3 hpos_w hu_w hv_w hm_w
          hbuf₂ hr5_2 hr7_2 hr8_2 hr9_2 with
        ⟨s₃, t₃, hex₃, ht₃, hbuf₃, hr5_3, harr₃, hreg₃⟩
      have hr1_3 : s₃.regs (r_base + 1) = m_acc := by
        rw [hreg₃ _ (by omega)]
        simp [s₂, hreg₁ (r_base + 1) (by omega) (by omega) (by omega), hr1]
      have hm_acc_w : m_acc < 2 ^ w := by omega
      have hm_acc1_w : m_acc + 1 < 2 ^ w := by omega
      let s₄ := s₃.setReg (r_base + 1) (m_acc + 1)
      have hex₄ : Exec w (.assign (r_base + 1) (.op .add (.reg (r_base + 1)) (.const 1))) s₃ s₄ 4 :=
        .assign (by simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hr1_3, hm_acc_w, hw, hm_acc1_w])
      have hr2_4 : s₄.regs (r_base + 2) = e_acc := by
        simp only [s₄, State.setReg_regs_ne _ _ (show (r_base + 2 : Reg) ≠ r_base + 1 by omega)]
        rw [hreg₃ _ (by omega)]
        simp [s₂, hreg₁ (r_base + 2) (by omega) (by omega) (by omega), hr2]
      have hr9_4 : s₄.regs (r_base + 9) = m := by
        simp only [s₄, State.setReg_regs_ne _ _ (show (r_base + 9 : Reg) ≠ r_base + 1 by omega)]
        rw [hreg₃ _ (by omega)]
        exact hr9_2
      have he_acc_w : e_acc < 2 ^ w := by
        simp only [MultiDigraph.sumEdgeMult] at he_bound; omega
      have he_accm_w : e_acc + m < 2 ^ w := by
        change e_acc + ((G.cap δ).edgeMult u v + MultiDigraph.sumEdgeMult (G.cap δ) ps) < 2 ^ w at he_bound
        omega
      let s₅ := s₄.setReg (r_base + 2) (e_acc + m)
      have hex₅ : Exec w (.assign (r_base + 2) (.op .add (.reg (r_base + 2)) (.reg (r_base + 9))))
          s₄ s₅ 4 :=
        .assign (by simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hr2_4, hr9_4,
          he_acc_w, hm_w, he_accm_w])
      have hex_ite_m : Exec w
          (.ite (.op .lt (.const 0) (.reg (r_base + 9)))
            (.seq (bufPush3 a_buf (r_base + 5) (r_base + 7) (r_base + 8) (r_base + 9))
              (.seq (.assign (r_base + 1) (.op .add (.reg (r_base + 1)) (.const 1)))
                (.assign (r_base + 2) (.op .add (.reg (r_base + 2)) (.reg (r_base + 9))))))
            .skip)
          s₂ s₅ (3 + (t₃ + (4 + 4))) :=
        .ite_true hcond_m (by omega) (.seq hex₃ (.seq hex₄ hex₅))
      have hex_body : Exec w (capMultiDigraphBody δ a_src a_buf r_base) s s₅
          (t₁ + (t₂ + (3 + (t₃ + (4 + 4))))) :=
        .seq hex₁ (.seq hex₂ hex_ite_m)
      have hr4_5 : s₅.regs (r_base + 4) = k := by
        simp only [s₅, s₄, State.setReg_regs_ne _ _ (show (r_base + 4 : Reg) ≠ r_base + 2 by omega),
          State.setReg_regs_ne _ _ (show (r_base + 4 : Reg) ≠ r_base + 1 by omega)]
        rw [hreg₃ _ (by omega)]
        simp [s₂, hreg₁ (r_base + 4) (by omega) (by omega) (by omega), hr4, k]
      let s₆ := s₅.setReg (r_base + 4) (k + 1)
      have hex_inc : Exec w (.assign (r_base + 4) (.op .add (.reg (r_base + 4)) (.const 1)))
          s₅ s₆ 4 :=
        .assign (by simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hr4_5, hk_w, hw,
          show k + 1 < 2 ^ w by omega])
      have hsrc₆ : s₆.arrs a_src = G.enc ++ extra := by
        simp only [s₆, s₅, s₄, State.setReg_arrs]
        rw [harr₃ a_src hne_sb]
        simp [s₂, harr₁, hsrc]
      have hbuf₆ : s₆.arrs a_buf = (pfx ++ [u.1, v.1, m]) ++ List.replicate (3 * ps.length + extra_buf) 0 := by
        simpa [s₆, s₅, s₄] using hbuf₃
      have hm_bound' :
          (m_acc + 1) + (ps.filter (fun p => decide (0 < (G.cap δ).edgeMult p.1 p.2))).length ≤
            G.numActivePairs := by
        have hflt :
            (List.filter (fun p => decide (0 < (G.cap δ).edgeMult p.1 p.2)) ((u, v) :: ps)).length =
              (List.filter (fun p => decide (0 < (G.cap δ).edgeMult p.1 p.2)) ps).length + 1 := by
          simp only [List.filter_cons, hm_pos, decide_true, ↓reduceIte, List.length_cons]
        omega
      have he_bound' : (e_acc + m) + MultiDigraph.sumEdgeMult (G.cap δ) ps < 2 ^ w := by
        change e_acc + ((G.cap δ).edgeMult u v + MultiDigraph.sumEdgeMult (G.cap δ) ps) < 2 ^ w at he_bound
        omega
      rcases ih (pref ++ [(u, v)]) hsplit' (pfx ++ [u.1, v.1, m]) extra_buf (m_acc + 1) (e_acc + m)
          (by simp [hpfx_len]; omega) hm_bound' he_bound' hsrc₆ hbuf₆
          (by simp only [s₆, s₅, s₄, State.setReg_regs_ne _ _ (by omega : (r_base : Reg) ≠ r_base + 4),
              State.setReg_regs_ne _ _ (by omega : (r_base : Reg) ≠ r_base + 2),
              State.setReg_regs_ne _ _ (by omega : (r_base : Reg) ≠ r_base + 1)];
              rw [hreg₃ _ (by omega)];
              simp [s₂, hreg₁ r_base (by omega) (by omega) (by omega), hr0])
          (by simp [s₆, s₅, s₄])
          (by simp [s₆, s₅])
          (by simp only [s₆, s₅, s₄,
              State.setReg_regs_ne _ _ (by omega : (r_base + 3 : Reg) ≠ r_base + 4),
              State.setReg_regs_ne _ _ (by omega : (r_base + 3 : Reg) ≠ r_base + 2),
              State.setReg_regs_ne _ _ (by omega : (r_base + 3 : Reg) ≠ r_base + 1)];
              rw [hreg₃ _ (by omega)];
              simp [s₂, hreg₁ (r_base + 3) (by omega) (by omega) (by omega), hr3])
          (by simp [s₆, k])
          (by simp [s₆, s₅, s₄, hr5_3]) with
        ⟨s₇, t₇, extra_buf', hex₇, ht₇, hbuf₇, hr0_7, hr1_7, hr2_7, hr5_7, harr₇, hreg₇⟩
      refine ⟨s₇, 3 + ((t₁ + (t₂ + (3 + (t₃ + (4 + 4))))) + 4) + t₇, extra_buf',
        .while_true hcond (by omega) (.seq hex_body hex_inc) hex₇,
        by simp only [List.length_cons]; omega,
        by simp only [MultiDigraph.capTriplesAux, hm_pos, ↓reduceIte]; simpa [m, List.append_assoc] using hbuf₇,
        hr0_7,
        by rw [hr1_7]
           have hflt :
               (List.filter (fun p => decide (0 < (G.cap δ).edgeMult p.1 p.2)) ((u, v) :: ps)).length =
                 (List.filter (fun p => decide (0 < (G.cap δ).edgeMult p.1 p.2)) ps).length + 1 := by
             simp only [List.filter_cons, hm_pos, decide_true, ↓reduceIte, List.length_cons]
           omega,
        by rw [hr2_7]; change e_acc + m + MultiDigraph.sumEdgeMult (G.cap δ) ps =
             e_acc + (m + MultiDigraph.sumEdgeMult (G.cap δ) ps); omega,
        by simp only [MultiDigraph.capTriplesAux, hm_pos, ↓reduceIte]; simpa [m, List.append_assoc] using hr5_7,
        fun a ha => by
          rw [harr₇ a ha]
          simp only [s₆, s₅, s₄, State.setReg_arrs]
          rw [harr₃ a ha]
          simp [s₂, harr₁],
        fun r hr => by
          rw [hreg₇ r hr]
          simp only [s₆, s₅, s₄,
            State.setReg_regs_ne _ _ (by omega : (r : Reg) ≠ r_base + 4),
            State.setReg_regs_ne _ _ (by omega : (r : Reg) ≠ r_base + 2),
            State.setReg_regs_ne _ _ (by omega : (r : Reg) ≠ r_base + 1)]
          rw [hreg₃ r (by omega)]
          simp [s₂, State.setReg_regs_ne _ _ (by omega : (r : Reg) ≠ r_base + 9),
            hreg₁ r (by omega) (by omega) (by omega)]⟩
    · have hm_pos' : ¬(0 < m) := hm_pos
      have hcond_m : (Expr.op .lt (.const 0) (.reg (r_base + 9))).eval w s₂ = some 0 := by
        simp [s₂, Expr.eval, BinOp.eval, BinOp.raw, checkWord, h0_w, hm_w, hm_pos']
      have hex_ite_m : Exec w
          (.ite (.op .lt (.const 0) (.reg (r_base + 9)))
            (.seq (bufPush3 a_buf (r_base + 5) (r_base + 7) (r_base + 8) (r_base + 9))
              (.seq (.assign (r_base + 1) (.op .add (.reg (r_base + 1)) (.const 1)))
                (.assign (r_base + 2) (.op .add (.reg (r_base + 2)) (.reg (r_base + 9))))))
            .skip)
          s₂ s₂ (3 + 1) :=
        .ite_false hcond_m (.skip s₂)
      have hex_body : Exec w (capMultiDigraphBody δ a_src a_buf r_base) s s₂
          (t₁ + (t₂ + (3 + 1))) :=
        .seq hex₁ (.seq hex₂ hex_ite_m)
      have hr4_2 : s₂.regs (r_base + 4) = k := by
        simp [s₂, hreg₁ (r_base + 4) (by omega) (by omega) (by omega), hr4, k]
      let s₃ := s₂.setReg (r_base + 4) (k + 1)
      have hex_inc : Exec w (.assign (r_base + 4) (.op .add (.reg (r_base + 4)) (.const 1)))
          s₂ s₃ 4 :=
        .assign (by simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hr4_2, hk_w, hw,
          show k + 1 < 2 ^ w by omega])
      have hsrc₃ : s₃.arrs a_src = G.enc ++ extra := by
        simp [s₃, s₂, harr₁, hsrc]
      have hbuf₃ : s₃.arrs a_buf = pfx ++ List.replicate (3 * ps.length + (extra_buf + 3)) 0 := by
        have hlen_eq : 3 * ((u, v) :: ps).length + extra_buf = 3 * ps.length + (extra_buf + 3) := by
          simp; omega
        rw [← hlen_eq]
        simpa [s₃, s₂, harr₁] using hbuf
      have hm_bound' :
          m_acc + (ps.filter (fun p => decide (0 < (G.cap δ).edgeMult p.1 p.2))).length ≤
            G.numActivePairs := by
        have hflt :
            (List.filter (fun p => decide (0 < (G.cap δ).edgeMult p.1 p.2)) ((u, v) :: ps)).length =
              (List.filter (fun p => decide (0 < (G.cap δ).edgeMult p.1 p.2)) ps).length := by
          simp only [List.filter_cons, hm_pos, decide_false, Bool.false_eq_true, ↓reduceIte]
        omega
      have hm_zero : (G.cap δ).edgeMult u v = 0 := by omega
      have he_bound' : e_acc + MultiDigraph.sumEdgeMult (G.cap δ) ps < 2 ^ w := by
        simp only [MultiDigraph.sumEdgeMult] at he_bound; omega
      rcases ih (pref ++ [(u, v)]) hsplit' pfx (extra_buf + 3) m_acc e_acc
          hpfx_len hm_bound' he_bound' hsrc₃ hbuf₃
          (by simp [s₃, s₂, hreg₁ r_base (by omega) (by omega) (by omega), hr0])
          (by simp [s₃, s₂, hreg₁ (r_base + 1) (by omega) (by omega) (by omega), hr1])
          (by simp [s₃, s₂, hreg₁ (r_base + 2) (by omega) (by omega) (by omega), hr2])
          (by simp [s₃, s₂, hreg₁ (r_base + 3) (by omega) (by omega) (by omega), hr3])
          (by simp [s₃, k])
          (by simp [s₃, s₂, hreg₁ (r_base + 5) (by omega) (by omega) (by omega), hr5]) with
        ⟨s₄, t₄, extra_buf', hex₄, ht₄, hbuf₄, hr0_4, hr1_4, hr2_4, hr5_4, harr₄, hreg₄⟩
      refine ⟨s₄, 3 + ((t₁ + (t₂ + (3 + 1))) + 4) + t₄, extra_buf',
        .while_true hcond (by omega) (.seq hex_body hex_inc) hex₄,
        by simp only [List.length_cons]; omega,
        by simp only [MultiDigraph.capTriplesAux, hm_pos, ↓reduceIte]; exact hbuf₄,
        hr0_4,
        by rw [hr1_4]
           have hflt :
               (List.filter (fun p => decide (0 < (G.cap δ).edgeMult p.1 p.2)) ((u, v) :: ps)).length =
                 (List.filter (fun p => decide (0 < (G.cap δ).edgeMult p.1 p.2)) ps).length := by
             simp only [List.filter_cons, hm_pos, decide_false, Bool.false_eq_true, ↓reduceIte]
           omega,
        by rw [hr2_4]; change e_acc + MultiDigraph.sumEdgeMult (G.cap δ) ps =
             e_acc + ((G.cap δ).edgeMult u v + MultiDigraph.sumEdgeMult (G.cap δ) ps); omega,
        by simp only [MultiDigraph.capTriplesAux, hm_pos, ↓reduceIte]; exact hr5_4,
        fun a ha => by rw [harr₄ a ha]; simp [s₃, s₂, harr₁],
        fun r hr => by
          rw [hreg₄ r hr]
          simp [s₃, s₂,
            State.setReg_regs_ne _ _ (by omega : (r : Reg) ≠ r_base + 4),
            State.setReg_regs_ne _ _ (by omega : (r : Reg) ≠ r_base + 9),
            hreg₁ r (by omega) (by omega) (by omega)]⟩

/-- Specification for `capMultiDigraphProg`: caps multiplicities of `G` (`≤ δ` loops, `≤ δ + 1`
non-loops) in `O(G.numActivePairs + 1)` steps, writing `(G.cap δ).enc` into `a_dst` and setting
`r_base = n`, `r_base + 1 = (G.cap δ).numActivePairs`, and `r_base + 2 = (G.cap δ).numEdges`.
Works even when `G` has unbounded multiplicities `≥ 2 ^ w` in `a_src`. -/
theorem capMultiDigraphProg_exec {w n : ℕ} (G : MultiDigraph n) (δ : ℕ) (extra : List ℕ)
    (a_src a_buf a_dst : ℕ) (r_base : ℕ)
    (hne_sb : a_src ≠ a_buf) (hne_bd : a_buf ≠ a_dst)
    (hw3 : 3 < 2 ^ w) (hn_w : n < 2 ^ w) (hδ_w : δ + 1 < 2 ^ w)
    (hm3_w : 2 + 3 * G.numActivePairs < 2 ^ w)
    (hedges_w : (G.cap δ).numEdges < 2 ^ w)
    {s : State}
    (hsrc : s.arrs a_src = G.enc ++ extra) :
    ∃ s' t,
      Exec w (capMultiDigraphProg δ a_src a_buf a_dst r_base) s s' t ∧
      t ≤ 115 * G.numActivePairs + 80 ∧
      s'.arrs a_dst = (G.cap δ).enc ∧
      s'.regs r_base = n ∧
      s'.regs (r_base + 1) = (G.cap δ).numActivePairs ∧
      s'.regs (r_base + 2) = (G.cap δ).numEdges ∧
      (∀ a : ℕ, a ≠ a_buf → a ≠ a_dst → s'.arrs a = s.arrs a) ∧
      (∀ r < r_base, s'.regs r = s.regs r) := by
  have hw : 1 < 2 ^ w := by omega
  have hw2 : 2 < 2 ^ w := by omega
  have h0_w : 0 < 2 ^ w := by omega
  have hm'_w : G.numActivePairs < 2 ^ w := by omega
  have h3m'_w : 3 * G.numActivePairs < 2 ^ w := by omega
  -- 1. r_base := a_src[0]
  obtain ⟨h0_len, h0_val⟩ := enc_getElem_zero G extra hsrc
  let s₁ := s.setReg r_base n
  have hex₁ : Exec w (.assign r_base (.read a_src (.const 0))) s s₁ 3 :=
    .assign (by simp [Expr.eval, checkWord, h0_w, h0_len, h0_val, hn_w])
  -- 2. r_base + 3 := a_src[1]
  obtain ⟨h1_len, h1_val⟩ := enc_getElem_one G extra hsrc
  let s₂ := s₁.setReg (r_base + 3) G.numActivePairs
  have hex₂ : Exec w (.assign (r_base + 3) (.read a_src (.const 1))) s₁ s₂ 3 :=
    .assign (by simp [s₁, Expr.eval, checkWord, hw, h1_len, h1_val, hm'_w])
  -- 3. r_base + 1 := 0
  let s₃ := s₂.setReg (r_base + 1) 0
  have hex₃ : Exec w (.assign (r_base + 1) (.const 0)) s₂ s₃ 2 :=
    .assign (by simp [Expr.eval, checkWord, h0_w])
  -- 4. r_base + 2 := 0
  let s₄ := s₃.setReg (r_base + 2) 0
  have hex₄ : Exec w (.assign (r_base + 2) (.const 0)) s₃ s₄ 2 :=
    .assign (by simp [Expr.eval, checkWord, h0_w])
  -- 5. r_base + 5 := 2 + 3 * (r_base + 3)
  let s₅ := s₄.setReg (r_base + 5) (2 + 3 * G.numActivePairs)
  have hex₅ : Exec w (.assign (r_base + 5)
      (.op .add (.const 2) (.op .mul (.const 3) (.reg (r_base + 3))))) s₄ s₅ 6 :=
    .assign (by simp [s₄, s₃, s₂, Expr.eval, BinOp.eval, BinOp.raw, checkWord,
      hw2, hw3, hm'_w, h3m'_w, hm3_w])
  -- 6. alloc a_buf (r_base + 5)
  let s₆ := s₅.setArr a_buf (List.replicate (2 + 3 * G.numActivePairs) 0)
  have hex₆ : Exec w (.alloc a_buf (.reg (r_base + 5))) s₅ s₆ (1 + (2 + 3 * G.numActivePairs)) :=
    .alloc (by simp [s₅, Expr.eval, checkWord, hm3_w])
  -- 7. write a_buf 0 r_base
  let s₇ := s₆.writeArr a_buf 0 n
  have hex₇ : Exec w (.write a_buf (.const 0) (.reg r_base)) s₆ s₇ 3 :=
    .write (by simp [Expr.eval, checkWord, h0_w])
      (by simp [s₆, s₅, s₄, s₃, s₂, s₁, Expr.eval, checkWord, hn_w])
      (by simp [s₆])
  -- 8. r_base + 5 := 2
  let s₈ := s₇.setReg (r_base + 5) 2
  have hex₈ : Exec w (.assign (r_base + 5) (.const 2)) s₇ s₈ 2 :=
    .assign (by simp [Expr.eval, checkWord, hw2])
  -- 9. r_base + 4 := 0
  let s₉ := s₈.setReg (r_base + 4) 0
  have hex₉ : Exec w (.assign (r_base + 4) (.const 0)) s₈ s₉ 2 :=
    .assign (by simp [Expr.eval, checkWord, h0_w])
  -- 10. capMultiDigraphLoop_exec
  have hbuf₉ : s₉.arrs a_buf = [n, 0] ++ List.replicate (3 * G.activePairsList.length + 0) 0 := by
    simp only [s₉, s₈, s₇, s₆, State.setReg_arrs, State.writeArr_arrs_self,
      State.setArr_arrs_self]
    have hrep : 2 + 3 * G.numActivePairs = 1 + (1 + 3 * G.activePairsList.length) := by
      simp [MultiDigraph.numActivePairs]; omega
    rw [hrep, List.replicate_add, List.replicate_add]
    rfl
  have hm_bound₉ :
      0 + (G.activePairsList.filter (fun p => decide (0 < (G.cap δ).edgeMult p.1 p.2))).length ≤
        G.numActivePairs := by
    simp only [Nat.zero_add, MultiDigraph.numActivePairs]
    exact List.length_filter_le _ _
  have he_bound₉ : 0 + MultiDigraph.sumEdgeMult (G.cap δ) G.activePairsList < 2 ^ w := by
    simpa [MultiDigraph.sumEdgeMult_cap_activePairsList] using hedges_w
  rcases capMultiDigraphLoop_exec G δ extra a_src a_buf r_base hne_sb hw3 hn_w hδ_w hm3_w
      G.activePairsList [] rfl [n, 0] 0 0 0 rfl hm_bound₉ he_bound₉
      (by simp [s₉, s₈, s₇, s₆, s₅, s₄, s₃, s₂, s₁, hne_sb, hsrc])
      hbuf₉
      (by simp [s₉, s₈, s₇, s₆, s₅, s₄, s₃, s₂, s₁])
      (by simp [s₉, s₈, s₇, s₆, s₅, s₄, s₃])
      (by simp [s₉, s₈, s₇, s₆, s₅, s₄])
      (by simp [s₉, s₈, s₇, s₆, s₅, s₄, s₃, s₂])
      (by simp [s₉])
      (by simp [s₉, s₈]) with
    ⟨s₁₀, t₁₀, extra_buf', hex₁₀, ht₁₀, hbuf₁₀, hr0_10, hr1_10, hr2_10, hr5_10, harr₁₀, hreg₁₀⟩
  rw [← MultiDigraph.flatTriples_cap] at hbuf₁₀ hr5_10
  rw [Nat.zero_add, ← MultiDigraph.activePairsList_cap] at hr1_10
  change s₁₀.regs (r_base + 1) = (G.cap δ).numActivePairs at hr1_10
  rw [Nat.zero_add, MultiDigraph.sumEdgeMult_cap_activePairsList] at hr2_10
  -- 11. write a_buf 1 (r_base + 1)
  have hcap_le : (G.cap δ).numActivePairs ≤ G.numActivePairs := by
    simp only [MultiDigraph.numActivePairs, MultiDigraph.activePairsList_cap]
    exact List.length_filter_le _ _
  have hcap_m'_w : (G.cap δ).numActivePairs < 2 ^ w := by omega
  let s₁₁ := s₁₀.writeArr a_buf 1 (G.cap δ).numActivePairs
  have hex₁₁ : Exec w (.write a_buf (.const 1) (.reg (r_base + 1))) s₁₀ s₁₁ 3 :=
    .write (by simp [Expr.eval, checkWord, hw])
      (by simp [Expr.eval, checkWord, hr1_10, hcap_m'_w])
      (by simp [hbuf₁₀])
  have hbuf₁₁ : s₁₁.arrs a_buf = [] ++ (G.cap δ).enc ++ List.replicate extra_buf' 0 := by
    simp only [s₁₁, State.writeArr_arrs_self, hbuf₁₀, MultiDigraph.enc]
    rfl
  -- 12. readSliceProg a_buf (.const 0) a_dst (.reg (r_base + 5)) (r_base + 6)
  have hlen_enc_cap : (G.cap δ).enc.length = 2 + 3 * (G.cap δ).numActivePairs :=
    (G.cap δ).length_enc
  have hr5_11 : s₁₁.regs (r_base + 5) = (G.cap δ).enc.length := by
    simpa [s₁₁, MultiDigraph.enc] using hr5_10
  have henc_w : ∀ x ∈ (G.cap δ).enc, x < 2 ^ w := by
    intro x hx
    simp only [MultiDigraph.enc, List.cons_append, List.nil_append, List.mem_cons] at hx
    rcases hx with rfl | rfl | hx
    · exact hn_w
    · exact hcap_m'_w
    · exact all_lt_flatTriples (G.cap δ) (G.cap δ).activePairsList hn_w
        (fun p _ => Nat.lt_of_le_of_lt (G.cap_edgeMult_le_succ δ p.1 p.2) hδ_w) x hx
  have hoff_len_w : 0 + (G.cap δ).enc.length < 2 ^ w := by omega
  rcases readSliceProg_exec a_buf a_dst (.const 0) (r_base + 5) (r_base + 6)
      hne_bd (by omega) [] (G.cap δ).enc (List.replicate extra_buf' 0)
      rfl rfl henc_w hw hoff_len_w
      (by simp [Expr.eval, checkWord, h0_w])
      hbuf₁₁ hr5_11 with
    ⟨s₁₂, t₁₂, hex₁₂, ht₁₂, hdst₁₂, harr₁₂, hreg₁₂⟩
  have hlen_apl : G.activePairsList.length = G.numActivePairs := rfl
  rw [hlen_apl] at ht₁₀
  rw [hlen_enc_cap] at ht₁₂
  dsimp only [Expr.cost] at ht₁₂
  refine ⟨s₁₂, _,
    .seq hex₁ (.seq hex₂ (.seq hex₃ (.seq hex₄ (.seq hex₅ (.seq hex₆
      (.seq hex₇ (.seq hex₈ (.seq hex₉ (.seq hex₁₀ (.seq hex₁₁ hex₁₂)))))))))),
    by omega,
    hdst₁₂,
    by rw [hreg₁₂ r_base (by omega)]; exact hr0_10,
    by rw [hreg₁₂ (r_base + 1) (by omega)]; exact hr1_10,
    by rw [hreg₁₂ (r_base + 2) (by omega)]; exact hr2_10,
    fun a hab had => by
      rw [harr₁₂ a had]
      simp only [s₁₁, State.writeArr_arrs_ne _ _ _ hab]
      rw [harr₁₀ a hab]
      simp [s₉, s₈, s₇, s₆, s₅, s₄, s₃, s₂, s₁, show (a : Arr) ≠ a_buf from hab],
    fun r hr => by
      rw [hreg₁₂ r (by omega)]
      simp only [s₁₁, State.writeArr_regs]
      rw [hreg₁₀ r hr]
      simp [s₉, s₈, s₇, s₆, s₅, s₄, s₃, s₂, s₁,
        State.setReg_regs_ne _ _ (by omega : (r : Reg) ≠ r_base + 4),
        State.setReg_regs_ne _ _ (by omega : (r : Reg) ≠ r_base + 5),
        State.setReg_regs_ne _ _ (by omega : (r : Reg) ≠ r_base + 2),
        State.setReg_regs_ne _ _ (by omega : (r : Reg) ≠ r_base + 1),
        State.setReg_regs_ne _ _ (by omega : (r : Reg) ≠ r_base + 3),
        State.setReg_regs_ne _ _ (by omega : (r : Reg) ≠ r_base)]⟩

/-! ### 3.4 Constructing the Underlying Simple Graph (`toSimpleGraphProg`) -/

open MultiDigraph

@[simp]
theorem flatEdges_cons {n : ℕ} (p : Fin n × Fin n) (ps : List (Fin n × Fin n)) :
    flatEdges (p :: ps) = p.1.1 :: p.2.1 :: flatEdges ps := rfl

theorem length_toSimplePairsAux_le {n : ℕ} (prev_u prev_v : ℕ) (ps : List (Fin n × Fin n)) :
    (toSimplePairsAux prev_u prev_v ps).length ≤ ps.length := by
  induction ps generalizing prev_u prev_v with
  | nil => simp [toSimplePairsAux]
  | cons p ps ih =>
    rcases p with ⟨u, v⟩
    simp only [toSimplePairsAux]
    split_ifs <;> simp only [List.length_cons]
    · exact Nat.succ_le_succ (ih u.1 v.1)
    · exact Nat.le_succ_of_le (ih prev_u prev_v)
    · exact Nat.succ_le_succ (ih v.1 u.1)
    · exact Nat.le_succ_of_le (ih prev_u prev_v)

theorem all_lt_flatEdges {n : ℕ} (ps : List (Fin n × Fin n)) {B : ℕ}
    (hn : n < B) : ∀ x ∈ flatEdges ps, x < B := by
  induction ps with
  | nil => simp [flatEdges]
  | cons p ps ih =>
    intro x hx
    simp only [flatEdges_cons, List.mem_cons] at hx
    rcases hx with rfl | rfl | hx
    · exact Nat.lt_trans p.1.2 hn
    · exact Nat.lt_trans p.2.2 hn
    · exact ih x hx

/-- Loop body for `toSimpleGraphEdgeListProg`.
Register layout starting at `r_base`:
- `r_base`: `n`
- `r_base + 1`: `m_simple` (undirected edges emitted so far)
- `r_base + 2`: `m'` (`G.numActivePairs`)
- `r_base + 3`: loop counter `k` (`0 .. m'`)
- `r_base + 4`: buffer write position `pos` (starts at `2`)
- `r_base + 5`: `prev_u` (initialized to `n`)
- `r_base + 6`: `prev_v` (initialized to `n`)
- `r_base + 7`: triple offset `idx = 2 + 3 * k`
- `r_base + 8`: `u`
- `r_base + 9`: `v` -/
def toSimpleGraphEdgeListBody (a_src a_buf : Arr) (r_base : Reg) : Cmd :=
  .seq (readTripleEndpoints a_src (r_base + 3) (r_base + 7) (r_base + 8) (r_base + 9))
    (.ite (.op .eq (.reg (r_base + 8)) (.reg (r_base + 9)))
      .skip
      (.ite (.op .lt (.reg (r_base + 8)) (.reg (r_base + 9)))
        (.seq (bufPush2 a_buf (r_base + 4) (r_base + 8) (r_base + 9))
          (.seq (.assign (r_base + 1) (.op .add (.reg (r_base + 1)) (.const 1)))
            (.seq (.assign (r_base + 5) (.reg (r_base + 8)))
              (.assign (r_base + 6) (.reg (r_base + 9))))))
        (.ite (.op .mul (.op .eq (.reg (r_base + 9)) (.reg (r_base + 5)))
                        (.op .eq (.reg (r_base + 8)) (.reg (r_base + 6))))
          .skip
          (.seq (bufPush2 a_buf (r_base + 4) (r_base + 9) (r_base + 8))
            (.seq (.assign (r_base + 1) (.op .add (.reg (r_base + 1)) (.const 1)))
              (.seq (.assign (r_base + 5) (.reg (r_base + 9)))
                (.assign (r_base + 6) (.reg (r_base + 8)))))))))

/-- Word RAM program that reads `G.enc` from `a_src` (without reading the multiplicity words, so
it works even if `G` has unbounded multiplicities `≥ 2 ^ w`) and writes the canonical flat
simple-graph encoding `encGraph G.toSimpleGraph` into `a_dst` using scratch buffer `a_buf`. -/
def toSimpleGraphEdgeListProg (a_src a_buf a_dst : Arr) (r_base : Reg) : Cmd :=
  .seq (.assign r_base (.read a_src (.const 0)))
    (.seq (.assign (r_base + 2) (.read a_src (.const 1)))
      (.seq (.assign (r_base + 1) (.const 0))
        (.seq (.assign (r_base + 4) (.op .add (.const 2) (.op .mul (.const 2) (.reg (r_base + 2)))))
          (.seq (.alloc a_buf (.reg (r_base + 4)))
            (.seq (.write a_buf (.const 0) (.reg r_base))
              (.seq (.assign (r_base + 4) (.const 2))
                (.seq (.assign (r_base + 5) (.reg r_base))
                  (.seq (.assign (r_base + 6) (.reg r_base))
                    (.seq (.assign (r_base + 3) (.const 0))
                      (.seq (forUp (r_base + 3) (.reg (r_base + 2))
                              (toSimpleGraphEdgeListBody a_src a_buf r_base))
                        (.seq (.write a_buf (.const 1) (.reg (r_base + 1)))
                          (readSliceProg a_buf (.const 0) a_dst (.reg (r_base + 4)) (r_base + 7)))))))))))))

/-- Suffix-induction specification for the main loop of `toSimpleGraphEdgeListProg`. -/
theorem toSimpleGraphEdgeListLoop_exec {w n : ℕ} (G : MultiDigraph n) (extra : List ℕ)
    (a_src a_buf : ℕ) (r_base : ℕ)
    (hne_sb : a_src ≠ a_buf)
    (hw3 : 3 < 2 ^ w) (hn_w : n < 2 ^ w)
    (hm3_w : 2 + 3 * G.numActivePairs < 2 ^ w)
    (suff : List (Fin n × Fin n)) :
    ∀ (pref : List (Fin n × Fin n)),
      G.activePairsList = pref ++ suff →
      ∀ (pfx : List ℕ) (extra_buf m_acc prev_u prev_v : ℕ),
        pfx.length = 2 + 2 * m_acc →
        m_acc + (toSimplePairsAux prev_u prev_v suff).length ≤ G.numActivePairs →
        prev_u ≤ n →
        prev_v ≤ n →
        ∀ {s : State},
          s.arrs a_src = G.enc ++ extra →
          s.arrs a_buf = pfx ++ List.replicate (2 * suff.length + extra_buf) 0 →
          s.regs r_base = n →
          s.regs (r_base + 1) = m_acc →
          s.regs (r_base + 2) = G.numActivePairs →
          s.regs (r_base + 3) = pref.length →
          s.regs (r_base + 4) = pfx.length →
          s.regs (r_base + 5) = prev_u →
          s.regs (r_base + 6) = prev_v →
          ∃ s' t extra_buf',
            Exec w (forUp (r_base + 3) (.reg (r_base + 2))
              (toSimpleGraphEdgeListBody a_src a_buf r_base)) s s' t ∧
            t ≤ 3 + 56 * suff.length ∧
            s'.arrs a_buf = pfx ++ flatEdges (toSimplePairsAux prev_u prev_v suff) ++
              List.replicate extra_buf' 0 ∧
            s'.regs r_base = n ∧
            s'.regs (r_base + 1) = m_acc + (toSimplePairsAux prev_u prev_v suff).length ∧
            s'.regs (r_base + 4) = (pfx ++ flatEdges (toSimplePairsAux prev_u prev_v suff)).length ∧
            (∀ a : ℕ, a ≠ a_buf → s'.arrs a = s.arrs a) ∧
            (∀ r < r_base, s'.regs r = s.regs r) := by
  have hw : 1 < 2 ^ w := by omega
  have hw2 : 2 < 2 ^ w := by omega
  have h0_w : 0 < 2 ^ w := by omega
  have hm'_w : G.numActivePairs < 2 ^ w := by omega
  induction suff with
  | nil =>
    intro pref hsplit pfx extra_buf m_acc prev_u prev_v hpfx_len hm_bound hpu hpv
      s hsrc hbuf hr0 hr1 hr2 hr3 hr4 hr5 hr6
    have hlen_pref : pref.length = G.numActivePairs := by
      have := congrArg List.length hsplit
      simp only [List.append_nil] at this
      exact this.symm
    have hcond : (Expr.op .lt (.reg (r_base + 3)) (.reg (r_base + 2))).eval w s = some 0 := by
      simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hr3, hr2, hlen_pref, hm'_w]
    refine ⟨s, 3, extra_buf, .while_false hcond, by simp, ?_, hr0, ?_, ?_,
      fun _ _ => rfl, fun _ _ => rfl⟩
    · simpa [toSimplePairsAux, flatEdges] using hbuf
    · simpa [toSimplePairsAux] using hr1
    · simpa [toSimplePairsAux, flatEdges] using hr4
  | cons p ps ih =>
    rcases p with ⟨u, v⟩
    intro pref hsplit pfx extra_buf m_acc prev_u prev_v hpfx_len hm_bound hpu hpv
      s hsrc hbuf hr0 hr1 hr2 hr3 hr4 hr5 hr6
    let k := pref.length
    obtain ⟨hk_lt, hget_k⟩ := getElem_of_eq_append_cons hsplit
    have hk_m' : k < G.numActivePairs := hk_lt
    have hk_w : k < 2 ^ w := by omega
    have hpu_w : prev_u < 2 ^ w := by omega
    have hpv_w : prev_v < 2 ^ w := by omega
    have hcond : (Expr.op .lt (.reg (r_base + 3)) (.reg (r_base + 2))).eval w s = some 1 := by
      simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hr3, hr2, k, hk_m', hk_w, hm'_w, hw]
    -- 1. readTripleEndpoints a_src (r_base + 3) (r_base + 7) (r_base + 8) (r_base + 9)
    rcases readTripleEndpoints_exec G extra a_src (r_base + 3) (r_base + 7) (r_base + 8) (r_base + 9)
        k s (by omega) (by omega) (by omega)
        hw3 hn_w hm3_w hk_m' hsrc hr3 with
      ⟨s₁, t₁, hex₁, ht₁, hr7_1, hr8_1, hr9_1, harr₁, hreg₁⟩
    have hget_u : (G.activePairsList[k]'hk_m').1 = u := congrArg Prod.fst hget_k
    have hget_v : (G.activePairsList[k]'hk_m').2 = v := congrArg Prod.snd hget_k
    rw [hget_u] at hr8_1
    rw [hget_v] at hr9_1
    have hu_w : u.1 < 2 ^ w := Nat.lt_trans u.2 hn_w
    have hv_w : v.1 < 2 ^ w := Nat.lt_trans v.2 hn_w
    have hsplit' : G.activePairsList = (pref ++ [(u, v)]) ++ ps := by
      simp [hsplit, List.append_assoc]
    -- 2. First ite: u.1 = v.1
    by_cases huv_eq : u.1 = v.1
    · have huv_not_lt : ¬(u.1 < v.1) := by omega
      have hvu_not_lt : ¬(v.1 < u.1) := by omega
      have haux_eq : toSimplePairsAux prev_u prev_v ((u, v) :: ps) = toSimplePairsAux prev_u prev_v ps := by
        simp [toSimplePairsAux, huv_not_lt, hvu_not_lt]
      have hcond_eq : (Expr.op .eq (.reg (r_base + 8)) (.reg (r_base + 9))).eval w s₁ = some 1 := by
        simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hr8_1, hr9_1, huv_eq, hv_w, hw]
      have hex_ite1 : Exec w
          (.ite (.op .eq (.reg (r_base + 8)) (.reg (r_base + 9)))
            .skip
            (.ite (.op .lt (.reg (r_base + 8)) (.reg (r_base + 9)))
              (.seq (bufPush2 a_buf (r_base + 4) (r_base + 8) (r_base + 9))
                (.seq (.assign (r_base + 1) (.op .add (.reg (r_base + 1)) (.const 1)))
                  (.seq (.assign (r_base + 5) (.reg (r_base + 8)))
                    (.assign (r_base + 6) (.reg (r_base + 9))))))
              (.ite (.op .mul (.op .eq (.reg (r_base + 9)) (.reg (r_base + 5)))
                              (.op .eq (.reg (r_base + 8)) (.reg (r_base + 6))))
                .skip
                (.seq (bufPush2 a_buf (r_base + 4) (r_base + 9) (r_base + 8))
                  (.seq (.assign (r_base + 1) (.op .add (.reg (r_base + 1)) (.const 1)))
                    (.seq (.assign (r_base + 5) (.reg (r_base + 9)))
                      (.assign (r_base + 6) (.reg (r_base + 8)))))))))
          s₁ s₁ (3 + 1) :=
        .ite_true hcond_eq (by omega) (.skip s₁)
      have hex_body : Exec w (toSimpleGraphEdgeListBody a_src a_buf r_base) s s₁ (t₁ + (3 + 1)) :=
        .seq hex₁ hex_ite1
      have hr3_1 : s₁.regs (r_base + 3) = k := by
        rw [hreg₁ (r_base + 3) (by omega) (by omega) (by omega)]; exact hr3
      let s₂ := s₁.setReg (r_base + 3) (k + 1)
      have hex_inc : Exec w (.assign (r_base + 3) (.op .add (.reg (r_base + 3)) (.const 1)))
          s₁ s₂ 4 :=
        .assign (by simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hr3_1, hk_w, hw,
          show k + 1 < 2 ^ w by omega])
      have hbuf₂ : s₂.arrs a_buf = pfx ++ List.replicate (2 * ps.length + (extra_buf + 2)) 0 := by
        have hlen_eq : 2 * ((u, v) :: ps).length + extra_buf = 2 * ps.length + (extra_buf + 2) := by
          simp; omega
        rw [← hlen_eq]
        simpa [s₂, harr₁] using hbuf
      have hm_bound' : m_acc + (toSimplePairsAux prev_u prev_v ps).length ≤ G.numActivePairs := by
        rwa [← haux_eq]
      rcases ih (pref ++ [(u, v)]) hsplit' pfx (extra_buf + 2) m_acc prev_u prev_v
          hpfx_len hm_bound' hpu hpv (s := s₂)
          (by simp [s₂, harr₁, hsrc])
          hbuf₂
          (by simp [s₂, hreg₁ r_base (by omega) (by omega) (by omega), hr0])
          (by simp [s₂, hreg₁ (r_base + 1) (by omega) (by omega) (by omega), hr1])
          (by simp [s₂, hreg₁ (r_base + 2) (by omega) (by omega) (by omega), hr2])
          (by simp [s₂, k])
          (by simp [s₂, hreg₁ (r_base + 4) (by omega) (by omega) (by omega), hr4])
          (by simp [s₂, hreg₁ (r_base + 5) (by omega) (by omega) (by omega), hr5])
          (by simp [s₂, hreg₁ (r_base + 6) (by omega) (by omega) (by omega), hr6]) with
        ⟨s₃, t₃, extra_buf', hex₃, ht₃, hbuf₃, hr0_3, hr1_3, hr4_3, harr₃, hreg₃⟩
      refine ⟨s₃, 3 + ((t₁ + (3 + 1)) + 4) + t₃, extra_buf',
        .while_true hcond (by omega) (.seq hex_body hex_inc) hex₃,
        by simp only [List.length_cons]; omega,
        by rw [haux_eq]; exact hbuf₃,
        hr0_3,
        by rw [haux_eq]; exact hr1_3,
        by rw [haux_eq]; exact hr4_3,
        fun a ha => by rw [harr₃ a ha]; simp [s₂, harr₁],
        fun r hr => by
          rw [hreg₃ r hr]
          simp [s₂, State.setReg_regs_ne _ _ (by omega : (r : Reg) ≠ r_base + 3),
            hreg₁ r (by omega) (by omega) (by omega)]⟩
    · have hcond_eq : (Expr.op .eq (.reg (r_base + 8)) (.reg (r_base + 9))).eval w s₁ = some 0 := by
        simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hr8_1, hr9_1, huv_eq, hu_w, hv_w]
      -- 3. Second ite: u.1 < v.1
      by_cases huv_lt : u.1 < v.1
      · have haux_lt :
            toSimplePairsAux prev_u prev_v ((u, v) :: ps) = (u, v) :: toSimplePairsAux u.1 v.1 ps := by
          simp [toSimplePairsAux, huv_lt]
        have hcond_lt : (Expr.op .lt (.reg (r_base + 8)) (.reg (r_base + 9))).eval w s₁ = some 1 := by
          simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hr8_1, hr9_1, huv_lt, hu_w, hv_w, hw]
        have hbuf₁ : s₁.arrs a_buf = pfx ++ List.replicate ((2 * ps.length + extra_buf) + 2) 0 := by
          have hlen_eq : 2 * ((u, v) :: ps).length + extra_buf = (2 * ps.length + extra_buf) + 2 := by
            simp; omega
          rw [← hlen_eq, harr₁]
          exact hbuf
        have hr4_1 : s₁.regs (r_base + 4) = pfx.length := by
          rw [hreg₁ (r_base + 4) (by omega) (by omega) (by omega)]; exact hr4
        have hm_acc_lt : m_acc + 1 ≤ G.numActivePairs := by
          rw [haux_lt, List.length_cons] at hm_bound
          omega
        have hpos_w : pfx.length + 2 < 2 ^ w := by omega
        rcases bufPush2_exec a_buf (r_base + 4) (r_base + 8) (r_base + 9)
            pfx (2 * ps.length + extra_buf) u.1 v.1 hw2 hpos_w hu_w hv_w
            hbuf₁ hr4_1 hr8_1 hr9_1 with
          ⟨s₂, t₂, hex₂, ht₂, hbuf₂, hr4_2, harr₂, hreg₂⟩
        have hr1_2 : s₂.regs (r_base + 1) = m_acc := by
          rw [hreg₂ _ (by omega), hreg₁ (r_base + 1) (by omega) (by omega) (by omega)]; exact hr1
        have hm_acc_w : m_acc < 2 ^ w := by omega
        have hm_acc1_w : m_acc + 1 < 2 ^ w := by omega
        let s₃ := s₂.setReg (r_base + 1) (m_acc + 1)
        have hex₃ : Exec w (.assign (r_base + 1) (.op .add (.reg (r_base + 1)) (.const 1))) s₂ s₃ 4 :=
          .assign (by simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hr1_2, hm_acc_w, hw, hm_acc1_w])
        have hr8_3 : s₃.regs (r_base + 8) = u.1 := by
          simp only [s₃, State.setReg_regs_ne _ _ (by omega : (r_base + 8 : Reg) ≠ r_base + 1)]
          rw [hreg₂ _ (by omega)]; exact hr8_1
        let s₄ := s₃.setReg (r_base + 5) u.1
        have hex₄ : Exec w (.assign (r_base + 5) (.reg (r_base + 8))) s₃ s₄ 2 :=
          .assign (by simp [Expr.eval, checkWord, hr8_3, hu_w])
        have hr9_4 : s₄.regs (r_base + 9) = v.1 := by
          simp only [s₄, s₃,
            State.setReg_regs_ne _ _ (by omega : (r_base + 9 : Reg) ≠ r_base + 5),
            State.setReg_regs_ne _ _ (by omega : (r_base + 9 : Reg) ≠ r_base + 1)]
          rw [hreg₂ _ (by omega)]; exact hr9_1
        let s₅ := s₄.setReg (r_base + 6) v.1
        have hex₅ : Exec w (.assign (r_base + 6) (.reg (r_base + 9))) s₄ s₅ 2 :=
          .assign (by simp [Expr.eval, checkWord, hr9_4, hv_w])
        have hex_ite2 : Exec w
            (.ite (.op .lt (.reg (r_base + 8)) (.reg (r_base + 9)))
              (.seq (bufPush2 a_buf (r_base + 4) (r_base + 8) (r_base + 9))
                (.seq (.assign (r_base + 1) (.op .add (.reg (r_base + 1)) (.const 1)))
                  (.seq (.assign (r_base + 5) (.reg (r_base + 8)))
                    (.assign (r_base + 6) (.reg (r_base + 9))))))
              (.ite (.op .mul (.op .eq (.reg (r_base + 9)) (.reg (r_base + 5)))
                              (.op .eq (.reg (r_base + 8)) (.reg (r_base + 6))))
                .skip
                (.seq (bufPush2 a_buf (r_base + 4) (r_base + 9) (r_base + 8))
                  (.seq (.assign (r_base + 1) (.op .add (.reg (r_base + 1)) (.const 1)))
                    (.seq (.assign (r_base + 5) (.reg (r_base + 9)))
                      (.assign (r_base + 6) (.reg (r_base + 8))))))))
            s₁ s₅ (3 + (t₂ + (4 + (2 + 2)))) :=
          .ite_true hcond_lt (by omega) (.seq hex₂ (.seq hex₃ (.seq hex₄ hex₅)))
        have hex_body : Exec w (toSimpleGraphEdgeListBody a_src a_buf r_base) s s₅
            (t₁ + (3 + (3 + (t₂ + (4 + (2 + 2)))))) :=
          .seq hex₁ (.ite_false hcond_eq hex_ite2)
        have hr3_5 : s₅.regs (r_base + 3) = k := by
          simp only [s₅, s₄, s₃,
            State.setReg_regs_ne _ _ (by omega : (r_base + 3 : Reg) ≠ r_base + 6),
            State.setReg_regs_ne _ _ (by omega : (r_base + 3 : Reg) ≠ r_base + 5),
            State.setReg_regs_ne _ _ (by omega : (r_base + 3 : Reg) ≠ r_base + 1)]
          rw [hreg₂ _ (by omega), hreg₁ (r_base + 3) (by omega) (by omega) (by omega)]; exact hr3
        let s₆ := s₅.setReg (r_base + 3) (k + 1)
        have hex_inc : Exec w (.assign (r_base + 3) (.op .add (.reg (r_base + 3)) (.const 1)))
            s₅ s₆ 4 :=
          .assign (by simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hr3_5, hk_w, hw,
            show k + 1 < 2 ^ w by omega])
        have hm_bound' : (m_acc + 1) + (toSimplePairsAux u.1 v.1 ps).length ≤ G.numActivePairs := by
          rw [haux_lt, List.length_cons] at hm_bound
          omega
        rcases ih (pref ++ [(u, v)]) hsplit' (pfx ++ [u.1, v.1]) extra_buf (m_acc + 1) u.1 v.1
            (by simp [hpfx_len]; omega) hm_bound' (Nat.le_of_lt u.2) (Nat.le_of_lt v.2) (s := s₆)
            (by simp only [s₆, s₅, s₄, s₃, State.setReg_arrs]; rw [harr₂ a_src hne_sb, harr₁]; exact hsrc)
            (by simpa [s₆, s₅, s₄, s₃] using hbuf₂)
            (by simp only [s₆, s₅, s₄, s₃,
                State.setReg_regs_ne _ _ (by omega : (r_base : Reg) ≠ r_base + 3),
                State.setReg_regs_ne _ _ (by omega : (r_base : Reg) ≠ r_base + 6),
                State.setReg_regs_ne _ _ (by omega : (r_base : Reg) ≠ r_base + 5),
                State.setReg_regs_ne _ _ (by omega : (r_base : Reg) ≠ r_base + 1)];
                rw [hreg₂ _ (by omega), hreg₁ r_base (by omega) (by omega) (by omega)]; exact hr0)
            (by simp [s₆, s₅, s₄, s₃])
            (by simp only [s₆, s₅, s₄, s₃,
                State.setReg_regs_ne _ _ (by omega : (r_base + 2 : Reg) ≠ r_base + 3),
                State.setReg_regs_ne _ _ (by omega : (r_base + 2 : Reg) ≠ r_base + 6),
                State.setReg_regs_ne _ _ (by omega : (r_base + 2 : Reg) ≠ r_base + 5),
                State.setReg_regs_ne _ _ (by omega : (r_base + 2 : Reg) ≠ r_base + 1)];
                rw [hreg₂ _ (by omega), hreg₁ (r_base + 2) (by omega) (by omega) (by omega)]; exact hr2)
            (by simp [s₆, k])
            (by simp [s₆, s₅, s₄, s₃, hr4_2])
            (by simp [s₆, s₅, s₄])
            (by simp [s₆, s₅]) with
          ⟨s₇, t₇, extra_buf', hex₇, ht₇, hbuf₇, hr0_7, hr1_7, hr4_7, harr₇, hreg₇⟩
        refine ⟨s₇, 3 + ((t₁ + (3 + (3 + (t₂ + (4 + (2 + 2)))))) + 4) + t₇, extra_buf',
          .while_true hcond (by omega) (.seq hex_body hex_inc) hex₇,
          by simp only [List.length_cons]; omega,
          by rw [haux_lt, flatEdges_cons]; simpa [List.append_assoc] using hbuf₇,
          hr0_7,
          by rw [haux_lt, List.length_cons]; omega,
          by rw [haux_lt, flatEdges_cons]; simpa [List.append_assoc] using hr4_7,
          fun a ha => by
            rw [harr₇ a ha]
            simp only [s₆, s₅, s₄, s₃, State.setReg_arrs]
            rw [harr₂ a ha, harr₁],
          fun r hr => by
            rw [hreg₇ r hr]
            simp only [s₆, s₅, s₄, s₃,
              State.setReg_regs_ne _ _ (by omega : (r : Reg) ≠ r_base + 3),
              State.setReg_regs_ne _ _ (by omega : (r : Reg) ≠ r_base + 6),
              State.setReg_regs_ne _ _ (by omega : (r : Reg) ≠ r_base + 5),
              State.setReg_regs_ne _ _ (by omega : (r : Reg) ≠ r_base + 1)]
            rw [hreg₂ r (by omega), hreg₁ r (by omega) (by omega) (by omega)]⟩
      · have hvu_lt : v.1 < u.1 := by omega
        have hcond_lt : (Expr.op .lt (.reg (r_base + 8)) (.reg (r_base + 9))).eval w s₁ = some 0 := by
          simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hr8_1, hr9_1, huv_lt, hu_w, hv_w]
        have hr5_1 : s₁.regs (r_base + 5) = prev_u := by
          rw [hreg₁ (r_base + 5) (by omega) (by omega) (by omega)]; exact hr5
        have hr6_1 : s₁.regs (r_base + 6) = prev_v := by
          rw [hreg₁ (r_base + 6) (by omega) (by omega) (by omega)]; exact hr6
        -- 4. Third ite: prev_u = v.1 ∧ prev_v = u.1
        by_cases hprev_eq : prev_u = v.1 ∧ prev_v = u.1
        · rcases hprev_eq with ⟨hvp, hup⟩
          have haux_prev :
              toSimplePairsAux prev_u prev_v ((u, v) :: ps) = toSimplePairsAux prev_u prev_v ps := by
            simp [toSimplePairsAux, huv_lt, hvu_lt, hvp, hup]
          have hcond_prev :
              (Expr.op .mul (.op .eq (.reg (r_base + 9)) (.reg (r_base + 5)))
                            (.op .eq (.reg (r_base + 8)) (.reg (r_base + 6)))).eval w s₁ = some 1 := by
            simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hr9_1, hr5_1, hr8_1, hr6_1,
              hvp, hup, hv_w, hu_w, hw]
          have hex_ite3 : Exec w
              (.ite (.op .mul (.op .eq (.reg (r_base + 9)) (.reg (r_base + 5)))
                              (.op .eq (.reg (r_base + 8)) (.reg (r_base + 6))))
                .skip
                (.seq (bufPush2 a_buf (r_base + 4) (r_base + 9) (r_base + 8))
                  (.seq (.assign (r_base + 1) (.op .add (.reg (r_base + 1)) (.const 1)))
                    (.seq (.assign (r_base + 5) (.reg (r_base + 9)))
                      (.assign (r_base + 6) (.reg (r_base + 8)))))))
              s₁ s₁ (7 + 1) :=
            .ite_true hcond_prev (by omega) (.skip s₁)
          have hex_body : Exec w (toSimpleGraphEdgeListBody a_src a_buf r_base) s s₁
              (t₁ + (3 + (3 + (7 + 1)))) :=
            .seq hex₁ (.ite_false hcond_eq (.ite_false hcond_lt hex_ite3))
          have hr3_1 : s₁.regs (r_base + 3) = k := by
            rw [hreg₁ (r_base + 3) (by omega) (by omega) (by omega)]; exact hr3
          let s₂ := s₁.setReg (r_base + 3) (k + 1)
          have hex_inc : Exec w (.assign (r_base + 3) (.op .add (.reg (r_base + 3)) (.const 1)))
              s₁ s₂ 4 :=
            .assign (by simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hr3_1, hk_w, hw,
              show k + 1 < 2 ^ w by omega])
          have hbuf₂ : s₂.arrs a_buf = pfx ++ List.replicate (2 * ps.length + (extra_buf + 2)) 0 := by
            have hlen_eq : 2 * ((u, v) :: ps).length + extra_buf = 2 * ps.length + (extra_buf + 2) := by
              simp; omega
            rw [← hlen_eq]
            simpa [s₂, harr₁] using hbuf
          have hm_bound' : m_acc + (toSimplePairsAux prev_u prev_v ps).length ≤ G.numActivePairs := by
            rwa [← haux_prev]
          rcases ih (pref ++ [(u, v)]) hsplit' pfx (extra_buf + 2) m_acc prev_u prev_v
              hpfx_len hm_bound' hpu hpv (s := s₂)
              (by simp [s₂, harr₁, hsrc])
              hbuf₂
              (by simp [s₂, hreg₁ r_base (by omega) (by omega) (by omega), hr0])
              (by simp [s₂, hreg₁ (r_base + 1) (by omega) (by omega) (by omega), hr1])
              (by simp [s₂, hreg₁ (r_base + 2) (by omega) (by omega) (by omega), hr2])
              (by simp [s₂, k])
              (by simp [s₂, hreg₁ (r_base + 4) (by omega) (by omega) (by omega), hr4])
              (by simp [s₂, hreg₁ (r_base + 5) (by omega) (by omega) (by omega), hr5])
              (by simp [s₂, hreg₁ (r_base + 6) (by omega) (by omega) (by omega), hr6]) with
            ⟨s₃, t₃, extra_buf', hex₃, ht₃, hbuf₃, hr0_3, hr1_3, hr4_3, harr₃, hreg₃⟩
          refine ⟨s₃, 3 + ((t₁ + (3 + (3 + (7 + 1)))) + 4) + t₃, extra_buf',
            .while_true hcond (by omega) (.seq hex_body hex_inc) hex₃,
            by simp only [List.length_cons]; omega,
            by rw [haux_prev]; exact hbuf₃,
            hr0_3,
            by rw [haux_prev]; exact hr1_3,
            by rw [haux_prev]; exact hr4_3,
            fun a ha => by rw [harr₃ a ha]; simp [s₂, harr₁],
            fun r hr => by
              rw [hreg₃ r hr]
              simp [s₂, State.setReg_regs_ne _ _ (by omega : (r : Reg) ≠ r_base + 3),
                hreg₁ r (by omega) (by omega) (by omega)]⟩
        · have haux_nprev :
              toSimplePairsAux prev_u prev_v ((u, v) :: ps) = (v, u) :: toSimplePairsAux v.1 u.1 ps := by
            simp [toSimplePairsAux, huv_lt, hvu_lt, hprev_eq]
          have hcond_prev :
              (Expr.op .mul (.op .eq (.reg (r_base + 9)) (.reg (r_base + 5)))
                            (.op .eq (.reg (r_base + 8)) (.reg (r_base + 6)))).eval w s₁ = some 0 := by
            have hmul0 : (if v.1 = prev_u then 1 else 0) * (if u.1 = prev_v then 1 else 0) = 0 := by
              split_ifs with h1 h2
              · exfalso; exact hprev_eq ⟨h1.symm, h2.symm⟩
              · rfl
              · rfl
              · rfl
            have hc1_w : (if v.1 = prev_u then 1 else 0) < 2 ^ w := by split_ifs <;> omega
            have hc2_w : (if u.1 = prev_v then 1 else 0) < 2 ^ w := by split_ifs <;> omega
            simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hr9_1, hr5_1, hr8_1, hr6_1,
              hv_w, hpu_w, hu_w, hpv_w, hc1_w, hc2_w, hmul0, h0_w]
          have hbuf₁ : s₁.arrs a_buf = pfx ++ List.replicate ((2 * ps.length + extra_buf) + 2) 0 := by
            have hlen_eq : 2 * ((u, v) :: ps).length + extra_buf = (2 * ps.length + extra_buf) + 2 := by
              simp; omega
            rw [← hlen_eq, harr₁]
            exact hbuf
          have hr4_1 : s₁.regs (r_base + 4) = pfx.length := by
            rw [hreg₁ (r_base + 4) (by omega) (by omega) (by omega)]; exact hr4
          have hm_acc_lt : m_acc + 1 ≤ G.numActivePairs := by
            rw [haux_nprev, List.length_cons] at hm_bound
            omega
          have hpos_w : pfx.length + 2 < 2 ^ w := by omega
          rcases bufPush2_exec a_buf (r_base + 4) (r_base + 9) (r_base + 8)
              pfx (2 * ps.length + extra_buf) v.1 u.1 hw2 hpos_w hv_w hu_w
              hbuf₁ hr4_1 hr9_1 hr8_1 with
            ⟨s₂, t₂, hex₂, ht₂, hbuf₂, hr4_2, harr₂, hreg₂⟩
          have hr1_2 : s₂.regs (r_base + 1) = m_acc := by
            rw [hreg₂ _ (by omega), hreg₁ (r_base + 1) (by omega) (by omega) (by omega)]; exact hr1
          have hm_acc_w : m_acc < 2 ^ w := by omega
          have hm_acc1_w : m_acc + 1 < 2 ^ w := by omega
          let s₃ := s₂.setReg (r_base + 1) (m_acc + 1)
          have hex₃ : Exec w (.assign (r_base + 1) (.op .add (.reg (r_base + 1)) (.const 1))) s₂ s₃ 4 :=
            .assign (by simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hr1_2, hm_acc_w, hw, hm_acc1_w])
          have hr9_3 : s₃.regs (r_base + 9) = v.1 := by
            simp only [s₃, State.setReg_regs_ne _ _ (by omega : (r_base + 9 : Reg) ≠ r_base + 1)]
            rw [hreg₂ _ (by omega)]; exact hr9_1
          let s₄ := s₃.setReg (r_base + 5) v.1
          have hex₄ : Exec w (.assign (r_base + 5) (.reg (r_base + 9))) s₃ s₄ 2 :=
            .assign (by simp [Expr.eval, checkWord, hr9_3, hv_w])
          have hr8_4 : s₄.regs (r_base + 8) = u.1 := by
            simp only [s₄, s₃,
              State.setReg_regs_ne _ _ (by omega : (r_base + 8 : Reg) ≠ r_base + 5),
              State.setReg_regs_ne _ _ (by omega : (r_base + 8 : Reg) ≠ r_base + 1)]
            rw [hreg₂ _ (by omega)]; exact hr8_1
          let s₅ := s₄.setReg (r_base + 6) u.1
          have hex₅ : Exec w (.assign (r_base + 6) (.reg (r_base + 8))) s₄ s₅ 2 :=
            .assign (by simp [Expr.eval, checkWord, hr8_4, hu_w])
          have hex_ite3 : Exec w
              (.ite (.op .mul (.op .eq (.reg (r_base + 9)) (.reg (r_base + 5)))
                              (.op .eq (.reg (r_base + 8)) (.reg (r_base + 6))))
                .skip
                (.seq (bufPush2 a_buf (r_base + 4) (r_base + 9) (r_base + 8))
                  (.seq (.assign (r_base + 1) (.op .add (.reg (r_base + 1)) (.const 1)))
                    (.seq (.assign (r_base + 5) (.reg (r_base + 9)))
                      (.assign (r_base + 6) (.reg (r_base + 8)))))))
              s₁ s₅ (7 + (t₂ + (4 + (2 + 2)))) :=
            .ite_false hcond_prev (.seq hex₂ (.seq hex₃ (.seq hex₄ hex₅)))
          have hex_body : Exec w (toSimpleGraphEdgeListBody a_src a_buf r_base) s s₅
              (t₁ + (3 + (3 + (7 + (t₂ + (4 + (2 + 2))))))) :=
            .seq hex₁ (.ite_false hcond_eq (.ite_false hcond_lt hex_ite3))
          have hr3_5 : s₅.regs (r_base + 3) = k := by
            simp only [s₅, s₄, s₃,
              State.setReg_regs_ne _ _ (by omega : (r_base + 3 : Reg) ≠ r_base + 6),
              State.setReg_regs_ne _ _ (by omega : (r_base + 3 : Reg) ≠ r_base + 5),
              State.setReg_regs_ne _ _ (by omega : (r_base + 3 : Reg) ≠ r_base + 1)]
            rw [hreg₂ _ (by omega), hreg₁ (r_base + 3) (by omega) (by omega) (by omega)]; exact hr3
          let s₆ := s₅.setReg (r_base + 3) (k + 1)
          have hex_inc : Exec w (.assign (r_base + 3) (.op .add (.reg (r_base + 3)) (.const 1)))
              s₅ s₆ 4 :=
            .assign (by simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hr3_5, hk_w, hw,
              show k + 1 < 2 ^ w by omega])
          have hm_bound' : (m_acc + 1) + (toSimplePairsAux v.1 u.1 ps).length ≤ G.numActivePairs := by
            rw [haux_nprev, List.length_cons] at hm_bound
            omega
          rcases ih (pref ++ [(u, v)]) hsplit' (pfx ++ [v.1, u.1]) extra_buf (m_acc + 1) v.1 u.1
              (by simp [hpfx_len]; omega) hm_bound' (Nat.le_of_lt v.2) (Nat.le_of_lt u.2) (s := s₆)
              (by simp only [s₆, s₅, s₄, s₃, State.setReg_arrs]; rw [harr₂ a_src hne_sb, harr₁]; exact hsrc)
              (by simpa [s₆, s₅, s₄, s₃] using hbuf₂)
              (by simp only [s₆, s₅, s₄, s₃,
                  State.setReg_regs_ne _ _ (by omega : (r_base : Reg) ≠ r_base + 3),
                  State.setReg_regs_ne _ _ (by omega : (r_base : Reg) ≠ r_base + 6),
                  State.setReg_regs_ne _ _ (by omega : (r_base : Reg) ≠ r_base + 5),
                  State.setReg_regs_ne _ _ (by omega : (r_base : Reg) ≠ r_base + 1)];
                  rw [hreg₂ _ (by omega), hreg₁ r_base (by omega) (by omega) (by omega)]; exact hr0)
              (by simp [s₆, s₅, s₄, s₃])
              (by simp only [s₆, s₅, s₄, s₃,
                  State.setReg_regs_ne _ _ (by omega : (r_base + 2 : Reg) ≠ r_base + 3),
                  State.setReg_regs_ne _ _ (by omega : (r_base + 2 : Reg) ≠ r_base + 6),
                  State.setReg_regs_ne _ _ (by omega : (r_base + 2 : Reg) ≠ r_base + 5),
                  State.setReg_regs_ne _ _ (by omega : (r_base + 2 : Reg) ≠ r_base + 1)];
                  rw [hreg₂ _ (by omega), hreg₁ (r_base + 2) (by omega) (by omega) (by omega)]; exact hr2)
              (by simp [s₆, k])
              (by simp [s₆, s₅, s₄, s₃, hr4_2])
              (by simp [s₆, s₅, s₄])
              (by simp [s₆, s₅]) with
            ⟨s₇, t₇, extra_buf', hex₇, ht₇, hbuf₇, hr0_7, hr1_7, hr4_7, harr₇, hreg₇⟩
          refine ⟨s₇, 3 + ((t₁ + (3 + (3 + (7 + (t₂ + (4 + (2 + 2))))))) + 4) + t₇, extra_buf',
            .while_true hcond (by omega) (.seq hex_body hex_inc) hex₇,
            by simp only [List.length_cons]; omega,
            by rw [haux_nprev, flatEdges_cons]; simpa [List.append_assoc] using hbuf₇,
            hr0_7,
            by rw [haux_nprev, List.length_cons]; omega,
            by rw [haux_nprev, flatEdges_cons]; simpa [List.append_assoc] using hr4_7,
            fun a ha => by
              rw [harr₇ a ha]
              simp only [s₆, s₅, s₄, s₃, State.setReg_arrs]
              rw [harr₂ a ha, harr₁],
            fun r hr => by
              rw [hreg₇ r hr]
              simp only [s₆, s₅, s₄, s₃,
                State.setReg_regs_ne _ _ (by omega : (r : Reg) ≠ r_base + 3),
                State.setReg_regs_ne _ _ (by omega : (r : Reg) ≠ r_base + 6),
                State.setReg_regs_ne _ _ (by omega : (r : Reg) ≠ r_base + 5),
                State.setReg_regs_ne _ _ (by omega : (r : Reg) ≠ r_base + 1)]
              rw [hreg₂ r (by omega), hreg₁ r (by omega) (by omega) (by omega)]⟩

/-- Specification for `toSimpleGraphEdgeListProg`: constructs `encGraph G.toSimpleGraph` in `a_dst`
in `O(G.numActivePairs + 1)` steps without reading the multiplicity words of `G.enc`. -/
theorem toSimpleGraphEdgeListProg_exec {w n : ℕ} (G : MultiDigraph n) (extra : List ℕ)
    (a_src a_buf a_dst : ℕ) (r_base : ℕ)
    (hne_sb : a_src ≠ a_buf) (hne_bd : a_buf ≠ a_dst)
    (hw3 : 3 < 2 ^ w) (hn_w : n < 2 ^ w)
    (hm3_w : 2 + 3 * G.numActivePairs < 2 ^ w)
    {s : State}
    (hsrc : s.arrs a_src = G.enc ++ extra) :
    ∃ s' t,
      Exec w (toSimpleGraphEdgeListProg a_src a_buf a_dst r_base) s s' t ∧
      t ≤ 96 * G.numActivePairs + 80 ∧
      s'.arrs a_dst = encGraph G.toSimpleGraph ∧
      s'.regs r_base = n ∧
      s'.regs (r_base + 1) = (edgeListOf G.toSimpleGraph).length ∧
      (∀ a : ℕ, a ≠ a_buf → a ≠ a_dst → s'.arrs a = s.arrs a) ∧
      (∀ r < r_base, s'.regs r = s.regs r) := by
  have hw : 1 < 2 ^ w := by omega
  have hw2 : 2 < 2 ^ w := by omega
  have h0_w : 0 < 2 ^ w := by omega
  have hm'_w : G.numActivePairs < 2 ^ w := by omega
  have h2m'_w : 2 * G.numActivePairs < 2 ^ w := by omega
  have hm2_w : 2 + 2 * G.numActivePairs < 2 ^ w := by omega
  -- 1. r_base := a_src[0]
  obtain ⟨h0_len, h0_val⟩ := enc_getElem_zero G extra hsrc
  let s₁ := s.setReg r_base n
  have hex₁ : Exec w (.assign r_base (.read a_src (.const 0))) s s₁ 3 :=
    .assign (by simp [Expr.eval, checkWord, h0_w, h0_len, h0_val, hn_w])
  -- 2. r_base + 2 := a_src[1]
  obtain ⟨h1_len, h1_val⟩ := enc_getElem_one G extra hsrc
  let s₂ := s₁.setReg (r_base + 2) G.numActivePairs
  have hex₂ : Exec w (.assign (r_base + 2) (.read a_src (.const 1))) s₁ s₂ 3 :=
    .assign (by simp [s₁, Expr.eval, checkWord, hw, h1_len, h1_val, hm'_w])
  -- 3. r_base + 1 := 0
  let s₃ := s₂.setReg (r_base + 1) 0
  have hex₃ : Exec w (.assign (r_base + 1) (.const 0)) s₂ s₃ 2 :=
    .assign (by simp [Expr.eval, checkWord, h0_w])
  -- 4. r_base + 4 := 2 + 2 * (r_base + 2)
  let s₄ := s₃.setReg (r_base + 4) (2 + 2 * G.numActivePairs)
  have hex₄ : Exec w (.assign (r_base + 4)
      (.op .add (.const 2) (.op .mul (.const 2) (.reg (r_base + 2))))) s₃ s₄ 6 :=
    .assign (by simp [s₃, s₂, Expr.eval, BinOp.eval, BinOp.raw, checkWord,
      hw2, hm'_w, h2m'_w, hm2_w])
  -- 5. alloc a_buf (r_base + 4)
  let s₅ := s₄.setArr a_buf (List.replicate (2 + 2 * G.numActivePairs) 0)
  have hex₅ : Exec w (.alloc a_buf (.reg (r_base + 4))) s₄ s₅ (1 + (2 + 2 * G.numActivePairs)) :=
    .alloc (by simp [s₄, Expr.eval, checkWord, hm2_w])
  -- 6. write a_buf 0 r_base
  let s₆ := s₅.writeArr a_buf 0 n
  have hex₆ : Exec w (.write a_buf (.const 0) (.reg r_base)) s₅ s₆ 3 :=
    .write (by simp [Expr.eval, checkWord, h0_w])
      (by simp [s₅, s₄, s₃, s₂, s₁, Expr.eval, checkWord, hn_w])
      (by simp [s₅])
  -- 7. r_base + 4 := 2
  let s₇ := s₆.setReg (r_base + 4) 2
  have hex₇ : Exec w (.assign (r_base + 4) (.const 2)) s₆ s₇ 2 :=
    .assign (by simp [Expr.eval, checkWord, hw2])
  -- 8. r_base + 5 := r_base
  let s₈ := s₇.setReg (r_base + 5) n
  have hex₈ : Exec w (.assign (r_base + 5) (.reg r_base)) s₇ s₈ 2 :=
    .assign (by simp [s₇, s₆, s₅, s₄, s₃, s₂, s₁, Expr.eval, checkWord, hn_w])
  -- 9. r_base + 6 := r_base
  let s₉ := s₈.setReg (r_base + 6) n
  have hex₉ : Exec w (.assign (r_base + 6) (.reg r_base)) s₈ s₉ 2 :=
    .assign (by simp [s₈, s₇, s₆, s₅, s₄, s₃, s₂, s₁, Expr.eval, checkWord, hn_w])
  -- 10. r_base + 3 := 0
  let s₁₀ := s₉.setReg (r_base + 3) 0
  have hex₁₀ : Exec w (.assign (r_base + 3) (.const 0)) s₉ s₁₀ 2 :=
    .assign (by simp [Expr.eval, checkWord, h0_w])
  -- 11. toSimpleGraphEdgeListLoop_exec
  have hbuf₁₀ : s₁₀.arrs a_buf = [n, 0] ++ List.replicate (2 * G.activePairsList.length + 0) 0 := by
    simp only [s₁₀, s₉, s₈, s₇, s₆, s₅, State.setReg_arrs, State.writeArr_arrs_self,
      State.setArr_arrs_self]
    have hrep : 2 + 2 * G.numActivePairs = 1 + (1 + 2 * G.activePairsList.length) := by
      simp [MultiDigraph.numActivePairs]; omega
    rw [hrep, List.replicate_add, List.replicate_add]
    rfl
  have hm_bound₁₀ : 0 + (toSimplePairsAux n n G.activePairsList).length ≤ G.numActivePairs := by
    simp only [Nat.zero_add, MultiDigraph.numActivePairs]
    exact length_toSimplePairsAux_le n n G.activePairsList
  rcases toSimpleGraphEdgeListLoop_exec G extra a_src a_buf r_base hne_sb hw3 hn_w hm3_w
      G.activePairsList [] rfl [n, 0] 0 0 n n rfl hm_bound₁₀ le_rfl le_rfl
      (by simp [s₁₀, s₉, s₈, s₇, s₆, s₅, s₄, s₃, s₂, s₁, hne_sb, hsrc])
      hbuf₁₀
      (by simp [s₁₀, s₉, s₈, s₇, s₆, s₅, s₄, s₃, s₂, s₁])
      (by simp [s₁₀, s₉, s₈, s₇, s₆, s₅, s₄, s₃])
      (by simp [s₁₀, s₉, s₈, s₇, s₆, s₅, s₄, s₃, s₂])
      (by simp [s₁₀])
      (by simp [s₁₀, s₉, s₈, s₇])
      (by simp [s₁₀, s₉, s₈])
      (by simp [s₁₀, s₉]) with
    ⟨s₁₁, t₁₁, extra_buf', hex₁₁, ht₁₁, hbuf₁₁, hr0_11, hr1_11, hr4_11, harr₁₁, hreg₁₁⟩
  rw [toSimplePairsAux_activePairsList] at hbuf₁₁ hr1_11 hr4_11
  rw [Nat.zero_add] at hr1_11
  -- 12. write a_buf 1 (r_base + 1)
  have hm_simple_le : (edgeListOf G.toSimpleGraph).length ≤ G.numActivePairs := by
    rw [← toSimplePairsAux_activePairsList]
    exact length_toSimplePairsAux_le n n G.activePairsList
  have hm_simple_w : (edgeListOf G.toSimpleGraph).length < 2 ^ w := by omega
  let s₁₂ := s₁₁.writeArr a_buf 1 (edgeListOf G.toSimpleGraph).length
  have hex₁₂ : Exec w (.write a_buf (.const 1) (.reg (r_base + 1))) s₁₁ s₁₂ 3 :=
    .write (by simp [Expr.eval, checkWord, hw])
      (by simp [Expr.eval, checkWord, hr1_11, hm_simple_w])
      (by simp [hbuf₁₁])
  have hbuf₁₂ : s₁₂.arrs a_buf = [] ++ encGraph G.toSimpleGraph ++ List.replicate extra_buf' 0 := by
    simp only [s₁₂, State.writeArr_arrs_self, hbuf₁₁, encGraph]
    rfl
  -- 13. readSliceProg a_buf (.const 0) a_dst (.reg (r_base + 4)) (r_base + 7)
  have hlen_enc : (encGraph G.toSimpleGraph).length = 2 + 2 * (edgeListOf G.toSimpleGraph).length := by
    simp [encGraph, length_flatEdges]; omega
  have hr4_12 : s₁₂.regs (r_base + 4) = (encGraph G.toSimpleGraph).length := by
    simpa [s₁₂, encGraph] using hr4_11
  have henc_w : ∀ x ∈ encGraph G.toSimpleGraph, x < 2 ^ w := by
    intro x hx
    simp only [encGraph, List.cons_append, List.nil_append, List.mem_cons] at hx
    rcases hx with rfl | rfl | hx
    · exact hn_w
    · exact hm_simple_w
    · exact all_lt_flatEdges (edgeListOf G.toSimpleGraph) hn_w x hx
  have hoff_len_w : 0 + (encGraph G.toSimpleGraph).length < 2 ^ w := by omega
  rcases readSliceProg_exec a_buf a_dst (.const 0) (r_base + 4) (r_base + 7)
      hne_bd (by omega) [] (encGraph G.toSimpleGraph) (List.replicate extra_buf' 0)
      rfl rfl henc_w hw hoff_len_w
      (by simp [Expr.eval, checkWord, h0_w])
      hbuf₁₂ hr4_12 with
    ⟨s₁₃, t₁₃, hex₁₃, ht₁₃, hdst₁₃, harr₁₃, hreg₁₃⟩
  have hlen_apl : G.activePairsList.length = G.numActivePairs := rfl
  rw [hlen_apl] at ht₁₁
  rw [hlen_enc] at ht₁₃
  dsimp only [Expr.cost] at ht₁₃
  refine ⟨s₁₃, _,
    .seq hex₁ (.seq hex₂ (.seq hex₃ (.seq hex₄ (.seq hex₅ (.seq hex₆
      (.seq hex₇ (.seq hex₈ (.seq hex₉ (.seq hex₁₀ (.seq hex₁₁ (.seq hex₁₂ hex₁₃))))))))))),
    by omega,
    hdst₁₃,
    by rw [hreg₁₃ r_base (by omega)]; exact hr0_11,
    by rw [hreg₁₃ (r_base + 1) (by omega)]; exact hr1_11,
    fun a hab had => by
      rw [harr₁₃ a had]
      simp only [s₁₂, State.writeArr_arrs_ne _ _ _ hab]
      rw [harr₁₁ a hab]
      simp [s₁₀, s₉, s₈, s₇, s₆, s₅, s₄, s₃, s₂, s₁, show (a : Arr) ≠ a_buf from hab],
    fun r hr => by
      rw [hreg₁₃ r (by omega)]
      simp only [s₁₂, State.writeArr_regs]
      rw [hreg₁₁ r hr]
      simp [s₁₀, s₉, s₈, s₇, s₆, s₅, s₄, s₃, s₂, s₁,
        State.setReg_regs_ne _ _ (by omega : (r : Reg) ≠ r_base + 3),
        State.setReg_regs_ne _ _ (by omega : (r : Reg) ≠ r_base + 6),
        State.setReg_regs_ne _ _ (by omega : (r : Reg) ≠ r_base + 5),
        State.setReg_regs_ne _ _ (by omega : (r : Reg) ≠ r_base + 4),
        State.setReg_regs_ne _ _ (by omega : (r : Reg) ≠ r_base + 1),
        State.setReg_regs_ne _ _ (by omega : (r : Reg) ≠ r_base + 2),
        State.setReg_regs_ne _ _ (by omega : (r : Reg) ≠ r_base)]⟩

/-- Word RAM program that reads `G.enc` from `a_src`, writes the flat simple-graph encoding
`encGraph G.toSimpleGraph` into `inArr` (using scratch buffer `a_buf`), and builds the CSR
adjacency list `IsAdjList G.toSimpleGraph a_start a_end a_entries` in `O(n + G.numActivePairs)`
steps. -/
def toSimpleGraphProg (a_src a_buf a_deg a_start a_end a_entries : Arr) (r_base : Reg) : Cmd :=
  .seq (toSimpleGraphEdgeListProg a_src a_buf inArr r_base)
    (parseGraphProg a_deg a_start a_end a_entries r_base)

/-- Specification for `toSimpleGraphProg`: builds both `s'.arrs inArr = encGraph G.toSimpleGraph`
and the CSR representation `IsAdjList G.toSimpleGraph a_start a_end a_entries` from `G.enc` in
`a_src` in at most `23 * n + 184 * G.numActivePairs + 107` steps. -/
theorem toSimpleGraphProg_exec {w n : ℕ} (G : MultiDigraph n) (extra : List ℕ)
    (a_src a_buf a_deg a_start a_end a_entries : ℕ) (r_base : ℕ)
    (hne_sb : a_src ≠ a_buf) (hne_bi : a_buf ≠ inArr)
    (hne_in_deg : (inArr : Arr) ≠ a_deg)
    (hne_in_st : (inArr : Arr) ≠ a_start)
    (hne_in_en : (inArr : Arr) ≠ a_end)
    (hne_in_ent : (inArr : Arr) ≠ a_entries)
    (hne_deg_st : a_deg ≠ a_start) (hne_deg_en : a_deg ≠ a_end) (hne_deg_ent : a_deg ≠ a_entries)
    (hne_se : a_start ≠ a_end) (hne_sent : a_start ≠ a_entries) (hne_eent : a_end ≠ a_entries)
    (hw3 : 3 < 2 ^ w) (hn_w : n < 2 ^ w)
    (hm3_w : 2 + 3 * G.numActivePairs < 2 ^ w)
    {s : State}
    (hsrc : s.arrs a_src = G.enc ++ extra) :
    ∃ s' t,
      Exec w (toSimpleGraphProg a_src a_buf a_deg a_start a_end a_entries r_base) s s' t ∧
      t ≤ 23 * n + 184 * G.numActivePairs + 107 ∧
      s'.arrs inArr = encGraph G.toSimpleGraph ∧
      s'.regs r_base = n ∧
      s'.regs (r_base + 1) = (edgeListOf G.toSimpleGraph).length ∧
      IsAdjList G.toSimpleGraph a_start a_end a_entries
        (edgeNeighbors (edgeListOf G.toSimpleGraph)) s' ∧
      (s'.arrs a_entries).length = 2 * (edgeListOf G.toSimpleGraph).length ∧
      (∀ a : ℕ, a ≠ a_buf → a ≠ inArr → a ≠ a_deg → a ≠ a_start → a ≠ a_end → a ≠ a_entries →
        s'.arrs a = s.arrs a) ∧
      (∀ r < r_base, s'.regs r = s.regs r) := by
  have hw2 : 2 < 2 ^ w := by omega
  rcases toSimpleGraphEdgeListProg_exec G extra a_src a_buf inArr r_base
      hne_sb hne_bi hw3 hn_w hm3_w hsrc with
    ⟨s₁, t₁, hex₁, ht₁, hin₁, hr0_1, hr1_1, harr₁, hreg₁⟩
  let edges := edgeListOf G.toSimpleGraph
  have hm_le : edges.length ≤ G.numActivePairs := by
    dsimp [edges]
    rw [← toSimplePairsAux_activePairsList]
    exact length_toSimplePairsAux_le n n G.activePairsList
  have hm2_w : 2 + 2 * edges.length < 2 ^ w := by omega
  have hin₁' : s₁.arrs inArr = [n, edges.length] ++ flatEdges edges ++ [] := by
    simpa [encGraph, edges] using hin₁
  rcases Triple.parseGraphProg_spec G.toSimpleGraph edges []
      a_deg a_start a_end a_entries r_base
      (isSimpleEdgeList_edgeListOf G.toSimpleGraph)
      hne_in_deg hne_in_st hne_in_en hne_in_ent
      hne_deg_st hne_deg_en hne_deg_ent hne_se hne_sent hne_eent
      hw2 hn_w hm2_w s₁ hin₁' with
    ⟨s₂, t₂, hex₂, ht₂, hin₂, hr0_2, hr1_2, hadj₂, hent₂, _⟩
  dsimp only at ht₂
  refine ⟨s₂, t₁ + t₂, .seq hex₁ hex₂, by omega,
    by simpa [encGraph, edges] using hin₂,
    hr0_2, hr1_2, hadj₂, hent₂,
    fun a hab hai had has hae haent => ?_,
    fun r hr => ?_⟩
  · have hnot_mem : (a : Arr) ∉ (parseGraphProg a_deg a_start a_end a_entries r_base).writtenArrs := by
      simp [parseGraphProg, parsePass1Body, parsePrefixBody, parsePass2Body,
        readEdgeEndpoints, incArrAt, csrAppend, listAppend, forUp, Cmd.writtenArrs,
        show (a : Arr) ≠ a_deg from had,
        show (a : Arr) ≠ a_start from has,
        show (a : Arr) ≠ a_end from hae,
        show (a : Arr) ≠ a_entries from haent]
    rw [Exec.arrs_eq_of_not_mem_writtenArrs hex₂ hnot_mem]
    exact harr₁ a hab hai
  · have hnot_mem : (r : Reg) ∉ (parseGraphProg a_deg a_start a_end a_entries r_base).writtenRegs := by
      simp [parseGraphProg, parsePass1Body, parsePrefixBody, parsePass2Body,
        readEdgeEndpoints, incArrAt, csrAppend, listAppend, forUp, Cmd.writtenRegs,
        show (r : Reg) ≠ r_base by omega,
        show (r : Reg) ≠ r_base + 1 by omega,
        show (r : Reg) ≠ r_base + 2 by omega,
        show (r : Reg) ≠ r_base + 3 by omega,
        show (r : Reg) ≠ r_base + 4 by omega,
        show (r : Reg) ≠ r_base + 5 by omega,
        show (r : Reg) ≠ r_base + 6 by omega]
    rw [Exec.regs_eq_of_not_mem_writtenRegs hex₂ hnot_mem]
    exact hreg₁ r hr

/-! ### 3.5 Deleting a Vertex (`deleteVertexMultiDigraphProg`) -/

theorem MultiDigraph.edgeMult_le_numEdges {n : ℕ} (G : MultiDigraph n) (u v : Fin n) :
    G.edgeMult u v ≤ G.numEdges := by
  unfold MultiDigraph.numEdges
  have h1 : G.edgeMult u v ≤ ∑ y : Fin n, G.edgeMult u y :=
    Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ v)
  have h2 : ∑ y : Fin n, G.edgeMult u y ≤ ∑ x : Fin n, ∑ y : Fin n, G.edgeMult x y :=
    Finset.single_le_sum (f := fun x : Fin n => ∑ y : Fin n, G.edgeMult x y)
      (fun _ _ => Nat.zero_le _) (Finset.mem_univ u)
  exact le_trans h1 h2

theorem MultiDigraph.numActivePairs_deleteVertex {n' : ℕ} (G : MultiDigraph (n' + 1))
    (v₀ : Fin (n' + 1)) :
    (G.deleteVertex v₀).numActivePairs =
      (G.activePairsList.filter (fun p => decide (p.1 ≠ v₀ ∧ p.2 ≠ v₀))).length := by
  have h := congrArg List.length (G.map_succAbove_activePairsList_deleteVertex v₀)
  simpa [MultiDigraph.numActivePairs] using h

/-- Shift register `r_x` by `v₀`: if `r_x < r_del`, leave unchanged; otherwise decrement by `1`. -/
def shiftRegProg (r_x r_del : Reg) : Cmd :=
  .ite (.op .lt (.reg r_x) (.reg r_del))
    .skip
    (.assign r_x (.op .sub (.reg r_x) (.const 1)))

theorem shiftRegProg_exec {w : ℕ} (r_x r_del : ℕ) (x v₀ : ℕ)
    (hw : 1 < 2 ^ w) (hx_w : x < 2 ^ w) (hv_w : v₀ < 2 ^ w)
    {s : State}
    (hrx : s.regs r_x = x) (hrdel : s.regs r_del = v₀) :
    ∃ s' t,
      Exec w (shiftRegProg r_x r_del) s s' t ∧
      t ≤ 7 ∧
      s'.regs r_x = shiftIdx v₀ x ∧
      (∀ a : ℕ, s'.arrs a = s.arrs a) ∧
      (∀ r : ℕ, r ≠ r_x → s'.regs r = s.regs r) := by
  by_cases hlt : x < v₀
  · have hcond : (Expr.op .lt (.reg r_x) (.reg r_del)).eval w s = some 1 := by
      simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hrx, hrdel, hlt, hx_w, hv_w, hw]
    refine ⟨s, 3 + 1, .ite_true hcond (by omega) (.skip s), by omega, ?_,
      fun _ => rfl, fun _ _ => rfl⟩
    simp [shiftIdx, hrx, hlt]
  · have hcond : (Expr.op .lt (.reg r_x) (.reg r_del)).eval w s = some 0 := by
      simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hrx, hrdel, hlt, hx_w, hv_w]
    have hx1_w : x - 1 < 2 ^ w := by omega
    let s₁ := s.setReg r_x (x - 1)
    have hex₁ : Exec w (.assign r_x (.op .sub (.reg r_x) (.const 1))) s s₁ 4 :=
      .assign (by simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hrx, hx_w, hw, hx1_w])
    refine ⟨s₁, 3 + 4, .ite_false hcond hex₁, by omega, ?_,
      fun _ => rfl, fun r hr => State.setReg_regs_ne s _ hr⟩
    simp [s₁, shiftIdx, hlt]

/-- Loop body for `deleteVertexMultiDigraphProg`.
Register layout starting at `r_base` (with `r_del < r_base` holding `v₀.1`):
- `r_base`: `n'` (where `a_src[0] = n' + 1`)
- `r_base + 1`: `m_del` (active pairs of `G.deleteVertex v₀` emitted so far)
- `r_base + 2`: `e_del` (total edges of `G.deleteVertex v₀` accumulated so far)
- `r_base + 3`: `m'` (`G.numActivePairs`)
- `r_base + 4`: loop counter `k` (`0 .. m'`)
- `r_base + 5`: buffer write position `pos` (starts at `2`)
- `r_base + 6`: triple offset `idx = 2 + 3 * k`
- `r_base + 7`: `u` (then shifted to `shiftIdx v₀.1 u.1`)
- `r_base + 8`: `v` (then shifted to `shiftIdx v₀.1 v.1`)
- `r_base + 9`: `mult = G.edgeMult u v` -/
def deleteVertexMultiDigraphBody (a_src a_buf : Arr) (r_del r_base : Reg) : Cmd :=
  .seq (readTripleEndpoints a_src (r_base + 4) (r_base + 6) (r_base + 7) (r_base + 8))
    (.ite (.op .eq (.reg (r_base + 7)) (.reg r_del))
      .skip
      (.ite (.op .eq (.reg (r_base + 8)) (.reg r_del))
        .skip
        (.seq (shiftRegProg (r_base + 7) r_del)
          (.seq (shiftRegProg (r_base + 8) r_del)
            (.seq (.assign (r_base + 9) (.read a_src (.op .add (.reg (r_base + 6)) (.const 2))))
              (.seq (bufPush3 a_buf (r_base + 5) (r_base + 7) (r_base + 8) (r_base + 9))
                (.seq (.assign (r_base + 1) (.op .add (.reg (r_base + 1)) (.const 1)))
                  (.assign (r_base + 2) (.op .add (.reg (r_base + 2)) (.reg (r_base + 9)))))))))))

/-- Word RAM program that reads `G.enc` for `G : MultiDigraph (n' + 1)` from `a_src` and vertex
`v₀ : Fin (n' + 1)` from `r_del`, writes `(G.deleteVertex v₀).enc` into `a_dst` (via `a_buf`),
and leaves `r_base = n'`, `r_base + 1 = (G.deleteVertex v₀).numActivePairs`, and
`r_base + 2 = (G.deleteVertex v₀).numEdges`. -/
def deleteVertexMultiDigraphProg (a_src a_buf a_dst : Arr) (r_del r_base : Reg) : Cmd :=
  .seq (.assign r_base (.op .sub (.read a_src (.const 0)) (.const 1)))
    (.seq (.assign (r_base + 3) (.read a_src (.const 1)))
      (.seq (.assign (r_base + 1) (.const 0))
        (.seq (.assign (r_base + 2) (.const 0))
          (.seq (.assign (r_base + 5) (.op .add (.const 2) (.op .mul (.const 3) (.reg (r_base + 3)))))
            (.seq (.alloc a_buf (.reg (r_base + 5)))
              (.seq (.write a_buf (.const 0) (.reg r_base))
                (.seq (.assign (r_base + 5) (.const 2))
                  (.seq (.assign (r_base + 4) (.const 0))
                    (.seq (forUp (r_base + 4) (.reg (r_base + 3))
                            (deleteVertexMultiDigraphBody a_src a_buf r_del r_base))
                      (.seq (.write a_buf (.const 1) (.reg (r_base + 1)))
                        (readSliceProg a_buf (.const 0) a_dst (.reg (r_base + 5)) (r_base + 6))))))))))))

/-- Suffix-induction specification for the main loop of `deleteVertexMultiDigraphProg`. -/
theorem deleteVertexMultiDigraphLoop_exec {w n' : ℕ} (G : MultiDigraph (n' + 1))
    (v₀ : Fin (n' + 1)) (extra : List ℕ)
    (a_src a_buf : ℕ) (r_del r_base : ℕ)
    (hne_sb : a_src ≠ a_buf)
    (hrdel_lt : r_del < r_base)
    (hw3 : 3 < 2 ^ w) (hn_w : n' + 1 < 2 ^ w)
    (hm3_w : 2 + 3 * G.numActivePairs < 2 ^ w)
    (suff : List (Fin (n' + 1) × Fin (n' + 1))) :
    ∀ (pref : List (Fin (n' + 1) × Fin (n' + 1))),
      G.activePairsList = pref ++ suff →
      ∀ (pfx : List ℕ) (extra_buf m_acc e_acc : ℕ),
        pfx.length = 2 + 3 * m_acc →
        m_acc + (suff.filter (fun p => decide (p.1 ≠ v₀ ∧ p.2 ≠ v₀))).length ≤ G.numActivePairs →
        e_acc + G.sumEdgeMultAvoiding v₀ suff < 2 ^ w →
        ∀ {s : State},
          s.arrs a_src = G.enc ++ extra →
          s.arrs a_buf = pfx ++ List.replicate (3 * suff.length + extra_buf) 0 →
          s.regs r_del = v₀.1 →
          s.regs r_base = n' →
          s.regs (r_base + 1) = m_acc →
          s.regs (r_base + 2) = e_acc →
          s.regs (r_base + 3) = G.numActivePairs →
          s.regs (r_base + 4) = pref.length →
          s.regs (r_base + 5) = pfx.length →
          ∃ s' t extra_buf',
            Exec w (forUp (r_base + 4) (.reg (r_base + 3))
              (deleteVertexMultiDigraphBody a_src a_buf r_del r_base)) s s' t ∧
            t ≤ 3 + 75 * suff.length ∧
            s'.arrs a_buf = pfx ++ G.deleteTriplesAux v₀ suff ++ List.replicate extra_buf' 0 ∧
            s'.regs r_base = n' ∧
            s'.regs (r_base + 1) =
              m_acc + (suff.filter (fun p => decide (p.1 ≠ v₀ ∧ p.2 ≠ v₀))).length ∧
            s'.regs (r_base + 2) = e_acc + G.sumEdgeMultAvoiding v₀ suff ∧
            s'.regs (r_base + 5) = (pfx ++ G.deleteTriplesAux v₀ suff).length ∧
            (∀ a : ℕ, a ≠ a_buf → s'.arrs a = s.arrs a) ∧
            (∀ r < r_base, s'.regs r = s.regs r) := by
  have hw : 1 < 2 ^ w := by omega
  have hw2 : 2 < 2 ^ w := by omega
  have h0_w : 0 < 2 ^ w := by omega
  have hm'_w : G.numActivePairs < 2 ^ w := by omega
  have hv0_w : v₀.1 < 2 ^ w := Nat.lt_trans v₀.2 hn_w
  induction suff with
  | nil =>
    intro pref hsplit pfx extra_buf m_acc e_acc hpfx_len hm_bound he_bound
      s hsrc hbuf hrdel hr0 hr1 hr2 hr3 hr4 hr5
    have hlen_pref : pref.length = G.numActivePairs := by
      have := congrArg List.length hsplit
      simp only [List.append_nil] at this
      exact this.symm
    have hcond : (Expr.op .lt (.reg (r_base + 4)) (.reg (r_base + 3))).eval w s = some 0 := by
      simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hr4, hr3, hlen_pref, hm'_w]
    refine ⟨s, 3, extra_buf, .while_false hcond, by simp, ?_, hr0, ?_, ?_, ?_,
      fun _ _ => rfl, fun _ _ => rfl⟩
    · simpa [MultiDigraph.deleteTriplesAux] using hbuf
    · simpa using hr1
    · simpa [MultiDigraph.sumEdgeMultAvoiding] using hr2
    · simpa [MultiDigraph.deleteTriplesAux] using hr5
  | cons p ps ih =>
    rcases p with ⟨u, v⟩
    intro pref hsplit pfx extra_buf m_acc e_acc hpfx_len hm_bound he_bound
      s hsrc hbuf hrdel hr0 hr1 hr2 hr3 hr4 hr5
    let k := pref.length
    obtain ⟨hk_lt, hget_k⟩ := getElem_of_eq_append_cons hsplit
    have hk_m' : k < G.numActivePairs := hk_lt
    have hk_w : k < 2 ^ w := by omega
    have hcond : (Expr.op .lt (.reg (r_base + 4)) (.reg (r_base + 3))).eval w s = some 1 := by
      simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hr4, hr3, k, hk_m', hk_w, hm'_w, hw]
    -- 1. readTripleEndpoints a_src (r_base + 4) (r_base + 6) (r_base + 7) (r_base + 8)
    rcases readTripleEndpoints_exec G extra a_src (r_base + 4) (r_base + 6) (r_base + 7) (r_base + 8)
        k s (by omega) (by omega) (by omega)
        hw3 hn_w hm3_w hk_m' hsrc hr4 with
      ⟨s₁, t₁, hex₁, ht₁, hr6_1, hr7_1, hr8_1, harr₁, hreg₁⟩
    have hget_u : (G.activePairsList[k]'hk_m').1 = u := congrArg Prod.fst hget_k
    have hget_v : (G.activePairsList[k]'hk_m').2 = v := congrArg Prod.snd hget_k
    rw [hget_u] at hr7_1
    rw [hget_v] at hr8_1
    have hu_w : u.1 < 2 ^ w := Nat.lt_trans u.2 hn_w
    have hv_w : v.1 < 2 ^ w := Nat.lt_trans v.2 hn_w
    have hrdel₁ : s₁.regs r_del = v₀.1 := by
      rw [hreg₁ r_del (by omega) (by omega) (by omega)]; exact hrdel
    have hsplit' : G.activePairsList = (pref ++ [(u, v)]) ++ ps := by
      simp [hsplit, List.append_assoc]
    -- 2. First ite: u = v₀
    by_cases hu_eq : u = v₀
    · have hu_val_eq : u.1 = v₀.1 := congrArg Fin.val hu_eq
      have hcond_u : (Expr.op .eq (.reg (r_base + 7)) (.reg r_del)).eval w s₁ = some 1 := by
        simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hr7_1, hrdel₁, hu_val_eq, hv0_w, hw]
      have hex_ite1 : Exec w
          (.ite (.op .eq (.reg (r_base + 7)) (.reg r_del))
            .skip
            (.ite (.op .eq (.reg (r_base + 8)) (.reg r_del))
              .skip
              (.seq (shiftRegProg (r_base + 7) r_del)
                (.seq (shiftRegProg (r_base + 8) r_del)
                  (.seq (.assign (r_base + 9) (.read a_src (.op .add (.reg (r_base + 6)) (.const 2))))
                    (.seq (bufPush3 a_buf (r_base + 5) (r_base + 7) (r_base + 8) (r_base + 9))
                      (.seq (.assign (r_base + 1) (.op .add (.reg (r_base + 1)) (.const 1)))
                        (.assign (r_base + 2) (.op .add (.reg (r_base + 2)) (.reg (r_base + 9)))))))))))
          s₁ s₁ (3 + 1) :=
        .ite_true hcond_u (by omega) (.skip s₁)
      have hex_body : Exec w (deleteVertexMultiDigraphBody a_src a_buf r_del r_base) s s₁
          (t₁ + (3 + 1)) :=
        .seq hex₁ hex_ite1
      have hr4_1 : s₁.regs (r_base + 4) = k := by
        rw [hreg₁ (r_base + 4) (by omega) (by omega) (by omega)]; exact hr4
      let s₂ := s₁.setReg (r_base + 4) (k + 1)
      have hex_inc : Exec w (.assign (r_base + 4) (.op .add (.reg (r_base + 4)) (.const 1)))
          s₁ s₂ 4 :=
        .assign (by simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hr4_1, hk_w, hw,
          show k + 1 < 2 ^ w by omega])
      have hbuf₂ : s₂.arrs a_buf = pfx ++ List.replicate (3 * ps.length + (extra_buf + 3)) 0 := by
        have hlen_eq : 3 * ((u, v) :: ps).length + extra_buf = 3 * ps.length + (extra_buf + 3) := by
          simp; omega
        rw [← hlen_eq]
        simpa [s₂, harr₁] using hbuf
      have hm_bound' :
          m_acc + (ps.filter (fun p => decide (p.1 ≠ v₀ ∧ p.2 ≠ v₀))).length ≤ G.numActivePairs := by
        simpa [hu_eq] using hm_bound
      have he_bound' : e_acc + G.sumEdgeMultAvoiding v₀ ps < 2 ^ w := by
        simpa [MultiDigraph.sumEdgeMultAvoiding, hu_eq] using he_bound
      rcases ih (pref ++ [(u, v)]) hsplit' pfx (extra_buf + 3) m_acc e_acc
          hpfx_len hm_bound' he_bound'
          (by simp [s₂, harr₁, hsrc])
          hbuf₂
          (by simp [s₂, State.setReg_regs_ne _ _ (by omega : (r_del : Reg) ≠ r_base + 4), hrdel₁])
          (by simp [s₂, hreg₁ r_base (by omega) (by omega) (by omega), hr0])
          (by simp [s₂, hreg₁ (r_base + 1) (by omega) (by omega) (by omega), hr1])
          (by simp [s₂, hreg₁ (r_base + 2) (by omega) (by omega) (by omega), hr2])
          (by simp [s₂, hreg₁ (r_base + 3) (by omega) (by omega) (by omega), hr3])
          (by simp [s₂, k])
          (by simp [s₂, hreg₁ (r_base + 5) (by omega) (by omega) (by omega), hr5]) with
        ⟨s₃, t₃, extra_buf', hex₃, ht₃, hbuf₃, hr0_3, hr1_3, hr2_3, hr5_3, harr₃, hreg₃⟩
      refine ⟨s₃, 3 + ((t₁ + (3 + 1)) + 4) + t₃, extra_buf',
        .while_true hcond (by omega) (.seq hex_body hex_inc) hex₃,
        by simp only [List.length_cons]; omega,
        by simpa [MultiDigraph.deleteTriplesAux, hu_eq] using hbuf₃,
        hr0_3,
        by simpa [hu_eq] using hr1_3,
        by simpa [MultiDigraph.sumEdgeMultAvoiding, hu_eq] using hr2_3,
        by simpa [MultiDigraph.deleteTriplesAux, hu_eq] using hr5_3,
        fun a ha => by rw [harr₃ a ha]; simp [s₂, harr₁],
        fun r hr => by
          rw [hreg₃ r hr]
          simp [s₂, State.setReg_regs_ne _ _ (by omega : (r : Reg) ≠ r_base + 4),
            hreg₁ r (by omega) (by omega) (by omega)]⟩
    · have hu_val_ne : u.1 ≠ v₀.1 := fun h => hu_eq (Fin.ext h)
      have hcond_u : (Expr.op .eq (.reg (r_base + 7)) (.reg r_del)).eval w s₁ = some 0 := by
        simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hr7_1, hrdel₁, hu_val_ne, hu_w, hv0_w]
      -- 3. Second ite: v = v₀
      by_cases hv_eq : v = v₀
      · have hv_val_eq : v.1 = v₀.1 := congrArg Fin.val hv_eq
        have hcond_v : (Expr.op .eq (.reg (r_base + 8)) (.reg r_del)).eval w s₁ = some 1 := by
          simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hr8_1, hrdel₁, hv_val_eq, hv0_w, hw]
        have hex_ite2 : Exec w
            (.ite (.op .eq (.reg (r_base + 8)) (.reg r_del))
              .skip
              (.seq (shiftRegProg (r_base + 7) r_del)
                (.seq (shiftRegProg (r_base + 8) r_del)
                  (.seq (.assign (r_base + 9) (.read a_src (.op .add (.reg (r_base + 6)) (.const 2))))
                    (.seq (bufPush3 a_buf (r_base + 5) (r_base + 7) (r_base + 8) (r_base + 9))
                      (.seq (.assign (r_base + 1) (.op .add (.reg (r_base + 1)) (.const 1)))
                        (.assign (r_base + 2) (.op .add (.reg (r_base + 2)) (.reg (r_base + 9))))))))))
            s₁ s₁ (3 + 1) :=
          .ite_true hcond_v (by omega) (.skip s₁)
        have hex_body : Exec w (deleteVertexMultiDigraphBody a_src a_buf r_del r_base) s s₁
            (t₁ + (3 + (3 + 1))) :=
          .seq hex₁ (.ite_false hcond_u hex_ite2)
        have hr4_1 : s₁.regs (r_base + 4) = k := by
          rw [hreg₁ (r_base + 4) (by omega) (by omega) (by omega)]; exact hr4
        let s₂ := s₁.setReg (r_base + 4) (k + 1)
        have hex_inc : Exec w (.assign (r_base + 4) (.op .add (.reg (r_base + 4)) (.const 1)))
            s₁ s₂ 4 :=
          .assign (by simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hr4_1, hk_w, hw,
            show k + 1 < 2 ^ w by omega])
        have hbuf₂ : s₂.arrs a_buf = pfx ++ List.replicate (3 * ps.length + (extra_buf + 3)) 0 := by
          have hlen_eq : 3 * ((u, v) :: ps).length + extra_buf = 3 * ps.length + (extra_buf + 3) := by
            simp; omega
          rw [← hlen_eq]
          simpa [s₂, harr₁] using hbuf
        have hm_bound' :
            m_acc + (ps.filter (fun p => decide (p.1 ≠ v₀ ∧ p.2 ≠ v₀))).length ≤ G.numActivePairs := by
          simpa [hv_eq] using hm_bound
        have he_bound' : e_acc + G.sumEdgeMultAvoiding v₀ ps < 2 ^ w := by
          simpa [MultiDigraph.sumEdgeMultAvoiding, hv_eq] using he_bound
        rcases ih (pref ++ [(u, v)]) hsplit' pfx (extra_buf + 3) m_acc e_acc
            hpfx_len hm_bound' he_bound'
            (by simp [s₂, harr₁, hsrc])
            hbuf₂
            (by simp [s₂, State.setReg_regs_ne _ _ (by omega : (r_del : Reg) ≠ r_base + 4), hrdel₁])
            (by simp [s₂, hreg₁ r_base (by omega) (by omega) (by omega), hr0])
            (by simp [s₂, hreg₁ (r_base + 1) (by omega) (by omega) (by omega), hr1])
            (by simp [s₂, hreg₁ (r_base + 2) (by omega) (by omega) (by omega), hr2])
            (by simp [s₂, hreg₁ (r_base + 3) (by omega) (by omega) (by omega), hr3])
            (by simp [s₂, k])
            (by simp [s₂, hreg₁ (r_base + 5) (by omega) (by omega) (by omega), hr5]) with
          ⟨s₃, t₃, extra_buf', hex₃, ht₃, hbuf₃, hr0_3, hr1_3, hr2_3, hr5_3, harr₃, hreg₃⟩
        refine ⟨s₃, 3 + ((t₁ + (3 + (3 + 1))) + 4) + t₃, extra_buf',
          .while_true hcond (by omega) (.seq hex_body hex_inc) hex₃,
          by simp only [List.length_cons]; omega,
          by simpa [MultiDigraph.deleteTriplesAux, hv_eq] using hbuf₃,
          hr0_3,
          by simpa [hv_eq] using hr1_3,
          by simpa [MultiDigraph.sumEdgeMultAvoiding, hv_eq] using hr2_3,
          by simpa [MultiDigraph.deleteTriplesAux, hv_eq] using hr5_3,
          fun a ha => by rw [harr₃ a ha]; simp [s₂, harr₁],
          fun r hr => by
            rw [hreg₃ r hr]
            simp [s₂, State.setReg_regs_ne _ _ (by omega : (r : Reg) ≠ r_base + 4),
              hreg₁ r (by omega) (by omega) (by omega)]⟩
      · have hv_val_ne : v.1 ≠ v₀.1 := fun h => hv_eq (Fin.ext h)
        have hcond_v : (Expr.op .eq (.reg (r_base + 8)) (.reg r_del)).eval w s₁ = some 0 := by
          simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hr8_1, hrdel₁, hv_val_ne, hv_w, hv0_w]
        -- 4. Keep branch: shift u, shift v, read mult, bufPush3, inc m_del, inc e_del
        rcases shiftRegProg_exec (r_base + 7) r_del u.1 v₀.1 hw hu_w hv0_w hr7_1 hrdel₁ with
          ⟨s₂, t₂, hex₂, ht₂, hr7_2, harr₂, hreg₂⟩
        have hr8_2 : s₂.regs (r_base + 8) = v.1 := by
          rw [hreg₂ _ (by omega)]; exact hr8_1
        have hrdel₂ : s₂.regs r_del = v₀.1 := by
          rw [hreg₂ _ (by omega)]; exact hrdel₁
        rcases shiftRegProg_exec (r_base + 8) r_del v.1 v₀.1 hw hv_w hv0_w hr8_2 hrdel₂ with
          ⟨s₃, t₃, hex₃, ht₃, hr8_3, harr₃, hreg₃⟩
        let m := G.edgeMult u v
        have he_bound_step : e_acc + (m + G.sumEdgeMultAvoiding v₀ ps) < 2 ^ w := by
          simpa [MultiDigraph.sumEdgeMultAvoiding, hu_eq, hv_eq, m] using he_bound
        have hm_w : m < 2 ^ w := by omega
        have he_acc_w : e_acc < 2 ^ w := by omega
        have he_accm_w : e_acc + m < 2 ^ w := by omega
        obtain ⟨hlen_m, hget_m⟩ := enc_getElem_triple_mult G extra hsrc hk_m'
        rw [hget_u, hget_v] at hget_m
        have hsrc₃ : s₃.arrs a_src = s.arrs a_src := by
          rw [harr₃, harr₂, harr₁]
        have hr6_3 : s₃.regs (r_base + 6) = 2 + 3 * k := by
          rw [hreg₃ _ (by omega), hreg₂ _ (by omega)]; exact hr6_1
        have hidx_w : 2 + 3 * k < 2 ^ w := by omega
        have hidx2_w : 2 + 3 * k + 2 < 2 ^ w := by omega
        have hlen_m₃ : 2 + 3 * k + 2 < (s₃.arrs a_src).length := by rw [hsrc₃]; exact hlen_m
        have hget_m₃ : (s₃.arrs a_src)[2 + 3 * k + 2]'hlen_m₃ = m := by
          simpa [hsrc₃, m] using hget_m
        let s₄ := s₃.setReg (r_base + 9) m
        have hex₄ : Exec w (.assign (r_base + 9)
            (.read a_src (.op .add (.reg (r_base + 6)) (.const 2)))) s₃ s₄ 5 :=
          .assign (by simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hr6_3,
            hidx_w, hw2, hidx2_w, hlen_m₃, hget_m₃, hm_w])
        have hbuf₄ : s₄.arrs a_buf = pfx ++ List.replicate ((3 * ps.length + extra_buf) + 3) 0 := by
          have hlen_eq : 3 * ((u, v) :: ps).length + extra_buf = (3 * ps.length + extra_buf) + 3 := by
            simp; omega
          rw [← hlen_eq]
          simp only [s₄, State.setReg_arrs]
          rw [harr₃, harr₂, harr₁]
          exact hbuf
        have hr5_4 : s₄.regs (r_base + 5) = pfx.length := by
          simp only [s₄, State.setReg_regs_ne _ _ (by omega : (r_base + 5 : Reg) ≠ r_base + 9)]
          rw [hreg₃ _ (by omega), hreg₂ _ (by omega), hreg₁ (r_base + 5) (by omega) (by omega) (by omega)]
          exact hr5
        have hr7_4 : s₄.regs (r_base + 7) = shiftIdx v₀.1 u.1 := by
          simp only [s₄, State.setReg_regs_ne _ _ (by omega : (r_base + 7 : Reg) ≠ r_base + 9)]
          rw [hreg₃ _ (by omega)]
          exact hr7_2
        have hr8_4 : s₄.regs (r_base + 8) = shiftIdx v₀.1 v.1 := by
          simp only [s₄, State.setReg_regs_ne _ _ (by omega : (r_base + 8 : Reg) ≠ r_base + 9)]
          exact hr8_3
        have hr9_4 : s₄.regs (r_base + 9) = m := by simp [s₄]
        have hsu_w : shiftIdx v₀.1 u.1 < 2 ^ w := by
          simp only [shiftIdx]; split_ifs <;> omega
        have hsv_w : shiftIdx v₀.1 v.1 < 2 ^ w := by
          simp only [shiftIdx]; split_ifs <;> omega
        have hflt_uv :
            (List.filter (fun p => decide (p.1 ≠ v₀ ∧ p.2 ≠ v₀)) ((u, v) :: ps)).length =
              (List.filter (fun p => decide (p.1 ≠ v₀ ∧ p.2 ≠ v₀)) ps).length + 1 := by
          simp [hu_eq, hv_eq]
        have hdel_uv :
            G.deleteTriplesAux v₀ ((u, v) :: ps) =
              shiftIdx v₀.1 u.1 :: shiftIdx v₀.1 v.1 :: m :: G.deleteTriplesAux v₀ ps := by
          simp [MultiDigraph.deleteTriplesAux, hu_eq, hv_eq, m]
        have hsum_uv :
            G.sumEdgeMultAvoiding v₀ ((u, v) :: ps) = m + G.sumEdgeMultAvoiding v₀ ps := by
          simp [MultiDigraph.sumEdgeMultAvoiding, hu_eq, hv_eq, m]
        have hm_acc_lt : m_acc + 1 ≤ G.numActivePairs := by
          rw [hflt_uv] at hm_bound
          omega
        have hpos_w : pfx.length + 3 < 2 ^ w := by omega
        rcases bufPush3_exec a_buf (r_base + 5) (r_base + 7) (r_base + 8) (r_base + 9)
            pfx (3 * ps.length + extra_buf) (shiftIdx v₀.1 u.1) (shiftIdx v₀.1 v.1) m
            hw3 hpos_w hsu_w hsv_w hm_w hbuf₄ hr5_4 hr7_4 hr8_4 hr9_4 with
          ⟨s₅, t₅, hex₅, ht₅, hbuf₅, hr5_5, harr₅, hreg₅⟩
        have hr1_5 : s₅.regs (r_base + 1) = m_acc := by
          rw [hreg₅ _ (by omega)]
          simp only [s₄, State.setReg_regs_ne _ _ (by omega : (r_base + 1 : Reg) ≠ r_base + 9)]
          rw [hreg₃ _ (by omega), hreg₂ _ (by omega), hreg₁ (r_base + 1) (by omega) (by omega) (by omega)]
          exact hr1
        have hm_acc_w : m_acc < 2 ^ w := by omega
        have hm_acc1_w : m_acc + 1 < 2 ^ w := by omega
        let s₆ := s₅.setReg (r_base + 1) (m_acc + 1)
        have hex₆ : Exec w (.assign (r_base + 1) (.op .add (.reg (r_base + 1)) (.const 1))) s₅ s₆ 4 :=
          .assign (by simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hr1_5, hm_acc_w, hw, hm_acc1_w])
        have hr2_6 : s₆.regs (r_base + 2) = e_acc := by
          simp only [s₆, State.setReg_regs_ne _ _ (by omega : (r_base + 2 : Reg) ≠ r_base + 1)]
          rw [hreg₅ _ (by omega)]
          simp only [s₄, State.setReg_regs_ne _ _ (by omega : (r_base + 2 : Reg) ≠ r_base + 9)]
          rw [hreg₃ _ (by omega), hreg₂ _ (by omega), hreg₁ (r_base + 2) (by omega) (by omega) (by omega)]
          exact hr2
        have hr9_6 : s₆.regs (r_base + 9) = m := by
          simp only [s₆, State.setReg_regs_ne _ _ (by omega : (r_base + 9 : Reg) ≠ r_base + 1)]
          rw [hreg₅ _ (by omega)]
          exact hr9_4
        let s₇ := s₆.setReg (r_base + 2) (e_acc + m)
        have hex₇ : Exec w (.assign (r_base + 2) (.op .add (.reg (r_base + 2)) (.reg (r_base + 9))))
            s₆ s₇ 4 :=
          .assign (by simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hr2_6, hr9_6,
            he_acc_w, hm_w, he_accm_w])
        have hex_ite2 : Exec w
            (.ite (.op .eq (.reg (r_base + 8)) (.reg r_del))
              .skip
              (.seq (shiftRegProg (r_base + 7) r_del)
                (.seq (shiftRegProg (r_base + 8) r_del)
                  (.seq (.assign (r_base + 9) (.read a_src (.op .add (.reg (r_base + 6)) (.const 2))))
                    (.seq (bufPush3 a_buf (r_base + 5) (r_base + 7) (r_base + 8) (r_base + 9))
                      (.seq (.assign (r_base + 1) (.op .add (.reg (r_base + 1)) (.const 1)))
                        (.assign (r_base + 2) (.op .add (.reg (r_base + 2)) (.reg (r_base + 9))))))))))
            s₁ s₇ (3 + (t₂ + (t₃ + (5 + (t₅ + (4 + 4)))))) :=
          .ite_false hcond_v (.seq hex₂ (.seq hex₃ (.seq hex₄ (.seq hex₅ (.seq hex₆ hex₇)))))
        have hex_body : Exec w (deleteVertexMultiDigraphBody a_src a_buf r_del r_base) s s₇
            (t₁ + (3 + (3 + (t₂ + (t₃ + (5 + (t₅ + (4 + 4)))))))) :=
          .seq hex₁ (.ite_false hcond_u hex_ite2)
        have hr4_7 : s₇.regs (r_base + 4) = k := by
          simp only [s₇, s₆,
            State.setReg_regs_ne _ _ (by omega : (r_base + 4 : Reg) ≠ r_base + 2),
            State.setReg_regs_ne _ _ (by omega : (r_base + 4 : Reg) ≠ r_base + 1)]
          rw [hreg₅ _ (by omega)]
          simp only [s₄, State.setReg_regs_ne _ _ (by omega : (r_base + 4 : Reg) ≠ r_base + 9)]
          rw [hreg₃ _ (by omega), hreg₂ _ (by omega), hreg₁ (r_base + 4) (by omega) (by omega) (by omega)]
          exact hr4
        let s₈ := s₇.setReg (r_base + 4) (k + 1)
        have hex_inc : Exec w (.assign (r_base + 4) (.op .add (.reg (r_base + 4)) (.const 1)))
            s₇ s₈ 4 :=
          .assign (by simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hr4_7, hk_w, hw,
            show k + 1 < 2 ^ w by omega])
        have hm_bound' :
            (m_acc + 1) + (ps.filter (fun p => decide (p.1 ≠ v₀ ∧ p.2 ≠ v₀))).length ≤
              G.numActivePairs := by
          rw [hflt_uv] at hm_bound
          omega
        have he_bound' : (e_acc + m) + G.sumEdgeMultAvoiding v₀ ps < 2 ^ w := by omega
        rcases ih (pref ++ [(u, v)]) hsplit' (pfx ++ [shiftIdx v₀.1 u.1, shiftIdx v₀.1 v.1, m])
            extra_buf (m_acc + 1) (e_acc + m)
            (by simp [hpfx_len]; omega) hm_bound' he_bound' (s := s₈)
            (by simp only [s₈, s₇, s₆, State.setReg_arrs]; rw [harr₅ a_src hne_sb];
                simp only [s₄, State.setReg_arrs]; rw [harr₃, harr₂, harr₁]; exact hsrc)
            (by simpa [s₈, s₇, s₆] using hbuf₅)
            (by simp only [s₈, s₇, s₆,
                State.setReg_regs_ne _ _ (by omega : (r_del : Reg) ≠ r_base + 4),
                State.setReg_regs_ne _ _ (by omega : (r_del : Reg) ≠ r_base + 2),
                State.setReg_regs_ne _ _ (by omega : (r_del : Reg) ≠ r_base + 1)];
                rw [hreg₅ _ (by omega)];
                simp only [s₄, State.setReg_regs_ne _ _ (by omega : (r_del : Reg) ≠ r_base + 9)];
                rw [hreg₃ _ (by omega)]; exact hrdel₂)
            (by simp only [s₈, s₇, s₆,
                State.setReg_regs_ne _ _ (by omega : (r_base : Reg) ≠ r_base + 4),
                State.setReg_regs_ne _ _ (by omega : (r_base : Reg) ≠ r_base + 2),
                State.setReg_regs_ne _ _ (by omega : (r_base : Reg) ≠ r_base + 1)];
                rw [hreg₅ _ (by omega)];
                simp only [s₄, State.setReg_regs_ne _ _ (by omega : (r_base : Reg) ≠ r_base + 9)];
                rw [hreg₃ _ (by omega), hreg₂ _ (by omega), hreg₁ r_base (by omega) (by omega) (by omega)];
                exact hr0)
            (by simp [s₈, s₇, s₆])
            (by simp [s₈, s₇])
            (by simp only [s₈, s₇, s₆,
                State.setReg_regs_ne _ _ (by omega : (r_base + 3 : Reg) ≠ r_base + 4),
                State.setReg_regs_ne _ _ (by omega : (r_base + 3 : Reg) ≠ r_base + 2),
                State.setReg_regs_ne _ _ (by omega : (r_base + 3 : Reg) ≠ r_base + 1)];
                rw [hreg₅ _ (by omega)];
                simp only [s₄, State.setReg_regs_ne _ _ (by omega : (r_base + 3 : Reg) ≠ r_base + 9)];
                rw [hreg₃ _ (by omega), hreg₂ _ (by omega), hreg₁ (r_base + 3) (by omega) (by omega) (by omega)];
                exact hr3)
            (by simp [s₈, k])
            (by simp [s₈, s₇, s₆, hr5_5]) with
          ⟨s₉, t₉, extra_buf', hex₉, ht₉, hbuf₉, hr0_9, hr1_9, hr2_9, hr5_9, harr₉, hreg₉⟩
        refine ⟨s₉, 3 + ((t₁ + (3 + (3 + (t₂ + (t₃ + (5 + (t₅ + (4 + 4)))))))) + 4) + t₉, extra_buf',
          .while_true hcond (by omega) (.seq hex_body hex_inc) hex₉,
          by simp only [List.length_cons]; omega,
          by rw [hdel_uv]; simpa [List.append_assoc] using hbuf₉,
          hr0_9,
          by rw [hflt_uv]; omega,
          by rw [hsum_uv, hr2_9]; omega,
          by rw [hdel_uv]; simpa [List.append_assoc] using hr5_9,
          fun a ha => by
            rw [harr₉ a ha]
            simp only [s₈, s₇, s₆, State.setReg_arrs]
            rw [harr₅ a ha]
            simp only [s₄, State.setReg_arrs]
            rw [harr₃, harr₂, harr₁],
          fun r hr => by
            rw [hreg₉ r hr]
            simp only [s₈, s₇, s₆,
              State.setReg_regs_ne _ _ (by omega : (r : Reg) ≠ r_base + 4),
              State.setReg_regs_ne _ _ (by omega : (r : Reg) ≠ r_base + 2),
              State.setReg_regs_ne _ _ (by omega : (r : Reg) ≠ r_base + 1)]
            rw [hreg₅ r (by omega)]
            simp only [s₄, State.setReg_regs_ne _ _ (by omega : (r : Reg) ≠ r_base + 9)]
            rw [hreg₃ r (by omega), hreg₂ r (by omega), hreg₁ r (by omega) (by omega) (by omega)]⟩

/-- Specification for `deleteVertexMultiDigraphProg`: deletes vertex `v₀ : Fin (n' + 1)` from
`G : MultiDigraph (n' + 1)` in `O(G.numActivePairs + 1)` steps, writing `(G.deleteVertex v₀).enc`
into `a_dst` and setting `r_base = n'`, `r_base + 1 = (G.deleteVertex v₀).numActivePairs`, and
`r_base + 2 = (G.deleteVertex v₀).numEdges`. -/
theorem deleteVertexMultiDigraphProg_exec {w n' : ℕ} (G : MultiDigraph (n' + 1))
    (v₀ : Fin (n' + 1)) (extra : List ℕ)
    (a_src a_buf a_dst : ℕ) (r_del r_base : ℕ)
    (hne_sb : a_src ≠ a_buf) (hne_bd : a_buf ≠ a_dst)
    (hrdel_lt : r_del < r_base)
    (hw3 : 3 < 2 ^ w) (hn_w : n' + 1 < 2 ^ w)
    (hm3_w : 2 + 3 * G.numActivePairs < 2 ^ w)
    (hedges_w : (G.deleteVertex v₀).numEdges < 2 ^ w)
    {s : State}
    (hsrc : s.arrs a_src = G.enc ++ extra)
    (hrdel : s.regs r_del = v₀.1) :
    ∃ s' t,
      Exec w (deleteVertexMultiDigraphProg a_src a_buf a_dst r_del r_base) s s' t ∧
      t ≤ 126 * G.numActivePairs + 80 ∧
      s'.arrs a_dst = (G.deleteVertex v₀).enc ∧
      s'.regs r_base = n' ∧
      s'.regs (r_base + 1) = (G.deleteVertex v₀).numActivePairs ∧
      s'.regs (r_base + 2) = (G.deleteVertex v₀).numEdges ∧
      (∀ a : ℕ, a ≠ a_buf → a ≠ a_dst → s'.arrs a = s.arrs a) ∧
      (∀ r < r_base, s'.regs r = s.regs r) := by
  have hw : 1 < 2 ^ w := by omega
  have hw2 : 2 < 2 ^ w := by omega
  have h0_w : 0 < 2 ^ w := by omega
  have hn'_w : n' < 2 ^ w := by omega
  have hm'_w : G.numActivePairs < 2 ^ w := by omega
  have h3m'_w : 3 * G.numActivePairs < 2 ^ w := by omega
  -- 1. r_base := a_src[0] - 1
  obtain ⟨h0_len, h0_val⟩ := enc_getElem_zero G extra hsrc
  let s₁ := s.setReg r_base n'
  have hex₁ : Exec w (.assign r_base (.op .sub (.read a_src (.const 0)) (.const 1))) s s₁ 5 :=
    .assign (by simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord,
      h0_w, h0_len, h0_val, hn_w, hw, hn'_w])
  -- 2. r_base + 3 := a_src[1]
  obtain ⟨h1_len, h1_val⟩ := enc_getElem_one G extra hsrc
  let s₂ := s₁.setReg (r_base + 3) G.numActivePairs
  have hex₂ : Exec w (.assign (r_base + 3) (.read a_src (.const 1))) s₁ s₂ 3 :=
    .assign (by simp [s₁, Expr.eval, checkWord, hw, h1_len, h1_val, hm'_w])
  -- 3. r_base + 1 := 0
  let s₃ := s₂.setReg (r_base + 1) 0
  have hex₃ : Exec w (.assign (r_base + 1) (.const 0)) s₂ s₃ 2 :=
    .assign (by simp [Expr.eval, checkWord, h0_w])
  -- 4. r_base + 2 := 0
  let s₄ := s₃.setReg (r_base + 2) 0
  have hex₄ : Exec w (.assign (r_base + 2) (.const 0)) s₃ s₄ 2 :=
    .assign (by simp [Expr.eval, checkWord, h0_w])
  -- 5. r_base + 5 := 2 + 3 * (r_base + 3)
  let s₅ := s₄.setReg (r_base + 5) (2 + 3 * G.numActivePairs)
  have hex₅ : Exec w (.assign (r_base + 5)
      (.op .add (.const 2) (.op .mul (.const 3) (.reg (r_base + 3))))) s₄ s₅ 6 :=
    .assign (by simp [s₄, s₃, s₂, Expr.eval, BinOp.eval, BinOp.raw, checkWord,
      hw2, hw3, hm'_w, h3m'_w, hm3_w])
  -- 6. alloc a_buf (r_base + 5)
  let s₆ := s₅.setArr a_buf (List.replicate (2 + 3 * G.numActivePairs) 0)
  have hex₆ : Exec w (.alloc a_buf (.reg (r_base + 5))) s₅ s₆ (1 + (2 + 3 * G.numActivePairs)) :=
    .alloc (by simp [s₅, Expr.eval, checkWord, hm3_w])
  -- 7. write a_buf 0 r_base
  let s₇ := s₆.writeArr a_buf 0 n'
  have hex₇ : Exec w (.write a_buf (.const 0) (.reg r_base)) s₆ s₇ 3 :=
    .write (by simp [Expr.eval, checkWord, h0_w])
      (by simp [s₆, s₅, s₄, s₃, s₂, s₁, Expr.eval, checkWord, hn'_w])
      (by simp [s₆])
  -- 8. r_base + 5 := 2
  let s₈ := s₇.setReg (r_base + 5) 2
  have hex₈ : Exec w (.assign (r_base + 5) (.const 2)) s₇ s₈ 2 :=
    .assign (by simp [Expr.eval, checkWord, hw2])
  -- 9. r_base + 4 := 0
  let s₉ := s₈.setReg (r_base + 4) 0
  have hex₉ : Exec w (.assign (r_base + 4) (.const 0)) s₈ s₉ 2 :=
    .assign (by simp [Expr.eval, checkWord, h0_w])
  -- 10. deleteVertexMultiDigraphLoop_exec
  have hbuf₉ : s₉.arrs a_buf = [n', 0] ++ List.replicate (3 * G.activePairsList.length + 0) 0 := by
    simp only [s₉, s₈, s₇, s₆, State.setReg_arrs, State.writeArr_arrs_self,
      State.setArr_arrs_self]
    have hrep : 2 + 3 * G.numActivePairs = 1 + (1 + 3 * G.activePairsList.length) := by
      simp [MultiDigraph.numActivePairs]; omega
    rw [hrep, List.replicate_add, List.replicate_add]
    rfl
  have hm_bound₉ :
      0 + (G.activePairsList.filter (fun p => decide (p.1 ≠ v₀ ∧ p.2 ≠ v₀))).length ≤
        G.numActivePairs := by
    simp only [Nat.zero_add, MultiDigraph.numActivePairs]
    exact List.length_filter_le _ _
  have he_bound₉ : 0 + G.sumEdgeMultAvoiding v₀ G.activePairsList < 2 ^ w := by
    simpa [MultiDigraph.sumEdgeMultAvoiding_activePairsList] using hedges_w
  rcases deleteVertexMultiDigraphLoop_exec G v₀ extra a_src a_buf r_del r_base
      hne_sb hrdel_lt hw3 hn_w hm3_w
      G.activePairsList [] rfl [n', 0] 0 0 0 rfl hm_bound₉ he_bound₉
      (by simp [s₉, s₈, s₇, s₆, s₅, s₄, s₃, s₂, s₁, hne_sb, hsrc])
      hbuf₉
      (by simp [s₉, s₈, s₇, s₆, s₅, s₄, s₃, s₂, s₁,
          State.setReg_regs_ne _ _ (by omega : (r_del : Reg) ≠ r_base + 4),
          State.setReg_regs_ne _ _ (by omega : (r_del : Reg) ≠ r_base + 5),
          State.setReg_regs_ne _ _ (by omega : (r_del : Reg) ≠ r_base + 2),
          State.setReg_regs_ne _ _ (by omega : (r_del : Reg) ≠ r_base + 1),
          State.setReg_regs_ne _ _ (by omega : (r_del : Reg) ≠ r_base + 3),
          State.setReg_regs_ne _ _ (by omega : (r_del : Reg) ≠ r_base), hrdel])
      (by simp [s₉, s₈, s₇, s₆, s₅, s₄, s₃, s₂, s₁])
      (by simp [s₉, s₈, s₇, s₆, s₅, s₄, s₃])
      (by simp [s₉, s₈, s₇, s₆, s₅, s₄])
      (by simp [s₉, s₈, s₇, s₆, s₅, s₄, s₃, s₂])
      (by simp [s₉])
      (by simp [s₉, s₈]) with
    ⟨s₁₀, t₁₀, extra_buf', hex₁₀, ht₁₀, hbuf₁₀, hr0_10, hr1_10, hr2_10, hr5_10, harr₁₀, hreg₁₀⟩
  rw [← MultiDigraph.flatTriples_deleteVertex] at hbuf₁₀ hr5_10
  rw [Nat.zero_add, ← MultiDigraph.numActivePairs_deleteVertex] at hr1_10
  rw [Nat.zero_add, MultiDigraph.sumEdgeMultAvoiding_activePairsList] at hr2_10
  -- 11. write a_buf 1 (r_base + 1)
  have hdel_le : (G.deleteVertex v₀).numActivePairs ≤ G.numActivePairs := by
    rw [MultiDigraph.numActivePairs_deleteVertex, MultiDigraph.numActivePairs]
    exact List.length_filter_le _ _
  have hdel_m'_w : (G.deleteVertex v₀).numActivePairs < 2 ^ w := by omega
  let s₁₁ := s₁₀.writeArr a_buf 1 (G.deleteVertex v₀).numActivePairs
  have hex₁₁ : Exec w (.write a_buf (.const 1) (.reg (r_base + 1))) s₁₀ s₁₁ 3 :=
    .write (by simp [Expr.eval, checkWord, hw])
      (by simp [Expr.eval, checkWord, hr1_10, hdel_m'_w])
      (by simp [hbuf₁₀])
  have hbuf₁₁ : s₁₁.arrs a_buf = [] ++ (G.deleteVertex v₀).enc ++ List.replicate extra_buf' 0 := by
    simp only [s₁₁, State.writeArr_arrs_self, hbuf₁₀, MultiDigraph.enc]
    rfl
  -- 12. readSliceProg a_buf (.const 0) a_dst (.reg (r_base + 5)) (r_base + 6)
  have hlen_enc_del : (G.deleteVertex v₀).enc.length = 2 + 3 * (G.deleteVertex v₀).numActivePairs :=
    (G.deleteVertex v₀).length_enc
  have hr5_11 : s₁₁.regs (r_base + 5) = (G.deleteVertex v₀).enc.length := by
    simpa [s₁₁, MultiDigraph.enc] using hr5_10
  have henc_w : ∀ x ∈ (G.deleteVertex v₀).enc, x < 2 ^ w := by
    intro x hx
    simp only [MultiDigraph.enc, List.cons_append, List.nil_append, List.mem_cons] at hx
    rcases hx with rfl | rfl | hx
    · exact hn'_w
    · exact hdel_m'_w
    · exact all_lt_flatTriples (G.deleteVertex v₀) (G.deleteVertex v₀).activePairsList hn'_w
        (fun p _ => Nat.lt_of_le_of_lt ((G.deleteVertex v₀).edgeMult_le_numEdges p.1 p.2) hedges_w)
        x hx
  have hoff_len_w : 0 + (G.deleteVertex v₀).enc.length < 2 ^ w := by omega
  rcases readSliceProg_exec a_buf a_dst (.const 0) (r_base + 5) (r_base + 6)
      hne_bd (by omega) [] (G.deleteVertex v₀).enc (List.replicate extra_buf' 0)
      rfl rfl henc_w hw hoff_len_w
      (by simp [Expr.eval, checkWord, h0_w])
      hbuf₁₁ hr5_11 with
    ⟨s₁₂, t₁₂, hex₁₂, ht₁₂, hdst₁₂, harr₁₂, hreg₁₂⟩
  have hlen_apl : G.activePairsList.length = G.numActivePairs := rfl
  rw [hlen_apl] at ht₁₀
  rw [hlen_enc_del] at ht₁₂
  dsimp only [Expr.cost] at ht₁₂
  refine ⟨s₁₂, _,
    .seq hex₁ (.seq hex₂ (.seq hex₃ (.seq hex₄ (.seq hex₅ (.seq hex₆
      (.seq hex₇ (.seq hex₈ (.seq hex₉ (.seq hex₁₀ (.seq hex₁₁ hex₁₂)))))))))),
    by omega,
    hdst₁₂,
    by rw [hreg₁₂ r_base (by omega)]; exact hr0_10,
    by rw [hreg₁₂ (r_base + 1) (by omega)]; exact hr1_10,
    by rw [hreg₁₂ (r_base + 2) (by omega)]; exact hr2_10,
    fun a hab had => by
      rw [harr₁₂ a had]
      simp only [s₁₁, State.writeArr_arrs_ne _ _ _ hab]
      rw [harr₁₀ a hab]
      simp [s₉, s₈, s₇, s₆, s₅, s₄, s₃, s₂, s₁, show (a : Arr) ≠ a_buf from hab],
    fun r hr => by
      rw [hreg₁₂ r (by omega)]
      simp only [s₁₁, State.writeArr_regs]
      rw [hreg₁₀ r hr]
      simp [s₉, s₈, s₇, s₆, s₅, s₄, s₃, s₂, s₁,
        State.setReg_regs_ne _ _ (by omega : (r : Reg) ≠ r_base + 4),
        State.setReg_regs_ne _ _ (by omega : (r : Reg) ≠ r_base + 5),
        State.setReg_regs_ne _ _ (by omega : (r : Reg) ≠ r_base + 2),
        State.setReg_regs_ne _ _ (by omega : (r : Reg) ≠ r_base + 1),
        State.setReg_regs_ne _ _ (by omega : (r : Reg) ≠ r_base + 3),
        State.setReg_regs_ne _ _ (by omega : (r : Reg) ≠ r_base)]⟩

/-! ### 3.6 Deleting the `v₀`-th Entry of an Array (`deleteNthArrProg`) -/

/-- Loop body for `deleteNthArrProg`: copies `a_arr[(v₀.succAbove i).1]` into `a_buf[i]`. -/
def deleteNthArrBody (a_arr a_buf : Arr) (r_del r_base : Reg) : Cmd :=
  .seq
    (.ite (.op .lt (.reg r_base) (.reg r_del))
      (.assign (r_base + 1) (.read a_arr (.reg r_base)))
      (.assign (r_base + 1) (.read a_arr (.op .add (.reg r_base) (.const 1)))))
    (.write a_buf (.reg r_base) (.reg (r_base + 1)))

/-- Word RAM program that deletes the `v₀`-th entry (`r_del = v₀.1`) from array `a_arr` of length
`n' + 1` (where `r_n_new = n'`), updating `a_arr` in place (using scratch buffer `a_buf`) to
`List.ofFn (f ∘ v₀.succAbove)` in `O(n' + 1)` steps. -/
def deleteNthArrProg (a_arr a_buf : Arr) (r_n_new r_del r_base : Reg) : Cmd :=
  .seq (.alloc a_buf (.reg r_n_new))
    (.seq (.assign r_base (.const 0))
      (.seq (forUp r_base (.reg r_n_new) (deleteNthArrBody a_arr a_buf r_del r_base))
        (readSliceProg a_buf (.const 0) a_arr (.reg r_n_new) (r_base + 2))))

/-- Specification for `deleteNthArrProg`: updates `s.arrs a_arr = List.ofFn f` in place to
`List.ofFn (f ∘ v₀.succAbove)` in at most `35 * n' + 15` steps. -/
theorem deleteNthArrProg_exec {w n' : ℕ} (f : Fin (n' + 1) → ℕ) (v₀ : Fin (n' + 1))
    (a_arr a_buf : ℕ) (r_n_new r_del r_base : ℕ)
    (hne_ab : a_arr ≠ a_buf)
    (hrn_lt : r_n_new < r_base) (hrdel_lt : r_del < r_base)
    (hw : 1 < 2 ^ w) (hn_w : n' + 1 < 2 ^ w)
    (hf_w : ∀ u : Fin (n' + 1), f u < 2 ^ w)
    {s : State}
    (harr : s.arrs a_arr = List.ofFn f)
    (hrn : s.regs r_n_new = n')
    (hrdel : s.regs r_del = v₀.1) :
    ∃ s' t,
      Exec w (deleteNthArrProg a_arr a_buf r_n_new r_del r_base) s s' t ∧
      t ≤ 35 * n' + 15 ∧
      s'.arrs a_arr = List.ofFn (f ∘ v₀.succAbove) ∧
      (∀ a : ℕ, a ≠ a_arr → a ≠ a_buf → s'.arrs a = s.arrs a) ∧
      (∀ r < r_base, s'.regs r = s.regs r) := by
  have h0_w : 0 < 2 ^ w := by omega
  have hn'_w : n' < 2 ^ w := by omega
  have hv0_w : v₀.1 < 2 ^ w := Nat.lt_trans v₀.2 hn_w
  -- 1. alloc a_buf (.reg r_n_new)
  let s₁ := s.setArr a_buf (List.replicate n' 0)
  have hex₁ : Exec w (.alloc a_buf (.reg r_n_new)) s s₁ (1 + n') :=
    .alloc (by simp [Expr.eval, checkWord, hrn, hn'_w])
  -- 2. r_base := 0
  let s₂ := s₁.setReg r_base 0
  have hex₂ : Exec w (.assign r_base (.const 0)) s₁ s₂ 2 :=
    .assign (by simp [Expr.eval, checkWord, h0_w])
  -- 3. forUp r_base (.reg r_n_new) (deleteNthArrBody a_arr a_buf r_del r_base)
  let Inv (k : ℕ) (st : State) : Prop :=
    st.arrs a_arr = List.ofFn f ∧
    (∃ (hlen : (st.arrs a_buf).length = n'),
      ∀ j : Fin n', j.1 < k →
        (st.arrs a_buf)[j.1]'(by rw [hlen]; exact j.2) = f (v₀.succAbove j)) ∧
    st.regs r_n_new = n' ∧
    st.regs r_del = v₀.1 ∧
    st.regs r_base = k ∧
    (∀ a : ℕ, a ≠ a_buf → st.arrs a = s.arrs a) ∧
    (∀ r < r_base, st.regs r = s.regs r)
  have hInv₀ : Inv 0 s₂ := by
    refine ⟨by simp [s₂, s₁, hne_ab, harr],
      ⟨by simp [s₂, s₁], fun j hj => by omega⟩,
      by simp [s₂, s₁, State.setReg_regs_ne _ _ (by omega : (r_n_new : Reg) ≠ r_base), hrn],
      by simp [s₂, s₁, State.setReg_regs_ne _ _ (by omega : (r_del : Reg) ≠ r_base), hrdel],
      by simp [s₂],
      fun a ha => by simp [s₂, s₁, show (a : Arr) ≠ a_buf from ha],
      fun r hr => by simp [s₂, s₁, State.setReg_regs_ne _ _ (by omega : (r : Reg) ≠ r_base)]⟩
  have hLoop :
      ⦃Inv 0⦄[w]
        forUp r_base (.reg r_n_new) (deleteNthArrBody a_arr a_buf r_del r_base)
      ⦃Inv n'⦄ ≤ fun _ => 3 + n' * (7 + 11) := by
    apply Triple.forUp_const Inv n' 11 hw hn'_w
    · intro k _ st ⟨_, _, hrn_k, _, hrb_k, _, _⟩
      exact ⟨hrb_k, by simp [Expr.eval, checkWord, hrn_k, hn'_w]⟩
    · intro k hk st ⟨harr_k, ⟨hlen_k, hbuf_k⟩, hrn_k, hrdel_k, hrb_k, harr_other, hreg_other⟩
      have hk_w : k < 2 ^ w := by omega
      have hk1_w : k + 1 < 2 ^ w := by omega
      let kFin : Fin n' := ⟨k, hk⟩
      have hlen_f : (st.arrs a_arr).length = n' + 1 := by simp [harr_k]
      have hval_w : f (v₀.succAbove kFin) < 2 ^ w := hf_w (v₀.succAbove kFin)
      have hex_ite :
          ∃ t_ite, t_ite ≤ 8 ∧
            Exec w
              (.ite (.op .lt (.reg r_base) (.reg r_del))
                (.assign (r_base + 1) (.read a_arr (.reg r_base)))
                (.assign (r_base + 1) (.read a_arr (.op .add (.reg r_base) (.const 1)))))
              st (st.setReg (r_base + 1) (f (v₀.succAbove kFin))) t_ite := by
        by_cases hlt : k < v₀.1
        · have hcond : (Expr.op .lt (.reg r_base) (.reg r_del)).eval w st = some 1 := by
            simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hrb_k, hrdel_k, hlt, hk_w, hv0_w, hw]
          have hsucc_eq : v₀.succAbove kFin = ⟨k, by omega⟩ := by
            ext
            simp [Fin.succAbove, Fin.lt_def, kFin, hlt]
          have hk_lt_len : k < (st.arrs a_arr).length := by omega
          have hget_k : (st.arrs a_arr)[k]'hk_lt_len = f (v₀.succAbove kFin) := by
            have h1 : (st.arrs a_arr)[k]'hk_lt_len = (List.ofFn f)[k]'(by simp; omega) := by
              simp only [harr_k]
            rw [h1, List.getElem_ofFn, hsucc_eq]
          have hex_r : Exec w (.assign (r_base + 1) (.read a_arr (.reg r_base)))
              st (st.setReg (r_base + 1) (f (v₀.succAbove kFin))) 3 :=
            .assign (by simp [Expr.eval, checkWord, hrb_k, hk_w, hk_lt_len, hget_k, hval_w])
          exact ⟨3 + 3, by omega, .ite_true hcond (by omega) hex_r⟩
        · have hcond : (Expr.op .lt (.reg r_base) (.reg r_del)).eval w st = some 0 := by
            simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hrb_k, hrdel_k, hlt, hk_w, hv0_w]
          have hsucc_eq : v₀.succAbove kFin = ⟨k + 1, by omega⟩ := by
            ext
            simp [Fin.succAbove, Fin.lt_def, kFin, hlt]
          have hk1_lt_len : k + 1 < (st.arrs a_arr).length := by omega
          have hget_k1 : (st.arrs a_arr)[k + 1]'hk1_lt_len = f (v₀.succAbove kFin) := by
            have h1 : (st.arrs a_arr)[k + 1]'hk1_lt_len = (List.ofFn f)[k + 1]'(by simp; omega) := by
              simp only [harr_k]
            rw [h1, List.getElem_ofFn, hsucc_eq]
          have hex_r : Exec w (.assign (r_base + 1) (.read a_arr (.op .add (.reg r_base) (.const 1))))
              st (st.setReg (r_base + 1) (f (v₀.succAbove kFin))) 5 :=
            .assign (by simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hrb_k, hk_w, hw,
              hk1_w, hk1_lt_len, hget_k1, hval_w])
          exact ⟨3 + 5, by omega, .ite_false hcond hex_r⟩
      rcases hex_ite with ⟨t_ite, ht_ite, hex_i⟩
      let st₁ := st.setReg (r_base + 1) (f (v₀.succAbove kFin))
      let st₂ := st₁.writeArr a_buf k (f (v₀.succAbove kFin))
      have hex_w : Exec w (.write a_buf (.reg r_base) (.reg (r_base + 1))) st₁ st₂ 3 :=
        .write (by simp [st₁, Expr.eval, checkWord, hrb_k, hk_w])
          (by simp [st₁, Expr.eval, checkWord, hval_w])
          (by simp [st₁, hlen_k, hk])
      refine ⟨st₂, t_ite + 3, .seq hex_i hex_w, show t_ite + 3 ≤ 11 by omega,
        ⟨by simp [st₂, st₁, hne_ab, harr_k],
         ⟨by simp [st₂, st₁, hlen_k], fun j hj => ?_⟩,
         by simp [st₂, st₁,
              State.setReg_regs_ne _ _ (by omega : (r_n_new : Reg) ≠ r_base),
              State.setReg_regs_ne _ _ (by omega : (r_n_new : Reg) ≠ r_base + 1), hrn_k],
         by simp [st₂, st₁,
              State.setReg_regs_ne _ _ (by omega : (r_del : Reg) ≠ r_base),
              State.setReg_regs_ne _ _ (by omega : (r_del : Reg) ≠ r_base + 1), hrdel_k],
         by simp [st₂, st₁],
         fun a ha => by simp [st₂, st₁, show (a : Arr) ≠ a_buf from ha, harr_other a ha],
         fun r hr => by simp [st₂, st₁,
           State.setReg_regs_ne _ _ (by omega : (r : Reg) ≠ r_base),
           State.setReg_regs_ne _ _ (by omega : (r : Reg) ≠ r_base + 1),
           hreg_other r hr]⟩,
        by simp [st₂, st₁, hrb_k]⟩
      simp only [st₂, st₁, State.writeArr_arrs_self, State.setReg_arrs]
      by_cases hjk : j.1 = k
      · have hj_eq : j = kFin := Fin.ext hjk
        subst hj_eq
        exact List.getElem_set_self (by simp [hlen_k, hk])
      · rw [List.getElem_set_ne (Ne.symm hjk)]
        exact hbuf_k j (by omega)
  rcases hLoop s₂ hInv₀ with
    ⟨s₃, t₃, hex₃, ht₃, _, ⟨hlen₃, hbuf₃⟩, hrn₃, _, _, harr₃, hreg₃⟩
  dsimp only at ht₃
  have hbuf₃_eq : s₃.arrs a_buf = [] ++ List.ofFn (f ∘ v₀.succAbove) ++ [] := by
    simp only [List.nil_append, List.append_nil]
    apply List.ext_getElem
    · simp [hlen₃]
    · intro i hi₁ hi₂
      rw [List.getElem_ofFn]
      exact hbuf₃ ⟨i, by omega⟩ (by omega)
  -- 4. readSliceProg a_buf (.const 0) a_arr (.reg r_n_new) (r_base + 2)
  have hf_succ_w : ∀ x ∈ List.ofFn (f ∘ v₀.succAbove), x < 2 ^ w := by
    intro x hx
    rw [List.mem_ofFn] at hx
    rcases hx with ⟨u, rfl⟩
    exact hf_w (v₀.succAbove u)
  have hoff_len_w : 0 + (List.ofFn (f ∘ v₀.succAbove)).length < 2 ^ w := by
    simp; omega
  have hrn₃' : s₃.regs r_n_new = (List.ofFn (f ∘ v₀.succAbove)).length := by
    simp [hrn₃]
  rcases readSliceProg_exec a_buf a_arr (.const 0) r_n_new (r_base + 2)
      hne_ab.symm (by omega) [] (List.ofFn (f ∘ v₀.succAbove)) []
      rfl rfl hf_succ_w hw hoff_len_w
      (by simp [Expr.eval, checkWord, h0_w])
      hbuf₃_eq hrn₃' with
    ⟨s₄, t₄, hex₄, ht₄, hdst₄, harr₄, hreg₄⟩
  simp only [List.length_ofFn, Expr.cost] at ht₄
  refine ⟨s₄, _, .seq hex₁ (.seq hex₂ (.seq hex₃ hex₄)), by omega, hdst₄,
    fun a ha_arr ha_buf => by
      rw [harr₄ a ha_arr]
      exact harr₃ a ha_buf,
    fun r hr => by
      rw [hreg₄ r (by omega)]
      exact hreg₃ r hr⟩

end GraphMinor.Compute
