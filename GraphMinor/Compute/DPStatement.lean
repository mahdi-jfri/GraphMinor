module

public import GraphMinor.Compute.MultiDigraph

/-!
# Graph Minors XIII: Statement of the `k`-Disjoint Paths Algorithm (`O(|V(G)|³)`)

This file states the final complexity theorem of Robertson and Seymour,
*Graph Minors. XIII. The Disjoint Paths Problem*, J. Combin. Theory Ser. B **63** (1995), 65–110
(pages 65–69):

> **Disjoint Paths (DP)** (page 65):
> *Instance:* A graph `G`, and `k` pairs `(s₁, t₁), ..., (s_k, t_k)` of vertices of `G`.
> *Question:* Do there exist `k` mutually vertex-disjoint paths of `G`, the `i`th joining `s_i` and
> `t_i` (`1 ≤ i ≤ k`)?

For every fixed `k : ℕ`, there is a Word RAM program that solves the `k`-Disjoint Paths problem in
`O(|V(G)|³)` steps (`DisjointPathsStatement`).

## Input format as a flat list of numbers

An instance `x : DPInput k` consists of a vertex count `n = |V(G)|`, a graph `G : MultiDigraph n`
(allowing loops and parallel edges, as in GM XIII pages 67–68: "Thus each edge has a head and a tail
(the same, for a loop)"), and `k` terminal pairs `pairs : Fin k → Fin n × Fin n`.

In the input array `inArr` (`arrs 0`), `encDPIn x : List ℕ` is the flat list of `2 + 3 * m' + 2 * k`
natural numbers
```text
[n, m', u_0, v_0, mult_0, ..., u_{m'-1}, v_{m'-1}, mult_{m'-1}, s_0, t_0, ..., s_{k-1}, t_{k-1}]
```
where:
* `n = x.n` is the number of vertices `|V(G)|` (with vertices numbered `0, ..., n - 1`);
* `m' = x.G.numActivePairs ≤ n²` is the number of ordered pairs `(u, v) ∈ Fin n × Fin n` with
  positive multiplicity `x.G.edgeMult u v > 0`, listed in lexicographic order as triples
  `u_j, v_j, mult_j` (`x.G.enc`); and
* `s_0, t_0, ..., s_{k-1}, t_{k-1} ∈ {0, ..., n - 1}` are the `k` terminal pairs
  (`encDPPairs x.pairs`).

## Word size

The problem size is `dpSize x = x.n = |V(G)|`, and execution in `ComputesRelInTime` runs at the
logarithmic Word RAM word size `wordSize c x.n = c * (Nat.log 2 (x.n + 2) + 1)` bits (`Basic.lean`).
This matches the standard `Θ(log |V(G)|)` word size of the Word RAM: since `2 ^ (wordSize c x.n) >
(x.n + 2) ^ c`, choosing `c ≥ 1` ensures that all vertex indices `< n`, active-pair counts `≤ n²`,
array lengths `O(n² + k)`, and polynomial loop bounds fit into single machine words (`< 2 ^ w`).
-/

@[expose] public section

namespace GraphMinor.Compute

open SimpleGraph

/-- An instance of the `k`-Disjoint Paths problem (GM XIII, page 65):
a finite graph `G : MultiDigraph n` on `n = |V(G)|` vertices (which may have loops or parallel
edges) together with `k` pairs `(s_i, t_i)` of vertices of `G`. -/
structure DPInput (k : ℕ) where
  /-- Number of vertices `v = |V(G)|`. -/
  n : ℕ
  /-- The input graph `G` on `Fin n` (allowing loops and multiple edges). -/
  G : MultiDigraph n
  /-- The `k` terminal pairs `(s_i, t_i)` of vertices in `Fin n`. -/
  pairs : Fin k → Fin n × Fin n

/-- Problem size `v = |V(G)|` of a `DPInput k` instance. -/
def dpSize {k : ℕ} (x : DPInput k) : ℕ :=
  x.n

/-- Flatten a list of vertex pairs `[(s_0, t_0), ..., (s_{k-1}, t_{k-1})]` into
`[s_0.1, t_0.1, ..., s_{k-1}.1, t_{k-1}.1]`. -/
def flatPairs {n : ℕ} (ps : List (Fin n × Fin n)) : List ℕ :=
  ps.flatMap (fun p => [p.1.1, p.2.1])

@[simp]
theorem length_flatPairs {n : ℕ} (ps : List (Fin n × Fin n)) :
    (flatPairs ps).length = 2 * ps.length := by
  induction ps with
  | nil => rfl
  | cons p ps ih =>
    simp only [flatPairs, List.flatMap_cons, List.length_append, List.length_cons, List.length_nil]
    rw [← flatPairs, ih]
    omega

theorem getElem_flatPairs_even {n : ℕ} (ps : List (Fin n × Fin n)) {i : ℕ}
    (hi : i < ps.length) :
    (flatPairs ps)[2 * i]'(by rw [length_flatPairs]; omega) = (ps[i]).1.1 := by
  induction ps generalizing i with
  | nil => simp at hi
  | cons p ps ih =>
    cases i with
    | zero => rfl
    | succ i' =>
      have hi' : i' < ps.length := by simpa using hi
      change ([p.1.1, p.2.1] ++ flatPairs ps)[2 * (i' + 1)]'(by
        simp [length_flatPairs]; omega) = (ps[i']).1.1
      rw [List.getElem_append_right (by simp)]
      have hidx : 2 * (i' + 1) - [p.1.1, p.2.1].length = 2 * i' := by
        simp only [List.length_cons, List.length_nil]; omega
      simp only [hidx]
      exact ih hi'

theorem getElem_flatPairs_odd {n : ℕ} (ps : List (Fin n × Fin n)) {i : ℕ}
    (hi : i < ps.length) :
    (flatPairs ps)[2 * i + 1]'(by rw [length_flatPairs]; omega) = (ps[i]).2.1 := by
  induction ps generalizing i with
  | nil => simp at hi
  | cons p ps ih =>
    cases i with
    | zero => rfl
    | succ i' =>
      have hi' : i' < ps.length := by simpa using hi
      change ([p.1.1, p.2.1] ++ flatPairs ps)[2 * (i' + 1) + 1]'(by
        simp [length_flatPairs]; omega) = (ps[i']).2.1
      rw [List.getElem_append_right (by simp; omega)]
      have hidx : 2 * (i' + 1) + 1 - [p.1.1, p.2.1].length = 2 * i' + 1 := by
        simp only [List.length_cons, List.length_nil]; omega
      simp only [hidx]
      exact ih hi'

/-- Flat word-list encoding `[s_0, t_0, ..., s_{k-1}, t_{k-1}]` of `k` terminal pairs in `Fin n`. -/
def encDPPairs {k n : ℕ} (pairs : Fin k → Fin n × Fin n) : List ℕ :=
  flatPairs (List.ofFn pairs)

@[simp]
theorem length_encDPPairs {k n : ℕ} (pairs : Fin k → Fin n × Fin n) :
    (encDPPairs pairs).length = 2 * k := by
  simp [encDPPairs]

theorem getElem_encDPPairs_even {k n : ℕ} (pairs : Fin k → Fin n × Fin n)
    (i : Fin k) :
    (encDPPairs pairs)[2 * i.1]'(by rw [length_encDPPairs]; omega) = (pairs i).1.1 := by
  exact (getElem_flatPairs_even (List.ofFn pairs) (by simp [i.2])).trans (by simp)

theorem getElem_encDPPairs_odd {k n : ℕ} (pairs : Fin k → Fin n × Fin n)
    (i : Fin k) :
    (encDPPairs pairs)[2 * i.1 + 1]'(by rw [length_encDPPairs]; omega) = (pairs i).2.1 := by
  exact (getElem_flatPairs_odd (List.ofFn pairs) (by simp [i.2])).trans (by simp)

/-- Flat word-list encoding of a `DPInput k` instance in `inArr`:
`x.G.enc ++ encDPPairs x.pairs`, that is,
`[n, m', u_0, v_0, mult_0, ..., u_{m'-1}, v_{m'-1}, mult_{m'-1}, s_0, t_0, ..., s_{k-1}, t_{k-1}]`. -/
def encDPIn {k : ℕ} (x : DPInput k) : List ℕ :=
  x.G.enc ++ encDPPairs x.pairs

@[simp]
theorem length_encDPIn {k : ℕ} (x : DPInput k) :
    (encDPIn x).length = 2 + 3 * x.G.numActivePairs + 2 * k := by
  simp [encDPIn, MultiDigraph.length_enc]

/-- Mathematical predicate for the `k`-Disjoint Paths problem (GM XIII, page 65):
there exist `k` paths `P_0, ..., P_{k-1}` in the underlying simple graph `x.G.toSimpleGraph` such
that `P_i` joins `s_i = (x.pairs i).1` and `t_i = (x.pairs i).2`, and `P_i` and `P_j` are
vertex-disjoint (`List.Disjoint (P i).support (P j).support`) whenever `i ≠ j`.

When `s_i = t_i`, the one-vertex walk `Walk.nil` is a valid path with support `[s_i]`. When two
distinct pairs share a vertex, no mutually vertex-disjoint paths exist because every walk's support
contains its endpoints. -/
def HasDisjointPaths {k : ℕ} (x : DPInput k) : Prop :=
  ∃ P : ∀ i : Fin k, x.G.toSimpleGraph.Walk (x.pairs i).1 (x.pairs i).2,
    (∀ i : Fin k, (P i).IsPath) ∧
    (∀ i j : Fin k, i ≠ j → List.Disjoint (P i).support (P j).support)

/-- Output specification for the `k`-Disjoint Paths decision problem:
the output register `outReg` (`regs 0`) holds `1` if `HasDisjointPaths x` is true and `0` if
`HasDisjointPaths x` is false. -/
def IsValidDPOutput {k : ℕ} (x : DPInput k) (s' : State) : Prop :=
  (HasDisjointPaths x ∧ s'.regs outReg = 1) ∨ (¬ HasDisjointPaths x ∧ s'.regs outReg = 0)

theorem IsValidDPOutput.outReg_eq_one_iff {k : ℕ} {x : DPInput k} {s' : State}
    (h : IsValidDPOutput x s') :
    s'.regs outReg = 1 ↔ HasDisjointPaths x := by
  rcases h with ⟨hyes, h1⟩ | ⟨hno, h0⟩
  · exact ⟨fun _ => hyes, fun _ => h1⟩
  · refine ⟨fun h1 => ?_, fun hyes => absurd hyes hno⟩
    omega

theorem IsValidDPOutput.outReg_eq_zero_iff {k : ℕ} {x : DPInput k} {s' : State}
    (h : IsValidDPOutput x s') :
    s'.regs outReg = 0 ↔ ¬ HasDisjointPaths x := by
  rcases h with ⟨hyes, h1⟩ | ⟨hno, h0⟩
  · refine ⟨fun h0 => ?_, fun hno => absurd hyes hno⟩
    omega
  · exact ⟨fun _ => hno, fun _ => h0⟩

/-- **Graph Minors XIII, Disjoint Paths (`O(|V(G)|³)`)** (Robertson and Seymour, 1995, pages 65–69):
For every fixed `k : ℕ`, there is a Word RAM program `P` that, given any graph `G` and `k` pairs
`(s₁, t₁), ..., (s_k, t_k)` of vertices of `G` encoded in `inArr` as `encDPIn x`, terminates in
`O((|V(G)| + 1)³)` steps at word size `wordSize c |V(G)|` and outputs `1` in `outReg` if `G` has `k`
mutually vertex-disjoint paths joining `s_i` to `t_i` (`1 ≤ i ≤ k`), and `0` otherwise. -/
def DisjointPathsStatement : Prop :=
  ∀ k : ℕ, ∃ P : Cmd,
    ComputesRelInTime (dpSize (k := k)) (fun x s => s.arrs inArr = encDPIn x)
      IsValidDPOutput P (fun v => (v + 1) ^ 3)

end GraphMinor.Compute
