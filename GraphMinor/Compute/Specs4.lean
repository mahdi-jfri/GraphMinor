module

public import GraphMinor.Compute.MultiDigraph
public import GraphMinor.Compute.Menger
public import GraphMinor.Compute.BranchDecomp
public import GraphMinor.Compute.FolioTable
public import GraphMinor.Compute.Bridge3
public import GraphMinor.Compute.Wall
public import GraphMinor.Compute.Join2
public import Mathlib.Combinatorics.SimpleGraph.Acyclic
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Finite
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring

/-!
# Shared Combinatorial Definitions, Encodings, and Subroutine Specifications for (4.4) and (7.2)

This file provides the combinatorial definitions, flat Word RAM encodings (including the concrete
flat `List ℕ` serialization of a branch-decomposition `(T, τ)`), and the two external subroutine
specifications (`Alg33Spec` for GM XIII Algorithm (3.3), page 72, and `Alg41Spec` for GM XIII
Algorithm (4.1), page 75) used by:
* `GraphMinor.Compute.Algorithm44` (GM XIII Algorithm (4.4), page 77)
* `GraphMinor.Compute.Algorithm72` (GM XIII Algorithm (7.2), page 89)
-/

@[expose] public section

namespace GraphMinor.Compute

open SimpleGraph

/-! ### Section 1: Graph and Digraph Models (GM XIII Section 2, page 68) -/

/-- Simple graph on `Fin n` induced by a list of non-loop edges `es : List (Fin n × Fin n)`. -/
def branchTreeGraph {n : ℕ} (es : List (Fin n × Fin n)) : SimpleGraph (Fin n) where
  Adj x y := x ≠ y ∧ ((x, y) ∈ es ∨ (y, x) ∈ es)
  symm := ⟨fun _ _ h => ⟨h.1.symm, h.2.symm⟩⟩
  loopless := ⟨fun _ h => h.1 rfl⟩

instance instDecidableRelBranchTreeGraphAdj {n : ℕ} (es : List (Fin n × Fin n)) :
    DecidableRel (branchTreeGraph es).Adj :=
  fun x y => by
    change Decidable (x ≠ y ∧ ((x, y) ∈ es ∨ (y, x) ∈ es))
    infer_instance

/-- A vertex set `X ⊆ Fin n` and duplicate-free edge list `es` form a non-null connected subgraph
on `X` (GM XIII Section 2, page 68: "assigns ... to each vertex $v$ of $H$ a non-null connected
subgraph $\phi(v)$ of $G$"). -/
def IsConnectedBranchSet {n : ℕ} (X : Finset (Fin n)) (es : List (Fin n × Fin n)) : Prop :=
  X.Nonempty ∧
  es.Nodup ∧
  (∀ p ∈ es, p.1 ∈ X ∧ p.2 ∈ X ∧ p.1 ≠ p.2 ∧ (p.2, p.1) ∉ es) ∧
  (∀ x ∈ X, ∀ y ∈ X, (branchTreeGraph es).Reachable x y)

/-- A model `φ` of a digraph (or graph) `H` with `p` vertices (`Fin p`) and edge list
`edgesH : List (Fin p × Fin p)` in a multigraph/digraph `G : MultiDigraph n`
(GM XIII Section 2, page 68):
"Let $G, H$ be both graphs or both digraphs. A *model* $\phi$ of $H$ in $G$ assigns to each edge
$e$ of $H$ an edge $\phi(e)$ of $G$, and to each vertex $v$ of $H$ a non-null connected subgraph
$\phi(v)$ of $G$, such that
(i) the graphs $\phi(v)$ ($v \in V(H)$) are mutually vertex-disjoint, the edges $\phi(e)$
($e \in E(H)$) are all distinct, and for $v \in V(H)$ and $e \in E(H)$, $\phi(e) \notin E(\phi(v))$
(ii) for $e \in E(H)$, if $e$ has head $u$ and tail $v$ (or, in the undirected case, has ends
$u, v$) then $\phi(e)$ has a head in $V(\phi(u))$ and a tail in $V(\phi(v))$ (respectively,
$\phi(e)$ has one end in $V(\phi(u))$ and the other in $V(\phi(v))$)." -/
structure MultiDigraphModel {p n : ℕ} (edgesH : List (Fin p × Fin p)) (G : MultiDigraph n) where
  /-- Vertex set `V(φ(u)) ⊆ V(G)` for each `u ∈ V(H)`. -/
  branchSet : Fin p → Finset (Fin n)
  /-- Edges `E(φ(u))` of the connected subgraph `φ(u)` for each `u ∈ V(H)`. -/
  treeEdges : Fin p → List (Fin n × Fin n)
  /-- Endpoint pair `(tail, head)` in `V(G) × V(G)` of the image edge `φ(e_k)` for each edge
  `e_k` of `H`. -/
  edgeMap : Fin edgesH.length → Fin n × Fin n

namespace MultiDigraphModel

/-- Number of branch subgraphs `φ(u)` that use directed edge `(x, y)` in `M.treeEdges u`. -/
def treeEdgeCount {p n : ℕ} {edgesH : List (Fin p × Fin p)} {G : MultiDigraph n}
    (M : MultiDigraphModel edgesH G) (x y : Fin n) : ℕ :=
  ((List.finRange p).filter (fun u => decide ((x, y) ∈ M.treeEdges u))).length

/-- Number of edges `e_k` of `H` mapped to directed pair `(x, y)` by `M.edgeMap`. -/
def modelEdgeCount {p n : ℕ} {edgesH : List (Fin p × Fin p)} {G : MultiDigraph n}
    (M : MultiDigraphModel edgesH G) (x y : Fin n) : ℕ :=
  ((List.finRange edgesH.length).filter (fun k => decide (M.edgeMap k = (x, y)))).length

/-- Reinterpret a `MultiDigraphModel` over another `MultiDigraph n` on the same vertex set `Fin n`. -/
def castGraph {p n : ℕ} {edgesH : List (Fin p × Fin p)} {G₁ G₂ : MultiDigraph n}
    (M : MultiDigraphModel edgesH G₁) : MultiDigraphModel edgesH G₂ where
  branchSet := M.branchSet
  treeEdges := M.treeEdges
  edgeMap := M.edgeMap

@[simp]
theorem treeEdgeCount_castGraph {p n : ℕ} {edgesH : List (Fin p × Fin p)}
    {G₁ G₂ : MultiDigraph n} (M : MultiDigraphModel edgesH G₁) (x y : Fin n) :
    (M.castGraph (G₂ := G₂)).treeEdgeCount x y = M.treeEdgeCount x y := rfl

@[simp]
theorem modelEdgeCount_castGraph {p n : ℕ} {edgesH : List (Fin p × Fin p)}
    {G₁ G₂ : MultiDigraph n} (M : MultiDigraphModel edgesH G₁) (x y : Fin n) :
    (M.castGraph (G₂ := G₂)).modelEdgeCount x y = M.modelEdgeCount x y := rfl

/-- Validity of a `MultiDigraphModel` in `G` (conditions (i) and (ii) of GM XIII Section 2, page 68,
in the undirected graph sense of GM XIII (4.4) and (7.2), pages 77 and 89). -/
def IsValid {p n : ℕ} {edgesH : List (Fin p × Fin p)} {G : MultiDigraph n}
    (M : MultiDigraphModel edgesH G) : Prop :=
  (∀ u : Fin p, IsConnectedBranchSet (M.branchSet u) (M.treeEdges u)) ∧
  (∀ u v : Fin p, u ≠ v → Disjoint (M.branchSet u) (M.branchSet v)) ∧
  (∀ k : Fin edgesH.length,
    (M.edgeMap k).1 ∈ M.branchSet (edgesH[k.1]'k.2).1 ∧
    (M.edgeMap k).2 ∈ M.branchSet (edgesH[k.1]'k.2).2) ∧
  (∀ x : Fin n, M.treeEdgeCount x x + M.modelEdgeCount x x ≤ G.edgeMult x x) ∧
  (∀ x y : Fin n, x ≠ y →
    (M.treeEdgeCount x y + M.treeEdgeCount y x) +
      (M.modelEdgeCount x y + M.modelEdgeCount y x) ≤
    G.edgeMult x y + G.edgeMult y x)

theorem modelEdgeCount_le_length {p n : ℕ} {edgesH : List (Fin p × Fin p)} {G : MultiDigraph n}
    (M : MultiDigraphModel edgesH G) (x y : Fin n) :
    M.modelEdgeCount x y ≤ edgesH.length := by
  unfold modelEdgeCount
  calc ((List.finRange edgesH.length).filter (fun k => decide (M.edgeMap k = (x, y)))).length
    _ ≤ (List.finRange edgesH.length).length := List.length_filter_le _ _
    _ = edgesH.length := List.length_finRange

theorem modelEdgeCount_add_symm_le_length {p n : ℕ} {edgesH : List (Fin p × Fin p)}
    {G : MultiDigraph n} (M : MultiDigraphModel edgesH G) {x y : Fin n} (hne : x ≠ y) :
    M.modelEdgeCount x y + M.modelEdgeCount y x ≤ edgesH.length := by
  let S₁ : Finset (Fin edgesH.length) :=
    Finset.univ.filter (fun k => M.edgeMap k = (x, y))
  let S₂ : Finset (Fin edgesH.length) :=
    Finset.univ.filter (fun k => M.edgeMap k = (y, x))
  have h1 : M.modelEdgeCount x y = S₁.card := by
    unfold modelEdgeCount S₁
    rw [← List.toFinset_card_of_nodup ((List.nodup_finRange edgesH.length).filter _)]
    congr 1; ext k; simp
  have h2 : M.modelEdgeCount y x = S₂.card := by
    unfold modelEdgeCount S₂
    rw [← List.toFinset_card_of_nodup ((List.nodup_finRange edgesH.length).filter _)]
    congr 1; ext k; simp
  have hdisj : Disjoint S₁ S₂ := by
    rw [Finset.disjoint_left]
    intro k hk₁ hk₂
    simp only [S₁, S₂, Finset.mem_filter, Finset.mem_univ, true_and] at hk₁ hk₂
    rw [hk₁] at hk₂
    exact hne (Prod.ext_iff.mp hk₂).1
  rw [h1, h2, ← Finset.card_union_of_disjoint hdisj]
  calc (S₁ ∪ S₂).card
    _ ≤ (Finset.univ : Finset (Fin edgesH.length)).card := Finset.card_le_univ _
    _ = edgesH.length := Finset.card_fin _

theorem treeEdgeCount_self_eq_zero {p n : ℕ} {edgesH : List (Fin p × Fin p)} {G : MultiDigraph n}
    {M : MultiDigraphModel edgesH G}
    (hconn : ∀ u : Fin p, IsConnectedBranchSet (M.branchSet u) (M.treeEdges u)) (x : Fin n) :
    M.treeEdgeCount x x = 0 := by
  unfold treeEdgeCount
  rw [List.length_eq_zero_iff, List.filter_eq_nil_iff]
  intro u _
  simp only [decide_eq_true_eq]
  intro hmem
  exact ((hconn u).2.2.1 (x, x) hmem).2.2.1 rfl

private theorem length_filter_le_one_of_pairwise {α : Type*} {l : List α} (hl : l.Nodup)
    (P : α → Bool) (huniq : ∀ a ∈ l, ∀ b ∈ l, P a = true → P b = true → a = b) :
    (l.filter P).length ≤ 1 := by
  have hsub : (l.filter P).Nodup := hl.filter P
  rcases h : l.filter P with _ | ⟨a, _ | ⟨b, rest⟩⟩
  · simp
  · simp
  · have ha : a ∈ l.filter P := by simp [h]
    have hb : b ∈ l.filter P := by simp [h]
    rw [List.mem_filter] at ha hb
    have hab : a = b := huniq a ha.1 b hb.1 ha.2 hb.2
    subst hab
    rw [h, List.nodup_cons] at hsub
    exact absurd (List.mem_cons_self) hsub.1

theorem treeEdgeCount_le_one {p n : ℕ} {edgesH : List (Fin p × Fin p)} {G : MultiDigraph n}
    {M : MultiDigraphModel edgesH G}
    (hconn : ∀ u : Fin p, IsConnectedBranchSet (M.branchSet u) (M.treeEdges u))
    (hdisj : ∀ u v : Fin p, u ≠ v → Disjoint (M.branchSet u) (M.branchSet v))
    (x y : Fin n) :
    M.treeEdgeCount x y ≤ 1 := by
  unfold treeEdgeCount
  apply length_filter_le_one_of_pairwise (List.nodup_finRange p)
  intro u _ v _ hu hv
  simp only [decide_eq_true_eq] at hu hv
  by_contra huv
  have hxu : x ∈ M.branchSet u := ((hconn u).2.2.1 (x, y) hu).1
  have hxv : x ∈ M.branchSet v := ((hconn v).2.2.1 (x, y) hv).1
  exact Finset.disjoint_left.mp (hdisj u v huv) hxu hxv

theorem treeEdgeCount_add_symm_le_one {p n : ℕ} {edgesH : List (Fin p × Fin p)}
    {G : MultiDigraph n} {M : MultiDigraphModel edgesH G}
    (hconn : ∀ u : Fin p, IsConnectedBranchSet (M.branchSet u) (M.treeEdges u))
    (hdisj : ∀ u v : Fin p, u ≠ v → Disjoint (M.branchSet u) (M.branchSet v))
    (x y : Fin n) :
    M.treeEdgeCount x y + M.treeEdgeCount y x ≤ 1 := by
  let S₁ : Finset (Fin p) := Finset.univ.filter (fun u => (x, y) ∈ M.treeEdges u)
  let S₂ : Finset (Fin p) := Finset.univ.filter (fun u => (y, x) ∈ M.treeEdges u)
  have h1 : M.treeEdgeCount x y = S₁.card := by
    unfold treeEdgeCount S₁
    rw [← List.toFinset_card_of_nodup ((List.nodup_finRange p).filter _)]
    congr 1; ext u; simp
  have h2 : M.treeEdgeCount y x = S₂.card := by
    unfold treeEdgeCount S₂
    rw [← List.toFinset_card_of_nodup ((List.nodup_finRange p).filter _)]
    congr 1; ext u; simp
  have hdisj_S : Disjoint S₁ S₂ := by
    rw [Finset.disjoint_left]
    intro u hu₁ hu₂
    simp only [S₁, S₂, Finset.mem_filter, Finset.mem_univ, true_and] at hu₁ hu₂
    exact ((hconn u).2.2.1 (x, y) hu₁).2.2.2 hu₂
  rw [h1, h2, ← Finset.card_union_of_disjoint hdisj_S]
  rw [Finset.card_le_one_iff]
  intro u v hu hv
  by_contra huv
  have hxu : x ∈ M.branchSet u := by
    rcases Finset.mem_union.mp hu with hu1 | hu2
    · exact ((hconn u).2.2.1 (x, y) (Finset.mem_filter.mp hu1).2).1
    · exact ((hconn u).2.2.1 (y, x) (Finset.mem_filter.mp hu2).2).2.1
  have hxv : x ∈ M.branchSet v := by
    rcases Finset.mem_union.mp hv with hv1 | hv2
    · exact ((hconn v).2.2.1 (x, y) (Finset.mem_filter.mp hv1).2).1
    · exact ((hconn v).2.2.1 (y, x) (Finset.mem_filter.mp hv2).2).2.1
  exact Finset.disjoint_left.mp (hdisj u v huv) hxu hxv

/-- Monotonicity of model validity with respect to subgraph inclusion `G₁ ≤ G₂`. -/
theorem IsValid.mono {p n : ℕ} {edgesH : List (Fin p × Fin p)} {G₁ G₂ : MultiDigraph n}
    {M : MultiDigraphModel edgesH G₁} (hle : G₁ ≤ G₂) (hM : M.IsValid) :
    (M.castGraph (G₂ := G₂)).IsValid := by
  rcases hM with ⟨h1, h2, h3, h4, h5⟩
  refine ⟨h1, h2, h3, fun x => le_trans (h4 x) (hle x x), fun x y hxy => ?_⟩
  exact le_trans (h5 x y hxy) (Nat.add_le_add (hle x y) (hle y x))

/-- **GM XIII (4.4) Step (1) invariance (`IsValid_cap_iff`, page 77)**:
"We choose a maximal subgraph $G_1$ of $G$ with at most $|E(H)|$ loops at every vertex and at most
$|E(H)| + 1$ edges mutually parallel. There is a model of $H$ in $G$ if and only if there is one in
$G_1$." -/
theorem isValid_cap_iff {p n : ℕ} {edgesH : List (Fin p × Fin p)} {G : MultiDigraph n}
    (M : MultiDigraphModel edgesH G) :
    (M.castGraph (G₂ := G.cap edgesH.length)).IsValid ↔ M.IsValid := by
  constructor
  · intro h
    exact IsValid.mono (G₁ := G.cap edgesH.length) (G₂ := G) (G.cap_le edgesH.length) h
  · rintro ⟨hconn, hdisj, hedges, hloop, hmult⟩
    refine ⟨hconn, hdisj, hedges, fun x => ?_, fun x y hxy => ?_⟩
    · rw [MultiDigraph.cap_edgeMult]
      simp only [treeEdgeCount_castGraph, modelEdgeCount_castGraph, ↓reduceIte]
      have htree0 := M.treeEdgeCount_self_eq_zero hconn x
      have hmod := M.modelEdgeCount_le_length x x
      have hm := hloop x
      rw [Nat.le_min]
      omega
    · rw [MultiDigraph.cap_edgeMult, MultiDigraph.cap_edgeMult]
      simp only [treeEdgeCount_castGraph, modelEdgeCount_castGraph, hxy, Ne.symm hxy, ↓reduceIte,
        Nat.min_def]
      have htree1 := M.treeEdgeCount_add_symm_le_one hconn hdisj x y
      have hmod := M.modelEdgeCount_add_symm_le_length hxy
      have hm := hmult x y hxy
      split_ifs <;> omega

/-- Flat `List ℕ` encoding of a `MultiDigraphModel`:
`[p, edgesH.length]` followed by the mapped edge endpoints `(x_k, y_k)` for `k : Fin edgesH.length`
and, for each vertex `u : Fin p`, the indicator bitlist `bitSetList (M.branchSet u)` of length `n`. -/
def enc {p n : ℕ} {edgesH : List (Fin p × Fin p)} {G : MultiDigraph n}
    (M : MultiDigraphModel edgesH G) : List ℕ :=
  [p, edgesH.length] ++
  (List.finRange edgesH.length).flatMap (fun k => [(M.edgeMap k).1.1, (M.edgeMap k).2.1]) ++
  (List.finRange p).flatMap (fun u => bitSetList (M.branchSet u))

theorem length_enc {p n : ℕ} {edgesH : List (Fin p × Fin p)} {G : MultiDigraph n}
    (M : MultiDigraphModel edgesH G) :
    M.enc.length = 2 + 2 * edgesH.length + p * n := by
  unfold enc
  have h1 :
      ((List.finRange edgesH.length).flatMap
        (fun k => [(M.edgeMap k).1.1, (M.edgeMap k).2.1])).length = 2 * edgesH.length := by
    rw [List.length_flatMap]
    simp [List.map_const', List.sum_replicate, List.length_finRange, Nat.mul_comm]
  have h2 :
      ((List.finRange p).flatMap (fun u => bitSetList (M.branchSet u))).length = p * n := by
    rw [List.length_flatMap]
    have hmap : List.map (fun u => (bitSetList (M.branchSet u)).length) (List.finRange p) =
        List.replicate (List.finRange p).length n := by
      rw [List.map_eq_replicate_iff]
      intro u _
      exact length_bitSetList (M.branchSet u)
    rw [hmap, List.length_finRange, List.sum_replicate, smul_eq_mul]
  simp only [List.length_append, List.length_cons, List.length_nil, h1, h2]

theorem all_lt_enc {p n B : ℕ} {edgesH : List (Fin p × Fin p)} {G : MultiDigraph n}
    (M : MultiDigraphModel edgesH G)
    (hp : p < B) (hm : edgesH.length < B) (hn : n < B) (h1 : 1 < B) :
    ∀ x ∈ M.enc, x < B := by
  intro x hx
  unfold enc at hx
  simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false, List.mem_flatMap] at hx
  rcases hx with ((rfl | rfl) | ⟨k, _, rfl | rfl⟩) | ⟨u, _, hbit⟩
  · exact hp
  · exact hm
  · exact lt_trans (M.edgeMap k).1.2 hn
  · exact lt_trans (M.edgeMap k).2.2 hn
  · rcases List.mem_iff_getElem.mp hbit with ⟨i, hi, rfl⟩
    have hle := getElem_bitSetList_le_one (M.branchSet u) i hi
    omega

end MultiDigraphModel

/-- Existence of a valid model of `H` (with `p` vertices and edges `edgesH`) in `G : MultiDigraph n`
(GM XIII Section 2, page 68: "$H$ is isomorphic to a minor of $G$ if and only if there is a model of
$H$ in $G$"). -/
def HasDigraphModel {p n : ℕ} (edgesH : List (Fin p × Fin p)) (G : MultiDigraph n) : Prop :=
  ∃ M : MultiDigraphModel edgesH G, M.IsValid

/-- **GM XIII (4.4) Step (1) theorem (page 77)**:
"There is a model of $H$ in $G$ if and only if there is one in $G_1$." -/
theorem hasDigraphModel_cap_iff {p n : ℕ} (edgesH : List (Fin p × Fin p)) (G : MultiDigraph n) :
    HasDigraphModel edgesH (G.cap edgesH.length) ↔ HasDigraphModel edgesH G := by
  constructor
  · rintro ⟨M, hM⟩
    exact ⟨M.castGraph, hM.mono (G.cap_le edgesH.length)⟩
  · rintro ⟨M, hM⟩
    exact ⟨M.castGraph, (M.isValid_cap_iff).mpr hM⟩

theorem hasDigraphModel_mono {p n : ℕ} {edgesH : List (Fin p × Fin p)}
    {G₁ G₂ : MultiDigraph n} (hle : G₁ ≤ G₂) (h : HasDigraphModel edgesH G₁) :
    HasDigraphModel edgesH G₂ := by
  rcases h with ⟨M, hM⟩
  exact ⟨M.castGraph, hM.mono hle⟩

/-! ### Section 2: Target Digraph Conversion and Model Encodings -/

/-- Convert a target graph `(p, edgesH)` with edge orientation `flips : Fin edgesH.length → Bool`
to a `0`-rooted `ComputeRootedDigraph 0`. When `flips e = false`, edge `e` is oriented from
`(edgesH[e]).1` (tail) to `(edgesH[e]).2` (head); when `flips e = true`, it is oriented from
`(edgesH[e]).2` (tail) to `(edgesH[e]).1` (head). -/
abbrev targetToOrientedComputeRootedDigraph (p : ℕ) (edgesH : List (Fin p × Fin p))
    (flips : Fin edgesH.length → Bool) :
    ComputeRootedDigraph 0 where
  digraph := {
    numVerts := p
    numEdges := edgesH.length
    head := fun e => if flips e then (edgesH[e.1]'e.2).1 else (edgesH[e.1]'e.2).2
    tail := fun e => if flips e then (edgesH[e.1]'e.2).2 else (edgesH[e.1]'e.2).1
  }
  roots := Fin.elim0

theorem targetToOrientedComputeRootedDigraph_hasDetailLe (p : ℕ) (edgesH : List (Fin p × Fin p))
    (flips : Fin edgesH.length → Bool) :
    (targetToOrientedComputeRootedDigraph p edgesH flips).HasDetailLe (edgesH.length + p) := by
  refine ⟨by simp, ?_⟩
  have hle :
      (Finset.univ \ (targetToOrientedComputeRootedDigraph p edgesH flips).rootFinset).card ≤
      (Finset.univ : Finset (Fin p)).card := Finset.card_le_univ _
  rw [Finset.card_fin] at hle
  omega

/-- Convert a target digraph `(p, edgesH)` to a `0`-rooted `ComputeRootedDigraph 0`. -/
abbrev targetToComputeRootedDigraph (p : ℕ) (edgesH : List (Fin p × Fin p)) :
    ComputeRootedDigraph 0 :=
  targetToOrientedComputeRootedDigraph p edgesH (fun _ => false)

theorem targetToComputeRootedDigraph_hasDetailLe (p : ℕ) (edgesH : List (Fin p × Fin p)) :
    (targetToComputeRootedDigraph p edgesH).HasDetailLe (edgesH.length + p) :=
  targetToOrientedComputeRootedDigraph_hasDetailLe p edgesH (fun _ => false)

/-- Convert a target graph `(p, edgesH)` to an undirected `Graph ℕ ℕ` in `GM13`'s sense
(`Digraph.toGraph`). -/
def targetGMGraph (p : ℕ) (edgesH : List (Fin p × Fin p)) :
    Graph ℕ ℕ :=
  (targetToComputeRootedDigraph p edgesH).digraph.toGMDigraph.toGraph

/-! ### Section 3: Subroutine Specifications (`Alg33Spec`, `Alg41Spec`, `Alg41MultiSpec`)

`FolioSetRep.decodedAt`, `encRootedDigraphModel`, `length_encRootedDigraphModel`,
`encFolioModels`, `Alg33Spec`, and `Alg41Spec` (over `G.toComputeRootedDigraph Z`) are imported
from `GraphMinor.Compute.Join2`. Here we also state `Alg41MultiSpec` (over
`G.toMultiComputeRootedDigraph Z`), which `Join441.lean` proves equivalent to `Alg41Spec`. -/

/-- **Specification of GM XIII Algorithm (4.1) (page 75)** over `G.toMultiComputeRootedDigraph Z`:
> **(4.1) Algorithm.**
> *Input:* A digraph $G$, and a subset $Z \subseteq V(G)$ with $|Z| \le \xi$, and a
> branch-decomposition $(T, \tau)$ of $G$ of width $\le \omega$.
> *Output:* The $\delta$-folio of $G$ relative to $Z$, and a modelling of it.
> *Running time:* $O(\varepsilon)$. -/
def Alg41MultiSpec (ξ δ ω_bd : ℕ)
    (a_G a_Z a_bd a_folio a_models a_base r_base : ℕ) (P41 : Cmd) : Prop :=
  ∃ (C₄₁ c_w : ℕ), 0 < C₄₁ ∧ 0 < c_w ∧
    ∀ (n : ℕ) (G : MultiDigraph n) (Z : List (Fin n)) (bdCode : List ℕ) (w : ℕ),
      Z.length ≤ ξ →
      IsValidBranchDecompCode ω_bd G bdCode →
      wordSize c_w (G.numEdges + n + 1) ≤ w →
      ω_bd < 2 ^ w →
      (∀ pair ∈ G.activePairsList, G.edgeMult pair.1 pair.2 < 2 ^ w) →
      ∀ (s : State),
        s.arrs a_G = G.enc →
        s.arrs a_Z = [Z.length] ++ Z.map Fin.val →
        s.arrs a_bd = bdCode →
        ∃ (s' : State) (t : ℕ) (F : FolioSetRep Z.length δ)
          (models : ∀ i : Fin F.codes.length,
            RootedDigraphModel (F.decodedAt i) (G.toMultiComputeRootedDigraph Z)),
          Exec w P41 s s' t ∧
          t ≤ C₄₁ * (G.numEdges + n + 1) ∧
          (∀ H : ComputeRootedDigraph Z.length, H.HasDetailLe δ →
            (F.MemIso H ↔ HasRootedDigraphModel H (G.toMultiComputeRootedDigraph Z))) ∧
          s'.arrs a_folio = encFolioSetRep F ∧
          s'.arrs a_models = encFolioModels F models ∧
          (∀ r < r_base, s'.regs r = s.regs r) ∧
          (∀ a < a_base, a ≠ a_folio → a ≠ a_models → s'.arrs a = s.arrs a)

/-! ### Section 6: Word RAM Array Copy and Word-Size Helpers -/

/-- Copy an entire array `a_src` of known length stored in `r_len` into `a_dst`, using scratch
registers `r_base, r_base + 1, r_base + 2`. -/
def copyFullArrProg (a_src a_dst : Arr) (r_len r_base : Reg) : Cmd :=
  readSliceProg a_src (.const 0) a_dst (.reg r_len) r_base

theorem copyFullArrProg_exec {w len : ℕ} (a_src a_dst : ℕ) (r_len r_base : ℕ)
    (hne_arr : a_src ≠ a_dst) (hr_len : r_len < r_base)
    (xs : List ℕ) (hxs_len : xs.length = len)
    (hxs_w : ∀ x ∈ xs, x < 2 ^ w)
    (hw : 1 < 2 ^ w) (hlen_w : len < 2 ^ w)
    {s : State}
    (hsrc : s.arrs a_src = xs)
    (hrlen_val : s.regs r_len = len) :
    ∃ s' t,
      Exec w (copyFullArrProg a_src a_dst r_len r_base) s s' t ∧
      t ≤ 16 * len + 9 ∧
      s'.arrs a_dst = xs ∧
      (∀ a : ℕ, a ≠ a_dst → s'.arrs a = s.arrs a) ∧
      (∀ r < r_base, s'.regs r = s.regs r) := by
  have h0_w : 0 < 2 ^ w := by omega
  have hsrc' : s.arrs a_src = ([] : List ℕ) ++ xs ++ [] := by simp [hsrc]
  rcases readSliceProg_exec (w := w) (n := len) (off := 0) a_src a_dst (.const 0) r_len r_base
      hne_arr hr_len [] xs [] rfl hxs_len hxs_w hw (by omega)
      (by simp [Expr.eval, checkWord, h0_w]) hsrc' hrlen_val with
    ⟨s', t, hex, ht, hdst, harr, hreg⟩
  exact ⟨s', t, hex, by simpa [Expr.cost] using ht, hdst, harr, hreg⟩

theorem mul_succ_le_pow_add_two (c m : ℕ) : c * (m + 1) ≤ (m + 2) ^ c := by
  induction c with
  | zero => simp
  | succ c ih =>
    have hpos : 1 ≤ (m + 2) ^ c := Nat.one_le_pow c (m + 2) (by omega)
    have hm : m ≤ (m + 2) ^ c * m := Nat.le_mul_of_pos_left m hpos
    rw [Nat.pow_succ]
    nlinarith

theorem mul_lt_two_pow_of_wordSize_le {c m w : ℕ} (hc : 1 ≤ c) (hw : wordSize c m ≤ w) :
    c * m < 2 ^ w := by
  have h0 : c * m ≤ c * (m + 1) := by nlinarith
  have h1 : c * m ≤ (m + 2) ^ c := le_trans h0 (mul_succ_le_pow_add_two c m)
  have h2 : (m + 2) ^ c < 2 ^ wordSize c m := pow_lt_two_pow_wordSize hc m
  have h3 : 2 ^ wordSize c m ≤ 2 ^ w := Nat.pow_le_pow_right (by omega) hw
  omega

end GraphMinor.Compute
