module

public import GraphMinor.Compute.DPStatement
public import GraphMinor.Compute.FolioTable
public import GraphMinor.Compute.BitSet
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Subgraph

/-!
# Graph Minors XIII: Disjoint Connected Subgraphs and the Folio Problem

This file formalizes the two intermediate algorithmic problems of Robertson and Seymour,
*Graph Minors. XIII. The Disjoint Paths Problem*, J. Combin. Theory Ser. B **63** (1995), 65–110
(pages 66, 68–69):

1. **Disjoint Connected Subgraphs** (Section 1, page 66):
   > *Disjoint Connected Subgraphs.*
   > Instance: A graph $G$ and non-null subsets $Z_1, \dots, Z_t \subseteq V(G)$ with
   > $\Sigma |Z_i| \le k$.
   > Question: Do there exist connected subgraphs $G_1, \dots, G_t$ of $G$, mutually
   > vertex-disjoint, with $Z_i \subseteq V(G_i)$ ($1 \le i \le t$)?

2. **Folio** (Section 2, pages 68–69):
   > If $\delta \ge 0$ is an integer, we say that $(H, u_1, \dots, u_k)$ has *detail* $\le \delta$
   > if $|E(H)| \le \delta$ and $|V(H) - \{u_1, \dots, u_k\}| \le \delta$. The $\delta$-*folio* of
   > $(G, v_1, \dots, v_k)$ is the set of all minors of $(G, v_1, \dots, v_k)$ with detail
   > $\le \delta$. ... Thus, if $Z \subseteq V(G)$, by the $\delta$-folio of $G$ relative to $Z$ we
   > mean the $\delta$-folio of $(G, v_1, \dots, v_k)$ for any choice of $v_1, \dots, v_k$ with
   > $k = |Z|$ and $Z = \{v_1, \dots, v_k\}$.
   >
   > *Folio.*
   > Instance: A digraph $G$, and a subset $Z \subseteq V(G)$ with $|Z| \le \xi$.
   > Question: What is the $\delta$-folio of $G$ relative to $Z$?

## How this file builds on `FolioTable.lean`

`FolioTable.lean` defines `ComputeDigraph`, `ComputeRootedDigraph q`, `HasDetailLe δ`,
`RootedDigraphIso`, `DigraphSubgraph`, `DigraphModel`, `RootedDigraphModel`,
`HasRootedDigraphModel`, the word-list encoding `encRootedDigraph`, the isomorphism test
`IsIsoRootedDigraphCode`, and the duplicate-free folio representation `FolioSetRep q δ` with its
flat word-list serialization `encFolioSetRep`.

Here we add:
* `MultiDigraph.toComputeDigraph`: converts a Word RAM input multi-digraph `G : MultiDigraph n`
  into a `ComputeDigraph` by expanding each ordered pair `(u, v)` into `G.edgeMult u v` directed
  edges with tail `u` and head `v`.
* `sortedFinsetList` and `rootsZ`: lists any terminal subset `Z ⊆ Fin n` in strictly increasing
  vertex order `v_0 < v_1 < ⋯ < v_{|Z|-1}`, yielding the canonical `|Z|`-rooted digraph
  `rootedDigraphOfZ G Z : ComputeRootedDigraph Z.card`.
* `IsDeltaFolioRep δ G Z F` and `IsValidFolioOutput δ x out`: specifies that the output array
  `outArr` holds `encFolioSetRep F` for a `FolioSetRep x.Z.card δ` containing (up to isomorphism)
  precisely the rooted digraphs of detail `≤ δ` that have a rooted digraph model in
  `rootedDigraphOfZ x.G x.Z`.
* `FolioStatement δ ξ`: states that for fixed `δ, ξ : ℕ`, there is a Word RAM program computing a
  valid `δ`-folio output from `encFolioIn x = x.G.enc ++ bitSetList x.Z` in `O((|V(G)| + 1)³)`
  steps (`ComputesArrRelInTime`), together with its subroutine preservation interface
  (`folioCallerRegBase`, `folioCallerArrBase`, `FolioStatement.subroutine_exec`).
* `DCSInput k`, `encDCSIn`, `HasDisjointConnectedSubgraphs`, and
  `DisjointConnectedSubgraphsStatement`: states the Disjoint Connected Subgraphs problem in the
  same style as `DisjointPathsStatement`, using Mathlib's `SimpleGraph.Subgraph.Connected`.
-/

@[expose] public section

namespace GraphMinor.Compute

open SimpleGraph
open scoped BigOperators

/-! ### Section 1: From `MultiDigraph n` to `ComputeDigraph` -/

/-- The list of all directed edges `(u, v)` of `G : MultiDigraph n` expanded according to their
multiplicity `G.edgeMult u v` (tail `u`, head `v`). -/
def MultiDigraph.directedEdgesList {n : ℕ} (G : MultiDigraph n) : List (Fin n × Fin n) :=
  (List.finRange n).flatMap (fun u =>
    (List.finRange n).flatMap (fun v =>
      List.replicate (G.edgeMult u v) (u, v)))

@[simp]
theorem MultiDigraph.mem_directedEdgesList_iff {n : ℕ} (G : MultiDigraph n)
    (p : Fin n × Fin n) :
    p ∈ G.directedEdgesList ↔ 0 < G.edgeMult p.1 p.2 := by
  rcases p with ⟨u, v⟩
  simp only [MultiDigraph.directedEdgesList, List.mem_flatMap, List.mem_finRange, true_and,
    List.mem_replicate, ne_eq, Prod.mk.injEq]
  constructor
  · rintro ⟨u', v', hne, rfl, rfl⟩
    omega
  · intro hpos
    exact ⟨u, v, by omega, rfl, rfl⟩

theorem sum_map_finRange {n : ℕ} (f : Fin n → ℕ) :
    ((List.finRange n).map f).sum = ∑ i : Fin n, f i :=
  rfl

@[simp]
theorem MultiDigraph.length_directedEdgesList {n : ℕ} (G : MultiDigraph n) :
    G.directedEdgesList.length = G.numEdges := by
  unfold MultiDigraph.directedEdgesList MultiDigraph.numEdges
  rw [List.length_flatMap]
  simp only [List.length_flatMap, List.length_replicate, sum_map_finRange]

/-- Convert a `MultiDigraph n` into a `ComputeDigraph` (`FolioTable.lean`) on `n` vertices with
`G.directedEdgesList.length = G.numEdges` directed edges, where the `e`-th edge has tail
`(G.directedEdgesList[e]).1` and head `(G.directedEdgesList[e]).2`. -/
@[reducible]
def MultiDigraph.toComputeDigraph {n : ℕ} (G : MultiDigraph n) : ComputeDigraph where
  numVerts := n
  numEdges := G.directedEdgesList.length
  head := fun e => (G.directedEdgesList[e.1]'(e.2)).2
  tail := fun e => (G.directedEdgesList[e.1]'(e.2)).1

@[simp]
theorem MultiDigraph.toComputeDigraph_numVerts {n : ℕ} (G : MultiDigraph n) :
    G.toComputeDigraph.numVerts = n := rfl

@[simp]
theorem MultiDigraph.toComputeDigraph_numEdges {n : ℕ} (G : MultiDigraph n) :
    G.toComputeDigraph.numEdges = G.directedEdgesList.length := rfl

/-- There is a directed edge in `G.toComputeDigraph` with tail `u` and head `v` if and only if
`0 < G.edgeMult u v`. -/
theorem MultiDigraph.exists_toComputeDigraph_edge_iff {n : ℕ} (G : MultiDigraph n)
    (u v : Fin n) :
    (∃ e : Fin G.toComputeDigraph.numEdges,
      G.toComputeDigraph.tail e = u ∧ G.toComputeDigraph.head e = v) ↔
    0 < G.edgeMult u v := by
  constructor
  · rintro ⟨e, rfl, rfl⟩
    have hmem : G.directedEdgesList[e.1] ∈ G.directedEdgesList := List.getElem_mem e.2
    exact (G.mem_directedEdgesList_iff _).mp hmem
  · intro hpos
    have hmem : (u, v) ∈ G.directedEdgesList := (G.mem_directedEdgesList_iff (u, v)).mpr hpos
    rcases List.mem_iff_getElem.mp hmem with ⟨i, hi, heq⟩
    refine ⟨⟨i, hi⟩, ?_, ?_⟩
    · exact congrArg Prod.fst heq
    · exact congrArg Prod.snd heq

/-- Two vertices `u, v : Fin n` are adjacent in `G.toSimpleGraph` if and only if `u ≠ v` and
`G.toComputeDigraph` has a directed edge joining `u` and `v` in either direction. -/
theorem MultiDigraph.toSimpleGraph_adj_iff_toComputeDigraph {n : ℕ} (G : MultiDigraph n)
    (u v : Fin n) :
    G.toSimpleGraph.Adj u v ↔
      u ≠ v ∧ ∃ e : Fin G.toComputeDigraph.numEdges,
        (G.toComputeDigraph.head e = u ∧ G.toComputeDigraph.tail e = v) ∨
        (G.toComputeDigraph.head e = v ∧ G.toComputeDigraph.tail e = u) := by
  rw [MultiDigraph.toSimpleGraph_adj]
  refine and_congr_right fun _ => ?_
  rw [← G.exists_toComputeDigraph_edge_iff u v, ← G.exists_toComputeDigraph_edge_iff v u]
  constructor
  · rintro (⟨e, htl, hhd⟩ | ⟨e, htl, hhd⟩)
    · exact ⟨e, Or.inr ⟨hhd, htl⟩⟩
    · exact ⟨e, Or.inl ⟨hhd, htl⟩⟩
  · rintro ⟨e, ⟨hhd, htl⟩ | ⟨hhd, htl⟩⟩
    · exact Or.inr ⟨e, htl, hhd⟩
    · exact Or.inl ⟨e, htl, hhd⟩

/-! ### Section 2: Canonical Root Ordering of `Z ⊆ V(G)` and `rootedDigraphOfZ` -/

/-- The elements of `Z : Finset (Fin n)` listed in strictly increasing order. -/
def sortedFinsetList {n : ℕ} (Z : Finset (Fin n)) : List (Fin n) :=
  (List.finRange n).filter (· ∈ Z)

@[simp]
theorem mem_sortedFinsetList {n : ℕ} (Z : Finset (Fin n)) (u : Fin n) :
    u ∈ sortedFinsetList Z ↔ u ∈ Z := by
  simp [sortedFinsetList]

theorem nodup_sortedFinsetList {n : ℕ} (Z : Finset (Fin n)) :
    (sortedFinsetList Z).Nodup :=
  (List.nodup_finRange n).filter _

theorem pairwise_lt_sortedFinsetList {n : ℕ} (Z : Finset (Fin n)) :
    (sortedFinsetList Z).Pairwise (· < ·) :=
  (List.pairwise_lt_finRange n).filter _

@[simp]
theorem toFinset_sortedFinsetList {n : ℕ} (Z : Finset (Fin n)) :
    (sortedFinsetList Z).toFinset = Z := by
  ext u
  simp [mem_sortedFinsetList]

@[simp]
theorem length_sortedFinsetList {n : ℕ} (Z : Finset (Fin n)) :
    (sortedFinsetList Z).length = Z.card :=
  (List.toFinset_card_of_nodup (nodup_sortedFinsetList Z)).symm.trans
    (congrArg Finset.card (toFinset_sortedFinsetList Z))

/-- The `i`-th element of `Z : Finset (Fin n)` in strictly increasing order (`0 ≤ i < |Z|`). -/
def rootsZ {n : ℕ} (Z : Finset (Fin n)) (i : Fin Z.card) : Fin n :=
  (sortedFinsetList Z)[i.1]'(by rw [length_sortedFinsetList]; exact i.2)

theorem rootsZ_mem {n : ℕ} (Z : Finset (Fin n)) (i : Fin Z.card) :
    rootsZ Z i ∈ Z := by
  rw [← mem_sortedFinsetList]
  exact List.getElem_mem _

theorem strictMono_rootsZ {n : ℕ} (Z : Finset (Fin n)) :
    StrictMono (rootsZ Z) := by
  intro i j hij
  exact List.pairwise_iff_getElem.mp (pairwise_lt_sortedFinsetList Z) i.1 j.1
    (by rw [length_sortedFinsetList]; exact i.2)
    (by rw [length_sortedFinsetList]; exact j.2) hij

theorem injective_rootsZ {n : ℕ} (Z : Finset (Fin n)) :
    Function.Injective (rootsZ Z) :=
  (strictMono_rootsZ Z).injective

theorem exists_rootsZ_eq {n : ℕ} (Z : Finset (Fin n)) {u : Fin n} (hu : u ∈ Z) :
    ∃ i : Fin Z.card, rootsZ Z i = u := by
  have hmem : u ∈ sortedFinsetList Z := (mem_sortedFinsetList Z u).mpr hu
  rcases List.mem_iff_getElem.mp hmem with ⟨idx, hidx, heq⟩
  exact ⟨⟨idx, by rw [← length_sortedFinsetList]; exact hidx⟩, heq⟩

@[simp]
theorem image_rootsZ {n : ℕ} (Z : Finset (Fin n)) :
    Finset.univ.image (rootsZ Z) = Z := by
  ext u
  simp only [Finset.mem_image, Finset.mem_univ, true_and]
  exact ⟨fun ⟨i, hi⟩ => hi ▸ rootsZ_mem Z i, exists_rootsZ_eq Z⟩

/-- The canonical `|Z|`-rooted digraph `(G, v_1, ..., v_{|Z|})` associated with `G : MultiDigraph n`
and `Z ⊆ V(G)`, where `v_1 < ⋯ < v_{|Z|}` are the elements of `Z` in increasing order
(GM XIII, Section 2, page 69: "Thus, if $Z \subseteq V(G)$, by the $\delta$-folio of $G$ relative
to $Z$ we mean the $\delta$-folio of $(G, v_1, \dots, v_k)$ for any choice of $v_1, \dots, v_k$
with $k = |Z|$ and $Z = \{v_1, \dots, v_k\}$."). -/
@[reducible]
def rootedDigraphOfZ {n : ℕ} (G : MultiDigraph n) (Z : Finset (Fin n)) :
    ComputeRootedDigraph Z.card where
  digraph := G.toComputeDigraph
  roots := rootsZ Z

@[simp]
theorem rootFinset_rootedDigraphOfZ {n : ℕ} (G : MultiDigraph n) (Z : Finset (Fin n)) :
    (rootedDigraphOfZ G Z).rootFinset = Z :=
  image_rootsZ Z

/-! ### Section 3: The `δ`-Folio Relative to `Z` and `FolioStatement δ ξ` -/

/-- A `FolioSetRep Z.card δ` represents the `δ`-folio of `G : MultiDigraph n` relative to
`Z ⊆ V(G)` if for every `Z.card`-rooted digraph `H` of detail `≤ δ`, `H` belongs up to
isomorphism to `F` (`F.MemIso H`) if and only if `H` is a minor of (has a model in)
`rootedDigraphOfZ G Z` (`HasRootedDigraphModel H (rootedDigraphOfZ G Z)`). -/
def IsDeltaFolioRep {n : ℕ} (δ : ℕ) (G : MultiDigraph n) (Z : Finset (Fin n))
    (F : FolioSetRep Z.card δ) : Prop :=
  ∀ H : ComputeRootedDigraph Z.card, H.HasDetailLe δ →
    (F.MemIso H ↔ HasRootedDigraphModel H (rootedDigraphOfZ G Z))

/-- An instance of the Folio problem with parameter `ξ` (GM XIII, Section 2, page 69):
"Instance: A digraph $G$, and a subset $Z \subseteq V(G)$ with $|Z| \le \xi$." -/
structure FolioInput (ξ : ℕ) where
  /-- Number of vertices `v = |V(G)|`. -/
  n : ℕ
  /-- The input digraph `G` on `Fin n` (allowing loops and multiple directed edges). -/
  G : MultiDigraph n
  /-- The root subset `Z ⊆ V(G)`. -/
  Z : Finset (Fin n)
  /-- Cardinality bound `|Z| ≤ ξ`. -/
  hZ : Z.card ≤ ξ

/-- Problem size `v = |V(G)|` of a `FolioInput ξ` instance. -/
def folioSize {ξ : ℕ} (x : FolioInput ξ) : ℕ :=
  x.n

/-- Flat word-list encoding of a `FolioInput ξ` instance in `inArr`:
`x.G.enc ++ bitSetList x.Z`, that is,
`[n, m', u_0, v_0, mult_0, ..., u_{m'-1}, v_{m'-1}, mult_{m'-1}, b_0, ..., b_{n-1}]`,
where `b_u = 1` if `u ∈ x.Z` and `b_u = 0` otherwise. This matches `encAlg65In` in
`Algorithm65.lean`. -/
def encFolioIn {ξ : ℕ} (x : FolioInput ξ) : List ℕ :=
  x.G.enc ++ bitSetList x.Z

@[simp]
theorem length_encFolioIn {ξ : ℕ} (x : FolioInput ξ) :
    (encFolioIn x).length = 2 + 3 * x.G.numActivePairs + x.n := by
  simp [encFolioIn, MultiDigraph.length_enc, length_bitSetList]

/-- Output specification for the `δ`-Folio problem on `x : FolioInput ξ`:
the output word list `out` in `outArr` is `encFolioSetRep F` for a `FolioSetRep x.Z.card δ`
that represents the `δ`-folio of `x.G` relative to `x.Z`. -/
def IsValidFolioOutput {ξ : ℕ} (δ : ℕ) (x : FolioInput ξ) (out : List ℕ) : Prop :=
  ∃ F : FolioSetRep x.Z.card δ,
    out = encFolioSetRep F ∧ IsDeltaFolioRep δ x.G x.Z F

/-- **Graph Minors XIII, Folio Problem (`O(v³)`)** (Robertson and Seymour, 1995, Section 2,
page 69, proved in (10.5), page 108):
"For fixed $\delta, \xi \ge 0$ we shall give an algorithm with running time $O(v^3)$ to solve the
following problem.
*Folio.*
Instance: A digraph $G$, and a subset $Z \subseteq V(G)$ with $|Z| \le \xi$.
Question: What is the $\delta$-folio of $G$ relative to $Z$?"

For fixed `δ, ξ : ℕ`, there is a Word RAM program `P` that, given any `x : FolioInput ξ` encoded
in `inArr` as `encFolioIn x`, terminates in `O((|V(G)| + 1)³)` steps at word size
`wordSize c |V(G)|` and writes to `outArr` the encoding `encFolioSetRep F` of the `δ`-folio of
`x.G` relative to `x.Z` (`IsValidFolioOutput δ x`). -/
def FolioStatement (δ ξ : ℕ) : Prop :=
  ∃ P : Cmd,
    ComputesArrRelInTime (folioSize (ξ := ξ)) encFolioIn (IsValidFolioOutput δ) P
      (fun v => (v + 1) ^ 3)

/-! ### Section 4: Subroutine Calling Convention for `FolioStatement` -/

/-- First register index guaranteed not to be modified by a command `P : Cmd`. Any caller that
places its preserved registers at indices `≥ folioCallerRegBase P` has those registers untouched
across an execution of `P`. -/
def folioCallerRegBase (P : Cmd) : Reg :=
  P.writtenRegs.sup id + 1

/-- First array index `≥ 2` guaranteed not to be modified by a command `P : Cmd`. Any caller that
places its preserved scratch arrays at indices `≥ folioCallerArrBase P` has those arrays untouched
across an execution of `P`. -/
def folioCallerArrBase (P : Cmd) : Arr :=
  max 2 (P.writtenArrs.sup id + 1)

theorem not_mem_writtenRegs_of_ge_folioCallerRegBase (P : Cmd) {r : Reg}
    (hr : folioCallerRegBase P ≤ r) :
    r ∉ P.writtenRegs := by
  intro hmem
  have hle : id r ≤ P.writtenRegs.sup id := Finset.le_sup (f := id) hmem
  dsimp [id, folioCallerRegBase, Reg] at hle hr
  omega

theorem not_mem_writtenArrs_of_ge_folioCallerArrBase (P : Cmd) {a : Arr}
    (ha : folioCallerArrBase P ≤ a) :
    a ∉ P.writtenArrs := by
  intro hmem
  have hle : id a ≤ P.writtenArrs.sup id := Finset.le_sup (f := id) hmem
  dsimp [id, folioCallerArrBase, Arr] at hle ha
  omega

theorem two_le_folioCallerArrBase (P : Cmd) :
    2 ≤ folioCallerArrBase P :=
  Nat.le_max_left 2 _

/-- Subroutine execution lemma for `FolioStatement δ ξ`: any program `P` witnessing
`ComputesArrRelInTime (folioSize (ξ := ξ)) encFolioIn (IsValidFolioOutput δ) P (fun v => (v + 1) ^ 3)`
can be called at any word size `w ≥ wordSize c (folioSize x)` from any state `s` with
`s.arrs inArr = encFolioIn x`, producing a valid `δ`-folio encoding in `s'.arrs outArr` in at most
`C * (x.n + 1) ^ 3` steps while preserving all caller registers `r ≥ folioCallerRegBase P` and all
caller arrays `a ≥ folioCallerArrBase P`. -/
theorem ComputesArrRelInTime.folio_subroutine_exec {δ ξ : ℕ} {P : Cmd}
    (hP : ComputesArrRelInTime (folioSize (ξ := ξ)) encFolioIn (IsValidFolioOutput δ) P
      (fun v => (v + 1) ^ 3)) :
    ∃ C c : ℕ, 1 ≤ C ∧ 1 ≤ c ∧
      ∀ (x : FolioInput ξ) (w : ℕ), wordSize c x.n ≤ w →
      ∀ (s : State), s.arrs inArr = encFolioIn x →
        ∃ (s' : State) (t : ℕ),
          Exec w P s s' t ∧
          t ≤ C * (x.n + 1) ^ 3 ∧
          IsValidFolioOutput δ x (s'.arrs outArr) ∧
          (∀ r : Reg, folioCallerRegBase P ≤ r → s'.regs r = s.regs r) ∧
          (∀ a : Arr, folioCallerArrBase P ≤ a → s'.arrs a = s.arrs a) := by
  rcases hP with ⟨C, c, hC, hc, hexec⟩
  refine ⟨C, c, hC, hc, fun x w hw s hs => ?_⟩
  rcases hexec x s hs with ⟨s', t, hex, ht, hout⟩
  have hex_w : Exec w P s s' t := hex.mono_wordSize hw
  refine ⟨s', t, hex_w, ht, hout, ?_, ?_⟩
  · intro r hr
    exact hex_w.regs_eq_of_not_mem_writtenRegs (not_mem_writtenRegs_of_ge_folioCallerRegBase P hr)
  · intro a ha
    exact hex_w.arrs_eq_of_not_mem_writtenArrs (not_mem_writtenArrs_of_ge_folioCallerArrBase P ha)

/-! ### Section 5: The Disjoint Connected Subgraphs Problem (GM XIII, Section 1, page 66) -/

/-- An instance of the Disjoint Connected Subgraphs problem with parameter `k`
(GM XIII, Section 1, page 66):
"Instance: A graph $G$ and non-null subsets $Z_1, \dots, Z_t \subseteq V(G)$ with
$\Sigma |Z_i| \le k$." -/
structure DCSInput (k : ℕ) where
  /-- Number of vertices `v = |V(G)|`. -/
  n : ℕ
  /-- The input graph `G` on `Fin n` (allowing loops and parallel edges). -/
  G : MultiDigraph n
  /-- Number of terminal subsets `t`. -/
  t : ℕ
  /-- The `t` subsets `Z_1, ..., Z_t ⊆ V(G)`. -/
  Z : Fin t → Finset (Fin n)
  /-- Each subset `Z_i` is non-null (`Z_i ≠ ∅`). -/
  nonempty_Z : ∀ i : Fin t, (Z i).Nonempty
  /-- Total size bound `∑ i, |Z_i| ≤ k`. -/
  sum_card_le : ∑ i : Fin t, (Z i).card ≤ k

/-- Problem size `v = |V(G)|` of a `DCSInput k` instance. -/
def dcsSize {k : ℕ} (x : DCSInput k) : ℕ :=
  x.n

/-- Since every `Z_i` is non-null (`1 ≤ |Z_i|`) and `∑ i, |Z_i| ≤ k`, the number of subsets `t`
satisfies `t ≤ k`. -/
theorem DCSInput.t_le {k : ℕ} (x : DCSInput k) : x.t ≤ k := by
  calc x.t = ∑ _i : Fin x.t, 1 := by simp
    _ ≤ ∑ i : Fin x.t, (x.Z i).card :=
      Finset.sum_le_sum fun i _ => Finset.Nonempty.card_pos (x.nonempty_Z i)
    _ ≤ k := x.sum_card_le

/-- Every individual subset `Z_i` in `x : DCSInput k` has cardinality at most `k`. -/
theorem DCSInput.card_Z_le {k : ℕ} (x : DCSInput k) (i : Fin x.t) :
    (x.Z i).card ≤ k := by
  calc (x.Z i).card
    _ ≤ ∑ j : Fin x.t, (x.Z j).card :=
      Finset.single_le_sum (f := fun j : Fin x.t => (x.Z j).card)
        (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
    _ ≤ k := x.sum_card_le

/-- The union `Z_1 ∪ ⋯ ∪ Z_t` of all terminal subsets in `x : DCSInput k` has cardinality at most
`k`. -/
theorem DCSInput.card_biUnion_Z_le {k : ℕ} (x : DCSInput k) :
    (Finset.univ.biUnion x.Z).card ≤ k := by
  calc (Finset.univ.biUnion x.Z).card
    _ ≤ ∑ i : Fin x.t, (x.Z i).card := Finset.card_biUnion_le
    _ ≤ k := x.sum_card_le

/-- The elements of `S : Finset (Fin n)` as a strictly increasing list of natural numbers `< n`. -/
def finsetToList {n : ℕ} (S : Finset (Fin n)) : List ℕ :=
  (sortedFinsetList S).map Fin.val

@[simp]
theorem length_finsetToList {n : ℕ} (S : Finset (Fin n)) :
    (finsetToList S).length = S.card := by
  simp [finsetToList]

@[simp]
theorem getElem_finsetToList {n : ℕ} (S : Finset (Fin n)) (j : Fin S.card) :
    (finsetToList S)[j.1]'(by rw [length_finsetToList]; exact j.2) = (rootsZ S j).1 := by
  simp [finsetToList, rootsZ]

theorem mem_finsetToList_iff {n : ℕ} (S : Finset (Fin n)) (v : ℕ) :
    v ∈ finsetToList S ↔ ∃ u ∈ S, u.1 = v := by
  simp [finsetToList, mem_sortedFinsetList]

theorem nodup_finsetToList {n : ℕ} (S : Finset (Fin n)) :
    (finsetToList S).Nodup :=
  (nodup_sortedFinsetList S).map Fin.val_injective

/-- Flat word-list encoding of `t` subsets `Z : Fin t → Finset (Fin n)`:
`[t, |Z_0|, z_{0,0}, ..., z_{0,|Z_0|-1}, ..., |Z_{t-1}|, z_{t-1,0}, ..., z_{t-1,|Z_{t-1}|-1}]`. -/
def encDCSSets {n t : ℕ} (Z : Fin t → Finset (Fin n)) : List ℕ :=
  [t] ++ (List.finRange t).flatMap (fun i => (Z i).card :: finsetToList (Z i))

@[simp]
theorem length_encDCSSets {n t : ℕ} (Z : Fin t → Finset (Fin n)) :
    (encDCSSets Z).length = 1 + t + ∑ i : Fin t, (Z i).card := by
  unfold encDCSSets
  rw [List.length_append, List.length_singleton, List.length_flatMap]
  simp only [List.length_cons, length_finsetToList, sum_map_finRange]
  rw [Finset.sum_add_distrib]
  simp [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]

/-- Flat word-list encoding of a `DCSInput k` instance in `inArr`:
`x.G.enc ++ encDCSSets x.Z`. -/
def encDCSIn {k : ℕ} (x : DCSInput k) : List ℕ :=
  x.G.enc ++ encDCSSets x.Z

@[simp]
theorem length_encDCSIn {k : ℕ} (x : DCSInput k) :
    (encDCSIn x).length = 2 + 3 * x.G.numActivePairs + 1 + x.t + ∑ i : Fin x.t, (x.Z i).card := by
  simp [encDCSIn, MultiDigraph.length_enc, length_encDCSSets, Nat.add_assoc]

/-- Mathematical predicate for the Disjoint Connected Subgraphs problem (GM XIII, page 66):
"Question: Do there exist connected subgraphs $G_1, \dots, G,$ of $G$, mutually vertex-disjoint,
with $Z_i \subseteq V(G_i)$ ($1 \le i \le t$)?"

Stated using Mathlib's `SimpleGraph.Subgraph` and `SimpleGraph.Subgraph.Connected` on the
underlying simple graph `x.G.toSimpleGraph`. -/
def HasDisjointConnectedSubgraphs {k : ℕ} (x : DCSInput k) : Prop :=
  ∃ G_sub : Fin x.t → x.G.toSimpleGraph.Subgraph,
    (∀ i : Fin x.t, (G_sub i).Connected) ∧
    (∀ i j : Fin x.t, i ≠ j → Disjoint (G_sub i).verts (G_sub j).verts) ∧
    (∀ i : Fin x.t, (x.Z i : Set (Fin x.n)) ⊆ (G_sub i).verts)

/-- Output specification for the Disjoint Connected Subgraphs decision problem:
the output register `outReg` (`regs 0`) holds `1` if `HasDisjointConnectedSubgraphs x` is true and
`0` if `HasDisjointConnectedSubgraphs x` is false. -/
def IsValidDCSOutput {k : ℕ} (x : DCSInput k) (s' : State) : Prop :=
  (HasDisjointConnectedSubgraphs x ∧ s'.regs outReg = 1) ∨
  (¬ HasDisjointConnectedSubgraphs x ∧ s'.regs outReg = 0)

/-- **Graph Minors XIII, Disjoint Connected Subgraphs (`O(v³)`)** (Robertson and Seymour, 1995,
Section 1, page 66, and Section 2, page 69):
"The following problem is more general than DP, but for fixed $k$ there is an $O(v^3)$ algorithm
for its solution as well:
*Disjoint Connected Subgraphs.*
Instance: A graph $G$ and non-null subsets $Z_1, \dots, Z_t \subseteq V(G)$ with
$\Sigma |Z_i| \le k$.
Question: Do there exist connected subgraphs $G_1, \dots, G,$ of $G$, mutually vertex-disjoint,
with $Z_i \subseteq V(G_i)$ ($1 \le i \le t$)?" -/
def DisjointConnectedSubgraphsStatement : Prop :=
  ∀ k : ℕ, ∃ P : Cmd,
    ComputesRelInTime (dcsSize (k := k)) (fun x s => s.arrs inArr = encDCSIn x)
      IsValidDCSOutput P (fun v => (v + 1) ^ 3)

end GraphMinor.Compute
