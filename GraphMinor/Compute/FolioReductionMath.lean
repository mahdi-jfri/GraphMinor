module

public import GraphMinor.Compute.DPToDCS

/-!
# Graph Minors XIII: Mathematical Reduction of Disjoint Connected Subgraphs to the `0`-Folio

This file formalizes the mathematical steps of the reduction of *Disjoint Connected Subgraphs* to
*Folio* in Robertson and Seymour, *Graph Minors. XIII. The Disjoint Paths Problem*, J. Combin.
Theory Ser. B **63** (1995), 65–110 (Section 2, page 69):

> For example, let $G$ be the digraph with four vertices $u, v_1, v_2, v_3$ and three edges
> $uv_1, uv_2, uv_3$; we shall examine the $0$-folio of $(G, v_1, v_2, v_3)$. For $i = 1, 2, 3$
> let $N_i$ be the digraph with vertex set $\{1, \dots, i\}$ and no edges. Then the $0$-folio of
> $(G, v_1, v_2, v_3)$ contains $(N_1, 1, 1, 1)$, $(N_2, 1, 1, 2)$, $(N_2, 1, 2, 1)$,
> $(N_2, 2, 1, 1)$, $(N_3, 1, 2, 3)$, and all rooted digraphs isomorphic to one of these.
> ...
> Let us see how Folio can be used to solve the two problems of the previous section. For Disjoint
> Connected Subgraphs, with input $G = (V, E)$ and $Z_1, \dots, Z_t \subseteq V$, we may assume
> that $Z_1, \dots, Z_t$ are mutually disjoint; we direct the edges of $G$ arbitrarily; we compute
> the $0$-folio of $G$ relative to $Z_1 \cup \dots \cup Z_t$, and from this we read off whether the
> desired connected subgraphs exist. (Compare the example above.)

## Main results

1. **Disjointness reduction** (`pairwiseDisjointZ_of_hasDisjointConnectedSubgraphs`,
   `not_hasDisjointConnectedSubgraphs_of_not_pairwiseDisjointZ`):
   If `Z_1, ..., Z_t` are not pairwise disjoint, then no mutually vertex-disjoint subgraphs
   `G_1, ..., G_t` with `Z_i ⊆ V(G_i)` can exist.
2. **Connected subgraph bridge** (`DigraphSubgraph.toSimpleSubgraph_connected`,
   `isNonNullConnected_inducedDigraphSubgraph`):
   Equivalence between connected subgraphs of `G.toSimpleGraph` (`SimpleGraph.Subgraph.Connected`)
   and non-null connected digraph subgraphs of `G.toComputeDigraph`
   (`DigraphSubgraph.IsNonNullConnected`).
3. **Target edgeless rooted digraph `(N_t, u_1, ..., u_q)`** (`edgelessRootedDigraph`,
   `hasDetailLe_zero_edgelessRootedDigraph`,
   `hasDisjointConnectedSubgraphs_iff_hasRootedDigraphModel`):
   When `Z_1, ..., Z_t` are non-null and pairwise disjoint with union `Z = Z_1 ∪ ⋯ ∪ Z_t` of
   cardinality `q = |Z|`, `HasDisjointConnectedSubgraphs x` holds if and only if the target
   edgeless rooted digraph `(N_t, dcsRootMap x hdisj)` has detail `≤ 0` and has a model in
   `rootedDigraphOfZ x.G Z`.
4. **Reading off membership in the `0`-folio via root kernels**
   (`isRootedDigraphIso_edgeless_iff`, `isIsoRootedDigraphCode_edgeless_iff`):
   For any surjective `part : Fin q → Fin t` and any code `c` in a `0`-folio (`IsDetailLeCode q 0 c`),
   `c` has length `2 + q` and is isomorphic to `encRootedDigraph (edgelessRootedDigraph t q part)`
   if and only if `c` induces the same root-equality kernel on `Fin q`:
   `∀ j₁ j₂ : Fin q, (part j₁).1 = (part j₂).1 ↔ c[2 + j₁.1]?.getD 0 = c[2 + j₂.1]?.getD 0`.
-/

@[expose] public section

namespace GraphMinor.Compute

open SimpleGraph
open scoped BigOperators

/-! ### Section 1: GM XIII, page 69: "we may assume that $Z_1, \dots, Z_t$ are mutually disjoint" -/

/-- Pairwise disjointness of the terminal subsets `Z_1, ..., Z_t` of `x : DCSInput k`. -/
def PairwiseDisjointZ {k : ℕ} (x : DCSInput k) : Prop :=
  ∀ i j : Fin x.t, i ≠ j → Disjoint (x.Z i) (x.Z j)

instance instDecidablePairwiseDisjointZ {k : ℕ} (x : DCSInput k) :
    Decidable (PairwiseDisjointZ x) := by
  unfold PairwiseDisjointZ
  infer_instance

/-- If `x : DCSInput k` has mutually vertex-disjoint subgraphs `G_1, ..., G_t` with
`Z_i ⊆ V(G_i)`, then `Z_1, ..., Z_t` must be mutually disjoint. -/
theorem pairwiseDisjointZ_of_hasDisjointConnectedSubgraphs {k : ℕ} {x : DCSInput k}
    (h : HasDisjointConnectedSubgraphs x) :
    PairwiseDisjointZ x := by
  rcases h with ⟨G_sub, _, hdisj, hZ⟩
  intro i j hij
  rw [Finset.disjoint_left]
  intro v hvi hvj
  exact Set.disjoint_left.mp (hdisj i j hij) (hZ i hvi) (hZ j hvj)

/-- **Step 1 of the DCS-to-Folio reduction** (GM XIII, page 69:
"we may assume that $Z_1, \dots, Z_t$ are mutually disjoint"):
if `Z_1, ..., Z_t` are not mutually disjoint, then `HasDisjointConnectedSubgraphs x` is false. -/
theorem not_hasDisjointConnectedSubgraphs_of_not_pairwiseDisjointZ {k : ℕ} {x : DCSInput k}
    (hnot : ¬ PairwiseDisjointZ x) :
    ¬ HasDisjointConnectedSubgraphs x :=
  fun h => hnot (pairwiseDisjointZ_of_hasDisjointConnectedSubgraphs h)

/-! ### Section 2: Bridge between `SimpleGraph.Subgraph.Connected` and `DigraphSubgraph.IsNonNullConnected` -/

/-- Convert a `DigraphSubgraph G.toComputeDigraph` into a `Subgraph` of `G.toSimpleGraph` on the
same vertex set `S.verts`. -/
@[reducible]
def DigraphSubgraph.toSimpleSubgraph {n : ℕ} {G : MultiDigraph n}
    (S : DigraphSubgraph G.toComputeDigraph) : G.toSimpleGraph.Subgraph where
  verts := (S.verts : Set (Fin n))
  Adj u v := S.underlyingSimpleGraph.Adj u v
  adj_sub := by
    intro u v ⟨hne, e, _, h⟩
    rw [G.toSimpleGraph_adj_iff_toComputeDigraph]
    exact ⟨hne, e, h⟩
  edge_vert := by
    intro u v ⟨_, e, he, h⟩
    rcases h with ⟨rfl, _⟩ | ⟨_, rfl⟩
    · exact S.head_mem he
    · exact S.tail_mem he
  symm := S.underlyingSimpleGraph.symm

@[simp]
theorem DigraphSubgraph.verts_toSimpleSubgraph {n : ℕ} {G : MultiDigraph n}
    (S : DigraphSubgraph G.toComputeDigraph) :
    S.toSimpleSubgraph.verts = (S.verts : Set (Fin n)) := rfl

theorem DigraphSubgraph.reachable_coe_toSimpleSubgraph_of_walk {n : ℕ} {G : MultiDigraph n}
    (S : DigraphSubgraph G.toComputeDigraph) {u v : Fin n}
    (w : S.underlyingSimpleGraph.Walk u v) (hu : u ∈ S.verts) (hv : v ∈ S.verts) :
    S.toSimpleSubgraph.coe.Reachable ⟨u, hu⟩ ⟨v, hv⟩ := by
  induction w with
  | nil => exact Reachable.refl _
  | @cons a b c hadj rest ih =>
    have hb : b ∈ S.verts := S.toSimpleSubgraph.edge_vert hadj.symm
    have hadj_coe : S.toSimpleSubgraph.coe.Adj ⟨a, hu⟩ ⟨b, hb⟩ := hadj
    exact hadj_coe.reachable.trans (ih hb hv)

/-- Every `DigraphSubgraph G.toComputeDigraph` satisfying `IsNonNullConnected` gives a connected
subgraph `S.toSimpleSubgraph` of `G.toSimpleGraph`. -/
theorem DigraphSubgraph.toSimpleSubgraph_connected {n : ℕ} {G : MultiDigraph n}
    {S : DigraphSubgraph G.toComputeDigraph} (h : S.IsNonNullConnected) :
    S.toSimpleSubgraph.Connected := by
  rw [Subgraph.connected_iff]
  refine ⟨⟨fun ⟨u, hu⟩ ⟨v, hv⟩ => ?_⟩, ?_⟩
  · rcases h.2 u hu v hv with ⟨w⟩
    exact S.reachable_coe_toSimpleSubgraph_of_walk w hu hv
  · exact Finset.coe_nonempty.mpr h.1

/-- The `DigraphSubgraph G.toComputeDigraph` induced on a vertex subset `V_sub : Finset (Fin n)`,
containing all directed edges of `G.toComputeDigraph` whose head and tail both lie in `V_sub`. -/
@[reducible]
def inducedDigraphSubgraph {n : ℕ} (G : MultiDigraph n) (V_sub : Finset (Fin n)) :
    DigraphSubgraph G.toComputeDigraph where
  verts := V_sub
  edges := Finset.univ.filter (fun e =>
    G.toComputeDigraph.head e ∈ V_sub ∧ G.toComputeDigraph.tail e ∈ V_sub)
  head_mem := fun _ he => (Finset.mem_filter.mp he).2.1
  tail_mem := fun _ he => (Finset.mem_filter.mp he).2.2

@[simp]
theorem verts_inducedDigraphSubgraph {n : ℕ} (G : MultiDigraph n) (V_sub : Finset (Fin n)) :
    (inducedDigraphSubgraph G V_sub).verts = V_sub := rfl

theorem adj_underlyingSimpleGraph_inducedDigraphSubgraph {n : ℕ} (G : MultiDigraph n)
    (V_sub : Finset (Fin n)) {u v : Fin n}
    (hu : u ∈ V_sub) (hv : v ∈ V_sub) (hadj : G.toSimpleGraph.Adj u v) :
    (inducedDigraphSubgraph G V_sub).underlyingSimpleGraph.Adj u v := by
  rw [G.toSimpleGraph_adj_iff_toComputeDigraph] at hadj
  rcases hadj with ⟨hne, e, h⟩
  refine ⟨hne, e, Finset.mem_filter.mpr ⟨Finset.mem_univ e, ?_⟩, h⟩
  rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact ⟨hu, hv⟩
  · exact ⟨hv, hu⟩

theorem reachable_inducedDigraphSubgraph_of_subgraph_walk {n : ℕ} {G : MultiDigraph n}
    (H : G.toSimpleGraph.Subgraph) (V_sub : Finset (Fin n))
    (hV : ∀ u : Fin n, u ∈ V_sub ↔ u ∈ H.verts)
    {a b : H.verts} (w : H.coe.Walk a b) :
    (inducedDigraphSubgraph G V_sub).underlyingSimpleGraph.Reachable a.1 b.1 := by
  induction w with
  | nil => exact Reachable.refl _
  | @cons x y z hadj rest ih =>
    have hx : x.1 ∈ V_sub := (hV x.1).mpr x.2
    have hy : y.1 ∈ V_sub := (hV y.1).mpr y.2
    have hadj_G : G.toSimpleGraph.Adj x.1 y.1 := H.adj_sub hadj
    have hadj_ind := adj_underlyingSimpleGraph_inducedDigraphSubgraph G V_sub hx hy hadj_G
    exact hadj_ind.reachable.trans ih

/-- Every connected subgraph `H : G.toSimpleGraph.Subgraph` induces a `DigraphSubgraph` of
`G.toComputeDigraph` on `V_sub = Finset.univ.filter (· ∈ H.verts)` satisfying
`IsNonNullConnected`. -/
theorem isNonNullConnected_inducedDigraphSubgraph_of_connected {n : ℕ} {G : MultiDigraph n}
    (H : G.toSimpleGraph.Subgraph) [DecidablePred (· ∈ H.verts)]
    (hconn : H.Connected) :
    (inducedDigraphSubgraph G (Finset.univ.filter (· ∈ H.verts))).IsNonNullConnected := by
  let V_sub := Finset.univ.filter (· ∈ H.verts)
  have hV : ∀ u : Fin n, u ∈ V_sub ↔ u ∈ H.verts := by
    intro u; simp [V_sub]
  refine ⟨?_, ?_⟩
  · rcases hconn.nonempty with ⟨u, hu⟩
    exact ⟨u, (hV u).mpr hu⟩
  · intro u hu v hv
    have hu' : u ∈ H.verts := (hV u).mp hu
    have hv' : v ∈ H.verts := (hV v).mp hv
    rcases hconn.preconnected ⟨u, hu'⟩ ⟨v, hv'⟩ with ⟨w⟩
    exact reachable_inducedDigraphSubgraph_of_subgraph_walk H V_sub hV w

/-! ### Section 3: Target Edgeless Rooted Digraph `(N_t, u_1, ..., u_q)` and `0`-Folio Equivalence -/

/-- Union `Z = Z_1 ∪ ⋯ ∪ Z_t` of all terminal subsets of `x : DCSInput k`. -/
def dcsUnionZ {k : ℕ} (x : DCSInput k) : Finset (Fin x.n) :=
  Finset.univ.biUnion x.Z

@[simp]
theorem mem_dcsUnionZ {k : ℕ} (x : DCSInput k) (v : Fin x.n) :
    v ∈ dcsUnionZ x ↔ ∃ i : Fin x.t, v ∈ x.Z i := by
  simp [dcsUnionZ]

/-- Computable lookup of the index `i < x.t` such that `v ∈ x.Z i` (returning `0` if none exists). -/
def ownerIdx {k : ℕ} (x : DCSInput k) (v : Fin x.n) : ℕ :=
  match (List.finRange x.t).find? (fun i => decide (v ∈ x.Z i)) with
  | some i => i.1
  | none => 0

/-- When `Z_1, ..., Z_t` are pairwise disjoint and `v ∈ x.Z i`, `ownerIdx x v = i.1`. -/
theorem ownerIdx_eq_of_mem {k : ℕ} {x : DCSInput k} (hdisj : PairwiseDisjointZ x)
    {i : Fin x.t} {v : Fin x.n} (hv : v ∈ x.Z i) :
    ownerIdx x v = i.1 := by
  unfold ownerIdx
  cases hfind : (List.finRange x.t).find? (fun j => decide (v ∈ x.Z j)) with
  | none =>
    exfalso
    have hnone := List.find?_eq_none.mp hfind i (List.mem_finRange i)
    simp [hv] at hnone
  | some j =>
    have hj : v ∈ x.Z j :=
      of_decide_eq_true (@List.find?_some _ (fun j => decide (v ∈ x.Z j)) _ _ hfind)
    by_cases hij : j = i
    · subst hij; rfl
    · exfalso
      exact Finset.disjoint_left.mp (hdisj j i hij) hj hv

theorem ownerIdx_lt_of_mem_dcsUnionZ {k : ℕ} {x : DCSInput k} (hdisj : PairwiseDisjointZ x)
    {v : Fin x.n} (hv : v ∈ dcsUnionZ x) :
    ownerIdx x v < x.t := by
  rcases (mem_dcsUnionZ x v).mp hv with ⟨i, hvi⟩
  rw [ownerIdx_eq_of_mem hdisj hvi]
  exact i.2

/-- The root partition map `Fin (dcsUnionZ x).card → Fin x.t` sending the `j`-th vertex of
`Z = Z_1 ∪ ⋯ ∪ Z_t` (in increasing order) to the unique index `i : Fin x.t` with
`rootsZ (dcsUnionZ x) j ∈ x.Z i`. -/
def dcsRootMap {k : ℕ} (x : DCSInput k) (hdisj : PairwiseDisjointZ x)
    (j : Fin (dcsUnionZ x).card) : Fin x.t :=
  ⟨ownerIdx x (rootsZ (dcsUnionZ x) j),
    ownerIdx_lt_of_mem_dcsUnionZ hdisj (rootsZ_mem (dcsUnionZ x) j)⟩

theorem dcsRootMap_eq_iff {k : ℕ} {x : DCSInput k} (hdisj : PairwiseDisjointZ x)
    (j : Fin (dcsUnionZ x).card) (i : Fin x.t) :
    dcsRootMap x hdisj j = i ↔ rootsZ (dcsUnionZ x) j ∈ x.Z i := by
  constructor
  · intro heq
    rcases (mem_dcsUnionZ x (rootsZ (dcsUnionZ x) j)).mp (rootsZ_mem (dcsUnionZ x) j) with
      ⟨i', hi'⟩
    have hval : (dcsRootMap x hdisj j).1 = i'.1 := ownerIdx_eq_of_mem hdisj hi'
    have hi_eq : i = i' := Fin.ext (by rw [← heq, hval])
    subst hi_eq
    exact hi'
  · intro hmem
    ext
    exact ownerIdx_eq_of_mem hdisj hmem

theorem surjective_dcsRootMap {k : ℕ} (x : DCSInput k) (hdisj : PairwiseDisjointZ x) :
    Function.Surjective (dcsRootMap x hdisj) := by
  intro i
  rcases x.nonempty_Z i with ⟨v, hvi⟩
  have hvU : v ∈ dcsUnionZ x := (mem_dcsUnionZ x v).mpr ⟨i, hvi⟩
  rcases exists_rootsZ_eq (dcsUnionZ x) hvU with ⟨j, rfl⟩
  exact ⟨j, (dcsRootMap_eq_iff hdisj j i).mpr hvi⟩

/-- The `q`-rooted edgeless digraph `(N_t, part 0, ..., part (q - 1))` on `t` vertices with no
edges (GM XIII, Section 2, page 69: "For $i = 1, 2, 3$ let $N_i$ be the digraph with
vertex set $\{1, \dots, i\}$ and no edges"). -/
@[reducible]
def edgelessRootedDigraph (t q : ℕ) (part : Fin q → Fin t) : ComputeRootedDigraph q where
  digraph := {
    numVerts := t
    numEdges := 0
    head := Fin.elim0
    tail := Fin.elim0
  }
  roots := part

@[simp]
theorem rootFinset_edgelessRootedDigraph_of_surjective {t q : ℕ} {part : Fin q → Fin t}
    (hsurj : Function.Surjective part) :
    (edgelessRootedDigraph t q part).rootFinset = Finset.univ := by
  ext i
  simp only [ComputeRootedDigraph.rootFinset, edgelessRootedDigraph]
  simp only [Finset.mem_image, Finset.mem_univ, true_and, iff_true]
  exact hsurj i

/-- Any `edgelessRootedDigraph t q part` with surjective root map `part : Fin q → Fin t` has
detail `≤ 0` (`|E(H)| = 0 ≤ 0` and `|V(H) \ rootFinset| = 0 ≤ 0`). -/
theorem hasDetailLe_zero_edgelessRootedDigraph {t q : ℕ} {part : Fin q → Fin t}
    (hsurj : Function.Surjective part) :
    (edgelessRootedDigraph t q part).HasDetailLe 0 := by
  refine ⟨le_rfl, ?_⟩
  rw [rootFinset_edgelessRootedDigraph_of_surjective hsurj, Finset.sdiff_self, Finset.card_empty]

/-- **Step 2 of the DCS-to-Folio reduction** (GM XIII, page 69:
"we direct the edges of $G$ arbitrarily; we compute the $0$-folio of $G$ relative to
$Z_1 \cup \dots \cup Z_t$, and from this we read off whether the desired connected subgraphs
exist"):
When `Z_1, ..., Z_t` are pairwise disjoint, `HasDisjointConnectedSubgraphs x` holds if and only if
the target edgeless rooted digraph `edgelessRootedDigraph x.t (dcsUnionZ x).card (dcsRootMap x hdisj)`
has a rooted digraph model in `rootedDigraphOfZ x.G (dcsUnionZ x)`. -/
theorem hasDisjointConnectedSubgraphs_iff_hasRootedDigraphModel {k : ℕ} {x : DCSInput k}
    (hdisj : PairwiseDisjointZ x) :
    HasDisjointConnectedSubgraphs x ↔
      HasRootedDigraphModel
        (edgelessRootedDigraph x.t (dcsUnionZ x).card (dcsRootMap x hdisj))
        (rootedDigraphOfZ x.G (dcsUnionZ x)) := by
  classical
  constructor
  · rintro ⟨G_sub, hconn, hG_disj, hZ_sub⟩
    refine ⟨{
      vertMap := fun i =>
        inducedDigraphSubgraph x.G (Finset.univ.filter (· ∈ (G_sub i).verts))
      edgeMap := Fin.elim0
      connected := fun i =>
        isNonNullConnected_inducedDigraphSubgraph_of_connected (G_sub i) (hconn i)
      vert_disjoint := by
        intro i₁ i₂ hne
        rw [Finset.disjoint_left]
        intro v hv₁ hv₂
        rw [verts_inducedDigraphSubgraph, Finset.mem_filter] at hv₁ hv₂
        exact Set.disjoint_left.mp (hG_disj i₁ i₂ hne) hv₁.2 hv₂.2
      edge_injective := fun e => Fin.elim0 e
      edge_notMem_vert := fun _ e => Fin.elim0 e
      head_mem_vertMap := fun e => Fin.elim0 e
      tail_mem_vertMap := fun e => Fin.elim0 e
      root_mem_vertMap := by
        intro j
        change rootsZ (dcsUnionZ x) j ∈
          Finset.univ.filter (· ∈ (G_sub (dcsRootMap x hdisj j)).verts)
        rw [Finset.mem_filter]
        have hmemZ : rootsZ (dcsUnionZ x) j ∈ x.Z (dcsRootMap x hdisj j) :=
          (dcsRootMap_eq_iff hdisj j (dcsRootMap x hdisj j)).mp rfl
        exact ⟨Finset.mem_univ _, hZ_sub (dcsRootMap x hdisj j) hmemZ⟩
    }⟩
  · rintro ⟨M⟩
    refine ⟨fun i => (M.vertMap i).toSimpleSubgraph,
      fun i => (M.vertMap i).toSimpleSubgraph_connected (M.connected i), ?_, ?_⟩
    · intro i₁ i₂ hne
      rw [Set.disjoint_left]
      intro v hv₁ hv₂
      exact Finset.disjoint_left.mp (M.vert_disjoint i₁ i₂ hne)
        (Finset.mem_coe.mp hv₁) (Finset.mem_coe.mp hv₂)
    · intro i v hv
      have hvU : v ∈ dcsUnionZ x := (mem_dcsUnionZ x v).mpr ⟨i, hv⟩
      rcases exists_rootsZ_eq (dcsUnionZ x) hvU with ⟨j, hj⟩
      have hmap : dcsRootMap x hdisj j = i :=
        (dcsRootMap_eq_iff hdisj j i).mpr (hj ▸ hv)
      have hroot := M.root_mem_vertMap j
      simp only [rootedDigraphOfZ, edgelessRootedDigraph, hj, hmap] at hroot
      exact Finset.mem_coe.mpr hroot

/-! ### Section 4: Kernel Characterization of Rooted Digraph Isomorphism in the `0`-Folio -/

/-- If `H : ComputeRootedDigraph q` has detail `≤ 0`, then `H` has `0` edges and its root map
`H.roots : Fin q → Fin H.digraph.numVerts` is surjective. -/
theorem numEdges_zero_and_surjective_roots_of_hasDetailLe_zero {q : ℕ}
    {H : ComputeRootedDigraph q} (h : H.HasDetailLe 0) :
    H.digraph.numEdges = 0 ∧ Function.Surjective H.roots := by
  have hm : H.digraph.numEdges = 0 := Nat.eq_zero_of_le_zero h.1
  have hsdiff : Finset.univ \ H.rootFinset = ∅ :=
    Finset.card_eq_zero.mp (Nat.eq_zero_of_le_zero h.2)
  refine ⟨hm, fun w => ?_⟩
  have hw_root : w ∈ H.rootFinset := by
    by_contra hnot
    have hmem : w ∈ Finset.univ \ H.rootFinset :=
      Finset.mem_sdiff.mpr ⟨Finset.mem_univ w, hnot⟩
    rw [hsdiff] at hmem
    exact Finset.notMem_empty w hmem
  unfold ComputeRootedDigraph.rootFinset at hw_root
  exact Finset.mem_image.mp hw_root |>.imp fun _ hi => hi.2

/-- Two `q`-rooted digraphs `edgelessRootedDigraph t q part` (with `part` surjective) and `H`
(with `H.HasDetailLe 0`) are isomorphic if and only if they have the same root-equality kernel on
`Fin q`:
`∀ j₁ j₂ : Fin q, (part j₁).1 = (part j₂).1 ↔ (H.roots j₁).1 = (H.roots j₂).1`. -/
theorem isRootedDigraphIso_edgeless_iff {t q : ℕ} {part : Fin q → Fin t}
    (hsurj : Function.Surjective part)
    {H : ComputeRootedDigraph q} (hdet : H.HasDetailLe 0) :
    IsRootedDigraphIso (edgelessRootedDigraph t q part) H ↔
      ∀ j₁ j₂ : Fin q, (part j₁).1 = (part j₂).1 ↔ (H.roots j₁).1 = (H.roots j₂).1 := by
  rcases numEdges_zero_and_surjective_roots_of_hasDetailLe_zero hdet with ⟨hm0, hsurj_H⟩
  constructor
  · rintro ⟨iso⟩ j₁ j₂
    constructor
    · intro h12
      have h' : part j₁ = part j₂ := Fin.ext h12
      have hmap₁ := iso.map_roots j₁
      have hmap₂ := iso.map_roots j₂
      simp only [edgelessRootedDigraph] at hmap₁ hmap₂
      exact Fin.ext_iff.mp (by rw [← hmap₁, ← hmap₂, h'])
    · intro h12
      have h' : H.roots j₁ = H.roots j₂ := Fin.ext h12
      have hmap₁ := iso.map_roots j₁
      have hmap₂ := iso.map_roots j₂
      simp only [edgelessRootedDigraph] at hmap₁ hmap₂
      have heq : iso.vertEquiv (part j₁) = iso.vertEquiv (part j₂) := by
        rw [hmap₁, hmap₂, h']
      exact Fin.ext_iff.mp (iso.vertEquiv.injective heq)
  · intro hker
    have hker_fin : ∀ j₁ j₂ : Fin q, part j₁ = part j₂ ↔ H.roots j₁ = H.roots j₂ := by
      intro j₁ j₂
      simp only [Fin.ext_iff]
      exact hker j₁ j₂
    choose g hg using hsurj
    choose gH hgH using hsurj_H
    let toFun : Fin t → Fin H.digraph.numVerts := fun i => H.roots (g i)
    let invFun : Fin H.digraph.numVerts → Fin t := fun w => part (gH w)
    have hmap : ∀ j : Fin q, toFun (part j) = H.roots j := by
      intro j
      dsimp [toFun]
      exact (hker_fin (g (part j)) j).mp (hg (part j))
    have hleft : Function.LeftInverse invFun toFun := by
      intro i
      dsimp [invFun, toFun]
      have h1 : H.roots (gH (H.roots (g i))) = H.roots (g i) := hgH (H.roots (g i))
      exact ((hker_fin (gH (H.roots (g i))) (g i)).mpr h1).trans (hg i)
    have hright : Function.RightInverse invFun toFun := by
      intro w
      dsimp [invFun]
      rw [hmap (gH w), hgH w]
    refine ⟨{
      vertEquiv := ⟨toFun, invFun, hleft, hright⟩
      edgeEquiv := finCongr hm0.symm
      map_head := fun e => Fin.elim0 e
      map_tail := fun e => Fin.elim0 e
      map_roots := hmap
    }⟩

/-- For any code `c` in a `0`-folio (`IsDetailLeCode q 0 c`) and any surjective
`part : Fin q → Fin t`:
1. `c.length = 2 + q`, and
2. `IsIsoRootedDigraphCode q (encRootedDigraph (edgelessRootedDigraph t q part)) c` holds if and
   only if `∀ j₁ j₂ : Fin q, (part j₁).1 = (part j₂).1 ↔ c[2 + j₁.1]?.getD 0 = c[2 + j₂.1]?.getD 0`. -/
theorem isIsoRootedDigraphCode_edgeless_iff {t q : ℕ} {part : Fin q → Fin t}
    (hsurj : Function.Surjective part)
    {c : List ℕ} (hc : IsDetailLeCode q 0 c) :
    c.length = 2 + q ∧
      (IsIsoRootedDigraphCode q (encRootedDigraph (edgelessRootedDigraph t q part)) c ↔
        ∀ j₁ j₂ : Fin q,
          (part j₁).1 = (part j₂).1 ↔ c[2 + j₁.1]?.getD 0 = c[2 + j₂.1]?.getD 0) := by
  unfold IsDetailLeCode at hc
  cases hdec : decRootedDigraph q c with
  | none => rw [hdec] at hc; exact False.elim hc
  | some H =>
    rw [hdec] at hc
    rcases hc with ⟨rfl, hdet⟩
    rcases numEdges_zero_and_surjective_roots_of_hasDetailLe_zero hdet with ⟨hm0, _⟩
    refine ⟨?_, ?_⟩
    · rw [length_encRootedDigraph, hm0, Nat.mul_zero, Nat.add_zero]
    · rw [isIsoRootedDigraphCode_enc_iff, isRootedDigraphIso_edgeless_iff hsurj hdet]
      refine forall_congr' fun j₁ => forall_congr' fun j₂ => iff_congr Iff.rfl ?_
      rw [encRootedDigraph_getElem_root H j₁, encRootedDigraph_getElem_root H j₂]

/-- **Reading off Disjoint Connected Subgraphs from a `0`-folio representation** (GM XIII, page 69):
Given `x : DCSInput k` with `hdisj : PairwiseDisjointZ x` and any `F : FolioSetRep (dcsUnionZ x).card 0`
satisfying `IsDeltaFolioRep 0 x.G (dcsUnionZ x) F`, `HasDisjointConnectedSubgraphs x` holds if and
only if `F.codes` contains a code `c` with the same root-equality kernel on `Fin (dcsUnionZ x).card`
as `dcsRootMap x hdisj`. -/
theorem hasDisjointConnectedSubgraphs_iff_exists_code_in_zero_folio {k : ℕ} {x : DCSInput k}
    (hdisj : PairwiseDisjointZ x)
    {F : FolioSetRep (dcsUnionZ x).card 0}
    (hF : IsDeltaFolioRep 0 x.G (dcsUnionZ x) F) :
    HasDisjointConnectedSubgraphs x ↔
      ∃ c ∈ F.codes,
        ∀ j₁ j₂ : Fin (dcsUnionZ x).card,
          (dcsRootMap x hdisj j₁).1 = (dcsRootMap x hdisj j₂).1 ↔
            c[2 + j₁.1]?.getD 0 = c[2 + j₂.1]?.getD 0 := by
  have hsurj := surjective_dcsRootMap x hdisj
  have hdet0 := hasDetailLe_zero_edgelessRootedDigraph hsurj
  rw [hasDisjointConnectedSubgraphs_iff_hasRootedDigraphModel hdisj, ← hF _ hdet0]
  unfold FolioSetRep.MemIso
  constructor
  · rintro ⟨c, hc_mem, hiso⟩
    have hc_det := F.all_detail c hc_mem
    exact ⟨c, hc_mem, ((isIsoRootedDigraphCode_edgeless_iff hsurj hc_det).2.mp hiso)⟩
  · rintro ⟨c, hc_mem, hker⟩
    have hc_det := F.all_detail c hc_mem
    exact ⟨c, hc_mem, ((isIsoRootedDigraphCode_edgeless_iff hsurj hc_det).2.mpr hker)⟩

/-! ### Section 5: Invariance of the `0`-Folio under Capping Multiplicities (`G.cap 0`) -/

theorem reachable_inducedDigraphSubgraph_of_digraphSubgraph_walk {n : ℕ}
    {G₁ G₂ : MultiDigraph n} (hG : G₁.toSimpleGraph = G₂.toSimpleGraph)
    (S : DigraphSubgraph G₁.toComputeDigraph)
    {a b : Fin n} (w : S.underlyingSimpleGraph.Walk a b) :
    (inducedDigraphSubgraph G₂ S.verts).underlyingSimpleGraph.Reachable a b := by
  induction w with
  | nil => exact Reachable.refl _
  | @cons x y z hadj rest ih =>
    have hx : x ∈ S.verts := S.toSimpleSubgraph.edge_vert hadj
    have hy : y ∈ S.verts :=
      S.toSimpleSubgraph.edge_vert hadj.symm
    have hadj_G₁ : G₁.toSimpleGraph.Adj x y := S.toSimpleSubgraph.adj_sub hadj
    have hadj_G₂ : G₂.toSimpleGraph.Adj x y := hG ▸ hadj_G₁
    have hadj_ind := adj_underlyingSimpleGraph_inducedDigraphSubgraph G₂ S.verts hx hy hadj_G₂
    exact hadj_ind.reachable.trans ih

theorem isNonNullConnected_inducedDigraphSubgraph_of_eq_toSimpleGraph {n : ℕ}
    {G₁ G₂ : MultiDigraph n} (hG : G₁.toSimpleGraph = G₂.toSimpleGraph)
    {S : DigraphSubgraph G₁.toComputeDigraph} (hS : S.IsNonNullConnected) :
    (inducedDigraphSubgraph G₂ S.verts).IsNonNullConnected := by
  refine ⟨hS.1, fun u hu v hv => ?_⟩
  rcases hS.2 u hu v hv with ⟨w⟩
  exact reachable_inducedDigraphSubgraph_of_digraphSubgraph_walk hG S w

/-- For any `G : MultiDigraph n`, `G.cap 0` and `G` have the exact same `0`-folio relative to any
subset `Z ⊆ V(G)`. -/
theorem isDeltaFolioRep_zero_cap_iff {n : ℕ} (G : MultiDigraph n) (Z : Finset (Fin n))
    (F : FolioSetRep Z.card 0) :
    IsDeltaFolioRep 0 (G.cap 0) Z F ↔ IsDeltaFolioRep 0 G Z F := by
  suffices hmodel : ∀ H : ComputeRootedDigraph Z.card, H.HasDetailLe 0 →
      (HasRootedDigraphModel H (rootedDigraphOfZ (G.cap 0) Z) ↔
        HasRootedDigraphModel H (rootedDigraphOfZ G Z)) by
    unfold IsDeltaFolioRep
    exact forall_congr' fun H => imp_congr_right fun hdet => iff_congr Iff.rfl (hmodel H hdet)
  intro H hdet
  rcases numEdges_zero_and_surjective_roots_of_hasDetailLe_zero hdet with ⟨hm0, _⟩
  constructor
  · rintro ⟨M⟩
    refine ⟨{
      vertMap := fun v => inducedDigraphSubgraph G (M.vertMap v).verts
      edgeMap := fun e => Fin.elim0 (hm0 ▸ e)
      connected := fun v =>
        isNonNullConnected_inducedDigraphSubgraph_of_eq_toSimpleGraph
          (G.toSimpleGraph_cap 0) (M.connected v)
      vert_disjoint := fun u v huv => M.vert_disjoint u v huv
      edge_injective := fun e => Fin.elim0 (hm0 ▸ e)
      edge_notMem_vert := fun _ e => Fin.elim0 (hm0 ▸ e)
      head_mem_vertMap := fun e => Fin.elim0 (hm0 ▸ e)
      tail_mem_vertMap := fun e => Fin.elim0 (hm0 ▸ e)
      root_mem_vertMap := fun j => M.root_mem_vertMap j
    }⟩
  · rintro ⟨M⟩
    refine ⟨{
      vertMap := fun v => inducedDigraphSubgraph (G.cap 0) (M.vertMap v).verts
      edgeMap := fun e => Fin.elim0 (hm0 ▸ e)
      connected := fun v =>
        isNonNullConnected_inducedDigraphSubgraph_of_eq_toSimpleGraph
          (G.toSimpleGraph_cap 0).symm (M.connected v)
      vert_disjoint := fun u v huv => M.vert_disjoint u v huv
      edge_injective := fun e => Fin.elim0 (hm0 ▸ e)
      edge_notMem_vert := fun _ e => Fin.elim0 (hm0 ▸ e)
      head_mem_vertMap := fun e => Fin.elim0 (hm0 ▸ e)
      tail_mem_vertMap := fun e => Fin.elim0 (hm0 ▸ e)
      root_mem_vertMap := fun j => M.root_mem_vertMap j
    }⟩

end GraphMinor.Compute
