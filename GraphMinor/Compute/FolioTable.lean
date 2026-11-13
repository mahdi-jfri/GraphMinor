module

public import GraphMinor.Compute.Basic
public import Mathlib.Combinatorics.SimpleGraph.Basic
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
public import Mathlib.Data.Finset.Basic
public import Mathlib.Data.Fintype.Perm
public import Mathlib.Data.Fintype.Pi

/-!
# Rooted Digraph Encodings, Models, and Folio Tables for GM XIII (4.1)

This file formalizes the data structures and representations for Section 2 and Algorithm (4.1) of
Robertson and Seymour, *Graph Minors. XIII. The Disjoint Paths Problem* (pages 68–70, 75–76):

1. Plain definitions of directed graphs (`ComputeDigraph`), rooted digraphs
   (`ComputeRootedDigraph q`), detail `≤ δ` (`HasDetailLe δ`), rooted digraph isomorphism
   (`RootedDigraphIso`, `IsRootedDigraphIso` with a `Decidable` instance), and models of
   (rooted) digraphs (`DigraphModel`, `RootedDigraphModel`, `HasRootedDigraphModel`), quoting
   GM XIII Section 2 word for word.
2. A bounded word-list encoding (`encRootedDigraph`, `decRootedDigraph`) of rooted digraphs
   `(H, v₁, ..., v_q)` with detail `≤ δ`, with round-trip decoding and explicit bounds on list
   length (`≤ 2 + q + 2 * δ`) and word size (`≤ q + δ`).
3. A decidable isomorphism test on word-list encodings (`IsIsoRootedDigraphCode`).
4. A bounded representation (`FolioSetRep q δ` and its flat word-list encoding `encFolioSetRep`)
   of a set of rooted digraphs of detail `≤ δ` up to isomorphism, together with canonical
   construction of the `δ`-folio of any rooted digraph `(G, u₁, ..., u_q)`.
-/

@[expose] public section

namespace GraphMinor.Compute

open SimpleGraph

/-! ### Section 1: Directed Graphs, Rooted Digraphs, Detail, and Isomorphism (GM XIII Section 2) -/

/-- A finite directed graph with vertices `Fin numVerts` and directed edges `Fin numEdges`,
where each edge has a head and a tail (GM XIII, Section 2, page 68:
"Thus each edge has a head and a tail (the same, for a loop). The underlying graph of a digraph is
obtained by forgetting the directions of its edges."). -/
structure ComputeDigraph where
  /-- Number of vertices `|V(G)|`. -/
  numVerts : ℕ
  /-- Number of directed edges `|E(G)|`. -/
  numEdges : ℕ
  /-- Head endpoint of each directed edge. -/
  head : Fin numEdges → Fin numVerts
  /-- Tail endpoint of each directed edge. -/
  tail : Fin numEdges → Fin numVerts

/-- A rooted digraph `(G, v₁, ..., v_q)` with `q` roots (not necessarily distinct), as defined in
GM XIII, Section 2, page 68:
"Thus, let us say that $(G, v_1, \dots, v_k)$ is a *rooted digraph* if $G$ is a digraph and
$v_1, \dots, v_k \in V(G)$ (not necessarily distinct). For $1 \le i \le k$, $v_i$ is the $i$ th
root." -/
structure ComputeRootedDigraph (q : ℕ) where
  /-- Underlying directed graph `G`. -/
  digraph : ComputeDigraph
  /-- The `q` root vertices `v₁, ..., v_q ∈ V(G)`. -/
  roots : Fin q → Fin digraph.numVerts

/-- The set of root vertices `{v₁, ..., v_q} ⊆ V(H)` of a rooted digraph `H`. -/
def ComputeRootedDigraph.rootFinset {q : ℕ} (H : ComputeRootedDigraph q) :
    Finset (Fin H.digraph.numVerts) :=
  Finset.univ.image H.roots

/-- Detail `≤ δ` of a rooted digraph `(H, u₁, ..., u_q)`, as defined in GM XIII, Section 2,
page 68:
"If $\delta \ge 0$ is an integer, we say that $(H, u_1, \dots, u_k)$ has *detail* $\le \delta$ if
$|E(H)| \le \delta$ and $|V(H) - \{u_1, \dots, u_k\}| \le \delta$." -/
def ComputeRootedDigraph.HasDetailLe {q : ℕ} (δ : ℕ) (H : ComputeRootedDigraph q) : Prop :=
  H.digraph.numEdges ≤ δ ∧ (Finset.univ \ H.rootFinset).card ≤ δ

instance instDecidableHasDetailLe {q : ℕ} (δ : ℕ) (H : ComputeRootedDigraph q) :
    Decidable (H.HasDetailLe δ) :=
  inferInstanceAs (Decidable (H.digraph.numEdges ≤ δ ∧ (Finset.univ \ H.rootFinset).card ≤ δ))

/-- Every rooted digraph `(H, u₁, ..., u_q)` with detail `≤ δ` has at most `q + δ` vertices. -/
theorem ComputeRootedDigraph.numVerts_le_of_hasDetailLe {q δ : ℕ} {H : ComputeRootedDigraph q}
    (h : H.HasDetailLe δ) :
    H.digraph.numVerts ≤ q + δ := by
  have hroots : H.rootFinset.card ≤ q := by
    unfold ComputeRootedDigraph.rootFinset
    exact Finset.card_image_le.trans (by simp)
  have hpart : (Finset.univ \ H.rootFinset).card + H.rootFinset.card = H.digraph.numVerts := by
    have h1 := Finset.card_sdiff_add_card_eq_card (Finset.subset_univ H.rootFinset)
    simpa using h1
  have hd := h.2
  omega

/-- An isomorphism between two rooted digraphs `H₁, H₂ : ComputeRootedDigraph q`, as defined in
GM XIII, Section 2, page 68:
"Isomorphism of rooted digraphs is defined in the natural way; thus, isomorphic rooted digraphs
have the same number of roots, and the isomorphism maps the $i$ th root of one to the $i$ th root
of the other, for all $i$." -/
structure RootedDigraphIso {q : ℕ} (H₁ H₂ : ComputeRootedDigraph q) where
  /-- Bijection between vertex sets `V(H₁) ≃ V(H₂)`. -/
  vertEquiv : Fin H₁.digraph.numVerts ≃ Fin H₂.digraph.numVerts
  /-- Bijection between edge sets `E(H₁) ≃ E(H₂)`. -/
  edgeEquiv : Fin H₁.digraph.numEdges ≃ Fin H₂.digraph.numEdges
  /-- Compatibility with edge heads. -/
  map_head : ∀ e : Fin H₁.digraph.numEdges,
    H₂.digraph.head (edgeEquiv e) = vertEquiv (H₁.digraph.head e)
  /-- Compatibility with edge tails. -/
  map_tail : ∀ e : Fin H₁.digraph.numEdges,
    H₂.digraph.tail (edgeEquiv e) = vertEquiv (H₁.digraph.tail e)
  /-- Preservation of the `i`-th root for all `i`. -/
  map_roots : ∀ i : Fin q, vertEquiv (H₁.roots i) = H₂.roots i

/-- Two rooted digraphs `H₁, H₂` are isomorphic (`IsRootedDigraphIso H₁ H₂`) if there exists a
`RootedDigraphIso H₁ H₂`. -/
def IsRootedDigraphIso {q : ℕ} (H₁ H₂ : ComputeRootedDigraph q) : Prop :=
  Nonempty (RootedDigraphIso H₁ H₂)

/-- Reflexivity of `RootedDigraphIso`. -/
def RootedDigraphIso.refl {q : ℕ} (H : ComputeRootedDigraph q) : RootedDigraphIso H H where
  vertEquiv := Equiv.refl _
  edgeEquiv := Equiv.refl _
  map_head _ := rfl
  map_tail _ := rfl
  map_roots _ := rfl

/-- Symmetry of `RootedDigraphIso`. -/
def RootedDigraphIso.symm {q : ℕ} {H₁ H₂ : ComputeRootedDigraph q}
    (iso : RootedDigraphIso H₁ H₂) : RootedDigraphIso H₂ H₁ where
  vertEquiv := iso.vertEquiv.symm
  edgeEquiv := iso.edgeEquiv.symm
  map_head e := by
    apply iso.vertEquiv.injective
    rw [Equiv.apply_symm_apply, ← iso.map_head, Equiv.apply_symm_apply]
  map_tail e := by
    apply iso.vertEquiv.injective
    rw [Equiv.apply_symm_apply, ← iso.map_tail, Equiv.apply_symm_apply]
  map_roots i := by
    apply iso.vertEquiv.injective
    simp [iso.map_roots]

/-- Transitivity of `RootedDigraphIso`. -/
def RootedDigraphIso.trans {q : ℕ} {H₁ H₂ H₃ : ComputeRootedDigraph q}
    (iso₁ : RootedDigraphIso H₁ H₂) (iso₂ : RootedDigraphIso H₂ H₃) :
    RootedDigraphIso H₁ H₃ where
  vertEquiv := iso₁.vertEquiv.trans iso₂.vertEquiv
  edgeEquiv := iso₁.edgeEquiv.trans iso₂.edgeEquiv
  map_head e := by simp [iso₂.map_head, iso₁.map_head]
  map_tail e := by simp [iso₂.map_tail, iso₁.map_tail]
  map_roots i := by simp [iso₁.map_roots, iso₂.map_roots]

theorem isRootedDigraphIso_refl {q : ℕ} (H : ComputeRootedDigraph q) :
    IsRootedDigraphIso H H :=
  ⟨RootedDigraphIso.refl H⟩

theorem isRootedDigraphIso_symm {q : ℕ} {H₁ H₂ : ComputeRootedDigraph q}
    (h : IsRootedDigraphIso H₁ H₂) : IsRootedDigraphIso H₂ H₁ :=
  h.map RootedDigraphIso.symm

theorem isRootedDigraphIso_trans {q : ℕ} {H₁ H₂ H₃ : ComputeRootedDigraph q}
    (h₁ : IsRootedDigraphIso H₁ H₂) (h₂ : IsRootedDigraphIso H₂ H₃) :
    IsRootedDigraphIso H₁ H₃ :=
  Nonempty.map2 RootedDigraphIso.trans h₁ h₂

/-- Decidable test for whether two `ComputeRootedDigraph q` are isomorphic, by checking whether the
vertex and edge counts match and searching the finite type of pairs of bijections
`(Fin v₁ ≃ Fin v₂) × (Fin m₁ ≃ Fin m₂)`. -/
instance instDecidableIsRootedDigraphIso {q : ℕ} (H₁ H₂ : ComputeRootedDigraph q) :
    Decidable (IsRootedDigraphIso H₁ H₂) := by
  unfold IsRootedDigraphIso
  by_cases hv : H₁.digraph.numVerts = H₂.digraph.numVerts
  · by_cases hm : H₁.digraph.numEdges = H₂.digraph.numEdges
    · haveI : Fintype (Fin H₁.digraph.numVerts ≃ Fin H₂.digraph.numVerts) :=
        Fintype.ofEquiv (Fin H₁.digraph.numVerts ≃ Fin H₁.digraph.numVerts)
          (hv ▸ Equiv.refl _)
      haveI : Fintype (Fin H₁.digraph.numEdges ≃ Fin H₂.digraph.numEdges) :=
        Fintype.ofEquiv (Fin H₁.digraph.numEdges ≃ Fin H₁.digraph.numEdges)
          (hm ▸ Equiv.refl _)
      exact decidable_of_iff
        (∃ (fv : Fin H₁.digraph.numVerts ≃ Fin H₂.digraph.numVerts)
           (fe : Fin H₁.digraph.numEdges ≃ Fin H₂.digraph.numEdges),
          (∀ e, H₂.digraph.head (fe e) = fv (H₁.digraph.head e)) ∧
          (∀ e, H₂.digraph.tail (fe e) = fv (H₁.digraph.tail e)) ∧
          (∀ i, fv (H₁.roots i) = H₂.roots i))
        ⟨fun ⟨fv, fe, hh, ht, hr⟩ => ⟨⟨fv, fe, hh, ht, hr⟩⟩,
         fun ⟨⟨fv, fe, hh, ht, hr⟩⟩ => ⟨fv, fe, hh, ht, hr⟩⟩
    · exact isFalse (fun ⟨iso⟩ => hm (Fintype.card_fin H₁.digraph.numEdges ▸
        Fintype.card_fin H₂.digraph.numEdges ▸ Fintype.card_congr iso.edgeEquiv))
  · exact isFalse (fun ⟨iso⟩ => hv (Fintype.card_fin H₁.digraph.numVerts ▸
      Fintype.card_fin H₂.digraph.numVerts ▸ Fintype.card_congr iso.vertEquiv))

/-- Detail `≤ δ` is preserved under rooted digraph isomorphism. -/
theorem HasDetailLe.of_iso {q δ : ℕ} {H₁ H₂ : ComputeRootedDigraph q}
    (iso : RootedDigraphIso H₁ H₂) (h : H₁.HasDetailLe δ) :
    H₂.HasDetailLe δ := by
  have hm : H₁.digraph.numEdges = H₂.digraph.numEdges := by
    have := Fintype.card_congr iso.edgeEquiv
    simpa using this
  have hsub : (Finset.univ \ H₂.rootFinset).card ≤ (Finset.univ \ H₁.rootFinset).card := by
    let f : Fin H₂.digraph.numVerts ↪ Fin H₁.digraph.numVerts := iso.vertEquiv.symm.toEmbedding
    have hmap : (Finset.univ \ H₂.rootFinset).map f ⊆ Finset.univ \ H₁.rootFinset := by
      intro x hx
      simp only [Finset.mem_map, Finset.mem_sdiff, Finset.mem_univ, true_and,
        ComputeRootedDigraph.rootFinset, Finset.mem_image] at hx ⊢
      rcases hx with ⟨y, hy_not_root, rfl⟩
      intro ⟨i, hi⟩
      apply hy_not_root
      refine ⟨i, ?_⟩
      have h1 : iso.vertEquiv (f y) = y := iso.vertEquiv.apply_symm_apply y
      rw [← h1, ← hi, iso.map_roots]
    rw [← Finset.card_map f]
    exact Finset.card_le_card hmap
  exact ⟨hm ▸ h.1, hsub.trans h.2⟩

/-! ### Section 2: Models of Digraphs and Rooted Digraphs (GM XIII Section 2, pages 68–69) -/

/-- A subgraph of a directed graph `G : ComputeDigraph`, specified by a subset of vertices `verts`
and a subset of directed edges `edges` whose heads and tails lie in `verts`. -/
structure DigraphSubgraph (G : ComputeDigraph) where
  /-- Vertex subset `V(S) ⊆ V(G)`. -/
  verts : Finset (Fin G.numVerts)
  /-- Edge subset `E(S) ⊆ E(G)`. -/
  edges : Finset (Fin G.numEdges)
  /-- Every edge in `E(S)` has its head in `V(S)`. -/
  head_mem : ∀ ⦃e : Fin G.numEdges⦄, e ∈ edges → G.head e ∈ verts
  /-- Every edge in `E(S)` has its tail in `V(S)`. -/
  tail_mem : ∀ ⦃e : Fin G.numEdges⦄, e ∈ edges → G.tail e ∈ verts

/-- The underlying undirected simple graph of a `DigraphSubgraph G` on vertex set `Fin G.numVerts`,
obtained by forgetting the directions of the edges in `S.edges` (GM XIII, Section 2, page 68:
"The underlying graph of a digraph is obtained by forgetting the directions of its edges...
In particular, a digraph is *connected* if the underlying graph is connected."). -/
def DigraphSubgraph.underlyingSimpleGraph {G : ComputeDigraph} (S : DigraphSubgraph G) :
    SimpleGraph (Fin G.numVerts) where
  Adj u v := u ≠ v ∧ ∃ e ∈ S.edges, (G.head e = u ∧ G.tail e = v) ∨ (G.head e = v ∧ G.tail e = u)
  symm := ⟨fun _ _ ⟨hne, e, he, h⟩ => ⟨hne.symm, e, he, h.symm⟩⟩
  loopless := ⟨fun _ ⟨hne, _⟩ => hne rfl⟩

/-- A `DigraphSubgraph G` is non-null and connected if `S.verts` is nonempty and every pair of
vertices in `S.verts` is connected by a walk in `S.underlyingSimpleGraph` (all of whose vertices
necessarily lie in `S.verts`). -/
def DigraphSubgraph.IsNonNullConnected {G : ComputeDigraph} (S : DigraphSubgraph G) : Prop :=
  S.verts.Nonempty ∧
  ∀ u ∈ S.verts, ∀ v ∈ S.verts, S.underlyingSimpleGraph.Reachable u v

/-- A model `φ` of a digraph `H` in a digraph `G`, quoting GM XIII, Section 2, page 68 word for word:
"Let $G, H$ be both graphs or both digraphs. A *model* $\phi$ of $H$ in $G$ assigns to each edge $e$
of $H$ an edge $\phi(e)$ of $G$, and to each vertex $v$ of $H$ a non-null connected subgraph $\phi(v)$
of $G$, such that
(i) the graphs $\phi(v)$ ($v \in V(H)$) are mutually vertex-disjoint, the edges $\phi(e)$
($e \in E(H)$) are all distinct, and for $v \in V(H)$ and $e \in E(H)$, $\phi(e) \notin E(\phi(v))$
(ii) for $e \in E(H)$, if $e$ has head $u$ and tail $v$ (or, in the undirected case, has ends $u, v$)
then $\phi(e)$ has a head in $V(\phi(u))$ and a tail in $V(\phi(v))$ (respectively, $\phi(e)$ has one
end in $V(\phi(u))$ and the other in $V(\phi(v))$)." -/
structure DigraphModel (H G : ComputeDigraph) where
  /-- For each vertex `v ∈ V(H)`, a subgraph `φ(v)` of `G`. -/
  vertMap : Fin H.numVerts → DigraphSubgraph G
  /-- For each edge `e ∈ E(H)`, an edge `φ(e)` of `G`. -/
  edgeMap : Fin H.numEdges → Fin G.numEdges
  /-- Each `φ(v)` is a non-null connected subgraph of `G`. -/
  connected : ∀ v : Fin H.numVerts, (vertMap v).IsNonNullConnected
  /-- Condition (i), part 1: the graphs `φ(v)` (`v ∈ V(H)`) are mutually vertex-disjoint. -/
  vert_disjoint : ∀ u v : Fin H.numVerts, u ≠ v → Disjoint (vertMap u).verts (vertMap v).verts
  /-- Condition (i), part 2: the edges `φ(e)` (`e ∈ E(H)`) are all distinct. -/
  edge_injective : Function.Injective edgeMap
  /-- Condition (i), part 3: for `v ∈ V(H)` and `e ∈ E(H)`, `φ(e) ∉ E(φ(v))`. -/
  edge_notMem_vert : ∀ (v : Fin H.numVerts) (e : Fin H.numEdges), edgeMap e ∉ (vertMap v).edges
  /-- Condition (ii), head: for `e ∈ E(H)`, `φ(e)` has its head in `V(φ(head(e)))`. -/
  head_mem_vertMap : ∀ e : Fin H.numEdges, G.head (edgeMap e) ∈ (vertMap (H.head e)).verts
  /-- Condition (ii), tail: for `e ∈ E(H)`, `φ(e)` has its tail in `V(φ(tail(e)))`. -/
  tail_mem_vertMap : ∀ e : Fin H.numEdges, G.tail (edgeMap e) ∈ (vertMap (H.tail e)).verts

/-- A model `φ` of a rooted digraph `(H, u₁, ..., u_q)` in a rooted digraph `(G, v₁, ..., v_q)`,
quoting GM XIII, Section 2, page 68 word for word:
"Let $(G, v_1, \dots, v_k)$, $(H, u_1, \dots, u_k)$ be rooted digraphs. A *model* of the second in
the first is a model $\phi$ of $H$ in $G$ such that $v_i \in V(\phi(u_i))$ ($1 \le i \le k$), and if
there is such a model, we say that $(H, u_1, \dots, u_k)$ is a minor of $(G, v_1, \dots, v_k)$." -/
structure RootedDigraphModel {q : ℕ} (H G : ComputeRootedDigraph q) extends
    DigraphModel H.digraph G.digraph where
  /-- Root preservation: `v_i ∈ V(φ(u_i))` for all `1 ≤ i ≤ q`. -/
  root_mem_vertMap : ∀ i : Fin q, G.roots i ∈ (vertMap (H.roots i)).verts

/-- `(H, u₁, ..., u_q)` is a minor of (has a model in) `(G, v₁, ..., v_q)`. -/
def HasRootedDigraphModel {q : ℕ} (H G : ComputeRootedDigraph q) : Prop :=
  Nonempty (RootedDigraphModel H G)

/-- Transporting a `RootedDigraphModel` along an isomorphism `RootedDigraphIso H₁ H₂` on the left. -/
def RootedDigraphModel.ofIsoLeft {q : ℕ} {H₁ H₂ G : ComputeRootedDigraph q}
    (iso : RootedDigraphIso H₁ H₂) (M : RootedDigraphModel H₂ G) :
    RootedDigraphModel H₁ G where
  vertMap v := M.vertMap (iso.vertEquiv v)
  edgeMap e := M.edgeMap (iso.edgeEquiv e)
  connected v := M.connected (iso.vertEquiv v)
  vert_disjoint u v huv := M.vert_disjoint _ _ (fun h => huv (iso.vertEquiv.injective h))
  edge_injective := M.edge_injective.comp iso.edgeEquiv.injective
  edge_notMem_vert v e := M.edge_notMem_vert (iso.vertEquiv v) (iso.edgeEquiv e)
  head_mem_vertMap e := by
    rw [← iso.map_head e]
    exact M.head_mem_vertMap (iso.edgeEquiv e)
  tail_mem_vertMap e := by
    rw [← iso.map_tail e]
    exact M.tail_mem_vertMap (iso.edgeEquiv e)
  root_mem_vertMap i := by
    rw [iso.map_roots i]
    exact M.root_mem_vertMap i

theorem HasRootedDigraphModel.iff_of_iso {q : ℕ} {H₁ H₂ G : ComputeRootedDigraph q}
    (hiso : IsRootedDigraphIso H₁ H₂) :
    HasRootedDigraphModel H₁ G ↔ HasRootedDigraphModel H₂ G := by
  rcases hiso with ⟨iso⟩
  exact ⟨fun ⟨M⟩ => ⟨M.ofIsoLeft iso.symm⟩, fun ⟨M⟩ => ⟨M.ofIsoLeft iso⟩⟩

/-! ### Section 3: Bounded Word-List Encoding of Rooted Digraphs (`encRootedDigraph`) -/

/-- Flat word-list encoding of a rooted digraph `H : ComputeRootedDigraph q`:
`[numVerts, numEdges, r₁, ..., r_q, head(e₁), tail(e₁), ..., head(e_m), tail(e_m)]`. -/
def encRootedDigraph {q : ℕ} (H : ComputeRootedDigraph q) : List ℕ :=
  [H.digraph.numVerts, H.digraph.numEdges] ++
    List.ofFn (fun i : Fin q => (H.roots i).1) ++
    (List.finRange H.digraph.numEdges).flatMap (fun e =>
      [(H.digraph.head e).1, (H.digraph.tail e).1])

theorem length_flatMap_edges {v m : ℕ} (hd tl : Fin m → Fin v) :
    ((List.finRange m).flatMap (fun e => [(hd e).1, (tl e).1])).length = 2 * m := by
  have : ∀ l : List (Fin m),
      (l.flatMap (fun e => [(hd e).1, (tl e).1])).length = 2 * l.length := by
    intro l
    induction l with
    | nil => simp
    | cons e tl_l ih => simp [ih]; omega
  rw [this, List.length_finRange]

/-- Exact length of `encRootedDigraph H`: `2 + q + 2 * H.digraph.numEdges`. -/
@[simp]
theorem length_encRootedDigraph {q : ℕ} (H : ComputeRootedDigraph q) :
    (encRootedDigraph H).length = 2 + q + 2 * H.digraph.numEdges := by
  unfold encRootedDigraph
  rw [List.length_append, List.length_append, List.length_ofFn, length_flatMap_edges]
  simp

/-- If `H` has detail `≤ δ`, its encoding `encRootedDigraph H` has length at most `2 + q + 2 * δ`. -/
theorem length_encRootedDigraph_le_of_hasDetailLe {q δ : ℕ} {H : ComputeRootedDigraph q}
    (h : H.HasDetailLe δ) :
    (encRootedDigraph H).length ≤ 2 + q + 2 * δ := by
  rw [length_encRootedDigraph]
  have := h.1
  omega

/-- If `H` has detail `≤ δ`, every word in `encRootedDigraph H` is bounded by `q + δ`. -/
theorem mem_encRootedDigraph_le_of_hasDetailLe {q δ : ℕ} {H : ComputeRootedDigraph q}
    (h : H.HasDetailLe δ) {w : ℕ} (hw : w ∈ encRootedDigraph H) :
    w ≤ q + δ := by
  have hv_le : H.digraph.numVerts ≤ q + δ := H.numVerts_le_of_hasDetailLe h
  have hm_le : H.digraph.numEdges ≤ δ := h.1
  unfold encRootedDigraph at hw
  simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false,
    List.mem_ofFn, List.mem_flatMap, List.mem_finRange, true_and] at hw
  rcases hw with ((rfl | rfl) | ⟨i, rfl⟩) | ⟨e, rfl | rfl⟩
  · exact hv_le
  · omega
  · have := (H.roots i).2; omega
  · have := (H.digraph.head e).2; omega
  · have := (H.digraph.tail e).2; omega

/-- Validity predicate for a flat word list `code : List ℕ` encoding a `ComputeRootedDigraph q`. -/
def IsValidRootedDigraphCode (q : ℕ) (code : List ℕ) : Prop :=
  2 ≤ code.length ∧
  code.length = 2 + q + 2 * (code[1]?.getD 0) ∧
  (∀ i : Fin q, (code[2 + i.1]?.getD 0) < (code[0]?.getD 0)) ∧
  (∀ e : Fin (code[1]?.getD 0),
    (code[2 + q + 2 * e.1]?.getD 0) < (code[0]?.getD 0) ∧
    (code[2 + q + 2 * e.1 + 1]?.getD 0) < (code[0]?.getD 0))

instance instDecidableIsValidRootedDigraphCode (q : ℕ) (code : List ℕ) :
    Decidable (IsValidRootedDigraphCode q code) := by
  unfold IsValidRootedDigraphCode
  infer_instance

/-- Pure decoder from a flat word list `code : List ℕ` to `Option (ComputeRootedDigraph q)`. -/
def decRootedDigraph (q : ℕ) (code : List ℕ) : Option (ComputeRootedDigraph q) :=
  if h : IsValidRootedDigraphCode q code then
    some {
      digraph := {
        numVerts := code[0]?.getD 0
        numEdges := code[1]?.getD 0
        head := fun e => ⟨code[2 + q + 2 * e.1]?.getD 0, (h.2.2.2 e).1⟩
        tail := fun e => ⟨code[2 + q + 2 * e.1 + 1]?.getD 0, (h.2.2.2 e).2⟩
      }
      roots := fun i => ⟨code[2 + i.1]?.getD 0, h.2.2.1 i⟩
    }
  else
    none

theorem getElem_flatMap_edges_even {v m : ℕ} (hd tl : Fin m → Fin v) (e : Fin m) :
    ((List.finRange m).flatMap (fun x => [(hd x).1, (tl x).1]))[2 * e.1]? = some (hd e).1 := by
  have haux : ∀ (l : List (Fin m)) (k : ℕ) (hk : k < l.length),
      (l.flatMap (fun x => [(hd x).1, (tl x).1]))[2 * k]? = some (hd (l[k]'hk)).1 := by
    intro l
    induction l with
    | nil => intro k hk; contradiction
    | cons a l ih =>
      intro k hk
      cases k with
      | zero => simp
      | succ k =>
        have hk' : k < l.length := by simpa using hk
        have hidx : 2 * (k + 1) = 2 + 2 * k := by omega
        rw [List.flatMap_cons, hidx, List.getElem?_append_right (by simp)]
        simpa using ih k hk'
  simpa using haux (List.finRange m) e.1 (by simp [e.2])

theorem getElem_flatMap_edges_odd {v m : ℕ} (hd tl : Fin m → Fin v) (e : Fin m) :
    ((List.finRange m).flatMap (fun x => [(hd x).1, (tl x).1]))[2 * e.1 + 1]? = some (tl e).1 := by
  have haux : ∀ (l : List (Fin m)) (k : ℕ) (hk : k < l.length),
      (l.flatMap (fun x => [(hd x).1, (tl x).1]))[2 * k + 1]? = some (tl (l[k]'hk)).1 := by
    intro l
    induction l with
    | nil => intro k hk; contradiction
    | cons a l ih =>
      intro k hk
      cases k with
      | zero => simp
      | succ k =>
        have hk' : k < l.length := by simpa using hk
        have hidx : 2 * (k + 1) + 1 = 2 + (2 * k + 1) := by omega
        rw [List.flatMap_cons, hidx, List.getElem?_append_right (by simp)]
        simpa using ih k hk'
  simpa using haux (List.finRange m) e.1 (by simp [e.2])

theorem encRootedDigraph_getElem_zero {q : ℕ} (H : ComputeRootedDigraph q) :
    (encRootedDigraph H)[0]?.getD 0 = H.digraph.numVerts := by
  unfold encRootedDigraph
  simp

theorem encRootedDigraph_getElem_one {q : ℕ} (H : ComputeRootedDigraph q) :
    (encRootedDigraph H)[1]?.getD 0 = H.digraph.numEdges := by
  unfold encRootedDigraph
  simp

theorem encRootedDigraph_getElem_root {q : ℕ} (H : ComputeRootedDigraph q) (i : Fin q) :
    (encRootedDigraph H)[2 + i.1]?.getD 0 = (H.roots i).1 := by
  unfold encRootedDigraph
  rw [List.getElem?_append_left (by simp; omega)]
  rw [List.getElem?_append_right (by simp)]
  simp

theorem encRootedDigraph_getElem_head {q : ℕ} (H : ComputeRootedDigraph q)
    (e : Fin H.digraph.numEdges) :
    (encRootedDigraph H)[2 + q + 2 * e.1]?.getD 0 = (H.digraph.head e).1 := by
  unfold encRootedDigraph
  rw [List.getElem?_append_right (by simp; omega)]
  have hsub : 2 + q + 2 * e.1 -
      ([H.digraph.numVerts, H.digraph.numEdges] ++ List.ofFn (fun i : Fin q => (H.roots i).1)).length =
      2 * e.1 := by simp; omega
  rw [hsub, getElem_flatMap_edges_even H.digraph.head H.digraph.tail e]
  rfl

theorem encRootedDigraph_getElem_tail {q : ℕ} (H : ComputeRootedDigraph q)
    (e : Fin H.digraph.numEdges) :
    (encRootedDigraph H)[2 + q + 2 * e.1 + 1]?.getD 0 = (H.digraph.tail e).1 := by
  unfold encRootedDigraph
  rw [List.getElem?_append_right (by simp; omega)]
  have hsub : 2 + q + 2 * e.1 + 1 -
      ([H.digraph.numVerts, H.digraph.numEdges] ++ List.ofFn (fun i : Fin q => (H.roots i).1)).length =
      2 * e.1 + 1 := by simp; omega
  rw [hsub, getElem_flatMap_edges_odd H.digraph.head H.digraph.tail e]
  rfl

theorem isValidRootedDigraphCode_encRootedDigraph {q : ℕ} (H : ComputeRootedDigraph q) :
    IsValidRootedDigraphCode q (encRootedDigraph H) := by
  refine ⟨by rw [length_encRootedDigraph]; omega, ?_, ?_, ?_⟩
  · rw [length_encRootedDigraph, encRootedDigraph_getElem_one]
  · intro i
    rw [encRootedDigraph_getElem_root, encRootedDigraph_getElem_zero]
    exact (H.roots i).2
  · intro e
    let e' : Fin H.digraph.numEdges := ⟨e.1, encRootedDigraph_getElem_one H ▸ e.2⟩
    have he_eq : e.1 = e'.1 := rfl
    rw [he_eq, encRootedDigraph_getElem_head H e', encRootedDigraph_getElem_tail H e',
      encRootedDigraph_getElem_zero]
    exact ⟨(H.digraph.head e').2, (H.digraph.tail e').2⟩

/-- Round-trip theorem: `decRootedDigraph q (encRootedDigraph H) = some H` for every rooted
digraph `H : ComputeRootedDigraph q`. -/
@[simp]
theorem decRootedDigraph_encRootedDigraph {q : ℕ} (H : ComputeRootedDigraph q) :
    decRootedDigraph q (encRootedDigraph H) = some H := by
  have hval := isValidRootedDigraphCode_encRootedDigraph H
  unfold decRootedDigraph
  simp only [hval, ↓reduceDIte, Option.some.injEq]
  rcases H with ⟨⟨v, m, hd, tl⟩, rts⟩
  have hhd : ∀ e : Fin m,
      (encRootedDigraph ⟨⟨v, m, hd, tl⟩, rts⟩)[2 + q + 2 * e.1]?.getD 0 = (hd e).1 :=
    encRootedDigraph_getElem_head ⟨⟨v, m, hd, tl⟩, rts⟩
  have htl : ∀ e : Fin m,
      (encRootedDigraph ⟨⟨v, m, hd, tl⟩, rts⟩)[2 + q + 2 * e.1 + 1]?.getD 0 = (tl e).1 :=
    encRootedDigraph_getElem_tail ⟨⟨v, m, hd, tl⟩, rts⟩
  have hrts : ∀ i : Fin q,
      (encRootedDigraph ⟨⟨v, m, hd, tl⟩, rts⟩)[2 + i.1]?.getD 0 = (rts i).1 :=
    encRootedDigraph_getElem_root ⟨⟨v, m, hd, tl⟩, rts⟩
  congr 1
  · congr 1
    · funext e
      exact Fin.ext (hhd e)
    · funext e
      exact Fin.ext (htl e)
  · funext i
    exact Fin.ext (hrts i)

/-! ### Section 4: Decidable Isomorphism Test on Encodings and Bounded Folio Sets -/

/-- Decidable isomorphism relation between two word-list encodings `c₁, c₂ : List ℕ` of
`q`-rooted digraphs. -/
def IsIsoRootedDigraphCode (q : ℕ) (c₁ c₂ : List ℕ) : Prop :=
  match decRootedDigraph q c₁, decRootedDigraph q c₂ with
  | some H₁, some H₂ => IsRootedDigraphIso H₁ H₂
  | none, none => True
  | _, _ => False

instance instDecidableIsIsoRootedDigraphCode (q : ℕ) (c₁ c₂ : List ℕ) :
    Decidable (IsIsoRootedDigraphCode q c₁ c₂) := by
  unfold IsIsoRootedDigraphCode
  cases decRootedDigraph q c₁ <;> cases decRootedDigraph q c₂ <;> infer_instance

/-- Soundness and completeness of `IsIsoRootedDigraphCode` on encodings of rooted digraphs. -/
@[simp]
theorem isIsoRootedDigraphCode_enc_iff {q : ℕ} (H₁ H₂ : ComputeRootedDigraph q) :
    IsIsoRootedDigraphCode q (encRootedDigraph H₁) (encRootedDigraph H₂) ↔
      IsRootedDigraphIso H₁ H₂ := by
  simp [IsIsoRootedDigraphCode]

/-- Decidable predicate testing whether a word list `c : List ℕ` is the canonical encoding of a
`q`-rooted digraph with detail `≤ δ`. -/
def IsDetailLeCode (q δ : ℕ) (c : List ℕ) : Prop :=
  match decRootedDigraph q c with
  | some H => c = encRootedDigraph H ∧ H.HasDetailLe δ
  | none => False

instance instDecidableIsDetailLeCode (q δ : ℕ) (c : List ℕ) :
    Decidable (IsDetailLeCode q δ c) := by
  unfold IsDetailLeCode
  cases decRootedDigraph q c with
  | none => exact isFalse id
  | some H => infer_instance

theorem isDetailLeCode_encRootedDigraph {q δ : ℕ} {H : ComputeRootedDigraph q}
    (h : H.HasDetailLe δ) :
    IsDetailLeCode q δ (encRootedDigraph H) := by
  simp [IsDetailLeCode, h]

/-- Every `c` satisfying `IsDetailLeCode q δ c` has length `≤ 2 + q + 2 * δ` and words `≤ q + δ`. -/
theorem length_and_words_le_of_isDetailLeCode {q δ : ℕ} {c : List ℕ}
    (hc : IsDetailLeCode q δ c) :
    c.length ≤ 2 + q + 2 * δ ∧ ∀ w ∈ c, w ≤ q + δ := by
  unfold IsDetailLeCode at hc
  cases hdec : decRootedDigraph q c with
  | none => rw [hdec] at hc; exact False.elim hc
  | some H =>
    rw [hdec] at hc
    rcases hc with ⟨rfl, hdet⟩
    exact ⟨length_encRootedDigraph_le_of_hasDetailLe hdet,
      fun w hw => mem_encRootedDigraph_le_of_hasDetailLe hdet hw⟩

/-- Bounded representation of a set of `q`-rooted digraphs of detail `≤ δ` up to isomorphism:
a duplicate-free list of pairwise non-isomorphic codes `codes : List (List ℕ)`, each satisfying
`IsDetailLeCode q δ`. -/
structure FolioSetRep (q δ : ℕ) where
  /-- List of representative word-list encodings. -/
  codes : List (List ℕ)
  /-- Every code in `codes` is the encoding of a `q`-rooted digraph with detail `≤ δ`. -/
  all_detail : ∀ c ∈ codes, IsDetailLeCode q δ c
  /-- Representative codes are pairwise non-isomorphic. -/
  pairwise_nonIso : codes.Pairwise (fun c₁ c₂ => ¬ IsIsoRootedDigraphCode q c₁ c₂)

/-- Membership of a `q`-rooted digraph `H` (up to isomorphism) in a `FolioSetRep q δ`. -/
def FolioSetRep.MemIso {q δ : ℕ} (H : ComputeRootedDigraph q) (F : FolioSetRep q δ) : Prop :=
  ∃ c ∈ F.codes, IsIsoRootedDigraphCode q (encRootedDigraph H) c

instance instDecidableFolioSetRepMemIso {q δ : ℕ} (H : ComputeRootedDigraph q)
    (F : FolioSetRep q δ) : Decidable (F.MemIso H) := by
  unfold FolioSetRep.MemIso
  infer_instance

/-- Flat word-list serialization of a `FolioSetRep q δ`:
`[codes.length] ++ codes.flatMap (fun c => c.length :: c)`. -/
def encFolioSetRep {q δ : ℕ} (F : FolioSetRep q δ) : List ℕ :=
  [F.codes.length] ++ F.codes.flatMap (fun c => c.length :: c)

/-- Enumerating all lists of length `len` with entries in `0 .. maxVal`. -/
def allBoundedWordLists (maxVal : ℕ) : (len : ℕ) → List (List ℕ)
  | 0 => [[]]
  | len + 1 =>
    (List.range (maxVal + 1)).flatMap (fun x =>
      (allBoundedWordLists maxVal len).map (fun l => x :: l))

theorem mem_allBoundedWordLists_iff (maxVal : ℕ) :
    ∀ (len : ℕ) (c : List ℕ),
      c ∈ allBoundedWordLists maxVal len ↔ c.length = len ∧ ∀ w ∈ c, w ≤ maxVal
  | 0, [] => by simp [allBoundedWordLists]
  | 0, _ :: _ => by simp [allBoundedWordLists]
  | len + 1, [] => by simp [allBoundedWordLists]
  | len + 1, x :: tl => by
    simp only [allBoundedWordLists, List.mem_flatMap, List.mem_range, List.mem_map,
       List.cons.injEq, List.length_cons, Nat.add_right_cancel_iff, List.mem_cons,
      forall_eq_or_imp, Nat.lt_succ_iff]
    constructor
    · rintro ⟨a, ha, l, hl, rfl, rfl⟩
      rcases (mem_allBoundedWordLists_iff maxVal len l).mp hl with ⟨hlen, hmem⟩
      exact ⟨hlen, ha, hmem⟩
    · rintro ⟨hlen, hx, hmem⟩
      exact ⟨x, hx, tl, (mem_allBoundedWordLists_iff maxVal len tl).mpr ⟨hlen, hmem⟩, rfl, rfl⟩

/-- Finite list of all valid word-list encodings of `q`-rooted digraphs with detail `≤ δ`. -/
def allDetailLeCodes (q δ : ℕ) : List (List ℕ) :=
  ((List.range (2 + q + 2 * δ + 1)).flatMap (allBoundedWordLists (q + δ))).filter
    (fun c => decide (IsDetailLeCode q δ c))

theorem mem_allDetailLeCodes_iff (q δ : ℕ) (c : List ℕ) :
    c ∈ allDetailLeCodes q δ ↔ IsDetailLeCode q δ c := by
  unfold allDetailLeCodes
  simp only [List.mem_filter, List.mem_flatMap, List.mem_range, Nat.lt_succ_iff,
    mem_allBoundedWordLists_iff, decide_eq_true_eq]
  constructor
  · rintro ⟨_, h⟩
    exact h
  · intro h
    rcases length_and_words_le_of_isDetailLeCode h with ⟨hlen, hwords⟩
    exact ⟨⟨c.length, hlen, rfl, hwords⟩, h⟩

/-- Deduplicate a list of codes up to `IsIsoRootedDigraphCode q`. -/
def dedupIsoCodes (q : ℕ) : List (List ℕ) → List (List ℕ)
  | [] => []
  | c :: cs =>
    if (dedupIsoCodes q cs).any (fun c' => decide (IsIsoRootedDigraphCode q c c')) then
      dedupIsoCodes q cs
    else
      c :: dedupIsoCodes q cs

theorem dedupIsoCodes_sub (q : ℕ) :
    ∀ (cs : List (List ℕ)) {c : List ℕ}, c ∈ dedupIsoCodes q cs → c ∈ cs
  | [], _, hc => by contradiction
  | a :: cs, c, hc => by
    unfold dedupIsoCodes at hc
    split_ifs at hc with h
    · exact List.mem_cons_of_mem a (dedupIsoCodes_sub q cs hc)
    · rcases List.mem_cons.mp hc with rfl | hmem
      · exact List.mem_cons_self
      · exact List.mem_cons_of_mem a (dedupIsoCodes_sub q cs hmem)

theorem isIsoRootedDigraphCode_trans_of_detail {q δ : ℕ} {c₁ c₂ c₃ : List ℕ}
    (h1 : IsDetailLeCode q δ c₁) (h2 : IsDetailLeCode q δ c₂) (h3 : IsDetailLeCode q δ c₃)
    (h12 : IsIsoRootedDigraphCode q c₁ c₂) (h23 : IsIsoRootedDigraphCode q c₂ c₃) :
    IsIsoRootedDigraphCode q c₁ c₃ := by
  unfold IsDetailLeCode at h1 h2 h3
  unfold IsIsoRootedDigraphCode at h12 h23 ⊢
  cases hd1 : decRootedDigraph q c₁ <;> rw [hd1] at h1 h12
  · exact False.elim h1
  cases hd2 : decRootedDigraph q c₂ <;> rw [hd2] at h2 h12 h23
  · exact False.elim h2
  cases hd3 : decRootedDigraph q c₃ <;> rw [hd3] at h3 h23
  · exact False.elim h3
  exact isRootedDigraphIso_trans h12 h23

theorem dedupIsoCodes_pairwise (q : ℕ) :
    ∀ (cs : List (List ℕ)),
      (dedupIsoCodes q cs).Pairwise (fun c₁ c₂ => ¬ IsIsoRootedDigraphCode q c₁ c₂)
  | [] => List.Pairwise.nil
  | c :: cs => by
    unfold dedupIsoCodes
    split_ifs with h
    · exact dedupIsoCodes_pairwise q cs
    · rw [List.pairwise_cons]
      refine ⟨fun c' hc' hiso => h ?_, dedupIsoCodes_pairwise q cs⟩
      rw [List.any_eq_true]
      exact ⟨c', hc', decide_eq_true hiso⟩

theorem exists_iso_dedupIsoCodes {q δ : ℕ} :
    ∀ (cs : List (List ℕ)),
      (∀ x ∈ cs, IsDetailLeCode q δ x) →
      ∀ c ∈ cs, ∃ c' ∈ dedupIsoCodes q cs, IsIsoRootedDigraphCode q c c'
  | [], _, c, hc => by contradiction
  | a :: cs, hall, c, hc => by
    have hall_cs : ∀ x ∈ cs, IsDetailLeCode q δ x :=
      fun x hx => hall x (List.mem_cons_of_mem a hx)
    unfold dedupIsoCodes
    rcases List.mem_cons.mp hc with rfl | hmem
    · split_ifs with h
      · rw [List.any_eq_true] at h
        rcases h with ⟨c', hc', hiso⟩
        exact ⟨c', hc', of_decide_eq_true hiso⟩
      · refine ⟨c, List.mem_cons_self, ?_⟩
        have hdet : IsDetailLeCode q δ c := hall c List.mem_cons_self
        unfold IsDetailLeCode at hdet
        unfold IsIsoRootedDigraphCode
        cases hd : decRootedDigraph q c <;> rw [hd] at hdet
        · exact False.elim hdet
        · exact isRootedDigraphIso_refl _
    · rcases exists_iso_dedupIsoCodes cs hall_cs c hmem with ⟨c', hc', hiso⟩
      split_ifs with h
      · exact ⟨c', hc', hiso⟩
      · exact ⟨c', List.mem_cons_of_mem a hc', hiso⟩

/-- Canonical `FolioSetRep q δ` of all `q`-rooted digraphs with detail `≤ δ` satisfying an
isomorphism-invariant decidable predicate `P`. -/
def buildFolioSetRep (q δ : ℕ) (P : ComputeRootedDigraph q → Prop) [DecidablePred P] :
    FolioSetRep q δ where
  codes := dedupIsoCodes q ((allDetailLeCodes q δ).filter (fun c =>
    match decRootedDigraph q c with
    | some H => decide (P H)
    | none => false))
  all_detail c hc := by
    have hmem := dedupIsoCodes_sub q _ hc
    rw [List.mem_filter, mem_allDetailLeCodes_iff] at hmem
    exact hmem.1
  pairwise_nonIso := dedupIsoCodes_pairwise q _

/-- Correctness of `buildFolioSetRep`: for any isomorphism-invariant predicate `P`, a rooted
digraph `H` with detail `≤ δ` belongs (up to isomorphism) to `buildFolioSetRep q δ P` if and only if
`P H` holds. -/
theorem memIso_buildFolioSetRep_iff {q δ : ℕ} (P : ComputeRootedDigraph q → Prop)
    [DecidablePred P]
    (hP_iso : ∀ ⦃H₁ H₂ : ComputeRootedDigraph q⦄, IsRootedDigraphIso H₁ H₂ → (P H₁ ↔ P H₂))
    {H : ComputeRootedDigraph q} (hdet : H.HasDetailLe δ) :
    (buildFolioSetRep q δ P).MemIso H ↔ P H := by
  unfold FolioSetRep.MemIso buildFolioSetRep
  dsimp only
  let filtered := (allDetailLeCodes q δ).filter (fun c =>
    match decRootedDigraph q c with
    | some H' => decide (P H')
    | none => false)
  have hall_det : ∀ x ∈ filtered, IsDetailLeCode q δ x := by
    intro x hx
    rw [List.mem_filter, mem_allDetailLeCodes_iff] at hx
    exact hx.1
  constructor
  · rintro ⟨c, hc_mem, hiso⟩
    have hc_filt := dedupIsoCodes_sub q filtered hc_mem
    rw [List.mem_filter, mem_allDetailLeCodes_iff] at hc_filt
    rcases hc_filt with ⟨hc_det, hc_P⟩
    unfold IsDetailLeCode at hc_det
    cases hd : decRootedDigraph q c with
    | none => rw [hd] at hc_det; exact False.elim hc_det
    | some H' =>
      rw [hd] at hc_det hc_P
      have hPH' : P H' := of_decide_eq_true hc_P
      unfold IsIsoRootedDigraphCode at hiso
      rw [decRootedDigraph_encRootedDigraph, hd] at hiso
      exact (hP_iso hiso).mpr hPH'
  · intro hPH
    have henc_filt : encRootedDigraph H ∈ filtered := by
      rw [List.mem_filter, mem_allDetailLeCodes_iff]
      refine ⟨isDetailLeCode_encRootedDigraph hdet, ?_⟩
      rw [decRootedDigraph_encRootedDigraph]
      exact decide_eq_true hPH
    exact exists_iso_dedupIsoCodes filtered hall_det (encRootedDigraph H) henc_filt

/-- Every `FolioSetRep q δ` has at most `(allDetailLeCodes q δ).length` representative codes
(a finite constant depending only on `q` and `δ`). -/
theorem length_codes_le_allDetailLeCodes {q δ : ℕ} (F : FolioSetRep q δ) :
    F.codes.length ≤ (allDetailLeCodes q δ).length := by
  have hnodup : F.codes.Nodup := by
    apply F.pairwise_nonIso.imp_of_mem
    intro c₁ c₂ hc₁ _ hne heq
    subst heq
    apply hne
    have hdet := F.all_detail c₁ hc₁
    unfold IsDetailLeCode at hdet
    unfold IsIsoRootedDigraphCode
    cases hd : decRootedDigraph q c₁ <;> rw [hd] at hdet
    · exact False.elim hdet
    · exact isRootedDigraphIso_refl _
  exact List.Subperm.length_le
    (hnodup.subperm (fun c hc =>
      (mem_allDetailLeCodes_iff q δ c).mpr (F.all_detail c hc)))

end GraphMinor.Compute
