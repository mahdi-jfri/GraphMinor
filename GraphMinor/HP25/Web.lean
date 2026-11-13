module

public import GraphMinor.HP25.Defs
public import GraphMinor.Surface.Defs

/-!
# Ribs and webs (Definition 2.1 of Humeau and Pous)

S. Humeau and D. Pous, *On the Two Paths Theorem and the Two Disjoint Paths Problem*,
arXiv:2505.16431v2, Definition 2.1 (page 6):

"Given $k\ge 3$, a $k$-*rib* is a planar graph such that in one of its plane embeddings, the outer
face is a cycle of length $k$ called its *frame*, all inner faces are triangles, and all triangles
are inner faces.

A $k$-*web* is a graph constructed from a $k$-rib $R$ by adding one clique $K_T$ per triangle $T$ of
$R$ and making vertices of $K_T$ adjacent to the vertices of $T$."

## Graphs on a vertex set

The papers' operations (web composition, Section 3) glue graphs along paths and cut graphs into
pieces. We keep all graphs on one type `V` and describe a graph with vertex set `S ⊆ V` as a
`SimpleGraph V` whose edges have both ends in `S` (`IsSupportedOn`). The pieces of a graph `G` are
then the graphs `G.restrict S` (`restrict`).

## Plane embeddings

A plane embedding of a graph `G` on a finite vertex set `R` (`PlaneEmbedding`) puts each vertex of
`R` at a point of the complex plane `ℂ` (distinct vertices at distinct points) and each edge `uv`
with both ends in `R` on a line (a set homeomorphic to `[0, 1]`) with ends the points of `u` and
`v`. Two lines of distinct edges meet only at the points of common ends, and no line passes through
the point of a vertex other than its ends. The drawn set `φ.U` is the union of the points and the
lines. The faces are the components of its complement, the outer face is the unbounded one, and the
inner faces are the bounded ones. A face "is" a cycle of the graph when its frontier is the union of
the lines of the cycle (`PlaneEmbedding.cycleImage`).

The plane is `ℂ` because the library's plane topology is stated there: the Jordan curve theorem
(`Surface.jordan_complex`, `Surface.isJordanParts`) and the closed discs bounded by `O`-arcs
(`Surface/PlaneDisc.lean`).

## Webs

A web on `S` is a graph `G` on `S` with a set `R ⊆ S` of rib vertices such that `G` on `R` is a rib,
and every other vertex `x` of `S` has a triangle `tri x` of the rib: the neighbours of `x` are the
vertices of `tri x` and the other vertices of `S \ R` with the same triangle. These other vertices
form the clique `K_T` of the triangle `T = tri x`.
-/

@[expose] public section

namespace GraphMinor.HP25

open SimpleGraph Set Surface

variable {V : Type*}

/-- The graph `G` has vertex set `S`: every edge of `G` has its ends in `S`. -/
def IsSupportedOn (G : SimpleGraph V) (S : Set V) : Prop :=
  ∀ ⦃x y : V⦄, G.Adj x y → x ∈ S

/-- The subgraph of `G` induced by `S`, as a graph on `V` with vertex set `S` (Section 2.1, page 5:
"$G[V]$ for the *subgraph of $G$ induced by $V$*"). -/
def restrict (G : SimpleGraph V) (S : Set V) : SimpleGraph V where
  Adj x y := G.Adj x y ∧ x ∈ S ∧ y ∈ S
  symm := ⟨fun _ _ h => ⟨h.1.symm, h.2.2, h.2.1⟩⟩
  loopless := ⟨fun _ h => G.loopless.irrefl _ h.1⟩

/-- A plane embedding of the graph `G` on the finite vertex set `R ⊆ V` (Definition 2.1, page 6:
"a planar graph such that in one of its plane embeddings"). Each vertex of `R` is drawn at a point
of `ℂ`, and each edge with both ends in `R` is drawn as a line between the points of its ends. -/
structure PlaneEmbedding (G : SimpleGraph V) (R : Set V) where
  /-- The point of the plane where a vertex is drawn. -/
  pt : V → ℂ
  /-- The line drawn for the pair `u v`. -/
  line : V → V → Set ℂ
  /-- The vertex set is finite. -/
  finite : R.Finite
  /-- Distinct vertices of `R` are drawn at distinct points. -/
  injOn : InjOn pt R
  /-- The line of `u v` is the line of `v u`. -/
  line_comm : ∀ u v, line u v = line v u
  /-- Each edge with both ends in `R` is drawn as a line between the points of its ends. -/
  isLine : ∀ u ∈ R, ∀ v ∈ R, G.Adj u v → IsLineWithEnds (line u v) (pt u) (pt v)
  /-- The lines of two distinct edges meet only at the points of their common ends. -/
  inter : ∀ u ∈ R, ∀ v ∈ R, ∀ u' ∈ R, ∀ v' ∈ R, G.Adj u v → G.Adj u' v' →
    s(u, v) ≠ s(u', v') → line u v ∩ line u' v' ⊆ pt '' ({u, v} ∩ {u', v'})
  /-- A line passes through the point of no vertex of `R` other than its ends. -/
  avoid : ∀ u ∈ R, ∀ v ∈ R, G.Adj u v → ∀ w ∈ R, pt w ∈ line u v → w = u ∨ w = v

namespace PlaneEmbedding

variable {G : SimpleGraph V} {R : Set V} (φ : PlaneEmbedding G R)

/-- The drawn set: the points of the vertices and the lines of the edges. -/
def U : Set ℂ :=
  φ.pt '' R ∪ ⋃ u ∈ R, ⋃ v ∈ R, ⋃ (_ : G.Adj u v), φ.line u v

/-- The faces of the embedding: the components of the complement of the drawn set. -/
def faces : Set (Set ℂ) :=
  componentsIn (univ \ φ.U)

/-- The image of a cyclic list of vertices `x₁ … x_k`: the union of the lines
`x₁x₂, …, x_{k-1}x_k, x_kx₁`. -/
def cycleImage (C : List V) : Set ℂ :=
  ⋃ p ∈ C.zip (C.rotate 1), φ.line p.1 p.2

end PlaneEmbedding

/-- The list `C` of vertices is a cycle of `G` (Section 2.1, page 5): it has at least three
vertices, they are distinct, and consecutive vertices, as well as the last and the first, are
adjacent. -/
def IsCycleList (G : SimpleGraph V) (C : List V) : Prop :=
  3 ≤ C.length ∧ C.Nodup ∧ ∀ p ∈ C.zip (C.rotate 1), G.Adj p.1 p.2

/-- `a b c` is a triangle of `G` on the vertex set `R`: three vertices of `R`, pairwise adjacent
(and so distinct). -/
def IsTriangleOn (G : SimpleGraph V) (R : Set V) (a b c : V) : Prop :=
  a ∈ R ∧ b ∈ R ∧ c ∈ R ∧ G.Adj a b ∧ G.Adj b c ∧ G.Adj a c

/-- The plane embedding `φ` of `G` on `R` has the faces of a rib with frame `C` (Definition 2.1,
page 6: "the outer face is a cycle of length $k$ called its *frame*, all inner faces are triangles,
and all triangles are inner faces"):
* every unbounded face is bounded by the image of `C`;
* every bounded face is bounded by the image of a triangle;
* every triangle bounds a bounded face. -/
def PlaneEmbedding.IsRibEmbedding {G : SimpleGraph V} {R : Set V} (φ : PlaneEmbedding G R)
    (C : List V) : Prop :=
  (∀ r ∈ φ.faces, ¬ Bornology.IsBounded r → frontier r = φ.cycleImage C) ∧
    (∀ r ∈ φ.faces, Bornology.IsBounded r →
      ∃ a b c, IsTriangleOn G R a b c ∧ frontier r = φ.cycleImage [a, b, c]) ∧
    (∀ a b c, IsTriangleOn G R a b c →
      ∃ r ∈ φ.faces, Bornology.IsBounded r ∧ frontier r = φ.cycleImage [a, b, c])

/-- **Rib** (Definition 2.1, page 6): `G` on the vertex set `R` is a `k`-rib with frame `C`, where
`k` is the length of `C`. "a planar graph such that in one of its plane embeddings, the outer face is
a cycle of length $k$ called its *frame*, all inner faces are triangles, and all triangles are inner
faces." The frame is a cycle of `G` on `R`, and some plane embedding has the faces of a rib
(`PlaneEmbedding.IsRibEmbedding`). Only the edges of `G` with both ends in `R` matter. -/
def IsRibOn (G : SimpleGraph V) (R : Set V) (C : List V) : Prop :=
  IsCycleList G C ∧ (∀ x ∈ C, x ∈ R) ∧ ∃ φ : PlaneEmbedding G R, φ.IsRibEmbedding C

/-- **Web** (Definition 2.1, page 6): "A $k$-*web* is a graph constructed from a $k$-rib $R$ by
adding one clique $K_T$ per triangle $T$ of $R$ and making vertices of $K_T$ adjacent to the vertices
of $T$." Here `G` is a graph on the vertex set `S`, `R ⊆ S` is the set of rib vertices, `G` on `R` is
a rib with frame `C`, and each vertex `x ∈ S \ R` has a triangle `tri x` of the rib; the neighbours
of `x` are the three vertices of `tri x` and the other vertices of `S \ R` with the same triangle
(the clique `K_T` of `T = tri x`). -/
def IsWebOn (G : SimpleGraph V) (S : Set V) (C : List V) : Prop :=
  IsSupportedOn G S ∧ ∃ (R : Set V) (tri : V → Set V), R ⊆ S ∧ IsRibOn G R C ∧
    ∀ x ∈ S \ R, (∃ a b c, IsTriangleOn G R a b c ∧ tri x = {a, b, c}) ∧
      ∀ y, G.Adj x y ↔ y ∈ tri x ∨ (y ∈ S \ R ∧ y ≠ x ∧ tri y = tri x)

/-- A rib with frame `C` is a graph that is a rib on all its vertices. -/
def IsRib (G : SimpleGraph V) (C : List V) : Prop :=
  IsRibOn G univ C

/-- A web with frame `C` is a graph that is a web on all its vertices. -/
def IsWeb (G : SimpleGraph V) (C : List V) : Prop :=
  IsWebOn G univ C

end GraphMinor.HP25
