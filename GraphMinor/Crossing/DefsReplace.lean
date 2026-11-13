module

public import GraphMinor.Crossing.Defs

/-!
# The replacement at a small separator (Section 3 of the note)

Section 3 of `docs/crossing/crossing_extractor.tex`: "Let $A\subseteq V(K)\setminus V(D)$ be a
connected set, and let $S=N_K(A)$, with $|S|\le 3$. The *replacement* deletes $A$ and adds every
missing edge of the clique on $S$. We record the graph before the operation, the set $A$, and the
set $S$." After Lemma 1: "We also allow deleting several components of $K-S$ at once, all with
neighborhood $S$, provided we record one of them. The recorded component is connected and has a
neighbor at every vertex of $S$."

* `replaceGraph G A S`: delete `A` and make `S` a clique.
* `ReplRecord`: the record (the graph before, its vertex set, the deleted set `A`, the boundary
  `S`, and the recorded connected component); `ReplRecord.IsValid` holds when the operation is
  allowed.
* `usesNewEdge`, `firstIn`, `lastIn`, `spliceBetween`: the reverse direction of Lemma 1, which
  replaces the segment of the affected path between its first and last vertices of `S` by a path
  found in `K[A ∪ {p, q}]`.
-/

@[expose] public section

namespace GraphMinor.Crossing

open SimpleGraph

variable {V : Type*}

/-- **The replacement** (Section 3): it "deletes $A$ and adds every missing edge of the clique on
$S$." -/
def replaceGraph (G : SimpleGraph V) (A S : Set V) : SimpleGraph V where
  Adj a b := (G.Adj a b ∧ a ∉ A ∧ b ∉ A) ∨ (a ∈ S ∧ b ∈ S ∧ a ≠ b)
  symm := ⟨fun a b h => by
    rcases h with ⟨h, ha, hb⟩ | ⟨ha, hb, hab⟩
    · exact Or.inl ⟨h.symm, hb, ha⟩
    · exact Or.inr ⟨hb, ha, Ne.symm hab⟩⟩
  loopless := ⟨fun a h => by
    rcases h with ⟨h, -, -⟩ | ⟨-, -, h⟩
    · exact G.loopless.irrefl _ h
    · exact h rfl⟩

/-- **The record of a replacement** (Section 3): "We record the graph before the operation, the set
$A$, and the set $S$." For the version with several components, the record also holds the
"recorded component", which is connected and has a neighbor at every vertex of `S`. -/
structure ReplRecord (V : Type*) where
  /-- The graph before the operation. -/
  graph : SimpleGraph V
  /-- Its vertex set. -/
  verts : Set V
  /-- The deleted set `A`, the union of the deleted components. -/
  deleted : Set V
  /-- The boundary `S`. -/
  boundary : Finset V
  /-- The recorded connected component, used by the reverse search of Lemma 1. -/
  rep : Set V

namespace ReplRecord

/-- The graph after the replacement. -/
def newGraph (r : ReplRecord V) : SimpleGraph V :=
  replaceGraph r.graph r.deleted r.boundary

/-- The vertex set after the replacement. -/
def newVerts (r : ReplRecord V) : Set V :=
  r.verts \ r.deleted

/-- **The replacement is allowed** (Section 3), for the cycle `D`:
* the deleted set lies in `V(K) \ V(D)`;
* the boundary has at most three vertices, all retained;
* every component of `K[A]` has the boundary `S` ("deleting several components of $K-S$ at once,
  all with neighborhood $S$");
* the recorded component is a component of `K[A]` with this boundary ("The recorded component is
  connected and has a neighbor at every vertex of $S$.").
The single version is the case where `A` itself is the recorded component. -/
def IsValid (r : ReplRecord V) (D : List V) : Prop :=
  r.deleted ⊆ r.verts ∧ (∀ a ∈ r.deleted, a ∉ D) ∧ r.boundary.card ≤ 3 ∧
    (r.boundary : Set V) ⊆ r.verts \ r.deleted ∧
    (∀ C, IsComponentIn r.graph r.deleted C → nbhd r.graph C = r.boundary) ∧
    IsComponentIn r.graph r.deleted r.rep

end ReplRecord

/-! ### The reverse direction of Lemma 1 -/

/-- The path list `L` uses an edge that `G` lacks: two consecutive entries of `L` are not adjacent
in `G` (Lemma 1: "If neither returned path uses a newly added edge, we keep both."). -/
def usesNewEdge (G : SimpleGraph V) (L : List V) : Prop :=
  ∃ i : ℕ, ∃ a b : V, L[i]? = some a ∧ L[i + 1]? = some b ∧ ¬ G.Adj a b

variable [DecidableEq V]

/-- The first vertex of `S` on `L` (Lemma 1: "Let $p$ and $q$ be the first and last vertices of $S$
on this path."). -/
def firstIn (S : Finset V) (L : List V) : Option V :=
  (L.dropWhile (fun y => decide (y ∉ S))).head?

/-- The last vertex of `S` on `L`. -/
def lastIn (S : Finset V) (L : List V) : Option V :=
  firstIn S L.reverse

/-- Replace the segment of `L` between its first and last vertices of `S` by `Y` (Lemma 1:
"We replace the whole segment between $p$ and $q$ by this path."). `Y` runs from the first to the
last vertex of `S` on `L`. -/
def spliceBetween (S : Finset V) (L Y : List V) : List V :=
  L.takeWhile (fun y => decide (y ∉ S)) ++ Y ++
    (L.reverse.takeWhile (fun y => decide (y ∉ S))).reverse

/-- `Y` is a search path for the affected path `L` in the reverse direction of Lemma 1: a path of
`K[A ∪ {p, q}]`, with `A` the recorded component, from the first vertex `p` of `S` on `L` to the
last one `q` ("We search for a path from $p$ to $q$ in $K[A\cup\{p,q\}]$."). -/
def IsReplSearchPath (r : ReplRecord V) (L Y : List V) : Prop :=
  ∃ p q, firstIn r.boundary L = some p ∧ lastIn r.boundary L = some q ∧
    IsPathList (HP25.restrict r.graph (r.rep ∪ {p, q})) Y ∧ HasEnds Y p q

end GraphMinor.Crossing
