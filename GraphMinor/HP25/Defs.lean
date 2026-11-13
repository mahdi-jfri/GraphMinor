module

public import Mathlib.Combinatorics.SimpleGraph.Paths
public import Mathlib.Combinatorics.SimpleGraph.Operations

/-!
# Definitions of Section 2 of Humeau and Pous, *On the two paths theorem*

This file gives the definitions of Sections 2.1 and 2.3 of S. Humeau and D. Pous, *On the Two
Paths Theorem and the Two Disjoint Paths Problem*, arXiv:2505.16431v2 (14 August 2025), on
Mathlib's simple graphs:

* `IsSetPath G H K p`: `p` is an `H`-`K` path (page 5);
* `IsTPath G T p`: `p` is a `T`-path, an `H`-`K` path with `H = K = T`;
* `IsCrossing G T Q R`, `IsCrossed G T`: crossings of a tuple (Definition 2.4, page 7);
* `IsMaximallyCrossless G T` (Definition 2.4);
* `IsConnectedAvoiding G X y A`: some path from `y` to `A` has no inner vertex in `X`;
* `IsOnSide G X A y`: the reading of "`y` is on `P`-side `i`" (page 17) that the proofs use, with
  `X = C ∪ P` and `A` the interior of `Pᵢ`.

A tuple is a `List V`. The paper writes vertices of a tuple as `x₁, …, x_k`; position `i` of the
list is `T[i]?`, counted from `0`.
-/

@[expose] public section

namespace GraphMinor.HP25

open SimpleGraph

variable {V : Type*} (G : SimpleGraph V)

/-- An *`H`-`K` path* (Section 2.1, page 5): "Given two sets $H,K$ of vertices, a path
$P=x_1\dots x_k$ is an *$H$-$K$ path* if $x_1\in H$, $x_k\in K$, and $x_i\not\in H\cup K$ for all
$1<i<k$." The inner vertices of a path are the vertices of its support other than its ends. -/
def IsSetPath (H K : Set V) {u v : V} (p : G.Walk u v) : Prop :=
  p.IsPath ∧ u ∈ H ∧ v ∈ K ∧ ∀ x ∈ p.support, x ≠ u → x ≠ v → x ∉ H ∧ x ∉ K

/-- A *`T`-path* (Section 2.1, page 5): "When $H=K$ we simply say that $P$ is an *$H$-path*."
Here `T` is a tuple, read as the set of its entries. -/
def IsTPath (T : List V) {u v : V} (p : G.Walk u v) : Prop :=
  IsSetPath G {x | x ∈ T} {x | x ∈ T} p

/-- A *crossing* of a tuple (Definition 2.4, page 7): "Let $T=(x_1,\dots,x_k)$ be a tuple of at
least three pairwise distinct vertices in a graph $G$. A *crossing* of $T$ is a pair of disjoint
$T$-paths, from $x_i$ to $x_j$ and $x_r$ to $x_s$, respectively, such that $i<r<j<s$."
"In this work, *disjoint paths* always means vertex-disjoint paths" (page 5). The conditions on `T`
itself are hypotheses of the results, not part of this definition. -/
def IsCrossing (T : List V) {a b c d : V} (Q : G.Walk a b) (R : G.Walk c d) : Prop :=
  (∃ i r j s : ℕ, i < r ∧ r < j ∧ j < s ∧
    T[i]? = some a ∧ T[r]? = some c ∧ T[j]? = some b ∧ T[s]? = some d) ∧
  IsTPath G T Q ∧ IsTPath G T R ∧ Q.support.Disjoint R.support

/-- "The tuple $T$ is *crossed* if it admits a crossing; it is *crossless* otherwise."
(Definition 2.4, page 7.) -/
def IsCrossed (T : List V) : Prop :=
  ∃ (a b c d : V) (Q : G.Walk a b) (R : G.Walk c d), IsCrossing G T Q R

/-- "The graph $G$ is *maximally $T$-crossless* when $T$ is crossless and in any edge extension of
$G$, $T$ crossed." (Definition 2.4, page 7.) An *edge extension* is "any graph obtained from it by
adding a new edge" (page 1). -/
def IsMaximallyCrossless (T : List V) : Prop :=
  ¬ IsCrossed G T ∧ ∀ u v : V, u ≠ v → ¬ G.Adj u v → IsCrossed (G ⊔ edge u v) T

/-- `y` is *`X`-connected* to the set `A`: some path from `y` to a vertex of `A` has no inner
vertex in `X`. This is the relation the proofs of Section 5 call "a $C\cup P$-path from $z$ to
$\mathring{P_i}$" (Claim 5.6, page 19) and "a $\mathring{P_1}$-$y_r$ path $Q$ inner disjoint with
$P\cup C$" (Lemma 5.4, page 19). -/
def IsConnectedAvoiding (X : Set V) (y : V) (A : Set V) : Prop :=
  ∃ z ∈ A, ∃ p : G.Walk y z, p.IsPath ∧ ∀ x ∈ p.support, x ≠ y → x ≠ z → x ∉ X

/-- `y` is on the side `A` of the path `P` (page 17): "we say that a vertex $y\in P$ *is on
$P$-side $i$* when $y$ and $\mathring{P_i}$ are $P$-connected". Read literally the definition never
holds, since a `P`-path has both ends in `P` and $\mathring{P_i}$ misses `P`. We use the reading of
the proofs (Lemma 5.4, page 19): `X` is `C ∪ P` and `A` is the interior of `Pᵢ`. -/
def IsOnSide (X A : Set V) (y : V) : Prop :=
  IsConnectedAvoiding G X y A

end GraphMinor.HP25
