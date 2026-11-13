module

public import GraphMinor.HP25.Web

/-!
# The basic definitions of the crossing extractor

This file gives the definitions of Section 2 of the note `docs/crossing/crossing_extractor.tex` (the
crossing extractor that replaces Shiloach's algorithm in Graph Minors XIII, (8.1)), and the plain
notions of connectivity they use.

A graph `K` is a `SimpleGraph V` supported on a set `S` of vertices (`HP25.IsSupportedOn K S`), and
the cycle is a list `D` with `HP25.IsCycleList K D`.

* `nbhd G A`: the neighbourhood `N_G(A)` of a set `A`, the vertices outside `A` with a neighbour in
  `A`.
* `ReachIn G T a b` and `IsConnectedOn G T`: walks that stay in a set `T`, and connectivity of the
  subgraph induced by `T`.
* `apex G D`: the graph `J = K + x` on `Option V`, where the new vertex `x` is `none` and is
  adjacent to every vertex of `D`; `apexVerts S` is its vertex set.
* `RootedConn J T x k`: the condition `𝓡_k(J, x)` on a graph `J` with vertex set `T`.
* `IsClean K S D`: the instance `(K, D)` is clean.
* `IsFourFan`, `HasFourFan`: four-fans from a vertex to `D`.
* `IsUnseparable J T v x k`: no set of at most `k` other vertices separates `v` from `x`;
  `IsGood` is the case `k = 3` (Section 9.4).
* `IsSeparator`, `IsMinSeparator`, `sourceSide`, `IsMaxSourceSeparator`: vertex separators between
  `z` and `x`, and the minimum separator with the largest source side (Section 2.2).
* `IsPathList`, `IsDPathList`, `IsCrossingPair`: paths and crossings written as vertex lists, as
  the programs store them. A crossing pair is a crossing of `D` up to the order and the direction
  of its two paths.
* `InDistinctBridges K D L₁ L₂`: no path of `K - V(D)` joins an inner vertex of `L₁` to an inner
  vertex of `L₂` (the two paths use distinct `D`-bridges, Section 5).
-/

@[expose] public section

namespace GraphMinor.Crossing

open SimpleGraph

variable {V W : Type*}

/-! ### Neighbourhoods and connectivity inside a set -/

/-- The neighbourhood `N_G(A)` of a set `A` of vertices: the vertices outside `A` with a neighbour
in `A` (Section 3: "with $S=N_K(A)$"). -/
def nbhd (G : SimpleGraph W) (A : Set W) : Set W :=
  {v | v ∉ A ∧ ∃ a ∈ A, G.Adj a v}

/-- Some walk of `G` from `a` to `b` has all its vertices in `T`. -/
def ReachIn (G : SimpleGraph W) (T : Set W) (a b : W) : Prop :=
  ∃ p : G.Walk a b, ∀ y ∈ p.support, y ∈ T

/-- The subgraph of `G` induced by `T` is connected: `T` is nonempty and any two vertices of `T`
are joined by a walk inside `T`. -/
def IsConnectedOn (G : SimpleGraph W) (T : Set W) : Prop :=
  T.Nonempty ∧ ∀ a ∈ T, ∀ b ∈ T, ReachIn G T a b

/-- `C` is a component of the subgraph of `G` induced by `T`: a connected subset of `T` with no
edge to the rest of `T`. -/
def IsComponentIn (G : SimpleGraph W) (T C : Set W) : Prop :=
  C ⊆ T ∧ IsConnectedOn G C ∧ ∀ a ∈ C, ∀ b ∈ T, G.Adj a b → b ∈ C

/-! ### The apex graph and the root condition (Section 2) -/

/-- The adjacency of the apex graph `K + x` on `Option V`, with `x = none`. -/
def apexAdj (G : SimpleGraph V) (D : List V) : Option V → Option V → Prop
  | some a, some b => G.Adj a b
  | none, some d => d ∈ D
  | some d, none => d ∈ D
  | none, none => False

/-- **The apex graph** `J = K + x` (Section 2): "Add a new vertex $x$, adjacent to every vertex
of $D$, and write $J=K+x$." The vertex `x` is `none`, and a
vertex `v` of `K` is `some v`. -/
def apex (G : SimpleGraph V) (D : List V) : SimpleGraph (Option V) where
  Adj := apexAdj G D
  symm := ⟨fun a b h => by
    cases a <;> cases b <;> simp only [apexAdj] at h ⊢ <;> first | exact h | exact h.symm⟩
  loopless := ⟨fun a h => by cases a <;> simp only [apexAdj] at h; exact G.loopless.irrefl _ h⟩

/-- The vertex set of `K + x`, when `K` has vertex set `S`. -/
def apexVerts (S : Set V) : Set (Option V) :=
  insert none (some '' S)

/-- **The root condition** `𝓡_k(J, x)` (Section 2), for a graph `J` with vertex set `T`:
"$J-S$ is connected for every set $S\subseteq V(J)\setminus\{x\}$ with $|S|<k$. All these
separators exclude $x$." -/
def RootedConn (J : SimpleGraph W) (T : Set W) (x : W) (k : ℕ) : Prop :=
  ∀ X : Finset W, (X : Set W) ⊆ T \ {x} → X.card < k → IsConnectedOn J (T \ X)

/-- **Clean instances** (Section 2): "We call $(K,D)$ *clean* when $\mathcal R_4(K+x,x)$
holds." Here `K` has vertex set `S`. -/
def IsClean (K : SimpleGraph V) (S : Set V) (D : List V) : Prop :=
  RootedConn (apex K D) (apexVerts S) none 4

/-- **A four-fan** from `v` to `D` (Section 2): "A *four-fan* from a vertex $v$ to $D$ consists
of four paths that share only their first vertex $v$ and end at four distinct vertices of $D$." -/
def IsFourFan (G : SimpleGraph V) (D : List V) (v : V) (e : Fin 4 → V)
    (P : ∀ i, G.Walk v (e i)) : Prop :=
  Function.Injective e ∧ (∀ i, e i ∈ D) ∧ (∀ i, (P i).IsPath) ∧
    ∀ i j, i ≠ j → ∀ y ∈ (P i).support, y ∈ (P j).support → y = v

/-- `v` has a four-fan to `D`. -/
def HasFourFan (G : SimpleGraph V) (D : List V) (v : V) : Prop :=
  ∃ (e : Fin 4 → V) (P : ∀ i, G.Walk v (e i)), IsFourFan G D v e P

/-! ### Separators -/

/-- `v` cannot be separated from `x` by at most `k` other vertices, in the graph `J` with vertex
set `T`: for every set `X` of at most `k` vertices of `T` other than `v` and `x`, some walk from
`v` to `x` avoids `X` (Section 2.2 and Lemma 6: "neither $p$ nor $q$ can be separated from $x$ by
at most two other vertices"). -/
def IsUnseparable (J : SimpleGraph W) (T : Set W) (v x : W) (k : ℕ) : Prop :=
  ∀ X : Finset W, (X : Set W) ⊆ T \ {v, x} → X.card ≤ k → ReachIn J (T \ X) v x

/-- **Good vertices** (Section 9.4): "Call a retained vertex **good** if no set of at most three
other vertices, excluding $x$, separates it from $x$." -/
def IsGood (J : SimpleGraph W) (T : Set W) (v x : W) : Prop :=
  IsUnseparable J T v x 3

/-- `X` is a `z`-`x` vertex separator of the graph `J` with vertex set `T`: a set of vertices of
`T` other than `z` and `x` that meets every walk from `z` to `x` inside `T`. -/
def IsSeparator (J : SimpleGraph W) (T : Set W) (z x : W) (X : Finset W) : Prop :=
  (X : Set W) ⊆ T \ {z, x} ∧ ¬ ReachIn J (T \ X) z x

/-- A minimum `z`-`x` vertex separator. -/
def IsMinSeparator (J : SimpleGraph W) (T : Set W) (z x : W) (X : Finset W) : Prop :=
  IsSeparator J T z x X ∧ ∀ X' : Finset W, IsSeparator J T z x X' → X.card ≤ X'.card

/-- The open source side of a separator `X` (Section 2.2): for a separator $S'$, "the set of
vertices outside $S'$ that are not in the component of $x$ in $J-S'$." Here $S' = X$. -/
def sourceSide (J : SimpleGraph W) (T : Set W) (x : W) (X : Finset W) : Set W :=
  {y | y ∈ T ∧ y ∉ X ∧ ¬ ReachIn J (T \ X) y x}

/-- **The minimum cut with maximum source side** (Section 2.2): a minimum `z`-`x` separator
whose open source side contains that of every minimum `z`-`x` separator. "This $U$ contains the
open source side of every minimum vertex separator between $z$ and $x$." -/
def IsMaxSourceSeparator (J : SimpleGraph W) (T : Set W) (z x : W) (X : Finset W) : Prop :=
  IsMinSeparator J T z x X ∧
    ∀ X' : Finset W, IsMinSeparator J T z x X' → sourceSide J T x X' ⊆ sourceSide J T x X

/-- `k` internally vertex-disjoint paths from `z` to `x` inside `T` (Section 2.1: "asks for
$k\le4$ internally vertex-disjoint paths"). -/
def IsDisjointPathFamily (J : SimpleGraph W) (T : Set W) (z x : W) {k : ℕ}
    (P : Fin k → J.Walk z x) : Prop :=
  (∀ i, (P i).IsPath) ∧ (∀ i, ∀ y ∈ (P i).support, y ∈ T) ∧
    ∀ i j, i ≠ j → ∀ y ∈ (P i).support, y ∈ (P j).support → y = z ∨ y = x

/-! ### Paths and crossings as vertex lists -/

/-- The list `L` is the vertex list of a path of `G`: nonempty, without repeats, and consecutive
entries adjacent. -/
def IsPathList (G : SimpleGraph W) (L : List W) : Prop :=
  L ≠ [] ∧ L.Nodup ∧ L.IsChain G.Adj

/-- The list `L` has ends `a` and `b`, in this order. -/
def HasEnds (L : List W) (a b : W) : Prop :=
  L.head? = some a ∧ L.getLast? = some b

/-- The inner vertices of a path list: all entries but the first and the last. -/
def inner (L : List W) : List W :=
  L.tail.dropLast

/-- `L` is the vertex list of a `D`-path of `G` (a `T`-path of Humeau and Pous, Section 2.1, with
`T = D`): a path with at least two vertices, both ends in `D` and no inner vertex in `D`. -/
def IsDPathList (G : SimpleGraph W) (D : List W) (L : List W) : Prop :=
  IsPathList G L ∧ 2 ≤ L.length ∧ (∀ a, L.head? = some a → a ∈ D) ∧
    (∀ b, L.getLast? = some b → b ∈ D) ∧ ∀ y ∈ inner L, y ∉ D

/-- The ends of `L` are `a` and `b`, in some order. -/
def HasEndsUnordered (L : List W) (a b : W) : Prop :=
  HasEnds L a b ∨ HasEnds L b a

/-- **A crossing pair** of `D`: two disjoint `D`-paths whose ends alternate on `D`. This is a
crossing of `D` (`HP25.IsCrossing`, Definition 2.4 of Humeau and Pous) up to the order and the
direction of the two paths; the note asks for "two disjoint $C$-paths" with "cyclic alternation"
(Lemma 1). -/
def IsCrossingPair (G : SimpleGraph W) (D : List W) (L₁ L₂ : List W) : Prop :=
  IsDPathList G D L₁ ∧ IsDPathList G D L₂ ∧ L₁.Disjoint L₂ ∧
    ∃ i r j s : ℕ, i < r ∧ r < j ∧ j < s ∧ ∃ a c b d : W,
      D[i]? = some a ∧ D[r]? = some c ∧ D[j]? = some b ∧ D[s]? = some d ∧
      ((HasEndsUnordered L₁ a b ∧ HasEndsUnordered L₂ c d) ∨
        (HasEndsUnordered L₁ c d ∧ HasEndsUnordered L₂ a b))

/-- The two paths `L₁`, `L₂` use distinct `D`-bridges (Section 5): no walk of `K` that avoids the
vertices of `D` joins an inner vertex of `L₁` to an inner vertex of `L₂`. A chord has no inner
vertex, so a pair with a chord always satisfies this. -/
def InDistinctBridges (K : SimpleGraph W) (D : List W) (L₁ L₂ : List W) : Prop :=
  ∀ a ∈ inner L₁, ∀ b ∈ inner L₂, ¬ ReachIn K {y | y ∉ D} a b

/-- `s(u, v)` is an edge of the cycle `D`: `u` and `v` are consecutive on `D`, cyclically. -/
def IsCycleEdge (D : List W) (u v : W) : Prop :=
  ∃ p ∈ D.zip (D.rotate 1), p = (u, v) ∨ p = (v, u)

end GraphMinor.Crossing
