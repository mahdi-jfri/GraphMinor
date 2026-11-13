module

public import GraphMinor.GM01.Defs
public import GraphMinor.GM10.BranchWidth
public import GraphMinor.GM10.Defs
public import GraphMinor.GM10.Defs2
public import GraphMinor.GM10.Section10
public import GraphMinor.GM10.Section2Six
public import GraphMinor.GM10.Section4K4
public import GraphMinor.GM10.Section6
public import GraphMinor.GM10.Section7
public import GraphMinor.GM10.Section7ModelRealization
public import GraphMinor.GM10.Section7ModelTangle
public import GraphMinor.GM10.Section7TreeWidth
public import GraphMinor.GM10.Statements
public import GraphMinor.GM10.Submodular
public import GraphMinor.GM10.SubmodularBasic
public import GraphMinor.GM10.SubmodularTree
public import GraphMinor.GM10.TangleLemmas
public import GraphMinor.GM10.TreeWidthClaims
public import GraphMinor.Minor.Basic
public import Mathlib.Data.Prod.Lex
import GraphMinor.GM10.Section11
import GraphMinor.GM10.Section12
import GraphMinor.GM10.Section4Minors
import GraphMinor.GM10.Section4Two
import GraphMinor.GM10.Section7GridTangleTheorem
import GraphMinor.GM10.Section7GridTheorem
import GraphMinor.GM10.Section8
import GraphMinor.GM10.Section9
import GraphMinor.GM10.TreeWidth

/-!
# Graph Minors X. Obstructions to tree-decomposition

N. Robertson and P. D. Seymour, J. Combin. Theory Ser. B 52 (1991) 153–190.

This file lists every numbered result of the paper in order. The proofs are in the other
files of this folder and, for algorithms, in `GraphMinor/Compute/`. The errors of the paper, and how
the Lean statements and proofs correct them, are listed in `corrections/GM10.md`.
-/

public section

namespace GraphMinor.GM10

/-! ## Section 1. Tangles -/

/-! ## Section 2. Some Tangle Lemmas -/

section

open Hypergraph

/-- **Graph Minors X, (2.1)** (page 155):
"If $\mathscr{T}$ is a tangle and $(A, B) \in \mathscr{T}$ then $(B, A) \notin \mathscr{T}$." -/
theorem theorem_2_1 {α β : Type*}
    {G : Hypergraph α β} {θ : ℕ}
    {𝒯 : Set (Hypergraph α β × Hypergraph α β)} (h𝒯 : IsTangle G θ 𝒯)
    {A B : Hypergraph α β} (hAB : (A, B) ∈ 𝒯) :
    (B, A) ∉ 𝒯 := by exact GraphMinor.GM10.theorem_2_1_proof h𝒯 hAB

end

section

open Hypergraph

/-- **Graph Minors X, (2.2)** (page 155):
"If $\mathscr{T}$ is a tangle of order $\theta$ and $(A, B), (A', B') \in \mathscr{T}$ and
$(A \cup A', B \cap B')$ has order $< \theta$ then $(A \cup A', B \cap B') \in \mathscr{T}$." -/
theorem theorem_2_2 {α β : Type*}
    {G : Hypergraph α β} {θ : ℕ}
    {𝒯 : Set (Hypergraph α β × Hypergraph α β)} (h𝒯 : IsTangle G θ 𝒯)
    {A B A' B' : Hypergraph α β} (hAB : (A, B) ∈ 𝒯) (hA'B' : (A', B') ∈ 𝒯)
    (hord : separationOrder (A ∪ A') (B ∩ B') < θ) :
    (A ∪ A', B ∩ B') ∈ 𝒯 := by exact GraphMinor.GM10.theorem_2_2_proof h𝒯 hAB hA'B' hord

end

section

open Hypergraph

/-- **Graph Minors X, (2.3)** (page 155):
"If $\mathscr{T}$ has order $\ge 2$ and $(A_1, B_1), (A_2, B_2), (A_3, B_3) \in \mathscr{T}$
then $E(A_1 \cup A_2 \cup A_3) \ne E(G)$." -/
theorem theorem_2_3 {α β : Type*}
    {G : Hypergraph α β} {θ : ℕ}
    {𝒯 : Set (Hypergraph α β × Hypergraph α β)} (h𝒯 : IsTangle G θ 𝒯) (hθ : 2 ≤ θ)
    {A₁ B₁ A₂ B₂ A₃ B₃ : Hypergraph α β}
    (h₁ : (A₁, B₁) ∈ 𝒯) (h₂ : (A₂, B₂) ∈ 𝒯) (h₃ : (A₃, B₃) ∈ 𝒯) :
    (A₁ ∪ A₂ ∪ A₃).edgeSet ≠ G.edgeSet := by exact GraphMinor.GM10.theorem_2_3_proof h𝒯 hθ h₁ h₂ h₃

end

section

open Hypergraph

/-- **Graph Minors X, (2.4)** (page 156):
"Let $\theta \ge 1$, and let $e$ be an edge of $G$ with size $\ge \theta$. Let $\mathscr{T}$
be the set of all separations $(A, B)$ of $G$ of order $< \theta$ with $e \in E(B)$. Then
$\mathscr{T}$ is a tangle of order $\theta$." -/
theorem theorem_2_4 {α β : Type*}
    {G : Hypergraph α β} {θ : ℕ} (hθ : 1 ≤ θ) {e : β}
    (he : e ∈ G.edgeSet) (hsize : θ ≤ edgeSize G e) :
    IsTangle G θ
      {p | G.IsSeparation p.1 p.2 ∧ separationOrder p.1 p.2 < θ ∧ e ∈ p.2.edgeSet} := by exact GraphMinor.GM10.theorem_2_4_proof hθ he hsize

end

section

open Hypergraph

/-- **Graph Minors X, (2.5)** (page 156):
"$G$ has a tangle if and only if $V(G) \ne \emptyset$." -/
theorem theorem_2_5 {α β : Type*}
    (G : Hypergraph α β) :
    (∃ θ 𝒯, IsTangle G θ 𝒯) ↔ G.vertexSet.Nonempty := by exact GraphMinor.GM10.theorem_2_5_proof G

end

section

open SimpleGraph Hypergraph

universe u v

/-- **Graph Minors X, (2.6)** (page 156):
"(2.6) *If $G$ is a graph, the tangles in $G$ of order 1 are in 1--1 correspondence with the
connected components of $G$, and those of order 2 are in 1-1 correspondence with the blocks of $G$
which have a non-loop edge.*" -/
theorem theorem_2_6 {α : Type u} {β : Type v}
    (G : Hypergraph α β) (hG : G.IsGraph) :
    Nonempty ({𝒯 // IsTangle G 1 𝒯} ≃ {C // IsConnectedComponent G C}) ∧
      Nonempty ({𝒯 // IsTangle G 2 𝒯} ≃ {B // IsBlock G B ∧ ∃ e ∈ B.edgeSet, 2 ≤ edgeSize G e}) := by exact GraphMinor.GM10.theorem_2_6_proof G hG

end

section

open Hypergraph

/-- **Graph Minors X, (2.7)** (page 157):
"Let $\mathscr{T}$ be a set of separations of a hypergraph $G$, each of order $<\theta$,
satisfying the first and second tangle axioms. Then $\mathscr{T}$ is a tangle if and only if
$(K_e, G\setminus e)\in \mathscr{T}$ for every $e\in E(G)$ of size $<\theta$, where $K_e$ is
the hypergraph formed by $e$ and its ends." -/
theorem theorem_2_7 {α β : Type*}
    {G : Hypergraph α β} {θ : ℕ} (hθ : 1 ≤ θ)
    {𝒯 : Set (Hypergraph α β × Hypergraph α β)}
    (hsep : ∀ ⦃A B : Hypergraph α β⦄, (A, B) ∈ 𝒯 → G.IsSeparation A B)
    (hord : ∀ ⦃A B : Hypergraph α β⦄, (A, B) ∈ 𝒯 → separationOrder A B < θ)
    (hax1 : TangleAxiom1 G θ 𝒯) (hax2 : TangleAxiom2 G 𝒯) :
    IsTangle G θ 𝒯 ↔
      ∀ e ∈ G.edgeSet, edgeSize G e < θ →
        (edgeHypergraph G e, G.deleteEdges {e}) ∈ 𝒯 := by exact GraphMinor.GM10.theorem_2_7_proof hθ hsep hord hax1 hax2

end

section

open Hypergraph

/-- **Graph Minors X, (2.8)** (page 157):
"(2.8) *Let $\mathscr{T}$ be a tangle of order $\theta$ in a hypergraph $G$, and let
$(A, B)\in \mathscr{T}$ be extreme. Then $(A, B)$ has order $\theta - 1$. Moreover, if $(B_1, B_2)$
is a separation of $B$, then either $B_1\subseteq A\cap B$ and $B_2 = B$, or $B_2\subseteq A\cap B$
and $B_1 = B$, or $(B_1, B_2)$ has order strictly greater than*
$$\min(|V(A\cap B_1)|, |V(A\cap B_2)|).$$
*In particular, there is no separation $(B_1, B_2)$ of $B$ with $B_1, B_2$ non-null of order $0$,
and there is no edge of $B$ with all its ends in $V(A)$.*" -/
theorem theorem_2_8 {α β : Type*}
    {G : Hypergraph α β} {θ : ℕ}
    {𝒯 : Set (Hypergraph α β × Hypergraph α β)} (h𝒯 : IsTangle G θ 𝒯)
    {A B : Hypergraph α β} (hext : IsExtreme 𝒯 A B) :
    separationOrder A B = θ - 1 ∧
    (∀ ⦃B₁ B₂ : Hypergraph α β⦄, B.IsSeparation B₁ B₂ →
      (B₁ ≤ A ∩ B ∧ B₂ = B) ∨ (B₂ ≤ A ∩ B ∧ B₁ = B) ∨
        min (A ∩ B₁).vertexSet.ncard (A ∩ B₂).vertexSet.ncard < separationOrder B₁ B₂) ∧
    (∀ ⦃B₁ B₂ : Hypergraph α β⦄, B.IsSeparation B₁ B₂ →
      IsNonNull B₁ → IsNonNull B₂ → separationOrder B₁ B₂ ≠ 0) ∧
    (∀ e ∈ B.edgeSet, ¬ B.ends e ⊆ A.vertexSet) := by exact GraphMinor.GM10.theorem_2_8_proof h𝒯 hext

end

section

open Hypergraph

/-- **Graph Minors X, (2.9)** (page 158):
"Let $\mathscr{T}$ be a tangle of order $\theta$ in a hypergraph $G$, and let $(A_1, B_1)\in
\mathscr{T}$. Let $(A_2, B_2)$ be a separation of order $<\theta$. If either* (i)
$V(B_1)\subseteq V(B_2)$, or (ii) $V(A_2)\subseteq V(A_1)$, or (iii) $\theta \ge 2$ and
$E(A_2)\subseteq E(A_1)$ (equivalently, $E(B_1)\subseteq E(B_2)$) *then* $(A_2, B_2)\in
\mathscr{T}$." -/
theorem theorem_2_9 {α β : Type*}
    {G : Hypergraph α β} {θ : ℕ}
    {𝒯 : Set (Hypergraph α β × Hypergraph α β)} (h𝒯 : IsTangle G θ 𝒯)
    {A₁ B₁ A₂ B₂ : Hypergraph α β} (h₁ : (A₁, B₁) ∈ 𝒯)
    (hsep₂ : G.IsSeparation A₂ B₂) (hord₂ : separationOrder A₂ B₂ < θ)
    (h : B₁.vertexSet ⊆ B₂.vertexSet ∨ A₂.vertexSet ⊆ A₁.vertexSet ∨
      (2 ≤ θ ∧ A₂.edgeSet ⊆ A₁.edgeSet)) :
    (A₂, B₂) ∈ 𝒯 := by exact GraphMinor.GM10.theorem_2_9_proof h𝒯 h₁ hsep₂ hord₂ h

end

section

open Graph SimpleGraph Hypergraph Relation

/-- **Graph Minors X, (2.10)** (pages 158–159):
"Let $\mathscr{T}$ be a tangle of order $\ge 3$ in a graph $G$, and let $(A, B)\in
\mathscr{T}$. Then $B$ has a circuit." -/
theorem theorem_2_10 {α β : Type*}
    {G : Hypergraph α β} {θ : ℕ}
    {𝒯 : Set (Hypergraph α β × Hypergraph α β)} (h𝒯 : IsTangle G θ 𝒯) (hθ : 3 ≤ θ)
    {A₀ B₀ : Hypergraph α β} (hAB₀ : (A₀, B₀) ∈ 𝒯) :
    HasCircuit B₀ := by exact GraphMinor.GM10.theorem_2_10_proof h𝒯 hθ hAB₀

end

/-! ## Section 3. A Lemma About Submodular Functions -/

section

open SimpleGraph

/-- **Graph Minors X, (3.1)** (page 160):
"If there is a bias extending $\mathscr{A}$ then there is no tree-labelling over $\mathscr{A}$." -/
theorem theorem_3_1 {β : Type*} {ι : Type*}
    [Fintype ι] {E : Set β} {κ : Set β → ℤ} {𝒜 ℬ : Set (Set β)}
    {T : SimpleGraph ι} {α : ι → Sym2 ι → Set β}
    (hℬ_ext : BiasExtends E κ 𝒜 ℬ) (hα : IsTreeLabelling E κ 𝒜 T α) : False := by exact GraphMinor.GM10.theorem_3_1_proof hℬ_ext hα

end

section

open SimpleGraph
open Classical

/-- **Graph Minors X, (3.2)** (page 160):
"If there is a tree-labelling over $\mathscr{A}$ then there is an exact tree-labelling over
$\mathscr{A}$, using the same tree." -/
theorem theorem_3_2 {β : Type*} {ι : Type*}
    [Fintype ι] {E : Set β} {κ : Set β → ℤ} {𝒜 : Set (Set β)}
    {T : SimpleGraph ι} {α₀ : ι → Sym2 ι → Set β}
    (hE : E.Finite) (hκ : IsConnectivityFunction E κ) (hα₀ : IsTreeLabelling E κ 𝒜 T α₀) :
    ∃ α, IsExactTreeLabelling E κ 𝒜 T α := by exact GraphMinor.GM10.theorem_3_2_proof hE hκ hα₀

end

section

open SimpleGraph
open Classical

/-- **Graph Minors X, (3.3)** (page 161):
"Let $(T, \alpha)$ be an exact tree-labelling over $\mathscr{A}$, and let $(u, f)$ be an
incidence in $T$. Let $T_0$ be the component of $T \setminus f$ which contains $u$. Then, as
$(v, e)$ ranges over all incidences of $T$ such that $v$ is a leaf of $T$ and $v \in
V(T_0)$, the sets $E - \alpha(v, e)$ are mutually disjoint and have union $E - \alpha(u,
f)$." -/
theorem theorem_3_3 {β : Type*} {ι : Type*}
    [Fintype ι] {E : Set β} {κ : Set β → ℤ} {𝒜 : Set (Set β)}
    {T : SimpleGraph ι} {α : ι → Sym2 ι → Set β}
    (hα : IsExactTreeLabelling E κ 𝒜 T α) {u : ι} {f : Sym2 ι} (huf : IsTreeIncidence T u f) :
    (leafIncidencesIn T u f).PairwiseDisjoint (fun p ↦ E \ α p.1 p.2) ∧
    (⋃ p ∈ leafIncidencesIn T u f, (E \ α p.1 p.2)) = E \ α u f := by exact GraphMinor.GM10.theorem_3_3_proof hα huf

end

section

open SimpleGraph

/-- **Graph Minors X, (3.4)** (page 162):
"If there is no bias extending $\mathscr{A}$ then there is an exact tree-labelling over $\mathscr{A}$."

**(3.4)** Let `κ` be a connectivity function on a finite set `E`, and let `𝒜` be a set of
efficient subsets of `E`. If there is no bias extending `𝒜`, then there is an exact
tree-labelling over `𝒜`
(Graph Minors X, Section 3, (3.4), page 162). -/
theorem theorem_3_4 {β : Type*}
    {E : Set β} {κ : Set β → ℤ} {𝒜 : Set (Set β)}
    (hE : E.Finite) (hκ : IsConnectivityFunction E κ)
    (h𝒜 : ∀ A ∈ 𝒜, IsEfficient E κ A)
    (hno_bias : ¬ ∃ ℬ, BiasExtends E κ 𝒜 ℬ) :
    ∃ (ι : Type) (_ : Fintype ι) (T : SimpleGraph ι) (α : ι → Sym2 ι → Set β),
      IsExactTreeLabelling E κ 𝒜 T α := by exact GraphMinor.GM10.theorem_3_4_proof hE hκ h𝒜 hno_bias

end

section

open SimpleGraph

/-- **Graph Minors X, (3.5)** (page 163):
"The following are equivalent:
(i) there is no bias extending $\mathscr{A}$
(ii) there is a tree-labelling over $\mathscr{A}$
(iii) there is an exact tree-labelling over $\mathscr{A}$."

**(3.5)** Let `κ` be a connectivity function on a finite set `E`, and let `𝒜` be a set of
efficient subsets of `E`. Then the following are equivalent:
(i) there is no bias extending `𝒜`;
(ii) there is a tree-labelling over `𝒜`;
(iii) there is an exact tree-labelling over `𝒜`
(Graph Minors X, Section 3, (3.5), page 163). -/
theorem theorem_3_5 {β : Type*}
    {E : Set β} {κ : Set β → ℤ} {𝒜 : Set (Set β)}
    (hE : E.Finite) (hκ : IsConnectivityFunction E κ)
    (h𝒜 : ∀ A ∈ 𝒜, IsEfficient E κ A) :
    ((¬ ∃ ℬ, BiasExtends E κ 𝒜 ℬ) ↔
      ∃ (ι : Type) (_ : Fintype ι) (T : SimpleGraph ι) (α : ι → Sym2 ι → Set β),
        IsTreeLabelling E κ 𝒜 T α) ∧
    ((∃ (ι : Type) (_ : Fintype ι) (T : SimpleGraph ι) (α : ι → Sym2 ι → Set β),
        IsTreeLabelling E κ 𝒜 T α) ↔
      ∃ (ι : Type) (_ : Fintype ι) (T : SimpleGraph ι) (α : ι → Sym2 ι → Set β),
        IsExactTreeLabelling E κ 𝒜 T α) := by exact GraphMinor.GM10.theorem_3_5_proof hE hκ h𝒜

end

section

open SimpleGraph

/-- **Graph Minors X, (3.6)** (page 163):
"If there is an exact tree-labelling over $\mathscr{A}$, then either $E = \emptyset$, or $E \in \mathscr{A}$, or there is an exact tree-labelling $(T, \alpha)$ over $\mathscr{A}$ such that for each leaf $v$ and incident edge $e$, $\alpha(v, e) \ne E$."

**(3.6)** If there is an exact tree-labelling over `𝒜`, then either `E = ∅`, or `E ∈ 𝒜`, or
there is an exact tree-labelling `(T, α)` over `𝒜` such that `α(v, e) ≠ E` for each leaf `v` and
incident edge `e`
(Graph Minors X, Section 3, (3.6), pages 163–164). -/
theorem theorem_3_6 {β : Type*} {ι : Type*}
    [Fintype ι] {E : Set β} {κ : Set β → ℤ} {𝒜 : Set (Set β)}
    (_h𝒜 : ∀ A ∈ 𝒜, IsEfficient E κ A)
    {T : SimpleGraph ι} {α : ι → Sym2 ι → Set β}
    (hα : IsExactTreeLabelling E κ 𝒜 T α) :
    E = ∅ ∨ E ∈ 𝒜 ∨
      ∃ (ι' : Type) (_ : Fintype ι') (T' : SimpleGraph ι') (α' : ι' → Sym2 ι' → Set β),
        IsExactTreeLabelling E κ 𝒜 T' α' ∧
        ∀ v e, IsTreeIncidence T' v e → IsLeaf T' v → α' v e ≠ E := by exact GraphMinor.GM10.theorem_3_6_proof _h𝒜 hα

end

/-! ## Section 4. BRANCH-WIDTH -/

section

open Graph SimpleGraph Hypergraph

universe u v

/-- **Graph Minors X, (4.1)** (page 164):
"(4.1) *If $H$ is a minor of a graph $G$, then $\beta(H) \le \beta(G)$.*" -/
theorem theorem_4_1 {α : Type u} {β : Type v}
    {G : Graph α β} {H : Graph (Set α) β}
    (hV : V(G).Finite) (hE : E(G).Finite)
    (hVH : V(H).Finite) (hEH : E(H).Finite)
    (hminor : IsMinor H G) :
    branchWidth (Hypergraph.ofGraph H hVH hEH) ≤ branchWidth (Hypergraph.ofGraph G hV hE) := by exact GraphMinor.GM10.theorem_4_1_proof hV hE hVH hEH hminor

end

section

open Graph Hypergraph SimpleGraph Classical

universe u v

/-- Graph Minors X, (4.2), page 165:
"(4.2) *A graph $G$ has branch-width*
(i) *$0$ if and only if every component of $G$ has $\le 1$ edge*
(ii) *$\le 1$ if and only if every component of $G$ has $\le 1$ vertex of valency $\ge 2$*
(iii) *$\le 2$ if and only if $G$ has no $K_4$ minor.*"
The printed proof of (ii) misses a case with loops. The leaf-cut argument of
`branchWidth_le_one_iff_components_le_one_deg_ge_two` covers it (see the correction to the proof of
(4.2)(ii) in `corrections/GM10.md`).

The low-width argument covers loops directly. For (iii) the paper cites Dirac's theorem that a
non-null simple graph with no $K_4$ minor has a vertex of valency at most 2. The Lean proves this
theorem by another argument. -/
theorem theorem_4_2 {α : Type u} {β : Type v} (G : Graph α β)
    (hV : V(G).Finite) (hE : E(G).Finite) :
    (branchWidth (Hypergraph.ofGraph G hV hE) = 0 ↔
      ∀ C, IsConnectedComponent (Hypergraph.ofGraph G hV hE) C → C.edgeSet.ncard ≤ 1) ∧
    (branchWidth (Hypergraph.ofGraph G hV hE) ≤ 1 ↔
      ∀ C, IsConnectedComponent (Hypergraph.ofGraph G hV hE) C →
        {x ∈ C.vertexSet | 2 ≤ {e ∈ (Hypergraph.ofGraph G hV hE).edgeSet |
          (Hypergraph.ofGraph G hV hE).Inc e x}.ncard}.ncard ≤ 1) ∧
    (branchWidth (Hypergraph.ofGraph G hV hE) ≤ 2 ↔
      ¬ IsIsoMinor (completeGraphGraph 4) G) := by exact GraphMinor.GM10.theorem_4_2_proof G hV hE

end

section

open SimpleGraph Hypergraph

/-- **Graph Minors X, (4.3)** (page 165):
"(4.3) *For any hypergraph $G$, $\max(\beta(G), \gamma(G)) = \theta(G)$ unless $\gamma(G) = 0$ and
$V(G) \ne \emptyset$.*" -/
theorem theorem_4_3 {α β : Type*}
    (G : Hypergraph α β)
    (h : ¬ (maxEdgeSize G = 0 ∧ G.vertexSet.Nonempty)) :
    max (branchWidth G) (maxEdgeSize G) = tangleNumber G := by exact GraphMinor.GM10.theorem_4_3_proof G h

end

section

open SimpleGraph Hypergraph

/-- **Graph Minors X, (4.4)** (page 166):
"For $n \ge 0$, $K_n$ has tangle number $\lceil(2/3) n\rceil$, and for $n \ge 3$, it has
branch-width $\lceil(2/3) n\rceil$." -/
theorem theorem_4_4 (n : ℕ) :
    tangleNumber (completeGraph n) = (2 * n + 2) / 3 ∧
      (3 ≤ n → branchWidth (completeGraph n) = (2 * n + 2) / 3) := by exact GraphMinor.GM10.theorem_4_4_proof n

end

section

open SimpleGraph Hypergraph

/-- **Graph Minors X, (4.5)** (page 167):
"Let $\theta \ge 2$, and let $\mathscr{T}$ be a set of separations of a hypergraph $G$, each
of order $< \theta$. Suppose that the first tangle axiom holds, and* (i) *if $(A_1, B_1),
(A_2, B_2) \in \mathscr{T}$ then $B_1 \not\subseteq A_2$* (ii) *there do not exist
subhypergraphs $A_1, A_2, A_3 \subseteq G$, mutually edge-disjoint, with $A_1 \cup A_2 \cup
A_3 = G$ and with $(A_1, A_2 \cup A_3)$, $(A_2, A_3 \cup A_1)$, $(A_3, A_1 \cup A_2)$ all in
$\mathscr{T}$.* *Then the second tangle axiom holds." -/
theorem theorem_4_5 {α β : Type*}
    {G : Hypergraph α β} {θ : ℕ} (_hθ : 2 ≤ θ)
    {𝒯 : Set (Hypergraph α β × Hypergraph α β)}
    (hsep : ∀ ⦃A B : Hypergraph α β⦄, (A, B) ∈ 𝒯 → G.IsSeparation A B)
    (hord : ∀ ⦃A B : Hypergraph α β⦄, (A, B) ∈ 𝒯 → separationOrder A B < θ)
    (hax1 : TangleAxiom1 G θ 𝒯)
    (hi : ∀ ⦃A₁ B₁ A₂ B₂ : Hypergraph α β⦄, (A₁, B₁) ∈ 𝒯 → (A₂, B₂) ∈ 𝒯 → ¬ B₁ ≤ A₂)
    (hii : ¬ ∃ A₁ A₂ A₃ : Hypergraph α β,
      A₁ ≤ G ∧ A₂ ≤ G ∧ A₃ ≤ G ∧
      Disjoint A₁.edgeSet A₂.edgeSet ∧
      Disjoint A₁.edgeSet A₃.edgeSet ∧
      Disjoint A₂.edgeSet A₃.edgeSet ∧
      A₁ ∪ A₂ ∪ A₃ = G ∧
      (A₁, A₂ ∪ A₃) ∈ 𝒯 ∧ (A₂, A₃ ∪ A₁) ∈ 𝒯 ∧ (A₃, A₁ ∪ A₂) ∈ 𝒯) :
    TangleAxiom2 G 𝒯 := by exact GraphMinor.GM10.theorem_4_5_proof _hθ hsep hord hax1 hi hii

end

/-! ## Section 5. BRANCH-WIDTH AND TREE-WIDTH -/

section

open SimpleGraph Hypergraph

/-- **Graph Minors X, (5.1)** (page 168):
"(5.1) *For any hypergraph $G$, $\max(\beta(G), \gamma(G)) \le \omega(G) + 1 \le
\max(\lfloor(3/2) \beta(G)\rfloor, \gamma(G), 1)$.*" -/
theorem theorem_5_1 {α β : Type*}
    (G : Hypergraph α β) :
    max (branchWidth G) (maxEdgeSize G) ≤ treeWidthPlusOne G ∧
      treeWidthPlusOne G ≤ max (max (3 * branchWidth G / 2) (maxEdgeSize G)) 1 := by exact GraphMinor.GM10.theorem_5_1_proof G

end

section

open SimpleGraph Hypergraph

/-- **Graph Minors X, (5.2)** (page 169):
"For any hypergraph $G$, $\theta(G) \le \omega(G) + 1 \le (3/2) \theta(G)$." -/
theorem theorem_5_2 {α β : Type*}
    (G : Hypergraph α β) :
    tangleNumber G ≤ treeWidthPlusOne G ∧ 2 * treeWidthPlusOne G ≤ 3 * tangleNumber G := by exact GraphMinor.GM10.theorem_5_2_proof G

end

/-! ## Section 6. New Tangles from Old -/

section

open Graph SimpleGraph Hypergraph Relation

/-- **Graph Minors X, (6.1)** (page 170):
"(6.1) *Let $H$ be a minor of a graph $G$, and let $\mathscr{T}'$ be a tangle in $H$ of order
$\theta \ge 2$. Let $\mathscr{T}$ be the set of all separations $(A, B)$ of $G$ of order $< \theta$
such that there exists $(A', B') \in \mathscr{T}'$ with $E(A') = E(A) \cap E(H)$. Then $\mathscr{T}$
is a tangle in $G$ of order $\theta$.*" -/
theorem theorem_6_1 {α β : Type*}
    {G : Graph α β} {H : Graph (Set α) β}
    (hV : V(G).Finite) (hE : E(G).Finite)
    (hVH : V(H).Finite) (hEH : E(H).Finite)
    (hminor : IsMinor H G) {θ : ℕ} (hθ : 2 ≤ θ)
    {𝒯' : Set (Hypergraph (Set α) β × Hypergraph (Set α) β)}
    (h𝒯' : IsTangle (Hypergraph.ofGraph H hVH hEH) θ 𝒯') :
    IsTangle (Hypergraph.ofGraph G hV hE) θ
      (inducedTangle (Hypergraph.ofGraph G hV hE) (Hypergraph.ofGraph H hVH hEH) 𝒯' θ) := by exact GraphMinor.GM10.theorem_6_1_proof hV hE hVH hEH hminor hθ h𝒯'

end

section

open Graph SimpleGraph Hypergraph Relation

/-- **Graph Minors X, (6.2)** (page 171):
"(6.2) *Let $\mathscr{T}$ be a tangle of order $\theta$ in a hypergraph $G$, and let $W \subseteq V(G)$ with $|W| < \theta$. Let $\mathscr{T}'$ be the set of all separations $(A', B')$ of $G/W$ such that there exists $(A, B) \in \mathscr{T}$ with $W \subseteq V(A \cap B)$, $A/W = A'$, and $B/W = B'$. Then $\mathscr{T}'$ is a tangle in $G/W$ of order $\theta - |W|$.*" -/
theorem theorem_6_2 {α β : Type*}
    {G : Hypergraph α β} {θ : ℕ}
    {𝒯 : Set (Hypergraph α β × Hypergraph α β)} (h𝒯 : IsTangle G θ 𝒯)
    {W : Set α} (hW : W ⊆ G.vertexSet) (hW_lt : W.ncard < θ) :
    IsTangle (quotientVertices G W) (θ - W.ncard) (quotientTangle G 𝒯 W) := by exact GraphMinor.GM10.theorem_6_2_proof h𝒯 hW hW_lt

end

section

open Graph SimpleGraph Hypergraph Relation

/-- **Graph Minors X, (6.3)** (page 171):
"(6.3) *Let $\mathscr{T}, \theta, G, W$ be as in (6.2), and let $(A, B)$ be a separation of $G$.
Then $(A/W, B/W) \in \mathscr{T}/W$ if and only if $(A, B) \in \mathscr{T}$ and
$|V(A \cap B) - W| < \theta - |W|$.*" -/
theorem theorem_6_3 {α β : Type*}
    {G : Hypergraph α β} {θ : ℕ}
    {𝒯 : Set (Hypergraph α β × Hypergraph α β)} (h𝒯 : IsTangle G θ 𝒯)
    {W : Set α} (hW : W ⊆ G.vertexSet) (hW_lt : W.ncard < θ)
    {A B : Hypergraph α β} (hsep : G.IsSeparation A B) :
    (quotientVertices A W, quotientVertices B W) ∈ quotientTangle G 𝒯 W ↔
      (A, B) ∈ 𝒯 ∧ ((A ∩ B).vertexSet \ W).ncard < θ - W.ncard := by exact GraphMinor.GM10.theorem_6_3_proof h𝒯 hW hW_lt hsep

end

/-! ## Section 7. A Tangle in a Grid -/

section

open Graph SimpleGraph Hypergraph

/-- **Graph Minors X, (7.1)** (page 171):
"If $X \subseteq E(G)$ and $|\partial(X)| < \theta$ then $X$ includes $E(P_i)$ for some $i$
$(1 \le i \le \theta)$ if and only if $X$ includes $E(Q_j)$ for some $j$ $(1 \le j \le
\theta)$."

The edge boundary consists of vertices of the graph (see the correction on page 171 in
`corrections/GM10.md`). The grid coordinates start at zero, as in `GM01.gridGraph`. -/
theorem theorem_7_1 {θ : ℕ} (hθ : 2 ≤ θ) {X : Set (Sym2 (Fin θ × Fin θ))}
    (_hX : X ⊆ (gridHypergraph θ).edgeSet)
    (hB : (edgeBoundary (gridHypergraph θ) X).ncard < θ) :
    (∃ i : Fin θ, (gridRowPath θ i).edgeSet ⊆ X) ↔
      (∃ j : Fin θ, (gridColPath θ j).edgeSet ⊆ X) := by exact GraphMinor.GM10.theorem_7_1_proof hθ _hX hB

end

section

open Graph SimpleGraph Hypergraph

/-- **Graph Minors X, (7.2)** (Kleitman–Saks lemma, page 172):
"If $G$ is a $\theta$-grid and $X_1, X_2, X_3 \subseteq E(G)$ with $X_1 \cup X_2 \cup X_3 =
E(G)$, then not all of $X_1, X_2, X_3$ are small in $G$."

The edge boundary consists of vertices of the graph (see the correction on page 171 in
`corrections/GM10.md`). The grid coordinates start at zero, as in `GM01.gridGraph`. -/
theorem theorem_7_2 {θ : ℕ} (hθ : 2 ≤ θ)
    {X₁ X₂ X₃ : Set (Sym2 (Fin θ × Fin θ))}
    (hU : X₁ ∪ X₂ ∪ X₃ = (gridHypergraph θ).edgeSet) :
    ¬ (IsSmallEdgeSet θ X₁ ∧ IsSmallEdgeSet θ X₂ ∧ IsSmallEdgeSet θ X₃) := by exact GraphMinor.GM10.theorem_7_2_proof hθ hU

end

section

open Graph SimpleGraph Hypergraph

/-- **Graph Minors X, (7.3)** (page 173):
"Given a $\theta$-grid $G$ with $P_1, \dots, P_\theta, Q_1, \dots, Q_\theta$ as before, let
$\mathscr{T}$ be the set of all separations $(A, B)$ of $G$ of order $<\theta$ such that $E(A)$ is
small.
(7.3) *$\mathscr{T}$ is a tangle in $G$ of order $\theta$.*"

The edge boundary consists of vertices of the graph (see the correction on page 171 in
`corrections/GM10.md`). The grid coordinates start at zero, as in `GM01.gridGraph`. -/
theorem theorem_7_3 {θ : ℕ} (hθ : 2 ≤ θ) :
    IsTangle (gridHypergraph θ) θ (gridTangle θ) := by exact GraphMinor.GM10.theorem_7_3_proof hθ

end

section

open Graph SimpleGraph

universe u v

/-- Graph Minors X, (7.4), page 173:
"For every $\theta \ge 2$ there exists $\phi \ge 0$ such that every graph with tree-width
$\ge \phi$ has a $\theta$-grid minor."
The cited result of Graph Minors V is used with its proof. -/
theorem theorem_7_4 (θ : ℕ) (_hθ : 2 ≤ θ) :
    ∃ φ : ℕ, ∀ {α : Type u} {β : Type v} (G : Graph α β)
      (hV : V(G).Finite) (hE : E(G).Finite),
      (φ : ℤ) ≤ treeWidth (Hypergraph.ofGraph G hV hE) →
      IsIsoMinor (GM01.gridGraph θ) G := by exact GraphMinor.GM10.theorem_7_4_proof θ _hθ

end

section

open Hypergraph RST94 Set Graph

universe u v

/-- Graph Minors X, (7.5), page 173:
"For every $\theta \ge 2$ there exists $\phi \ge 0$ such that for every graph
$G$ and every tangle $\mathscr{T}$ in $G$ of order $\ge \phi$, the truncation of
$\mathscr{T}$ to order $\theta$ is the tangle induced by some $\theta$-grid minor of $G$."

The minor is literal and is explicitly isomorphic to the grid. The two maps
identify its canonical tangle with the image of `gridTangle`. The cited grid
result is used with its proof, so no cited hypothesis remains. -/
theorem theorem_7_5 (g : ℕ) (hg : 2 ≤ g) :
    ∃ φ : ℕ, ∀ {α : Type u} {β : Type v} (G : Graph α β)
      (hV : V(G).Finite) (hE : E(G).Finite)
      (θ : ℕ) (T : Set (Hypergraph α β × Hypergraph α β)),
      IsTangle (Hypergraph.ofGraph G hV hE) θ T → φ ≤ θ →
      ∃ (H : Graph (Set α) β) (hVH : V(H).Finite) (hEH : E(H).Finite)
        (fV : Fin g × Fin g → Set α) (fE : Sym2 (Fin g × Fin g) → β),
        IsMinor H G ∧ Nonempty (Iso (GM01.gridGraph g) H) ∧
        InjOn fV (gridHypergraph g).vertexSet ∧
        InjOn fE (gridHypergraph g).edgeSet ∧
        Hypergraph.ofGraph H hVH hEH = GM21.isoImage fV fE (gridHypergraph g) ∧
        IsTangle (Hypergraph.ofGraph H hVH hEH) g
          (GM21.isoImageTangle fV fE (gridTangle g)) ∧
        truncation T g = inducedTangle (Hypergraph.ofGraph G hV hE)
          (Hypergraph.ofGraph H hVH hEH)
          (GM21.isoImageTangle fV fE (gridTangle g)) g := by exact GraphMinor.GM10.theorem_7_5_proof g hg

end

/-! ## Section 8. Robust and Titanic Separations -/

section

open Hypergraph

universe u v

/-- **Graph Minors X, (8.1)** (page 174):
"Let* $(A, B)$ *be a robust separation of* $G$, *and let* $(C, D)$ *be a separation of* $G$.
*Then one of* $(A \cup C, B \cap D)$, $(A \cup D, B \cap C)$ *has order at most that of*
$(C, D)$." -/
theorem theorem_8_1 {α : Type u} {β : Type v}
    {G A B C D : Hypergraph α β}
    (hAB : IsRobust G A B) (hCD : G.IsSeparation C D) :
    separationOrder (A ∪ C) (B ∩ D) ≤ separationOrder C D ∨
      separationOrder (A ∪ D) (B ∩ C) ≤ separationOrder C D := by exact GraphMinor.GM10.theorem_8_1_proof hAB hCD

end

section

open Hypergraph

universe u v

/-- **Graph Minors X, (8.2)** (page 174):
"Every titanic separation is robust." -/
theorem theorem_8_2 {α : Type u} {β : Type v}
    {G A B : Hypergraph α β} (h : IsTitanic G A B) :
    IsRobust G A B := by exact GraphMinor.GM10.theorem_8_2_proof h

end

section

open Hypergraph

universe u v

/-- **Graph Minors X, (8.3)** (page 175):
"Let* $(C, D)$ *be a separation of a hypergraph* $G$, *and let* $(C', D)$ *be a titanic
separation of a hypergraph* $G'$, *with* $V(C \cap D) = V(C' \cap D)$. *Let* $\mathscr{T}$
*be a tangle in* $G$ *of order* $\theta \ge 2$ *with* $(C, D) \in \mathscr{T}$. *Let*
$\mathscr{T}'$ *be the set of all separations* $(A', B')$ *of* $G'$ *of order* $<\theta$
*such that there exists* $(A, B) \in \mathscr{T}$ *with* $E(A \cap D) = E(A' \cap D)$.
*Then* $\mathscr{T}'$ *is a tangle in* $G'$ *of order* $\theta$." -/
theorem theorem_8_3 {α : Type u} {β : Type v}
    {G G' C C' D : Hypergraph α β} {θ : ℕ}
    {𝒯 : Set (Hypergraph α β × Hypergraph α β)}
    (hCD : G.IsSeparation C D) (hC'D : IsTitanic G' C' D)
    (hV_inter : (C ∩ D).vertexSet = (C' ∩ D).vertexSet)
    (hθ : 2 ≤ θ) (h𝒯 : IsTangle G θ 𝒯) (hCD_mem : (C, D) ∈ 𝒯) :
    IsTangle G' θ (titanicTransferredTangle G' D 𝒯 θ) := by exact GraphMinor.GM10.theorem_8_3_proof hCD hC'D hV_inter hθ h𝒯 hCD_mem

end

section

open Hypergraph

universe u v

/-- **Graph Minors X, (8.4)** (page 176):
"Let* $\mathscr{T}$ *be a tangle of order* $\theta \ge 2$ *in a hypergraph* $G$, *and let* $e
\in E(G)$ *with at most one end. Let* $\mathscr{T}'$ *be the set of all separations* $(A',
B')$ *of* $G \setminus e$ *of order* $<\theta$ *such that there exists* $(A, B) \in
\mathscr{T}$ *with* $E(A \cap (G \setminus e)) = E(A')$. *Then* $\mathscr{T}'$ *is a tangle
in* $G \setminus e$ *of order* $\theta$." -/
theorem theorem_8_4 {α : Type u} {β : Type v}
    {G : Hypergraph α β} {θ : ℕ}
    {𝒯 : Set (Hypergraph α β × Hypergraph α β)}
    (h𝒯 : IsTangle G θ 𝒯) (hθ : 2 ≤ θ)
    {e : β} (he : e ∈ G.edgeSet) (hsize : (G.ends e).ncard ≤ 1) :
    IsTangle (G.deleteEdges {e}) θ (deleteEdgeTangle G e 𝒯 θ) := by exact GraphMinor.GM10.theorem_8_4_proof h𝒯 hθ he hsize

end

section

open Hypergraph

universe u v

/-- **Graph Minors X, (8.5)** (page 177):
"Let $\mathscr{T}$ be a tangle in a graph $G$ of order $\theta \ge 1$. Let $W \subseteq V(G)$
with $|W| < \theta$. Let $\mathscr{T}'$ be the set of all separations $(A', B')$ of $G
\setminus W$ of order $< \theta - |W|$ such that there exists $(A, B) \in \mathscr{T}$ with
$W \subseteq V(A \cap B)$ and $A \setminus W = A'$, $B \setminus W = B'$. Then
$\mathscr{T}'$ is a tangle in $G \setminus W$ of order $\theta - |W|$." -/
theorem theorem_8_5 {α : Type u} {β : Type v}
    {G : Hypergraph α β} (hG : G.IsGraph) {θ : ℕ}
    {𝒯 : Set (Hypergraph α β × Hypergraph α β)} (h𝒯 : IsTangle G θ 𝒯)
    {W : Set α} (hW : W ⊆ G.vertexSet) (hW_lt : W.ncard < θ) :
    IsTangle (G.deleteVertices W) (θ - W.ncard) (deleteVerticesTangle G W 𝒯 θ) := by exact GraphMinor.GM10.theorem_8_5_proof hG h𝒯 hW hW_lt

end

/-! ## Section 9. Laminar Separations -/

section

open SimpleGraph Hypergraph
open Classical

/-- **Graph Minors X, (9.1)** (page 177):
"If $(T, \tau)$ is a tree-decomposition of $G$, then the set of all separations of $G$ made by edges of $T$ is laminar. Conversely, if $\{(A_i, B_i) : 1 \le i \le k\}$ is a laminar set of separations of $G$, there is a tree-decomposition $(T, \tau)$ of $G$ such that
(i) for $1 \le i \le k$, $(A_i, B_i)$ is made by a unique edge of $T$
(ii) for each edge $e$ of $T$, at least one of the two separations made by $e$ equals $(A_i, B_i)$ for some $i$ ($1 \le i \le k$)."

**Graph Minors X, (9.1)** (page 177):
Characterization of laminar sets of separations of a hypergraph `G` as those made by edges of a
tree-decomposition of `G`. -/
theorem theorem_9_1 {α β : Type*}
    {G : Hypergraph α β}
    {𝒮 : Set (Hypergraph α β × Hypergraph α β)}
    (hsep : ∀ p ∈ 𝒮, G.IsSeparation p.1 p.2) :
    IsLaminar 𝒮 ↔
      ∃ (ι : Type) (_ : Fintype ι) (T : SimpleGraph ι) (τ : ι → Hypergraph α β),
        IsTreeDecomposition G T τ ∧
        (∀ p ∈ 𝒮, ∃! e : Sym2 ι, e ∈ T.edgeSet ∧ MakesSeparation T τ e p.1 p.2) ∧
        (∀ e ∈ T.edgeSet, ∃ p ∈ 𝒮, MakesSeparation T τ e p.1 p.2) ∧
        separationsMadeBy T τ = 𝒮 ∪ Prod.swap '' 𝒮 := by exact GraphMinor.GM10.theorem_9_1_proof hsep

end

section

open SimpleGraph Hypergraph
open Classical

/-- **Graph Minors X, (9.2)** (page 178):
"In every hypergraph there is a tie-breaker." -/
theorem theorem_9_2 {α β : Type*}
    (G : Hypergraph α β) :
    ∃ (lam : Hypergraph α β × Hypergraph α β → Lex (ℕ × Lex (ℕ × ℕ))),
      IsTieBreaker G lam := by exact GraphMinor.GM10.theorem_9_2_proof G

end

section

open SimpleGraph Hypergraph
open Classical

/-- **Graph Minors X, (9.3)** (page 179):
"Let $\lambda$ be a tie-breaker in a hypergraph $G$, and let $(A, B)$, $(C, D)$ be
separations of $G$. Then either* (i) *$(A \cup C, B \cap D)$ has smaller $\lambda$-order
than $(A, B)$, or* (ii) *$(A \cap C, B \cup D)$ has smaller $\lambda$-order than $(C, D)$,
or* (iii) *$C \subseteq A$ and $B \subseteq D$, or* (iv) *$B = C = G$ and $A = D$ and $E(A)
= \emptyset$." -/
theorem theorem_9_3 {α β : Type*}
    {Λ : Type*} [LinearOrder Λ] {G : Hypergraph α β}
    {lam : Hypergraph α β × Hypergraph α β → Λ} (hTB : IsTieBreaker G lam)
    {A B C D : Hypergraph α β} (hAB : G.IsSeparation A B) (hCD : G.IsSeparation C D) :
    HasSmallerLambdaOrder lam (A ∪ C) (B ∩ D) A B ∨
      HasSmallerLambdaOrder lam (A ∩ C) (B ∪ D) C D ∨
      (C ≤ A ∧ B ≤ D) ∨
      (B = G ∧ C = G ∧ A = D ∧ A.edgeSet = ∅) := by exact GraphMinor.GM10.theorem_9_3_proof hTB hAB hCD

end

section

open SimpleGraph Hypergraph
open Classical

/-- **Graph Minors X, (9.4)** (page 180):
"Let $(A, B)$, $(C, D)$ be doubly $\lambda$-robust separations of $G$. Then $(A, B)$ and $(C,
D)$ do not cross." -/
theorem theorem_9_4 {α β : Type*}
    {Λ : Type*} [LinearOrder Λ] {G : Hypergraph α β}
    {lam : Hypergraph α β × Hypergraph α β → Λ} (hTB : IsTieBreaker G lam)
    {A B C D : Hypergraph α β}
    (hAB : IsDoublyLambdaRobust G lam A B) (hCD : IsDoublyLambdaRobust G lam C D) :
    ¬ SeparationsCross A B C D := by exact GraphMinor.GM10.theorem_9_4_proof hTB hAB hCD

end

/-! ## Section 10. Tangle Tree-Decompositions -/

section

open SimpleGraph Hypergraph

universe u v w

/-- **Graph Minors X, (10.1)** (page 180):
"Either there is a separation of $G$ which distinguishes $\mathscr{T}_1$ from $\mathscr{T}_2$
or $\mathscr{T}_1$, $\mathscr{T}_2$ are indistinguishable and not both." -/
theorem theorem_10_1 {α : Type u} {β : Type v}
    {G : Hypergraph α β} {θ₁ θ₂ : ℕ}
    {𝒯₁ 𝒯₂ : Set (Hypergraph α β × Hypergraph α β)}
    (h𝒯₁ : IsTangle G θ₁ 𝒯₁) (h𝒯₂ : IsTangle G θ₂ 𝒯₂) :
    ((∃ A B : Hypergraph α β, Distinguishes 𝒯₁ 𝒯₂ A B) ∨ AreIndistinguishable 𝒯₁ 𝒯₂) ∧
      ¬ ((∃ A B : Hypergraph α β, Distinguishes 𝒯₁ 𝒯₂ A B) ∧ AreIndistinguishable 𝒯₁ 𝒯₂) := by exact GraphMinor.GM10.theorem_10_1_proof h𝒯₁ h𝒯₂

end

section

open SimpleGraph Hypergraph

universe u v w

/-- **Graph Minors X, (10.2)** (page 181):
"If $\mathscr{T}_1, \mathscr{T}_2$ are distinguishable tangles in $G$, the $(\mathscr{T}_1,
\mathscr{T}_2)$-distinction is doubly $\lambda$-robust." -/
theorem theorem_10_2 {α : Type u} {β : Type v} {Λ : Type w}
    [LinearOrder Λ]
    (G : Hypergraph α β) (lam : Hypergraph α β × Hypergraph α β → Λ)
    (θ₁ θ₂ : ℕ) (𝒯₁ 𝒯₂ : Set (Hypergraph α β × Hypergraph α β))
    (A B : Hypergraph α β)
    (hTB : IsTieBreaker G lam)
    (h𝒯₁ : IsTangle G θ₁ 𝒯₁)
    (h𝒯₂ : IsTangle G θ₂ 𝒯₂)
    (hdist : IsDistinction lam 𝒯₁ 𝒯₂ A B) :
    IsDoublyLambdaRobust G lam A B := by exact GraphMinor.GM10.theorem_10_2_proof G lam θ₁ θ₂ 𝒯₁ 𝒯₂ A B hTB h𝒯₁ h𝒯₂ hdist

end

section

open SimpleGraph Hypergraph

universe u v w

/-- **Graph Minors X, (10.3)** (page 181):
"Let $\mathscr{T}_1, \dots, \mathscr{T}_n$ be mutually distinguishable tangles in a
hypergraph $G$ with $n \ge 1$, and let $\lambda$ be a tie-breaker. Then there is a
tree-decomposition $(T, \tau)$ of $G$, where $V(T) = \{t_1, \dots, t_n\}$, with the
following properties:* (i) *For every $e \in E(T)$ and for $1 \le i \le n$, if $T_1, T_2$
are the components of $T \setminus e$ and $t_i \in V(T_1)$ then* $$ \left( \bigcup_{t \in
V(T_1)} \tau(t), \bigcup_{t \in V(T_2)} \tau(t) \right) \notin \mathscr{T}_i. $$ (ii) *For
all $i \ne j$ with $1 \le i, j \le n$, let $e$ be the edge of the path of $T$ between $t_i$
and $t_j$ making separations of smallest $\lambda$-order; then these separations are the
$(\mathscr{T}_i, \mathscr{T}_j)$- and $(\mathscr{T}_j, \mathscr{T}_i)$-distinctions." -/
theorem theorem_10_3 {α : Type u} {β : Type v} {Λ : Type w}
    [LinearOrder Λ] {n : ℕ}
    (G : Hypergraph α β) (lam : Hypergraph α β × Hypergraph α β → Λ)
    (θ : Fin n → ℕ) (𝒯 : Fin n → Set (Hypergraph α β × Hypergraph α β))
    (hn : 1 ≤ n)
    (hTB : IsTieBreaker G lam)
    (h𝒯 : ∀ i : Fin n, IsTangle G (θ i) (𝒯 i))
    (hdist : ∀ i j : Fin n, i ≠ j → AreDistinguishable (𝒯 i) (𝒯 j)) :
    ∃ (T : SimpleGraph (Fin n)) (τ : Fin n → Hypergraph α β),
      IsStandardTreeDecomposition G lam 𝒯 T τ := by exact GraphMinor.GM10.theorem_10_3_proof G lam θ 𝒯 hn hTB h𝒯 hdist

end

section

open SimpleGraph Hypergraph

universe u v w

/-- **Graph Minors X, (10.4)** (page 184):
"In any hypergraph $G$ there are at most $|V(G)|$ maximal tangles." -/
theorem theorem_10_4 {α : Type u} {β : Type v}
    (G : Hypergraph α β) :
    (maximalTangles G).ncard ≤ G.vertexSet.ncard := by exact GraphMinor.GM10.theorem_10_4_proof G

end

/-! ## Section 11. STRUCTURE RELATIVE TO A TANGLE -/

section

open SimpleGraph Hypergraph

/-- **Graph Minors X, (11.1)** (page 185):
"For any $\theta \ge 1$, let $\mathscr{S}$ be a class of designs which is $\theta$-pervasive
in a hypergraph $G$; then $G$ has a tree-decomposition over $\mathscr{S}^{3\theta - 2} \cup
\mathscr{R}_{4\theta - 3}$." -/
theorem theorem_11_1 {α β : Type*}
    {G : Hypergraph α β} {θ : ℕ} {𝒮 : Set (Design α β)}
    (hθ : 1 ≤ θ) (hperv : IsPervasive G θ 𝒮) :
    ∃ (ι : Type) (_ : Fintype ι) (T : SimpleGraph ι) (τ : ι → Hypergraph α β),
      IsTreeDecompositionOver G
        (enlargementClass 𝒮 (3 * θ - 2) ∪ smallDesignClass (4 * θ - 3)) T τ := by exact GraphMinor.GM10.theorem_11_1_proof hθ hperv

end

section

open SimpleGraph Hypergraph

/-- **Graph Minors X, (11.2)** (page 185):
"Let $\theta \ge 1$, let $\mathscr{S}$ be $\theta$-pervasive in $G$, and let $Z \subseteq V(G)$ with $|Z| = 3\theta - 2$. Then either
(i) there is a separation $(A, B)$ of $G$ of order $< \theta$ with
$$
|(Z \cup V(A)) \cap V(B)|, |(Z \cup V(B)) \cap V(A)| \le 3\theta - 3
$$"

**Graph Minors X, (11.2)** (pages 185–186): -/
theorem theorem_11_2 {α β : Type*}
    {G : Hypergraph α β} {θ : ℕ} {𝒮 : Set (Design α β)} {Z : Set α}
    (hθ : 1 ≤ θ) (hperv : IsPervasive G θ 𝒮)
    (hZ_sub : Z ⊆ G.vertexSet) (hZ_card : Z.ncard = 3 * θ - 2) :
    (∃ A B : Hypergraph α β, G.IsSeparation A B ∧ separationOrder A B < θ ∧
      ((Z ∪ A.vertexSet) ∩ B.vertexSet).ncard ≤ 3 * θ - 3 ∧
      ((Z ∪ B.vertexSet) ∩ A.vertexSet).ncard ≤ 3 * θ - 3) ∨
    (∃ ℒ : Set (Hypergraph α β × Hypergraph α β),
      IsLocation G ℒ ∧ locationDesign G ℒ ∈ 𝒮 ∧
      ∀ p ∈ ℒ, (Z ∩ p.1.vertexSet).ncard ≤ separationOrder p.1 p.2 ∧
        separationOrder p.1 p.2 < θ) := by exact GraphMinor.GM10.theorem_11_2_proof hθ hperv hZ_sub hZ_card

end

section

open SimpleGraph Hypergraph

/-- **Graph Minors X, (11.3)** (page 186):
"Let $\mathscr{S}$ be a class of designs, and let $\theta \ge 1$. Let $G$ be a hypergraph
such that $\mathscr{S}$ is $\theta$-pervasive in $G$, and let $Z \subseteq V(G)$ with $|Z|
\le 3\theta - 2$. Then there is a tree-decomposition $(T, \tau)$ of $G$ over
$\mathscr{S}^{3\theta - 2} \cup \mathscr{R}_{4\theta - 3}$, such that for some $t_0 \in
V(T)$, $Z \subseteq V(\tau(t_0))$ and $\mathscr{S}^{3\theta - 2} \cup \mathscr{R}_{4\theta -
3}$ contains the $Z$-extension of the design of $t_0$ in $(T, \tau)$." -/
theorem theorem_11_3 {α β : Type*}
    {G : Hypergraph α β} {θ : ℕ} {𝒮 : Set (Design α β)} {Z : Set α}
    (hθ : 1 ≤ θ) (hperv : IsPervasive G θ 𝒮)
    (hZ_sub : Z ⊆ G.vertexSet) (hZ_card : Z.ncard ≤ 3 * θ - 2) :
    let 𝒮' := enlargementClass 𝒮 (3 * θ - 2) ∪ smallDesignClass (4 * θ - 3)
    ∃ (ι : Type) (_ : Fintype ι) (T : SimpleGraph ι) (τ : ι → Hypergraph α β) (t₀ : ι),
      IsTreeDecompositionOver G 𝒮' T τ ∧
      Z ⊆ (τ t₀).vertexSet ∧
      designExtension (vertexDesign T τ t₀) Z ∈ 𝒮' := by exact GraphMinor.GM10.theorem_11_3_proof hθ hperv hZ_sub hZ_card

end

/-! ## Section 12. Tangles and Matroids -/

section

open Hypergraph Set Matroid
open scoped Sym2

/-- **Graph Minors X, (12.1)** (pages 188–189):
"Let $\mathscr{T}$ be a tangle in a hypergraph $G$, of order $\theta$. For $X \subseteq
V(G)$, let us define $r(X)$ to be the least order of a separation $(A, B) \in \mathscr{T}$
with $X \subseteq V(A)$, if one exists, and $\theta$ otherwise. (12.1) *$r$ is the rank
function of a matroid on $V(G)$." -/
theorem theorem_12_1 {α β : Type*}
    (G : Hypergraph α β) {θ : ℕ}
    {𝒯 : Set (Hypergraph α β × Hypergraph α β)} (h𝒯 : IsTangle G θ 𝒯) :
    IsMatroidRankOn G.vertexSet (tangleRank 𝒯 θ) := by exact GraphMinor.GM10.theorem_12_1_proof G h𝒯

end

section

open Hypergraph Set Matroid
open scoped Sym2

/-- **Graph Minors X, (12.2)** (page 189):
"The free sets are the independent sets of a matroid on $V(G)$ with rank function $r$ as in
(12.1)." -/
theorem theorem_12_2 {α β : Type*}
    (G : Hypergraph α β) {θ : ℕ}
    {𝒯 : Set (Hypergraph α β × Hypergraph α β)} (h𝒯 : IsTangle G θ 𝒯) :
    ∃ M : Matroid α, M.E = G.vertexSet ∧
      (∀ I : Set α, M.Indep I ↔ IsFreeSet G 𝒯 θ I) ∧
      (∀ X : Set α, X ⊆ G.vertexSet → M.eRk X = tangleRank 𝒯 θ X) := by exact GraphMinor.GM10.theorem_12_2_proof G h𝒯

end

end GraphMinor.GM10
