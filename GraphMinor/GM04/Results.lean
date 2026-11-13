module

public import GraphMinor.GM04.Axioms
public import GraphMinor.GM04.Cited
public import GraphMinor.GM04.Decomposition.Contraction
public import GraphMinor.GM04.Decomposition.Linked
public import GraphMinor.GM04.Decomposition.TreeWidth
public import GraphMinor.GM04.HigmanProof
public import GraphMinor.GM04.Main
public import GraphMinor.GM04.NumberedDecomposition
public import GraphMinor.GM04.Painting
public import GraphMinor.GM04.Patchwork.Defs
public import GraphMinor.GM04.Patchwork.Expansion
public import GraphMinor.GM04.Patchwork.Main
public import GraphMinor.GM04.Patchwork.Menger
public import GraphMinor.GM04.Patchwork.Stars
public import GraphMinor.GM04.TopologicalContainment
public import GraphMinor.GM04.TreeLemma.Basic
public import GraphMinor.GM04.TreeLemma.Lemma21
public import GraphMinor.GM04.TreeLemma.Lemma22
public import GraphMinor.GM06.Section3Dual
public import GraphMinor.Menger.Basic
public import GraphMinor.Minor.Basic
public import GraphMinor.Planar.Defs
public import GraphMinor.Statement
public import GraphMinor.Thomas.Translate
import GraphMinor.GM04.Decomposition.Rotund
import GraphMinor.GM04.KruskalProved
import GraphMinor.GM04.MaderProved
import GraphMinor.GM04.NumberedPatchwork
import GraphMinor.GM04.PaintingTheorem
import GraphMinor.GM04.PlanarExcluded
import GraphMinor.GM04.Wagner

/-!
# Graph Minors IV. Tree-width and well-quasi-ordering

N. Robertson and P. D. Seymour, J. Combin. Theory Ser. B 48 (1990) 227–254.

This file lists every numbered result of the paper in order. The proofs are in the other
files of this folder and, for algorithms, in `GraphMinor/Compute/`. Where a printed statement
or proof has an error, the docstring says so and refers to `corrections/GM04.md`.
-/

public section

namespace GraphMinor.GM04

/-! ## Section 1. INTRODUCTION -/

section

open Graph

/-- Graph Minors IV, (1.1), page 228: "If $G_1, G_2, \dots$ is any countable sequence of graphs then there exist $j > i \ge 1$ such that $G_i$ is isomorphic to a minor of $G_j$."
The proof is the graph minor theorem of Graph Minors XX. -/
theorem theorem_1_1 {α β : Type*} (G : ℕ → Graph α β)
    (hV : ∀ n, V(G n).Finite) (hE : ∀ n, E(G n).Finite) :
    ∃ i j, i < j ∧ IsIsoMinor (G i) (G j) := by exact GraphMinor.GM04.theorem_1_1_proof G hV hE

end

section

open Graph

universe u v

/-- Graph Minors IV, (1.2), page 229:
"The class of all trees is well-quasi-ordered by topological containment."
The cited tree theorem is supplied by `Kruskal.kruskal_tree`.

The paper cites this theorem. We prove it by the minimal bad sequence argument of Nash-Williams
(Proc. Cambridge Philos. Soc. 59 (1963), Theorem 1). -/
theorem theorem_1_2 {α : Type u} {β : Type v} (G : ℕ → Graph α β)
    (hV : ∀ n, V(G n).Finite) (hE : ∀ n, E(G n).Finite)
    (hT : ∀ n, IsUndirectedTree (G n)) :
    ∃ i j, i < j ∧ IsTopologicalMinor (G i) (G j) := by exact GraphMinor.GM04.theorem_1_2_proved G hV hE hT

end

section

open Graph

universe u v

/-- Graph Minors IV, (1.3), page 229:
"For any integer $k \ge 0$, the class of all graphs without $k$ vertex-disjoint circuits is well-quasi-ordered by topological containment."
The external statement is supplied by `Mader.mader_circuit`.

The paper cites this theorem of Mader. We prove it from V (8.1), which gives a bounded set of
vertices meeting every circuit, and from the labelled form of the tree theorem. -/
theorem theorem_1_3 (k : ℕ) {α : Type u} {β : Type v}
    (G : ℕ → Graph α β) (hV : ∀ i, V(G i).Finite) (hE : ∀ i, E(G i).Finite)
    (hC : ∀ i, ¬ HasDisjointCircuits (G i) k) :
    ∃ i j, i < j ∧ IsTopologicalMinor (G i) (G j) := by exact GraphMinor.GM04.theorem_1_3_proved k G hV hE hC

end

section

open Graph

universe u v u' v'

/-- Graph Minors IV, (1.4), page 229:
"For any planar graph $H$, the class of all graphs with no minor isomorphic to $H$ is well-quasi-ordered by minors."
The proof is the paper's: the graphs with no `H` minor have bounded tree-width by
Graph Minors V, (1.5), so (1.5) applies. -/
theorem theorem_1_4 {α' : Type u'} {β' : Type v'} (H : Graph α' β') (hH : IsPlanar H)
    {α : Type u} {β : Type v} (G : ℕ → Graph α β)
    (hV : ∀ n, V(G n).Finite) (hE : ∀ n, E(G n).Finite)
    (hexcl : ∀ n, ¬ IsIsoMinor H (G n)) :
    ∃ i j, i < j ∧ IsIsoMinor (G i) (G j) := by exact GraphMinor.GM04.theorem_1_4_proof H hH G hV hE hexcl

end

section

open Graph

universe u v

/-- Graph Minors IV, (1.5) (page 228): "For any integer $k$ the class of all graphs with tree-width $\le k$ is well-quasi-ordered by
minors." In the form of `theorem_1_5`: every sequence
of finite graphs of tree-width `≤ k` has `i < j` with `G i` isomorphic to a minor of `G j`. -/
theorem theorem_1_5 {α : Type u} {β : Type v} (k : ℕ) (G : ℕ → Graph α β)
    (hV : ∀ n, V(G n).Finite) (hE : ∀ n, E(G n).Finite)
    (htw : ∀ n, TreeWidthLE (Hypergraph.ofGraph (G n) (hV n) (hE n)).toRooted k) :
    ∃ i j, i < j ∧ IsIsoMinor (G i) (G j) := by exact GraphMinor.GM04.theorem_1_5_proved k G hV hE htw

end

/-! ## Section 2. A Lemma about Trees -/

section

open Classical

/-- **Graph Minors IV, (2.1)** (page 230):
"Let $T_1, T_2, \dots$ be a countable sequence of disjoint trees. Let $M$ be an infinite graph with $V(M) = V(T_1 \cup T_2 \cup \dots)$, such that for $i' > i \ge 1$, if $u \in V(T_i)$ is $M$-adjacent to $w \in V(T_{i'})$ and $v \in V(T_{i'}) - \{o(T_{i'})\}$ lies on the path of $T_{i'}$ from $o(T_{i'})$ to $w$ then $u$ is $M$-adjacent to $v$. Let $\{o(T_1), o(T_2), \dots\}$ be $M$-stable. Then there is an infinite $M$-stable set $X \subseteq V(M)$ such that $|X \cap V(T_i)| \le 1$ for each $i \ge 1$ and such that the set of heads of all edges of $T_1 \cup T_2 \cup \dots$ with tails in $X$ is $M$-rich."

Graph Minors IV, (2.1) (page 230). Let `T₁, T₂, …` be a countable sequence of disjoint trees,
and `M` be a graph on their vertices such that whenever `i < i'`, `u ∈ V(Tᵢ)` is `M`-adjacent to
`w ∈ V(T_{i'})`, and `v ∈ V(T_{i'}) - {o(T_{i'})}` lies on the path of `T_{i'}` from `o(T_{i'})`
to `w`, `u` is `M`-adjacent to `v`. If `{o(T₁), o(T₂), …}` is `M`-stable, then there is an infinite
`M`-stable set `X ⊆ ⋃ᵢ V(Tᵢ)` meeting each `V(Tᵢ)` in at most one vertex such that the set of heads
of all edges of `T₁ ∪ T₂ ∪ ⋯` with tails in `X` is `M`-rich. -/
theorem theorem_2_1 {ι : Type*}
    (T : ℕ → RootedTree ι) (M : SimpleGraph ι)
    (hdisj : Pairwise (fun i j ↦ Disjoint (T i).verts (T j).verts))
    (hM : ∀ i i', i < i' → ∀ u ∈ (T i).verts, ∀ w ∈ (T i').verts, ∀ v,
      M.Adj u w → v ≠ (T i').root → (T i').Reaches v w → M.Adj u v)
    (hroot : M.IsIndepSet (Set.range fun i ↦ (T i).root)) :
    ∃ X : Set ι, X.Infinite ∧ M.IsIndepSet X ∧ X ⊆ ⋃ i, ((T i).verts : Set ι) ∧
      (∀ i, (X ∩ (T i).verts).Subsingleton) ∧
      IsRich M {v | ∃ i, v ∈ (T i).edges ∧ (T i).parent v ∈ X} := by exact GraphMinor.GM04.lemma_2_1 T M hdisj hM hroot

end

section



/-- **Graph Minors IV, (2.2)** (page 232):
"Let $T_1, T_2, \dots$ be a countable sequence of disjoint trees, let $n \ge 0$ be an integer, and for each $i \ge 1$ let $\phi_i: E(T_i) \to \{0, 1, \dots, n\}$ be some function. Let $M$ be an infinite graph with $V(M) = V(T_1 \cup T_2 \cup \dots)$ such that for $i' > i \ge 1$, if $u \in V(T_i)$ is $M$-adjacent to $w \in V(T_{i'})$, and $v \in V(T_{i'})$ precedes $w$ (with respect to $\phi_{i'}$) then $u$ is $M$-adjacent to $v$. Let $\{o(T_1), o(T_2), \dots\}$ be $M$-stable. Then there is an infinite $M$-stable set $X \subseteq V(M)$ such that $|X \cap V(T_i)| \le 1$ for each $i \ge 1$ and such that the set of heads of all edges of $T_1 \cup T_2 \cup \dots$ with tails in $X$ is $M$-rich."

Graph Minors IV, (2.2) (page 232). -/
theorem theorem_2_2 :
  ∀ {ι : Type*} (T : ℕ → RootedTree ι) (n : ℕ) (φ : ℕ → ι → ℕ) (M : SimpleGraph ι),
    Pairwise (fun i j ↦ Disjoint (T i).verts (T j).verts) →
    (∀ i, ∀ f ∈ (T i).edges, φ i f ≤ n) →
    (∀ i i', i < i' → ∀ u ∈ (T i).verts, ∀ w ∈ (T i').verts, ∀ v,
      M.Adj u w → (T i').Precedes (φ i') v w → M.Adj u v) →
    M.IsIndepSet (Set.range fun i ↦ (T i).root) →
    ∃ X : Set ι, X.Infinite ∧ M.IsIndepSet X ∧ X ⊆ ⋃ i, ((T i).verts : Set ι) ∧
      (∀ i, (X ∩ (T i).verts).Subsingleton) ∧
      IsRich M {v | ∃ i, v ∈ (T i).edges ∧ (T i).parent v ∈ X} := by exact GraphMinor.GM04.lemma_2_2

end

/-! ## Section 3. Hypergraphs and Tree-Decompositions -/

section

open _root_.GraphMinor.Hypergraph

universe u v w

/-- **Graph Minors IV, (3.1)** (page 234):
"Let $(T, \tau)$ be a tree-decomposition of some rooted hypergraph $G$. Let $f \in E(T)$ with head $t_1$ and tail $t_2$. Then $(\tau \times T^f, \tau \times T_f)$ is a separation of $G$."

Graph Minors IV, (3.1), page 234: an edge of a tree-decomposition gives a separation. -/
theorem theorem_3_1 {α : Type u} {β : Type v} {ι : Type w}
    {G : RootedHypergraph α β} {T : RootedTree ι} {τ : ι → RootedHypergraph α β}
    (h : IsTreeDecomposition G T τ) {f : ι} (hf : f ∈ T.edges) :
    G.IsSeparation (cross τ (T.subtreeAt f) f) (cross τ (T.rootSide f) T.root) := by exact GraphMinor.GM04.theorem_3_1_proof h hf

end

section

open _root_.GraphMinor.Hypergraph

universe u v w

/-- **Graph Minors IV, (3.2)** (page 234):
"Let $(T, \tau)$ be a tree-decomposition of a rooted hypergraph $G$, and let $F \subseteq E(T)$. Let $S$ be the contraction of $T$ onto $F$, and for each $s \in V(S)$, let $\sigma(s)$ be $\tau \times T_s$ where $T_s$ is the component of $T\setminus F$ with root $s$. Then $(S, \sigma)$ is a tree-decomposition of $G$."

Graph Minors IV, (3.2), page 234: contracting the tree and taking the union of each
component's bags preserves a tree-decomposition. -/
theorem theorem_3_2 {α : Type u} {β : Type v} {ι : Type w}
    {G : RootedHypergraph α β} {T : RootedTree ι} {τ : ι → RootedHypergraph α β}
    (h : IsTreeDecomposition G T τ) {F : Set ι} (hF : F ⊆ T.edges)
    {S : RootedTree ι} (hS : T.IsContraction F S) (σ : ι → RootedHypergraph α β)
    (hσ : ∀ s ∈ S.verts, σ s = cross τ (T.componentAt F s) s) :
    IsTreeDecomposition G S σ := by exact GraphMinor.GM04.theorem_3_2_proof h hF hS σ hσ

end

section

open _root_.GraphMinor.Hypergraph

universe u v w

/-- **Graph Minors IV, (3.3)** (page 235):
"Let $\mathscr{S}$ be good, and let $(T_i, \tau_i)$ ($i = 1, 2, ...$) be a countable sequence of linked tree-decompositions, each branching of which is in $\mathscr{S}$. Then there exist $i' > i \ge 1$ such that $\tau_i \times T_i$ is simulated in $\tau_{i'} \times T_{i'}$."

Graph Minors IV, (3.3), page 235, using the proved tree lemma (2.2). -/
theorem theorem_3_3 {α : Type u} {β : Type v} {ι : Type w}
    {R : Set (RootedHypergraph α β)}
    {sim : RootedHypergraph α β → RootedHypergraph α β → Prop}
    (hA1 : Axiom1 R) (hA2 : Axiom2 R sim)
    (𝒮 : Set (RootedTree ι × (ι → RootedHypergraph α β))) (h𝒮 : IsGood R sim 𝒮)
    (T : ℕ → RootedTree ι) (τ : ℕ → ι → RootedHypergraph α β)
    (hdec : ∀ i, IsTreeDecomposition (cross (τ i) (T i).verts (T i).root) (T i) (τ i))
    (hlinked : ∀ i, IsLinked sim (T i) (τ i) (T i).edges)
    (hbr : ∀ i, ∀ s ∈ (T i).verts, ((T i).starAt s, branching (T i) (τ i) s) ∈ 𝒮) :
    ∃ i i', i < i' ∧
      sim (cross (τ i) (T i).verts (T i).root) (cross (τ i') (T i').verts (T i').root) := by exact GraphMinor.GM04.theorem_3_3_proved hA1 hA2 𝒮 h𝒮 T τ hdec hlinked hbr

end

/-! ## Section 4. ROTUNDITY -/

section

open _root_.GraphMinor.Hypergraph

universe u

/-- **Graph Minors IV, (4.1)** (page 237):
"Let $(T, \tau)$ be a tree-decomposition with $\tau \times T \in \mathscr{R}$, and let $F \subseteq E(T)$ be rotund in $(T, \tau)$. Then there is a tree-decomposition $(T, \tau')$ of $\tau \times T$, such that $\tau(t)^- = \tau'(t)^-$ for each $t \in V(T)$, and such that $F$ is linked in $(T, \tau')$."

Graph Minors IV, (4.1). -/
theorem theorem_4_1 {α β : Type*} {R : Set (RootedHypergraph α β)} {sim : RootedHypergraph α β → RootedHypergraph α β → Prop}
    {ι : Type*} (hA1 : Axiom1 R) (hA2 : Axiom2 R sim) (hA3 : Axiom3 R sim)
    (T : RootedTree ι) (τ : ι → RootedHypergraph α β)
    (hdec : IsTreeDecomposition (cross τ T.verts T.root) T τ)
    (hR : cross τ T.verts T.root ∈ R) (F : Set ι) (hF : F ⊆ T.edges)
    (hrot : IsRotund T τ F) :
    ∃ τ' : ι → RootedHypergraph α β,
      IsTreeDecomposition (cross τ T.verts T.root) T τ' ∧
      (∀ t ∈ T.verts, (τ' t).toHypergraph = (τ t).toHypergraph) ∧ IsLinked sim T τ' F := by exact GraphMinor.GM04.theorem_4_1_proof hA1 hA2 hA3 T τ hdec hR F hF hrot

end

section

open _root_.GraphMinor.Hypergraph

universe u v w

/-- **Graph Minors IV, (4.2)** (page 238):
"Let $\mathscr{S}$ be good and symmetric, and let $(T_i, \tau_i)$ ($i = 1, 2, ...$) be a countable sequence of rotund tree-decompositions, each branching of which is in $\mathscr{S}$. Then there exist $i' > i \ge 1$ such that $\tau_i \times T_i$ is simulated in $\tau_{i'} \times T_{i'}$."

Graph Minors IV, (4.2), page 238, using the proved tree lemma (2.2). -/
theorem theorem_4_2 {α : Type u} {β : Type v} {ι : Type w}
    {R : Set (RootedHypergraph α β)}
    {sim : RootedHypergraph α β → RootedHypergraph α β → Prop}
    (hA1 : Axiom1 R) (hA2 : Axiom2 R sim) (hA3 : Axiom3 R sim)
    (𝒮 : Set (RootedTree ι × (ι → RootedHypergraph α β))) (h𝒮 : IsGood R sim 𝒮)
    (hsym : IsSymmetric 𝒮) (T : ℕ → RootedTree ι) (τ : ℕ → ι → RootedHypergraph α β)
    (hdec : ∀ i, IsTreeDecomposition (cross (τ i) (T i).verts (T i).root) (T i) (τ i))
    (hrot : ∀ i, IsRotund (T i) (τ i) (T i).edges)
    (hbr : ∀ i, ∀ s ∈ (T i).verts, ((T i).starAt s, branching (T i) (τ i) s) ∈ 𝒮) :
    ∃ i i', i < i' ∧
      sim (cross (τ i) (T i).verts (T i).root) (cross (τ i') (T i').verts (T i').root) := by exact GraphMinor.GM04.theorem_4_2_proved hA1 hA2 hA3 𝒮 h𝒮 hsym T τ hdec hrot hbr

end

/-! ## Section 5. A LEMMA OF THOMAS -/

section

open _root_.GraphMinor.Hypergraph
open _root_.GraphMinor.Hypergraph
open Classical

universe u v w

/-- **Graph Minors IV, (5.1)** (page 238):
"Let $G$ be a graph. If $(G, 0)$ has a tree-decomposition of width $\le w$, then it has a tree-decomposition $(T, \tau)$ of width $\le w$ such that for all distinct $t_1$, $t_2 \in V(T)$ and all $k \ge 0$ either there are $k$ mutually vertex-disjoint paths of $G$ from $V(\tau(t_1))$ to $V(\tau(t_2))$, or some edge of the path of $T$ between $t_1$ and $t_2$ has order $< k$."

Graph Minors IV, (5.1), page 238: Thomas's path-or-small-separator decomposition.

The paper cites this lemma of Thomas without proof. We prove it by the short proof of Bellenbaum
and Diestel (2002). -/
theorem theorem_5_1 :
  ∀ {α β : Type*} (G : Hypergraph α β), G.IsGraph → ∀ w : ℕ, TreeWidthLE G.toRooted w →
    ∃ (T : RootedTree ℕ) (τ : ℕ → RootedHypergraph α β),
      IsTreeDecomposition G.toRooted T τ ∧ WidthLE T τ w ∧
      ∀ t₁ ∈ T.verts, ∀ t₂ ∈ T.verts, t₁ ≠ t₂ → ∀ k : ℕ,
        HasDisjointPaths G.skeleton (τ t₁).vertexSet (τ t₂).vertexSet k ∨
          ∃ f, T.OnPathEdge t₁ t₂ f ∧ edgeOrder T τ f < k := by exact GraphMinor.GM04.theorem_5_1_proof

end

section

open _root_.GraphMinor.Hypergraph

universe u v w

/-- **Graph Minors IV, (5.2)** (page 239):
"Let $G$ be a rooted hypergraph of tree-width $\le w$. Then there is a rotund tree-decomposition of $G$ of width $\le w$."

Graph Minors IV, (5.2), page 239: a rooted hypergraph has a rotund decomposition
of the same width. -/
theorem theorem_5_2 {α : Type u} {β : Type v}
    (G : RootedHypergraph α β) (w : ℕ) (h : TreeWidthLE G w) :
    ∃ (T : RootedTree ℕ) (τ : ℕ → RootedHypergraph α β),
      IsTreeDecomposition G T τ ∧ WidthLE T τ w ∧ IsRotund T τ T.edges := by exact GraphMinor.GM04.theorem_5_2_proved G w h

end

section

open _root_.GraphMinor.Hypergraph
open _root_.GraphMinor.Hypergraph

universe u v w

/-- **Graph Minors IV, (5.3)** (page 240):
"Let $G_i$ ($i = 1, 2, \dots$) be a countable sequence of elements of $\mathscr{R}$, each of tree-width $\le n$. Then there exist $i' > i \ge 1$ such that $G_i$ is simulated in $G_{i'}$."

Graph Minors IV, (5.3), page 240: Axioms 1–4 imply well-quasi-ordering
on each class of bounded tree-width. -/
theorem theorem_5_3 :
  ∀ {α β : Type*} (R : Set (RootedHypergraph α β))
    (sim : RootedHypergraph α β → RootedHypergraph α β → Prop),
    Axiom1 R → Axiom2 R sim → Axiom3 R sim → Axiom4 ℕ R sim →
    ∀ (n : ℕ) (G : ℕ → RootedHypergraph α β), (∀ i, G i ∈ R) → (∀ i, TreeWidthLE (G i) n) →
      ∃ i i', i < i' ∧ sim (G i) (G i') := by exact GraphMinor.GM04.theorem_5_3_proved

end

/-! ## Section 6. PATCHWORKS -/

section

open _root_.GraphMinor.Hypergraph

universe u v w u₁ u₂

/-- **Graph Minors IV, (6.1)** (page 241):
"Let $P = (G, \mu, \Delta, \phi)$ be a robust $\Omega$-patchwork, let $X_1, X_2 \subseteq V(G)$, and let $k \ge 0$ be an integer. The following are equivalent:"

Graph Minors IV, (6.1), page 241, with its tree, path, and finite-set inputs proved. -/
theorem theorem_6_1 {Ω : Type w} {α : Type u} {β : Type v}
    {P : Patchwork Ω α β} (hrob : P.IsRobust)
    {X₁ X₂ : Set α} (hX₁ : X₁ ⊆ P.G.vertexSet) (hX₂ : X₂ ⊆ P.G.vertexSet) (k : ℕ) :
    (Theorem61Cond1 P X₁ X₂ k ↔ Theorem61Cond2 P X₁ X₂ k) ∧
    (Theorem61Cond2 P X₁ X₂ k ↔ Theorem61Cond3 P X₁ X₂ k) := by exact GraphMinor.GM04.theorem_6_1_proved hrob hX₁ hX₂ k

end

/-! ## Section 7. PATCHWORK CONTAINMENT -/

section

open SimpleGraph
open Classical

universe u v w

/-- **Graph Minors IV, (7.1)** (page 244):
"Let $\eta$ be a expansion of $P = (G, \mu, \Delta, \phi)$ in $P' = (G', \mu', \Delta', \phi')$, and let $\eta'$ be an expansion of $P'$ in $P'' = (G'', \mu'', \Delta'', \phi'')$. Let $\eta''$ be defined by"

**Graph Minors IV, (7.1)** (pages 244–247): If `η = (ηv, ηe)` is an expansion of `P` in `P'`
and `η' = (η'v, η'e)` is an expansion of `P'` in `P''`, then `η'' = (compVertex ηv η'v, compEdge ηe η'e)`
is an expansion of `P` in `P''`; and if `η` and `η'` are realizable then so is `η''`. -/
theorem theorem_7_1 {Ω : Type w} [Preorder Ω] {α α' α'' : Type*} {β β' β'' : Type*}
    {P : Patchwork Ω α β} {P' : Patchwork Ω α' β'}
    {P'' : Patchwork Ω α'' β''} {ηv : α → Set α'} {ηe : β → β'}
    {η'v : α' → Set α''} {η'e : β' → β''}
    (hη : IsExpansion P P' ηv ηe) (hη' : IsExpansion P' P'' η'v η'e) :
    IsExpansion P P'' (compVertex ηv η'v) (compEdge ηe η'e) ∧
      ((∃ H, Realizes P P' ηv ηe H) → (∃ H', Realizes P' P'' η'v η'e H') →
        ∃ H'', Realizes P P'' (compVertex ηv η'v) (compEdge ηe η'e) H'') := by exact GraphMinor.GM04.theorem_7_1_proof hη hη'

end

/-! ## Section 8. Stars with Small Hearts -/

section

open SimpleGraph _root_.GraphMinor.Hypergraph
open Classical

universe u v w

/-- **Graph Minors IV, (8.1)** (page 247):
"Let $P = (G, \mu, \Delta, \phi)$, $P' = (G', \mu', \Delta', \phi')$ be $\Omega$-patchworks, and let $(G_1, G_2)$, $(G'_1, G'_2)$ be separations of $G$, $G'$ respectively. Let $\eta_1$ be a realizable expansion of $P | G_1$ in $P' | G'_1$ (whence $|\bar{\pi}(G_1)| = |\bar{\pi}(G'_1)| = k$, say) and let $\eta_2$ be a realizable expansion of $P | G_2$ in $P' | G'_2$ such that for $1 \le i \le k$, $\eta_2(v)$ contains the $i$th term of $\pi(G'_1)$, where $v$ is the $i$th term of $\pi(G_1)$. Define $\eta$ by
$$
\begin{aligned}
\eta(v) &= \eta_1(v) && (v \in V(G_1) - V(G_2)) \\
&= \eta_2(v) && (v \in V(G_2) - V(G_1)) \\
&= \eta_1(v) \cup \eta_2(v) && (v \in V(G_1) \cap V(G_2)) \\
\eta(e) &= \eta_1(e) && (e \in E(G_1)) \\
&= \eta_2(e) && (e \in E(G_2)).
\end{aligned}
$$
Then $\eta$ is a realizable expansion of $P$ in $P'$."

**Graph Minors IV, (8.1)** (page 247): -/
theorem theorem_8_1 {Ω : Type w} [Preorder Ω] {α α' β β' : Type*}
    {P : Patchwork Ω α β} {P' : Patchwork Ω α' β'}
    {G₁ G₂ : RootedHypergraph α β} {G'₁ G'₂ : RootedHypergraph α' β'}
    (hsep : P.G.IsSeparation G₁ G₂) (hsep' : P'.G.IsSeparation G'₁ G'₂)
    {η₁v η₂v : α → Set α'} {η₁e η₂e : β → β'}
    (hη₁ : IsRealizableExpansion (P.restrict G₁) (P'.restrict G'₁) η₁v η₁e)
    (hη₂ : IsRealizableExpansion (P.restrict G₂) (P'.restrict G'₂) η₂v η₂e)
    (hroots_mem : ∀ (i : ℕ) (hi : i < G₁.roots.length) (hi' : i < G'₁.roots.length),
      G'₁.roots[i] ∈ η₂v G₁.roots[i]) :
    IsRealizableExpansion P P' (glueVertex G₁ G₂ η₁v η₂v) (glueEdge G₁ η₁e η₂e) := by exact GraphMinor.GM04.theorem_8_1_proof hsep hsep' hη₁ hη₂ hroots_mem

end

section

open SimpleGraph _root_.GraphMinor.Hypergraph
open Classical
open Classical

universe u v w

/-- **Graph Minors IV, (8.2)** (page 248):
"Let $P = (G, \mu, \Delta, \phi)$, $P' = (G', \mu', \Delta', \phi')$ be $\Omega$-patchworks where $P'$ is removable. Let $(S, \sigma)$, $(S', \sigma')$ be star-decompositions of $G$, $G'$, respectively. Let $\gamma$ be a bijection from $V(\sigma(o(S)))$ to $V(\sigma'(o(S')))$ mapping $\pi(G)$ to $\pi(G')$. Let $\alpha$ be an injection from $E(\sigma(o(S)))$ into $E(\sigma'(o(S')))$, such that for each $e \in E(\sigma(o(S)))$
(i) $\alpha(e) \in \operatorname{dom}(\mu')$ if and only if $e \in \operatorname{dom}(\mu)$
(ii) if $e \in \operatorname{dom}(\mu)$ then $\gamma$ maps $\mu(e)$ to $\mu'(\alpha(e))$
(iii) if $e \notin \operatorname{dom}(\mu)$ then $\gamma$ maps $V_G(e)$ to $V_{G'}(\alpha(e))$
(iv) $\phi(e) \le \phi'(\alpha(e))$."

Note on condition (ii): the paper omits '`μ(e) → μ'(α(e))` maps `Δ(e)` to `Δ'(α(e))`' in the
statement of (8.2)(ii), which is required for `η₀` to satisfy condition (viii) of an expansion;
in the proof of (8.4) (page 250, claims (4) and (6)(ii)), the paper explicitly establishes
`Δᵢ(e) = Δ_{i'}(α(e))` before invoking (8.2).

The march bijection also preserves the patch groupings, as required by an expansion. See the
correction to (8.2) in `corrections/GM04.md`. -/
theorem theorem_8_2 {Ω : Type w} [Preorder Ω] {α α' β β' ι ι' : Type*}
    {P : Patchwork Ω α β} {P' : Patchwork Ω α' β'}
    (hP' : P'.IsRemovable)
    {S : RootedTree ι} {σ : ι → RootedHypergraph α β}
    {S' : RootedTree ι'} {σ' : ι' → RootedHypergraph α' β'}
    (hstar : S.IsStar) (htd : IsTreeDecomposition P.G S σ)
    (hstar' : S'.IsStar) (htd' : IsTreeDecomposition P'.G S' σ')
    {γ : α → α'} (hγ_bij : Set.BijOn γ (σ S.root).vertexSet (σ' S'.root).vertexSet)
    (hγ_roots : P'.G.roots = P.G.roots.map γ)
    {αe : β → β'} (hα_maps : Set.MapsTo αe (σ S.root).edgeSet (σ' S'.root).edgeSet)
    (hα_inj : Set.InjOn αe (σ S.root).edgeSet)
    (hα_dom : ∀ e ∈ (σ S.root).edgeSet, αe e ∈ P'.dom ↔ e ∈ P.dom)
    (hα_μ : ∀ e ∈ (σ S.root).edgeSet, e ∈ P.dom →
      P'.μ (αe e) = (P.μ e).map γ ∧
        Set.MapsTo (marchMapSubgraph (P.μ e) (P'.μ (αe e)))
          (P.Δ e).groupings (P'.Δ (αe e)).groupings)
    (hα_ends : ∀ e ∈ (σ S.root).edgeSet, e ∉ P.dom →
      γ '' P.G.ends e = P'.G.ends (αe e))
    (hα_φ : ∀ e ∈ (σ S.root).edgeSet, P.φ e ≤ P'.φ (αe e))
    {βf : ι → ι'} (hβ_bij : Set.BijOn βf (S.edges : Set ι) (S'.edges : Set ι'))
    (hβ_roots : ∀ s ∈ S.edges, (σ' (βf s)).roots = (σ s).roots.map γ)
    (hβ_sim : ∀ s ∈ S.edges, Simulated (P.restrict (σ s)) (P'.restrict (σ' (βf s)))) :
    Simulated P P' := by exact GraphMinor.GM04.theorem_8_2_proof hP' hstar htd hstar' htd' hγ_bij hγ_roots hα_maps hα_inj hα_dom hα_μ hα_ends hα_φ hβ_bij hβ_roots hβ_sim

end

section

open _root_.GraphMinor.Hypergraph

universe u v w u₁ u₂

/-- **Graph Minors IV, (8.3)** (page 249):
"Let $\Omega$ be a well-quasi -order, and let $X_i$ ($i = 1, 2, \dots$) be a countable sequence of finite subsets of $E(\Omega)$. Then there exists an infinite subset $I \subseteq \{1, 2, \dots\}$ with the property that for all $i$, $i' \in I$ with $i < i'$ there is an injection $\alpha \colon X_i \to X_{i'}$ such that $x \le \alpha(x)$ for all $x \in X_i$."

Graph Minors IV, (8.3), page 249: finite labelled sets in a well-quasi-order
have label-increasing injections along an infinite set of indices.

The sets are finite sets with a labelling, and the labels need not be distinct, because the proof
of (8.4) applies (8.3) to sets of edges that may share a label. -/
theorem theorem_8_3 :
  ∀ {κ Ω : Type*} [Preorder Ω], WellQuasiOrderedLE Ω → ∀ (X : ℕ → Finset κ) (ℓ : ℕ → κ → Ω),
    ∃ I : Set ℕ, I.Infinite ∧ ∀ i ∈ I, ∀ i' ∈ I, i < i' →
      ∃ g : κ → κ, Set.InjOn g (X i) ∧ Set.MapsTo g (X i) (X i') ∧
        ∀ x ∈ X i, ℓ i x ≤ ℓ i' (g x) := by exact GraphMinor.GM04.theorem_8_3_proof

end

section

open _root_.GraphMinor.Hypergraph

universe u v w u₁ u₂

/-- **Graph Minors IV, (8.4)** (page 249):
"Let $n \ge 0$, let $\Omega$ be a well-quasi-order, and let $P_i = (G_i, \mu_i, \Delta_i, \phi_i)$ ($i = 1, 2, \dots$) be a countable sequence of removable $\Omega$-patchworks. For each $i \ge 1$ let $(S_i, \sigma_i)$ be a star-decomposition of $G_i$ with $|V(\sigma_i(o(S_i)))| \le n$."

Graph Minors IV, (8.4), page 249, with its tree, path, and finite-set inputs proved.

The proof pulls back root marches to finite coordinates, instead of replacing each patchwork by an
isomorphic one, because all patchworks of the sequence share one vertex type. -/
theorem theorem_8_4 {Ω : Type w} [Preorder Ω] {α : Type u} {β : Type v} {ι : Type*}
    (hΩ : WellQuasiOrderedLE Ω)
    (n : ℕ) (P : ℕ → Patchwork Ω α β) (hrem : ∀ i, (P i).IsRemovable)
    (S : ℕ → RootedTree ι) (σ : ℕ → ι → RootedHypergraph α β)
    (hstar : ∀ i, (S i).IsStar)
    (htd : ∀ i, IsTreeDecomposition (P i).G (S i) (σ i))
    (hcard : ∀ i, (σ i (S i).root).vertexSet.ncard ≤ n)
    (hwqo : ∀ Q : ℕ → Patchwork Ω α β,
      (∀ k, ∃ i, ∃ s ∈ (S i).edges, Q k = (P i).restrict (σ i s)) →
      ∃ j j', j < j' ∧ Simulated (Q j) (Q j')) :
    ∃ i i', i < i' ∧ Simulated (P i) (P i') := by exact GraphMinor.GM04.theorem_8_4_proved hΩ n P hrem S σ hstar htd hcard hwqo

end

/-! ## Section 9. VERIFYING THE AXIOMS -/

section

open _root_.GraphMinor.Hypergraph

universe u v w u₁ u₂

/-- **Graph Minors IV, (9.1)** (page 252):
"Let $n \ge 0$, let $\Omega$ be a well-quasi-order, and let $P_i = (G_i, \mu_i, \Delta_i, \phi_i)$ $(i = 1, 2, \dots)$ be a countable sequence of robust $\Omega$-patchworks, where each $G_i$ has tree-width $\le n$. Then there exist $i' > i \ge 1$ such that there is a realizable expansion of $P_i$ in $P_{i'}$."

Graph Minors IV, (9.1), page 252, with its tree, path, and finite-set inputs proved.

The proof tags edges with their sequence index, instead of assuming that the graphs are disjoint,
because all graphs of the sequence share one edge type. -/
theorem theorem_9_1 {Ω : Type w} [Preorder Ω] {α : Type u} {β : Type v}
    (hΩ : WellQuasiOrderedLE Ω)
    (n : ℕ) (P : ℕ → Patchwork Ω α β)
    (hrob : ∀ i, (P i).IsRobust)
    (htw : ∀ i, TreeWidthLE (P i).G n) :
    ∃ i i', i < i' ∧ Simulated (P i) (P i') := by exact GraphMinor.GM04.theorem_9_1_proved hΩ n P hrob htw

end

section

open Set Surface Graph

universe u w

/-- **Graph Minors IV, (9.2)** (page 253):
"Let $\Sigma$ be a surface, let $n \ge 0$, and let $\Omega$ be a well-quasi-order. For $i \ge 1$ let $(U_i, N_i, \pi_i, \mu_i, \phi_i)$ be such that"

Graph Minors IV, (9.2), pages 253–254: a sequence of labelled paintings
of bounded tree-width has an expansion by components of a drawn forest,
with its edges inside cells and with the prescribed marches and labels.
The second part of printed (c) is corrected to apply to distinct vertices,
as explained in the module docstring.

Clause (c) requires distinct source vertices. See the correction to (9.2) in
`corrections/GM04.md`. -/
theorem theorem_9_2 {Ω : Type w} [Preorder Ω] (hΩ : WellQuasiOrderedLE Ω)
    {S : Type u} [TopologicalSpace S] [T2Space S] (hS : IsClosedSurface S)
    (n : ℕ) (P : ℕ → LabelledPainting Ω S)
    (htw : ∀ i, TreeWidthLE (P i).toRootedHypergraph n) :
    ∃ i j, i < j ∧ ∃ (Ξ : Drawing S) (σv : S → Graph S (Set S)) (σe : Set S → Set S),
      Ξ.V = (P j).painting.V ∧ IsGraphForest Ξ.toGraph ∧
      (∀ f ∈ Ξ.E, ∃ e ∈ (P j).painting.E, f ⊆ e) ∧
      (∀ v ∈ (P i).painting.V, GM06.IsGraphComponent (σv v) Ξ.toGraph) ∧
      Set.MapsTo σe (P i).painting.E (P j).painting.E ∧
      Set.InjOn σe (P i).painting.E ∧
      (∀ v ∈ (P i).painting.V, ∀ v' ∈ (P i).painting.V, v ≠ v' →
        Disjoint (GM06.compPointSet (σv v)) (GM06.compPointSet (σv v'))) ∧
      (∀ v ∈ (P i).painting.V, ∀ e ∈ (P i).painting.E,
        ∀ f ∈ E(σv v), Disjoint f (σe e)) ∧
      (∀ e ∈ (P i).painting.E,
        (closure e \ e).ncard = (closure (σe e) \ σe e).ncard ∧
        ((P i).μ e).length = ((P j).μ (σe e)).length ∧
        ∀ k (hk : k < ((P i).μ e).length) (hk' : k < ((P j).μ (σe e)).length),
          ((P j).μ (σe e))[k] ∈ V(σv ((P i).μ e)[k])) ∧
      ((P i).roots.length = (P j).roots.length ∧
        ∀ k (hk : k < (P i).roots.length) (hk' : k < (P j).roots.length),
          (P j).roots[k] ∈ V(σv (P i).roots[k])) ∧
      (∀ e ∈ (P i).painting.E, (P i).φ e ≤ (P j).φ (σe e)) := by exact GraphMinor.GM04.theorem_9_2_proof hΩ hS n P htw

end

end GraphMinor.GM04
