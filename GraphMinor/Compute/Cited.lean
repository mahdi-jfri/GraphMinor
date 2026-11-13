module

public import GraphMinor.Compute.Graph
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
public import Mathlib.Combinatorics.SimpleGraph.Finite

/-!
# Cited Algorithmic Results from Outside the Graph Minors Series

This file states `Shiloach80Statement`, the external algorithm of Y. Shiloach cited by Robertson
and Seymour in *Graph Minors. XIII. The Disjoint Paths Problem*, Section 8, (8.1), page 93:

* Y. Shiloach, *A polynomial solution to the undirected two paths problem*, J. ACM **27** (1980),
  445–456.

In Graph Minors XIII, (8.1) (page 93), Robertson and Seymour write:
* "We apply an algorithm of Shiloach [27] to find two paths of $G \cup H$, vertex-disjoint,
  joining $s_1, t_1$ and $s_2, t_2$, respectively, if they exist."
* "Shiloach's algorithm has running time $O(v\varepsilon)$"

Here $v = v(G) = |V(G)| + 1$ (page 66) and $\varepsilon = \varepsilon(G) = |E(G)| + |V(G)| + 1$
(page 71).
-/

@[expose] public section

namespace GraphMinor.Compute

open SimpleGraph

/-- **Shiloach's undirected two-paths algorithm** (Y. Shiloach, *A polynomial solution to the
undirected two paths problem*, J. ACM 27 (1980), 445–456), as cited in Robertson and Seymour,
*Graph Minors. XIII. The Disjoint Paths Problem*, Section 8, (8.1), page 93:

* "an algorithm of Shiloach [27] to find two paths of $G \cup H$, vertex-disjoint, joining
  $s_1, t_1$ and $s_2, t_2$, respectively, if they exist"
* "Shiloach's algorithm has running time $O(v\varepsilon)$"

Fixed Word RAM calling convention:
* **Input registers (`30..34`):** `s.regs 30 = N` (number of vertices) and
  `s.regs 31 = s₁.1`, `s.regs 32 = t₁.1`, `s.regs 33 = s₂.1`, `s.regs 34 = t₂.1` for four
  pairwise distinct vertices `s₁, t₁, s₂, t₂ : Fin N`.
* **Input arrays (`30..32`):** CSR adjacency-list representation `IsAdjList G 30 31 32 lists s`
  of a simple graph `G : SimpleGraph (Fin N)` with `(s.arrs 32).length < 2 ^ w`.
* **Scratch space:** The program may only modify registers `≥ 30` and arrays `≥ 33`; all caller
  registers `< 30` and arrays `< 33` (including `inArr = 0`, `outArr = 1`, and the input CSR
  arrays `30, 31, 32`) are preserved.
* **Output (`reg 35`, `arrs 33, 34`):** Within `C * (N + 1) * (G.edgeFinset.card + N + 1)` steps
  (`C · v · ε`, where `v = N + 1` and `ε = |E(G)| + N + 1`), either:
  - `s'.regs 35 = 1` and arrays `33` and `34` store the vertex lists `P₁.support.map Fin.val` and
    `P₂.support.map Fin.val` of two vertex-disjoint simple paths `P₁ : G.Walk s₁ t₁` and
    `P₂ : G.Walk s₂ t₂`, or
  - `s'.regs 35 = 0` and no two vertex-disjoint simple paths in `G` join `s₁, t₁` and `s₂, t₂`. -/
def Shiloach80Statement : Prop :=
  ∃ (prog : Cmd) (C c_w : ℕ), 0 < C ∧ 0 < c_w ∧
    ∀ (N : ℕ) (G : SimpleGraph (Fin N)) [DecidableRel G.Adj]
      (lists : Fin N → List ℕ) (s₁ t₁ s₂ t₂ : Fin N),
      s₁ ≠ t₁ → s₁ ≠ s₂ → s₁ ≠ t₂ → t₁ ≠ s₂ → t₁ ≠ t₂ → s₂ ≠ t₂ →
      ∀ (w : ℕ), wordSize c_w ((N + 1) * (G.edgeFinset.card + N + 1)) ≤ w →
      ∀ (s : State),
        IsAdjList G 30 31 32 lists s →
        (s.arrs 32).length < 2 ^ w →
        s.regs 30 = N →
        s.regs 31 = s₁.1 →
        s.regs 32 = t₁.1 →
        s.regs 33 = s₂.1 →
        s.regs 34 = t₂.1 →
        ∃ (s' : State) (t : ℕ),
          Exec w prog s s' t ∧
          t ≤ C * (N + 1) * (G.edgeFinset.card + N + 1) ∧
          (∀ r < 30, s'.regs r = s.regs r) ∧
          (∀ a < 33, s'.arrs a = s.arrs a) ∧
          ((s'.regs 35 = 1 ∧
              ∃ (P₁ : G.Walk s₁ t₁) (P₂ : G.Walk s₂ t₂),
                P₁.IsPath ∧ P₂.IsPath ∧
                List.Disjoint P₁.support P₂.support ∧
                s'.arrs 33 = P₁.support.map Fin.val ∧
                s'.arrs 34 = P₂.support.map Fin.val) ∨
            (s'.regs 35 = 0 ∧
              ∀ (P₁ : G.Walk s₁ t₁) (P₂ : G.Walk s₂ t₂),
                P₁.IsPath → P₂.IsPath → ¬ List.Disjoint P₁.support P₂.support))

end GraphMinor.Compute
