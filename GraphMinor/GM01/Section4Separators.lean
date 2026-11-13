module

public import GraphMinor.GM01.CombBypassFork
public import GraphMinor.GM01.BlockBypass
import Lean.Elab.Tactic.Omega

/-!
# The block separators in the rooted fork reduction

Graph Minors I, (4.1), page 55, says each block separates the union of
the blocks up to it from the union of the blocks from it on. Failure gives a clean bypass between
two blocks on opposite sides. The proved comb-bypass construction turns
it into the forbidden rooted fork. This proves the separator assertion
from the actual subdivided-comb data and the paper's fork exclusion.
-/

public section

namespace GraphMinor.GM01

open Set Graph SimpleGraph Function GraphMinor.GM09

universe u v

/-- The form of Graph Minors I, (4.1), page 55, with both unions open at
`S_j`: block `j` separates the earlier blocks from the later ones. This
is the form the paper's proof shows, and the one later steps use.

The indices here start at zero. The proof trims a separator-failure path
and performs the paper's rooted-fork contraction using the preceding
initial piece, skipped binary arm and final comb arm. -/
theorem block_separates_strict {α : Type u} {β : Type v} {γ δ L n : ℕ}
    (hγ : 0 < γ) (hδ : 2 ≤ δ) (hL : 0 < L)
    (htail : 2 * n - 2 + 2 * δ ≤ L) (G : RootedGraph α β)
    (hno : ¬ HasRootedMinor (rootedForkGraph γ δ hγ hδ) G)
    {N R : Graph α β} (hN : N ≤ G.graph)
    {c : (pathComb (γ - 1) L).verts → α} (hc : Injective c)
    {P : (pathComb (γ - 1) L).coe.edgeSet → Graph α β}
    (hV : V(N) = range c ∪ ⋃ e, V(P e)) (hE : E(N) = ⋃ e, E(P e))
    (hPaths : ∀ e : (pathComb (γ - 1) L).coe.edgeSet, ∃ a b, e.val = s(a,b) ∧
      (pathComb (γ - 1) L).coe.Adj a b ∧ IsGraphPathWithEnds N (P e) (c a) (c b) ∧
      V(P e) ∩ range c = {c a,c b})
    (hInter : ∀ e f : (pathComb (γ - 1) L).coe.edgeSet, e ≠ f →
      V(P e) ∩ V(P f) ⊆ range c ∧ Disjoint E(P e) E(P f))
    (hR : IsGraphPathWithEnds G.graph R G.root.val
      (c (rootedPathComb (γ - 1) L hL).root))
    (hmeetR : V(N) ∩ V(R) ⊆ {c (rootedPathComb (γ - 1) L hL).root})
    (j : Fin n) :
    GraphSeparates G.graph
      (combBlock hL (subgraphUnion G.graph N R) c j)
      (⋃ i : Fin n, ⋃ (_ : i < j), combBlock hL (subgraphUnion G.graph N R) c i)
      (⋃ i : Fin n, ⋃ (_ : j < i), combBlock hL (subgraphUnion G.graph N R) c i) := by
  classical
  by_contra hfail
  have hcentres : ∀ v, c v ∈ V(N) := by
    intro v
    rw [hV]
    exact Or.inl (mem_range_self v)
  have hPN : ∀ e, P e ≤ N := by
    intro e
    obtain ⟨_, _, _, _, hPath, _⟩ := hPaths e
    exact hPath.le
  have hRanges : ∀ e : (pathComb (γ - 1) L).coe.edgeSet, ∃ a b, e.val = s(a,b) ∧
      V(P e) ∩ range c = {c a,c b} := by
    intro e
    obtain ⟨a, b, he, _, _, hRange⟩ := hPaths e
    exact ⟨a, b, he, hRange⟩
  have hcover := (combBlock_partition hL (Nat.zero_lt_of_lt j.isLt) hN hR.le hc hcentres hPN
    hE hRanges (fun e f hne ↦ (hInter e f hne).1) hmeetR).2
  obtain ⟨i, hij, k, hjk, a, ha, b, hb, P₀, hP₀, _, hMeet⟩ :=
    exists_block_bypass_of_not_separates
      (fun i : Fin n ↦ combBlock hL (subgraphUnion G.graph N R) c i) hcover j hfail
  apply hno
  exact rootedFork_of_comb_bypass hγ hδ hL htail G hN hc hV hE hPaths hInter hR hmeetR
    i k (by have hi := hij; have hk := hjk; change i.val < j.val at hi; change j.val < k.val at hk; omega)
    ha hb hP₀ hMeet

/-- Graph Minors I, (4.1), page 55:
"For $1 \le j \le n$, $S_j$ separates $\bigcup_{1 \le j' \le j} S_{j'}$ from $\bigcup_{j \le j' \le n} S_{j'}$ in $G$."

As printed, both unions contain `S_j`. A vertex of `S_j` lies on no path
that avoids `S_j`, so this is equivalent to the form with both unions
open at `S_j`, which is `block_separates_strict`. The indices here start
at zero. -/
theorem theorem_4_1_proof {α : Type u} {β : Type v} {γ δ L n : ℕ}
    (hγ : 0 < γ) (hδ : 2 ≤ δ) (hL : 0 < L)
    (htail : 2 * n - 2 + 2 * δ ≤ L) (G : RootedGraph α β)
    (hno : ¬ HasRootedMinor (rootedForkGraph γ δ hγ hδ) G)
    {N R : Graph α β} (hN : N ≤ G.graph)
    {c : (pathComb (γ - 1) L).verts → α} (hc : Injective c)
    {P : (pathComb (γ - 1) L).coe.edgeSet → Graph α β}
    (hV : V(N) = range c ∪ ⋃ e, V(P e)) (hE : E(N) = ⋃ e, E(P e))
    (hPaths : ∀ e : (pathComb (γ - 1) L).coe.edgeSet, ∃ a b, e.val = s(a,b) ∧
      (pathComb (γ - 1) L).coe.Adj a b ∧ IsGraphPathWithEnds N (P e) (c a) (c b) ∧
      V(P e) ∩ range c = {c a,c b})
    (hInter : ∀ e f : (pathComb (γ - 1) L).coe.edgeSet, e ≠ f →
      V(P e) ∩ V(P f) ⊆ range c ∧ Disjoint E(P e) E(P f))
    (hR : IsGraphPathWithEnds G.graph R G.root.val
      (c (rootedPathComb (γ - 1) L hL).root))
    (hmeetR : V(N) ∩ V(R) ⊆ {c (rootedPathComb (γ - 1) L hL).root})
    (j : Fin n) :
    GraphSeparates G.graph
      (combBlock hL (subgraphUnion G.graph N R) c j)
      (⋃ i : Fin n, ⋃ (_ : i ≤ j), combBlock hL (subgraphUnion G.graph N R) c i)
      (⋃ i : Fin n, ⋃ (_ : j ≤ i), combBlock hL (subgraphUnion G.graph N R) c i) := by
  refine (block_separates_strict hγ hδ hL htail G hno hN hc hV hE hPaths hInter hR hmeetR
    j).union_cut.mono ?_ ?_
  · intro x hx
    obtain ⟨i, hx⟩ := mem_iUnion.mp hx
    obtain ⟨hij, hxi⟩ := mem_iUnion.mp hx
    rcases lt_or_eq_of_le hij with hlt | rfl
    · exact Or.inl (mem_iUnion.mpr ⟨i, mem_iUnion.mpr ⟨hlt, hxi⟩⟩)
    · exact Or.inr hxi
  · intro x hx
    obtain ⟨i, hx⟩ := mem_iUnion.mp hx
    obtain ⟨hji, hxi⟩ := mem_iUnion.mp hx
    rcases lt_or_eq_of_le hji with hlt | rfl
    · exact Or.inl (mem_iUnion.mpr ⟨i, mem_iUnion.mpr ⟨hlt, hxi⟩⟩)
    · exact Or.inr hxi

end GraphMinor.GM01
