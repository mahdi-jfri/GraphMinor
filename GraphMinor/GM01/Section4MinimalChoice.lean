module

public import GraphMinor.GM01.Section4SmallSeparators
public import GraphMinor.GM01.MinimalSeparators

/-!
# Choosing the small block separators minimally

After (4.2), Graph Minors I, page 56, chooses its separators minimally.
A finite separator has an inclusion-minimal subset, whose cardinality
still satisfies the same strict bound. The late endpoint set begins at
the last block of the window, as printed in (4.2). Thus minimality in
(4.3) and (4.4) is an available choice.
-/

public section

namespace GraphMinor.GM01

open Set Graph SimpleGraph Function GraphMinor.GM09

universe u v

/-- The minimal choice preceding GM01 (4.3), page 56, applied to the
separator of (4.2) (`theorem_4_2_proof`).
Taking a minimal subset preserves the strict cardinality bound. -/
theorem exists_small_minimal_block_separator {α : Type u} {β : Type v} {γ δ L n θ : ℕ}
    (hγ : 0 < γ) (hδ : 2 ≤ δ) (hL : 0 < L)
    (htail : 2 * n - 2 + 2 * δ ≤ L) (G : RootedGraph α β) (hfin : V(G.graph).Finite)
    (hθ : 6 ≤ θ) (heven : Even θ) (hGrid : ¬ IsIsoMinor (gridGraph θ) G.graph)
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
    (j : Fin n) (hj : θ ^ (2 * θ) ≤ j.val + 1) :
    ∃ X ⊆ V(G.graph), X.ncard < θ ^ 2 / 2 ∧ IsMinimalGraphSeparator G.graph X
      (⋃ i : Fin n, ⋃ (_ : i.val < j.val + 2 - θ ^ (2 * θ)),
        combBlock hL (subgraphUnion G.graph N R) c i)
      (⋃ i : Fin n, ⋃ (_ : j ≤ i), combBlock hL (subgraphUnion G.graph N R) c i) := by
  obtain ⟨X, hXG, hcard, hsep⟩ := theorem_4_2_proof
    hγ hδ hL htail G hfin hθ heven hGrid hno hN hc hV hE hPaths hInter hR hmeetR j hj
  have hXfin := hfin.subset hXG
  obtain ⟨Y, hYX, hmin⟩ := exists_minimal_graph_separator hXfin hsep
  exact ⟨Y, hYX.trans hXG, lt_of_le_of_lt (Set.ncard_le_ncard hYX hXfin) hcard, hmin⟩

end GraphMinor.GM01
