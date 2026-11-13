module

public import GraphMinor.GM01.Section4LayerModelExclusion
public import GraphMinor.GM01.PathWidthComponents
import GraphMinor.GM01.GraphComponents

/-!
# Applying the preceding induction bound to each layer component

Graph Minors I, page 57, roots each component of a layer and applies
the induction bound for `P(γ−1,μ)`. The layer-model exclusion proves
that the component has no such rooted minor. It inherits finiteness
and grid exclusion from the ambient graph. Result (1.4) then gives
the same width bound for the entire layer.
-/

public section

namespace GraphMinor.GM01

open Set Graph SimpleGraph Function GraphMinor.GM09

universe u v

/-- The component-width step on page 57 of GM01. `hPrev` is the
preceding-height induction hypothesis for the fixed larger comb;
the forbidden model in each component is excluded by the proved
Section 4 argument, not assumed. -/
theorem section4_layer_widths {α : Type u} {β : Type v} {γ δ L n : ℕ}
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
    {T ν : ℕ} (hν : 3 ≤ ν) (left right : Fin T → Fin n)
    (hleft : ∀ i, (left i).val = ν * i.val)
    (hright : ∀ i, (right i).val + 1 = ν * (i.val + 1))
    (Y : Fin T → Set α)
    (hY : ∀ i, IsMinimalGraphSeparator G.graph (Y i)
      (⋃ k : Fin n, ⋃ (_ : k ≤ left i), combBlock hL (subgraphUnion G.graph N R) c k)
      (⋃ k : Fin n, ⋃ (_ : right i ≤ k), combBlock hL (subgraphUnion G.graph N R) c k))
    (hn : n = ν * T + 1)
    {m : ℕ} (hm : m = 2 + 4 * ν + 2 * δ) (hT : 2 ≤ T)
    (hmaxT : ∀ t : ℕ, 2 * ν * t ≤ L - 2 * δ → t ≤ T)
    (hmaxL : ∀ k (hk : 0 < k), HasRootedMinor (rootedPathComb (γ - 1) k hk) G → k ≤ L)
    (hGconn : GraphConnected G.graph) (hfin : V(G.graph).Finite) {θ p : ℕ}
    (hGrid : ¬ IsIsoMinor (gridGraph θ) G.graph)
    (hPrev : ∀ C : RootedGraph α β, V(C.graph).Finite → GraphConnected C.graph →
      (¬ IsIsoMinor (gridGraph θ) C.graph) →
      (¬ HasRootedMinor (rootedPathComb (γ - 1) m (by omega)) C) → HasPathWidthLE C.graph p) :
    ∀ i : Fin (T + 1), HasPathWidthLE (G.graph.induce (separatorLayer G.graph G.root.val Y i)) p := by
  intro i
  let Gi := G.graph.induce (separatorLayer G.graph G.root.val Y i)
  have hGiG : Gi ≤ G.graph := G.graph.induce_le (fun _ hx ↦ hx.1)
  have hfinGi : V(Gi).Finite := hfin.subset hGiG.vertexSet_mono
  apply theorem_1_4_proof hfinGi
  intro v
  let C : RootedGraph α β := ⟨Gi.induce (componentVertices Gi v), ⟨v.val, mem_componentVertices_self Gi v⟩⟩
  have hCGi : C.graph ≤ Gi := Gi.induce_le (fun _ hx ↦ hx.1)
  have hCG : C.graph ≤ G.graph := hCGi.trans hGiG
  have hCW : V(C.graph) ⊆ separatorLayer G.graph G.root.val Y i := hCGi.vertexSet_mono
  have hCGrid : ¬ IsIsoMinor (gridGraph θ) C.graph := by
    rintro ⟨K, hKC, edges, hEdges, hIso⟩
    exact hGrid ⟨K, hKC.trans hCG, edges, hEdges, hIso⟩
  have hCno := no_rooted_comb_model_in_separator_layer hγ hδ hL htail G hno hN hc hV hE hPaths hInter
    hR hmeetR hν left right hleft hright Y hY hn i hm hT hmaxT hmaxL hGconn C hCG hCW
  exact hPrev C (hfin.subset hCG.vertexSet_mono) (componentVertices_connected Gi v) hCGrid hCno

end GraphMinor.GM01
