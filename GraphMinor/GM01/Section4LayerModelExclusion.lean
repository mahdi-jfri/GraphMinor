module

public import GraphMinor.GM01.Section4LayerSubdivisionExclusion
import GraphMinor.GM01.CombSubdivision

/-!
# Excluding a rooted comb model from a separator layer

Graph Minors I, page 57, obtains a subdivision from a rooted model
in a component of a layer. The source comb is subcubic, so the proved
subdivision construction applies. Its vertices stay in the layer.
The completed Section 4 contradiction excludes this subdivision and
therefore the original rooted model. The same proof applies to every
rooted subgraph of the layer.
-/

public section

namespace GraphMinor.GM01

open Set Graph SimpleGraph Function GraphMinor.GM09

universe u v

/-- The model exclusion on page 57 of GM01, using the proved
subcubic subdivision construction and the full (4.8)–(4.14) argument. -/
theorem no_rooted_comb_model_in_separator_layer {α : Type u} {β : Type v} {γ δ L n : ℕ}
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
    (hn : n = ν * T + 1) (i : Fin (T + 1))
    {m : ℕ} (hm : m = 2 + 4 * ν + 2 * δ) (hT : 2 ≤ T)
    (hmaxT : ∀ t : ℕ, 2 * ν * t ≤ L - 2 * δ → t ≤ T)
    (hmaxL : ∀ k (hk : 0 < k), HasRootedMinor (rootedPathComb (γ - 1) k hk) G → k ≤ L)
    (hGconn : GraphConnected G.graph) (C : RootedGraph α β) (hCG : C.graph ≤ G.graph)
    (hCW : V(C.graph) ⊆ separatorLayer G.graph G.root.val Y i) :
    ¬ HasRootedMinor (rootedPathComb (γ - 1) m (by omega)) C := by
  rintro ⟨M⟩
  obtain ⟨D, cD, PD, _, hDC, hcD, hVD, _, hDPaths, hDInter, _⟩ :=
    M.pathComb_subdivision (by omega : 2 ≤ m) C
  have hOnly : ∀ e : (pathComb (γ - 1) m).coe.edgeSet, ∃ a b, e.val = s(a,b) ∧
      IsGraphPathWithEnds D (PD e) (cD a) (cD b) ∧ V(PD e) ∩ range cD = {cD a,cD b} := by
    intro e
    obtain ⟨a, b, he, _, hP, hRange⟩ := hDPaths e
    exact ⟨a, b, he, hP, hRange⟩
  exact no_comb_subdivision_in_separator_layer hγ hδ hL htail G hno hN hc hV hE hPaths hInter hR hmeetR
    hν left right hleft hright Y hY hn i hm D (hDC.trans hCG) (hDC.vertexSet_mono.trans hCW)
    hcD PD hVD hOnly (fun e f hne ↦ ⟨(hDInter e f hne).2, (hDInter e f hne).1⟩)
    hT hmaxT hmaxL hGconn

end GraphMinor.GM01
