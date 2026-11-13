module

public import GraphMinor.GM01.Section4RootSeparation
public import GraphMinor.GM01.LayerBlockSets
import GraphMinor.GM01.CombPrefixes

/-!
# The distant block sets avoid a layer

Graph Minors I, (4.6), page 57, states that the early and late block
sets and the current layer are disjoint. A late block is separated
from the root by the next sampled separator, contrary to membership
in the layer. An early block is not separated by the preceding
sampled separator, again contrary to the layer definition. The first
and last layer cases use the empty index ranges.
-/

public section

namespace GraphMinor.GM01

open Set Graph SimpleGraph Function GraphMinor.GM09

universe u v

/-- Graph Minors I, (4.6), page 57: "$A, B$ and $W_i$ are disjoint."
The proof uses (4.4) for each block and the defining two tests of the
layer. The local choices are the minimal separators of (4.3) and
(4.4). No separation conclusion is assumed. -/
theorem theorem_4_6_proof {α : Type u} {β : Type v} {γ δ L n : ℕ}
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
    (hn : n = ν * T + 1) (i : Fin (T + 1)) :
    let S := fun k : Fin n ↦ combBlock hL (subgraphUnion G.graph N R) c k
    Disjoint (layerLateBlocks S ν i.val) (layerEarlyBlocks S ν i.val) ∧
      Disjoint (layerLateBlocks S ν i.val) (separatorLayer G.graph G.root.val Y i) ∧
      Disjoint (layerEarlyBlocks S ν i.val) (separatorLayer G.graph G.root.val Y i) := by
  let H := subgraphUnion G.graph N R
  let S := fun k : Fin n ↦ combBlock hL H c k
  change Disjoint (layerLateBlocks S ν i.val) (layerEarlyBlocks S ν i.val) ∧
    Disjoint (layerLateBlocks S ν i.val) (separatorLayer G.graph G.root.val Y i) ∧
    Disjoint (layerEarlyBlocks S ν i.val) (separatorLayer G.graph G.root.val Y i)
  have hwindow : ∀ a, (left a).val + ν = (right a).val + 1 := by
    intro a
    rw [hleft, hright, Nat.mul_add, Nat.mul_one]
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
  have hpart := combBlock_partition hL (by omega : 0 < n) hN hR.le hc
    hcentres hPN hE hRanges (fun e f hne ↦ (hInter e f hne).1) hmeetR
  refine ⟨disjoint_layerLateBlocks_layerEarlyBlocks S (by omega) hpart.1 i.val, ?_, ?_⟩
  · apply Set.disjoint_left.mpr
    intro x hxA hxW
    obtain ⟨k, hk, hxk⟩ := Set.mem_iUnion₂.mp hxA
    have hiT : i.val < T := by
      by_contra hnot
      have hieq : i.val = T := by have hi := i.isLt; omega
      rw [hieq, Nat.mul_add, Nat.mul_one] at hk
      have hkn := k.isLt
      omega
    let a : Fin T := ⟨i.val, hiT⟩
    have hsep := (theorem_4_4_proof hγ hδ hL htail G hno hN hc hV hE hPaths hInter hR hmeetR
      ν hν (left a) (right a) (hwindow a) (hY a) k hxk).1
    have hra : (right a).val + 1 = ν * (i.val + 1) := hright a
    have hrk : right a ≤ k := by change (right a).val ≤ k.val; omega
    exact hxW.2.2 a rfl (hsep hrk)
  · apply Set.disjoint_left.mpr
    intro x hxB hxW
    obtain ⟨k, hk, hxk⟩ := Set.mem_iUnion₂.mp hxB
    have hipos : 0 < i.val := by
      by_contra hnot
      have hi0 : i.val = 0 := by omega
      rw [hi0, Nat.zero_sub, Nat.mul_zero] at hk
      omega
    let a : Fin T := ⟨i.val - 1, by have hi := i.isLt; omega⟩
    have hnoSep := (theorem_4_4_proof hγ hδ hL htail G hno hN hc hV hE hPaths hInter hR hmeetR
      ν hν (left a) (right a) (hwindow a) (hY a) k hxk).2
    have hla : (left a).val = ν * (i.val - 1) := hleft a
    have hwa := hwindow a
    have hkr : k.val + ν ≤ (right a).val := by omega
    have hsucc : a.val + 1 = i.val := by change i.val - 1 + 1 = i.val; omega
    exact hnoSep hkr (hxW.2.1 a hsucc)

end GraphMinor.GM01
