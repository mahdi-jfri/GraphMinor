module

public import GraphMinor.GM01.Section4Separators
public import GraphMinor.GM01.ManyGraphSeparators
import GraphMinor.GM01.CombBlockConnectivity
import GraphMinor.GM01.CombPrefixes
import GraphMinor.GM01.ConnectedInducedSets
import Lean.Elab.Tactic.Omega

/-!
# Small separators across a consecutive block window

Graph Minors I, (4.2), pages 55–56, uses the `θ^(2θ)` consecutive block
separators ending at the chosen index. The blocks are connected and
disjoint. By (4.1), each separates the early endpoint set from the late
one, which begins at the last block of the window, as printed. The
boundary blocks may themselves contain endpoints, which are already met
by their separators. The proved Menger/(2.7) argument for general graphs
then gives a separator with fewer than `θ²/2` vertices.
-/

public section

namespace GraphMinor.GM01

open Set Graph SimpleGraph Function GraphMinor.GM09

universe u v

/-- Graph Minors I, (4.2), pages 55–56. The zero-based condition
`θ^(2θ) ≤ j+1` corresponds to the paper's `ν ≤ j`. The early union has
`j+2−ν` blocks, matching the paper's union through `S_{j−ν+1}`, and the
late union begins at block `j`, as printed (`j ≤ j' ≤ n`). The proof is
the paper's: each of the `ν` blocks of the window separates the two
unions by (4.1), so (2.7) and Menger's theorem give a small separator. -/
theorem theorem_4_2_proof {α : Type u} {β : Type v} {γ δ L n θ : ℕ}
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
    ∃ X ⊆ V(G.graph), X.ncard < θ ^ 2 / 2 ∧ GraphSeparates G.graph X
      (⋃ i : Fin n, ⋃ (_ : i.val < j.val + 2 - θ ^ (2 * θ)),
        combBlock hL (subgraphUnion G.graph N R) c i)
      (⋃ i : Fin n, ⋃ (_ : j ≤ i), combBlock hL (subgraphUnion G.graph N R) c i) := by
  let ν := θ ^ (2 * θ)
  have hν : 0 < ν := Nat.pow_pos (by omega : 0 < θ)
  let start := j.val + 1 - ν
  have hstart : start + ν = j.val + 1 := Nat.sub_add_cancel hj
  let index (k : Fin ν) : Fin n := ⟨start + k.val, by have hk := k.isLt; have hjn := j.isLt; omega⟩
  have hIndex : Injective index := by
    intro k k' heq
    apply Fin.ext
    have hv := congrArg Fin.val heq
    dsimp [index] at hv
    omega
  let H := subgraphUnion G.graph N R
  let blocks := fun i : Fin n ↦ combBlock hL H c i
  let A := ⋃ i : Fin n, ⋃ (_ : i.val < j.val + 2 - ν), blocks i
  let B := ⋃ i : Fin n, ⋃ (_ : j ≤ i), blocks i
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
  have hInterV := fun e f hne ↦ (hInter e f hne).1
  have hpair := (combBlock_partition hL (Nat.zero_lt_of_lt j.isLt) hN hR.le hc hcentres hPN
    hE hRanges hInterV hmeetR).1
  have hHG : H ≤ G.graph := subgraphUnion_le hN hR.le
  have hBlocks : ∀ i, blocks i ⊆ V(G.graph) :=
    fun i ↦ (combBlock_subset_graph hL H c i).trans hHG.vertexSet_mono
  have hConn : ∀ k : Fin ν, GraphConnected (G.graph.induce (blocks (index k))) := by
    intro k
    have hconn := combBlock_connected hL (by omega : 2 * n ≤ L) hN hc hV hPaths hInterV hE
      G.root.val hR hmeetR (index k)
    exact graphConnected_induce_of_subgraph
      ((H.induce_le (combBlock_subset_graph hL H c (index k))).trans hHG) hconn
  have hSep : ∀ k : Fin ν, GraphSeparates G.graph (blocks (index k)) A B := by
    intro k
    have hsep := block_separates_strict hγ hδ hL htail G hno hN hc hV hE hPaths hInter hR hmeetR (index k)
    apply hsep.union_cut.mono
    · intro x hx
      obtain ⟨i, hx⟩ := mem_iUnion.mp hx
      obtain ⟨hi, hxi⟩ := mem_iUnion.mp hx
      have hik : i.val ≤ (index k).val := by
        have hk := k.isLt
        dsimp [index]
        omega
      by_cases hieq : i = index k
      · exact Or.inr (hieq ▸ hxi)
      · have hilt : i < index k := lt_of_le_of_ne hik hieq
        exact Or.inl (mem_iUnion.mpr ⟨i, mem_iUnion.mpr ⟨hilt, hxi⟩⟩)
    · intro x hx
      obtain ⟨i, hx⟩ := mem_iUnion.mp hx
      obtain ⟨hji, hxi⟩ := mem_iUnion.mp hx
      have hki : index k ≤ i := by
        have hk := k.isLt
        change j.val ≤ i.val at hji
        change start + k.val ≤ i.val
        omega
      by_cases hkieq : index k = i
      · exact Or.inr (hkieq.symm ▸ hxi)
      · have hklt : index k < i := lt_of_le_of_ne hki hkieq
        exact Or.inl (mem_iUnion.mpr ⟨i, mem_iUnion.mpr ⟨hklt, hxi⟩⟩)
  exact exists_small_graph_separator_of_many_separators hθ heven G.graph hfin hGrid A B
    (fun k : Fin ν ↦ blocks (index k)) (fun k ↦ hBlocks (index k)) hConn
    (fun k k' hne ↦ hpair (hIndex.ne hne)) hSep

end GraphMinor.GM01
