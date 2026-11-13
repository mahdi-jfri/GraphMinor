module

public import GraphMinor.GM01.CombBypassExtension
public import GraphMinor.GM01.CombLastBlockMinor
public import GraphMinor.GM01.CombSkippedAttachment
public import GraphMinor.GM01.RootedCombMinor
public import GraphMinor.GM01.RootedForkAttachmentPaths
import GraphMinor.GM01.CombPrefixRoot
import GraphMinor.GM01.CombBlockConnectivity
import GraphMinor.GM01.ConnectedInducedSets
import GraphMinor.GM01.PathCombTrees
import GraphMinor.GM13.Section7WallModel
import Lean.Elab.Tactic.Omega

/-!
# The forbidden rooted fork from a block bypass

This is the contraction argument in Graph Minors I, (4.1), page 55.
Extend the clean bypass to its first final-block vertex. Root the shorter
comb there using the long ordinary tail minor. The skipped block supplies
the binary-tree arm and its boundary attachment. The initial prefix is
connected, contains the ambient root, and is disjoint from both arms.
The attachment-path constructor then builds the rooted fork by adding
the two path prefixes to this initial piece.
-/

public section

namespace GraphMinor.GM01

open Set Graph SimpleGraph Function GraphMinor.GM09

/-- The actual forbidden-fork construction in the proof of GM01 (4.1),
page 55. A clean bypass skipping a block gives `Q(γ,δ)` as a rooted minor
when the last block retains a `2δ`-vertex comb. -/
theorem rootedFork_of_comb_bypass {α β : Type*} {γ δ L n : ℕ}
    (hγ : 0 < γ) (hδ : 2 ≤ δ) (hL : 0 < L)
    (htail : 2 * n - 2 + 2 * δ ≤ L) (G : RootedGraph α β)
    {N R P₀ : Graph α β} (hN : N ≤ G.graph)
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
    (i k : Fin n) (hik : i.val + 2 ≤ k.val) {a b : α}
    (ha : a ∈ combBlock hL (subgraphUnion G.graph N R) c i)
    (hb : b ∈ combBlock hL (subgraphUnion G.graph N R) c k)
    (hP₀ : IsGraphPathWithEnds G.graph P₀ a b)
    (hmeetP : V(P₀) ∩ V(subgraphUnion G.graph N R) = {a,b}) :
    HasRootedMinor (rootedForkGraph γ δ hγ hδ) G := by
  have hn : 3 ≤ n := by have hk := k.isLt; omega
  have htail' : 2 * n ≤ L := by omega
  let H := subgraphUnion G.graph N R
  let blocks := fun j : Fin n ↦ combBlock hL H c j
  let j : Fin n := ⟨i.val + 1, by omega⟩
  let last : Fin n := ⟨n - 1, by omega⟩
  have hj0 : 0 < j.val := by dsimp [j]; omega
  have hjn : j.val + 1 < n := by dsimp [j]; have hk := k.isLt; omega
  have hcentres : ∀ v, c v ∈ V(N) := by
    intro v
    rw [hV]
    exact Or.inl (mem_range_self v)
  have hPN : ∀ e, P e ≤ N := by
    intro e
    obtain ⟨_, _, _, _, hP, _⟩ := hPaths e
    exact hP.le
  have hOnly : ∀ e : (pathComb (γ - 1) L).coe.edgeSet, ∃ a b, e.val = s(a,b) ∧
      IsGraphPathWithEnds N (P e) (c a) (c b) ∧ V(P e) ∩ range c = {c a,c b} := by
    intro e
    obtain ⟨a, b, he, _, hP, hRange⟩ := hPaths e
    exact ⟨a, b, he, hP, hRange⟩
  have hRanges : ∀ e : (pathComb (γ - 1) L).coe.edgeSet, ∃ a b, e.val = s(a,b) ∧
      V(P e) ∩ range c = {c a,c b} := by
    intro e
    obtain ⟨a, b, he, _, hRange⟩ := hOnly e
    exact ⟨a, b, he, hRange⟩
  have hInterV := fun e f hne ↦ (hInter e f hne).1
  have hNconn := subdivision_connected (pathComb_connected (γ := γ - 1) hL).coe
    (rootedPathComb (γ - 1) L hL).root N c P hV (fun e ↦ by
      obtain ⟨a, b, he, hab, hP, _⟩ := hPaths e
      exact ⟨a, b, he, hab, hP⟩)
  have hHconn : GraphConnected H := graphConnected_subgraphUnion hN hR.le hNconn
    (graphConnected_of_isGraphPath hR) ⟨_, hcentres _, hR.right_mem⟩
  have hcentresH : ∀ v, c v ∈ V(H) := fun v ↦ Or.inl (hcentres v)
  have hHG : H ≤ G.graph := subgraphUnion_le hN hR.le
  have hreg := combSpineRegion_antitone hL hN hR.le hc hcentres hPN hE hRanges hInterV hmeetR
  have hpair := (combBlock_partition hL (by omega : 0 < n) hN hR.le hc hcentres hPN hE
    hRanges hInterV hmeetR).1
  let C := combPrefix hL H c j.val
  obtain ⟨hCconnH, hCutC⟩ := combPrefix_connected hL hHconn c hcentresH j.val hj0 (by omega)
  have hCsubH : C ⊆ V(H) := sdiff_subset
  have hCsub : C ⊆ V(G.graph) := hCsubH.trans hHG.vertexSet_mono
  have hCconn : GraphConnected (G.graph.induce C) := graphConnected_induce_of_subgraph
    ((H.induce_le hCsubH).trans hHG) hCconnH
  have hrootC : G.root.val ∈ C := root_mem_combPrefix hL hN hc hcentres hPN hE hRanges hInterV
    G.root.val hR hmeetR j.val hj0 (by omega)
  have haC : a ∈ C := combBlock_subset_prefix hL H c hreg i j (by change i.val < i.val + 1; omega) ha
  obtain ⟨t, htLast, Q, hQ, hQavoid, hQmeet⟩ := exists_comb_bypass_to_last hL htail' hN hc hV hE
    hPaths hInterV G.root.val hR hmeetR i k hik ha hb hP₀ hmeetP
  have hConnLast := combBlock_connected hL htail' hN hc hV hPaths hInterV hE
    G.root.val hR hmeetR last
  let GP : RootedGraph α β := ⟨H.induce (blocks last), ⟨t, htLast⟩⟩
  have hGP : GP.graph ≤ G.graph := (H.induce_le (combBlock_subset_graph hL H c last)).trans hHG
  let u : (pathComb (γ - 1) L).verts := ⟨Sum.inl ⟨0, by omega⟩, pathComb_spine_mem _ _ _⟩
  let v : (pathComb (γ - 1) L).verts := ⟨Sum.inl ⟨1, by omega⟩, pathComb_spine_mem _ _ _⟩
  have huv : (pathComb (γ - 1) L).coe.Adj u v := pathComb_spine_adj
    (γ := γ - 1) (pathGraph_adj.mpr (Or.inl rfl))
  let edge : (pathComb (γ - 1) L).coe.edgeSet := ⟨s(u,v), huv⟩
  obtain ⟨x, y, _, hxy, hPath, _⟩ := hPaths edge
  obtain ⟨edgeLabel, _, _, _, _, _, _, _⟩ := hPath.exists_last_edge (fun h ↦ hxy.ne (hc h))
  let : Nonempty β := ⟨edgeLabel⟩
  obtain ⟨ηv, ηe, hTailModel⟩ := comb_lastBlock_minor_model (by omega : 2 ≤ n) htail' htail
    hN hc hcentres P hOnly hInter hE G.root.val hR hmeetR
  obtain ⟨MP⟩ := rootedPathComb_of_long_minor (by omega : 0 < δ - 1)
    (by omega : 2 * (δ - 1) + 1 ≤ 2 * δ) GP hConnLast hTailModel
  obtain ⟨K, hKN, hKblock, bRoot, ⟨MB⟩, B, hB, hBmeet, hBavoid⟩ :=
    exists_skipped_binary_attachment hL htail' hN hc hcentres P hE hOnly hInter
      G.root.val hR hmeetR j hj0 hjn
  let GB : RootedGraph α β := ⟨K, bRoot⟩
  have hGB : GB.graph ≤ G.graph := hKN.trans hN
  have hCPlast : Disjoint C (blocks last) := combPrefix_disjoint_block hL H c hreg j last (by
    change j.val ≤ n - 1
    omega)
  have hCB : Disjoint C V(K) :=
    (combPrefix_disjoint_block hL H c hreg j j le_rfl).mono_right hKblock
  have hLastNe : last ≠ j := by
    intro heq
    have hval := congrArg Fin.val heq
    dsimp [last] at hval
    omega
  have hPB : Disjoint (blocks last) V(K) := (hpair hLastNe).mono_right hKblock
  have hQavoidK : Disjoint V(Q) V(K) :=
    (hQavoid.mono_right subset_union_right).mono_right hKblock
  exact ⟨rootedForkModelOfAttachmentPaths hγ hδ G C hCsub hCconn hrootC hGP hGB MP MB
    hCPlast hCB hPB haC hCutC hQ hB hQmeet hBmeet hQavoidK hBavoid⟩

end GraphMinor.GM01
