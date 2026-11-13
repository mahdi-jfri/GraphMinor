module

public import GraphMinor.GM01.Section4Separators
public import GraphMinor.GM01.OrderedSeparatorLocalization

/-!
# Localization of the chosen small separators

Graph Minors I, (4.3), page 56, localizes a minimal separator to the two
boundary blocks and the attachment regions of the blocks between them.
We apply the ordered-block argument to the actual comb subdivision.
Its block partition and separator property are proved from that data.
As printed after (4.2), the minimal separator is chosen for the late
union that begins at the right boundary block.
-/

public section

namespace GraphMinor.GM01

open Set Graph SimpleGraph Function GraphMinor.GM09

universe u v

/-- Graph Minors I, (4.3), page 56.
"For $\nu \le j \le n$, $X_j \subseteq S_{j-\nu+1} \cup Z_{j-\nu+2} \cup \dots \cup Z_{j-1} \cup S_j$."

A minimal window separator is contained in its boundary blocks and the attachment regions between.
The indices start at zero. The parameter `ν` is the window length
(called `v` in the paper). As in the minimal choice after (4.2), `X`
is an inclusion-minimal separator of the blocks up to `l` from the
blocks from `j` on. -/
theorem theorem_4_3_proof {α : Type u} {β : Type v} {γ δ L n : ℕ}
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
    (ν : ℕ) (hν : 3 ≤ ν) (l j : Fin n) (hwindow : l.val + ν = j.val + 1)
    {X : Set α} (hX : IsMinimalGraphSeparator G.graph X
      (⋃ i : Fin n, ⋃ (_ : i ≤ l), combBlock hL (subgraphUnion G.graph N R) c i)
      (⋃ i : Fin n, ⋃ (_ : j ≤ i), combBlock hL (subgraphUnion G.graph N R) c i)) :
    X ⊆ combBlock hL (subgraphUnion G.graph N R) c l ∪
      (⋃ i : Fin n, ⋃ (_ : l < i ∧ i < j),
        blockAttachmentRegion G.graph (⋃ k : Fin n,
          combBlock hL (subgraphUnion G.graph N R) c k)
          (combBlock hL (subgraphUnion G.graph N R) c i)) ∪
      combBlock hL (subgraphUnion G.graph N R) c j := by
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
  have hpart := combBlock_partition hL (Nat.zero_lt_of_lt j.isLt) hN hR.le hc
    hcentres hPN hE hRanges (fun e f hne ↦ (hInter e f hne).1) hmeetR
  have hBlocks : ∀ i : Fin n,
      combBlock hL (subgraphUnion G.graph N R) c i ⊆ V(G.graph) := by
    intro i x hx
    have hxH : x ∈ V(subgraphUnion G.graph N R) :=
      hpart.2 ▸ Set.mem_iUnion.mpr ⟨i, hx⟩
    exact (subgraphUnion_le hN hR.le).vertexSet_mono hxH
  exact minimal_separator_ordered_localization _ hBlocks hpart.1
    (fun k ↦ block_separates_strict hγ hδ hL htail G hno hN hc hV hE hPaths hInter hR hmeetR k)
    l j (by omega) hX

end GraphMinor.GM01
