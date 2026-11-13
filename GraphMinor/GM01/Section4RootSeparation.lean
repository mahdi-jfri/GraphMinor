module

public import GraphMinor.GM01.Section4Localization
import GraphMinor.GM01.CombPrefixRoot
import GraphMinor.GM01.CombPrefixes
import GraphMinor.GM01.SubdivisionConnected
import GraphMinor.GM01.PathCombTrees
import GraphMinor.GM01.ConnectedInducedSets

/-!
# Which blocks are separated from the root

Graph Minors I, (4.4), page 56, first uses the defining separator to
separate every late block from the root. For an early block, (4.3)
places the separator beyond a connected initial piece containing both
that block and the root. A path inside that piece avoids the separator.
As printed after (4.2), the late endpoint set of the minimal separator
begins at the right boundary block.
-/

public section

namespace GraphMinor.GM01

open Set Graph SimpleGraph Function GraphMinor.GM09

universe u v

/-- Graph Minors I, (4.4), page 56, parts (i) and (ii).
"For $\nu \le i \le n$, $1 \le j \le n$, if $s \in S_j$, then (i) $X_i$ separates $s$ and $\rho(G)$ if $j \ge 1$, and (ii) $X_i$ does not separate $s$ and $\rho(G)$ if $j \le i - \nu$."

Late blocks are separated from the root and blocks before the separator window
are not. Indices start at zero. Part (i) is stated for `j ≥ i`, not for
`j ≥ 1` as printed, which contradicts (ii) at `j = 1`. See the correction to (4.4) in
`corrections/GM01.md`. -/
theorem theorem_4_4_proof {α : Type u} {β : Type v} {γ δ L n : ℕ}
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
      (⋃ i : Fin n, ⋃ (_ : j ≤ i), combBlock hL (subgraphUnion G.graph N R) c i))
    (k : Fin n) {s : α} (hs : s ∈ combBlock hL (subgraphUnion G.graph N R) c k) :
    (j ≤ k → GraphSeparates G.graph X {s} {G.root.val}) ∧
    (k.val + ν ≤ j.val → ¬ GraphSeparates G.graph X {s} {G.root.val}) := by
  let H := subgraphUnion G.graph N R
  let S := fun i : Fin n ↦ combBlock hL H c i
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
  have hpart := combBlock_partition hL (Nat.zero_lt_of_lt j.isLt) hN hR.le hc
    hcentres hPN hE hRanges hInterV hmeetR
  have hHG : H ≤ G.graph := subgraphUnion_le hN hR.le
  have hreg := combSpineRegion_antitone hL hN hR.le hc hcentres hPN hE hRanges hInterV hmeetR
  have hn : 2 < n := by have hjn := j.isLt; omega
  have htwoL : 2 < L := by omega
  have hrootPrefix := root_mem_combPrefix hL hN hc hcentres hPN hE hRanges hInterV
    G.root.val hR hmeetR 1 (by omega) (by omega)
  have hrootS : G.root.val ∈ S ⟨0, by omega⟩ := by
    simpa only [S, combBlock, orderedRegionBlock, Nat.zero_lt_of_lt hn,
      show 0 + 1 < n by omega, ↓reduceIte, Fin.val_zero, Nat.mul_zero,
      combSpineRegion_zero, combPrefix, Nat.mul_one] using hrootPrefix
  constructor
  · intro hjk a ha b hb hav hbv hr
    have ha' : a = s := mem_singleton_iff.mp ha
    have hb' : b = G.root.val := mem_singleton_iff.mp hb
    subst a
    subst b
    exact hX.1 G.root.val (Set.mem_iUnion₂.mpr ⟨⟨0, by omega⟩,
      by change 0 ≤ l.val; exact Nat.zero_le _, hrootS⟩)
      s (Set.mem_iUnion₂.mpr ⟨k, hjk, hs⟩) hbv hav (Std.Symm.symm _ _ hr)
  · intro hkj
    have hkl : k < l := by change k.val < l.val; omega
    have hlpos : 0 < l.val := by omega
    have hlL : 2 * l.val < L := by have hjn := j.isLt; omega
    have hNconn := subdivision_connected (pathComb_connected (γ := γ - 1) hL).coe
      (rootedPathComb (γ - 1) L hL).root N c P hV (fun e ↦ by
        obtain ⟨a, b, he, hab, hP, _⟩ := hPaths e
        exact ⟨a, b, he, hab, hP⟩)
    have hHconn : GraphConnected H := graphConnected_subgraphUnion hN hR.le hNconn
      (graphConnected_of_isGraphPath hR) ⟨_, hcentres _, hR.right_mem⟩
    have hcentresH : ∀ v, c v ∈ V(H) := fun v ↦ Or.inl (hcentres v)
    have hconn := (combPrefix_connected hL hHconn c hcentresH l.val hlpos hlL).1
    have hroot := root_mem_combPrefix hL hN hc hcentres hPN hE hRanges hInterV
      G.root.val hR hmeetR l.val hlpos hlL
    have hsPrefix := combBlock_subset_prefix hL H c hreg k l hkl hs
    have hlocal := theorem_4_3_proof hγ hδ hL htail G hno hN hc hV hE hPaths hInter hR hmeetR
      ν hν l j hwindow hX
    have hdis : Disjoint (combPrefix hL H c l.val) X := by
      apply Set.disjoint_left.mpr
      intro x hx hxX
      have hdisBlock : ∀ i : Fin n, l ≤ i → x ∉ S i := by
        intro i hli hxi
        exact Set.disjoint_left.mp (combPrefix_disjoint_block hL H c hreg l i hli) hx hxi
      rcases hlocal hxX with (hxl | hxi) | hxj
      · exact hdisBlock l le_rfl hxl
      · obtain ⟨i, hi, hxZ⟩ := Set.mem_iUnion₂.mp hxi
        have hxU : x ∈ ⋃ i : Fin n, S i := hpart.2.symm ▸ hx.1
        have hSiU : S i ⊆ ⋃ i : Fin n, S i := fun _ h ↦ Set.mem_iUnion.mpr ⟨i, h⟩
        have hSiG : S i ⊆ V(G.graph) :=
          (combBlock_subset_graph hL H c i).trans hHG.vertexSet_mono
        have hxi : x ∈ S i := (blockAttachmentRegion_inter hSiU hSiG) ▸ ⟨hxZ, hxU⟩
        exact hdisBlock i hi.1.le hxi
      · exact hdisBlock j (by change l.val ≤ j.val; omega) hxj
    have hprefixG : H.induce (combPrefix hL H c l.val) ≤ G.graph := by
      refine ⟨fun _ hx ↦ hHG.vertexSet_mono hx.1, ?_⟩
      intro e a b he
      exact he.1.mono hHG
    exact not_graphSeparates_of_connected_induce
      (D := combPrefix hL H c l.val)
      (fun _ hx ↦ hHG.vertexSet_mono hx.1)
      (graphConnected_induce_of_subgraph hprefixG hconn) hdis hsPrefix hroot

end GraphMinor.GM01
