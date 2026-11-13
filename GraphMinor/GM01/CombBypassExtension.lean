module

public import GraphMinor.GM01.CombBlocks
public import GraphMinor.GM01.OrderedBlockExtension
import GraphMinor.GM01.SubdivisionConnected
import GraphMinor.GM01.PathCombTrees
import GraphMinor.GM09.Section2c
import Lean.Elab.Tactic.Omega

/-!
# Extending the comb bypass to the last block

The second sentence of the proof of Graph Minors I, (4.1), page 55,
follows a clean bypass into the final block while avoiding all earlier
blocks and the skipped next block. Apply the ordered-block extension to
the actual decreasing comb regions. Their connectivity and membership
of the last centre are proved from the graph construction, so the
resulting path has its terminal vertex in the last block.
-/

public section

namespace GraphMinor.GM01

open Set Graph SimpleGraph Function GraphMinor.GM09

/-- The path to the final block in the proof of GM01 (4.1), page 55.
The forbidden earlier and next blocks are avoided by a constructed path,
not assumed to be avoidable. -/
theorem exists_comb_bypass_to_last {α β : Type*} {γ L n : ℕ} (hL : 0 < L)
    (htail : 2 * n ≤ L) {G N R P₀ : Graph α β} (hN : N ≤ G)
    {c : (pathComb γ L).verts → α} (hc : Injective c)
    {P : (pathComb γ L).coe.edgeSet → Graph α β}
    (hV : V(N) = range c ∪ ⋃ e, V(P e)) (hE : E(N) = ⋃ e, E(P e))
    (hPaths : ∀ e : (pathComb γ L).coe.edgeSet, ∃ a b, e.val = s(a,b) ∧
      (pathComb γ L).coe.Adj a b ∧ IsGraphPathWithEnds N (P e) (c a) (c b) ∧
      V(P e) ∩ range c = {c a,c b})
    (hInter : ∀ e f : (pathComb γ L).coe.edgeSet, e ≠ f →
      V(P e) ∩ V(P f) ⊆ range c)
    (root : α) (hR : IsGraphPathWithEnds G R root (c (rootedPathComb γ L hL).root))
    (hmeetR : V(N) ∩ V(R) ⊆ {c (rootedPathComb γ L hL).root})
    (i k : Fin n) (hik : i.val + 2 ≤ k.val) {a b : α}
    (ha : a ∈ combBlock hL (subgraphUnion G N R) c i)
    (hb : b ∈ combBlock hL (subgraphUnion G N R) c k)
    (hP₀ : IsGraphPathWithEnds G P₀ a b)
    (hmeetP : V(P₀) ∩ V(subgraphUnion G N R) = {a,b}) :
    ∃ t ∈ combBlock hL (subgraphUnion G N R) c (⟨n - 1, by omega⟩ : Fin n),
      ∃ Q : Graph α β, IsGraphPathWithEnds G Q a t ∧
        Disjoint V(Q) ((⋃ j : Fin n, ⋃ (_ : j < i), combBlock hL (subgraphUnion G N R) c j) ∪
          combBlock hL (subgraphUnion G N R) c (⟨i.val + 1, by omega⟩ : Fin n)) ∧
        V(Q) ∩ combBlock hL (subgraphUnion G N R) c (⟨n - 1, by omega⟩ : Fin n) = {t} := by
  let H := subgraphUnion G N R
  let F := fun q ↦ if q < n then combSpineRegion hL H c (2 * q) else ∅
  have hcentres : ∀ v, c v ∈ V(N) := by
    intro v
    rw [hV]
    exact Or.inl (mem_range_self v)
  have hPN : ∀ e, P e ≤ N := by
    intro e
    obtain ⟨_, _, _, _, hP, _⟩ := hPaths e
    exact hP.le
  have hRanges : ∀ e : (pathComb γ L).coe.edgeSet, ∃ a b, e.val = s(a,b) ∧
      V(P e) ∩ range c = {c a,c b} := by
    intro e
    obtain ⟨a, b, he, _, _, hRange⟩ := hPaths e
    exact ⟨a, b, he, hRange⟩
  have hNconn := subdivision_connected (pathComb_connected (γ := γ) hL).coe
    (rootedPathComb γ L hL).root N c P hV (fun e ↦ by
      obtain ⟨a, b, he, hab, hP, _⟩ := hPaths e
      exact ⟨a, b, he, hab, hP⟩)
  have hHconn : GraphConnected H := graphConnected_subgraphUnion hN hR.le hNconn
    (graphConnected_of_isGraphPath hR) ⟨_, hcentres _, hR.right_mem⟩
  have hcentresH : ∀ v, c v ∈ V(H) := fun v ↦ Or.inl (hcentres v)
  have hreg := combSpineRegion_antitone hL hN hR.le hc hcentres hPN hE hRanges hInter hmeetR
  have hF : Antitone F := by
    intro q q' hqq
    by_cases hq' : q' < n
    · have hq : q < n := lt_of_le_of_lt hqq hq'
      simp only [F, hq, hq', ↓reduceIte]
      exact hreg (Nat.mul_le_mul_left 2 hqq)
    · simp only [F, hq', ↓reduceIte]
      exact empty_subset _
  have hzero : F 0 = V(H) := by
    have hn : 0 < n := by omega
    simp only [F, hn, ↓reduceIte, Nat.mul_zero, combSpineRegion_zero]
  let t := c (⟨Sum.inl ⟨L - 1, by omega⟩, pathComb_spine_mem γ L _⟩ : (pathComb γ L).verts)
  have hq : i.val + 2 < n := by omega
  have htailRegion := combSpineRegion_connected hL hHconn hc hcentresH (2 * (i.val + 2))
    (by omega : 2 * (i.val + 2) < L)
  have hconnTail : GraphConnected (H.induce (F (i.val + 2))) := by
    simpa only [F, hq, ↓reduceIte] using htailRegion.1
  have htTail : t ∈ F (i.val + 2) := by
    simpa only [F, hq, ↓reduceIte] using htailRegion.2
  obtain ⟨Q, hQ, hQavoid⟩ := exists_ordered_block_extension (subgraphUnion_le hN hR.le)
    F hF hzero i k hik ha hb hP₀ hmeetP hconnTail htTail
  have hlastRegion := (combSpineRegion_connected hL hHconn hc hcentresH (2 * (n - 1))
    (by omega : 2 * (n - 1) < L)).2
  have hnlt : n - 1 < n := by omega
  have hnnot : ¬ n - 1 + 1 < n := by omega
  have htLast : t ∈ combBlock hL H c (⟨n - 1, by omega⟩ : Fin n) := by
    simpa only [combBlock, orderedRegionBlock, hnlt, hnnot, ↓reduceIte, sdiff_empty] using hlastRegion
  obtain ⟨t', ⟨_, ht'⟩, Q', hQ'Q, hQ', hMeet, _⟩ :=
    hQ.exists_first_hit ⟨t, hQ.right_mem, htLast⟩
  exact ⟨t', ht', Q', hQ'.mono hQ.le, hQavoid.mono_left hQ'Q.vertexSet_mono, hMeet⟩

end GraphMinor.GM01
