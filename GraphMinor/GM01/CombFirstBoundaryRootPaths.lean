module

public import GraphMinor.GM01.CombFirstBoundaryPaths
import GraphMinor.GM01.CombPrefixRoot
import GraphMinor.GM01.PathCombTrees
import GraphMinor.GM01.SubdivisionConnected

/-!
# The root path before the first boundary

After Graph Minors I, (4.8), page 58, `P_0` is the path in `H` from
`w_1` to the root. In layers zero and one, it is the one-vertex root
path. Otherwise both ends lie in the connected early prefix, which is
exactly `B`, so the path is wholly in `B`. This gives its disjointness
from the layer subdivision in the contraction proving (4.9).
-/

public section

namespace GraphMinor.GM01

open Set Graph SimpleGraph Function GraphMinor.GM09 GraphMinor.Surface

/-- The path `P_0` defined after GM01 (4.8), page 58, with its location
in the early block set made explicit for the contraction in (4.9). -/
theorem exists_root_path_to_first_layer_boundary {α β : Type*} {γ L n T ν : ℕ}
    (hL : 0 < L) (hν : 3 ≤ ν) (h2n : 2 * n ≤ L) (hn : n = ν * T + 1)
    (G : RootedGraph α β) {N R : Graph α β} (hN : N ≤ G.graph)
    {c : (pathComb γ L).verts → α} (hc : Injective c)
    {P : (pathComb γ L).coe.edgeSet → Graph α β}
    (hV : V(N) = range c ∪ ⋃ e, V(P e)) (hE : E(N) = ⋃ e, E(P e))
    (hPaths : ∀ e : (pathComb γ L).coe.edgeSet, ∃ a b, e.val = s(a,b) ∧
      (pathComb γ L).coe.Adj a b ∧ IsGraphPathWithEnds N (P e) (c a) (c b) ∧
      V(P e) ∩ range c = {c a,c b})
    (hInter : ∀ e f : (pathComb γ L).coe.edgeSet, e ≠ f → V(P e) ∩ V(P f) ⊆ range c)
    (hR : IsGraphPathWithEnds G.graph R G.root.val (c (rootedPathComb γ L hL).root))
    (hmeetR : V(N) ∩ V(R) ⊆ {c (rootedPathComb γ L hL).root})
    (i : Fin (T + 1)) (hbound : 2 * (ν * (i.val - 1)) ≤ L) :
    let S := fun k : Fin n ↦ combBlock hL (subgraphUnion G.graph N R) c k
    let w := firstLayerBoundary G c ν i.val (by omega) hbound
    ∃ P₀ : Graph α β, IsGraphPathWithEnds G.graph P₀ G.root.val w ∧
      V(P₀) ⊆ if i.val ≤ 1 then {G.root.val} else layerEarlyBlocks S ν i.val := by
  let H := subgraphUnion G.graph N R
  let S := fun k : Fin n ↦ combBlock hL H c k
  let w := firstLayerBoundary G c ν i.val (by omega : 0 < ν) hbound
  change ∃ P₀ : Graph α β, IsGraphPathWithEnds G.graph P₀ G.root.val w ∧
    V(P₀) ⊆ if i.val ≤ 1 then {G.root.val} else layerEarlyBlocks S ν i.val
  by_cases hiSmall : i.val ≤ 1
  · have hw : w = G.root.val := by simp only [w, firstLayerBoundary, hiSmall, ↓reduceDIte]
    obtain ⟨P₀, hP₀, hV₀, _⟩ := exists_isGraphPathWithEnds_of_walk (GraphWalk.nil G.root.property)
    refine ⟨P₀, hw.symm ▸ hP₀, ?_⟩
    simp only [hiSmall, ↓reduceIte]
    intro x hx
    simpa only [Set.mem_ofPred_eq, GraphWalk.support_nil, List.mem_singleton, Set.mem_singleton_iff] using hV₀ hx
  · have hcentres : ∀ v, c v ∈ V(N) := by
      intro v
      rw [hV]
      exact Or.inl (mem_range_self v)
    have hPN : ∀ e, P e ≤ N := by
      intro e
      obtain ⟨_, _, _, _, hPath, _⟩ := hPaths e
      exact hPath.le
    have hRanges : ∀ e : (pathComb γ L).coe.edgeSet, ∃ a b, e.val = s(a,b) ∧
        V(P e) ∩ range c = {c a,c b} := by
      intro e
      obtain ⟨a, b, he, _, _, hRange⟩ := hPaths e
      exact ⟨a, b, he, hRange⟩
    have hreg := combSpineRegion_antitone hL hN hR.le hc hcentres hPN hE hRanges hInter hmeetR
    have hNconn := subdivision_connected (pathComb_connected (γ := γ) hL).coe
      (rootedPathComb γ L hL).root N c P hV (fun e ↦ by
        obtain ⟨a, b, he, hab, hP, _⟩ := hPaths e
        exact ⟨a, b, he, hab, hP⟩)
    have hHconn : GraphConnected H := graphConnected_subgraphUnion hN hR.le hNconn
      (graphConnected_of_isGraphPath hR) ⟨_, hcentres _, hR.right_mem⟩
    have hcentresH : ∀ v, c v ∈ V(H) := fun v ↦ Or.inl (hcentres v)
    have hpT : ν * (i.val - 1) ≤ ν * T := Nat.mul_le_mul_left ν (by omega)
    let p : Fin n := ⟨ν * (i.val - 1), by omega⟩
    have hp : 0 < p.val := Nat.mul_pos (by omega) (by omega)
    have hpL : 2 * p.val < L := by have hpn := p.isLt; omega
    have hB := layerEarlyBlocks_eq_combPrefix hL H c hreg ν i.val p rfl
    have hconn := (combPrefix_connected hL hHconn c hcentresH p.val hp hpL).1
    have hcut := (combPrefix_connected hL hHconn c hcentresH p.val hp hpL).2
    have hroot := root_mem_combPrefix hL hN hc hcentres hPN hE hRanges hInter
      G.root.val hR hmeetR p.val hp hpL
    have hw : w ∈ combPrefix hL H c p.val := by
      simpa only [w, firstLayerBoundary, hiSmall, ↓reduceDIte] using hcut
    obtain ⟨P₀, hP₀⟩ := exists_path_of_adj_reachable hroot (hconn.2 G.root.val hroot w hw)
    have hle : H.induce (combPrefix hL H c p.val) ≤ G.graph :=
      (H.induce_le sdiff_subset).trans (subgraphUnion_le hN hR.le)
    refine ⟨P₀, hP₀.mono hle, ?_⟩
    simp only [hiSmall, ↓reduceIte]
    have hB' : layerEarlyBlocks S ν i.val = combPrefix hL H c p.val := hB
    rw [hB']
    exact hP₀.le.vertexSet_mono

end GraphMinor.GM01
