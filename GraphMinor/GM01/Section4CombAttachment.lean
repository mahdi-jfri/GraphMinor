module

public import GraphMinor.GM01.Section4LayerDisjointness
public import GraphMinor.GM01.LayerAttachmentPaths
public import GraphMinor.GM01.OrderedBlockWindows
import GraphMinor.GM01.SubdivisionConnected
import GraphMinor.GM01.CombPrefixes

/-!
# Joining a layer component to the subdivided comb

Graph Minors I, (4.7), page 58, joins the chosen subdivision in a layer
to the original comb graph while avoiding the early and late blocks.
For the first layer, take an avoiding path to the root. For any later
layer, first follow a path within that layer to its preceding sampled
separator, then follow its attachment window to a block. Both paths
avoid the early and late sets. Their connected union supplies a path.
-/

public section

namespace GraphMinor.GM01

open Set Graph SimpleGraph Function Relation GraphMinor.GM09

universe u v

/-- Graph Minors I, (4.7), page 58:
"There is a path in $G$ from $V(D)$ to $V(H)$ avoiding $A \cup B$."
Only nonemptiness and containment in the layer are needed from the
chosen subdivision `D`. The proof follows the paper's two layer cases,
using the minimal separators of (4.3). -/
theorem theorem_4_7_proof {α : Type u} {β : Type v} {γ δ L n : ℕ}
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
    (hGconn : GraphConnected G.graph) (hT : 1 ≤ T)
    (D : Graph α β) (hD : V(D).Nonempty)
    (hDW : V(D) ⊆ separatorLayer G.graph G.root.val Y i) :
    let H := subgraphUnion G.graph N R
    let S := fun k : Fin n ↦ combBlock hL H c k
    ∃ d ∈ V(D), ∃ s ∈ V(H), ∃ P₀ : Graph α β,
      IsGraphPathWithEnds G.graph P₀ d s ∧
      Disjoint V(P₀) (layerLateBlocks S ν i.val ∪ layerEarlyBlocks S ν i.val) := by
  let H := subgraphUnion G.graph N R
  let S := fun k : Fin n ↦ combBlock hL H c k
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
  let A := layerLateBlocks S ν i.val
  let B := layerEarlyBlocks S ν i.val
  change ∃ d ∈ V(D), ∃ s ∈ V(H), ∃ P₀ : Graph α β,
    IsGraphPathWithEnds G.graph P₀ d s ∧ Disjoint V(P₀) (A ∪ B)
  obtain ⟨d, hd⟩ := hD
  have hdW := hDW hd
  have hrootH : G.root.val ∈ V(H) := Or.inr hR.left_mem
  have hSG : ∀ k, S k ⊆ V(G.graph) := fun k ↦
    (combBlock_subset_graph hL H c k).trans (subgraphUnion_le hN hR.le).vertexSet_mono
  by_cases hi0 : i.val = 0
  · let a : Fin T := ⟨0, by omega⟩
    have ha : a.val = i.val := hi0.symm
    obtain ⟨d', hd', r', hr', Q, hQ, hAvoid⟩ :=
      not_graphSeparates_iff.mp (hdW.2.2 a ha)
    have hdd : d' = d := hd'
    have hrr : r' = G.root.val := hr'
    subst d'
    subst r'
    refine ⟨d, hd, G.root.val, hrootH, Q, hQ, ?_⟩
    have hNoSep := not_separated_vertices_of_avoiding_root_path hQ hAvoid
    apply Set.disjoint_left.mpr
    intro x hx hxAB
    rcases hxAB with hxA | hxB
    · obtain ⟨k, hk, hxk⟩ := Set.mem_iUnion₂.mp hxA
      have hrak : right a ≤ k := by
        have hra := hright a
        change (right a).val ≤ k.val
        change ν * (i.val + 1) ≤ k.val + 1 at hk
        rw [hi0, Nat.zero_add, Nat.mul_one] at hk
        change (right a).val + 1 = ν * (0 + 1) at hra
        rw [Nat.zero_add, Nat.mul_one] at hra
        omega
      have hsep := (theorem_4_4_proof hγ hδ hL htail G hno hN hc hV hE hPaths hInter hR hmeetR
        ν hν (left a) (right a) (hwindow a) (hY a) k hxk).1 hrak
      exact hNoSep x hx hsep
    · obtain ⟨k, hk, _⟩ := Set.mem_iUnion₂.mp hxB
      change k.val + 1 ≤ ν * (i.val - 1) at hk
      rw [hi0, Nat.zero_sub, Nat.mul_zero] at hk
      omega
  · have hipos : 0 < i.val := by omega
    let a : Fin T := ⟨i.val - 1, by omega⟩
    have ha : a.val + 1 = i.val := by dsimp [a]; omega
    obtain ⟨y, hy, Q, hQ, hQW⟩ := exists_path_in_layer_to_preceding_separator
      hGconn G.root.property Y hipos hdW
    have hyY : y ∈ Y a := hy
    have hlocal := theorem_4_3_proof hγ hδ hL htail G hno hN hc hV hE hPaths hInter hR hmeetR
      ν hν (left a) (right a) (hwindow a) (hY a) hyY
    have hlr : left a ≤ right a := by
      have hw := hwindow a
      change (left a).val ≤ (right a).val
      omega
    obtain ⟨k, hlk, hkr, s, hs, Q', hQ', hQ'Window⟩ :=
      exists_path_in_blockAttachmentWindow hSG hlr hlocal
    have hdis := theorem_4_6_proof hγ hδ hL htail G hno hN hc hV hE hPaths hInter hR hmeetR
      hν left right hleft hright Y hY hn i
    have hWAvoid : Disjoint (separatorLayer G.graph G.root.val Y i) (A ∪ B) :=
      Set.disjoint_union_right.mpr ⟨hdis.2.1.symm, hdis.2.2.symm⟩
    have hWindowAvoid : Disjoint (blockAttachmentWindow G.graph S (left a) (right a))
        (A ∪ B) := by
      apply (disjoint_blockAttachmentWindow_outside_blocks S hSG hpart.1 (left a) (right a) hlr).mono_right
      intro x hx
      rcases hx with hxA | hxB
      · obtain ⟨k, hk, hxk⟩ := Set.mem_iUnion₂.mp hxA
        have hra := hright a
        rw [ha] at hra
        change ν * (i.val + 1) ≤ k.val + 1 at hk
        rw [Nat.mul_add, Nat.mul_one] at hk
        have hrk : right a < k := by change (right a).val < k.val; omega
        exact Set.mem_iUnion₂.mpr ⟨k, Or.inr hrk, hxk⟩
      · obtain ⟨k, hk, hxk⟩ := Set.mem_iUnion₂.mp hxB
        have hla : (left a).val = ν * (i.val - 1) := hleft a
        change k.val + 1 ≤ ν * (i.val - 1) at hk
        have hkl : k < left a := by change k.val < (left a).val; omega
        exact Set.mem_iUnion₂.mpr ⟨k, Or.inl hkl, hxk⟩
    have hQAvoid := hWAvoid.mono_left hQW
    have hQ'Avoid := hWindowAvoid.mono_left hQ'Window
    let K := subgraphUnion G.graph Q Q'
    have hK : GraphConnected K := graphConnected_subgraphUnion hQ.le hQ'.le
      (graphConnected_of_isGraphPath hQ) (graphConnected_of_isGraphPath hQ')
      ⟨y, hQ.right_mem, hQ'.left_mem⟩
    have hdK : d ∈ V(K) := Or.inl hQ.left_mem
    have hsK : s ∈ V(K) := Or.inr hQ'.right_mem
    obtain ⟨P₀, hP₀⟩ := exists_path_of_adj_reachable hdK (hK.2 d hdK s hsK)
    have hKG : K ≤ G.graph := subgraphUnion_le hQ.le hQ'.le
    refine ⟨d, hd, s, combBlock_subset_graph hL H c k hs, P₀, hP₀.mono hKG, ?_⟩
    apply Set.disjoint_left.mpr
    intro x hx hxAB
    rcases hP₀.le.vertexSet_mono hx with hxQ | hxQ'
    · exact Set.disjoint_left.mp hQAvoid hxQ hxAB
    · exact Set.disjoint_left.mp hQ'Avoid hxQ' hxAB

end GraphMinor.GM01
