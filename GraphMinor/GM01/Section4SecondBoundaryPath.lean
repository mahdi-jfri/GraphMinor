module

public import GraphMinor.GM01.Section4NotLastLayer
public import GraphMinor.GM01.CombLateBoundaryVertices
import GraphMinor.GM01.CombLayerMiddle
import GraphMinor.GM01.ConnectedBoundaryPaths
import GraphMinor.GM01.Section4CombAttachment
import GraphMinor.GM01.SubdivisionConnected

/-!
# The second path from the layer subdivision to a boundary

Graph Minors I, (4.11), page 58, extends the attachment from (4.7) to
the vertex `w_2` just inside the late block range. Result (4.10) makes
this boundary available. The middle part of `H` is connected and
contains the adjacent cut centre. Extend through its boundary edge,
join the two paths, and trim the resulting path to its first vertex
of `D`, as chosen in the sentence following (4.11).
-/

public section

namespace GraphMinor.GM01

open Set Graph SimpleGraph Function GraphMinor.GM09

universe u v

/-- Graph Minors I, (4.11), page 58:
"There is a path $P_2$ from $D$ to $w_2$ avoiding $A \cup B - \{w_2\}$."
The conclusion also constructs the late boundary vertex with its
printed block and adjacency conditions, and makes the following
minimal first-hit choice explicit. Result (4.10) is proved and used,
not assumed as an extra hypothesis. -/
theorem theorem_4_11_proof {α : Type u} {β : Type v} {γ δ L n : ℕ}
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
    {m : ℕ} (hm : m = 2 + 4 * ν + 2 * δ) (D : Graph α β) (hDG : D ≤ G.graph)
    (hDW : V(D) ⊆ separatorLayer G.graph G.root.val Y i)
    {cD : (pathComb (γ - 1) m).verts → α} (hcD : Injective cD)
    (PD : (pathComb (γ - 1) m).coe.edgeSet → Graph α β)
    (hVD : V(D) = range cD ∪ ⋃ e, V(PD e))
    (hDPaths : ∀ e : (pathComb (γ - 1) m).coe.edgeSet, ∃ a b, e.val = s(a,b) ∧
      IsGraphPathWithEnds D (PD e) (cD a) (cD b) ∧ V(PD e) ∩ range cD = {cD a,cD b})
    (hDInter : ∀ e f : (pathComb (γ - 1) m).coe.edgeSet, e ≠ f →
      V(PD e) ∩ V(PD f) ⊆ range cD ∧ Disjoint E(PD e) E(PD f))
    (d₁ : V(D)) (P₁ : Graph α β)
    (hP₁ : IsGraphPathWithEnds G.graph P₁ d₁.val
      (firstLayerBoundary G c ν i.val (by omega) (by
        have hm' := Nat.mul_le_mul_left ν (show i.val - 1 ≤ T by omega)
        omega)))
    (hP₁D : V(P₁) ∩ V(D) = {d₁.val})
    (hAvoidP₁ :
      let S := fun k : Fin n ↦ combBlock hL (subgraphUnion G.graph N R) c k
      let hbound : 2 * (ν * (i.val - 1)) ≤ L := by
        have hm' := Nat.mul_le_mul_left ν (show i.val - 1 ≤ T by omega)
        omega
      let w := firstLayerBoundary G c ν i.val (by omega) hbound
      Disjoint V(P₁) ((layerLateBlocks S ν i.val ∪ layerEarlyBlocks S ν i.val) \ {w}))
    (hT : 2 ≤ T)
    (hmaxT : ∀ t : ℕ, 2 * ν * t ≤ L - 2 * δ → t ≤ T)
    (hmaxL : ∀ k (hk : 0 < k), HasRootedMinor (rootedPathComb (γ - 1) k hk) G → k ≤ L)
    (hGconn : GraphConnected G.graph) :
    let H := subgraphUnion G.graph N R
    let S := fun k : Fin n ↦ combBlock hL H c k
    let h2n : 2 * n ≤ L := by omega
    let cut := combBlockCutCentre hL h2n c
    ∃ k : Fin n, k.val + 1 = ν * (i.val + 1) ∧ ∃ w₂ ∈ S k,
      cut k ∈ S (⟨k.val - 1, by omega⟩ : Fin n) ∧ H.Adj (cut k) w₂ ∧
      ∃ d₂ ∈ V(D), ∃ P₂ : Graph α β, IsGraphPathWithEnds G.graph P₂ d₂ w₂ ∧
        Disjoint V(P₂) ((layerLateBlocks S ν i.val ∪ layerEarlyBlocks S ν i.val) \ {w₂}) ∧
        V(P₂) ∩ V(D) = {d₂} := by
  classical
  have hnotLast := theorem_4_10_proof hγ hδ hL htail G hno hN hc hV hE hPaths hInter hR hmeetR
    hν left right hleft hright Y hY hn i hm D hDG hDW hcD PD hVD hDPaths hDInter
    d₁ P₁ hP₁ hP₁D hAvoidP₁ hT hmaxT hmaxL
  have hiT : i.val < T := by omega
  let H := subgraphUnion G.graph N R
  let S := fun k : Fin n ↦ combBlock hL H c k
  let A := layerLateBlocks S ν i.val
  let B := layerEarlyBlocks S ν i.val
  have h2n : 2 * n ≤ L := by omega
  let cut := combBlockCutCentre hL h2n c
  change ∃ k : Fin n, k.val + 1 = ν * (i.val + 1) ∧ ∃ w₂ ∈ S k,
    cut k ∈ S (⟨k.val - 1, by omega⟩ : Fin n) ∧ H.Adj (cut k) w₂ ∧
    ∃ d₂ ∈ V(D), ∃ P₂ : Graph α β, IsGraphPathWithEnds G.graph P₂ d₂ w₂ ∧
      Disjoint V(P₂) ((A ∪ B) \ {w₂}) ∧ V(P₂) ∩ V(D) = {d₂}
  have hmul := Nat.mul_le_mul_left ν (Nat.succ_le_of_lt hiT)
  change ν * (i.val + 1) ≤ ν * T at hmul
  have hmulpos := Nat.mul_le_mul_left ν (Nat.succ_le_succ (Nat.zero_le i.val))
  change ν * 1 ≤ ν * (i.val + 1) at hmulpos
  simp only [Nat.mul_one] at hmulpos
  let q : Fin n := ⟨ν * (i.val + 1) - 1, by omega⟩
  have hq : q.val + 1 = ν * (i.val + 1) := by dsimp [q]; omega
  have hq2 : 2 ≤ q.val := by dsimp [q]; omega
  have hqnext : q.val + 1 < n := by omega
  have hcentres : ∀ v, c v ∈ V(N) := by
    intro v
    rw [hV]
    exact Or.inl (mem_range_self v)
  have hOnly : ∀ e : (pathComb (γ - 1) L).coe.edgeSet, ∃ a b, e.val = s(a,b) ∧
      IsGraphPathWithEnds N (P e) (c a) (c b) ∧ V(P e) ∩ range c = {c a,c b} := by
    intro e
    obtain ⟨a, b, he, _, hP, hRange⟩ := hPaths e
    exact ⟨a, b, he, hP, hRange⟩
  have hInterV := fun e f hne ↦ (hInter e f hne).1
  obtain ⟨w₂, hw₂, hAdj⟩ := exists_comb_late_boundary_vertex hL h2n hN hR.le hc hcentres P hE
    hOnly hInterV hmeetR q hq2 hqnext
  have hCutPrev := comb_cut_centre_mem_preceding_block hL h2n hN hR.le hc hcentres P hE hOnly hInterV hmeetR q hq2
  have hMid := comb_layer_middle_connected hL hν h2n hn G hN hc hV hE hPaths hInterV hR hmeetR i q hq
  obtain ⟨d, hd, x, hxH, Q, hQ, hQAvoid⟩ := theorem_4_7_proof hγ hδ hL htail G hno hN hc hV hE
    hPaths hInter hR hmeetR hν left right hleft hright Y hY hn i hGconn (by omega) D ⟨d₁.val, d₁.property⟩ hDW
  have hxMid : x ∈ V(H) \ (A ∪ B) := ⟨hxH, fun h ↦ Set.disjoint_left.mp hQAvoid hQ.right_mem h⟩
  obtain ⟨Q', hQ', hQ'Avoid⟩ := exists_avoiding_path_across_boundary_edge (G := H)
    (C := V(H) \ (A ∪ B)) (F := A ∪ B) Subset.rfl hMid.1 hMid.2 hAdj hxMid
  have hHG : H ≤ G.graph := subgraphUnion_le hN hR.le
  have hQ'G := hQ'.mono hHG
  let K := subgraphUnion G.graph Q Q'
  have hKconn : GraphConnected K := graphConnected_subgraphUnion hQ.le hQ'G.le
    (graphConnected_of_isGraphPath hQ) (graphConnected_of_isGraphPath hQ'G)
    ⟨x, hQ.right_mem, hQ'G.left_mem⟩
  have hdK : d ∈ V(K) := Or.inl hQ.left_mem
  have hwK : w₂ ∈ V(K) := Or.inr hQ'G.right_mem
  obtain ⟨P₂, hP₂⟩ := exists_path_of_adj_reachable hdK (hKconn.2 d hdK w₂ hwK)
  have hKG : K ≤ G.graph := subgraphUnion_le hQ.le hQ'G.le
  have hP₂G := hP₂.mono hKG
  have hAvoid : Disjoint V(P₂) ((A ∪ B) \ {w₂}) := by
    apply Set.disjoint_left.mpr
    intro z hz hzCut
    rcases hP₂.le.vertexSet_mono hz with hzQ | hzQ'
    · exact Set.disjoint_left.mp hQAvoid hzQ hzCut.1
    · exact Set.disjoint_left.mp hQ'Avoid hzQ' hzCut
  obtain ⟨d', hd', w', hw', P₂', hP₂'P₂, hP₂'⟩ := hP₂G.exists_isFromToPathWithEnds (X := V(D)) (Y := {w₂}) hd rfl
  have hww : w' = w₂ := hw'
  subst w'
  exact ⟨q, hq, w₂, hw₂, hCutPrev, hAdj, d', hd', P₂', hP₂'.1,
    hAvoid.mono_left hP₂'P₂.vertexSet_mono, hP₂'.2.1⟩

end GraphMinor.GM01
