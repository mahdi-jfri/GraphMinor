module

public import GraphMinor.GM01.Section4CombAttachment
public import GraphMinor.GM01.CombFirstBoundaryPaths
import GraphMinor.GM01.SubdivisionConnected

/-!
# The first path from the layer subdivision to a boundary

Graph Minors I, (4.8), page 58, extends the attachment path from (4.7)
along the subdivided comb to the first boundary vertex. Both parts
avoid the early and late blocks, except that the target itself may
belong to the early blocks. Extracting a path from their connected
union gives the required first path.
-/

public section

namespace GraphMinor.GM01

open Set Graph SimpleGraph Function GraphMinor.GM09

universe u v

/-- Graph Minors I, (4.8), page 58:
"There is a path $P_1$ in $G$ from $D$ to $w_1$, avoiding $A \cup B - \{w_1\}$."
The first path is obtained from proved (4.7) and the boundary extension
inside `H`. The bound ensuring the boundary vertex exists is derived
from the paper's tail inequality, not assumed. -/
theorem theorem_4_8_proof {α : Type u} {β : Type v} {γ δ L n : ℕ}
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
    let hbound : 2 * (ν * (i.val - 1)) ≤ L := by
      have hm := Nat.mul_le_mul_left ν (show i.val - 1 ≤ T by omega)
      omega
    let w := firstLayerBoundary G c ν i.val (by omega) hbound
    ∃ d ∈ V(D), ∃ P₁ : Graph α β, IsGraphPathWithEnds G.graph P₁ d w ∧
      Disjoint V(P₁) ((layerLateBlocks S ν i.val ∪ layerEarlyBlocks S ν i.val) \ {w}) := by
  let H := subgraphUnion G.graph N R
  let S := fun k : Fin n ↦ combBlock hL H c k
  let A := layerLateBlocks S ν i.val
  let B := layerEarlyBlocks S ν i.val
  have hbound : 2 * (ν * (i.val - 1)) ≤ L := by
    have hm := Nat.mul_le_mul_left ν (show i.val - 1 ≤ T by omega)
    omega
  let w := firstLayerBoundary G c ν i.val (by omega : 0 < ν) hbound
  change ∃ d ∈ V(D), ∃ P₁ : Graph α β, IsGraphPathWithEnds G.graph P₁ d w ∧
    Disjoint V(P₁) ((A ∪ B) \ {w})
  obtain ⟨d, hd, s, hsH, Q, hQ, hQAvoid⟩ := theorem_4_7_proof hγ hδ hL htail G hno hN hc hV hE
    hPaths hInter hR hmeetR hν left right hleft hright Y hY hn i hGconn hT D hD hDW
  have hsAvoid : s ∉ A ∪ B := fun h ↦ Set.disjoint_left.mp hQAvoid hQ.right_mem h
  have h2n : 2 * n ≤ L := by omega
  obtain ⟨Q', hQ', hQ'Avoid⟩ := exists_comb_first_boundary_path hL hν h2n hn G hN hc
    hV hE hPaths (fun e f hne ↦ (hInter e f hne).1) hR hmeetR i hbound hsH hsAvoid
  have hHG : H ≤ G.graph := subgraphUnion_le hN hR.le
  have hQ'G := hQ'.mono hHG
  have hQCut : Disjoint V(Q) ((A ∪ B) \ {w}) := hQAvoid.mono_right sdiff_subset
  let K := subgraphUnion G.graph Q Q'
  have hK : GraphConnected K := graphConnected_subgraphUnion hQ.le hQ'G.le
    (graphConnected_of_isGraphPath hQ) (graphConnected_of_isGraphPath hQ'G)
    ⟨s, hQ.right_mem, hQ'G.left_mem⟩
  have hdK : d ∈ V(K) := Or.inl hQ.left_mem
  have hwK : w ∈ V(K) := Or.inr hQ'G.right_mem
  obtain ⟨P₁, hP₁⟩ := exists_path_of_adj_reachable hdK (hK.2 d hdK w hwK)
  have hKG : K ≤ G.graph := subgraphUnion_le hQ.le hQ'G.le
  refine ⟨d, hd, P₁, hP₁.mono hKG, ?_⟩
  apply Set.disjoint_left.mpr
  intro x hx hxCut
  rcases hP₁.le.vertexSet_mono hx with hxQ | hxQ'
  · exact Set.disjoint_left.mp hQCut hxQ hxCut
  · exact Set.disjoint_left.mp hQ'Avoid hxQ' hxCut

/-- The minimal first-hit choice following GM01 (4.8), page 58. Trim
the boundary path so that its sole vertex in `D` is its initial end.
The path keeps the avoidance property of (4.8). -/
theorem exists_first_boundary_path_with_single_D_vertex {α : Type u} {β : Type v} {γ δ L n : ℕ}
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
    let hbound : 2 * (ν * (i.val - 1)) ≤ L := by
      have hm := Nat.mul_le_mul_left ν (show i.val - 1 ≤ T by omega)
      omega
    let w := firstLayerBoundary G c ν i.val (by omega) hbound
    ∃ d ∈ V(D), ∃ P₁ : Graph α β, IsGraphPathWithEnds G.graph P₁ d w ∧
      Disjoint V(P₁) ((layerLateBlocks S ν i.val ∪ layerEarlyBlocks S ν i.val) \ {w}) ∧
        V(P₁) ∩ V(D) = {d} := by
  let H := subgraphUnion G.graph N R
  let S := fun k : Fin n ↦ combBlock hL H c k
  let A := layerLateBlocks S ν i.val
  let B := layerEarlyBlocks S ν i.val
  have hbound : 2 * (ν * (i.val - 1)) ≤ L := by
    have hm := Nat.mul_le_mul_left ν (show i.val - 1 ≤ T by omega)
    omega
  let w := firstLayerBoundary G c ν i.val (by omega : 0 < ν) hbound
  change ∃ d ∈ V(D), ∃ P₁ : Graph α β, IsGraphPathWithEnds G.graph P₁ d w ∧
    Disjoint V(P₁) ((A ∪ B) \ {w}) ∧ V(P₁) ∩ V(D) = {d}
  obtain ⟨d, hd, Q, hQ, hAvoid⟩ := theorem_4_8_proof hγ hδ hL htail G hno hN hc hV hE
    hPaths hInter hR hmeetR hν left right hleft hright Y hY hn i hGconn hT D hD hDW
  obtain ⟨d', hd', w', hw', P₁, hP₁Q, hP₁⟩ :=
    hQ.exists_isFromToPathWithEnds (X := V(D)) (Y := {w}) hd rfl
  have hww : w' = w := hw'
  subst w'
  exact ⟨d', hd', P₁, hP₁.1, hAvoid.mono_left hP₁Q.vertexSet_mono, hP₁.2.1⟩

end GraphMinor.GM01
