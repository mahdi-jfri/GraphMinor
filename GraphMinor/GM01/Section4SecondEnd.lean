module

public import GraphMinor.GM01.Section4SecondBoundaryPath
import GraphMinor.GM01.SecondEndForkAssembly
import GraphMinor.GM01.CombFinalBlockPaths
import GraphMinor.GM01.CombFirstBoundaryRootPaths
import GraphMinor.GM01.CombLastBlockMinor
import GraphMinor.GM01.CombBlockConnectivity
import GraphMinor.GM01.CombLayerBlockSets
import GraphMinor.GM01.RootedCombMinor
import GraphMinor.GM01.CombPrefixRoot
import GraphMinor.GM01.PathLastEdgeCover
import GraphMinor.GM01.PathCombTrees
import GraphMinor.GM01.SubdivisionConnected

/-!
# The second attachment lies in the second end

Graph Minors I, (4.12), page 59, keeps the second end as a binary
arm and the final block as a comb arm. If the second attachment misses
that end, the rest of the subdivision and the first three paths form
a connected root piece. The final path and the boundary replacing
path attach the two arms, giving the excluded rooted fork.
-/

public section

namespace GraphMinor.GM01

open Set Graph SimpleGraph Function GraphMinor.GM09 GraphMinor.Surface

universe u v

/-- Graph Minors I, (4.12), page 59:
"$d_2$ *is in the second end of* $D$."
The first attachment is in the first end, in the orientation chosen
after (4.9). The maximality conditions are the actual choices from
page 55 and are used through proved (4.10). -/
theorem theorem_4_12_proof {α : Type u} {β : Type v} {γ δ L n : ℕ}
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
    (hfirst : d₁.val ∈ combFirstEndSupport (by omega) cD PD)
    (q : Fin n) (hq : q.val + 1 = ν * (i.val + 1))
    (w₂ : α) (hw₂ : w₂ ∈ combBlock hL (subgraphUnion G.graph N R) c q)
    (d₂ : V(D)) (P₂ : Graph α β) (hP₂ : IsGraphPathWithEnds G.graph P₂ d₂.val w₂)
    (hAvoidP₂ :
      let S := fun k : Fin n ↦ combBlock hL (subgraphUnion G.graph N R) c k
      Disjoint V(P₂) ((layerLateBlocks S ν i.val ∪ layerEarlyBlocks S ν i.val) \ {w₂}))
    (hP₂D : V(P₂) ∩ V(D) = {d₂.val}) :
    d₂.val ∈ combSecondEndSupport (by omega) cD PD := by
  classical
  by_contra hsecond
  have hnotLast := theorem_4_10_proof hγ hδ hL htail G hno hN hc hV hE hPaths hInter hR hmeetR
    hν left right hleft hright Y hY hn i hm D hDG hDW hcD PD hVD hDPaths hDInter
    d₁ P₁ hP₁ hP₁D hAvoidP₁ hT hmaxT hmaxL
  have hiT : i.val < T := by omega
  have hmul := Nat.mul_le_mul_left ν (Nat.succ_le_of_lt hiT)
  change ν * (i.val + 1) ≤ ν * T at hmul
  have hqnext : q.val + 1 < n := by omega
  have hqpos : 0 < q.val := by
    have hh := Nat.mul_le_mul_left ν (Nat.succ_le_succ (Nat.zero_le i.val))
    change ν * 1 ≤ ν * (i.val + 1) at hh
    simp only [Nat.mul_one] at hh
    omega
  have h2n : 2 * n ≤ L := by omega
  let H := subgraphUnion G.graph N R
  let S := fun k : Fin n ↦ combBlock hL H c k
  let A := layerLateBlocks S ν i.val
  let B := layerEarlyBlocks S ν i.val
  let last : Fin n := ⟨n - 1, by omega⟩
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
  have hpart := (combBlock_partition hL (by omega : 0 < n) hN hR.le hc hcentres hPN hE
    hRanges hInterV hmeetR).1
  have hdis := theorem_4_6_proof hγ hδ hL htail G hno hN hc hV hE hPaths hInter hR hmeetR
    hν left right hleft hright Y hY hn i
  have hAD : Disjoint A V(D) := hdis.2.1.mono_right hDW
  have hBD : Disjoint B V(D) := hdis.2.2.mono_right hDW
  have hLastA : S last ⊆ A := by
    intro x hx
    exact Set.mem_iUnion₂.mpr ⟨last, by change ν * (i.val + 1) ≤ n - 1 + 1; omega, hx⟩
  have hAw : A = combSpineRegion hL H c (2 * q.val) :=
    layerLateBlocks_eq_combSpineRegion hL H c hreg ν i.val q hq
  have hwRegion : w₂ ∈ combSpineRegion hL H c (2 * q.val) := by
    simpa only [combBlock, orderedRegionBlock, q.isLt, ↓reduceIte] using hw₂.1
  obtain ⟨t, htLast, P₃, hP₃, hP₃reg, hP₃Last⟩ := exists_path_to_final_combBlock hL
    (by omega : 0 < n) h2n hHconn hc hcentresH q hwRegion
  have hP₃A : V(P₃) ⊆ A := hAw.symm ▸ hP₃reg
  have hConnLast := combBlock_connected hL h2n hN hc hV hPaths hInterV hE
    G.root.val hR hmeetR last
  let GP : RootedGraph α β := ⟨H.induce (S last), ⟨t, htLast⟩⟩
  have hGP : GP.graph ≤ G.graph := (H.induce_le (combBlock_subset_graph hL H c last)).trans hHG
  let u : (pathComb (γ - 1) L).verts := ⟨Sum.inl ⟨0, by omega⟩, pathComb_spine_mem _ _ _⟩
  let v : (pathComb (γ - 1) L).verts := ⟨Sum.inl ⟨1, by omega⟩, pathComb_spine_mem _ _ _⟩
  have huv : (pathComb (γ - 1) L).coe.Adj u v := pathComb_spine_adj
    (γ := γ - 1) (pathGraph_adj.mpr (Or.inl rfl))
  let edge : (pathComb (γ - 1) L).coe.edgeSet := ⟨s(u,v), huv⟩
  obtain ⟨x, y, _, hxy, hPath, _⟩ := hPaths edge
  obtain ⟨edgeLabel, _, _, _, _, _, _, _⟩ := exists_last_edge_with_vertex_cover hPath (fun h ↦ hxy.ne (hc h))
  let : Nonempty β := ⟨edgeLabel⟩
  obtain ⟨ηv, ηe, hTailModel⟩ := comb_lastBlock_minor_model (by omega : 2 ≤ n) h2n htail
    hN hc hcentres P hOnly hInter hE G.root.val hR hmeetR
  obtain ⟨MP⟩ := rootedPathComb_of_long_minor (by omega : 0 < δ - 1)
    (by omega : 2 * (δ - 1) + 1 ≤ 2 * δ) GP hConnLast hTailModel
  have hDGP : Disjoint V(D) V(GP.graph) := (hAD.mono_left hLastA).symm
  have hbound : 2 * (ν * (i.val - 1)) ≤ L := by
    have hh := Nat.mul_le_mul_left ν (show i.val - 1 ≤ T by omega)
    omega
  let w₁ := firstLayerBoundary G c ν i.val (by omega : 0 < ν) hbound
  have hP1 : IsGraphPathWithEnds G.graph P₁ d₁.val w₁ := hP₁
  obtain ⟨P₀, hP₀, hP₀loc⟩ := exists_root_path_to_first_layer_boundary hL hν h2n hn G hN hc
    hV hE hPaths hInterV hR hmeetR i hbound
  have hrootPrefix := root_mem_combPrefix hL hN hc hcentres hPN hE hRanges hInterV
    G.root.val hR hmeetR q.val hqpos (by have := q.isLt; omega)
  have hrootNotA : G.root.val ∉ A := by rw [hAw]; exact hrootPrefix.2
  have hP₀A : Disjoint V(P₀) A := by
    apply Set.disjoint_left.mpr
    intro x hx hxA
    by_cases hiSmall : i.val ≤ 1
    · have hloc : V(P₀) ⊆ {G.root.val} := by simpa only [hiSmall, ↓reduceIte] using hP₀loc
      have heq : x = G.root.val := hloc hx
      exact hrootNotA (heq ▸ hxA)
    · have hloc : V(P₀) ⊆ B := by simpa only [hiSmall, ↓reduceIte] using hP₀loc
      exact Set.disjoint_left.mp hdis.1 hxA (hloc hx)
  have hw₁NotA : w₁ ∉ A := fun h ↦ Set.disjoint_left.mp hP₀A hP₀.right_mem h
  have hP₁A : Disjoint V(P₁) A := by
    apply Set.disjoint_left.mpr
    intro x hx hxA
    exact Set.disjoint_left.mp hAvoidP₁ hx ⟨Or.inl hxA, fun heq ↦ hw₁NotA (show w₁ ∈ A from (show x = w₁ from heq) ▸ hxA)⟩
  have hw₂NotLast : w₂ ∉ S last := by
    have hne : q ≠ last := by intro heq; have := congrArg Fin.val heq; dsimp [last] at this; omega
    exact fun h ↦ Set.disjoint_left.mp (hpart hne) hw₂ h
  have hP₂GP : Disjoint V(P₂) V(GP.graph) := by
    apply Set.disjoint_left.mpr
    intro x hx hxLast
    exact Set.disjoint_left.mp hAvoidP₂ hx
      ⟨Or.inl (hLastA hxLast), fun heq ↦ hw₂NotLast (heq ▸ hxLast)⟩
  have hP₀D : V(P₀) ∩ V(D) ⊆ {d₁.val} := by
    intro x hxD
    by_cases hiSmall : i.val ≤ 1
    · have hloc : V(P₀) ⊆ {G.root.val} := by simpa only [hiSmall, ↓reduceIte] using hP₀loc
      have hxRoot : x = G.root.val := hloc hxD.1
      have hw : w₁ = G.root.val := by simp only [w₁, firstLayerBoundary, hiSmall, ↓reduceDIte]
      have hxP1 : x ∈ V(P₁) := by rw [hxRoot, ← hw]; exact hP1.right_mem
      exact hP₁D ▸ ⟨hxP1, hxD.2⟩
    · have hloc : V(P₀) ⊆ B := by simpa only [hiSmall, ↓reduceIte] using hP₀loc
      exact False.elim (Set.disjoint_left.mp hBD (hloc hxD.1) hxD.2)
  have hDRanges : ∀ e : (pathComb (γ - 1) m).coe.edgeSet, ∃ a b, e.val = s(a,b) ∧
      V(PD e) ∩ range cD = {cD a,cD b} := by
    intro e
    obtain ⟨a, b, he, _, hRange⟩ := hDPaths e
    exact ⟨a, b, he, hRange⟩
  have hd₁NotSecond : d₁.val ∉ combSecondEndSupport (by omega) cD PD :=
    fun h ↦ Set.disjoint_left.mp (disjoint_comb_ends (by omega : 4 ≤ m) hcD PD hDRanges
      (fun e f hne ↦ (hDInter e f hne).1)) hfirst h
  exact hno (rootedFork_of_attachments_outside_second_end hγ hδ (by omega : 3 ≤ m) G hDG
    cD hcD PD hVD hDPaths hDInter GP hGP MP hDGP ⟨d₁.property, hd₁NotSecond⟩
    ⟨d₂.property, hsecond⟩ hP₀ hP1 hP₂ (hP₃.mono hHG) hP₀D hP₁D.subset hP₂D.subset
    (hP₀A.mono_right hLastA) (hP₁A.mono_right hLastA) hP₂GP
    (hAD.mono_left hP₃A) hP₃Last)

end GraphMinor.GM01
