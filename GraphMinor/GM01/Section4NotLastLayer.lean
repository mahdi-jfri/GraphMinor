module

public import GraphMinor.GM01.Section4FirstEnd
public import GraphMinor.GM01.CombPrefixModels
public import GraphMinor.GM01.CombEndAttachmentPaths
import GraphMinor.GM01.CombJoinModels
import GraphMinor.GM01.CleanHitPathJoins
import GraphMinor.GM01.CombExtensionBounds
import GraphMinor.GM01.CombReflectionSubdivision
import GraphMinor.GM01.CombLayerBlockSets

/-!
# The layer containing the subdivision is not the last layer

Graph Minors I, (4.10), page 58, retains the old prefix in `B` and the
part of `D` after its first end. The first boundary path and a path
through that end join the retained pieces cleanly. Their rooted comb
models concatenate to a comb longer than the maximal represented
length. The strict length inequality follows from maximality of `T`.
This uses the orientation chosen after (4.9), with the first attachment
in the first end of `D`.
-/

public section

namespace GraphMinor.GM01

open Set Graph SimpleGraph Function GraphMinor.GM09

universe u v

/-- Graph Minors I, (4.10), page 58: "$i \ne T$."
The longer comb is constructed from the actual retained pieces and
connecting path. Only the printed maximal choices of the represented
length and of `T` are assumed, not the extension model. -/
private theorem not_last_layer_of_first_end_orientation {α : Type u} {β : Type v} {γ δ L n : ℕ}
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
    (hfirst : d₁.val ∈ combFirstEndSupport (by omega) cD PD)
    (hAvoidP₁ :
      let S := fun k : Fin n ↦ combBlock hL (subgraphUnion G.graph N R) c k
      let hbound : 2 * (ν * (i.val - 1)) ≤ L := by
        have hm' := Nat.mul_le_mul_left ν (show i.val - 1 ≤ T by omega)
        omega
      let w := firstLayerBoundary G c ν i.val (by omega) hbound
      Disjoint V(P₁) ((layerLateBlocks S ν i.val ∪ layerEarlyBlocks S ν i.val) \ {w}))
    (hT : 2 ≤ T)
    (hmaxT : ∀ t : ℕ, 2 * ν * t ≤ L - 2 * δ → t ≤ T)
    (hmaxL : ∀ k (hk : 0 < k), HasRootedMinor (rootedPathComb (γ - 1) k hk) G → k ≤ L) :
    i.val ≠ T := by
  classical
  intro hiT
  let H := subgraphUnion G.graph N R
  let S := fun k : Fin n ↦ combBlock hL H c k
  let j := ν * (T - 1)
  have hj : 0 < j := Nat.mul_pos (by omega) (by omega)
  have hjT : j ≤ ν * T := Nat.mul_le_mul_left ν (Nat.sub_le T 1)
  have hjL : 2 * j < L := by omega
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
  have hreg := combSpineRegion_antitone hL hN hR.le hc hcentres hPN hE hRanges
    (fun e f hne ↦ (hInter e f hne).1) hmeetR
  let p : Fin n := ⟨j, by omega⟩
  have hp : p.val = ν * (i.val - 1) := by dsimp [p, j]; rw [hiT]
  have hB : layerEarlyBlocks S ν i.val = combPrefix hL H c j :=
    layerEarlyBlocks_eq_combPrefix hL H c hreg ν i.val p hp
  obtain ⟨G₁, hG₁, hG₁Prefix, hG₁root, M₁, hLast⟩ := exists_rooted_comb_prefix_model hL G hN hc
    hV hE hPaths hInter hR hmeetR j hj hjL
  have hG₁B : V(G₁.graph) ⊆ layerEarlyBlocks S ν i.val := by
    rw [hB]
    exact hG₁Prefix
  have hdisLayer := theorem_4_6_proof hγ hδ hL htail G hno hN hc hV hE hPaths hInter hR hmeetR
    hν left right hleft hright Y hY hn i
  have hdisD : Disjoint V(G₁.graph) V(D) := hdisLayer.2.2.mono hG₁B hDW
  have hbound : 2 * (ν * (i.val - 1)) ≤ L := by
    have hm' := Nat.mul_le_mul_left ν (show i.val - 1 ≤ T by omega)
    omega
  let w := firstLayerBoundary G c ν i.val (by omega : 0 < ν) hbound
  have hP1 : IsGraphPathWithEnds G.graph P₁ d₁.val w := hP₁
  have hAvoid : Disjoint V(P₁) ((layerLateBlocks S ν i.val ∪ layerEarlyBlocks S ν i.val) \ {w}) := hAvoidP₁
  have hiSmall : ¬ i.val ≤ 1 := by omega
  have hw : w = c ⟨Sum.inl ⟨2 * j - 1, by omega⟩, pathComb_spine_mem (γ - 1) L _⟩ := by
    simp only [w, firstLayerBoundary, hiSmall, ↓reduceDIte]
    apply congrArg c
    apply Subtype.ext
    apply congrArg Sum.inl
    apply Fin.ext
    change 2 * (ν * (i.val - 1)) - 1 = 2 * j - 1
    dsimp [j]
    rw [hiT]
  have hLastW : w ∈ M₁.branch (pathCombLastSpine (γ - 1) (2 * j) (by omega)) := hw.symm ▸ hLast
  have hwG₁ : w ∈ V(G₁.graph) := M₁.branch_subset _ hLastW
  have hP₁G₁ : V(P₁) ∩ V(G₁.graph) = {w} := by
    apply Set.Subset.antisymm
    · intro x hx
      by_contra hxNot
      exact Set.disjoint_left.mp hAvoid hx.1 ⟨Or.inr (hG₁B hx.2), hxNot⟩
    · intro x hx
      have hxw : x = w := hx
      subst x
      exact ⟨hP1.right_mem, hwG₁⟩
  have hcentresD : ∀ v, cD v ∈ V(D) := by
    intro v
    rw [hVD]
    exact Or.inl (mem_range_self v)
  have htailpos : 0 < m - 2 := by omega
  have htailbound : 2 + (m - 2) ≤ m := by omega
  let G₂ := rootedCombSegment htailpos D cD PD 2 htailbound
  obtain ⟨hG₂D, _, M₂, _⟩ := combSegment_model htailpos cD hcD hcentresD PD hDPaths hDInter 2 htailbound
  obtain ⟨Q, hQ, hQG₂⟩ := exists_path_from_first_end_to_tail htailpos htailbound cD hcD hcentresD
    PD hDPaths hDInter hfirst
  obtain ⟨J, hJ, hJG₁, hJG₂⟩ := exists_clean_join_of_first_hit hDG hG₂D hdisD hP1 hP₁D hP₁G₁ hQ hQG₂
  have hdisPieces : Disjoint V(G₁.graph) V(G₂.graph) := hdisD.mono_right hG₂D.vertexSet_mono
  let M := rootedModelOfCombJoin (by omega : 0 < 2 * j) htailpos G G₁ G₂ hG₁ (hG₂D.trans hDG)
    hG₁root hdisPieces M₁ M₂ hLastW hJ hJG₁ hJG₂
  have hsum : 2 * j + (m - 2) ≤ L := hmaxL _ (by omega) ⟨M⟩
  have hstrict := comb_extension_length_exceeds_maxT ν δ L T m (by omega) hm hmaxT
  exact (Nat.not_le_of_gt hstrict) hsum

/-- Graph Minors I, (4.10), page 58: "$i \ne T$."
Apply proved (4.9), reflect the actual subdivision when needed, and
perform the longer-comb contraction in the resulting first-end
orientation. The orientation is a constructed choice, not a hypothesis. -/
theorem theorem_4_10_proof {α : Type u} {β : Type v} {γ δ L n : ℕ}
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
    (hmaxL : ∀ k (hk : 0 < k), HasRootedMinor (rootedPathComb (γ - 1) k hk) G → k ≤ L) :
    i.val ≠ T := by
  have hends := theorem_4_9_proof hγ hδ hL htail G hno hN hc hV hE hPaths hInter hR hmeetR
    hν left right hleft hright Y hY hn i hm D hDG hDW hcD PD hVD hDPaths
    (fun e f hne ↦ (hDInter e f hne).1) d₁ P₁ hP₁ hP₁D
  obtain ⟨cD', PD', hcD', hVD', hDPaths', hDInter', hfirst⟩ := exists_first_end_orientation
    (by omega : 2 ≤ m) cD hcD PD hVD hDPaths hDInter hends
  exact not_last_layer_of_first_end_orientation hγ hδ hL htail G hno hN hc hV hE hPaths hInter hR hmeetR
    hν left right hleft hright Y hY hn i hm D hDG hDW hcD' PD' hVD' hDPaths' hDInter'
    d₁ P₁ hP₁ hP₁D hfirst hAvoidP₁ hT hmaxT hmaxL

end GraphMinor.GM01
