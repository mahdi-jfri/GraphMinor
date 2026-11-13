module

public import GraphMinor.GM01.Section4DisjointPaths
import GraphMinor.GM01.CombLatePieceModels
import GraphMinor.GM01.CombMiddleLateAssembly
import GraphMinor.GM01.CombConclusionLengths
import GraphMinor.GM01.CombPrefixModels
import GraphMinor.GM01.CombFirstBoundaryRootPaths
import GraphMinor.GM01.CombLayerBlockSets
import GraphMinor.GM01.CombPrefixRoot
import GraphMinor.GM01.RootedPathAttachment

/-!
# The longer comb contradicts maximality

Graph Minors I, (4.14), page 59, retains the early old comb, the
middle of the layer subdivision, and the old late comb after its
boundary block. The two clean attachments join these pieces in
order. At the first two layers there is no early piece, so the first
attachment transports the ambient root instead. The resulting comb
is longer than the maximal old comb, a contradiction.
-/

public section

namespace GraphMinor.GM01

open Set Graph SimpleGraph Function GraphMinor.GM09

universe u v

/-- Graph Minors I, (4.14), page 59, the conclusion of Part 2.
The actual three retained pieces and their joining paths give the
longer rooted comb, contradicting the chosen maximal length.
Results (4.10), (4.12), and (4.13) are proved and invoked internally. -/
theorem theorem_4_14_proof {α : Type u} {β : Type v} {γ δ L n : ℕ}
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
    False := by
  classical
  have hsecond := theorem_4_12_proof hγ hδ hL htail G hno hN hc hV hE hPaths hInter hR hmeetR
    hν left right hleft hright Y hY hn i hm D hDG hDW hcD PD hVD hDPaths hDInter
    d₁ P₁ hP₁ hP₁D hAvoidP₁ hT hmaxT hmaxL hfirst q hq w₂ hw₂ d₂ P₂ hP₂ hAvoidP₂ hP₂D
  have hP₁P₂ := theorem_4_13_proof hγ hδ hL htail G hno hN hc hV hE hPaths hInter hR hmeetR
    hν left right hleft hright Y hY hn i hm D hDG hDW hcD PD hVD hDPaths hDInter
    d₁ P₁ hP₁ hP₁D hAvoidP₁ hT hmaxT hmaxL hfirst q hq w₂ hw₂ d₂ P₂ hP₂ hAvoidP₂ hP₂D
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
  have hcentres : ∀ v, c v ∈ V(N) := by
    intro v
    rw [hV]
    exact Or.inl (mem_range_self v)
  have hPN : ∀ e, P e ≤ N := by
    intro e
    obtain ⟨_, _, _, _, hP, _⟩ := hPaths e
    exact hP.le
  have hRanges : ∀ e : (pathComb (γ - 1) L).coe.edgeSet, ∃ a b, e.val = s(a,b) ∧
      V(P e) ∩ range c = {c a,c b} := by
    intro e
    obtain ⟨a, b, he, _, _, hRange⟩ := hPaths e
    exact ⟨a, b, he, hRange⟩
  have hInterV := fun e f hne ↦ (hInter e f hne).1
  have hreg := combSpineRegion_antitone hL hN hR.le hc hcentres hPN hE hRanges hInterV hmeetR
  have hdis := theorem_4_6_proof hγ hδ hL htail G hno hN hc hV hE hPaths hInter hR hmeetR
    hν left right hleft hright Y hY hn i
  have hAD : Disjoint A V(D) := hdis.2.1.mono_right hDW
  have hBD : Disjoint B V(D) := hdis.2.2.mono_right hDW
  have hAw : A = combSpineRegion hL H c (2 * q.val) :=
    layerLateBlocks_eq_combSpineRegion hL H c hreg ν i.val q hq
  have hw₂A : w₂ ∈ A := Set.mem_iUnion₂.mpr ⟨q, by omega, hw₂⟩
  have hw₂NotB : w₂ ∉ B := fun h ↦ Set.disjoint_left.mp hdis.1 hw₂A h
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
  have hw₁NotA : w₁ ∉ A := by
    intro hwA
    by_cases hiSmall : i.val ≤ 1
    · have hw : w₁ = G.root.val := by simp only [w₁, firstLayerBoundary, hiSmall, ↓reduceDIte]
      exact hrootNotA (hw ▸ hwA)
    · have hloc : V(P₀) ⊆ B := by simpa only [hiSmall, ↓reduceIte] using hP₀loc
      exact Set.disjoint_left.mp hdis.1 hwA (hloc hP₀.right_mem)
  have hP₁A : Disjoint V(P₁) A := by
    apply Set.disjoint_left.mpr
    intro x hx hxA
    exact Set.disjoint_left.mp hAvoidP₁ hx
      ⟨Or.inl hxA, fun heq ↦ hw₁NotA ((show x = w₁ from heq) ▸ hxA)⟩
  have hP₂B : Disjoint V(P₂) B := by
    apply Set.disjoint_left.mpr
    intro x hx hxB
    exact Set.disjoint_left.mp hAvoidP₂ hx ⟨Or.inr hxB, fun heq ↦ hw₂NotB (heq ▸ hxB)⟩
  let b := L - 2 * (q.val + 1)
  have hb : 0 < b := by dsimp [b]; omega
  have hbBound : 2 * (q.val + 1) + b ≤ L := by dsimp [b]; omega
  obtain ⟨Late, hLateG, hLateRegion, hLateRoot, ⟨MLate⟩⟩ := exists_rooted_comb_late_piece
    hL h2n hb hN c hc P hV hE hPaths hInter G.root.val hR hmeetR q hqpos hqnext hbBound hw₂
  have hLateA : V(Late.graph) ⊆ A := hAw.symm ▸ hLateRegion
  have hDLate : Disjoint V(D) V(Late.graph) := (hAD.mono_left hLateA).symm
  have hP₂Late : V(P₂) ∩ V(Late.graph) = {Late.root.val} := by
    rw [hLateRoot]
    apply Set.Subset.antisymm
    · intro x hx
      by_contra hnot
      exact Set.disjoint_left.mp hAvoidP₂ hx.1 ⟨Or.inl (hLateA hx.2), hnot⟩
    · intro x hx
      have hxw : x = w₂ := hx
      subst x
      exact ⟨hP₂.right_mem, hLateRoot ▸ Late.root.property⟩
  have hP2LateRoot : IsGraphPathWithEnds G.graph P₂ d₂.val Late.root.val := by
    rw [hLateRoot]
    exact hP₂
  obtain ⟨K, hKG, hKV, ⟨MK⟩, J, hJ, hJMeet, hJV⟩ :=
    exists_middle_late_comb_with_clean_root_path (by omega : 6 ≤ m) hb hDG cD hcD PD hVD hDPaths hDInter
      Late hLateG MLate hDLate hfirst hsecond hP1 hP2LateRoot hP₁D hP₂D
      (hP₁A.mono_right hLateA) hP₂Late hP₁P₂
  have hLong := comb_conclusion_length_exceeds hν hδ hm hq (by omega : 2 * (q.val + 1) ≤ L)
  change L < 2 * (ν * (i.val - 1)) + (m - 4) + b at hLong
  by_cases hiSmall : i.val ≤ 1
  · have hw : w₁ = G.root.val := by simp only [w₁, firstLayerBoundary, hiSmall, ↓reduceDIte]
    have hRootPath : IsGraphPathWithEnds G.graph J G.root.val K.root.val := hw ▸ hJ
    have hMeet : V(K.graph) ∩ V(J) ⊆ {K.root.val} := by
      intro x hx
      exact hJMeet ▸ ⟨hx.2, hx.1⟩
    have hModel : HasRootedMinor (rootedPathComb (γ - 1) ((m - 4) + b) (by omega)) G :=
      ⟨(MK.attachRootPath hKG G.root.val hRootPath hMeet).mono (subgraphUnion_le hKG hRootPath.le) rfl⟩
    have hmax := hmaxL ((m - 4) + b) (by omega) hModel
    have hi0 : i.val - 1 = 0 := Nat.sub_eq_zero_of_le hiSmall
    rw [hi0, Nat.mul_zero, Nat.mul_zero, Nat.zero_add] at hLong
    omega
  · let p : Fin n := ⟨ν * (i.val - 1), by
      have hh := Nat.mul_le_mul_left ν (show i.val - 1 ≤ T by omega)
      omega⟩
    have hp : 0 < p.val := Nat.mul_pos (by omega) (by omega)
    have hpL : 2 * p.val < L := by have := p.isLt; omega
    have hBPrefix : B = combPrefix hL H c p.val :=
      layerEarlyBlocks_eq_combPrefix hL H c hreg ν i.val p rfl
    obtain ⟨Early, hEarlyG, hEarlyPrefix, hEarlyRoot, MEarly, hLast⟩ := exists_rooted_comb_prefix_model
      hL G hN hc hV hE hPaths hInter hR hmeetR p.val hp hpL
    have hEarlyB : V(Early.graph) ⊆ B := hBPrefix.symm ▸ hEarlyPrefix
    have hw : w₁ = c ⟨Sum.inl ⟨2 * p.val - 1, by omega⟩, pathComb_spine_mem (γ - 1) L _⟩ := by
      simp only [w₁, firstLayerBoundary, hiSmall, ↓reduceDIte]
      rfl
    have hwOwn : w₁ ∈ MEarly.branch (pathCombLastSpine (γ - 1) (2 * p.val) (by omega)) := hw.symm ▸ hLast
    have hwEarly : w₁ ∈ V(Early.graph) := MEarly.branch_subset _ hwOwn
    have hEarlyK : Disjoint V(Early.graph) V(K.graph) := by
      apply Set.disjoint_left.mpr
      intro x hxEarly hxK
      have hxB := hEarlyB hxEarly
      rcases hKV hxK with (hxD | hxLate) | hxP₂
      · exact Set.disjoint_left.mp hBD hxB hxD
      · exact Set.disjoint_left.mp hdis.1 (hLateA hxLate) hxB
      · exact Set.disjoint_left.mp hP₂B hxP₂ hxB
    have hJEarly : V(J) ∩ V(Early.graph) = {w₁} := by
      apply Set.Subset.antisymm
      · intro x hx
        rcases hJV hx.1 with hxP₁ | hxD
        · by_contra hnot
          exact Set.disjoint_left.mp hAvoidP₁ hxP₁
            ⟨Or.inr (hEarlyB hx.2), fun heq ↦ hnot (show x = w₁ from heq)⟩
        · exact False.elim (Set.disjoint_left.mp hBD (hEarlyB hx.2) hxD)
      · intro x hx
        have hxw : x = w₁ := hx
        subst x
        exact ⟨hJ.left_mem, hwEarly⟩
    have hModel : HasRootedMinor (rootedPathComb (γ - 1) (2 * p.val + ((m - 4) + b)) (by omega)) G :=
      ⟨rootedModelOfCombJoin (by omega : 0 < 2 * p.val) (by omega : 0 < (m - 4) + b)
        G Early K hEarlyG hKG hEarlyRoot hEarlyK MEarly MK hwOwn hJ hJEarly hJMeet⟩
    have hmax := hmaxL (2 * p.val + ((m - 4) + b)) (by omega) hModel
    change L < 2 * p.val + (m - 4) + b at hLong
    omega

end GraphMinor.GM01
