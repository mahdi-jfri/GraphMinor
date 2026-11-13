module

public import GraphMinor.GM01.Section4SecondEnd
import GraphMinor.GM01.IntersectingAttachmentPaths

/-!
# The two attachment paths are disjoint

Graph Minors I, (4.13), page 59, reroutes the second path through
the first if they meet. The resulting path starts at the first
attachment and has the defining properties of the second path.
Result (4.12) would put that vertex in the second end, whereas the
chosen orientation puts it in the first end. Those ends are disjoint.
-/

public section

namespace GraphMinor.GM01

open Set Graph SimpleGraph Function GraphMinor.GM09

universe u v

/-- Graph Minors I, (4.13), page 59:
"$P_1$ *and* $P_2$ *are disjoint.*"
Apply proved (4.12) to the rerouted clean path, as in the paper. -/
theorem theorem_4_13_proof {α : Type u} {β : Type v} {γ δ L n : ℕ}
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
    Disjoint V(P₁) V(P₂) := by
  classical
  let H := subgraphUnion G.graph N R
  let S := fun k : Fin n ↦ combBlock hL H c k
  let A := layerLateBlocks S ν i.val
  let B := layerEarlyBlocks S ν i.val
  let F := A ∪ B
  have hbound : 2 * (ν * (i.val - 1)) ≤ L := by
    have hh := Nat.mul_le_mul_left ν (show i.val - 1 ≤ T by omega)
    omega
  let w₁ := firstLayerBoundary G c ν i.val (by omega : 0 < ν) hbound
  have hP1 : IsGraphPathWithEnds G.graph P₁ d₁.val w₁ := hP₁
  have hdis := theorem_4_6_proof hγ hδ hL htail G hno hN hc hV hE hPaths hInter hR hmeetR
    hν left right hleft hright Y hY hn i
  have hDF : Disjoint V(D) F :=
    ((hdis.2.1.mono_right hDW).union_left (hdis.2.2.mono_right hDW)).symm
  have hw₂F : w₂ ∈ F := Or.inl (Set.mem_iUnion₂.mpr ⟨q, by omega, hw₂⟩)
  have hDRanges : ∀ e : (pathComb (γ - 1) m).coe.edgeSet, ∃ a b, e.val = s(a,b) ∧
      V(PD e) ∩ range cD = {cD a,cD b} := by
    intro e
    obtain ⟨a, b, he, _, hRange⟩ := hDPaths e
    exact ⟨a, b, he, hRange⟩
  have hd₁NotSecond : d₁.val ∉ combSecondEndSupport (by omega) cD PD :=
    fun h ↦ Set.disjoint_left.mp (disjoint_comb_ends (by omega : 4 ≤ m) hcD PD hDRanges
      (fun e f hne ↦ (hDInter e f hne).1)) hfirst h
  have hImpossible : ∀ (Q : Graph α β), IsGraphPathWithEnds G.graph Q d₁.val w₂ →
      Disjoint V(Q) (F \ {w₂}) → V(Q) ∩ V(D) = {d₁.val} → False := by
    intro Q hQ hQF hQD
    exact hd₁NotSecond (theorem_4_12_proof hγ hδ hL htail G hno hN hc hV hE hPaths hInter hR hmeetR
      hν left right hleft hright Y hY hn i hm D hDG hDW hcD PD hVD hDPaths hDInter
      d₁ P₁ hP₁ hP₁D hAvoidP₁ hT hmaxT hmaxL hfirst q hq w₂ hw₂ d₁ Q hQ hQF hQD)
  by_cases hw : w₁ = w₂
  · have hPath : IsGraphPathWithEnds G.graph P₁ d₁.val w₂ := hw ▸ hP1
    have hAvoid : Disjoint V(P₁) (F \ {w₂}) := by
      have h : Disjoint V(P₁) (F \ {w₁}) := hAvoidP₁
      rwa [hw] at h
    exact False.elim (hImpossible P₁ hPath hAvoid hP₁D)
  · by_contra hmeet
    obtain ⟨Q, hQ, hQF, hQD⟩ := exists_rerouted_clean_attachment hDF d₁.property d₂.property
      hw₂F hw hP1 hP₂ hP₁D hP₂D hAvoidP₁ hAvoidP₂ (Set.not_disjoint_iff_nonempty_inter.mp hmeet)
    exact hImpossible Q hQ hQF hQD

end GraphMinor.GM01
