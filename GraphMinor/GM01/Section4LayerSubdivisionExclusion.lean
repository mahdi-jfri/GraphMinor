module

public import GraphMinor.GM01.Section4Conclusion
import GraphMinor.GM01.CombReflectionSubdivision
import GraphMinor.GM01.Section4FirstBoundaryPath

/-!
# Excluding the larger comb subdivision from every layer

On pages 57–59, Graph Minors I rules out the layer subdivision `D`.
Choose the clean first attachment using (4.8), locate its end by
(4.9), and orient the subdivision by the proved reflection choice.
Then (4.11) constructs the clean second attachment and (4.14) gives
the maximality contradiction. All attachment and orientation choices
are made inside this proof.
-/

public section

namespace GraphMinor.GM01

open Set Graph SimpleGraph Function GraphMinor.GM09

universe u v

/-- The subdivision exclusion in Part 2, GM01 pages 57–59, obtained
from the actual choices and proved claims (4.8)–(4.14). -/
theorem no_comb_subdivision_in_separator_layer {α : Type u} {β : Type v} {γ δ L n : ℕ}
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
    (hT : 2 ≤ T)
    (hmaxT : ∀ t : ℕ, 2 * ν * t ≤ L - 2 * δ → t ≤ T)
    (hmaxL : ∀ k (hk : 0 < k), HasRootedMinor (rootedPathComb (γ - 1) k hk) G → k ≤ L)
    (hGconn : GraphConnected G.graph) : False := by
  let v := (rootedPathComb (γ - 1) m (by omega : 0 < m)).root
  have hD : V(D).Nonempty := ⟨cD v, by rw [hVD]; exact Or.inl (mem_range_self v)⟩
  obtain ⟨d, hd, P₁, hP₁, hAvoidP₁, hP₁D⟩ := exists_first_boundary_path_with_single_D_vertex
    hγ hδ hL htail G hno hN hc hV hE hPaths hInter hR hmeetR
    hν left right hleft hright Y hY hn i hGconn (by omega) D hD hDW
  let d₁ : V(D) := ⟨d, hd⟩
  have hEnds := theorem_4_9_proof hγ hδ hL htail G hno hN hc hV hE hPaths hInter hR hmeetR
    hν left right hleft hright Y hY hn i hm D hDG hDW hcD PD hVD hDPaths
    (fun e f hne ↦ (hDInter e f hne).1) d₁ P₁ hP₁ hP₁D
  obtain ⟨cD', PD', hcD', hVD', hDPaths', hDInter', hfirst⟩ :=
    exists_first_end_orientation (by omega : 2 ≤ m) cD hcD PD hVD hDPaths hDInter hEnds
  obtain ⟨q, hq, w₂, hw₂, _, _, d₂, hd₂, P₂, hP₂, hAvoidP₂, hP₂D⟩ :=
    theorem_4_11_proof hγ hδ hL htail G hno hN hc hV hE hPaths hInter hR hmeetR
      hν left right hleft hright Y hY hn i hm D hDG hDW hcD' PD' hVD' hDPaths' hDInter'
      d₁ P₁ hP₁ hP₁D hAvoidP₁ hT hmaxT hmaxL hGconn
  exact theorem_4_14_proof hγ hδ hL htail G hno hN hc hV hE hPaths hInter hR hmeetR
    hν left right hleft hright Y hY hn i hm D hDG hDW hcD' PD' hVD' hDPaths' hDInter'
    d₁ P₁ hP₁ hP₁D hAvoidP₁ hT hmaxT hmaxL hfirst q hq w₂ hw₂ ⟨d₂, hd₂⟩ P₂ hP₂ hAvoidP₂ hP₂D

end GraphMinor.GM01
