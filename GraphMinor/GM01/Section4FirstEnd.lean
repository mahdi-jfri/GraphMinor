module

public import GraphMinor.GM01.Section4LayerDisjointness
public import GraphMinor.GM01.SubdivisionInteriorFork
public import GraphMinor.GM01.CombFirstBoundaryRootPaths
import GraphMinor.GM01.RootedPathAttachment
import GraphMinor.GM01.SubdivisionConnected

/-!
# The first attachment lies in an end of the layer subdivision

Graph Minors I, (4.9), page 58, contracts the first attachment path and
the path from its boundary to the ambient root. Their union meets `D`
only at the attachment vertex. If that vertex is outside the two ends,
the controlled contraction of `D` gives a rooted fork there. Moving
its root along the extracted root path gives the forbidden fork in
`G`, contradicting the standing exclusion.
-/

public section

namespace GraphMinor.GM01

open Set Graph SimpleGraph Function GraphMinor.GM09

universe u v

/-- Graph Minors I, (4.9), page 58: "$d_1$ is in one of the ends of $D$."
The first boundary path is the paper's chosen path meeting `D` only
at its initial end. The proof constructs the root path and the rooted
fork model, rather than assuming the contraction step. -/
theorem theorem_4_9_proof {α : Type u} {β : Type v} {γ δ L n : ℕ}
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
    (hDInter : ∀ e f : (pathComb (γ - 1) m).coe.edgeSet, e ≠ f → V(PD e) ∩ V(PD f) ⊆ range cD)
    (d₁ : V(D)) (P₁ : Graph α β)
    (hP₁ : IsGraphPathWithEnds G.graph P₁ d₁.val
      (firstLayerBoundary G c ν i.val (by omega) (by
        have hm' := Nat.mul_le_mul_left ν (show i.val - 1 ≤ T by omega)
        omega)))
    (hP₁D : V(P₁) ∩ V(D) = {d₁.val}) :
    d₁.val ∈ combFirstEndSupport (by omega) cD PD ∪ combSecondEndSupport (by omega) cD PD := by
  classical
  by_contra hx
  obtain ⟨M⟩ := rootedFork_of_subdivision_attachment_outside_ends hγ hδ (by omega : 5 ≤ m)
    (by omega : 2 * δ ≤ m) hcD PD hVD hDPaths hDInter d₁ hx
  let H := subgraphUnion G.graph N R
  let S := fun k : Fin n ↦ combBlock hL H c k
  have hbound : 2 * (ν * (i.val - 1)) ≤ L := by
    have hm' := Nat.mul_le_mul_left ν (show i.val - 1 ≤ T by omega)
    omega
  let w := firstLayerBoundary G c ν i.val (by omega : 0 < ν) hbound
  have hP1 : IsGraphPathWithEnds G.graph P₁ d₁.val w := hP₁
  have h2n : 2 * n ≤ L := by omega
  obtain ⟨P₀, hP₀, hP₀loc⟩ := exists_root_path_to_first_layer_boundary hL hν h2n hn G hN hc
    hV hE hPaths (fun e f hne ↦ (hInter e f hne).1) hR hmeetR i hbound
  have hP₀D : V(P₀) ∩ V(D) ⊆ {d₁.val} := by
    intro x hxD
    by_cases hiSmall : i.val ≤ 1
    · have hloc : V(P₀) ⊆ {G.root.val} := by simpa only [hiSmall, ↓reduceIte] using hP₀loc
      have hxRoot : x = G.root.val := hloc hxD.1
      have hw : w = G.root.val := by simp only [w, firstLayerBoundary, hiSmall, ↓reduceDIte]
      have hxP1 : x ∈ V(P₁) := by rw [hxRoot, ← hw]; exact hP1.right_mem
      exact hP₁D ▸ ⟨hxP1, hxD.2⟩
    · have hloc : V(P₀) ⊆ layerEarlyBlocks S ν i.val := by
        simpa only [hiSmall, ↓reduceIte] using hP₀loc
      have hdis := theorem_4_6_proof hγ hδ hL htail G hno hN hc hV hE hPaths hInter hR hmeetR
        hν left right hleft hright Y hY hn i
      exact False.elim (Set.disjoint_left.mp hdis.2.2 (hloc hxD.1) (hDW hxD.2))
  let K := subgraphUnion G.graph P₀ P₁
  have hKconn : GraphConnected K := graphConnected_subgraphUnion hP₀.le hP1.le
    (graphConnected_of_isGraphPath hP₀) (graphConnected_of_isGraphPath hP1)
    ⟨w, hP₀.right_mem, hP1.right_mem⟩
  have hrootK : G.root.val ∈ V(K) := Or.inl hP₀.left_mem
  have hdK : d₁.val ∈ V(K) := Or.inr hP1.left_mem
  obtain ⟨R₀, hR₀⟩ := exists_path_of_adj_reachable hrootK
    (hKconn.2 G.root.val hrootK d₁.val hdK)
  have hKG : K ≤ G.graph := subgraphUnion_le hP₀.le hP1.le
  have hR0 := hR₀.mono hKG
  have hmeet : V(D) ∩ V(R₀) ⊆ {d₁.val} := by
    intro x hx
    rcases hR₀.le.vertexSet_mono hx.2 with hxP0 | hxP1
    · exact hP₀D ⟨hxP0, hx.1⟩
    · exact hP₁D ▸ ⟨hxP1, hx.1⟩
  have M' : RootedMinorModel (rootedForkGraph γ δ hγ hδ) G :=
    (M.attachRootPath hDG G.root.val hR0 hmeet).mono (subgraphUnion_le hDG hR0.le) rfl
  exact hno ⟨M'⟩

end GraphMinor.GM01
