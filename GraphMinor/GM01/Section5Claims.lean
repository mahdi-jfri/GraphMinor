module

public import GraphMinor.GM01.RootedWidth
public import GraphMinor.GM01.RootedForestFamilies
public import GraphMinor.GM01.GraphComponents
public import GraphMinor.GM01.GraphSeparators
public import GraphMinor.GM09.Defs
import GraphMinor.GM01.OutsideRootSupportCombExclusion
import GraphMinor.GM01.InsideRootSupportForkExclusion
import GraphMinor.GM01.SubdivisionConnected
import GraphMinor.GM01.ConnectedInducedSets

/-!
# The two numbered component claims in Part 3

Graph Minors I, (5.1) and (5.2), pages 60–61, bound the components
after the small cut. Their actual rooted-minor exclusions were proved
by the half contraction and the packed-family contradiction. The
closed induction (3.7) now supplies the two width bounds without
assuming an induction step in either numbered statement. Connectivity
of the root support is derived from its subdivision and separate
root path. Connectivity, finiteness and grid exclusion of each
component are derived from its component definition.
-/

public section

namespace GraphMinor.GM01

open Set Graph SimpleGraph Function GraphMinor.GM09

private theorem binary_root_support_connected {α β : Type*} {γ : ℕ}
    {G N R : Graph α β} (hNG : N ≤ G) (c : (binaryTree γ).verts → α)
    (P : (binaryTree γ).coe.edgeSet → Graph α β)
    (hV : V(N) = range c ∪ ⋃ e, V(P e))
    (hPaths : ∀ e : (binaryTree γ).coe.edgeSet, ∃ a b, e.val = s(a,b) ∧
      (binaryTree γ).coe.Adj a b ∧ IsGraphPathWithEnds N (P e) (c a) (c b))
    {root : α} (hR : IsGraphPathWithEnds G R root (c (binaryRootedTree γ).root)) :
    GraphConnected (subgraphUnion G N R) := by
  have hNC := subdivision_connected (binaryTree_connected γ).coe (binaryRootedTree γ).root N c P hV hPaths
  apply graphConnected_subgraphUnion hNG hR.le hNC (graphConnected_of_isGraphPath hR)
  refine ⟨c (binaryRootedTree γ).root,?_,hR.right_mem⟩
  rw [hV]
  exact Or.inl (mem_range_self _)

private theorem not_grid_minor_of_le {α β : Type*} {θ : ℕ} {G C : Graph α β}
    (hCG : C ≤ G) (hNo : ¬ IsIsoMinor (gridGraph θ) G) : ¬ IsIsoMinor (gridGraph θ) C := by
  rintro ⟨K,hKC,edges,hEdges,hIso⟩
  exact hNo ⟨K,hKC.trans hCG,edges,hEdges,hIso⟩

/-- Graph Minors I, (5.1), pages 60–61:
"If $X_0$ does not contain any vertex of $C$, then $C$ has path-width $\le p(\gamma, \delta - 1)$."

The root support is the actual binary subdivision and its separate root
path. The component root is chosen by the proved clean joining-path and
half-contraction argument, then the closed length bound is applied. -/
theorem theorem_5_1_proof {α β : Type*} {γ δ n : ℕ} (lam : ℕ) (hodd : Odd lam)
    (hγ : 0 < γ) (hγlam : γ ≤ lam) (hδ : 3 ≤ δ)
    (G : RootedGraph α β) (hVfin : V(G.graph).Finite) (hEfin : E(G.graph).Finite)
    (hConn : GraphConnected G.graph) (hGrid : ¬ IsIsoMinor (gridGraph (gm01Theta lam)) G.graph)
    (hNo : ¬ HasRootedMinor (rootedPathComb γ δ (by omega)) G)
    (F : RootedForestFamily G γ n) {N R : Graph α β} (hNG : N ≤ G.graph)
    (c : (binaryTree γ).verts → α) (P : (binaryTree γ).coe.edgeSet → Graph α β)
    (hV : V(N) = range c ∪ ⋃ e, V(P e))
    (hPaths : ∀ e : (binaryTree γ).coe.edgeSet, ∃ a b, e.val = s(a,b) ∧
      (binaryTree γ).coe.Adj a b ∧ IsGraphPathWithEnds N (P e) (c a) (c b))
    (hR : IsGraphPathWithEnds G.graph R G.root.val (c (binaryRootedTree γ).root))
    (hRootSet : F.rootSet = V(N) ∪ V(R)) (X : Set α) (a : V(G.graph.deleteVerts X))
    (hDis : Disjoint F.rootSet (componentVertices (G.graph.deleteVerts X) a)) :
    HasPathWidthLE ((G.graph.deleteVerts X).induce (componentVertices (G.graph.deleteVerts X) a))
      (pathWidthBound lam γ (δ - 1)) := by
  let D := G.graph.deleteVerts X
  let C := D.induce (componentVertices D a)
  have hCD : C ≤ D := D.induce_le (fun _ hx ↦ hx.1)
  have hCG : C ≤ G.graph := hCD.trans Graph.deleteVerts_le
  have hCC : GraphConnected C := componentVertices_connected D a
  have hKC := binary_root_support_connected hNG c P hV hPaths hR
  have hKG := subgraphUnion_le hNG hR.le
  have hSC := graphConnected_induce_of_subgraph hKG hKC
  change GraphConnected (G.graph.induce (V(N) ∪ V(R))) at hSC
  rw [← hRootSet] at hSC
  obtain ⟨v,hNoShort⟩ := exists_root_outside_support_not_shorter_comb hγ (by omega) G hConn hNo
    F.rootSet F.root_subset F.root_mem hSC F.root_minor C hCG hCC hDis
  exact (theorem_3_7_proof lam (hγ.trans_le hγlam) hodd ⟨C,v⟩
    (hVfin.subset hCG.vertexSet_mono) (hEfin.subset hCG.edgeSet_mono) hCC
    (not_grid_minor_of_le hCG hGrid)).1 γ hγlam (δ - 1) (by omega) hNoShort

/-- Graph Minors I, (5.2), page 61:
"If $X_0$ contains a vertex of $C$, then $C$ has path-width at most $q(\gamma, 3\Omega + 6)$."

The actual cut and maximal family give the geometric fork exclusion by
packing and replacement. The closed current-height fork bound is then
applied at the constructed component root. -/
theorem theorem_5_2_proof {α β : Type*} {γ n Ω : ℕ} (lam : ℕ) (hodd : Odd lam)
    (hγ : 0 < γ) (hγlam : γ ≤ lam) (G : RootedGraph α β)
    (hVfin : V(G.graph).Finite) (hEfin : E(G.graph).Finite)
    (hGrid : ¬ IsIsoMinor (gridGraph (gm01Theta lam)) G.graph)
    (F : RootedForestFamily G γ n) (hMax : ∀ k, RootedForestFamily G γ k → k ≤ n)
    {N R : Graph α β} (hNG : N ≤ G.graph) (c : (binaryTree γ).verts → α)
    (P : (binaryTree γ).coe.edgeSet → Graph α β)
    (hV : V(N) = range c ∪ ⋃ e, V(P e))
    (hPaths : ∀ e : (binaryTree γ).coe.edgeSet, ∃ a b, e.val = s(a,b) ∧
      (binaryTree γ).coe.Adj a b ∧ IsGraphPathWithEnds N (P e) (c a) (c b))
    (hR : IsGraphPathWithEnds G.graph R G.root.val (c (binaryRootedTree γ).root))
    (hRootSet : F.rootSet = V(N) ∪ V(R)) (X : Set α) (J : Set (Fin n))
    (hSize : X.ncard + J.ncard ≤ Ω)
    (hSep : ∀ j ∉ J, GraphSeparates G.graph X F.rootSet (F.otherSet j))
    (a : V(G.graph.deleteVerts X))
    (hMeet : (componentVertices (G.graph.deleteVerts X) a ∩ F.rootSet).Nonempty) :
    HasPathWidthLE ((G.graph.deleteVerts X).induce (componentVertices (G.graph.deleteVerts X) a))
      (forkWidthBound lam γ (3 * Ω + 6)) := by
  let D := G.graph.deleteVerts X
  let C := D.induce (componentVertices D a)
  have hCD : C ≤ D := D.induce_le (fun _ hx ↦ hx.1)
  have hCG : C ≤ G.graph := hCD.trans Graph.deleteVerts_le
  have hCC : GraphConnected C := componentVertices_connected D a
  let K := subgraphUnion G.graph N R
  have hKG : K ≤ G.graph := subgraphUnion_le hNG hR.le
  have hKC : GraphConnected K := binary_root_support_connected hNG c P hV hPaths hR
  have hKS : V(K) = F.rootSet := hRootSet.symm
  have hJ : J.ncard ≤ Ω := (Nat.le_add_left J.ncard X.ncard).trans hSize
  obtain ⟨v,hNoFork⟩ := exists_root_inside_support_not_large_fork hγ G hVfin hEfin F hMax
    X J hJ hSep K hKG hKC hKS C hCD hCC hMeet
  exact (theorem_3_7_proof lam (hγ.trans_le hγlam) hodd ⟨C,v⟩
    (hVfin.subset hCG.vertexSet_mono) (hEfin.subset hCG.edgeSet_mono) hCC
    (not_grid_minor_of_le hCG hGrid)).2 γ hγ hγlam (3 * Ω + 6) (by omega) hNoFork

end GraphMinor.GM01
