module

public import GraphMinor.GM01.QuantitativeBounds
public import GraphMinor.GM01.RootedForestFamilies
public import GraphMinor.GM01.RootedForks
public import GraphMinor.GM01.PathWidth
public import GraphMinor.GM01.GraphSeparators
import GraphMinor.GM01.GraphComponents
import GraphMinor.GM01.OutsideRootSupportCombExclusion
import GraphMinor.GM01.InsideRootSupportForkExclusion
import GraphMinor.GM01.ConnectedInducedSets

/-!
# Applying the induction bounds to the two component cases

In Part 3 of Graph Minors I, (3.7), page 60, delete the constructed
small cut and consider each remaining component. The geometric
proof of (5.1) chooses a root excluding the shorter comb. The
geometric proof of (5.2) chooses a root excluding the large fork.
Apply the actual preceding-length induction hypothesis in the first
case and the Part 2 fork bound in the second. Then (1.4) gives the
maximum of these two bounds after deletion of the cut.
-/

public section

namespace GraphMinor.GM01

open Set Graph

/-- Apply the actual length and fork induction bounds to the proved
geometric exclusions (5.1)/(5.2), GM01 pages 60–61. These induction
hypotheses are discharged when Part 3 and the height induction close. -/
theorem section5_deleted_graph_width {α β : Type*} (lam : ℕ) {γ δ Ω n : ℕ}
    (hγ : 0 < γ) (hδ : 2 ≤ δ)
    (hLength : ∀ C : RootedGraph α β, V(C.graph).Finite → GraphConnected C.graph →
      (¬ IsIsoMinor (gridGraph (gm01Theta lam)) C.graph) →
      (¬ HasRootedMinor (rootedPathComb γ (δ - 1) (by omega)) C) →
      HasPathWidthLE C.graph (pathWidthBound lam γ (δ - 1)))
    (hFork : ∀ (d : ℕ) (hd : 2 ≤ d), ∀ C : RootedGraph α β,
      V(C.graph).Finite → GraphConnected C.graph →
      (¬ IsIsoMinor (gridGraph (gm01Theta lam)) C.graph) →
      (¬ HasRootedMinor (rootedForkGraph γ d hγ hd) C) →
      HasPathWidthLE C.graph (forkWidthBound lam γ d))
    (G : RootedGraph α β) (hV : V(G.graph).Finite) (hE : E(G.graph).Finite)
    (hConn : GraphConnected G.graph)
    (hGrid : ¬ IsIsoMinor (gridGraph (gm01Theta lam)) G.graph)
    (hNo : ¬ HasRootedMinor (rootedPathComb γ δ (by omega)) G)
    (F : RootedForestFamily G γ n) (hMax : ∀ k, RootedForestFamily G γ k → k ≤ n)
    (K : Graph α β) (hKG : K ≤ G.graph) (hKC : GraphConnected K) (hKS : V(K) = F.rootSet)
    (X : Set α) (J : Set (Fin n)) (hJ : J.ncard ≤ Ω)
    (hSep : ∀ j ∉ J, GraphSeparates G.graph X F.rootSet (F.otherSet j)) :
    HasPathWidthLE (G.graph.deleteVerts X)
      (max (pathWidthBound lam γ (δ - 1)) (forkWidthBound lam γ (3 * Ω + 6))) := by
  let D := G.graph.deleteVerts X
  have hDG : D ≤ G.graph := Graph.deleteVerts_le
  have hDV : V(D).Finite := hV.subset hDG.vertexSet_mono
  have hSC : GraphConnected (G.graph.induce F.rootSet) := by
    have h := graphConnected_induce_of_subgraph hKG hKC
    rw [hKS] at h
    exact h
  apply theorem_1_4_proof hDV
  intro a
  let C := D.induce (componentVertices D a)
  have hCD : C ≤ D := D.induce_le (fun _ h ↦ h.1)
  have hCG : C ≤ G.graph := hCD.trans hDG
  have hCV : V(C).Finite := hV.subset hCG.vertexSet_mono
  have hCC : GraphConnected C := componentVertices_connected D a
  have hCGrid : ¬ IsIsoMinor (gridGraph (gm01Theta lam)) C := by
    rintro ⟨L,hLC,edges,hEdges,hIso⟩
    exact hGrid ⟨L,hLC.trans hCG,edges,hEdges,hIso⟩
  by_cases hMeet : (V(C) ∩ F.rootSet).Nonempty
  · obtain ⟨v,hNoFork⟩ := exists_root_inside_support_not_large_fork hγ G hV hE F hMax
      X J hJ hSep K hKG hKC hKS C hCD hCC hMeet
    exact (hFork (3 * Ω + 6) (by omega) ⟨C,v⟩ hCV hCC hCGrid hNoFork).mono (Nat.le_max_right _ _)
  · have hDis : Disjoint F.rootSet V(C) := by
      apply disjoint_left.mpr
      intro x hxS hxC
      exact hMeet ⟨x,hxC,hxS⟩
    obtain ⟨v,hNoShort⟩ := exists_root_outside_support_not_shorter_comb hγ hδ G hConn hNo
      F.rootSet F.root_subset F.root_mem hSC F.root_minor C hCG hCC hDis
    exact (hLength ⟨C,v⟩ hCV hCC hCGrid hNoShort).mono (Nat.le_max_left _ _)

end GraphMinor.GM01
