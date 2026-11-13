module

public import GraphMinor.GM01.QuantitativeBounds
public import GraphMinor.GM01.RootedForks
public import GraphMinor.GM01.PathWidth
import GraphMinor.GM01.Section5ComponentWidths
import GraphMinor.GM01.MaximalForestFamilies
import GraphMinor.GM01.ForestFamilySubdivisionSupports
import GraphMinor.GM01.ForestFamilySmallCut
import GraphMinor.GM01.ForkFourInitialMinors
import GraphMinor.GM01.RootedModelComposition
import GraphMinor.GM01.SubdivisionConnected
import GraphMinor.GM01.ConnectedInducedSets
import GraphMinor.GM01.QuantitativeFirstEstimates
import GraphMinor.GM01.QuantitativeLastEstimate
import GraphMinor.GM01.QuantitativeParity

/-!
# Part 3 of the rooted width induction

Graph Minors I, (3.7), pages 59–61, derives the comb bound at one
height from the fork bound at that same height. Induct on comb length.
If the four-fork is excluded, its bound already suffices. Otherwise
choose the maximum forest family, shrink to the actual subdivision
supports, and construct the small cut. Apply the two proved component
exclusions and their induction bounds. Deletion gluing and (3.6)(iv)
give the required width. Finite edge-label types suffice here; the
final rooted theorem passes to the finite underlying simple graph.
-/

public section

namespace GraphMinor.GM01

open Set Graph SimpleGraph Function GraphMinor.GM09

private theorem width_of_four_fork_and_not_comb {α β : Type*} [Finite β]
    (lam : ℕ) (hodd : Odd lam) {γ δ : ℕ} (hγ : 0 < γ) (hγlam : γ ≤ lam) (hδ : 3 ≤ δ)
    (hLength : ∀ C : RootedGraph α β, V(C.graph).Finite → GraphConnected C.graph →
      (¬ IsIsoMinor (gridGraph (gm01Theta lam)) C.graph) →
      (¬ HasRootedMinor (rootedPathComb γ (δ - 1) (by omega)) C) →
      HasPathWidthLE C.graph (pathWidthBound lam γ (δ - 1)))
    (hFork : ∀ (d : ℕ) (hd : 2 ≤ d), ∀ C : RootedGraph α β,
      V(C.graph).Finite → GraphConnected C.graph →
      (¬ IsIsoMinor (gridGraph (gm01Theta lam)) C.graph) →
      (¬ HasRootedMinor (rootedForkGraph γ d hγ hd) C) →
      HasPathWidthLE C.graph (forkWidthBound lam γ d))
    (G : RootedGraph α β) (hV : V(G.graph).Finite) (hConn : GraphConnected G.graph)
    (hGrid : ¬ IsIsoMinor (gridGraph (gm01Theta lam)) G.graph)
    (hNo : ¬ HasRootedMinor (rootedPathComb γ δ (by omega)) G)
    (hFour : HasRootedMinor (rootedForkGraph γ 4 hγ (by decide)) G) :
    HasPathWidthLE G.graph (pathWidthBound lam γ δ) := by
  classical
  have hE : E(G.graph).Finite := Set.toFinite _
  obtain ⟨n,F,hMax⟩ := exists_max_rooted_forest_family_of_four_fork G hV hγ hFour
  obtain ⟨F',_,_,hRoot,hOthers⟩ := exists_rooted_forest_family_subdivision_supports hγ F hV hE
  obtain ⟨N,c,P,R,hNG,hc,hVN,_,hPaths,hInter,hR,hMeet,hRootSet⟩ := hRoot
  have hOtherConn : ∀ i, GraphConnected (G.graph.induce (F'.otherSet i)) := by
    intro i
    obtain ⟨B,_,_,hBG,_,_,_,_,_,hBC,hEq⟩ := hOthers i
    have h := graphConnected_induce_of_subgraph hBG hBC
    rw [← hEq] at h
    exact h
  have hPaths' : ∀ e : (binaryTree γ).coe.edgeSet, ∃ a b, e.val = s(a,b) ∧
      IsGraphPathWithEnds N (P e) (c a) (c b) ∧ V(P e) ∩ range c = {c a,c b} := by
    intro e
    obtain ⟨a,b,he,_,hP,hRange⟩ := hPaths e
    exact ⟨a,b,he,hP,hRange⟩
  have hInter' := fun e f hne ↦ (hInter e f hne).2
  obtain ⟨X,J,hX,hSize,hSep⟩ := exists_small_cut_for_rooted_forest_family hγ (by omega)
    (gm01Theta_ge_six lam) (gm01Theta_even lam) G hV hE hGrid hNo F' hOtherConn
    hNG hc hVN hPaths' hInter' hR hMeet hRootSet
  let Ω := (gm01Alpha lam) ^ (δ * 2 ^ γ)
  have hSizeΩ : X.ncard + J.ncard ≤ Ω := hSize
  have hXBound : X.ncard ≤ Ω := (Nat.le_add_right X.ncard J.ncard).trans hSizeΩ
  have hJBound : J.ncard ≤ Ω := (Nat.le_add_left J.ncard X.ncard).trans hSizeΩ
  have hNC : GraphConnected N := by
    apply subdivision_connected (binaryTree_connected γ).coe (binaryRootedTree γ).root N c P hVN
    intro e
    obtain ⟨a,b,he,hab,hP,_⟩ := hPaths e
    exact ⟨a,b,he,hab,hP⟩
  let K := subgraphUnion G.graph N R
  have hKG : K ≤ G.graph := subgraphUnion_le hNG hR.le
  have hKC : GraphConnected K := by
    apply graphConnected_subgraphUnion hNG hR.le hNC (graphConnected_of_isGraphPath hR)
    refine ⟨c (binaryRootedTree γ).root,?_,hR.right_mem⟩
    rw [hVN]
    exact Or.inl (mem_range_self _)
  have hKS : V(K) = F'.rootSet := hRootSet.symm
  have hDeleted := section5_deleted_graph_width lam hγ (by omega) hLength hFork
    G hV hE hConn hGrid hNo F' hMax K hKG hKC hKS X J hJBound hSep
  have hWidth := theorem_1_5_proof hV hX hDeleted
  have hMargin := pathWidthBound_induction_margin hodd (by omega : 1 ≤ γ) hγlam hδ
  change Ω + max (pathWidthBound lam γ (δ - 1)) (forkWidthBound lam γ (3 * Ω + 6)) ≤
    pathWidthBound lam γ δ at hMargin
  apply hWidth.mono
  exact (Nat.add_le_add_left hXBound _).trans ((Nat.add_comm _ _).le.trans hMargin)

/-- The actual Part 3 implication of GM01 (3.7), pages 59–61.
The only result hypothesis is the current-height fork bound supplied
by Part 2. Length induction and both component arguments close here.
The finite-label assumption is removed by simplification in the final
rooted theorem. -/
theorem pathWidthLE_of_not_rootedPathComb_of_fork_width {α β : Type*} [Finite β]
    (lam : ℕ) (hodd : Odd lam) {γ : ℕ} (hγ : 0 < γ) (hγlam : γ ≤ lam)
    (hFork : ∀ (d : ℕ) (hd : 2 ≤ d), ∀ C : RootedGraph α β,
      V(C.graph).Finite → GraphConnected C.graph →
      (¬ IsIsoMinor (gridGraph (gm01Theta lam)) C.graph) →
      (¬ HasRootedMinor (rootedForkGraph γ d hγ hd) C) →
      HasPathWidthLE C.graph (forkWidthBound lam γ d)) :
    ∀ (δ : ℕ) (hδ : 2 ≤ δ), ∀ G : RootedGraph α β,
      V(G.graph).Finite → GraphConnected G.graph →
      (¬ IsIsoMinor (gridGraph (gm01Theta lam)) G.graph) →
      (¬ HasRootedMinor (rootedPathComb γ δ (by omega)) G) →
      HasPathWidthLE G.graph (pathWidthBound lam γ δ) := by
  intro δ
  induction δ using Nat.strong_induction_on with
  | h δ ih =>
    intro hδ G hV hConn hGrid hNo
    by_cases hFour : HasRootedMinor (rootedForkGraph γ 4 hγ (by decide)) G
    · have hne : δ ≠ 2 := by
        intro heq
        subst δ
        obtain ⟨M⟩ := hFour
        exact hNo ⟨(rootedTwoCellCombModelOfForkFour hγ).trans M⟩
      have hδ3 : 3 ≤ δ := by omega
      have hLength : ∀ C : RootedGraph α β, V(C.graph).Finite → GraphConnected C.graph →
          (¬ IsIsoMinor (gridGraph (gm01Theta lam)) C.graph) →
          (¬ HasRootedMinor (rootedPathComb γ (δ - 1) (by omega)) C) →
          HasPathWidthLE C.graph (pathWidthBound lam γ (δ - 1)) :=
        ih (δ - 1) (by omega) (by omega)
      exact width_of_four_fork_and_not_comb lam hodd hγ hγlam hδ3 hLength hFork
        G hV hConn hGrid hNo hFour
    · exact (hFork 4 (by decide) G hV hConn hGrid hFour).mono
        (pathWidthBound_ge_fork_four lam (by omega) hδ)

end GraphMinor.GM01
