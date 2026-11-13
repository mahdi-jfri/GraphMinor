module

public import GraphMinor.GM01.QuantitativeParity
public import GraphMinor.GM01.RootedForks
public import GraphMinor.GM01.PathWidth
import GraphMinor.GM01.Section4Reduction
import GraphMinor.GM01.Section5Reduction
import GraphMinor.GM01.RootedPathWidthGraph
import GraphMinor.GM01.QuantitativeFirstEstimates

/-!
# Closing the height induction in the rooted width bound

The three parts of Graph Minors I, (3.7), pages 54–61, now give a
closed induction. At height zero use the proved root-deletion path
bound. At a positive height, Part 2 derives the fork bound from the
previous-height comb bounds. Part 3 derives every comb-length bound
from those current-height fork bounds. No result of the induction
is assumed below the conclusion. The finite-label hypothesis here
will hold for the underlying simple graph in the general-graph proof.
-/

public section

namespace GraphMinor.GM01

open Set Graph

/-- The closed Parts 1–3 height induction of GM01 (3.7), pages 54–61,
for finite edge-label types. Both bounds are proved together, with no
fork, comb, or component result left as a hypothesis. -/
theorem rooted_width_bounds_of_finite_edge_labels {α β : Type*} [Finite β]
    (lam : ℕ) (hodd : Odd lam) : ∀ γ : ℕ, γ ≤ lam →
    ((∀ (δ : ℕ) (hδ : 2 ≤ δ), ∀ G : RootedGraph α β,
      V(G.graph).Finite → GraphConnected G.graph →
      (¬ IsIsoMinor (gridGraph (gm01Theta lam)) G.graph) →
      (¬ HasRootedMinor (rootedPathComb γ δ (by omega)) G) →
      HasPathWidthLE G.graph (pathWidthBound lam γ δ)) ∧
    (∀ hγ : 0 < γ, ∀ (δ : ℕ) (hδ : 2 ≤ δ), ∀ G : RootedGraph α β,
      V(G.graph).Finite → GraphConnected G.graph →
      (¬ IsIsoMinor (gridGraph (gm01Theta lam)) G.graph) →
      (¬ HasRootedMinor (rootedForkGraph γ δ hγ hδ) G) →
      HasPathWidthLE G.graph (forkWidthBound lam γ δ))) := by
  intro γ
  induction γ with
  | zero =>
    intro hγlam
    refine ⟨?_,?_⟩
    · intro δ hδ G hV hConn _ hNo
      exact (pathWidthLE_of_not_rootedPathComb_graph G hV hConn (by omega) hNo).mono
        (pathWidthBound_zero lam δ)
    · intro hγ
      exact False.elim (Nat.not_lt_zero 0 hγ)
  | succ γ ih =>
    intro hγlam
    have hPrev := (ih ((Nat.le_succ γ).trans hγlam)).1
    have hFork : ∀ (δ : ℕ) (hδ : 2 ≤ δ), ∀ G : RootedGraph α β,
        V(G.graph).Finite → GraphConnected G.graph →
        (¬ IsIsoMinor (gridGraph (gm01Theta lam)) G.graph) →
        (¬ HasRootedMinor (rootedForkGraph (γ + 1) δ (Nat.succ_pos γ) hδ) G) →
        HasPathWidthLE G.graph (forkWidthBound lam (γ + 1) δ) := by
      intro δ hδ G hV hConn hGrid hNo
      exact pathWidthLE_of_not_rootedFork_of_previous_height lam (Nat.succ_pos γ) hδ
        hPrev G hV hConn hGrid hNo
    refine ⟨pathWidthLE_of_not_rootedPathComb_of_fork_width lam hodd (Nat.succ_pos γ) hγlam hFork,?_⟩
    intro hγ δ hδ G hV hConn hGrid hNo
    exact hFork δ hδ G hV hConn hGrid hNo

end GraphMinor.GM01
