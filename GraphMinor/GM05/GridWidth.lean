module

public import GraphMinor.GM05.GridLines
import GraphMinor.GM05.GridUpperWidth
import GraphMinor.GM05.GridObstruction
import GraphMinor.GM05.ConnectedBags
import GraphMinor.GM05.CompleteWidth
import GraphMinor.GM05.MinorWidth

/-!
# Graph Minors V, (1.4): exact widths of complete graphs and grids

The connected grid family meets pairwise, so one bag of any decomposition
meets all its members. Such a bag has at least `n + 1` vertices. The path
decomposition in `GridUpperWidth.lean` attains this bound. Together with the
complete-graph bound this proves (1.4).
-/

public section

namespace GraphMinor.GM05

open SimpleGraph Set

/-- The grid family forces a bag with at least `n + 1` vertices in every
finite tree-decomposition of the `n`-grid. -/
theorem grid_treeWidth_ge {n : ℕ} (hn : 2 ≤ n) : n ≤ treeWidth (squareGrid n) := by
  classical
  have hfin : (squareGrid n).verts.Finite := finite_univ
  obtain ⟨ι, _, T, χ, htd, hw⟩ := treeWidthLE_treeWidth hfin
  obtain ⟨t, ht⟩ := htd.exists_bag_meeting_touching (gridTouchingFamily hn)
    (gridTouchingFamily_le hn) (gridTouchingFamily_connected hn) (gridTouchingFamily_touch hn)
  have hχ : (χ t).Finite := Set.toFinite _
  have hcard := gridTouchingFamily_hitting_card hn hχ ht
  have hbound := hw t
  omega

/-- The grid assertion of Graph Minors V, (1.4), page 93. -/
theorem treeWidth_squareGrid {n : ℕ} (hn : 2 ≤ n) : treeWidth (squareGrid n) = n :=
  Nat.le_antisymm (Nat.sInf_le (grid_treeWidthLE hn)) (grid_treeWidth_ge hn)

/-- Graph Minors V, (1.4), page 93:
"For $n \ge 1$, the complete graph $K_n$ has tree-width $n - 1$, and for $\theta \ge 2$ the $\theta$-grid has tree-width $\theta$."
The lower bounds force a large bag, and explicit decompositions give the
matching upper bounds. -/
theorem theorem_1_4_proof {n θ : ℕ} (hn : 1 ≤ n) (hθ : 2 ≤ θ) :
    treeWidth (SimpleGraph.toSubgraph (⊤ : SimpleGraph (Fin n)) le_top) = n - 1 ∧
      treeWidth (squareGrid θ) = θ :=
  ⟨treeWidth_completeGraph hn, treeWidth_squareGrid hθ⟩

end GraphMinor.GM05
