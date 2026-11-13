module

public import GraphMinor.GM01.ForestTrees
public import GraphMinor.GM01.Defs
import GraphMinor.GM01.GridBinaryMinor
import GraphMinor.GM01.ForestBinaryMinor
import GraphMinor.Minor.Basic
import Lean.Elab.Tactic.Omega

/-!
# The three-branch tree as a grid minor

Graph Minors I, (3.4), page 52, combines the binary-tree diagram
(3.2) with the contraction (3.3). For odd height, the next binary
height is even, and its corrected grid exponent is exactly the
exponent printed in (3.4).
-/

public section

namespace GraphMinor.GM01

/-- Graph Minors I, (3.4), page 52: "For any odd $\lambda \ge 1$, the
$(2^{(\lambda+3)/2}-1)$-grid has a minor isomorphic to $\mathbf{Y}_\lambda$."
Compose the corrected diagram (3.2) with the contraction (3.3), as in
the paper. -/
theorem theorem_3_4_proof (lam : ℕ) (hlam : 1 ≤ lam) (hodd : Odd lam) :
    IsIsoMinor (forestTreeGraph lam) (gridGraph (2 ^ ((lam + 3) / 2) - 1)) := by
  have heven : Even (lam + 1) := by
    obtain ⟨n, hn⟩ := hodd
    exact ⟨n + 1, by omega⟩
  have hminor := (theorem_3_3_proof lam hlam).trans (theorem_3_2_proof (lam + 1) heven)
  have hdiv : (lam + 1) / 2 + 1 = (lam + 3) / 2 := by omega
  rw [hdiv] at hminor
  exact hminor

end GraphMinor.GM01
