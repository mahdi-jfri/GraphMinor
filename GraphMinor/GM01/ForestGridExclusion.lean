module

public import GraphMinor.GM01.ForestTrees
public import GraphMinor.GM01.Defs
public import GraphMinor.GM01.QuantitativeBounds
import GraphMinor.GM01.GridForestMinor
import GraphMinor.GM01.GridInclusionMinor
import GraphMinor.Minor.Basic
import Lean.Elab.Tactic.Omega

/-!
# Forest-tree exclusion implies grid exclusion

Graph Minors I, (3.5), page 52, applies (3.4) inside the grid of
side `max 6 (2^((λ+3)/2))`. A model of that grid would compose with
the constructed forest-tree minor, contradicting its exclusion.
The argument applies to the library's general multigraphs.
-/

public section

namespace GraphMinor.GM01

/-- Graph Minors I, (3.5), page 52: "For odd $\lambda \ge 1$, let
$\theta = \max(6, 2^{(\lambda+3)/2})$. For any graph $G$, if $G$ has no
minor isomorphic to $\mathbf{Y}_\lambda$, then $G \in \mathscr{F}_\theta$."
Use (3.4), include its grid in the larger square, and compose minors. -/
theorem theorem_3_5_proof {α β : Type*} (lam : ℕ) (hlam : 1 ≤ lam) (hodd : Odd lam)
    (G : Graph α β) (hNo : ¬ IsIsoMinor (forestTreeGraph lam) G) :
    ¬ IsIsoMinor (gridGraph (gm01Theta lam)) G := by
  have hp : 2 ≤ 2 ^ ((lam + 3) / 2) := by
    exact Nat.pow_le_pow_right (by decide : 0 < 2) (show 1 ≤ (lam + 3) / 2 by omega)
  have hsmall : 0 < 2 ^ ((lam + 3) / 2) - 1 := by omega
  have hle : 2 ^ ((lam + 3) / 2) - 1 ≤ gm01Theta lam :=
    (Nat.sub_le _ _).trans (Nat.le_max_right _ _)
  intro hGrid
  exact hNo ((theorem_3_4_proof lam hlam hodd).trans
    ((gridGraph_isIsoMinor_of_le hsmall hle).trans hGrid))

end GraphMinor.GM01
