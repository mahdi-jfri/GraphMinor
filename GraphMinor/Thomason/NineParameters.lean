module

public import GraphMinor.Thomason.NonneighborCliqueCriterion
import Mathlib.Tactic.IntervalCases
import Lean.Elab.Tactic.Omega

/-!
# Parameters for the nine-vertex target

After both neighbourhood reductions, it suffices to find a seven-vertex
clique minor. For orders thirteen through forty-two and degree surplus
eleven, select three singleton branches, then three pairs. Each pair
needs at most one common neighbour. The residual graph is the last
branch. The subset inequalities are finite integer checks in the kernel.
-/

public section
namespace GraphMinor.Thomason
open SimpleGraph Finset
universe u

private def nineSelectionSize (j : ℕ) : ℕ := if j < 3 then 1 else 2

private theorem nine_parameter_counts (n : ℕ) (hn : 13 ≤ n) (hn' : n ≤ 42) :
    ∀ j < 6, 0 < nineSelectionSize j ∧ selectionBudget nineSelectionSize j < 11 ∧
      j * ((n - 13) / 2).choose (nineSelectionSize j) <
        (n - selectionBudget nineSelectionSize j).choose (nineSelectionSize j) := by
  intro j hj
  interval_cases j <;> interval_cases n <;> decide

/-- The reduced graph for the nine-vertex density case has a `K₇`
minor whenever its order is at most forty-two and its degree surplus
is at least eleven. -/
theorem clique_seven_of_order_le_forty_two {V : Type u} [Fintype V] [Nonempty V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hN : Fintype.card V ≤ 42)
    (hdeg : ∀ v, Fintype.card V + 11 ≤ 2 * G.degree v) :
    IsIsoMinor (Graph.ofSimpleGraph (⊤ : SimpleGraph (Fin 7))) (Graph.ofSimpleGraph G) := by
  classical
  let n := Fintype.card V
  let D := (n - 13) / 2
  have hn : 13 ≤ n := by
    let v := Classical.arbitrary V
    have hd := hdeg v
    have hv := G.degree_lt_card_verts v
    dsimp only [n]
    omega
  have hdegree : ∀ v, Fintype.card V ≤ G.degree v + D + 1 := by
    intro v
    have hd := hdeg v
    dsimp only [D, n]
    omega
  have hbudget : selectionBudget nineSelectionSize 6 = 12 := by decide
  apply clique_isIsoMinor_of_nonneighbor_parameters G 11 D 6 nineSelectionSize
    (by omega) hdegree hdeg (nine_parameter_counts n hn hN) (by rw [hbudget])
  rw [hbudget]
  dsimp only [D, n]
  omega

end GraphMinor.Thomason
