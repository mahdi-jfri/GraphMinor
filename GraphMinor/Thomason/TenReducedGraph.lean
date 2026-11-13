module

public import GraphMinor.Thomason.NonneighborCliqueCriterion
import Mathlib.Tactic.IntervalCases
import Lean.Elab.Tactic.Omega

/-!
# A reduced-graph criterion for the ten-vertex target

Use three singleton selections followed by four pairs, and take the
residual graph as the eighth branch. Three elementary degree bounds
control the number of non-neighbours over orders twenty-two through
forty-five. The finite subset inequalities are checked in the kernel.
-/

public section
namespace GraphMinor.Thomason
open SimpleGraph Finset
universe u

private def tenSelectionSize (j : ℕ) : ℕ := if j < 3 then 1 else 2
private def tenNonneighborCap (n : ℕ) : ℕ := min 12 (min ((n - 16) / 2) ((n - 6) / 3))

private theorem ten_parameter_counts (n : ℕ) (hn : 22 ≤ n) (hn' : n ≤ 45) :
    ∀ j < 7, 0 < tenSelectionSize j ∧ selectionBudget tenSelectionSize j < 14 ∧
      j * (tenNonneighborCap n).choose (tenSelectionSize j) <
        (n - selectionBudget tenSelectionSize j).choose (tenSelectionSize j) := by
  intro j hj
  interval_cases j <;> interval_cases n <;> decide

/-- The reduced eight-vertex clique criterion used for the density
bound at ten vertices. Its degree conditions give explicit bounds on
the complement, rather than assuming any branch-existence step. -/
theorem clique_eight_of_order_le_forty_five {V : Type u} [Fintype V] [Nonempty V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hNlow : 22 ≤ Fintype.card V) (hN : Fintype.card V ≤ 45)
    (hdeg : ∀ v, Fintype.card V + 14 ≤ 2 * G.degree v)
    (hthree : ∀ v, 2 * Fintype.card V + 3 ≤ 3 * G.degree v)
    (htwelve : ∀ v, Fintype.card V ≤ G.degree v + 13) :
    IsIsoMinor (Graph.ofSimpleGraph (⊤ : SimpleGraph (Fin 8))) (Graph.ofSimpleGraph G) := by
  classical
  let n := Fintype.card V
  let D := tenNonneighborCap n
  have hdegree : ∀ v, Fintype.card V ≤ G.degree v + D + 1 := by
    intro v
    have h1 := hdeg v
    have h2 := hthree v
    have h3 := htwelve v
    dsimp only [D, tenNonneighborCap, n]
    omega
  have hbudget : selectionBudget tenSelectionSize 7 = 15 := by decide
  apply clique_isIsoMinor_of_nonneighbor_parameters G 14 D 7 tenSelectionSize
    (by omega) hdegree hdeg (ten_parameter_counts n hNlow hN) (by rw [hbudget])
  rw [hbudget]
  dsimp only [D, tenNonneighborCap, n]
  omega

end GraphMinor.Thomason
