module

public import GraphMinor.Thomason.NonneighborCliqueCriterion
import Mathlib.Tactic.IntervalCases
import Lean.Elab.Tactic.Omega

/-!
# A reduced-graph criterion for the eleven-vertex target

Use four singleton selections, three pairs, and one triple, and take the
residual graph as the eighth branch. Three elementary degree bounds
control the number of non-neighbours over orders twenty-six through
fifty-three. The finite subset inequalities are checked in the kernel.
-/

public section
namespace GraphMinor.Thomason
open SimpleGraph Finset
universe u

private def elevenSelectionSize (j : ℕ) : ℕ := if j < 4 then 1 else if j < 7 then 2 else 3
private def elevenNonneighborCap (n : ℕ) : ℕ := min 14 (min ((n - 19) / 2) ((n - 7) / 3))

private theorem eleven_parameter_counts (n : ℕ) (hn : 26 ≤ n) (hn' : n ≤ 53) :
    ∀ j < 8, 0 < elevenSelectionSize j ∧ selectionBudget elevenSelectionSize j < 17 ∧
      j * (elevenNonneighborCap n).choose (elevenSelectionSize j) <
        (n - selectionBudget elevenSelectionSize j).choose (elevenSelectionSize j) := by
  intro j hj
  interval_cases j <;> interval_cases n <;> decide

/-- The reduced nine-vertex clique criterion used for the density
bound at ten vertices. Its degree conditions give explicit bounds on
the complement, rather than assuming any branch-existence step. -/
theorem clique_nine_of_order_le_fifty_three {V : Type u} [Fintype V] [Nonempty V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hNlow : 26 ≤ Fintype.card V) (hN : Fintype.card V ≤ 53)
    (hdeg : ∀ v, Fintype.card V + 17 ≤ 2 * G.degree v)
    (hthree : ∀ v, 2 * Fintype.card V + 4 ≤ 3 * G.degree v)
    (htwelve : ∀ v, Fintype.card V ≤ G.degree v + 15) :
    IsIsoMinor (Graph.ofSimpleGraph (⊤ : SimpleGraph (Fin 9))) (Graph.ofSimpleGraph G) := by
  classical
  let n := Fintype.card V
  let D := elevenNonneighborCap n
  have hdegree : ∀ v, Fintype.card V ≤ G.degree v + D + 1 := by
    intro v
    have h1 := hdeg v
    have h2 := hthree v
    have h3 := htwelve v
    dsimp only [D, elevenNonneighborCap, n]
    omega
  have hbudget : selectionBudget elevenSelectionSize 8 = 18 := by decide
  apply clique_isIsoMinor_of_nonneighbor_parameters G 17 D 8 elevenSelectionSize
    (by omega) hdegree hdeg (eleven_parameter_counts n hNlow hN) (by rw [hbudget])
  rw [hbudget]
  dsimp only [D, elevenNonneighborCap, n]
  omega

end GraphMinor.Thomason
