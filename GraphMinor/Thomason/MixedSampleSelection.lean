module

public import GraphMinor.Thomason.SelectionMethods
import Lean.Elab.Tactic.Omega

/-!
# Choosing among three connected branch constructions

Apply the proved selection theorem for the chosen candidate family.
The exceptional and uncovered counts use the same units as that family.
This permits a different choice at each stage of the clique construction.
-/

public section
namespace GraphMinor.Thomason
open SimpleGraph Finset
universe u v
variable {V : Type u} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

/-- Each of the three sample methods constructs a connected set from its
proved candidate and uncovered-count bounds. -/
theorem exists_connected_selection_avoiding
    {I : Type v} [DecidableEq I] (indices : Finset I) (B : I → Finset V) (t : I → ℕ)
    (D k T : ℕ) (method : SelectionMethod) (hk : 0 < k) (hD : D ≤ Fintype.card V)
    (hdegree : ∀ v, Fintype.card V ≤ G.degree v + D + 1)
    (hnear : ∀ v, Fintype.card V ≤ 2 * G.degree v + 1)
    (hB : ∀ i ∈ indices, (B i).card ≤ t i)
    (hcount : selectionUncoveredBound (Fintype.card V) D k method <
      (selectionCount (Fintype.card V) D k method -
        ∑ i ∈ indices, selectionExceptionBound (t i) k method) * (T + 1) ∨
      (D ≤ T ∧ (∑ i ∈ indices, selectionExceptionBound (t i) k method) <
        selectionCount (Fintype.card V) D k method)) :
    ∃ X : Finset V, X.card ≤ selectionCost (Fintype.card V) D k method ∧
      (G.induce (X : Set V)).Connected ∧ (undominatedVertices G X).card ≤ T ∧
      ∀ i ∈ indices, ¬ X ⊆ B i := by
  cases method with
  | hub =>
    exact exists_connected_star_candidate_avoiding G indices B t D k T false hk
      hdegree hnear hB hcount
  | star =>
    exact exists_connected_star_candidate_avoiding G indices B t D k T true hk
      hdegree hnear hB hcount
  | oneMissed =>
    have heq : k - 1 + 1 = k := Nat.sub_add_cancel hk
    obtain ⟨X, hcard, hconn, hundom, havoid⟩ := exists_connected_oneMissedSet_avoiding G
      indices B t (k - 1) D T hD hdegree hnear hB (by
        simpa only [heq, selectionUncoveredBound, selectionCount, selectionExceptionBound] using hcount)
    refine ⟨X, ?_, hconn, hundom, havoid⟩
    change X.card ≤ k + 1
    omega

end GraphMinor.Thomason
