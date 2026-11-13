module

public import GraphMinor.Thomason.DominatingSets
import GraphMinor.Thomason.HalfDomination
import Mathlib.Combinatorics.Enumerative.DoubleCounting
import Mathlib.Tactic.Linarith
import Lean.Elab.Tactic.Omega

/-!
# Domination estimates using the actual degree

The pair count behind Thomason's Lemma 3 (1984), p. 263, also bounds
vertices which leave at most an arbitrary number of a chosen set
undominated. Keeping this threshold explicit uses the actual degree
rather than only the fact that the degree is more than half the order.
-/

@[expose] public section
namespace GraphMinor.Thomason
open SimpleGraph Finset
universe u
variable {V : Type u} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

/-- Vertices leaving at most `h` members of `X` undominated. -/
def verticesLeavingAtMost (X : Finset V) (h : ℕ) : Finset V :=
  univ.filter (fun v => (X ∩ undominatedVertices G {v}).card ≤ h)

/-- The missing-pair count gives a lower bound on the number of vertices
leaving at most `h` chosen vertices undominated. Each vertex has at most
`D` non-neighbours other than itself. -/
theorem card_verticesLeavingAtMost (X : Finset V) (h D M : ℕ)
    (hdegree : ∀ v, Fintype.card V ≤ G.degree v + D + 1)
    (hM : M ≤ Fintype.card V)
    (hcount : X.card * D < (Fintype.card V + 1 - M) * (h + 1)) :
    M ≤ (verticesLeavingAtMost G X h).card := by
  let B := univ.filter (fun v => ¬ (X ∩ undominatedVertices G {v}).card ≤ h)
  let S := ∑ v : V, (X ∩ undominatedVertices G {v}).card
  have hsum : S ≤ X.card * D := by
    dsimp only [S]
    rw [sum_card_inter_undominatedVertices_singleton G X]
    calc
      (∑ x ∈ X, (undominatedVertices G {x}).card) ≤ ∑ _ ∈ X, D := by
        apply sum_le_sum
        intro x _
        rw [card_undominatedVertices_singleton]
        have hd := hdegree x
        omega
      _ = X.card * D := by simp
  have hpart : (verticesLeavingAtMost G X h).card + B.card = Fintype.card V := by
    simpa only [verticesLeavingAtMost, B, card_univ] using
      card_filter_add_card_filter_not (s := (univ : Finset V))
        (fun v => (X ∩ undominatedVertices G {v}).card ≤ h)
  by_contra hsmall
  have hB : Fintype.card V + 1 - M ≤ B.card := by omega
  have hlower : B.card * (h + 1) ≤ S := by
    calc
      B.card * (h + 1) = ∑ _ ∈ B, (h + 1) := by simp
      _ ≤ ∑ v ∈ B, (X ∩ undominatedVertices G {v}).card := by
        apply sum_le_sum
        intro v hv
        have hh := (mem_filter.mp hv).2
        omega
      _ ≤ ∑ v : V, (X ∩ undominatedVertices G {v}).card :=
        sum_le_sum_of_subset_of_nonneg (subset_univ B) (fun _ _ _ => Nat.zero_le _)
  have hcontra := (Nat.mul_le_mul_right (h + 1) hB).trans (hlower.trans hsum)
  exact (not_lt_of_ge hcontra) hcount

end GraphMinor.Thomason
