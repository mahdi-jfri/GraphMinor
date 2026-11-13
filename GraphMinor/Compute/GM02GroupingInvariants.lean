module

public import GraphMinor.Compute.GM02GroupingStepBounds

/-!
# Correctness of the component-grouping scan

Before the threshold is reached, the selected side contains every
previously scanned vertex outside the separator. Its terminal count is
less than one third of the total. After the threshold is reached, the
chosen side stays fixed and has the required balance bounds. Component
closure and avoidance of the separator hold throughout the scan.
-/

public section
namespace GraphMinor.Compute
open Classical

/-- The data-only grouping state satisfies all required invariants after
any prefix of the vertex scan in II (3.1)'s successful-output construction. -/
theorem gm02GroupingState_invariants {n : ℕ} (G : SimpleGraph (Fin n))
    (Q X : Finset (Fin n))
    (hcomp : ∀ a ∉ X, 3 * (gm02FiniteComponent G X a ∩ Q).card ≤ 2 * (Q \ X).card)
    (i : ℕ) (hi : i ≤ n) :
    let st := gm02GroupingState G Q X i
    Disjoint X st.1 ∧ (∀ a ∈ st.1, gm02FiniteComponent G X a ⊆ st.1) ∧
      (st.2 = true → (Q \ X).card ≤ 3 * (st.1 ∩ Q).card ∧
        3 * (st.1 ∩ Q).card ≤ 2 * (Q \ X).card) ∧
      (st.2 = false → 3 * (st.1 ∩ Q).card < (Q \ X).card) ∧
      (st.2 = false → ∀ a : Fin n, a.val < i → a ∉ X → a ∈ st.1) := by
  induction i with
  | zero =>
    dsimp only [gm02GroupingState]
    refine ⟨Finset.disjoint_empty_right _, by simp, ?_, ?_, ?_⟩
    · intro hr
      have hz := of_decide_eq_true hr
      simp only [Finset.empty_inter, Finset.card_empty, Nat.mul_zero]
      exact ⟨Nat.le_of_eq hz, Nat.zero_le _⟩
    · intro hr
      have hz := of_decide_eq_false hr
      simp only [Finset.empty_inter, Finset.card_empty, Nat.mul_zero]
      exact Nat.pos_of_ne_zero hz
    · intro _ a ha _
      omega
  | succ i ih =>
    have hin : i < n := by omega
    obtain ⟨hdis, hclosed, hready, hnotready, hcover⟩ := ih (Nat.le_of_succ_le hi)
    let st := gm02GroupingState G Q X i
    let a : Fin n := ⟨i, hin⟩
    have hstep := gm02GroupingStep_bounds G Q X a st hcomp hdis hclosed hready hnotready
    rw [gm02GroupingState, dite_eq_left hin]
    dsimp only
    refine ⟨hstep.1, hstep.2.1, hstep.2.2.1, hstep.2.2.2, ?_⟩
    intro hout v hv hvX
    have hfalse : st.2 = false := by
      cases he : st.2 with
      | false => rfl
      | true =>
        have htrue : (gm02GroupingStep G Q X a st).2 = true := by
          simp only [gm02GroupingStep, he, ↓reduceIte]
        rw [hout] at htrue
        contradiction
    have hsubset := gm02GroupingStep_subset_of_not_ready G Q X a st hout
    rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hv) with hlt | heq
    · exact hsubset (hcover hfalse v hlt hvX)
    · have hva : v = a := Fin.ext heq
      subst v
      rcases gm02GroupingStep_ready_or_mem G Q X a st hvX with htrue | hmem
      · rw [hout] at htrue
        contradiction
      · exact hmem

end GraphMinor.Compute
