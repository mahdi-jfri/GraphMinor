module

public import GraphMinor.Compute.GM06Alg511SuccTrace
import Mathlib.Data.List.Chain
import Mathlib.Tactic

/-!
# Exact successor steps in a returned flow trace

The full initial linkage in VI (5.11), page 134, follows the raw
successor array of maximum flow. Consecutive vertices of each trace
are exactly a source vertex and its stored successor. This identifies
the edge-choice array's entry with the directed edge required at
each position of every returned path.
-/

public section
namespace GraphMinor.Compute

private theorem traceWalk_chain {n : ℕ} {G : SimpleGraph (Fin n)}
    {A B : Finset (Fin n)} {used pred succ : Fin n → ℕ}
    (hsys : IsValidPathSystem G A B used pred succ) (fuel : ℕ) (u : Fin n) :
    (traceWalk hsys fuel u).2.support.IsChain (fun a b => succ a = b.val) := by
  induction fuel generalizing u with
  | zero => exact .singleton u
  | succ fuel ih =>
    by_cases hnext : succ u < n
    · rw [traceWalk_succ_of_lt hsys fuel u hnext]
      change (u :: (traceWalk hsys fuel ⟨succ u, hnext⟩).2.support).IsChain _
      have ht := ih ⟨succ u, hnext⟩
      rw [← (traceWalk hsys fuel ⟨succ u, hnext⟩).2.cons_tail_support] at ht ⊢
      exact .cons_cons rfl ht
    · rw [traceWalk_succ_of_not_lt hsys fuel u hnext]
      exact .singleton u

/-- Every consecutive pair in a finite successor trace is given by
the actual stored successor value, including every proper prefix. -/
theorem gm06Alg511TraceWalk_successors {n : ℕ} {G : SimpleGraph (Fin n)}
    {A B : Finset (Fin n)} {used pred succ : Fin n → ℕ}
    (hsys : IsValidPathSystem G A B used pred succ) (fuel : ℕ) (u : Fin n) :
    ∀ j (hj : j + 1 < (traceWalk hsys fuel u).2.support.length),
      succ ((traceWalk hsys fuel u).2.support[j]) =
        ((traceWalk hsys fuel u).2.support[j + 1]).val :=
  List.isChain_iff_getElem.mp (traceWalk_chain hsys fuel u)

/-- In the complete source-to-target path extracted from the raw
system, every step follows its stored successor word. -/
theorem gm06Alg511AbWalk_successors {n : ℕ} {G : SimpleGraph (Fin n)}
    {A B : Finset (Fin n)} {used pred succ : Fin n → ℕ}
    (hsys : IsValidPathSystem G A B used pred succ)
    (u : Fin n) (hu : u ∈ pathStarts used pred) :
    ∀ j (hj : j + 1 < (abWalkOfStart hsys u hu).walk.support.length),
      succ ((abWalkOfStart hsys u hu).walk.support[j]) =
        ((abWalkOfStart hsys u hu).walk.support[j + 1]).val :=
  gm06Alg511TraceWalk_successors hsys n u

end GraphMinor.Compute
