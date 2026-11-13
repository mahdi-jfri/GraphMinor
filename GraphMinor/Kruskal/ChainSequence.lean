module

public import GraphMinor.Kruskal.ChainSubdivision
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise

/-!
# Finite subdivision sequences for edge chains

Induct on the total number of internal vertices over the finite edge set.
Remove one internal vertex from a nonempty chain, apply induction, then
append the literal subdivision step that restores it. This proves that
simultaneously replacing all edges by finite chains is a subdivision.
-/

public section

namespace GraphMinor.Kruskal

open Graph Set
open scoped BigOperators

/-- Replacing finitely many edges by chains is a finite sequence of edge
subdivisions. The sum of the internal-vertex counts is the induction rank. -/
theorem edgeChains_subdivisions {V E : Type*} [Fintype E] [DecidableEq E]
    (left right : E → V) (n : E → ℕ) :
    Relation.ReflTransGen GM04.IsEdgeSubdivision
      (edgeChains left right (fun _ ↦ 0)) (edgeChains left right n) := by
  induction hs : (∑ e, n e) using Nat.strong_induction_on generalizing n with
  | _ s ih =>
    by_cases hz : ∀ e, n e = 0
    · have hn : n = fun _ ↦ 0 := funext hz
      rw [hn]
    · push Not at hz
      obtain ⟨e, he⟩ := hz
      let m := Function.update n e (n e - 1)
      have hsum : (∑ i, n i) = n e + ∑ i ∈ Finset.univ \ {e}, n i := by
        simpa only [Function.update_eq_self] using
          Finset.sum_update_of_mem (Finset.mem_univ e) n (n e)
      have hlt : (∑ i, m i) < s := by
        change (∑ i, Function.update n e (n e - 1) i) < s
        rw [Finset.sum_update_of_mem (Finset.mem_univ e)]
        omega
      have hupdate : Function.update m e (m e + 1) = n := by
        funext i
        by_cases hi : i = e
        · subst i
          simp only [Function.update_self, m]
          omega
        · simp only [Function.update_of_ne hi, m]
      have hprev := ih _ hlt m rfl
      have hstep := edgeChains_subdivision_step left right m e
      rw [hupdate] at hstep
      exact hprev.tail hstep

/-- The chain construction meets the natural-name definition of topological
containment whenever the original vertex names are countable. -/
theorem edgeChains_isTopologicalMinor {V E : Type*} [Countable V] [Fintype E]
    (left right : E → V) (n : E → ℕ) :
    GM04.IsTopologicalMinor (edgeChains left right (fun _ ↦ 0))
      (edgeChains left right n) := by
  classical
  exact isTopologicalMinor_of_countable_subdivisions (edgeChains_subdivisions left right n)

end GraphMinor.Kruskal
