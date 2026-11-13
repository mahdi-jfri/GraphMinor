module

public import Mathlib.Data.Set.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
# Distance along a chain of circuit insides

The proof of Graph Minors XII, (4.1), page 248, bounds the distance between
its endpoints by adding the costs of a chain of overlapping circuit insides.
This file proves that step for any natural-valued distance satisfying the
triangle inequality. The sets need not be disjoint or have distinct endpoints.
-/

public section

namespace GraphMinor.GM12

/-- The first inequality in the circuit-chain calculation of Graph Minors XII,
(4.1), page 248. Choose a point in each consecutive intersection and apply the
triangle inequality. A bound within each set then gives the sum of the costs. -/
theorem distance_le_chain_sum {α : Type*} (d : α → α → ℕ)
    (htriangle : ∀ x y z, d x z ≤ d x y + d y z)
    {n : ℕ} (C : Fin (n + 1) → Set α) (cost : Fin (n + 1) → ℕ)
    (hcost : ∀ i, ∀ x ∈ C i, ∀ y ∈ C i, d x y ≤ cost i)
    (hmeet : ∀ i : Fin n, (C i.castSucc ∩ C i.succ).Nonempty)
    {u v : α} (hu : u ∈ C 0) (hv : v ∈ C (Fin.last n)) :
    d u v ≤ ∑ i, cost i := by
  induction n generalizing u with
  | zero =>
      simpa using hcost 0 u hu v hv
  | succ n ih =>
      obtain ⟨x, hx, hx'⟩ := hmeet 0
      have htail : d x v ≤ ∑ i : Fin (n + 1), cost i.succ := by
        apply ih (fun i => C i.succ) (fun i => cost i.succ)
          (fun i => hcost i.succ)
        · intro i
          exact hmeet i.succ
        · exact hx'
        · exact hv
      calc
        d u v ≤ d u x + d x v := htriangle u x v
        _ ≤ cost 0 + ∑ i : Fin (n + 1), cost i.succ :=
          Nat.add_le_add (hcost 0 u hu x hx) htail
        _ = ∑ i, cost i := (Fin.sum_univ_succ cost).symm

end GraphMinor.GM12
