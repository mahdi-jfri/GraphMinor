module

public import GraphMinor.Compute.Case3StepsBucketTotal
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.Linarith

/-!
# Total work for encoding the selected members

Each member scan costs linear vertex work plus linear work in its bucket.
The bucket lengths sum to the stored pair count. Summing even over all
candidate labels therefore gives the required quadratic vertex and linear
pair bound for writing the division's member data.
-/

public section

namespace GraphMinor.Compute

open scoped BigOperators

/-- The sum of the per-member encoding bounds counts each pair record once. -/
theorem case3MemberEncoding_sum_cost {A L : ℕ} (owner : Fin A → ℕ)
    (howner : ∀ j, owner j < L) (n : ℕ) :
    (∑ b : Fin L, (78 * n + 83 * (case3BucketIndices owner b.1 0).length + 129)) =
      L * (78 * n + 129) + 83 * A := by
  calc
    _ = ∑ b : Fin L, ((78 * n + 129) + 83 * (case3BucketIndices owner b.1 0).length) := by
      apply Finset.sum_congr rfl
      intro b _
      omega
    _ = L * (78 * n + 129) + 83 * ∑ b : Fin L, (case3BucketIndices owner b.1 0).length := by
      rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
        Nat.nsmul_eq_mul, Finset.mul_sum]
    _ = _ := by rw [case3BucketIndices_sum_length owner howner]

/-- Any selected subset of candidate encodings obeys the same total bound. -/
theorem case3MemberEncoding_selected_cost {A L : ℕ} (owner : Fin A → ℕ)
    (howner : ∀ j, owner j < L) (n : ℕ) (selected : Finset (Fin L)) :
    (∑ b ∈ selected, (78 * n + 83 * (case3BucketIndices owner b.1 0).length + 129)) ≤
      L * (78 * n + 129) + 83 * A := by
  rw [← case3MemberEncoding_sum_cost owner howner n]
  exact Finset.sum_le_sum_of_subset (Finset.subset_univ selected)

/-- The encoding bound fits the case (iii) graph-size parameter. -/
theorem case3MemberEncoding_cost_le {k m a n e : ℕ} (hk : k ≤ n) (hm : m ≤ a) (ha : a ≤ e) :
    (k + m) * (78 * k + 129) + 83 * a ≤ 1000 * ((n + 1) * (e + n + 1)) := by
  have hkk := Nat.mul_le_mul hk hk
  have hkm := Nat.mul_le_mul hk (hm.trans ha)
  nlinarith [Nat.zero_le (n * e), Nat.zero_le (n * n)]

end GraphMinor.Compute
