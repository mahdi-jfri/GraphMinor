module

public import GraphMinor.Compute.GM02RowMajorPairs
import Mathlib.Data.List.Sort

/-!
# Recognizing canonical graph edge lists by their order

Row-major pair numbering strictly increases through the canonical pair
list. Filtering preserves that order. A list with the same members and
the same strict order is therefore the canonical edge list. This lets
the terminal builder scan active pattern positions directly while still
producing the exact encoding required by the terminated-graph program.
-/

public section
namespace GraphMinor.Compute

/-- Canonical graph edges have strictly increasing row-major pair numbers. -/
theorem gm02EdgeListOf_pairwise_rank {n : ℕ} (F : SimpleGraph (Fin n)) [DecidableRel F.Adj] :
    (edgeListOf F).Pairwise (fun p q =>
      (finProdFinEquiv p).val < (finProdFinEquiv q).val) := by
  apply List.Pairwise.filter
  rw [gm02AllPairs_eq_ofFn, List.pairwise_ofFn]
  intro i j hij
  rw [Equiv.apply_symm_apply, Equiv.apply_symm_apply]
  exact hij

/-- A correctly ordered list with exactly the increasing adjacent pairs is the canonical edge list. -/
theorem gm02EdgeListOf_eq_of_pairwise_rank {n : ℕ} (F : SimpleGraph (Fin n)) [DecidableRel F.Adj]
    (L : List (Fin n × Fin n))
    (hL : L.Pairwise (fun p q => (finProdFinEquiv p).val < (finProdFinEquiv q).val))
    (hmem : ∀ p, p ∈ L ↔ p.1.val < p.2.val ∧ F.Adj p.1 p.2) : L = edgeListOf F := by
  let R : (Fin n × Fin n) → (Fin n × Fin n) → Prop :=
    fun p q => (finProdFinEquiv p).val < (finProdFinEquiv q).val
  let : Std.Antisymm R := ⟨fun _ _ h₁ h₂ => False.elim (Nat.lt_asymm h₁ h₂)⟩
  let : Std.Irrefl R := ⟨fun _ => Nat.lt_irrefl _⟩
  exact List.Pairwise.eq_of_mem_iff (r := R) hL (gm02EdgeListOf_pairwise_rank F)
    (fun p => (hmem p).trans (mem_edgeListOf F p).symm)

end GraphMinor.Compute
