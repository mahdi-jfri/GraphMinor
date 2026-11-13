module

public import GraphMinor.Thomason.HalfDomination
public import Mathlib.Data.Finset.Powerset
import Lean.Elab.Tactic.Omega

/-!
# Finite families of almost-dominating subsets

Thomason's Lemma 5, page 263 (1984), counts `k`-subsets leaving at most
`floor(n/2^k)` vertices undominated. We define that family and prove that
adjoining a vertex which dominates half of the uncovered vertices gives
a member of the next family.
-/

@[expose] public section

namespace GraphMinor.Thomason

open SimpleGraph Finset

universe u
variable {V : Type u} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

/-- The `k`-subsets leaving at most `floor(n/2^k)` vertices undominated,
as in Thomason's Lemma 5, page 263. -/
def almostDominatingSets (k : ℕ) : Finset (Finset V) :=
  (univ : Finset V).powersetCard k |>.filter
    (fun Y => (undominatedVertices G Y).card ≤ Fintype.card V / 2 ^ k)

/-- Membership records both the order and the undominated-vertex bound. -/
theorem mem_almostDominatingSets_iff (k : ℕ) (Y : Finset V) :
    Y ∈ almostDominatingSets G k ↔
      Y.card = k ∧ (undominatedVertices G Y).card ≤ Fintype.card V / 2 ^ k := by
  simp only [almostDominatingSets, mem_filter, mem_powersetCard, subset_univ, true_and]

/-- The empty set is the member of the zero-th family. -/
theorem empty_mem_almostDominatingSets : (∅ : Finset V) ∈ almostDominatingSets G 0 := by
  rw [mem_almostDominatingSets_iff]
  simp

/-- Adding a vertex which dominates half of the uncovered set advances
the order and halves the uncovered-vertex bound. -/
theorem insert_mem_almostDominatingSets {k : ℕ} {Y : Finset V} {v : V}
    (hY : Y ∈ almostDominatingSets G k) (hvY : v ∉ Y)
    (hv : v ∈ verticesDominatingHalf G (undominatedVertices G Y)) :
    insert v Y ∈ almostDominatingSets G (k + 1) := by
  obtain ⟨hcard, hbound⟩ := (mem_almostDominatingSets_iff G k Y).mp hY
  apply (mem_almostDominatingSets_iff G (k + 1) (insert v Y)).mpr
  refine ⟨by rw [card_insert_of_notMem hvY, hcard], ?_⟩
  have hhalf : 2 * (undominatedVertices G Y ∩ undominatedVertices G {v}).card ≤
      (undominatedVertices G Y).card := (mem_filter.mp hv).2
  have heq : undominatedVertices G (insert v Y) =
      undominatedVertices G Y ∩ undominatedVertices G {v} := by
    rw [undominatedVertices_insert]
    ext x
    simp only [undominatedVertices, dominatedVertices_singleton,
      mem_sdiff, mem_inter, mem_univ, true_and]
  have hnew : (undominatedVertices G (insert v Y)).card ≤
      (undominatedVertices G Y).card / 2 := by
    rw [heq]
    omega
  calc
    (undominatedVertices G (insert v Y)).card ≤ (undominatedVertices G Y).card / 2 := hnew
    _ ≤ (Fintype.card V / 2 ^ k) / 2 := Nat.div_le_div_right hbound
    _ = Fintype.card V / 2 ^ (k + 1) := by rw [Nat.div_div_eq_div_mul, pow_succ]

end GraphMinor.Thomason
