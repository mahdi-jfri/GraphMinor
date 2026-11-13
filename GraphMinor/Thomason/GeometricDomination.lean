module

public import GraphMinor.Thomason.ResidualFamilies
import GraphMinor.Thomason.ResidualCount
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega

/-!
# Geometric uncovered-vertex bounds

The missing-pair estimate allows each selected vertex to reduce the
uncovered bound by the ratio of the non-neighbour bound to the number
of vertices left after reserving the possible selection choices. Round
down at every step. The resulting recurrence is bounded by a single
rounded geometric expression, giving an explicit subset count.
-/

@[expose] public section
namespace GraphMinor.Thomason
open SimpleGraph Finset

/-- Repeated reduction of an uncovered bound by the ratio `D/B`, with
rounding down after each selection. -/
def residualDecay (N D B : ℕ) : ℕ → ℕ
  | 0 => N
  | k + 1 => residualDecay N D B k * D / B

/-- The rounded recurrence meets the strict missing-pair inequality. -/
theorem residualDecay_budget (N D B k : ℕ) (hB : 0 < B) :
    residualDecay N D B k * D < B * (residualDecay N D B (k + 1) + 1) := by
  rw [residualDecay]
  exact (Nat.div_lt_iff_lt_mul hB).mp (Nat.lt_succ_self _) |>.trans_eq (Nat.mul_comm _ _)

/-- Before division, the recurrence is bounded by its geometric product. -/
theorem residualDecay_mul_pow_le (N D B k : ℕ) :
    residualDecay N D B k * B ^ k ≤ N * D ^ k := by
  induction k with
  | zero => simp [residualDecay]
  | succ k ih =>
    have hd := Nat.div_mul_le_self (residualDecay N D B k * D) B
    calc
      residualDecay N D B (k + 1) * B ^ (k + 1) =
          (residualDecay N D B k * D / B * B) * B ^ k := by rw [residualDecay, pow_succ]; ring
      _ ≤ (residualDecay N D B k * D) * B ^ k := Nat.mul_le_mul_right _ hd
      _ = (residualDecay N D B k * B ^ k) * D := by ring
      _ ≤ (N * D ^ k) * D := Nat.mul_le_mul_right _ ih
      _ = N * D ^ (k + 1) := by rw [pow_succ]; ring

/-- Repeated rounding down is bounded by rounding the geometric bound once. -/
theorem residualDecay_le_div_pow (N D B k : ℕ) (hB : 0 < B) :
    residualDecay N D B k ≤ N * D ^ k / B ^ k := by
  exact (Nat.le_div_iff_mul_le (pow_pos hB k)).mpr (residualDecay_mul_pow_le N D B k)

universe u
variable {V : Type u} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

/-- The degree-sensitive subset count with the explicit rounded recurrence. -/
theorem card_residualBoundedSets_decay (M D k : ℕ) (hM : M ≤ Fintype.card V)
    (hdegree : ∀ v, Fintype.card V ≤ G.degree v + D + 1) :
    M.choose k ≤ (residualBoundedSets G k
      (residualDecay (Fintype.card V) D (Fintype.card V + 1 - M) k)).card := by
  apply card_residualBoundedSets G M D hM hdegree _ (le_refl _) _ k
  intro j
  exact residualDecay_budget _ _ _ _ (by omega)

/-- A geometric replacement for the halving bound in Thomason's Lemma 5.
It uses the actual non-neighbour bound `D` and counts at least
`choose(M,k)` selected sets. -/
theorem card_residualBoundedSets_geometric (M D k : ℕ) (hM : M ≤ Fintype.card V)
    (hdegree : ∀ v, Fintype.card V ≤ G.degree v + D + 1) :
    M.choose k ≤ (residualBoundedSets G k
      (Fintype.card V * D ^ k / (Fintype.card V + 1 - M) ^ k)).card := by
  apply (card_residualBoundedSets_decay G M D k hM hdegree).trans
  apply card_le_card
  intro Y hY
  obtain ⟨hcard, hbound⟩ := (mem_residualBoundedSets_iff G _ _ Y).mp hY
  exact (mem_residualBoundedSets_iff G _ _ Y).mpr
    ⟨hcard, hbound.trans (residualDecay_le_div_pow _ _ _ _ (by omega))⟩

end GraphMinor.Thomason
