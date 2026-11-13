module

public import GraphMinor.Compute.GM06Alg511TurnWords
import Mathlib.Tactic

/-!
# Word bounds for computed path turn sums

The winding phase of VI (5.11), page 134, sums signed edge words
along a simple path. Each magnitude word is bounded by the sum of
the supplied magnitudes. Multiplying that sum by the vertex count
therefore bounds both accumulators, for every selected dart trace.
-/

public section
namespace GraphMinor.Compute

private theorem word_le_sum (words : List ℕ) (v : ℕ) (hv : v ∈ words) : v ≤ words.sum := by
  induction words with
  | nil => simp at hv
  | cons a as ih =>
    rcases List.mem_cons.mp hv with rfl | hv
    · simp
    · exact (ih hv).trans (by simp)

private theorem mapped_sum_le (xs : List ℕ) (f : ℕ → ℕ) (M : ℕ)
    (h : ∀ x ∈ xs, f x ≤ M) : (xs.map f).sum ≤ xs.length * M := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    have htail := ih (fun y hy => h y (List.mem_cons_of_mem _ hy))
    have hx := h x (by simp)
    simp only [List.map_cons, List.sum_cons, List.length_cons]
    calc
      f x + (xs.map f).sum ≤ M + xs.length * M := Nat.add_le_add hx htail
      _ = (xs.length + 1) * M := by ring

/-- A single numeric product bound on supplied magnitudes bounds
both accumulators for every valid dart trace of at most `n` entries. -/
theorem gm06Alg511TurnSum_word_bounds {w n : ℕ} (turns : List ℤ) (darts : List ℕ)
    (hlen : darts.length ≤ n) (hdarts : ∀ d ∈ darts, d < 2 * turns.length)
    (hproduct : n * (gm06Alg511TurnWords turns).sum < 2 ^ w) :
    (darts.map (fun d => (gm06Alg511TurnWords turns).getD d 0)).sum < 2 ^ w ∧
    (darts.map (fun d => (gm06Alg511TurnWords turns).getD (gm06DartMate d) 0)).sum < 2 ^ w := by
  have hget (d : ℕ) (hd : d < 2 * turns.length) :
      (gm06Alg511TurnWords turns).getD d 0 ≤ (gm06Alg511TurnWords turns).sum := by
    have hd' : d < (gm06Alg511TurnWords turns).length := by
      simpa only [gm06Alg511TurnWords_length] using hd
    apply word_le_sum
    simpa only [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hd',
      Option.getD_some] using List.getElem_mem hd'
  constructor
  · exact ((mapped_sum_le darts _ _ (fun d hd => hget d (hdarts d hd))).trans
      (Nat.mul_le_mul_right _ hlen)).trans_lt hproduct
  · exact ((mapped_sum_le darts _ _ (fun d hd => hget _ (gm06DartMate_lt (hdarts d hd)))).trans
      (Nat.mul_le_mul_right _ hlen)).trans_lt hproduct

end GraphMinor.Compute
