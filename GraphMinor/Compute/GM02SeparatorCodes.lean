module

public import GraphMinor.Compute.GM02TupleVertices
public import Mathlib.Data.Nat.Digits.Defs

/-!
# Enumerating separator tuples by integer codes

Use base one plus the vertex count. A fixed-length numeric tuple is
encoded by its base expansion, and division and remainder recover each
slot. All tuples occur among the codes below the corresponding power.
Combining this with the slot representation proves that this loop visits
every permitted separator in II (3.1), page 316, including the empty graph.
-/

@[expose] public section
namespace GraphMinor.Compute
open Classical

/-- The integer code of a fixed-length separator tuple. -/
def gm02SeparatorCode {k : ℕ} (n : ℕ) (f : Fin k → ℕ) : ℕ :=
  Nat.ofDigits (n + 1) (List.ofFn f)

/-- Recover the numbered slot by division and remainder. -/
def gm02SeparatorDigit (n code i : ℕ) : ℕ := code / (n + 1) ^ i % (n + 1)

/-- Every decoded slot is either a vertex number or the empty-slot number. -/
theorem gm02SeparatorDigit_le (n code i : ℕ) : gm02SeparatorDigit n code i ≤ n :=
  Nat.le_of_lt_succ (Nat.mod_lt _ (Nat.succ_pos n))

/-- The base code recovers all slots, including empty slots. -/
theorem gm02SeparatorDigit_code {n k : ℕ} (f : Fin k → ℕ) (hf : ∀ i, f i ≤ n)
    (i : Fin k) : gm02SeparatorDigit n (gm02SeparatorCode n f) i.val = f i := by
  have hdigits : ∀ d ∈ List.ofFn f, d < n + 1 := by
    intro d hd
    obtain ⟨j, rfl⟩ := List.mem_ofFn.1 hd
    exact Nat.lt_succ_of_le (hf j)
  have hi : i.val < (List.ofFn f).length := by simpa only [List.length_ofFn] using i.isLt
  rw [gm02SeparatorDigit, gm02SeparatorCode,
    Nat.ofDigits_div_pow_eq_ofDigits_drop _ (Nat.succ_pos n) _ hdigits,
    List.drop_eq_getElem_cons hi, Nat.ofDigits_cons, List.getElem_ofFn]
  simp only [Nat.add_mod, Nat.mul_mod_right, Nat.add_zero,
    Nat.mod_eq_of_lt (Nat.lt_succ_of_le (hf i))]

/-- Every permitted tuple code lies in the polynomial enumeration range. -/
theorem gm02SeparatorCode_lt {n k : ℕ} (f : Fin k → ℕ) (hf : ∀ i, f i ≤ n) :
    gm02SeparatorCode n f < (n + 1) ^ k := by
  cases n with
  | zero =>
    have he : f = fun _ => 0 := by funext i; exact Nat.eq_zero_of_le_zero (hf i)
    simp [gm02SeparatorCode, he]
  | succ n =>
    have hd : ∀ d ∈ List.ofFn f, d < n + 1 + 1 := by
      intro d hd
      obtain ⟨j, rfl⟩ := List.mem_ofFn.1 hd
      exact Nat.lt_succ_of_le (hf j)
    simpa only [gm02SeparatorCode, List.length_ofFn] using
      Nat.ofDigits_lt_base_pow_length (by omega : 1 < n + 1 + 1) hd

/-- Scanning integer codes visits every separator of size at most the
fixed bound; the input contains only the graph and the original subset. -/
theorem exists_gm02SeparatorCode {n k : ℕ} (X : Finset (Fin n)) (hX : X.card ≤ k) :
    ∃ code < (n + 1) ^ k,
      gm02SlotVertices (fun i : Fin k => gm02SeparatorDigit n code i.val) = X := by
  obtain ⟨f, hf, hrep⟩ := exists_gm02SlotVertices X hX
  refine ⟨gm02SeparatorCode n f, gm02SeparatorCode_lt f hf, ?_⟩
  simpa only [gm02SeparatorDigit_code f hf] using hrep

end GraphMinor.Compute
