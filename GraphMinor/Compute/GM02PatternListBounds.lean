module

public import GraphMinor.Compute.GM02PatternCall
import Mathlib.Tactic.Ring

/-!
# Common bounds for a fixed finite pattern family

Choose a word coefficient and time exponent larger than each member's
by summing the fixed member bounds. Sum the time coefficients too.
The extra constants cover the finite scan's guards and final answer
copy, including the case of an empty pattern family.
-/

public section
namespace GraphMinor.Compute

/-- A common word coefficient for all tests in the fixed family. -/
@[expose] noncomputable def gm02PatternListWordCoefficient (ps : List GM02EdgeListInput) (w : ℤ) : ℕ :=
  4 + (ps.map (fun J => gm02InjectionWordCoefficient (gm02PatternWidthParameter J w) J)).sum

/-- A common polynomial exponent for all tests in the fixed family. -/
@[expose] noncomputable def gm02PatternListExponent (ps : List GM02EdgeListInput) (w : ℤ) : ℕ :=
  2 + (ps.map (fun J => gm02InjectionPolynomialExponent (gm02PatternWidthParameter J w) J)).sum

/-- A common time coefficient including the sequential guards and final output copy. -/
@[expose] noncomputable def gm02PatternListCoefficient (ps : List GM02EdgeListInput) (w : ℤ) : ℕ :=
  4 + (ps.map (fun J => gm02PatternCallCoefficient J w + 2)).sum

private theorem le_sum_map {ι : Type*} (f : ι → ℕ) (ps : List ι) (i : ι) :
    i ∈ ps → f i ≤ (ps.map f).sum := by
  induction ps with
  | nil => intro h; exact (List.not_mem_nil h).elim
  | cons j ps ih =>
    intro h
    simp only [List.map_cons, List.sum_cons]
    rcases List.mem_cons.1 h with rfl | h
    · exact Nat.le_add_right _ _
    · exact (ih h).trans (Nat.le_add_left _ _)

/-- Each member's word coefficient is bounded by the family's common coefficient. -/
theorem gm02PatternList_word_le (ps : List GM02EdgeListInput) (w : ℤ)
    (J : GM02EdgeListInput) (hJ : J ∈ ps) :
    gm02InjectionWordCoefficient (gm02PatternWidthParameter J w) J ≤ gm02PatternListWordCoefficient ps w := by
  unfold gm02PatternListWordCoefficient
  have h := le_sum_map (fun K : GM02EdgeListInput =>
    gm02InjectionWordCoefficient (gm02PatternWidthParameter K w) K) ps J hJ
  exact h.trans (Nat.le_add_left _ 4)

/-- Each member's exponent is bounded by the family's common exponent. -/
theorem gm02PatternList_exponent_le (ps : List GM02EdgeListInput) (w : ℤ)
    (J : GM02EdgeListInput) (hJ : J ∈ ps) :
    gm02InjectionPolynomialExponent (gm02PatternWidthParameter J w) J ≤ gm02PatternListExponent ps w := by
  unfold gm02PatternListExponent
  have h := le_sum_map (fun K : GM02EdgeListInput =>
    gm02InjectionPolynomialExponent (gm02PatternWidthParameter K w) K) ps J hJ
  exact h.trans (Nat.le_add_left _ 2)

private theorem sum_time_bound (ps : List GM02EdgeListInput) (w : ℤ) (n D : ℕ) :
    (∀ J ∈ ps, gm02InjectionPolynomialExponent (gm02PatternWidthParameter J w) J ≤ D) →
    (ps.map (fun J => gm02PatternCallCoefficient J w *
      (n + 1) ^ gm02InjectionPolynomialExponent (gm02PatternWidthParameter J w) J + 2)).sum ≤
      (ps.map (fun J => gm02PatternCallCoefficient J w + 2)).sum * (n + 1) ^ D := by
  induction ps with
  | nil => intro _; simp
  | cons J ps ih =>
    intro hD
    have hrest := ih (fun K hK => hD K (List.mem_cons_of_mem J hK))
    have hp := Nat.pow_le_pow_right (by omega : 1 ≤ n + 1) (hD J List.mem_cons_self)
    have hone : 1 ≤ (n + 1) ^ D := Nat.one_le_pow D _ (by omega)
    have hhead : gm02PatternCallCoefficient J w *
        (n + 1) ^ gm02InjectionPolynomialExponent (gm02PatternWidthParameter J w) J + 2 ≤
        (gm02PatternCallCoefficient J w + 2) * (n + 1) ^ D := by
      have hm := Nat.mul_le_mul_left (gm02PatternCallCoefficient J w) hp
      rw [Nat.add_mul]
      omega
    simpa only [List.map_cons, List.sum_cons, Nat.add_mul] using Nat.add_le_add hhead hrest

/-- The sum of all guarded tests and the final output copy has one fixed polynomial bound. -/
theorem gm02PatternList_time_le (ps : List GM02EdgeListInput) (w : ℤ) (n : ℕ) :
    (ps.map (fun J => gm02PatternCallCoefficient J w *
      (n + 1) ^ gm02InjectionPolynomialExponent (gm02PatternWidthParameter J w) J + 2)).sum + 4 ≤
      gm02PatternListCoefficient ps w * (n + 1) ^ gm02PatternListExponent ps w := by
  have hsum := sum_time_bound ps w n (gm02PatternListExponent ps w)
    (fun J hJ => gm02PatternList_exponent_le ps w J hJ)
  have hone : 1 ≤ (n + 1) ^ gm02PatternListExponent ps w := Nat.one_le_pow _ _ (by omega)
  unfold gm02PatternListCoefficient
  rw [Nat.add_mul]
  omega

end GraphMinor.Compute
