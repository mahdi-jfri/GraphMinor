module
public import GraphMinor.Thomason.UniformTwoSizes
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp

/-!
# An integer test for the random block lemma

The hypothesis of `clique_isIsoMinor_of_two_sizes` is an inequality between
rational numbers when the parameters `A` are rational. We write the total
expected loss as one fraction of natural numbers, built by adding seven
fractions without reducing them, and compare it with the number of blocks.
The test `twoSizeOK` uses only addition, multiplication, powers and
comparisons of natural numbers, so Lean's kernel can evaluate it with its
fast arithmetic on natural numbers. This is how the certificates of the note
`docs/thomason/uniform_minor_bound.tex` are checked.
-/

public section
namespace GraphMinor.Thomason.Uniform
open Finset

/-- The sum of two fractions of natural numbers, not reduced. -/
@[expose] def qadd (x y : ℕ × ℕ) : ℕ × ℕ := (x.1 * y.2 + y.1 * x.2, x.2 * y.2)

/-- The value of a fraction of natural numbers. -/
@[expose] noncomputable def qval (x : ℕ × ℕ) : ℝ := (x.1 : ℝ) / x.2

theorem qadd_den_pos {x y : ℕ × ℕ} (hx : 0 < x.2) (hy : 0 < y.2) : 0 < (qadd x y).2 :=
  Nat.mul_pos hx hy

theorem qval_qadd {x y : ℕ × ℕ} (hx : 0 < x.2) (hy : 0 < y.2) :
    qval (qadd x y) = qval x + qval y := by
  have hx' : (x.2 : ℝ) ≠ 0 := by positivity
  have hy' : (y.2 : ℝ) ≠ 0 := by positivity
  simp only [qval, qadd]
  push_cast
  field_simp

/-- The expected loss for `Na` blocks of size `ka` with `A = aN / aD`,
followed by `Nb` blocks of size `kb` with `A = bN / bD`, as one fraction:
connectivity and domination losses of each kind, then the three kinds of
missing pairs. -/
@[expose] def lossTwo (n q ka kb Na Nb aN aD bN bD : ℕ) : ℕ × ℕ :=
  qadd (Na * (2 ^ (ka - 1) - 1) * q ^ (ka - 1), (n + 1 - ka) ^ (ka - 1)) <|
  qadd (Na * aD, aN) <|
  qadd (Nb * (2 ^ (kb - 1) - 1) * q ^ (kb - 1), (n + 1 - kb) ^ (kb - 1)) <|
  qadd (Nb * bD, bN) <|
  qadd (Na * (Na - 1) * (aN * q ^ ka) ^ ka, 2 * (aD * n ^ (ka - 1) * (n - ka)) ^ ka) <|
  qadd (Na * Nb * (aN * q ^ ka) ^ kb, (aD * n ^ (ka - 1) * (n - ka)) ^ kb)
    (Nb * (Nb - 1) * (bN * q ^ kb) ^ kb, 2 * (bD * n ^ (kb - 1) * (n - kb)) ^ kb)

/-- The integer test: the block sizes fit, the factors `A` are positive, and
the expected number of surviving blocks exceeds `m - 1`. -/
@[expose] def twoSizeOK (n q m ka kb Na Nb aN aD bN bD : ℕ) : Bool :=
  decide (1 ≤ ka) && decide (1 ≤ kb) && decide (ka < n) && decide (kb < n) &&
  decide (Na * ka + Nb * kb ≤ n) && decide (0 < aN) && decide (0 < aD) &&
  decide (0 < bN) && decide (0 < bD) && decide (m ≤ Na + Nb) &&
  decide ((lossTwo n q ka kb Na Nb aN aD bN bD).1 <
    (Na + Nb + 1 - m) * (lossTwo n q ka kb Na Nb aN aD bN bD).2)

private theorem cast_mul_pred (N : ℕ) : ((N * (N - 1) : ℕ) : ℝ) = N * ((N : ℝ) - 1) := by
  rcases Nat.eq_zero_or_pos N with h | h
  · subst h; simp
  · rw [Nat.cast_mul, Nat.cast_sub h]; simp

private theorem x_eq (n q k aN aD : ℕ) (hk : 1 ≤ k) (hkn : k < n) (haD : 0 < aD) :
    (aN : ℝ) / aD * (n * ((q : ℝ) / n) ^ k) / ((n : ℝ) - k) =
      ((aN * q ^ k : ℕ) : ℝ) / ((aD * n ^ (k - 1) * (n - k) : ℕ) : ℝ) := by
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  have hn : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hnk : (0 : ℝ) < (n : ℝ) - (j + 1 : ℕ) := by
    have : ((j + 1 : ℕ) : ℝ) < n := by exact_mod_cast hkn
    linarith
  have haD' : (0 : ℝ) < aD := by exact_mod_cast haD
  rw [show j + 1 - 1 = j by omega]
  push_cast [Nat.cast_sub hkn.le]
  push_cast at hnk
  have hnj : (n : ℝ) ^ j ≠ 0 := pow_ne_zero _ hn.ne'
  rw [div_pow, pow_succ, pow_succ]
  field_simp

private theorem one_sub_eq (n k : ℕ) (hk : k ≤ n) :
    ((n + 1 - k : ℕ) : ℝ) = (n : ℝ) - k + 1 := by
  rw [Nat.cast_sub (by omega)]; push_cast; ring

private theorem two_pow_sub (k : ℕ) : ((2 ^ (k - 1) - 1 : ℕ) : ℝ) = (2 : ℝ) ^ (k - 1) - 1 := by
  rw [Nat.cast_sub Nat.one_le_two_pow]; push_cast; ring

variable {W : Type*} [Fintype W] [DecidableEq W] (H : SimpleGraph W) [DecidableRel H.Adj]

/-- The integer test gives a `K_m` minor, by the random block lemma with
blocks of two sizes. -/
theorem clique_isIsoMinor_of_twoSizeOK (q : ℕ) (hq : ∀ v, (nonNbr H v).card ≤ q)
    {n m ka kb Na Nb aN aD bN bD : ℕ} (hn : Fintype.card W = n)
    (hok : twoSizeOK n q m ka kb Na Nb aN aD bN bD = true) :
    IsIsoMinor (Graph.ofSimpleGraph (⊤ : SimpleGraph (Fin m))) (Graph.ofSimpleGraph H) := by
  simp only [twoSizeOK, Bool.and_eq_true, decide_eq_true_eq] at hok
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hka, hkb⟩, hkan⟩, hkbn⟩, hsum⟩, haN⟩, haD⟩, hbN⟩, hbD⟩, hm⟩, hloss⟩ := hok
  refine clique_isIsoMinor_of_two_sizes H q hq ka kb Na Nb hka hkb (hn ▸ hsum)
    ((aN : ℝ) / aD) ((bN : ℝ) / bD) (by positivity) (by positivity) m ?_
  rw [hn]
  -- positivity of the denominators
  have hp1 : 0 < (n + 1 - ka) ^ (ka - 1) := pow_pos (by omega) _
  have hp3 : 0 < (n + 1 - kb) ^ (kb - 1) := pow_pos (by omega) _
  have hda : 0 < aD * n ^ (ka - 1) * (n - ka) :=
    Nat.mul_pos (Nat.mul_pos haD (pow_pos (by omega) _)) (by omega)
  have hdb : 0 < bD * n ^ (kb - 1) * (n - kb) :=
    Nat.mul_pos (Nat.mul_pos hbD (pow_pos (by omega) _)) (by omega)
  have hp5 : 0 < 2 * (aD * n ^ (ka - 1) * (n - ka)) ^ ka := Nat.mul_pos (by norm_num) (pow_pos hda _)
  have hp6 : 0 < (aD * n ^ (ka - 1) * (n - ka)) ^ kb := pow_pos hda _
  have hp7 : 0 < 2 * (bD * n ^ (kb - 1) * (n - kb)) ^ kb := Nat.mul_pos (by norm_num) (pow_pos hdb _)
  -- the value of the loss
  have hval : qval (lossTwo n q ka kb Na Nb aN aD bN bD) =
      Na * (((2 : ℝ) ^ (ka - 1) - 1) * ((q : ℝ) / ((n : ℝ) - ka + 1)) ^ (ka - 1)) +
      Na * (1 / ((aN : ℝ) / aD)) +
      Nb * (((2 : ℝ) ^ (kb - 1) - 1) * ((q : ℝ) / ((n : ℝ) - kb + 1)) ^ (kb - 1)) +
      Nb * (1 / ((bN : ℝ) / bD)) +
      Na * (Na - 1) / 2 * ((aN : ℝ) / aD * (n * ((q : ℝ) / n) ^ ka) / ((n : ℝ) - ka)) ^ ka +
      Na * Nb * ((aN : ℝ) / aD * (n * ((q : ℝ) / n) ^ ka) / ((n : ℝ) - ka)) ^ kb +
      Nb * (Nb - 1) / 2 * ((bN : ℝ) / bD * (n * ((q : ℝ) / n) ^ kb) / ((n : ℝ) - kb)) ^ kb := by
    unfold lossTwo
    rw [qval_qadd hp1 (by simp only [qadd]; positivity), qval_qadd haN (by simp only [qadd]; positivity),
      qval_qadd hp3 (by simp only [qadd]; positivity), qval_qadd hbN (by simp only [qadd]; positivity),
      qval_qadd hp5 (by simp only [qadd]; positivity), qval_qadd hp6 hp7]
    rw [x_eq n q ka aN aD hka hkan haD, x_eq n q kb bN bD hkb hkbn hbD]
    simp only [qval]
    rw [← one_sub_eq n ka hkan.le, ← one_sub_eq n kb hkbn.le, ← two_pow_sub, ← two_pow_sub,
      ← cast_mul_pred Na, ← cast_mul_pred Nb]
    have haN' : (aN : ℝ) ≠ 0 := by positivity
    have hbN' : (bN : ℝ) ≠ 0 := by positivity
    have haD' : (aD : ℝ) ≠ 0 := by positivity
    have hbD' : (bD : ℝ) ≠ 0 := by positivity
    push_cast
    rw [div_pow, div_pow, div_pow, div_pow]
    field_simp
    ring
  have hlt : qval (lossTwo n q ka kb Na Nb aN aD bN bD) < ((Na + Nb + 1 - m : ℕ) : ℝ) := by
    have hden : (0 : ℝ) < (lossTwo n q ka kb Na Nb aN aD bN bD).2 := by
      unfold lossTwo; simp only [qadd]; positivity
    rw [qval, div_lt_iff₀ hden]
    exact_mod_cast hloss
  rw [hval, Nat.cast_sub (by omega)] at hlt
  push_cast at hlt
  linarith

end GraphMinor.Thomason.Uniform
