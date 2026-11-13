module
public import GraphMinor.Thomason.UniformPartition
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp

/-!
# The random block lemma with blocks of two sizes

We specialize `clique_isIsoMinor_of_blocks` to `Na` blocks of size `ka`
followed by `Nb` blocks of size `kb`. With `Nb = 0` this is Lemma 1 of the
note `docs/thomason/uniform_minor_bound.tex`, formula (5), and with `ka = 2`,
`kb = 3` it is the mixed variant, Lemma 2 and formula (7) of the note. Write
`F k = (2 ^ (k - 1) - 1) (q / (n - k + 1)) ^ (k - 1)` and
`x k A = A n (q / n) ^ k / (n - k)`. The losses of pairs of blocks are
`(x ka Aa) ^ ka` for two blocks of the first kind, `(x ka Aa) ^ kb` for a
block of the first kind and a later block of the second kind, and
`(x kb Ab) ^ kb` for two blocks of the second kind.
-/

public section
namespace GraphMinor.Thomason.Uniform
open Finset

/-- The number of pairs `i < j` in `Fin a`, weighted by a constant. -/
theorem sum_sum_ite_lt (a : ℕ) (c : ℝ) :
    ∑ i : Fin a, ∑ j : Fin a, (if i < j then c else 0) = a * (a - 1) / 2 * c := by
  have hsymm : ∑ i : Fin a, ∑ j : Fin a, (if i < j then (1 : ℝ) else 0) =
      ∑ i : Fin a, ∑ j : Fin a, (if j < i then (1 : ℝ) else 0) := Finset.sum_comm
  have hdiag : ∑ i : Fin a, ∑ j : Fin a, (if i = j then (1 : ℝ) else 0) = a := by
    simp
  have htot : ∑ i : Fin a, ∑ j : Fin a, ((if i < j then (1 : ℝ) else 0) +
      (if j < i then (1 : ℝ) else 0) + (if i = j then (1 : ℝ) else 0)) = a * a := by
    have h (i j : Fin a) : (if i < j then (1 : ℝ) else 0) + (if j < i then (1 : ℝ) else 0) +
        (if i = j then (1 : ℝ) else 0) = 1 := by
      rcases lt_trichotomy i j with h | h | h
      · simp [h, h.ne, not_lt.mpr h.le]
      · simp [h]
      · simp [h, h.ne', not_lt.mpr h.le]
    simp [h]
  simp only [Finset.sum_add_distrib] at htot
  have hcount : ∑ i : Fin a, ∑ j : Fin a, (if i < j then (1 : ℝ) else 0) = a * (a - 1) / 2 := by
    linarith
  rw [← hcount, Finset.sum_mul]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun j _ => ?_
  split_ifs <;> simp

variable {W : Type*} [Fintype W] [DecidableEq W] (H : SimpleGraph W) [DecidableRel H.Adj]

/-- Lemmas 1 and 2 of the note `docs/thomason/uniform_minor_bound.tex` (the second is the mixed
variant): `Na` blocks of size `ka` and `Nb` blocks of size `kb`. -/
theorem clique_isIsoMinor_of_two_sizes (q : ℕ) (hq : ∀ v, (nonNbr H v).card ≤ q)
    (ka kb Na Nb : ℕ) (hka : 1 ≤ ka) (hkb : 1 ≤ kb)
    (hsum : Na * ka + Nb * kb ≤ Fintype.card W)
    (Aa Ab : ℝ) (hAa : 0 < Aa) (hAb : 0 < Ab) (m : ℕ)
    (hB : (m : ℝ) - 1 <
      Na * (1 - ((2 : ℝ) ^ (ka - 1) - 1) *
          ((q : ℝ) / ((Fintype.card W : ℝ) - ka + 1)) ^ (ka - 1) - 1 / Aa) +
      Nb * (1 - ((2 : ℝ) ^ (kb - 1) - 1) *
          ((q : ℝ) / ((Fintype.card W : ℝ) - kb + 1)) ^ (kb - 1) - 1 / Ab) -
      Na * (Na - 1) / 2 * (Aa * (Fintype.card W * ((q : ℝ) / Fintype.card W) ^ ka) /
          ((Fintype.card W : ℝ) - ka)) ^ ka -
      Na * Nb * (Aa * (Fintype.card W * ((q : ℝ) / Fintype.card W) ^ ka) /
          ((Fintype.card W : ℝ) - ka)) ^ kb -
      Nb * (Nb - 1) / 2 * (Ab * (Fintype.card W * ((q : ℝ) / Fintype.card W) ^ kb) /
          ((Fintype.card W : ℝ) - kb)) ^ kb) :
    IsIsoMinor (Graph.ofSimpleGraph (⊤ : SimpleGraph (Fin m))) (Graph.ofSimpleGraph H) := by
  generalize hn : Fintype.card W = n at hsum hB
  obtain ⟨s, hs_def⟩ : ∃ s : Fin (Na + Nb) → ℕ, s = fun i => if i.val < Na then ka else kb :=
    ⟨_, rfl⟩
  obtain ⟨A, hA_def⟩ : ∃ A : Fin (Na + Nb) → ℝ, A = fun i => if i.val < Na then Aa else Ab :=
    ⟨_, rfl⟩
  obtain ⟨F, hF_def⟩ : ∃ F : ℕ → ℝ,
      F = fun k : ℕ => ((2 : ℝ) ^ (k - 1) - 1) * ((q : ℝ) / ((n : ℝ) - k + 1)) ^ (k - 1) := ⟨_, rfl⟩
  obtain ⟨x, hx_def⟩ : ∃ x : ℕ → ℝ → ℝ,
      x = fun (k : ℕ) (B : ℝ) => B * (n * ((q : ℝ) / n) ^ k) / ((n : ℝ) - k) := ⟨_, rfl⟩
  have hsA (i : Fin Na) : s (Fin.castAdd Nb i) = ka := by simp [hs_def]
  have hsB (i : Fin Nb) : s (Fin.natAdd Na i) = kb := by simp [hs_def]
  have hAA (i : Fin Na) : A (Fin.castAdd Nb i) = Aa := by simp [hA_def]
  have hAB (i : Fin Nb) : A (Fin.natAdd Na i) = Ab := by simp [hA_def]
  have hs1 (i : Fin (Na + Nb)) : 1 ≤ s i := by rw [hs_def]; dsimp only; split_ifs <;> assumption
  have hA0 (i : Fin (Na + Nb)) : 0 < A i := by rw [hA_def]; dsimp only; split_ifs <;> assumption
  have hssum : ∑ i, s i ≤ Fintype.card W := by
    rw [Fin.sum_univ_add]
    simp only [hsA, hsB, Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]
    rw [hn]; exact hsum
  refine clique_isIsoMinor_of_blocks H q hq s hs1 hssum A hA0 m ?_
  rw [hn]
  have h1 : ∑ i, (F (s i) + 1 / A i) = Na * (F ka + 1 / Aa) + Nb * (F kb + 1 / Ab) := by
    rw [Fin.sum_univ_add]
    simp only [hsA, hsB, hAA, hAB, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul]
  have hAAlt (i j : Fin Na) : (Fin.castAdd Nb i < Fin.castAdd Nb j) ↔ i < j := Iff.rfl
  have hABlt (i : Fin Na) (j : Fin Nb) : Fin.castAdd Nb i < Fin.natAdd Na j := by
    show i.val < Na + j.val; omega
  have hBAlt (i : Fin Nb) (j : Fin Na) : ¬ Fin.natAdd Na i < Fin.castAdd Nb j := by
    show ¬ (Na + i.val < j.val); omega
  have hBBlt (i j : Fin Nb) : (Fin.natAdd Na i < Fin.natAdd Na j) ↔ i < j := by
    show Na + i.val < Na + j.val ↔ i.val < j.val; omega
  have h2 : ∑ i, ∑ j ∈ univ.filter (fun j => i < j), (x (s i) (A i)) ^ s j =
      Na * (Na - 1) / 2 * (x ka Aa) ^ ka + Na * Nb * (x ka Aa) ^ kb +
        Nb * (Nb - 1) / 2 * (x kb Ab) ^ kb := by
    simp only [Finset.sum_filter]
    rw [Fin.sum_univ_add]
    simp only [Fin.sum_univ_add, hsA, hsB, hAA, hAB, hAAlt, hABlt, hBAlt, hBBlt, ite_true,
      ite_false, Finset.sum_const_zero, zero_add, sum_sum_ite_lt, Finset.sum_add_distrib,
      Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    ring
  have hF : ∀ i, F (s i) = ((2 : ℝ) ^ (s i - 1) - 1) *
      ((q : ℝ) / ((n : ℝ) - s i + 1)) ^ (s i - 1) := fun i => by rw [hF_def]
  have hx : ∀ i j, (x (s i) (A i)) ^ s j = (A i * (n * ((q : ℝ) / n) ^ s i) /
      ((n : ℝ) - s i)) ^ s j := fun i j => by rw [hx_def]
  simp only [← hF, ← hx]
  rw [h1, h2]
  rw [hF_def, hx_def]
  dsimp only
  push_cast
  linarith

end GraphMinor.Thomason.Uniform
