module
public import GraphMinor.Thomason.UniformBlockCounts
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp

/-!
# Expected losses over a random choice of disjoint blocks

A choice of `N` disjoint blocks, block `i` with `s i` vertices, is an
injective map from the positions `Σ i, Fin (s i)` into the vertices. Over
all such maps we bound three sums, which are the expected losses in the
proof of Lemma 1 of the note `docs/thomason/uniform_minor_bound.tex`:

* the number of maps for which block `i` is not good, that is, it leaves
  more than `A n (q / n) ^ s` vertices undominated (Markov's inequality);
* the number of maps for which block `i` is disconnected;
* the number of maps for which block `i` is good and block `j` lies among
  the vertices that block `i` does not dominate.

For the last one we split a map into block `i` and the rest. The rest is
an injective map into the unused vertices, and we split it again at block
`j`.
-/

public section
namespace GraphMinor.Thomason.Uniform
open Finset

variable {W : Type*} [Fintype W] [DecidableEq W] (H : SimpleGraph W) [DecidableRel H.Adj]
variable {N : ℕ} (s : Fin N → ℕ)

/-- The positions of the blocks: block `i` has `s i` positions. -/
abbrev Pos := Σ i : Fin N, Fin (s i)

variable {s}

/-- The vertices that a choice of blocks puts in block `i`. -/
@[expose] def block (g : Pos s ↪ W) (i : Fin N) : Finset W :=
  univ.image (fun x : {x : Pos s // x.1 = i} => g x)

theorem block_eq_image_splitEmb (g : Pos s ↪ W) (i : Fin N) :
    block g i = univ.image (splitEmb (fun x : Pos s => x.1 = i) g).1 := rfl

theorem card_pos_eq : Fintype.card (Pos s) = ∑ i, s i := by
  simp [Fintype.card_sigma]

theorem card_blockPos (i : Fin N) : Fintype.card {x : Pos s // x.1 = i} = s i := by
  rw [Fintype.card_subtype]
  have : (univ.filter fun x : Pos s => x.1 = i) =
      ({i} : Finset (Fin N)).sigma (fun _ => univ) := by
    ext ⟨a, b⟩; simp
  rw [this, card_sigma, sum_singleton, card_univ, Fintype.card_fin]

theorem card_blockPos_rest {i j : Fin N} (hij : i ≠ j) :
    Fintype.card {y : {x : Pos s // ¬x.1 = i} // y.1.1 = j} = s j := by
  rw [← card_blockPos (s := s) j]
  exact Fintype.card_congr
    { toFun := fun y => ⟨y.1.1, y.2⟩
      invFun := fun x => ⟨⟨x.1, fun h => hij (h.symm.trans x.2)⟩, x.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }

theorem mem_block {g : Pos s ↪ W} {i : Fin N} {v : W} :
    v ∈ block g i ↔ ∃ x : {x : Pos s // x.1 = i}, g x = v := by
  simp [block]

/-- Different blocks of an injective map are disjoint. -/
theorem disjoint_block (g : Pos s ↪ W) {i j : Fin N} (hij : i ≠ j) :
    Disjoint (block g i) (block g j) := by
  rw [Finset.disjoint_left]
  intro v hv hv'
  obtain ⟨x, rfl⟩ := (mem_block (g := g) (i := i)).mp hv
  obtain ⟨y, hy⟩ := (mem_block (g := g) (i := j)).mp hv'
  have hxy := g.injective hy
  exact hij (x.2.symm.trans ((congrArg Sigma.fst hxy).symm.trans y.2))

/-- The number of block choices, through block `i`. -/
theorem card_emb_eq_mul (i : Fin N) :
    (Fintype.card (Pos s ↪ W) : ℝ) =
      (Fintype.card ({x : Pos s // x.1 = i} ↪ W) : ℝ) *
      ((Fintype.card W - Fintype.card {x : Pos s // x.1 = i}).descFactorial
        (Fintype.card {x : Pos s // ¬x.1 = i}) : ℝ) := by
  rw [card_embedding_eq_mul (fun x : Pos s => x.1 = i), Fintype.card_embedding_eq]

/-- A sum over block choices of a quantity depending only on block `i`. -/
theorem sum_block_eq (i : Fin N) (Φ : Finset W → ℝ) :
    ∑ g : Pos s ↪ W, Φ (block g i) =
      (∑ f : {x : Pos s // x.1 = i} ↪ W, Φ (univ.image f)) *
      ((Fintype.card W - Fintype.card {x : Pos s // x.1 = i}).descFactorial
        (Fintype.card {x : Pos s // ¬x.1 = i}) : ℝ) :=
  sum_comp_splitEmb_fst (fun x : Pos s => x.1 = i) (fun f => Φ (univ.image f))

/-- Markov's inequality for the undominated vertices of block `i`: at most
a `1 / A` proportion of the choices leave more than `A n (q / n) ^ s`
vertices undominated. -/
theorem sum_not_good_le (q : ℕ) (hq : ∀ v, (nonNbr H v).card ≤ q) (i : Fin N)
    (A : ℝ) (hA : 0 < A) :
    ∑ g : Pos s ↪ W, (if A * (Fintype.card W * ((q : ℝ) / Fintype.card W) ^ s i) <
        (undom H (block g i)).card then (1 : ℝ) else 0) ≤
      (Fintype.card (Pos s ↪ W) : ℝ) / A := by
  obtain ⟨e, he_def⟩ : ∃ e : ℝ, e = Fintype.card W * ((q : ℝ) / Fintype.card W) ^ s i :=
    ⟨_, rfl⟩
  obtain ⟨T, hT_def⟩ : ∃ T : ℝ, T = (Fintype.card (Pos s ↪ W) : ℝ) := ⟨_, rfl⟩
  rw [← he_def, ← hT_def]
  have he : 0 ≤ e := by rw [he_def]; positivity
  have hT : 0 ≤ T := by rw [hT_def]; positivity
  have hU : ∑ g : Pos s ↪ W, ((undom H (block g i)).card : ℝ) ≤ T * e := by
    have hsplit := sum_block_eq (W := W) (s := s) i (fun S => ((undom H S).card : ℝ))
    rw [hsplit]
    have h := sum_card_undom_le H q hq (α := {x : Pos s // x.1 = i})
    rw [card_blockPos, ← he_def] at h
    rw [hT_def, card_emb_eq_mul (W := W) (s := s) i]
    have hext : (0 : ℝ) ≤ ((Fintype.card W - Fintype.card {x : Pos s // x.1 = i}).descFactorial
        (Fintype.card {x : Pos s // ¬x.1 = i}) : ℝ) := Nat.cast_nonneg _
    calc _ ≤ _ := mul_le_mul_of_nonneg_right h hext
      _ = _ := by ring
  have hterm (g : Pos s ↪ W) :
      (if A * e < (undom H (block g i)).card then (1 : ℝ) else 0) * (A * e) ≤
        (undom H (block g i)).card := by
    split_ifs with h
    · linarith
    · rw [zero_mul]; exact Nat.cast_nonneg _
  rcases eq_or_lt_of_le he with he0 | hepos
  · have hzero : ∀ g ∈ (univ : Finset (Pos s ↪ W)), ((undom H (block g i)).card : ℝ) = 0 := by
      refine (Finset.sum_eq_zero_iff_of_nonneg fun g _ => Nat.cast_nonneg _).mp ?_
      refine le_antisymm ?_ (Finset.sum_nonneg fun g _ => Nat.cast_nonneg _)
      rw [← he0, mul_zero] at hU
      exact hU
    calc ∑ g : Pos s ↪ W, (if A * e < (undom H (block g i)).card then (1 : ℝ) else 0)
        = ∑ _g : Pos s ↪ W, (0 : ℝ) := by
          refine Finset.sum_congr rfl fun g hg => ?_
          rw [hzero g hg, ← he0, mul_zero]; simp
      _ ≤ T / A := by rw [Finset.sum_const_zero]; exact div_nonneg hT hA.le
  · have hAe : 0 < A * e := mul_pos hA hepos
    rw [le_div_iff₀ hA]
    have hsum : (∑ g : Pos s ↪ W, (if A * e < (undom H (block g i)).card then (1 : ℝ) else 0)) *
        (A * e) ≤ T * e := by
      rw [Finset.sum_mul]
      exact (Finset.sum_le_sum fun g _ => hterm g).trans hU
    have h2 : (∑ g : Pos s ↪ W, (if A * e < (undom H (block g i)).card then (1 : ℝ) else 0)) *
        A * e ≤ T * e := by rw [mul_assoc]; exact hsum
    exact le_of_mul_le_mul_right h2 hepos

open Classical in
/-- The disconnected blocks: at most an `F` proportion of choices make
block `i` disconnected, where
`F = (2 ^ (s - 1) - 1) (q / (n - s + 1)) ^ (s - 1)`. -/
theorem sum_not_connected_le (q : ℕ) (hq : ∀ v, (nonNbr H v).card ≤ q) (i : Fin N)
    (hs : 1 ≤ s i) (hsn : s i ≤ Fintype.card W) :
    ∑ g : Pos s ↪ W, (if ¬ (H.induce ((block g i : Finset W) : Set W)).Connected
        then (1 : ℝ) else 0) ≤
      (Fintype.card (Pos s ↪ W) : ℝ) * (((2 : ℝ) ^ (s i - 1) - 1) *
        ((q : ℝ) / ((Fintype.card W : ℝ) - s i + 1)) ^ (s i - 1)) := by
  have hsplit := sum_block_eq (W := W) (s := s) i
    (fun S => if ¬ (H.induce (S : Set W)).Connected then (1 : ℝ) else 0)
  rw [hsplit, card_emb_eq_mul (W := W) (s := s) i, Fintype.card_embedding_eq, card_blockPos]
  have x₀ : {x : Pos s // x.1 = i} := ⟨⟨i, ⟨0, hs⟩⟩, rfl⟩
  have hcount := card_not_connected_le H q hq x₀
  rw [card_blockPos] at hcount
  have hsumeq : (∑ f : {x : Pos s // x.1 = i} ↪ W,
      (if ¬ (H.induce ((univ.image f : Finset W) : Set W)).Connected then (1 : ℝ) else 0)) =
      ((univ.filter (fun f : {x : Pos s // x.1 = i} ↪ W =>
        ¬ (H.induce ((univ.image f : Finset W) : Set W)).Connected)).card : ℝ) := by
    rw [card_filter]; push_cast; rfl
  rw [hsumeq]
  have hext : (0 : ℝ) ≤ ((Fintype.card W - s i).descFactorial
    (Fintype.card {x : Pos s // ¬x.1 = i}) : ℝ) := Nat.cast_nonneg _
  generalize ((Fintype.card W - s i).descFactorial (Fintype.card {x : Pos s // ¬x.1 = i}) : ℝ) = ext
    at *
  generalize (univ.filter (fun f : {x : Pos s // x.1 = i} ↪ W =>
        ¬ (H.induce ((univ.image f : Finset W) : Set W)).Connected)).card = bad at *
  have hdesc0 := mul_pow_le_descFactorial (Fintype.card W) (s i - 1)
  generalize Fintype.card W = n at *
  rw [Nat.sub_add_cancel hs] at hdesc0
  have hcountR : (bad : ℝ) ≤ ((2 : ℝ) ^ (s i - 1) - 1) * (n * (q : ℝ) ^ (s i - 1)) := by
    have h2 : ((2 ^ (s i - 1) - 1 : ℕ) : ℝ) = (2 : ℝ) ^ (s i - 1) - 1 := by
      rw [Nat.cast_sub Nat.one_le_two_pow]; push_cast; ring
    rw [← h2]
    exact_mod_cast hcount
  have hd : (0 : ℝ) < (n : ℝ) - s i + 1 := by
    have : (s i : ℝ) ≤ n := by exact_mod_cast hsn
    linarith
  have hdesc : (n : ℝ) * ((n : ℝ) - s i + 1) ^ (s i - 1) ≤ (n.descFactorial (s i) : ℝ) := by
    have hcast : ((n - (s i - 1) : ℕ) : ℝ) = (n : ℝ) - s i + 1 := by
      rw [Nat.cast_sub (by omega), Nat.cast_sub hs]; push_cast; ring
    rw [← hcast]
    exact_mod_cast hdesc0
  have h2pos : (0 : ℝ) ≤ (2 : ℝ) ^ (s i - 1) - 1 := by
    have : (1 : ℝ) ≤ (2 : ℝ) ^ (s i - 1) := one_le_pow₀ (by norm_num)
    linarith
  rw [div_pow]
  have hdpow : (0 : ℝ) < ((n : ℝ) - s i + 1) ^ (s i - 1) := pow_pos hd _
  calc (bad : ℝ) * ext
      ≤ ((2 : ℝ) ^ (s i - 1) - 1) * (n * (q : ℝ) ^ (s i - 1)) * ext :=
        mul_le_mul_of_nonneg_right hcountR hext
    _ = (n * ((n : ℝ) - s i + 1) ^ (s i - 1)) * ext *
          (((2 : ℝ) ^ (s i - 1) - 1) * ((q : ℝ) ^ (s i - 1) / ((n : ℝ) - s i + 1) ^ (s i - 1))) := by
        field_simp
    _ ≤ (n.descFactorial (s i) : ℝ) * ext *
          (((2 : ℝ) ^ (s i - 1) - 1) * ((q : ℝ) ^ (s i - 1) / ((n : ℝ) - s i + 1) ^ (s i - 1))) := by
        refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hdesc hext) ?_
        exact mul_nonneg h2pos (div_nonneg (pow_nonneg (Nat.cast_nonneg _) _) hdpow.le)

end GraphMinor.Thomason.Uniform
