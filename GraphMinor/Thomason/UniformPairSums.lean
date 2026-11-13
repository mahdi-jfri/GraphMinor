module
public import GraphMinor.Thomason.UniformBlockSums
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Expected missing adjacencies between two random blocks

Condition on a good block `i`, that is, one that leaves at most `a`
vertices undominated. The rest of the choice is a uniform injective map
into the `n - s i` unused vertices. Block `j` has no neighbour in block
`i` only if all its `s j` vertices lie among the undominated ones, which
happens with probability at most `(a / (n - s i)) ^ s j`. This is the
missing-pair estimate in the proof of Lemma 1 of the note
`docs/thomason/uniform_minor_bound.tex`.
-/

public section
namespace GraphMinor.Thomason.Uniform
open Finset

/-- Injective maps whose restriction to `t` positions lands in a set of at
most `b` vertices make up at most a `(b / m) ^ t` proportion, where `m` is
the number of vertices. -/
theorem sum_restrict_into_le {Y W' : Type*} [Fintype Y] [DecidableEq Y] [Fintype W']
    [DecidableEq W'] (Q' : Y → Prop) [DecidablePred Q'] (U' : Finset W') (b : ℝ)
    (hb : (U'.card : ℝ) ≤ b) {t : ℕ} (ht : Fintype.card {y // Q' y} = t) :
    ∑ h : Y ↪ W', (if ∀ z : {y // Q' y}, h z ∈ U' then (1 : ℝ) else 0) ≤
      (Fintype.card (Y ↪ W') : ℝ) * (b / Fintype.card W') ^ t := by
  subst ht
  have hsplit := sum_comp_splitEmb_fst (W := W') Q'
    (fun f' => if ∀ z, f' z ∈ U' then (1 : ℝ) else 0)
  rw [show (∑ h : Y ↪ W', (if ∀ z : {y // Q' y}, h z ∈ U' then (1 : ℝ) else 0)) =
    ∑ h : Y ↪ W', (if ∀ z, (splitEmb Q' h).1 z ∈ U' then (1 : ℝ) else 0) from rfl, hsplit,
    card_embedding_eq_mul Q']
  have hcount : (∑ f' : {y // Q' y} ↪ W', (if ∀ z, f' z ∈ U' then (1 : ℝ) else 0)) =
      (U'.card.descFactorial (Fintype.card {y // Q' y}) : ℝ) := by
    rw [← card_embedding_into (α := {y // Q' y}) U', card_filter]
    push_cast
    rfl
  rw [hcount]
  set t := Fintype.card {y // Q' y}
  have hext : (0 : ℝ) ≤ ((Fintype.card W' - Fintype.card {y // Q' y}).descFactorial
      (Fintype.card {y // ¬Q' y}) : ℝ) := Nat.cast_nonneg _
  have hU : U'.card ≤ Fintype.card W' := card_le_univ _
  have hb0 : 0 ≤ b := (Nat.cast_nonneg _).trans hb
  have hmain : (U'.card.descFactorial t : ℝ) ≤
      ((Fintype.card W').descFactorial t : ℝ) * (b / Fintype.card W') ^ t := by
    rcases le_or_gt t (Fintype.card W') with htn | htn
    · have hd := descFactorial_div_le_pow hU htn
      have hpos : (0 : ℝ) < (Fintype.card W').descFactorial t := by
        exact_mod_cast Nat.descFactorial_pos.mpr htn
      rw [div_le_iff₀ hpos] at hd
      refine hd.trans ?_
      rw [mul_comm]
      refine mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) ?_ t) hpos.le
      exact div_le_div_of_nonneg_right hb (Nat.cast_nonneg _)
    · rw [Nat.descFactorial_eq_zero_iff_lt.mpr (hU.trans_lt htn), Nat.cast_zero]
      exact mul_nonneg (Nat.cast_nonneg _) (pow_nonneg (div_nonneg hb0 (Nat.cast_nonneg _)) _)
  calc _ ≤
      ((Fintype.card W').descFactorial t : ℝ) * (b / Fintype.card W') ^ t *
        ((Fintype.card W' - Fintype.card {y // Q' y}).descFactorial
          (Fintype.card {y // ¬Q' y}) : ℝ) := mul_le_mul_of_nonneg_right hmain hext
    _ = _ := by ring

variable {W : Type*} [Fintype W] [DecidableEq W] (H : SimpleGraph W) [DecidableRel H.Adj]
variable {N : ℕ} {s : Fin N → ℕ}

/-- The expected number of choices in which block `i` is good and block `j`
lies among the vertices that block `i` does not dominate. -/
theorem sum_pair_le {i j : Fin N} (hij : i ≠ j) (a : ℝ) (ha : 0 ≤ a)
    (hsi : s i ≤ Fintype.card W) :
    ∑ g : Pos s ↪ W, (if ((undom H (block g i)).card : ℝ) ≤ a ∧
        block g j ⊆ undom H (block g i) then (1 : ℝ) else 0) ≤
      (Fintype.card (Pos s ↪ W) : ℝ) * (a / ((Fintype.card W : ℝ) - s i)) ^ s j := by
  classical
  let Q : Pos s → Prop := fun x => x.1 = i
  let e := splitEmb (W := W) Q
  let G : (Σ f : {x // Q x} ↪ W, ({x // ¬Q x} ↪ ↥(Set.range f)ᶜ)) → ℝ := fun σ =>
    if ((undom H (univ.image σ.1)).card : ℝ) ≤ a ∧
      ∀ y : {y : {x // ¬Q x} // y.1.1 = j}, (σ.2 y.1 : W) ∈ undom H (univ.image σ.1)
    then 1 else 0
  have hFG (g : Pos s ↪ W) : (if ((undom H (block g i)).card : ℝ) ≤ a ∧
      block g j ⊆ undom H (block g i) then (1 : ℝ) else 0) = G (e g) := by
    have hblk_j : block g j ⊆ undom H (block g i) ↔
        ∀ y : {y : {x // ¬Q x} // y.1.1 = j}, ((e g).2 y.1 : W) ∈ undom H (block g i) := by
      constructor
      · intro h y
        exact h (mem_block.mpr ⟨⟨y.1.1, y.2⟩, rfl⟩)
      · intro h v hv
        obtain ⟨x, rfl⟩ := (mem_block (g := g) (i := j)).mp hv
        exact h ⟨⟨x.1, fun h' => hij (h'.symm.trans x.2)⟩, x.2⟩
    have hblk_i : block g i = univ.image (e g).1 := block_eq_image_splitEmb g i
    rw [hblk_i] at hblk_j ⊢
    exact if_congr (and_congr Iff.rfl hblk_j) rfl rfl
  rw [Finset.sum_congr rfl fun g _ => hFG g, Equiv.sum_comp e G, Fintype.sum_sigma]
  have hT : (Fintype.card (Pos s ↪ W) : ℝ) =
      ∑ f : {x // Q x} ↪ W, (Fintype.card ({x // ¬Q x} ↪ ↥(Set.range f)ᶜ) : ℝ) := by
    rw [Fintype.card_congr e, Fintype.card_sigma]
    push_cast
    rfl
  rw [hT, Finset.sum_mul]
  refine Finset.sum_le_sum fun f _ => ?_
  have hcardW : (Fintype.card ↥(Set.range f)ᶜ : ℝ) = (Fintype.card W : ℝ) - s i := by
    rw [card_compl_range, card_blockPos, Nat.cast_sub hsi]
  by_cases hgood : ((undom H (univ.image f)).card : ℝ) ≤ a
  · let U' : Finset ↥(Set.range f)ᶜ := univ.filter (fun w => (w : W) ∈ undom H (univ.image f))
    have hU' : (U'.card : ℝ) ≤ a := by
      refine le_trans ?_ hgood
      have : U'.card ≤ (undom H (univ.image f)).card := by
        refine card_le_card_of_injOn (fun w => (w : W)) ?_ ?_
        · intro w hw
          simpa [U'] using hw
        · intro w _ w' _ h
          exact Subtype.ext h
      exact_mod_cast this
    have hinner : ∑ h, G ⟨f, h⟩ =
        ∑ h : {x // ¬Q x} ↪ ↥(Set.range f)ᶜ,
          (if ∀ z : {y : {x // ¬Q x} // y.1.1 = j}, h z ∈ U' then (1 : ℝ) else 0) := by
      refine Finset.sum_congr rfl fun h _ => ?_
      simp only [G, hgood, true_and, U', mem_filter, mem_univ]
    rw [hinner, ← hcardW]
    exact sum_restrict_into_le (fun y : {x // ¬Q x} => y.1.1 = j) U' a hU'
      (card_blockPos_rest hij)
  · have hzero : ∑ h, G ⟨f, h⟩ = 0 := by
      refine Finset.sum_eq_zero fun h _ => ?_
      simp only [G, hgood, false_and, ite_false]
    rw [hzero]
    refine mul_nonneg (Nat.cast_nonneg _) (pow_nonneg (div_nonneg ha ?_) _)
    have : (s i : ℝ) ≤ Fintype.card W := by exact_mod_cast hsi
    linarith

end GraphMinor.Thomason.Uniform
