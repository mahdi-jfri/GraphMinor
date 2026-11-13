module
public import Mathlib.Data.Fintype.CardEmbedding
public import Mathlib.Logic.Equiv.Embedding
public import Mathlib.Data.Real.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Zify
import Mathlib.Tactic.Ring

/-!
# Counting embeddings of positions into vertices

A random ordered choice of disjoint blocks of vertices is an injective
map from a finite set of positions into the vertex set. We count such
maps by splitting them into their restriction to some positions and an
injective map of the remaining positions into the unused vertices. Every
restriction has the same number of extensions. So an average over all
injective maps of a quantity that depends only on one block equals the
average over the injective maps of that block alone. This replaces the
conditional probabilities in the proof of Lemma 1 of the note
`docs/thomason/uniform_minor_bound.tex`.

We also prove the elementary estimates on falling factorials used there:
the chance that `s` distinct samples lie in a fixed set of size `a` is at
most `(a / b) ^ s` when the samples come from `b` elements.
-/

public section
namespace GraphMinor.Thomason.Uniform
open Finset

section Split
variable {P W : Type*} [Fintype P] [DecidableEq P] [Fintype W] [DecidableEq W]

/-- An injective map on positions is its restriction to the positions
satisfying `Q`, together with an injective map of the other positions into
the vertices not used by that restriction. -/
@[expose] def splitEmb (Q : P → Prop) [DecidablePred Q] :
    (P ↪ W) ≃ Σ f : {x // Q x} ↪ W, ({x // ¬Q x} ↪ ↥(Set.range f)ᶜ) :=
  (Equiv.embeddingCongr (Equiv.sumCompl Q) (Equiv.refl W)).symm.trans
    Equiv.sumEmbeddingEquivSigmaEmbeddingRestricted

theorem splitEmb_fst_apply (Q : P → Prop) [DecidablePred Q] (g : P ↪ W)
    (x : {x // Q x}) : (splitEmb Q g).1 x = g x := rfl

theorem splitEmb_snd_apply (Q : P → Prop) [DecidablePred Q] (g : P ↪ W)
    (x : {x // ¬Q x}) : ((splitEmb Q g).2 x : W) = g x := rfl

/-- The unused vertices of an injective map. -/
theorem card_compl_range {α : Type*} [Fintype α] (f : α ↪ W) :
    Fintype.card ↥(Set.range f)ᶜ = Fintype.card W - Fintype.card α := by
  rw [Fintype.card_compl_set, Set.card_range_of_injective f.injective]

/-- A sum over injective maps of a quantity depending on a restriction.
Every restriction has the same number of extensions. -/
theorem sum_comp_splitEmb_fst (Q : P → Prop) [DecidablePred Q]
    (F : ({x // Q x} ↪ W) → ℝ) :
    ∑ g : P ↪ W, F (splitEmb Q g).1 =
      (∑ f, F f) * ((Fintype.card W - Fintype.card {x // Q x}).descFactorial
        (Fintype.card {x // ¬Q x}) : ℝ) := by
  rw [Equiv.sum_comp (splitEmb Q) (fun σ => F σ.1), Fintype.sum_sigma, Finset.sum_mul]
  refine Finset.sum_congr rfl fun f _ => ?_
  simp only [Finset.sum_const, Finset.card_univ]
  rw [Fintype.card_embedding_eq, card_compl_range, nsmul_eq_mul, mul_comm]

/-- The number of injective maps, through a restriction. -/
theorem card_embedding_eq_mul (Q : P → Prop) [DecidablePred Q] :
    (Fintype.card (P ↪ W) : ℝ) =
      ((Fintype.card W).descFactorial (Fintype.card {x // Q x}) : ℝ) *
      ((Fintype.card W - Fintype.card {x // Q x}).descFactorial
        (Fintype.card {x // ¬Q x}) : ℝ) := by
  have h := sum_comp_splitEmb_fst (W := W) Q (fun _ => (1 : ℝ))
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one,
    Fintype.card_embedding_eq] at h
  rw [Fintype.card_embedding_eq]
  exact h

end Split

section Into
variable {α W : Type*} [Fintype α] [Fintype W] [DecidableEq W]

/-- Injective maps into a fixed set of size `a` are counted by the falling
factorial of `a`. -/
theorem card_embedding_into (A : Finset W) :
    (univ.filter (fun f : α ↪ W => ∀ x, f x ∈ A)).card =
      A.card.descFactorial (Fintype.card α) := by
  rw [← Fintype.card_subtype, ← Fintype.card_coe A, ← Fintype.card_embedding_eq]
  refine Fintype.card_congr
    { toFun := fun f => ⟨fun x => ⟨f.1 x, f.2 x⟩,
        fun x y h => f.1.injective (congrArg Subtype.val h)⟩
      invFun := fun g => ⟨g.trans (Function.Embedding.subtype _), fun x => (g x).2⟩
      left_inv := fun f => by ext; rfl
      right_inv := fun g => by ext; rfl }

end Into

section Falling

/-- Drawing without replacement from `b` elements lands in a fixed set of
`a ≤ b` elements less often than drawing with replacement. -/
theorem descFactorial_mul_pow_le {a b : ℕ} (hab : a ≤ b) :
    ∀ s : ℕ, a.descFactorial s * b ^ s ≤ a ^ s * b.descFactorial s
  | 0 => by simp
  | s + 1 => by
    have ih := descFactorial_mul_pow_le hab s
    have hstep : (a - s) * b ≤ a * (b - s) := by
      rcases le_or_gt a s with has | has
      · simp [Nat.sub_eq_zero_of_le has]
      · have hsb : s ≤ b := has.le.trans hab
        zify [has.le, hsb]
        nlinarith
    rw [Nat.descFactorial_succ, Nat.descFactorial_succ, pow_succ, pow_succ]
    calc (a - s) * a.descFactorial s * (b ^ s * b)
        = ((a - s) * b) * (a.descFactorial s * b ^ s) := by ring
      _ ≤ (a * (b - s)) * (a ^ s * b.descFactorial s) := Nat.mul_le_mul hstep ih
      _ = a ^ s * a * ((b - s) * b.descFactorial s) := by ring

/-- The real form of `descFactorial_mul_pow_le`. -/
theorem descFactorial_div_le_pow {a b s : ℕ} (hab : a ≤ b) (hs : s ≤ b) :
    (a.descFactorial s : ℝ) / b.descFactorial s ≤ ((a : ℝ) / b) ^ s := by
  have hpos : (0 : ℝ) < b.descFactorial s := by
    exact_mod_cast Nat.descFactorial_pos.mpr hs
  rcases Nat.eq_zero_or_pos b with hb | hb
  · subst hb
    have : s = 0 := Nat.le_zero.mp hs
    subst this; simp
  have hbpos : (0 : ℝ) < b := by exact_mod_cast hb
  rw [div_le_iff₀ hpos, div_pow, div_mul_eq_mul_div, le_div_iff₀ (by positivity)]
  exact_mod_cast descFactorial_mul_pow_le hab s

/-- The first factor of a falling factorial is `n`, and the other `t`
factors are at least `n - t`. -/
theorem mul_pow_le_descFactorial (n : ℕ) :
    ∀ t : ℕ, n * (n - t) ^ t ≤ n.descFactorial (t + 1)
  | 0 => by simp
  | t + 1 => by
    have ih := mul_pow_le_descFactorial n t
    rw [Nat.descFactorial_succ, pow_succ]
    have h1 : (n - (t + 1)) ^ t ≤ (n - t) ^ t := Nat.pow_le_pow_left (by omega) t
    calc n * ((n - (t + 1)) ^ t * (n - (t + 1)))
        = (n - (t + 1)) * (n * (n - (t + 1)) ^ t) := by ring
      _ ≤ (n - (t + 1)) * (n * (n - t) ^ t) :=
          Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ h1)
      _ ≤ (n - (t + 1)) * n.descFactorial (t + 1) := Nat.mul_le_mul_left _ ih

end Falling

end GraphMinor.Thomason.Uniform
