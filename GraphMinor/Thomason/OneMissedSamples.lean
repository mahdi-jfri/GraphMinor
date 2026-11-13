module

public import GraphMinor.Thomason.VertexSamples
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Finset.Prod
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega

/-!
# Counting sequences with at most one exceptional coordinate

Partition a sequence by its first coordinate. If that coordinate is
exceptional, every later coordinate must be ordinary. Otherwise the tail
may contain one exceptional coordinate. This recurrence gives an exact
count, including repetitions, for use in the branch selection argument.
-/

@[expose] public section
namespace GraphMinor.Thomason
open Finset
universe u
variable {V : Type u} [Fintype V] [DecidableEq V]

/-- The positions at which a sample takes a value in the exceptional set. -/
def sampleBadPositions (A : Finset V) {m : ℕ} (f : Fin m → V) : Finset (Fin m) :=
  univ.filter (fun i => f i ∈ A)

/-- Sequences that avoid the exceptional set entirely. -/
def avoidingSamples (A : Finset V) (m : ℕ) : Finset (Fin m → V) :=
  univ.filter (fun f => ∀ i, f i ∉ A)

/-- Sequences with at most one exceptional position. -/
def oneBadSamples (A : Finset V) (m : ℕ) : Finset (Fin m → V) :=
  univ.filter (fun f => (sampleBadPositions A f).card ≤ 1)

omit [Fintype V] in
/-- No exceptional positions means every coordinate is ordinary. -/
theorem card_sampleBadPositions_eq_zero_iff (A : Finset V) {m : ℕ} (f : Fin m → V) :
    (sampleBadPositions A f).card = 0 ↔ ∀ i, f i ∉ A := by
  simp [sampleBadPositions, card_eq_zero]

omit [Fintype V] in
/-- Separate the exceptional count at the first coordinate from the tail. -/
theorem card_sampleBadPositions_cons (A : Finset V) {m : ℕ} (a : V) (f : Fin m → V) :
    (sampleBadPositions A (Fin.cons a f)).card =
      (if a ∈ A then 1 else 0) + (sampleBadPositions A f).card := by
  simp only [sampleBadPositions, card_eq_sum_ones, sum_filter]
  rw [Fin.sum_univ_succ]
  simp only [Fin.cons_zero, Fin.cons_succ]

/-- All avoiding sequences are counted by a power of the complement size. -/
theorem card_avoidingSamples (A : Finset V) (m : ℕ) :
    (avoidingSamples A m).card = (Fintype.card V - A.card) ^ m := by
  have hh := card_vertex_sequences_in_finset ((univ : Finset V) \ A) m
  simpa only [avoidingSamples, mem_sdiff, mem_univ, true_and,
    card_sdiff_of_subset (subset_univ A), card_univ] using hh

/-- Split the one-exception family according to whether the first
coordinate is ordinary or exceptional. -/
theorem oneBadSamples_succ (A : Finset V) (m : ℕ) :
    oneBadSamples A (m + 1) =
      (((univ \ A).product (oneBadSamples A m)) ∪
        (A.product (avoidingSamples A m))).image (fun p => Fin.cons p.1 p.2) := by
  ext f
  obtain ⟨⟨a, g⟩, rfl⟩ := (Fin.consEquiv (fun _ : Fin (m + 1) => V)).surjective f
  change (Fin.cons a g : Fin (m + 1) → V) ∈ _ ↔ (Fin.cons a g : Fin (m + 1) → V) ∈ _
  constructor
  · intro hf
    have hcard : (if a ∈ A then 1 else 0) + (sampleBadPositions A g).card ≤ 1 := by
      simpa only [oneBadSamples, mem_filter, mem_univ, true_and,
        card_sampleBadPositions_cons] using hf
    refine mem_image.mpr ⟨(a, g), ?_, rfl⟩
    by_cases ha : a ∈ A
    · have hzero : (sampleBadPositions A g).card = 0 := by simp only [ha, ite_true] at hcard; omega
      exact mem_union_right _ (mem_product.mpr ⟨ha, mem_filter.mpr ⟨mem_univ _,
        (card_sampleBadPositions_eq_zero_iff A g).mp hzero⟩⟩)
    · have htail : (sampleBadPositions A g).card ≤ 1 := by simpa only [ha, ite_false, zero_add] using hcard
      exact mem_union_left _ (mem_product.mpr ⟨mem_sdiff.mpr ⟨mem_univ _, ha⟩,
        mem_filter.mpr ⟨mem_univ _, htail⟩⟩)
  · intro hf
    obtain ⟨⟨b, h⟩, hmem, heq⟩ := mem_image.mp hf
    obtain ⟨hab, hhg⟩ := Fin.cons_inj.mp heq
    change b = a at hab
    change h = g at hhg
    subst b
    subst h
    apply mem_filter.mpr
    refine ⟨mem_univ _, ?_⟩
    rw [card_sampleBadPositions_cons]
    rcases mem_union.mp hmem with hgood | hbad
    · obtain ⟨ha, hg⟩ := mem_product.mp hgood
      have hnot := (mem_sdiff.mp ha).2
      simpa only [hnot, ite_false, zero_add] using (mem_filter.mp hg).2
    · obtain ⟨ha, hg⟩ := mem_product.mp hbad
      have hz := (card_sampleBadPositions_eq_zero_iff A g).mpr (mem_filter.mp hg).2
      simp only [ha, ite_true, hz, add_zero, le_refl]

/-- The disjoint first-coordinate split gives the cardinal recurrence. -/
theorem card_oneBadSamples_succ (A : Finset V) (m : ℕ) :
    (oneBadSamples A (m + 1)).card =
      (Fintype.card V - A.card) * (oneBadSamples A m).card +
        A.card * (avoidingSamples A m).card := by
  have hinj : Function.Injective (fun p : V × (Fin m → V) => (Fin.cons p.1 p.2 : Fin (m + 1) → V)) :=
    (Fin.consEquiv (fun _ : Fin (m + 1) => V)).injective
  rw [oneBadSamples_succ, card_image_of_injective _ hinj]
  have hdis : Disjoint ((univ \ A).product (oneBadSamples A m))
      (A.product (avoidingSamples A m)) := by
    apply disjoint_left.mpr
    intro p hp hq
    exact (mem_sdiff.mp (mem_product.mp hp).1).2 (mem_product.mp hq).1
  rw [card_union_of_disjoint hdis]
  simp only [product_eq_sprod, card_product, card_sdiff_of_subset (subset_univ A), card_univ]

/-- There are `g^m + m*d*g^(m-1)` sequences with at most one exceptional
coordinate, where the exceptional set has size `d` and its complement size `g`. -/
theorem card_oneBadSamples (A : Finset V) (m : ℕ) :
    (oneBadSamples A m).card = (Fintype.card V - A.card) ^ m +
      m * A.card * (Fintype.card V - A.card) ^ (m - 1) := by
  induction m with
  | zero => simp [oneBadSamples, sampleBadPositions]
  | succ m ih =>
    rw [card_oneBadSamples_succ, ih, card_avoidingSamples]
    cases m with
    | zero => simp
    | succ m => simp only [pow_succ, Nat.add_sub_cancel]; ring

end GraphMinor.Thomason
