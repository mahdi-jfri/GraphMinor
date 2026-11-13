module

public import GraphMinor.GM02.SmallArrangementLists
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Basic.Finite.Sum

/-!
# Counting even lists on small separators

On two separator vertices, if all path lengths are even then either every
path list is empty, with four unused label choices, or one list contains
both vertices, with a path choice and two possible orders. On one vertex
all lists are empty, leaving two unused labels. These are the zero-parity
cases in the proof of II (2.8).
-/

public section
namespace GraphMinor.GM02
open Set Classical
universe u t

private theorem eq_of_full_path {α : Type u} {S : Set α} {I : Type t}
    (hS : S.Finite) (A B : PathListArrangement S I) (i : I)
    (hlen : (A.paths i).length = S.ncard) (hfull : ∀ v ∈ S, v ∈ A.paths i)
    (heq : A.paths i = B.paths i) : A = B := by
  apply PathListArrangement.ext_data
  · funext j
    by_cases hji : j = i
    · subst j; exact heq
    · have hA := A.length_add_le hS (Ne.symm hji)
      have hB := B.length_add_le hS (Ne.symm hji)
      rw [← heq] at hB
      rw [hlen] at hA hB
      have hAz : A.paths j = [] := List.length_eq_zero_iff.1 (by omega)
      have hBz : B.paths j = [] := List.length_eq_zero_iff.1 (by omega)
      exact hAz.trans hBz.symm
  · have hA : A.marked = ∅ := Set.eq_empty_iff_forall_notMem.2 (fun v hv =>
      A.marked_unused v hv i (hfull v (A.marked_subset hv)))
    have hB : B.marked = ∅ := Set.eq_empty_iff_forall_notMem.2 (fun v hv =>
      B.marked_unused v hv i (heq ▸ hfull v (B.marked_subset hv)))
    exact hA.trans hB.symm

private def EvenPairCodeDescribes {α : Type u} {I : Type t} (a b : α)
    (A : PathListArrangement ({a, b} : Set α) I) :
    (Bool × Bool) ⊕ (I × Bool) → Prop
  | Sum.inl bits => (∀ i, A.paths i = []) ∧
      (a ∈ A.marked ↔ bits.1 = true) ∧ (b ∈ A.marked ↔ bits.2 = true)
  | Sum.inr slot => A.paths slot.1 = if slot.2 then [a, b] else [b, a]

private theorem even_pair_code_exists {α : Type u} {I : Type t} {a b : α}
    (hab : a ≠ b) (A : PathListArrangement ({a, b} : Set α) I)
    (heven : ∀ i, (A.paths i).length % 2 = 0) :
    ∃ code, EvenPairCodeDescribes a b A code := by
  by_cases hused : ∃ i, A.paths i ≠ []
  · obtain ⟨i, hi⟩ := hused
    rcases even_list_on_pair hab (A.paths i) (A.nodup i) (A.vertex_mem i) (heven i) with
      hnil | horder | horder
    · exact (hi hnil).elim
    · exact ⟨Sum.inr (i, true), horder⟩
    · exact ⟨Sum.inr (i, false), horder⟩
  · exact ⟨Sum.inl (decide (a ∈ A.marked), decide (b ∈ A.marked)),
      ⟨fun i => by by_contra hn; exact hused ⟨i, hn⟩, by simp, by simp⟩⟩

private theorem even_pair_code_unique {α : Type u} {I : Type t} {a b : α}
    (hab : a ≠ b) {A B : PathListArrangement ({a, b} : Set α) I} {code}
    (hA : EvenPairCodeDescribes a b A code) (hB : EvenPairCodeDescribes a b B code) : A = B := by
  cases code with
  | inl bits =>
    apply PathListArrangement.ext_data
    · funext i; exact (hA.1 i).trans (hB.1 i).symm
    · ext v
      constructor
      · intro hv
        have hm := A.marked_subset hv
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hm
        rcases hm with rfl | rfl
        · exact hB.2.1.mpr (hA.2.1.mp hv)
        · exact hB.2.2.mpr (hA.2.2.mp hv)
      · intro hv
        have hm := B.marked_subset hv
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hm
        rcases hm with rfl | rfl
        · exact hA.2.1.mpr (hB.2.1.mp hv)
        · exact hA.2.2.mpr (hB.2.2.mp hv)
  | inr slot =>
    change A.paths slot.1 = (if slot.2 then [a, b] else [b, a]) at hA
    change B.paths slot.1 = (if slot.2 then [a, b] else [b, a]) at hB
    apply eq_of_full_path ((Set.finite_singleton b).insert a) A B slot.1
    · rw [hA, Set.ncard_pair hab]
      cases slot.2 <;> rfl
    · intro v hv
      rw [hA]
      cases slot.2 <;> simpa [or_comm] using hv
    · exact hA.trans hB.symm

/-- At most four empty-list labelings and two orders for each possible
nonempty path occur in an even arrangement on two vertices. -/
theorem card_even_arrangements_on_pair {α : Type u} {I : Type t} [Finite I]
    {a b : α} (hab : a ≠ b) :
    Nat.card {A : PathListArrangement ({a, b} : Set α) I //
      ∀ i, (A.paths i).length % 2 = 0} ≤ 4 + 2 * Nat.card I := by
  let f : {A : PathListArrangement ({a, b} : Set α) I // ∀ i, (A.paths i).length % 2 = 0} →
      (Bool × Bool) ⊕ (I × Bool) := fun A => (even_pair_code_exists hab A.val A.property).choose
  have hf : Function.Injective f := by
    intro A B heq
    apply Subtype.ext
    have hB : EvenPairCodeDescribes a b B.val (f A) := by
      rw [heq]
      exact (even_pair_code_exists hab B.val B.property).choose_spec
    exact even_pair_code_unique hab (even_pair_code_exists hab A.val A.property).choose_spec hB
  have hc := Nat.card_le_card_of_injective f hf
  have hb : Nat.card Bool = 2 := by simp [Nat.card_eq_fintype_card]
  simpa [Nat.card_sum, Nat.card_prod, hb, Nat.mul_comm] using hc

/-- On a singleton separator, all even lists are empty and only the
unused vertex's marked bit remains. -/
theorem card_even_arrangements_on_singleton {α : Type u} {I : Type t} (a : α) :
    Nat.card {A : PathListArrangement ({a} : Set α) I //
      ∀ i, (A.paths i).length % 2 = 0} ≤ 2 := by
  let T := {A : PathListArrangement ({a} : Set α) I // ∀ i, (A.paths i).length % 2 = 0}
  have hnil : ∀ A : T, ∀ i, A.val.paths i = [] := by
    intro A i
    have hl := A.val.length_le (Set.finite_singleton a) i
    rw [Set.ncard_singleton] at hl
    have he := A.property i
    exact List.length_eq_zero_iff.1 (by omega)
  let f : T → Bool := fun A => decide (a ∈ A.val.marked)
  have hf : Function.Injective f := by
    intro A B heq
    apply Subtype.ext
    apply PathListArrangement.ext_data
    · funext i; exact (hnil A i).trans (hnil B i).symm
    · have hm : a ∈ A.val.marked ↔ a ∈ B.val.marked := by
        change decide (a ∈ A.val.marked) = decide (a ∈ B.val.marked) at heq
        simpa using (congrArg (fun b : Bool => b = true) heq).to_iff
      ext v
      by_cases hv : v = a
      · subst v; exact hm
      · have hA : v ∉ A.val.marked := fun h => hv (A.val.marked_subset h)
        have hB : v ∉ B.val.marked := fun h => hv (B.val.marked_subset h)
        simp [hA, hB]
  have hc := Nat.card_le_card_of_injective f hf
  simpa [T, Nat.card_eq_fintype_card] using hc

/-- The zero-parity profile count for a two-vertex separator. -/
theorem card_even_arrangements_of_ncard_two {α : Type u} {I : Type t} [Finite I]
    {S : Set α} (hn : S.ncard = 2) :
    Nat.card {A : PathListArrangement S I // ∀ i, (A.paths i).length % 2 = 0} ≤
      4 + 2 * Nat.card I := by
  obtain ⟨a, b, hab, rfl⟩ := Set.ncard_eq_two.1 hn
  exact card_even_arrangements_on_pair hab

/-- The zero-parity profile count for a one-vertex separator. -/
theorem card_even_arrangements_of_ncard_one {α : Type u} {I : Type t}
    {S : Set α} (hn : S.ncard = 1) :
    Nat.card {A : PathListArrangement S I // ∀ i, (A.paths i).length % 2 = 0} ≤ 2 := by
  obtain ⟨a, rfl⟩ := Set.ncard_eq_one.1 hn
  exact card_even_arrangements_on_singleton a

end GraphMinor.GM02
