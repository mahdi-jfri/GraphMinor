module

public import Mathlib.Order.WellFoundedSet
import Lean.Elab.Tactic.Omega

/-!
# The minimal bad sequence argument for finite trees

An object has a finite list of children of smaller rank. A child embeds in its
parent, and an embedding of child lists gives an embedding of parents. Under
these conditions, a preorder on the objects is a well-quasi-order.

We follow the minimal bad sequence argument of Nash-Williams, using Mathlib's
minimal bad sequence construction and Higman's lemma. First the children of a
minimal bad sequence form a well-quasi-ordered set. Higman then compares two
lists of children and hence two terms of the purported bad sequence.
-/

public section

namespace GraphMinor.Kruskal

open Set Set.PartiallyWellOrderedOn

/-- The children of a minimal bad sequence are well-quasi-ordered. Otherwise
splice a bad sequence of children into the first parent from which it is
chosen, contradicting the minimal rank at that position. -/
theorem children_partiallyWellOrderedOn {α : Type*} {r : α → α → Prop}
    [IsPreorder α r] (children : α → List α) (rank : α → ℕ)
    (child_rank : ∀ a b, b ∈ children a → rank b < rank a)
    (child_embeds : ∀ a b, b ∈ children a → r b a)
    (f : ℕ → α) (hf : IsBadSeq r univ f)
    (hmin : ∀ n, IsMinBadSeq r rank univ n f) :
    {b | ∃ n, b ∈ children (f n)}.PartiallyWellOrderedOn r := by
  classical
  rw [iff_forall_not_isBadSeq]
  intro g hg
  choose origin horigin using hg.1
  obtain ⟨φ, hφ⟩ :=
    (wellQuasiOrdered_le (α := ℕ)).exists_monotone_subseq origin
  let k := origin (φ 0)
  let splice : ℕ → α := fun n ↦ if n < k then f n else g (φ (n - k))
  have hprefix : ∀ m, m < k → f m = splice m := by
    intro m hm
    simp only [splice, hm, ↓reduceIte]
  have hrank : rank (splice k) < rank (f k) := by
    simpa only [splice, lt_irrefl, ↓reduceIte, Nat.sub_self] using
      child_rank (f k) (g (φ 0)) (horigin (φ 0))
  apply hmin k splice hprefix hrank
  refine ⟨fun _ ↦ mem_univ _, ?_⟩
  intro m n hmn hrel
  by_cases hm : m < k
  · by_cases hn : n < k
    · simp only [splice, hm, hn, ↓reduceIte] at hrel
      exact hf.2 m n hmn hrel
    · simp only [splice, hm, hn, ↓reduceIte] at hrel
      have hkn : k ≤ origin (φ (n - k)) := hφ 0 (n - k) (Nat.zero_le _)
      exact hf.2 m (origin (φ (n - k))) (lt_of_lt_of_le hm hkn)
        (_root_.trans hrel (child_embeds _ _ (horigin (φ (n - k)))))
  · have hn : ¬ n < k := by omega
    simp only [splice, hm, hn, ↓reduceIte] at hrel
    exact hg.2 (φ (m - k)) (φ (n - k)) (φ.strictMono (by omega)) hrel

/-- Nash-Williams' minimal bad sequence argument, with Higman's lemma for
lists of children. The hypotheses describe the rank and the embedding
operations, so the theorem also applies to other finite recursive objects. -/
theorem wellQuasiOrdered_of_children {α : Type*} {r : α → α → Prop}
    [IsPreorder α r] (children : α → List α) (rank : α → ℕ)
    (child_rank : ∀ a b, b ∈ children a → rank b < rank a)
    (child_embeds : ∀ a b, b ∈ children a → r b a)
    (parents_embed : ∀ a b,
      List.SublistForall₂ r (children a) (children b) → r a b) :
    WellQuasiOrdered r := by
  rw [← partiallyWellOrderedOn_univ_iff, iff_not_exists_isMinBadSeq rank]
  rintro ⟨f, hf, hmin⟩
  have hc := children_partiallyWellOrderedOn children rank child_rank child_embeds f hf hmin
  have hl := hc.partiallyWellOrderedOn_sublistForall₂ r
  obtain ⟨i, j, hij, hrel⟩ := partiallyWellOrderedOn_iff_exists_lt.1 hl
    (fun n ↦ children (f n)) (fun n b hb ↦ ⟨n, hb⟩)
  exact hf.2 i j hij (parents_embed (f i) (f j) hrel)

end GraphMinor.Kruskal
