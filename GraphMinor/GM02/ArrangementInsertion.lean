module

public import GraphMinor.GM02.PathListArrangement
import Mathlib.Data.Set.Insert

/-!
# Recovering an arrangement after one erasure

The insertion choices for II (2.8) are two unused labels, a beginning of
one of the path lists, or a position after one remaining vertex. Each
arrangement admits such a slot. Its erased lists and that slot recover
all the original lists.
-/

@[expose] public section
namespace GraphMinor.GM02
open Set Classical
universe u t
variable {α : Type u} {S : Set α} {I : Type t}

/-- The possible insertion slots: unused label, path beginning, or predecessor. -/
abbrev ArrangementSlot (S : Set α) (I : Type t) := Bool ⊕ (I ⊕ S)

/-- The slot describes the erased vertex's original position. -/
def PathListArrangement.SlotDescribes (A : PathListArrangement S I) (a : α) :
    ArrangementSlot (S \ {a}) I → Prop
  | Sum.inl b => (∀ i, a ∉ A.paths i) ∧ (a ∈ A.marked ↔ b = true)
  | Sum.inr (Sum.inl i) => listInsertionSlot a (A.paths i) = some none
  | Sum.inr (Sum.inr b) => ∃ i, listInsertionSlot a (A.paths i) = some (some b.val)

/-- Every arrangement supplies a slot for a vertex in the fixed set. -/
theorem PathListArrangement.exists_slot (A : PathListArrangement S I) (a : α) :
    ∃ slot : ArrangementSlot (S \ {a}) I, A.SlotDescribes a slot := by
  by_cases hused : ∃ i, a ∈ A.paths i
  · obtain ⟨i, hi⟩ := hused
    cases hs : listInsertionSlot a (A.paths i) with
    | none => exact ((listInsertionSlot_none_iff a _).1 hs hi).elim
    | some slot =>
      cases slot with
      | none => exact ⟨Sum.inr (Sum.inl i), hs⟩
      | some b =>
        have hb := mem_erase_of_listInsertionSlot (A.nodup i) hs
        have hbS : b ∈ S \ {a} := (A.erase a).vertex_mem i b hb
        exact ⟨Sum.inr (Sum.inr ⟨b, hbS⟩), i, hs⟩
  · refine ⟨Sum.inl (decide (a ∈ A.marked)), ?_⟩
    exact ⟨fun i hi => hused ⟨i, hi⟩, by simp⟩

/-- Reinsert a vertex into its slot in a family of erased lists. -/
noncomputable def restoreArrangementPaths (a : α) (paths : I → List α)
    (slot : ArrangementSlot (S \ {a}) I) : I → List α :=
  match slot with
  | Sum.inl _ => paths
  | Sum.inr (Sum.inl i) => fun j => if j = i then a :: paths j else paths j
  | Sum.inr (Sum.inr b) => fun j => insertAfter a b.val (paths j)

/-- The erased lists and a described slot recover the original lists. -/
theorem PathListArrangement.restore_paths (A : PathListArrangement S I) (a : α)
    (slot : ArrangementSlot (S \ {a}) I) (hs : A.SlotDescribes a slot) :
    restoreArrangementPaths a (A.erase a).paths slot = A.paths := by
  funext j
  cases slot with
  | inl b =>
    have hnone := (listInsertionSlot_none_iff a (A.paths j)).2 (hs.1 j)
    simpa [restoreArrangementPaths, PathListArrangement.erase, hnone] using
      reconstruct_list_of_slot a (A.nodup j)
  | inr slot =>
    cases slot with
    | inl i =>
      change listInsertionSlot a (A.paths i) = some none at hs
      have hi : a ∈ A.paths i := by
        by_contra hn
        have heq := (listInsertionSlot_none_iff a _).2 hn
        rw [hs] at heq
        contradiction
      by_cases hji : j = i
      · subst j
        simpa [restoreArrangementPaths, PathListArrangement.erase, hs] using
          reconstruct_list_of_slot a (A.nodup i)
      · have hja : a ∉ A.paths j := A.disjoint i j (Ne.symm hji) a hi
        have hnone := (listInsertionSlot_none_iff a (A.paths j)).2 hja
        simpa [restoreArrangementPaths, PathListArrangement.erase, hji, hnone] using
          reconstruct_list_of_slot a (A.nodup j)
    | inr b =>
      obtain ⟨i, hi⟩ := hs
      by_cases hji : j = i
      · subst j
        simpa [restoreArrangementPaths, PathListArrangement.erase, hi] using
          reconstruct_list_of_slot a (A.nodup i)
      · have hbi : b.val ∈ A.paths i := mem_of_listInsertionSlot hi
        have hbj : b.val ∉ A.paths j := A.disjoint i j (Ne.symm hji) b.val hbi
        have hai : a ∈ A.paths i := by
          by_contra hn
          have heq := (listInsertionSlot_none_iff a _).2 hn
          rw [hi] at heq
          contradiction
        have haj : a ∉ A.paths j := A.disjoint i j (Ne.symm hji) a hai
        have hnone := (listInsertionSlot_none_iff a (A.paths j)).2 haj
        have hlist := reconstruct_list_of_slot a (A.nodup j)
        simp only [hnone] at hlist
        change insertAfter a b.val ((A.paths j).erase a) = A.paths j
        rw [hlist, insertAfter_eq_of_not_mem a b.val hbj]

/-- The unused true slot records exactly membership in the marked set. -/
theorem PathListArrangement.marked_iff_slot (A : PathListArrangement S I) (a : α)
    (slot : ArrangementSlot (S \ {a}) I) (hs : A.SlotDescribes a slot) :
    a ∈ A.marked ↔ slot = Sum.inl true := by
  cases slot with
  | inl b => simpa using hs.2
  | inr slot =>
    have hm : a ∉ A.marked := by
      intro ha
      cases slot with
      | inl i =>
        change listInsertionSlot a (A.paths i) = some none at hs
        have heq := (listInsertionSlot_none_iff a _).2 (A.marked_unused a ha i)
        rw [hs] at heq
        contradiction
      | inr b =>
        obtain ⟨i, hi⟩ := hs
        have heq := (listInsertionSlot_none_iff a _).2 (A.marked_unused a ha i)
        rw [hi] at heq
        contradiction
    simp [hm]

/-- Recover the marked set from an erasure and its slot. -/
noncomputable def restoreArrangementMarked (a : α) (marked : Set α)
    (slot : ArrangementSlot (S \ {a}) I) : Set α :=
  (if slot = Sum.inl true then {a} else ∅) ∪ marked

/-- The erased marked set and a described slot recover the original one. -/
theorem PathListArrangement.restore_marked (A : PathListArrangement S I) (a : α)
    (slot : ArrangementSlot (S \ {a}) I) (hs : A.SlotDescribes a slot) :
    restoreArrangementMarked a (A.erase a).marked slot = A.marked := by
  have hm := A.marked_iff_slot a slot hs
  ext v
  by_cases hv : v = a
  · subst v
    by_cases hslot : slot = Sum.inl true
    · have ha := hm.mpr hslot
      simp [restoreArrangementMarked, PathListArrangement.erase, Set.mem_singleton_iff, hslot, ha]
    · have ha : a ∉ A.marked := fun h => hslot (hm.mp h)
      simp [restoreArrangementMarked, PathListArrangement.erase, Set.mem_singleton_iff, hslot, ha]
  · by_cases hslot : slot = Sum.inl true <;>
      simp [restoreArrangementMarked, PathListArrangement.erase, Set.mem_singleton_iff, hslot, hv]

/-- Erase one vertex and record its slot. -/
noncomputable def PathListArrangement.erasureEncoding (a : α)
    (A : PathListArrangement S I) :
    PathListArrangement (S \ {a}) I × ArrangementSlot (S \ {a}) I :=
  (A.erase a, (A.exists_slot a).choose)

/-- Erasure together with the slot is an injection. Consequently its
codomain bounds the number of insertion choices at each stage. -/
theorem PathListArrangement.erasureEncoding_injective (a : α) :
    Function.Injective (PathListArrangement.erasureEncoding (S := S) (I := I) a) := by
  intro A B heq
  have he := congrArg Prod.fst heq
  have hs := congrArg Prod.snd heq
  change A.erase a = B.erase a at he
  change (A.exists_slot a).choose = (B.exists_slot a).choose at hs
  apply PathListArrangement.ext_data
  · calc
      A.paths = restoreArrangementPaths a (A.erase a).paths (A.exists_slot a).choose :=
        (A.restore_paths a _ (A.exists_slot a).choose_spec).symm
      _ = restoreArrangementPaths a (B.erase a).paths (B.exists_slot a).choose := by rw [he, hs]
      _ = B.paths := B.restore_paths a _ (B.exists_slot a).choose_spec
  · calc
      A.marked = restoreArrangementMarked a (A.erase a).marked (A.exists_slot a).choose :=
        (A.restore_marked a _ (A.exists_slot a).choose_spec).symm
      _ = restoreArrangementMarked a (B.erase a).marked (B.exists_slot a).choose := by rw [he, hs]
      _ = B.marked := B.restore_marked a _ (B.exists_slot a).choose_spec

end GraphMinor.GM02
