module

public import Mathlib.Data.Set.Card
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-!
# Counting finite disjoint regions

The component grouping in II (2.6) uses the fact that the count in a
union of disjoint components is the sum of their counts. This file proves
that fact by inserting one region at a time.
-/

public section
namespace GraphMinor.GM02
open Set Finset Classical

/-- Counting a finite union of disjoint regions inside a finite set. -/
theorem ncard_regions_inter {α : Type*} {ι : Type*} (s : Finset ι)
    (C : ι → Set α) {Q : Set α} (hQ : Q.Finite)
    (hdis : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → Disjoint (C i) (C j)) :
    ((⋃ i ∈ s, C i) ∩ Q).ncard = ∑ i ∈ s, (C i ∩ Q).ncard := by
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
    have hrest : ∀ a ∈ s, ∀ b ∈ s, a ≠ b → Disjoint (C a) (C b) :=
      fun a ha b hb hab => hdis a (mem_insert_of_mem ha) b (mem_insert_of_mem hb) hab
    have hd : Disjoint (C i ∩ Q) ((⋃ j ∈ s, C j) ∩ Q) := by
      apply Set.disjoint_left.2
      intro x hxi hxs
      obtain ⟨j, hj⟩ := Set.mem_iUnion.1 hxs.1
      obtain ⟨hjs, hxj⟩ := Set.mem_iUnion.1 hj
      exact Set.disjoint_left.1
        (hdis i (mem_insert_self _ _) j (mem_insert_of_mem hjs)
          (fun h => hi (h ▸ hjs))) hxi.1 hxj
    have heq : (⋃ j ∈ insert i s, C j) ∩ Q =
        (C i ∩ Q) ∪ ((⋃ j ∈ s, C j) ∩ Q) := by
      simp only [Finset.set_biUnion_insert, Set.union_inter_distrib_right]
    rw [heq, Set.ncard_union_eq hd (hQ.subset Set.inter_subset_right)
      (hQ.subset Set.inter_subset_right), ih hrest, Finset.sum_insert hi]

end GraphMinor.GM02
