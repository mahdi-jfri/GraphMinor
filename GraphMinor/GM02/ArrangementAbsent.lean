module

public import GraphMinor.GM02.ArrangementInsertion
import Mathlib.Data.Set.Insert

/-!
# Erasing a vertex absent from every path list

If a separator vertex is an original terminal, the list encoding for
II (2.8) puts it in no internal list. Erasing that vertex loses only its
marked bit. This gives two choices rather than a general insertion slot,
which is needed for the small-separator cases of the count.
-/

public section
namespace GraphMinor.GM02
open Set Classical
universe u t

/-- For a vertex absent from every list, erasure loses only its marked bit. -/
theorem PathListArrangement.eq_of_erase_of_absent {α : Type u} {S : Set α} {I : Type t}
    {A B : PathListArrangement S I} (a : α)
    (haA : ∀ i, a ∉ A.paths i) (haB : ∀ i, a ∉ B.paths i)
    (he : A.erase a = B.erase a) (hm : a ∈ A.marked ↔ a ∈ B.marked) : A = B := by
  apply PathListArrangement.ext_data
  · funext i
    have hA := reconstruct_list_of_slot a (A.nodup i)
    have hB := reconstruct_list_of_slot a (B.nodup i)
    rw [(listInsertionSlot_none_iff a _).2 (haA i)] at hA
    rw [(listInsertionSlot_none_iff a _).2 (haB i)] at hB
    calc
      A.paths i = (A.erase a).paths i := hA.symm
      _ = (B.erase a).paths i := congrArg (fun C => C.paths i) he
      _ = B.paths i := hB
  · have hme := congrArg PathListArrangement.marked he
    change A.marked \ {a} = B.marked \ {a} at hme
    ext v
    by_cases hv : v = a
    · subst v; exact hm
    · have h := Set.ext_iff.1 hme v
      simpa [Set.mem_sdiff, Set.mem_singleton_iff, hv] using h

end GraphMinor.GM02
