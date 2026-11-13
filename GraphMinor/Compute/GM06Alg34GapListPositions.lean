module

public import GraphMinor.Compute.GM06Alg34DualGapRelation
public import GraphMinor.Compute.GM06Alg34MapCrossing

/-!
# Reading crossing order through cuff list positions

A cuff without repeated labels identifies its positions with its listed
vertices. Both primal crossing tests and primal-versus-gap comparisons
are unchanged by this identification. These equalities let a sorted
geometric vertex list supply the gap input's crossing interpretation.
-/

public section
namespace GraphMinor.Compute

open GM06DrawingData

private theorem idxOf_get {n : ℕ} {L : List (Fin n)} (hL : L.Nodup) (i : Fin L.length) :
    L.idxOf (L.get i) = i.val := by
  have hb := List.idxOf_lt_length_iff.mpr (L.get_mem i)
  have hg := List.idxOf_get (a := L.get i) hb
  have hi : (⟨L.idxOf (L.get i), hb⟩ : Fin L.length) = i := hL.get_inj_iff.mp hg
  exact congrArg Fin.val hi

/-- Crossing a pair of listed labels with gaps agrees with the position comparison. -/
theorem gm06PairCrossesGaps_get {n : ℕ} {L : List (Fin n)} (hL : L.Nodup)
    (a b i j : Fin L.length) :
    pairCrossesGaps L (L.get a) (L.get b) i j =
      pairCrossesGaps (List.finRange L.length) a b
        (Fin.cast List.length_finRange.symm i) (Fin.cast List.length_finRange.symm j) := by
  simp only [pairCrossesGaps, gapSide, List.get_mem, List.mem_finRange, true_and,
    ne_eq, hL.get_inj_iff, idxOf_get hL, List.idxOf_finRange]
  rfl

/-- Crossing four listed labels agrees with their four cuff positions. -/
theorem gm06CrossesOnList_get {n : ℕ} {L : List (Fin n)} (hL : L.Nodup)
    (a c b d : Fin L.length) :
    crossesOnList L (L.get a) (L.get c) (L.get b) (L.get d) =
      crossesOnList (List.finRange L.length) a c b d := by
  have hi : Function.Injective L.get := fun _ _ he => hL.get_inj_iff.mp he
  have hm : (List.finRange L.length).map L.get = L := by
    rw [← List.ofFn_eq_map, List.ofFn_get]
  have he := gm06_crossesOnList_map L.get hi (List.finRange L.length) a c b d
  rw [hm] at he
  exact he

end GraphMinor.Compute
