module

public import GraphMinor.Compute.GM06Alg34GapPositionOrder

/-!
# Restricting an interleaved cuff order

An increasing selection of cuff positions selects their vertices and
following gaps together. Its extension to alternating even and odd
positions is still increasing. Hence both the primal-versus-gap crossing
test and the gap cyclic order restrict exactly to the selected positions.
-/

@[expose] public section
namespace GraphMinor.Compute

/-- Extend a position selection by retaining its vertex and following gap together. -/
def gm06InterleavedIndex {k n : ℕ} (f : Fin k → Fin n) (a : Fin (2 * k)) : Fin (2 * n) :=
  ⟨2 * (f ⟨a.val / 2, by omega⟩).val + a.val % 2, by
    have hb := (f ⟨a.val / 2, by omega⟩).isLt
    omega⟩

/-- An increasing selection remains increasing on the full alternating order. -/
theorem gm06InterleavedIndex_strictMono {k n : ℕ} (f : Fin k → Fin n) (hf : StrictMono f) :
    StrictMono (gm06InterleavedIndex f) := by
  intro a b hab
  let i : Fin k := ⟨a.val / 2, by omega⟩
  let j : Fin k := ⟨b.val / 2, by omega⟩
  change 2 * (f i).val + a.val % 2 < 2 * (f j).val + b.val % 2
  change a.val < b.val at hab
  by_cases he : a.val / 2 = b.val / 2
  · have hij : i = j := Fin.ext he
    rw [hij]
    omega
  · have hij : i < j := by change a.val / 2 < b.val / 2; omega
    have hh := hf hij
    change (f i).val < (f j).val at hh
    omega

/-- The extended selection sends each even position to the selected vertex position. -/
theorem gm06InterleavedIndex_even {k n : ℕ} (f : Fin k → Fin n) (a : Fin k) :
    gm06InterleavedIndex f (gm06EvenIndex a) = gm06EvenIndex (f a) := by
  have hi : (⟨(2 * a.val) / 2, by omega⟩ : Fin k) = a := Fin.ext (by change (2 * a.val) / 2 = a.val; omega)
  apply Fin.ext
  change 2 * (f ⟨(2 * a.val) / 2, by omega⟩).val + (2 * a.val) % 2 = 2 * (f a).val
  rw [hi]
  omega

/-- The extended selection sends each odd position to the selected following gap. -/
theorem gm06InterleavedIndex_odd {k n : ℕ} (f : Fin k → Fin n) (a : Fin k) :
    gm06InterleavedIndex f (gm06OddIndex a) = gm06OddIndex (f a) := by
  have hi : (⟨(2 * a.val + 1) / 2, by omega⟩ : Fin k) = a := Fin.ext (by change (2 * a.val + 1) / 2 = a.val; omega)
  apply Fin.ext
  change 2 * (f ⟨(2 * a.val + 1) / 2, by omega⟩).val + (2 * a.val + 1) % 2 = 2 * (f a).val + 1
  rw [hi]
  omega

/-- Selecting increasing vertex positions and their following gaps preserves the gap crossing test. -/
theorem gm06PairCrossesGaps_fin_mono {k n : ℕ} (f : Fin k → Fin n) (hf : StrictMono f)
    (a b i j : Fin k) :
    GM06DrawingData.pairCrossesGaps (List.finRange k) a b
      (Fin.cast List.length_finRange.symm i) (Fin.cast List.length_finRange.symm j) =
    GM06DrawingData.pairCrossesGaps (List.finRange n) (f a) (f b)
      (Fin.cast List.length_finRange.symm (f i)) (Fin.cast List.length_finRange.symm (f j)) := by
  have he := gm06CrossesFinRange_map (gm06InterleavedIndex f)
    (gm06InterleavedIndex_strictMono f hf) (gm06EvenIndex a) (gm06EvenIndex b)
    (gm06OddIndex i) (gm06OddIndex j)
  rw [gm06InterleavedIndex_even, gm06InterleavedIndex_even,
    gm06InterleavedIndex_odd, gm06InterleavedIndex_odd,
    gm06EvenOdd_crosses, gm06EvenOdd_crosses] at he
  exact he.symm

end GraphMinor.Compute
