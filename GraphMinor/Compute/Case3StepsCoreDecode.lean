module

public import GraphMinor.Compute.Case3StepsDivision

/-!
# Reading the core vertex set from the (8.6) output

The division decoder reads its core from the tail of the output list. The
first `n` words of that tail specify core membership by being nonzero, with
missing words interpreted as zero. This file relates that reading to the
normalized bitset that the member-computation program uses.
-/

@[expose] public section

namespace GraphMinor.Compute

open Classical

/-- The normalized core membership words, including zero defaults for short
outputs, in exactly the sense of `decAlg83Out`. -/
def case3CoreBitList (n : ℕ) (out : List ℕ) : List ℕ :=
  List.ofFn (fun i : Fin n => if out.getD (i.1 + 1) 0 = 0 then 0 else 1)

/-- Normalization writes the core bitset specified by the decoder. -/
theorem case3CoreBitList_eq_bitSetList (n : ℕ) (out : List ℕ) :
    case3CoreBitList n out = bitSetList (finsetOfBitList n (out.tail.take n)) := by
  apply List.ext_getElem (by simp only [case3CoreBitList, List.length_ofFn, length_bitSetList])
  intro i hi hj
  have hin : i < n := by simpa only [case3CoreBitList, List.length_ofFn] using hi
  rw [getElem_bitSetList _ i hin]
  simp only [case3CoreBitList, List.getElem_ofFn, mem_finsetOfBitList,
    List.getD_eq_getElem?_getD, List.getElem?_take, hin, ↓reduceIte, List.getElem?_tail]
  by_cases hz : out[i + 1]?.getD 0 = 0 <;> simp [hz]

private theorem getD_take_eq (l : List ℕ) (len i : ℕ) (hi : i < len) :
    (l.take len).getD i 0 = l.getD i 0 := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_take, hi, ↓reduceIte]

private theorem graphOfFlatEdges_take_header (n : ℕ) (l : List ℕ) :
    graphOfFlatEdges n (l.take (2 + 2 * l.getD 1 0)) = graphOfFlatEdges n l := by
  ext u v
  change (u ≠ v ∧ ∃ k < _, _) ↔ (u ≠ v ∧ ∃ k < _, _)
  rw [getD_take_eq l (2 + 2 * l.getD 1 0) 1 (by omega)]
  apply and_congr_right
  intro _
  constructor
  · rintro ⟨k, hk, hp⟩
    refine ⟨k, hk, ?_⟩
    simpa only [getD_take_eq l (2 + 2 * l.getD 1 0) (2 + 2 * k) (by omega),
      getD_take_eq l (2 + 2 * l.getD 1 0) (2 + 2 * k + 1) (by omega)] using hp
  · rintro ⟨k, hk, hp⟩
    refine ⟨k, hk, ?_⟩
    simpa only [getD_take_eq l (2 + 2 * l.getD 1 0) (2 + 2 * k) (by omega),
      getD_take_eq l (2 + 2 * l.getD 1 0) (2 + 2 * k + 1) (by omega)] using hp

private theorem decodedCore_eq (x : Alg81Input) (words : List ℕ) :
    ({ Z := (decAlg86SubgraphWords x.n words).1.1
       C := (decAlg86SubgraphWords x.n words).1.2 } : Alg83Output x) = decAlg83Out x words := by
  have hdrop : (words.drop x.n).getD 1 0 = words.getD (x.n + 1) 0 := by
    simp only [List.getD_eq_getElem?_getD, List.getElem?_drop]
  change ({ Z := finsetOfBitList x.n (words.take x.n)
            C := graphOfFlatEdges x.n ((words.drop x.n).take (2 + 2 * words.getD (x.n + 1) 0)) } : Alg83Output x) =
    ({ Z := finsetOfBitList x.n (words.take x.n), C := graphOfFlatEdges x.n (words.drop x.n) } : Alg83Output x)
  rw [← hdrop, graphOfFlatEdges_take_header]

/-- A division returned by `decAlg86Out` has precisely the core read from the
output tail, even when the cross decoder failed before taking this branch. -/
theorem case3Alg86Division_core (x : Alg81Input) (out : List ℕ)
    (d : Alg86DivisionOutput x) (hdec : decAlg86Out x out = Sum.inr d) :
    d.core = decAlg83Out x out.tail := by
  unfold decAlg86Out at hdec
  split_ifs at hdec with htag
  · cases hc : decAlg81Out x out with
    | none =>
      simp only [hc] at hdec
      exact (congrArg Alg86DivisionOutput.core (Sum.inr.inj hdec)).symm.trans (decodedCore_eq x out.tail)
    | some c =>
      simp only [hc] at hdec
      cases hdec
  · exact (congrArg Alg86DivisionOutput.core (Sum.inr.inj hdec)).symm.trans (decodedCore_eq x out.tail)

/-- The normalized words are the actual returned division's core bitset. -/
theorem case3CoreBitList_eq_division (x : Alg81Input) (out : List ℕ)
    (d : Alg86DivisionOutput x) (hdec : decAlg86Out x out = Sum.inr d) :
    case3CoreBitList x.n out = bitSetList d.core.Z := by
  rw [case3Alg86Division_core x out d hdec]
  exact case3CoreBitList_eq_bitSetList x.n out

end GraphMinor.Compute
