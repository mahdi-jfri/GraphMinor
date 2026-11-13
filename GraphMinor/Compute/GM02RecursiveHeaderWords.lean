module

public import GraphMinor.Compute.GM02RecursiveInstanceWords

/-!
# Word-sized saved-parent headers

The plain input length, side lengths, phase tag, scheme code, answer
bits, and catalogue form the eight saved header words. The root word
bound covers each one, including every scheme code in the fixed range.
-/

public section
namespace GraphMinor.Compute

/-- Every header of a bounded recursive parent fits the fixed root word size. -/
theorem gm02RecursiveHeader_all_lt (q n w : ℕ) (x : GM02SimpleTerminatedInput)
    (L R : Finset (Fin x.n)) (mode code aggregate leftAnswer catalogue : ℕ)
    (hx : x.n ≤ n) (hw : wordSize (gm02RecursiveWordConstant q) n ≤ w)
    (hm : mode ≤ 3) (hc : code < gm02RecursiveCodeBound q)
    (ha : aggregate ≤ 1) (hl : leftAnswer ≤ 1)
    (hcat : catalogue < 2 ^ gm02RecursiveCodeBound q) :
    ∀ v ∈ gm02SavedFrameHeader x.enc (bitSetList L) (bitSetList R)
      mode code aggregate leftAnswer catalogue, v < 2 ^ w := by
  obtain ⟨h4, _, _, _, hK, _, hcodes, _⟩ := gm02Recursive_fixed_wordBounds q n w hw
  obtain ⟨hn, hlen, _⟩ := gm02Recursive_instance_wordBounds q n w x hx hw
  intro v hv
  simp only [gm02SavedFrameHeader, length_bitSetList, List.mem_cons,
    List.not_mem_nil, or_false] at hv
  rcases hv with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact hlen
  · exact hn
  · exact hn
  · omega
  · omega
  · omega
  · omega
  · exact hcat.trans_le hcodes

end GraphMinor.Compute
