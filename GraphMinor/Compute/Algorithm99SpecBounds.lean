module

public import GraphMinor.Compute.Algorithm99SpecOut
import GraphMinor.Compute.Algorithm94Init

/-!
# Bounds on the non-decomposition outputs of Algorithm (9.9)

A model has one bit per vertex in each branch set. The other output has one
vertex bitset and the bounded case-three block. These facts bound the full
output length and every word before the output is split into caller arrays.
-/

public section
namespace GraphMinor.Compute

/-- The two non-decomposition output forms have linear length and valid words. -/
theorem alg99SpecOut_bounds {pp h ω C_blk w m : ℕ} (G : MultiDigraph m)
    (Z : Finset (Fin m)) (out : List ℕ) (hw : 3 < 2 ^ w)
    (hout : (∃ a2, out = 1 :: a2 ∧ Alg99SpecOutII pp G Z a2) ∨
      (∃ a2 a3, out = 2 :: (a2 ++ a3) ∧ a2.length = m ∧
        Alg99SpecOutIII pp h ω C_blk w G Z a2 a3)) :
    out.length ≤ (pp + C_blk + 3) * (m + (G.deleteVertices Z).numEdges + 1) ∧
      (∀ v ∈ out, v < 2 ^ w) := by
  rcases hout with ⟨a2, rfl, X, rfl, _⟩ | ⟨a2, a3, rfl, ha2, hIII⟩
  · constructor
    · rw [List.length_cons, length_encBitSetsUpTo X pp le_rfl]
      nlinarith
    · intro v hv
      rcases List.mem_cons.1 hv with rfl | hv
      · omega
      · exact all_lt_encBitSetsUpTo X (by omega) pp le_rfl v hv
  · obtain ⟨X, block, rfl, rfl, hlen, hwords, _⟩ := hIII
    constructor
    · simp only [List.length_cons, List.length_append, length_bitSetList]
      nlinarith
    · intro v hv
      rcases List.mem_cons.1 hv with rfl | hv
      · omega
      · rcases List.mem_append.1 hv with hv | hv
        · exact all_lt_bitSetList X (by omega) v hv
        · exact hwords v hv

end GraphMinor.Compute
