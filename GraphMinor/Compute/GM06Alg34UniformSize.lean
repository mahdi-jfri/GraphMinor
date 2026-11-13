module

public import GraphMinor.Compute.GM06Alg34UniformSections
import Mathlib.Tactic.Ring

/-!
# A uniform quadratic input size bound

The three variable-length sections each have a fixed quadratic bound.
The remaining header and endpoint words use only a constant and twice
the edge count. Thus a fixed bound on vertices and edges bounds the
whole input size, independently of the number of previous reductions.
-/

public section
namespace GraphMinor.Compute

private theorem total_budget (Q : ℕ) :
    3 + 3 * Q + 3 * gm06SectionCap Q ≤ 40 * (Q + 2) ^ 2 := by
  unfold gm06SectionCap
  ring_nf
  omega

/-- Fixed section, vertex and edge bounds imply a uniform quadratic size bound. -/
theorem gm06Size_le_of_sections (Q : ℕ) (x : GM06DrawingData)
    (hn : x.n ≤ Q) (he : x.ends.length ≤ Q)
    (hr : x.regionWords.length ≤ gm06SectionCap Q)
    (hc : x.cuffWords.length ≤ gm06SectionCap Q)
    (hd : x.divisionWords.length ≤ gm06SectionCap Q) :
    x.size ≤ 40 * (Q + 2) ^ 2 := by
  have hwords := x.words_length
  change x.n + x.words.length ≤ _
  exact (show x.n + x.words.length ≤ 3 + 3 * Q + 3 * gm06SectionCap Q by omega).trans
    (total_budget Q)

/-- An induced restriction has the uniform size bound whenever its cuff
and division sections already have their fixed bounds. -/
theorem gm06Induced_size_le_uniform (Q : ℕ) (x : GM06DrawingData)
    (hQ : x.cellCount ≤ Q)
    (hc : x.cuffWords.length ≤ gm06SectionCap Q)
    (hd : x.divisionWords.length ≤ gm06SectionCap Q) (vs : List (Fin x.n)) :
    (x.inducedData vs).size ≤ 40 * (Q + 2) ^ 2 := by
  have hn : x.n ≤ Q := by unfold GM06DrawingData.cellCount at hQ; omega
  have he : x.ends.length ≤ Q := by unfold GM06DrawingData.cellCount at hQ; omega
  have hn' : (x.inducedData vs).n ≤ Q := by
    rw [x.inducedData_n]
    exact ((List.length_filter_le _ _).trans_eq List.length_finRange).trans hn
  have he' : (x.inducedData vs).ends.length ≤ Q := by
    rw [x.inducedData_ends_length]
    exact ((List.length_filter_le _ _).trans_eq List.length_finRange).trans he
  exact gm06Size_le_of_sections Q _ hn' he' (gm06Induced_regionWords_le_cap Q x hQ vs)
    ((gm06Induced_cuffWords_length_le x vs).trans hc)
    ((gm06Induced_divisionWords_length_le x vs).trans hd)

/-- A computed dual has the uniform size bound from the same fixed cell count. -/
theorem gm06Dual_size_le_uniform (Q : ℕ) (x : GM06DrawingData)
    (hQ : x.cellCount ≤ Q) (L : List (Fin x.n)) (hLN : L.Nodup)
    (hR : 0 < x.regions.length) (g : Fin L.length → Fin x.regions.length) :
    (x.dualData L hR g).size ≤ 40 * (Q + 2) ^ 2 := by
  have hn : (x.dualData L hR g).n ≤ Q := by
    change x.regions.length ≤ Q
    unfold GM06DrawingData.cellCount at hQ
    omega
  have he : (x.dualData L hR g).ends.length ≤ Q := by
    rw [x.dualData_edges_length]
    unfold GM06DrawingData.cellCount at hQ
    omega
  exact gm06Size_le_of_sections Q _ hn he (gm06Dual_regionWords_le_cap Q x hQ L hR g)
    (gm06Dual_cuffWords_le_cap Q x hQ L hLN hR g)
    (gm06Dual_divisionWords_le_cap Q x hQ L hLN hR g)

end GraphMinor.Compute
