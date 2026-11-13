module

public import GraphMinor.Compute.GM06Alg34InducedSizeBounds
public import GraphMinor.Compute.GM06Alg34DualPayloadSpace
import GraphMinor.Compute.GM06Alg34DualCuffProg
import Mathlib.Tactic.Ring

/-!
# Uniform section bounds through the reduction loop

Keep a fixed bound on the total number of vertices, edges and regions.
An induced region record scans at most that many labels. Dual region
and division records also have quadratic bounds in that fixed count.
Cuff and division sections cannot grow under deletion. Bounding the
three sections separately therefore prevents repeated deletions and
dual transitions from compounding the input-size bound.
-/

@[expose] public section
namespace GraphMinor.Compute

/-- A common bound for each variable-length section in a reduction state. -/
def gm06SectionCap (Q : ℕ) : ℕ := 10 * (Q + 2) ^ 2

private theorem region_budget (Q : ℕ) : Q * (Q + 2) ≤ gm06SectionCap Q := by
  unfold gm06SectionCap
  ring_nf
  omega

private theorem division_budget (Q : ℕ) : 1 + Q * (Q + 1) ≤ gm06SectionCap Q := by
  unfold gm06SectionCap
  ring_nf
  omega

private theorem cuff_budget (Q : ℕ) : Q + 2 ≤ gm06SectionCap Q := by
  unfold gm06SectionCap
  ring_nf
  omega

/-- Each newly computed induced region section has a uniform quadratic bound. -/
theorem gm06Induced_regionWords_le_cap (Q : ℕ) (x : GM06DrawingData)
    (hQ : x.cellCount ≤ Q) (vs : List (Fin x.n)) :
    (x.inducedData vs).regionWords.length ≤ gm06SectionCap Q := by
  have hc : x.n + x.ends.length ≤ Q := by
    unfold GM06DrawingData.cellCount at hQ
    omega
  exact (gm06Induced_regionWords_length_le x vs).trans
    ((Nat.mul_le_mul hQ (show 2 + x.n + x.ends.length ≤ Q + 2 by omega)).trans (region_budget Q))

/-- Dual region records have the same uniform quadratic bound. -/
theorem gm06Dual_regionWords_le_cap (Q : ℕ) (x : GM06DrawingData)
    (hQ : x.cellCount ≤ Q) (L : List (Fin x.n))
    (hR : 0 < x.regions.length) (g : Fin L.length → Fin x.regions.length) :
    (x.dualData L hR g).regionWords.length ≤ gm06SectionCap Q := by
  have hc : x.n ≤ Q ∧ x.regions.length + x.ends.length ≤ Q := by
    unfold GM06DrawingData.cellCount at hQ
    omega
  rw [← gm06DualRegionWords_eq x hR L g]
  have h := gm06DualRegionWords_length_le x (List.finRange x.n)
  simp only [List.length_finRange] at h
  exact h.trans ((Nat.mul_le_mul hc.1 (by omega : 2 + x.regions.length + x.ends.length ≤ Q + 2)).trans (region_budget Q))

/-- A dual cuff section fits the uniform bound when the original cuff has no repetitions. -/
theorem gm06Dual_cuffWords_le_cap (Q : ℕ) (x : GM06DrawingData)
    (hQ : x.cellCount ≤ Q) (L : List (Fin x.n)) (hLN : L.Nodup)
    (hR : 0 < x.regions.length) (g : Fin L.length → Fin x.regions.length) :
    (x.dualData L hR g).cuffWords.length ≤ gm06SectionCap Q := by
  have hk : L.length ≤ Q := by
    have hl := List.Nodup.length_le_card hLN
    simp only [Fintype.card_fin] at hl
    unfold GM06DrawingData.cellCount at hQ
    omega
  have heq : (x.dualData L hR g).cuffWords.length = 2 + L.length := by
    rw [gm06DualCuffWords_eq]
    simp only [List.length_cons, List.length_ofFn]
    omega
  rw [heq]
  exact (show 2 + L.length ≤ Q + 2 by omega).trans (cuff_budget Q)

/-- Canonical dual division sections have a uniform quadratic bound. -/
theorem gm06Dual_divisionWords_le_cap (Q : ℕ) (x : GM06DrawingData)
    (hQ : x.cellCount ≤ Q) (L : List (Fin x.n)) (hLN : L.Nodup)
    (hR : 0 < x.regions.length) (g : Fin L.length → Fin x.regions.length) :
    (x.dualData L hR g).divisionWords.length ≤ gm06SectionCap Q := by
  have hk : L.length ≤ Q := by
    have hl := List.Nodup.length_le_card hLN
    simp only [Fintype.card_fin] at hl
    unfold GM06DrawingData.cellCount at hQ
    omega
  rw [← gm06DualDivisionRecordWords_eq x L hR g, List.length_cons]
  have h := gm06DualDivisionRecordWords_length_le x L g (List.finRange L.length)
  simp only [List.length_finRange] at h
  have hp := Nat.mul_le_mul hk (show 1 + L.length ≤ Q + 1 by omega)
  exact (show (gm06DualDivisionRecordWords x L g (List.finRange L.length)).length + 1 ≤
    1 + Q * (Q + 1) by omega).trans (division_budget Q)

end GraphMinor.Compute
