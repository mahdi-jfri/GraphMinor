module

public import GraphMinor.Compute.GM06Alg34UniformSize
public import GraphMinor.Compute.GM06Alg34QueueBounds

/-!
# Numerical bounds carried by the reduction loop

The loop uses fixed bounds on vertices plus regions, edges and cells.
It also carries the separate region, cuff and division word bounds.
These numerical conditions imply the uniform input size bound and
contain no geometric information or feasibility answer.
-/

@[expose] public section
namespace GraphMinor.Compute

/-- Numerical conditions at a state of the disc reduction loop. -/
def gm06LoopBounds (M E Q : ℕ) (X : GM06GapInput) : Prop :=
  X.drawing.n + X.drawing.regions.length ≤ M ∧ X.drawing.ends.length ≤ E ∧
    X.drawing.cellCount ≤ Q ∧ X.drawing.regionWords.length ≤ gm06SectionCap Q ∧
    X.drawing.cuffWords.length ≤ gm06SectionCap Q ∧ X.drawing.divisionWords.length ≤ gm06SectionCap Q

/-- The numerical loop conditions give the uniform input size bound. -/
theorem gm06LoopBounds_size {M E Q : ℕ} {X : GM06GapInput} (h : gm06LoopBounds M E Q X) :
    X.drawing.size ≤ 40 * (Q + 2) ^ 2 := by
  have hn : X.drawing.n ≤ Q := by
    have hc := h.2.2.1
    unfold GM06DrawingData.cellCount at hc
    omega
  have he : X.drawing.ends.length ≤ Q := by
    have hc := h.2.2.1
    unfold GM06DrawingData.cellCount at hc
    omega
  exact gm06Size_le_of_sections Q X.drawing hn he h.2.2.2.1 h.2.2.2.2.1 h.2.2.2.2.2

/-- The supplied original sections fit their fixed bounds. -/
theorem gm06LoopBounds_initial (X : GM06GapInput) (Q : ℕ) (hQ : X.drawing.size ≤ Q) :
    gm06LoopBounds (X.drawing.n + X.drawing.regions.length) X.drawing.ends.length Q X := by
  have hc := X.drawing.cellCount_le_size.trans hQ
  have hw := X.drawing.words_length
  have hs := X.drawing.words_length_le_size.trans hQ
  have hcap : Q ≤ gm06SectionCap Q := by unfold gm06SectionCap; ring_nf; omega
  exact ⟨le_rfl, le_rfl, hc,
    (show X.drawing.regionWords.length ≤ Q by omega).trans hcap,
    (show X.drawing.cuffWords.length ≤ Q by omega).trans hcap,
    (show X.drawing.divisionWords.length ≤ Q by omega).trans hcap⟩

end GraphMinor.Compute
