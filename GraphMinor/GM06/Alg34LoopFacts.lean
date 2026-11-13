module

public import GraphMinor.GM06.Alg34LoopInstance
public import GraphMinor.GM06.Alg34DiscArrayBounds
import GraphMinor.Compute.GM06Alg34DiscRep

/-!
# Finite preconditions supplied by intended loop instances

Unpack the existing disc-instance witness only in proofs. Its supplied
cuff is repetition-free, its gap list matches that cuff and its finite
division is valid. A non-null proper disc also has a region. These facts
supply the finite preconditions of the phase execution theorems.
-/

public section
namespace GraphMinor.Compute

open Set Surface GM06
universe u

/-- Intended loop instances have the complete finite one-cuff layout. -/
theorem gm06LoopInstance_layout {X : GM06GapInput} (hX : gm06LoopInstance.{u} X) :
    ∃ L R, X.drawing.cuffs = [L] ∧ X.gapRegions = [R] ∧ R.length = L.length ∧ L.Nodup := by
  obtain ⟨I, ⟨h⟩, _⟩ := hX
  exact h.disc_layout_nodup I.hDisc

/-- The interpreted division condition implies validity of the supplied finite division. -/
theorem gm06LoopInstance_division {X : GM06GapInput} (hX : gm06LoopInstance.{u} X) :
    IsDivision X.drawing.divisionSet := by
  obtain ⟨I, ⟨h⟩, _⟩ := hX
  exact h.drawing.division_isDivision I.hΔ

/-- The current gap array is no longer than the supplied vertex range. -/
theorem gm06LoopInstance_gap_length {X : GM06GapInput} (hX : gm06LoopInstance.{u} X) :
    X.discGapWords.length ≤ X.drawing.n := by
  obtain ⟨I, ⟨h⟩, _⟩ := hX
  exact h.discGapWords_length_le I.hDisc

/-- Non-null intended loop instances have a nonempty finite region range. -/
theorem gm06LoopInstance_regions_pos {X : GM06GapInput} (hX : gm06LoopInstance.{u} X)
    (hn : 0 < X.drawing.n) : 0 < X.drawing.regions.length := by
  obtain ⟨I, ⟨h⟩, _⟩ := hX
  exact h.drawing.regions_pos_of_vertices I.hDisc I.hProper hn

end GraphMinor.Compute
