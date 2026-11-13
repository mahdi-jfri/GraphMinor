module

public import GraphMinor.Compute.GM06Alg34GapSingletonData

/-!
# The internal single-cuff gap array

The disc program keeps its one supplied gap region group in a separate
array while replacing the base drawing array. Concatenating the finite
gap groups reads that array in the single-cuff case. Equal group lengths
and the single-cuff layout are preserved by every induced deletion.
-/

@[expose] public section
namespace GraphMinor.Compute.GM06GapInput

/-- Region-number words in the internal disc gap array. -/
def discGapWords (X : GM06GapInput) : List ℕ := X.gapRegions.flatten.map Fin.val

/-- A single supplied gap group has exactly its listed region words. -/
theorem discGapWords_singleton (X : GM06GapInput) (R : List (Fin X.drawing.regions.length))
    (hR : X.gapRegions = [R]) : X.discGapWords = R.map Fin.val := by
  simp only [discGapWords, hR, List.flatten_cons, List.flatten_nil, List.append_nil]

/-- Updating a single cuff and gap group gives precisely the retained gap words. -/
theorem inducedGapInput_discGapWords (X : GM06GapInput) (vs L : List (Fin X.drawing.n))
    (R : List (Fin X.drawing.regions.length)) (hL : X.drawing.cuffs = [L])
    (hR : X.gapRegions = [R]) :
    (X.inducedGapInput vs).discGapWords = (X.drawing.gapRegionsAfterDeletion vs L R).map Fin.val :=
  (X.inducedGapInput vs).discGapWords_singleton _ (X.inducedGapInput_disc vs L R hL hR)

/-- The single-cuff matching-length layout survives every induced update. -/
theorem inducedGapInput_disc_layout (X : GM06GapInput) (vs : List (Fin X.drawing.n))
    (hshape : ∃ L R, X.drawing.cuffs = [L] ∧ X.gapRegions = [R] ∧ R.length = L.length) :
    ∃ L R, (X.inducedGapInput vs).drawing.cuffs = [L] ∧
      (X.inducedGapInput vs).gapRegions = [R] ∧ R.length = L.length := by
  obtain ⟨L, R, hL, hR, hlen⟩ := hshape
  refine ⟨X.drawing.relabelVertexList vs L, X.drawing.gapRegionsAfterDeletion vs L R,
    ?_, X.inducedGapInput_disc vs L R hL hR, X.drawing.gapRegionsAfterDeletion_length vs L R hlen⟩
  change (X.drawing.cuffs.map (X.drawing.relabelVertexList vs)) = _
  rw [hL]
  rfl

end GraphMinor.Compute.GM06GapInput
