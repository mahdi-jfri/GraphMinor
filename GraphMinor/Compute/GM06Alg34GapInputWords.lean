module

public import GraphMinor.Compute.GM06Alg34GapInput

/-!
# Reading all fields of the augmented drawing input

The base prefix and the group of gap region lists have exact round
trips. Equality of word arrays therefore forces equality of the base
drawing and every supplied gap region label, including their order.
-/

@[expose] public section
namespace GraphMinor.Compute.GM06GapInput

private theorem read_lists_words (Ls : List (List ℕ)) (tail : List ℕ) :
    GM06RawDrawingData.readLists Ls.length
      (Ls.flatMap GM06DrawingData.listWords ++ tail) = (Ls, tail) := by
  induction Ls with
  | nil => rfl
  | cons L Ls ih =>
    simp only [List.length_cons, List.flatMap_cons, List.append_assoc,
      GM06RawDrawingData.readLists]
    have hr : GM06RawDrawingData.readList
        (GM06DrawingData.listWords L ++ (Ls.flatMap GM06DrawingData.listWords ++ tail)) =
          (L, Ls.flatMap GM06DrawingData.listWords ++ tail) := by
      simp [GM06RawDrawingData.readList, GM06DrawingData.listWords]
    rw [hr]
    exact congrArg (fun q : List (List ℕ) × List ℕ => (L :: q.1, q.2)) ih

/-- The augmented array recovers the supplied gap region lists exactly. -/
theorem read_gaps (x : GM06GapInput) :
    (GM06RawDrawingData.readGroup (GM06RawDrawingData.readList x.words).2).1 = x.gapWords := by
  rw [x.read_gap_section]
  have hr := read_lists_words x.gapWords []
  simpa only [GM06DrawingData.listsWords, GM06RawDrawingData.readGroup,
    List.append_nil] using congrArg Prod.fst hr

private theorem fin_list_injective {n : ℕ} :
    Function.Injective (List.map (Fin.val : Fin n → ℕ)) := by
  intro A B h
  exact List.map_injective_iff.mpr Fin.val_injective h

private theorem fin_lists_injective {n : ℕ} :
    Function.Injective (List.map (List.map (Fin.val : Fin n → ℕ))) := by
  exact List.map_injective_iff.mpr fin_list_injective

/-- Equal augmented word arrays contain identical finite drawing and gap incidence data. -/
theorem words_injective : Function.Injective words := by
  rintro ⟨d, gs⟩ ⟨d', gs'⟩ hw
  have hd : d = d' := drawing_eq_of_words_eq hw
  subst d'
  have hgs : gs.map (List.map Fin.val) = gs'.map (List.map Fin.val) := by
    have hr := congrArg (fun w =>
      (GM06RawDrawingData.readGroup (GM06RawDrawingData.readList w).2).1) hw
    simpa only [read_gaps, gapWords] using hr
  have he := fin_lists_injective hgs
  subst gs'
  rfl

end GraphMinor.Compute.GM06GapInput
