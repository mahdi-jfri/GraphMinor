module

public import GraphMinor.Compute.CrossingLiftHistorySplit
public import GraphMinor.Compute.CrossingLiftCost
public import GraphMinor.Compute.CrossingLiftRead

/-!
# Data for one backward history iteration

The last record has a last encoding in the buffer. Lifting it and then lifting the prefix
composes to a lift through the whole history. The work count is additive, so each iteration
can charge its own encoded words and its own possible vertex-count work.
-/

public section

namespace GraphMinor.Compute.Crossing

open GraphMinor.Crossing

/-- Split the encoding list at the last encoded record. -/
theorem liftRecordEncoding_snoc {N : ℕ} {rs : List (CrossRecord (Fin N))}
    {r : CrossRecord (Fin N)} {ls : List (List ℕ)}
    (h : List.Forall₂ IsRecordEnc (rs ++ [r]) ls) :
    ∃ encs words, ls = encs ++ [words] ∧
      List.Forall₂ IsRecordEnc rs encs ∧ IsRecordEnc r words := by
  induction rs generalizing ls with
  | nil =>
    cases h with
    | cons hw ht =>
      cases ht
      exact ⟨[], _, rfl, .nil, hw⟩
  | cons x rs ih =>
    cases h with
    | cons hx ht =>
      obtain ⟨encs, words, rfl, hp, hw⟩ := ih ht
      exact ⟨_ :: encs, words, rfl, .cons hx hp, hw⟩

/-- Lifts compose in reverse record order, as required by the history definition. -/
theorem liftHistory_lift_append {V : Type*} [DecidableEq V]
    {rs ss : List (CrossRecord V)} {P Q R : List V × List V}
    (hss : IsLift ss P Q) (hrs : IsLift rs Q R) : IsLift (rs ++ ss) P R := by
  induction rs generalizing R with
  | nil => cases hrs; exact hss
  | cons r rs ih =>
    obtain ⟨M, hm, hr⟩ := hrs
    exact ⟨M, ih hm, hr⟩

/-- The count of replacements and contractions is additive over consecutive record lists. -/
theorem liftWorkCount_append {V : Type*} (rs ss : List (CrossRecord V)) :
    liftWorkCount (rs ++ ss) = liftWorkCount rs + liftWorkCount ss := by
  induction rs with
  | nil => simp [liftWorkCount]
  | cons r rs ih =>
    cases r <;> simp only [List.cons_append, liftWorkCount, ih] <;> omega

end GraphMinor.Compute.Crossing
