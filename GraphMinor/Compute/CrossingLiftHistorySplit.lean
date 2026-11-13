module

public import GraphMinor.Crossing.DefsHistory

/-!
# Splitting a history before its last record

The lift program reads records backwards. Splitting a history at a list append identifies
the instance just before the last record, so lifting that record leaves the crossing pair
needed for the remaining prefix. This is a direct induction on the definition of history.
-/

public section

namespace GraphMinor.Compute.Crossing

open SimpleGraph GraphMinor.Crossing

/-- A history of two consecutive record lists has an intermediate instance. -/
theorem liftHistory_append_iff {V : Type*} [DecidableEq V]
    (rs ss : List (CrossRecord V)) (st st' : SimpleGraph V × Set V × List V) :
    IsHistory st (rs ++ ss) st' ↔
      ∃ mid, IsHistory st rs mid ∧ IsHistory mid ss st' := by
  induction rs generalizing st with
  | nil =>
    simp only [List.nil_append, IsHistory]
    constructor
    · intro h; exact ⟨st, rfl, h⟩
    · rintro ⟨mid, rfl, h⟩; exact h
  | cons r rs ih =>
    obtain ⟨G, S, D⟩ := st
    cases r with
    | repl r =>
      simp only [List.cons_append, IsHistory]
      rw [ih]
      constructor
      · rintro ⟨hg, hs, hv, mid, hr, hss⟩
        exact ⟨mid, ⟨hg, hs, hv, hr⟩, hss⟩
      · rintro ⟨mid, ⟨hg, hs, hv, hr⟩, hss⟩
        exact ⟨hg, hs, hv, mid, hr, hss⟩
    | contr r =>
      simp only [List.cons_append, IsHistory]
      rw [ih]
      constructor
      · rintro ⟨hg, hs, hd, hv, mid, hr, hss⟩
        exact ⟨mid, ⟨hg, hs, hd, hv, hr⟩, hss⟩
      · rintro ⟨mid, ⟨hg, hs, hd, hv, hr⟩, hss⟩
        exact ⟨hg, hs, hd, hv, mid, hr, hss⟩
    | del H T =>
      simp only [List.cons_append, IsHistory]
      rw [ih]
      constructor
      · rintro ⟨hg, hs, hv, hd, he, mid, hr, hss⟩
        exact ⟨mid, ⟨hg, hs, hv, hd, he, hr⟩, hss⟩
      · rintro ⟨mid, ⟨hg, hs, hv, hd, he, hr⟩, hss⟩
        exact ⟨hg, hs, hv, hd, he, mid, hr, hss⟩

/-- The last record of a nonempty history starts at the final instance of its prefix. -/
theorem liftHistory_snoc {V : Type*} [DecidableEq V]
    {rs : List (CrossRecord V)} {r : CrossRecord V}
    {st st' : SimpleGraph V × Set V × List V}
    (h : IsHistory st (rs ++ [r]) st') :
    ∃ mid, IsHistory st rs mid ∧ IsHistory mid [r] st' :=
  (liftHistory_append_iff rs [r] st st').mp h

end GraphMinor.Compute.Crossing
