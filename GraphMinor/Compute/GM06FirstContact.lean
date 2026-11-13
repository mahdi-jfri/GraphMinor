module

public import GraphMinor.Compute.Basic

/-!
# First contact in a finite face walk

Section 15 of our proof of VI (5.7) (outlined in `GraphMinor/GM06/Alg57Algorithm.lean`) traces a
face until the head of a dart first meets a specified set of vertices.
The returned darts are a prefix, including the first contact dart.
Every earlier dart has its head outside the set. The Boolean records
whether a contact was found, including when the input walk is empty.
-/

@[expose] public section
namespace GraphMinor.Compute

/-- Scan until the first marked item, retaining that item. -/
def gm06FirstContact {α : Type*} (stop : α → Bool) : List α → List α × Bool
  | [] => ([], false)
  | d :: ds => if stop d then ([d], true)
      else let r := gm06FirstContact stop ds; (d :: r.1, r.2)

/-- The trace is a prefix of the supplied face walk. -/
theorem gm06FirstContact_prefix {α : Type*} (stop : α → Bool) (ds : List α) :
    (gm06FirstContact stop ds).1 <+: ds := by
  induction ds with
  | nil => exact List.prefix_refl _
  | cons d ds ih =>
    simp only [gm06FirstContact]
    split
    · exact ⟨ds, rfl⟩
    · obtain ⟨tail, ht⟩ := ih
      exact ⟨tail, by simp only [List.cons_append, ht]⟩

/-- A trace contains at most as many darts as the input. -/
theorem gm06FirstContact_length_le {α : Type*} (stop : α → Bool) (ds : List α) :
    (gm06FirstContact stop ds).1.length ≤ ds.length :=
  (gm06FirstContact_prefix stop ds).length_le

/-- Failure to find a contact means that the complete input was traced. -/
theorem gm06FirstContact_eq_self_of_false {α : Type*} (stop : α → Bool) (ds : List α)
    (h : (gm06FirstContact stop ds).2 = false) :
    (gm06FirstContact stop ds).1 = ds := by
  induction ds with
  | nil => rfl
  | cons d ds ih =>
    cases hd : stop d with
    | true => simp [gm06FirstContact, hd] at h
    | false =>
      simp only [gm06FirstContact, hd, Bool.false_eq_true, ↓reduceIte] at h ⊢
      exact congrArg (List.cons d) (ih h)

/-- A failed scan is equivalent to the absence of a marked dart. -/
theorem gm06FirstContact_false_iff {α : Type*} (stop : α → Bool) (ds : List α) :
    (gm06FirstContact stop ds).2 = false ↔ ∀ d ∈ ds, stop d = false := by
  induction ds with
  | nil => simp [gm06FirstContact]
  | cons d ds ih =>
    by_cases hd : stop d = true
    · simp [gm06FirstContact, hd]
    · have hd' : stop d = false := Bool.eq_false_iff.mpr hd
      simp [gm06FirstContact, hd', ih]

/-- A successful trace ends with a marked dart. -/
theorem gm06FirstContact_last {α : Type*} (stop : α → Bool) (ds : List α)
    (h : (gm06FirstContact stop ds).2 = true) :
    ∃ d, (gm06FirstContact stop ds).1.getLast? = some d ∧ stop d = true := by
  induction ds with
  | nil => cases h
  | cons d ds ih =>
    by_cases hd : stop d = true
    · exact ⟨d, by simp [gm06FirstContact, hd], hd⟩
    · have hd' : stop d = false := Bool.eq_false_iff.mpr hd
      have ht : (gm06FirstContact stop ds).2 = true := by
        simpa only [gm06FirstContact, hd', Bool.false_eq_true, ↓reduceIte] using h
      obtain ⟨e, he, hs⟩ := ih ht
      refine ⟨e, ?_, hs⟩
      have hne : (gm06FirstContact stop ds).1 ≠ [] := by
        intro hz
        simp only [hz, List.getLast?_nil] at he
        cases he
      simp only [gm06FirstContact, hd', Bool.false_eq_true, ↓reduceIte]
      cases hl : (gm06FirstContact stop ds).1 with
      | nil => exact False.elim (hne hl)
      | cons a as => simpa only [hl, List.getLast?_cons_cons] using he

/-- No dart strictly before the last traced dart meets the target set. -/
theorem gm06FirstContact_internal {α : Type*} (stop : α → Bool) (ds : List α) :
    ∀ d ∈ (gm06FirstContact stop ds).1.dropLast, stop d = false := by
  induction ds with
  | nil => simp [gm06FirstContact]
  | cons d ds ih =>
    by_cases hd : stop d = true
    · simp [gm06FirstContact, hd]
    · have hd' : stop d = false := Bool.eq_false_iff.mpr hd
      simp only [gm06FirstContact, hd', Bool.false_eq_true, ↓reduceIte]
      cases ht : (gm06FirstContact stop ds).1 with
      | nil => simp
      | cons e es =>
        simp only [List.dropLast_cons_cons, List.mem_cons]
        intro x hx
        rcases hx with rfl | hx
        · exact hd'
        · exact ih x (by simpa only [ht] using hx)

/-- Extending an input prefix performs exactly one conditional append. -/
theorem gm06FirstContact_append_one {α : Type*} (stop : α → Bool) (ds : List α) (d : α) :
    gm06FirstContact stop (ds ++ [d]) =
      if (gm06FirstContact stop ds).2 then gm06FirstContact stop ds
      else ((gm06FirstContact stop ds).1 ++ [d], stop d) := by
  induction ds with
  | nil => cases hd : stop d <;> simp [gm06FirstContact, hd]
  | cons e es ih =>
    cases he : stop e <;> simp only [List.cons_append, gm06FirstContact, he, ↓reduceIte]
    rw [ih]
    cases ht : (gm06FirstContact stop es).2 <;> simp [ht]

/-- The mark used for terminal tracing: the head vertex of a dart
has a nonzero target bit. Missing entries are treated as zero. -/
def gm06TerminalContact (heads targets : List ℕ) (d : ℕ) : Bool :=
  targets[(heads[d]?.getD 0)]?.getD 0 != 0

/-- The exact first-contact dart list and success flag. The input
face row has already been rotated and its final cuff dart removed. -/
def gm06TerminalTrace (heads targets ds : List ℕ) : List ℕ × Bool :=
  gm06FirstContact (gm06TerminalContact heads targets) ds

/-- The terminal trace is a face-walk prefix with no internal head
in the target set. A nonempty trace starts with the same dart. -/
theorem gm06TerminalTrace_spec (heads targets ds : List ℕ) :
    (gm06TerminalTrace heads targets ds).1 <+: ds ∧
    (∀ d ∈ (gm06TerminalTrace heads targets ds).1.dropLast,
      targets[(heads[d]?.getD 0)]?.getD 0 = 0) ∧
    ((gm06TerminalTrace heads targets ds).2 = false ↔
      ∀ d ∈ ds, targets[(heads[d]?.getD 0)]?.getD 0 = 0) := by
  refine ⟨gm06FirstContact_prefix _ _, ?_, ?_⟩
  · intro d hd
    have hh := gm06FirstContact_internal (gm06TerminalContact heads targets) ds d hd
    simpa only [gm06TerminalContact, bne_eq_false_iff_eq] using hh
  · simpa only [gm06TerminalTrace, gm06TerminalContact, bne_eq_false_iff_eq] using
      gm06FirstContact_false_iff (gm06TerminalContact heads targets) ds

end GraphMinor.Compute
