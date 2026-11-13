module

public import GraphMinor.Compute.GM02SeparatorCodes

/-!
# Integer codes for vertex injections

For II (4.7), pages 319–320, use one base digit for each fixed pattern
vertex. The host vertex count is the sentinel, so the base remains
positive even on an empty host. A valid code has no sentinel and no
repeated digit. Every injection occurs below the fixed power of the base.
-/

@[expose] public section
namespace GraphMinor.Compute

/-- The raw vertex assignment decoded from one candidate integer. -/
def gm02InjectionDigit (n p code : ℕ) (i : Fin p) : ℕ :=
  gm02SeparatorDigit n code i.val

/-- Valid injection codes avoid the sentinel and repeat no host vertex. -/
def gm02InjectionCodeValid (n p code : ℕ) : Prop :=
  (∀ i : Fin p, gm02InjectionDigit n p code i < n) ∧
    Function.Injective (gm02InjectionDigit n p code)

/-- A valid code supplies the actual injection used by the labelled test. -/
def gm02InjectionOfCode (n p code : ℕ) (h : gm02InjectionCodeValid n p code) :
    Fin p ↪ Fin n where
  toFun i := ⟨gm02InjectionDigit n p code i, h.1 i⟩
  inj' _ _ he := h.2 (congrArg Fin.val he)

/-- Every vertex injection is represented by a valid code in the fixed polynomial range. -/
theorem exists_gm02InjectionCode (n p : ℕ) (f : Fin p ↪ Fin n) :
    ∃ code < (n + 1) ^ p, ∃ h : gm02InjectionCodeValid n p code,
      gm02InjectionOfCode n p code h = f := by
  let digits : Fin p → ℕ := fun i => (f i).val
  have hd : ∀ i, digits i ≤ n := fun i => (f i).isLt.le
  let code := gm02SeparatorCode n digits
  have he : gm02InjectionDigit n p code = digits := by
    funext i
    exact gm02SeparatorDigit_code digits hd i
  have hv : gm02InjectionCodeValid n p code := by
    constructor
    · intro i
      rw [he]
      exact (f i).isLt
    · rw [he]
      intro a b hab
      exact f.injective (Fin.ext hab)
  refine ⟨code, gm02SeparatorCode_lt digits hd, hv, ?_⟩
  apply Function.Embedding.ext
  intro i
  apply Fin.ext
  exact congrFun he i

end GraphMinor.Compute
