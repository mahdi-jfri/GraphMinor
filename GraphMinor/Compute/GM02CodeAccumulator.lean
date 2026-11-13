module

public import GraphMinor.Compute.GM02RecursiveAfterRight

/-!
# A feasibility accumulator over injective finite codes

Before code `i`, the accumulator records whether an earlier code has
both required properties. A missing code leaves that statement unchanged.
At a present code, the program's bit formula adds exactly the conjunction
of its two answers. Injectivity identifies the new code with its object.
-/

public section
namespace GraphMinor.Compute

/-- Skipping an absent code preserves the exact bounded existential represented by the accumulator. -/
theorem gm02CodeAccumulator_skip {α : Type*} (code : α → ℕ) (P : α → Prop) (i : ℕ)
    (hi : ¬∃ x, code x = i) :
    (∃ x, code x < i + 1 ∧ P x) ↔ ∃ x, code x < i ∧ P x := by
  constructor
  · rintro ⟨x, hx, hP⟩
    have hne : code x ≠ i := fun he => hi ⟨x, he⟩
    exact ⟨x, by omega, hP⟩
  · rintro ⟨x, hx, hP⟩
    exact ⟨x, by omega, hP⟩

/-- The program's bit update adds exactly the two properties of the current code. -/
theorem gm02CodeAccumulator_step {α : Type*} (code : α → ℕ) (hcode : Function.Injective code)
    (L R : α → Prop) (i a l r : ℕ) (current : α) (hcurrent : code current = i)
    (ha : a ≤ 1) (hl : l ≤ 1) (hr : r ≤ 1)
    (hacc : a = 1 ↔ ∃ x, code x < i ∧ L x ∧ R x)
    (hleft : l = 1 ↔ L current) (hright : r = 1 ↔ R current) :
    1 - (1 - a) * (1 - l * r) = 1 ↔ ∃ x, code x < i + 1 ∧ L x ∧ R x := by
  rw [gm02RecursiveAccumulator_eq_one ha hl hr, hacc, hleft, hright]
  constructor
  · rintro (⟨x, hx, hL, hR⟩ | ⟨hL, hR⟩)
    · exact ⟨x, by omega, hL, hR⟩
    · exact ⟨current, by omega, hL, hR⟩
  · rintro ⟨x, hx, hL, hR⟩
    by_cases hxi : code x < i
    · exact Or.inl ⟨x, hxi, hL, hR⟩
    · have he : code x = code current := by omega
      have hxcurrent : x = current := hcode he
      subst x
      exact Or.inr ⟨hL, hR⟩

end GraphMinor.Compute
