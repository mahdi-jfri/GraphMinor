module

public import GraphMinor.Surface.Dihedral
import Mathlib.Data.Set.Card

/-!
# Counting the ends of cut vertex sectors

The side ends at a surface vertex form one orbit of two involutions.
Cutting replaces some crossings by fixed points. If at least one crossing
is cut, every resulting sector has a fixed end, and each sector has exactly
two fixed ends. This is the local counting step for branch vertices in
the Euler calculation of VIII (18.2).
-/

public section

namespace GraphMinor.GM08

open Set Function Relation GraphMinor.Surface

/-- Every sector obtained by cutting links in one vertex orbit contains
an end of a cut link. This is the reachability part of the vertex count
in VIII (18.2), page 286. -/
theorem exists_fixed_end_in_cut_orbit {G : Type*} {τ π σ : G → G}
    (hτ : Involutive τ) (hπ : Involutive π) (hσ : Involutive σ)
    (hs : ∀ a, σ a = a ∨ σ a = π a) {c g : G} (hc : σ c = c)
    (hg : TwoOrb τ π c g) : ∃ z, σ z = z ∧ TwoOrb τ σ g z := by
  let P : G → Prop := fun a => ∃ z, σ z = z ∧ TwoOrb τ σ a z
  have ht : ∀ a, P a → P (τ a) := by
    rintro a ⟨z, hz, haz⟩
    exact ⟨z, hz, EqvGen.trans _ _ _ (TwoOrb.left τ σ a).symm haz⟩
  have hp : ∀ a, P a → P (π a) := by
    rintro a ⟨z, hz, haz⟩
    rcases hs a with hfix | hcross
    · have hfix' : σ (π a) = π a := by
        rcases hs (π a) with hh | hh
        · exact hh
        · rw [hπ a] at hh
          have heq : π a = a := (hσ (π a)).symm.trans ((congrArg σ hh).trans hfix)
          rw [heq, hfix]
      exact ⟨π a, hfix', .refl _⟩
    · refine ⟨z, hz, ?_⟩
      have hreach : TwoOrb τ σ a (π a) := hcross ▸ TwoOrb.right τ σ a
      exact EqvGen.trans _ _ _ hreach.symm haz
  have hpres : ∀ a b, TwoOrb τ π a b → (P a ↔ P b) := by
    intro a b hab
    induction hab with
    | rel a b h =>
      rcases h with rfl | rfl
      · exact ⟨ht a, fun hh => by simpa only [hτ a] using ht (τ a) hh⟩
      · exact ⟨hp a, fun hh => by simpa only [hπ a] using hp (π a) hh⟩
    | refl a => exact Iff.rfl
    | symm a b _ ih => exact ih.symm
    | trans a b d _ _ ih₁ ih₂ => exact ih₁.trans ih₂
  exact (hpres c g hg).mp ⟨c, hc, .refl _⟩

/-- Each sector at a cut vertex has exactly two cut ends. Combined with
the count of cut side ends, this gives the fibre count needed in the
proof of VIII (18.2), page 286. -/
theorem cut_orbit_fixed_ends_ncard {G : Type*} [Finite G] {τ π σ : G → G}
    (hτ : Involutive τ) (hπ : Involutive π) (hσ : Involutive σ)
    (hfree : ∀ a, τ a ≠ a) (hs : ∀ a, σ a = a ∨ σ a = π a)
    {c g : G} (hc : σ c = c) (hg : TwoOrb τ π c g) :
    {z | TwoOrb τ σ g z ∧ σ z = z}.ncard = 2 := by
  obtain ⟨x, hx, hgx⟩ := exists_fixed_end_in_cut_orbit hτ hπ hσ hs hc hg
  obtain ⟨y, hyx, hy, hxy, hends⟩ := exists_other_end hτ hσ hfree hx
  have heq : {z | TwoOrb τ σ g z ∧ σ z = z} = {x, y} := by
    ext z
    constructor
    · rintro ⟨hgz, hz⟩
      exact hends z (EqvGen.trans _ _ _ hgx.symm hgz) hz
    · rintro (rfl | rfl)
      · exact ⟨hgx, hx⟩
      · exact ⟨EqvGen.trans _ _ _ hgx hxy, hy⟩
  rw [heq, ncard_pair hyx.symm]

end GraphMinor.GM08
