module

public import GraphMinor.GM08.Section16PrintedDefs
public import GraphMinor.GM08.Section15

/-!
# The printed no-inner-tube class

The printed width is at least the side-qualified width. Thus forbidding
a wide, long inner tube for the printed width also forbids it for the
side-qualified width. Apply the already proved decomposition to obtain
(15.3) for the printed class. Its conclusion uses only length and index.
-/

public section

namespace GraphMinor.GM08

open Set

universe u v w

/-- The printed no-inner-tube condition implies the side-qualified
condition: any forbidden side-qualified tube has printed width at
least as large. -/
theorem Tube.HasNoPrintedSubTubeOf.hasNoSubTubeOf {S : Type w} [TopologicalSpace S]
    {τ : Tube S} {r s : ℕ} (h : τ.HasNoPrintedSubTubeOf r s) :
    τ.HasNoSubTubeOf r s := by
  rintro ⟨A, B, hlam, hA, hB, hNA, hNB, hw, hl⟩
  exact h ⟨A, B, hlam, hA, hB, hNA, hNB,
    hw.trans (τ.subTube hlam hNA hNB).width_le_printedWidth, hl⟩

/-- The printed class `𝒜(k,r,s)` lies in the side-qualified class with
the same parameters. -/
theorem printedClassA_subset_classA {α : Type u} {β : Type v} (k r s : ℕ) :
    printedClassA (α := α) (β := β) k r s ⊆ classA k r s := by
  rintro X ⟨hk, S, tS, τ, hfr, hno⟩
  exact ⟨hk, S, tS, τ, hfr, hno.hasNoSubTubeOf⟩

/-- Graph Minors VIII, (15.3), pages 281–282, for the printed width:
every member of `𝒜(k,r,s)` is a concatenation of tubular grafts of
length less than `s` and index at most `k + r(r - 1)`. The decomposition
only needs the weaker side-qualified no-inner-tube condition. -/
theorem theorem_15_3_proof {α : Type u} {β : Type v} (k r s : ℕ) :
    printedClassA (α := α) (β := β) k r s ⊆
      concatenationClass
        {Y : Graft α β | IsTubularGraft Y ∧ tubularLength Y < s ∧ Y.index ≤ k + r * (r - 1)} :=
  (printedClassA_subset_classA k r s).trans (theorem_15_3_sideQualified k r s)

end GraphMinor.GM08
