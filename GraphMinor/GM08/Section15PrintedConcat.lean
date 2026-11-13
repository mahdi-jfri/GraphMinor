module

public import GraphMinor.GM08.Section15Printed

/-!
# Graph Minors VIII, (15.2) with the printed width

The width of a tubular graft on page 280 is the maximum width of its framings,
where the width of a tube uses exactly the two printed exceptions. This file
defines that width, `tubularPrintedWidth`, and the class $\mathcal{G}(t, u)$ of
the proof of (15.2) with it.

The proof of (15.2) on page 281 is an induction that applies (15.1) once for
each width. We run that induction with (15.1) for the side-qualified width
(`GM08.theorem_15_1`), see `GM08.theorem_15_2_sideQualified`. A tube of
side-qualified width at least $r$ has printed width at least $r$
(`GM08.Tube.width_le_printedWidth`), so each piece of that concatenation is a
tubular graft of printed width at least $r$. This gives (15.2) as printed.
-/

@[expose] public section

namespace GraphMinor.GM08

open Set

universe u v w

/-- The *width* of a tubular graft with the printed tube width: the maximum
printed width of all its framings.
Graph Minors VIII, Section 15, page 280: "If $(G, T)$ is a tubular graft, its
*width* is the maximum width of all its framings". -/
noncomputable def tubularPrintedWidth {α : Type u} {β : Type v} (X : Graft α β) : ℕ∞ :=
  sSup {w₀ : ℕ∞ | ∃ (S : Type) (_ : TopologicalSpace S) (τ : Tube S),
    τ.IsFraming X ∧ τ.printedWidth = w₀}

/-- The class $\mathcal{G}(t, u)$ of all tubular grafts of (printed) width
$\ge t$ and index $\le u$.
Graph Minors VIII, proof of (15.2), page 281: "Let $\mathcal{G}(t, u)$ be the
class of all tubular grafts of width $\ge t$ and index $\le u$." -/
def printedTubularClass {α : Type u} {β : Type v} (t k : ℕ) : Set (Graft α β) :=
  {X : Graft α β | IsTubularGraft X ∧ (t : ℕ∞) ≤ tubularPrintedWidth X ∧ X.index ≤ k}

/-- The side-qualified width of a tubular graft is at most its printed width,
since this holds for each framing. -/
theorem tubularWidth_le_tubularPrintedWidth {α : Type u} {β : Type v} (X : Graft α β) :
    tubularWidth X ≤ tubularPrintedWidth X := by
  refine sSup_le ?_
  rintro w₀ ⟨S, tS, τ, hfr, rfl⟩
  exact τ.width_le_printedWidth.trans (le_sSup ⟨S, tS, τ, hfr, rfl⟩)

/-- Every tubular graft of side-qualified width $\ge t$ has printed width $\ge t$. -/
theorem tubularClass_subset_printedTubularClass {α : Type u} {β : Type v} (t k : ℕ) :
    tubularClass (α := α) (β := β) t k ⊆ printedTubularClass t k := by
  rintro X ⟨htub, hw, hk⟩
  exact ⟨htub, hw.trans (tubularWidth_le_tubularPrintedWidth X), hk⟩

/-- Concatenations are monotone in the class of pieces. -/
theorem concatenationClass_mono {α : Type u} {β : Type v} {𝒜 ℬ : Set (Graft α β)}
    (h : 𝒜 ⊆ ℬ) : concatenationClass 𝒜 ⊆ concatenationClass ℬ := by
  rintro X ⟨t, hX⟩
  exact ⟨t, CKGraftClass_mono t h hX⟩

/-- **Graph Minors VIII, (15.2)** (page 281):
"(15.2) *Let $(G, T)$ be a tubular graft of index $\le k$ and let $r \ge 0$ be an
integer. Then $(G, T)$ is a concatenation of tubular grafts of width $\ge r$ and
index $\le k + r(r - 1)$.*"
The width is the printed one. The proof is the induction of page 281, run with
(15.1) for the side-qualified width (`GM08.theorem_15_2_sideQualified`). -/
theorem theorem_15_2_proof {α : Type u} {β : Type v} {X : Graft α β} {k : ℕ} (r : ℕ)
    (hX : IsTubularGraft X) (hk : X.index ≤ k) :
    X ∈ concatenationClass (printedTubularClass r (k + r * (r - 1))) :=
  concatenationClass_mono (tubularClass_subset_printedTubularClass _ _)
    (theorem_15_2_sideQualified r hX hk)

/-- When both bounding hoops of a tube carry at least `r` vertices, printed width at least `r`
gives side-qualified width at least `r`: an exempt hoop has the vertex set of `F₁` or of `F₂`,
so it has at least `r` vertices anyway. -/
theorem Tube.le_width_of_le_printedWidth {S : Type w} [TopologicalSpace S] (τ : Tube S) {r : ℕ}
    (hw : (r : ℕ∞) ≤ τ.printedWidth) (h₁ : r ≤ (τ.F₁ ∩ τ.Γ.V).ncard)
    (h₂ : r ≤ (τ.F₂ ∩ τ.Γ.V).ncard) : (r : ℕ∞) ≤ τ.width := by
  refine τ.le_width_iff.mpr fun F hF hN hsub => Or.inr ?_
  rcases τ.le_printedWidth_iff.mp hw F hF hN hsub with heq | heq | hle
  · rw [heq]; exact_mod_cast h₁
  · rw [heq]; exact_mod_cast h₂
  · exact hle

/-- (15.1) with the printed width, for a graft that has a framing of printed width at least `r`
whose two hoops each carry at least `r` vertices. The printed (15.1) in general is
`theorem_15_1_printed` (`Section15PrintedFinal.lean`). -/
theorem printed_train_of_framing_sides {α : Type u} {β : Type v} (r k : ℕ) {X : Graft α β}
    (hk : X.index ≤ k) {S : Type w} [TopologicalSpace S] {τ : Tube S} (hfr : τ.IsFraming X)
    (hw : (r : ℕ∞) ≤ τ.printedWidth) (h₁ : r ≤ (τ.F₁ ∩ τ.Γ.V).ncard)
    (h₂ : r ≤ (τ.F₂ ∩ τ.Γ.V).ncard) :
    X ∈ LKGraftClass r (printedTubularClass (r + 1) (k + 2 * r)) := by
  have hX : X ∈ tubularClass r k :=
    ⟨IsTubularGraft.of_framing hfr,
      (τ.le_width_of_le_printedWidth hw h₁ h₂).trans (le_tubularWidth_of_framing hfr), hk⟩
  exact LKGraftClass_mono r (tubularClass_subset_printedTubularClass (r + 1) (k + 2 * r))
    (theorem_15_1_side_qualified r k hX)

end GraphMinor.GM08
