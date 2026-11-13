module

public import GraphMinor.GM16.DiscChord
import GraphMinor.Surface.DiscArcs

/-!
# Keeping three boundary points when drawing an edge

The small society discs in XVI (1.3), page 51, have at most three
marked boundary points. Draw a chord between two of them. Of the two
closed discs it cuts off, one retains the third marked point on its
boundary. Repeating this draws parallel edges and the edges of a
triangle while keeping the marked vertices available on the boundary.
-/

public section
namespace GraphMinor.GM16
open Set Surface
universe w

/-- A chord can be drawn while retaining three prescribed boundary
points in a smaller closed disc. The new chord and any retained part
of the old boundary lie on the new boundary. -/
theorem exists_chord_retaining_three_points
    {S : Type w} [TopologicalSpace S] [T2Space S]
    {D : Set S} (hD : IsClosedDisc D) {a b c : S}
    (ha : a ∈ discBd D) (hb : b ∈ discBd D) (hc : c ∈ discBd D) (hab : a ≠ b) :
    ∃ F D' : Set S, IsLineWithEnds F a b ∧ F ⊆ D ∧
      F ∩ discBd D = {a, b} ∧ IsClosedDisc D' ∧ D' ⊆ D ∧
      a ∈ discBd D' ∧ b ∈ discBd D' ∧ c ∈ discBd D' ∧
      F ⊆ discBd D' ∧ D' ∩ discBd D ⊆ discBd D' := by
  obtain ⟨F, hF, hFD, hmeet⟩ := exists_disc_chord hD ha hb hab
  obtain ⟨A₁, A₂, D₁, D₂, _, hcomp, hD₁, hD₂, hun, hinter, hbd₁, hbd₂, _⟩ :=
    disc_iArc D F a b hD hFD hab hF hmeet
  have hF₁ : F ⊆ discBd D₁ := hbd₁ ▸ subset_union_right
  have hF₂ : F ⊆ discBd D₂ := hbd₂ ▸ subset_union_right
  have hD₁D : D₁ ⊆ D := hun ▸ subset_union_left
  have hD₂D : D₂ ⊆ D := hun ▸ subset_union_right
  have hCover : discBd D ⊆ discBd D₁ ∪ discBd D₂ := by
    intro x hx
    by_cases hxab : x ∈ ({a, b} : Set S)
    · exact Or.inl (hF₁ ((hmeet ▸ hxab).1))
    · have hMem : connectedComponentIn (discBd D \ {a, b}) x ∈
          componentsIn (discBd D \ {a, b}) := ⟨x, ⟨hx, hxab⟩, rfl⟩
      rw [hcomp] at hMem
      have hxComp := mem_connectedComponentIn (show x ∈ discBd D \ {a, b} from ⟨hx, hxab⟩)
      rcases hMem with hMem | hMem
      · left
        rw [hbd₁]
        exact Or.inl (hMem ▸ hxComp)
      · right
        rw [hbd₂]
        exact Or.inl ((mem_singleton_iff.mp hMem) ▸ hxComp)
  have hOld₁ : D₁ ∩ discBd D ⊆ discBd D₁ := by
    rintro x ⟨hxD, hxBd⟩
    rcases hCover hxBd with hx | hx
    · exact hx
    · have hxD₂ := discBd_subset D₂ hx
      exact hF₁ (hinter ▸ And.intro hxD hxD₂)
  have hOld₂ : D₂ ∩ discBd D ⊆ discBd D₂ := by
    rintro x ⟨hxD, hxBd⟩
    rcases hCover hxBd with hx | hx
    · have hxD₁ := discBd_subset D₁ hx
      exact hF₂ (hinter ▸ And.intro hxD₁ hxD)
    · exact hx
  have haF : a ∈ F := ((hmeet.symm ▸ (Or.inl rfl : a ∈ ({a, b} : Set S))) : a ∈ F ∩ discBd D).1
  have hbF : b ∈ F := ((hmeet.symm ▸ (Or.inr (mem_singleton b) : b ∈ ({a, b} : Set S))) : b ∈ F ∩ discBd D).1
  rcases hCover hc with hc₁ | hc₂
  · exact ⟨F, D₁, hF, hFD, hmeet, hD₁, hD₁D, hF₁ haF, hF₁ hbF, hc₁, hF₁, hOld₁⟩
  · exact ⟨F, D₂, hF, hFD, hmeet, hD₂, hD₂D, hF₂ haF, hF₂ hbF, hc₂, hF₂, hOld₂⟩

private theorem subset_triple_of_ncard_le_three {S : Type w} {P : Set S}
    (hP : P.Finite) (hcard : P.ncard ≤ 3) {a b : S}
    (ha : a ∈ P) (hb : b ∈ P) (hab : a ≠ b) :
    ∃ c ∈ P, P ⊆ {a, b, c} := by
  have hpair : ({a, b} : Set S) ⊆ P := by
    rintro x (rfl | rfl) <;> assumption
  have hdiff : (P \ {a, b}).ncard ≤ 1 := by
    rw [ncard_sdiff hpair ((finite_singleton b).insert a), ncard_pair hab]
    omega
  by_cases hne : (P \ {a, b}).Nonempty
  · obtain ⟨c, hc⟩ := hne
    refine ⟨c, hc.1, ?_⟩
    intro x hx
    by_cases hxab : x ∈ ({a, b} : Set S)
    · rcases hxab with rfl | rfl <;> simp
    · have hxc := (ncard_le_one (hP.subset sdiff_subset)).mp hdiff x ⟨hx, hxab⟩ c hc
      simp [hxc]
  · refine ⟨a, ha, ?_⟩
    intro x hx
    have hxab : x ∈ ({a, b} : Set S) := by
      by_contra hnot
      exact hne ⟨x, hx, hnot⟩
    rcases hxab with rfl | rfl <;> simp

/-- The small society boundary can be retained after drawing a chord
between any two of its vertices. -/
theorem exists_chord_retaining_boundary_set
    {S : Type w} [TopologicalSpace S] [T2Space S]
    {D P : Set S} (hD : IsClosedDisc D) (hP : P.Finite)
    (hcard : P.ncard ≤ 3) (hPb : P ⊆ discBd D)
    {a b : S} (ha : a ∈ P) (hb : b ∈ P) (hab : a ≠ b) :
    ∃ F D' : Set S, IsLineWithEnds F a b ∧ F ⊆ D ∧
      F ∩ discBd D = {a, b} ∧ IsClosedDisc D' ∧ D' ⊆ D ∧
      P ⊆ discBd D' ∧ F ⊆ discBd D' ∧ D' ∩ discBd D ⊆ discBd D' := by
  obtain ⟨c, hc, hsub⟩ := subset_triple_of_ncard_le_three hP hcard ha hb hab
  obtain ⟨F, D', hF, hFD, hmeet, hD', hD'D, ha', hb', hc', hFbd, hOld⟩ :=
    exists_chord_retaining_three_points hD (hPb ha) (hPb hb) (hPb hc) hab
  refine ⟨F, D', hF, hFD, hmeet, hD', hD'D, ?_, hFbd, hOld⟩
  intro x hx
  rcases hsub hx with rfl | rfl | rfl <;> assumption

end GraphMinor.GM16
