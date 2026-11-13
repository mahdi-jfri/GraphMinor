module

public import GraphMinor.GM16.ThreeBoundaryPoints

/-!
# Drawing non-loop edges in a small society disc

For the small torsos in XVI (1.3), page 51, there are at most three
vertices on the disc boundary. We insert the edges one at a time.
After each chord, a smaller closed disc retains all the vertices and
meets the edges already drawn only on its boundary. The next chord
therefore meets those edges only at its ends.
-/

public section
namespace GraphMinor.GM16
open Set Surface
universe u w

/-- A finite family of non-loop edges on at most three prescribed
boundary vertices can be drawn without crossings in the disc. A remaining
disc retains all vertices and has no edge in its interior. -/
theorem exists_small_boundary_lines
    {S : Type w} [TopologicalSpace S] [T2Space S] {ι : Type u}
    {D P : Set S} (hD : IsClosedDisc D) (hP : P.Finite)
    (hcard : P.ncard ≤ 3) (hPb : P ⊆ discBd D)
    (a b : ι → S) (F : Set ι) (hFinite : F.Finite)
    (hEnds : ∀ i ∈ F, a i ∈ P ∧ b i ∈ P ∧ a i ≠ b i) :
    ∃ (J : ι → Set S) (D' : Set S),
      IsClosedDisc D' ∧ D' ⊆ D ∧ P ⊆ discBd D' ∧
      D' ∩ discBd D ⊆ discBd D' ∧
      (∀ i ∈ F, IsLineWithEnds (J i) (a i) (b i) ∧ J i ⊆ D ∧
        J i ∩ P = {a i, b i} ∧ J i ∩ discBd D = {a i, b i} ∧
        J i ∩ D' ⊆ discBd D') ∧
      F.Pairwise (fun i j => J i ∩ J j ⊆ P) := by
  classical
  revert hEnds
  induction F, hFinite using Set.Finite.induction_on with
  | empty =>
    intro _
    exact ⟨fun _ => ∅, D, hD, Subset.refl _, hPb, inter_subset_right,
      fun i hi => (notMem_empty i hi).elim, fun i hi => (notMem_empty i hi).elim⟩
  | @insert i F hi hFinite ih =>
    intro hEnds
    have hOldEnds := fun j hj => hEnds j (Or.inr hj)
    obtain ⟨J, D₁, hD₁, hD₁D, hPD₁, hActiveBd, hJ, hJJ⟩ := ih hOldEnds
    obtain ⟨hai, hbi, habi⟩ := hEnds i (Or.inl rfl)
    obtain ⟨L, D₂, hL, hLD₁, hLbd, hD₂, hD₂D₁, hPD₂, hLbd₂, hOldBd⟩ :=
      exists_chord_retaining_boundary_set hD₁ hP hcard hPD₁ hai hbi habi
    let J' : ι → Set S := fun j => if j = i then L else J j
    have hNewMeet : L ∩ P = {a i, b i} := by
      ext x
      constructor
      · rintro ⟨hxL, hxP⟩
        exact hLbd ▸ And.intro hxL (hPD₁ hxP)
      · intro hx
        have hBoth : x ∈ L ∩ discBd D₁ := hLbd.symm ▸ hx
        refine ⟨hBoth.1, ?_⟩
        rcases hx with rfl | rfl <;> assumption
    have hNewOld : ∀ j ∈ F, L ∩ J j ⊆ P := by
      intro j hj x ⟨hxL, hxJ⟩
      have hxBd := (hJ j hj).2.2.2.2 ⟨hxJ, hLD₁ hxL⟩
      have hxEnds : x ∈ ({a i, b i} : Set S) := hLbd ▸ And.intro hxL hxBd
      rcases hxEnds with rfl | rfl <;> assumption
    have hNewOuter : L ∩ discBd D = {a i, b i} := by
      ext x
      constructor
      · rintro ⟨hxL, hxD⟩
        exact hLbd ▸ And.intro hxL (hActiveBd ⟨hLD₁ hxL, hxD⟩)
      · intro hx
        have hxP : x ∈ P := by rcases hx with rfl | rfl <;> assumption
        exact ⟨(hNewMeet.symm ▸ hx).1, hPb hxP⟩
    refine ⟨J', D₂, hD₂, hD₂D₁.trans hD₁D, hPD₂,
      fun x hx => hOldBd ⟨hx.1, hActiveBd ⟨hD₂D₁ hx.1, hx.2⟩⟩, ?_, ?_⟩
    · intro j hj
      by_cases hji : j = i
      · subst j
        simp only [J', ite_eq_left]
        exact ⟨hL, hLD₁.trans hD₁D, hNewMeet, hNewOuter, fun x hx => hLbd₂ hx.1⟩
      · have hjF : j ∈ F := hj.resolve_left hji
        simp only [J', ite_eq_right hji]
        obtain ⟨hLine, hSub, hMeet, hOuter, hBd⟩ := hJ j hjF
        refine ⟨hLine, hSub, hMeet, hOuter, ?_⟩
        rintro x ⟨hxJ, hxD₂⟩
        exact hOldBd ⟨hxD₂, hBd ⟨hxJ, hD₂D₁ hxD₂⟩⟩
    · intro j hj k hk hjk
      by_cases hji : j = i <;> by_cases hki : k = i
      · exact (hjk (hji.trans hki.symm)).elim
      · subst j
        simp only [J', ite_eq_left, ite_eq_right hki]
        exact hNewOld k (hk.resolve_left hki)
      · subst k
        simp only [J', ite_eq_left, ite_eq_right hji]
        rw [inter_comm]
        exact hNewOld j (hj.resolve_left hji)
      · simp only [J', ite_eq_right hji, ite_eq_right hki]
        exact hJJ (hj.resolve_left hji) (hk.resolve_left hki) hjk

end GraphMinor.GM16
