module

public import GraphMinor.GM08.Section11Side
import GraphMinor.GM08.Section12LoopFamily
import GraphMinor.GM08.Section12NonloopFamily

/-!
# Thickening all edges outside the foundation

Use the empty region disc for each loop and a lens for each non-loop.
The lens construction protects every loop disc. Hence all the discs
meet the drawing, the foundation, and each other exactly as required
on VIII, page 272. These are the edge pieces of the derived portrait
used in Section 12.
-/

public section

namespace GraphMinor.GM08

open Set Surface

universe u

/-- Every cellular proper drawing with a foundation admits the edge
thickening of VIII, page 272. The extra boundary conditions verify that
the resulting union is a painting in the disc. -/
theorem exists_edge_thickening {S : Type u} [TopologicalSpace S]
    (hS : IsClosedDisc (univ : Set S)) (D : Drawing S)
    (hp : D.IsProper) (hc : IsCellularDrawing D)
    {t : ℕ} {F : Fin t → Set S} (hF : IsFoundation D univ F) :
    ∃ C : ringEdges D F → Set S,
      (∀ i, IsClosedDisc (C i) ∧ closure i.1 ⊆ C i ∧
        C i ∩ D.U = closure i.1 ∧
        (∀ j, C i ∩ (F j ∪ insideSet (F j)) ⊆ closure i.1) ∧
        C i ∩ D.V ⊆ discBd (C i) ∧ C i ∩ bd S ⊆ D.V) ∧
      ∀ i j, i ≠ j → C i ∩ C j ⊆ closure i.1 ∩ closure j.1 := by
  classical
  obtain ⟨B, hB, hBB⟩ := exists_loop_disc_family hS D hp hc hF
  have hB' : ∀ i, IsClosedDisc (B i) ∧ discBd (B i) = closure i.1 ∧
      B i ∩ D.U = closure i.1 := fun i =>
    ⟨(hB i).1, (hB i).2.1, (hB i).2.2.1⟩
  obtain ⟨A, hA, hAA⟩ := exists_nonloop_disc_family hS D hp hF B hB'
  let C : ringEdges D F → Set S := fun i =>
    if h : D.IsLoop i.1 then B ⟨i.1, i.2, h⟩ else A ⟨i.1, i.2, h⟩
  have hCB : ∀ (i : ringEdges D F) (h : D.IsLoop i.1), C i = B ⟨i.1, i.2, h⟩ := by
    intro i h
    simp only [C, dite_eq_left h]
  have hCA : ∀ (i : ringEdges D F) (h : ¬ D.IsLoop i.1), C i = A ⟨i.1, i.2, h⟩ := by
    intro i h
    simp only [C, dite_eq_right h]
  refine ⟨C, ?_, ?_⟩
  · intro i
    by_cases hi : D.IsLoop i.1
    · rw [hCB i hi]
      let j := (⟨i.1, i.2, hi⟩ : {e : Set S // e ∈ ringEdges D F ∧ D.IsLoop e})
      refine ⟨(hB j).1, ?_, (hB j).2.2.1, (hB j).2.2.2.1, ?_, (hB j).2.2.2.2⟩
      · rw [← (hB j).2.1]
        exact discBd_subset _
      · intro x hx
        rw [(hB j).2.1]
        exact (hB j).2.2.1 ▸ And.intro hx.1 (D.V_subset_U hx.2)
    · rw [hCA i hi]
      let j := (⟨i.1, i.2, hi⟩ : {e : Set S // e ∈ ringEdges D F ∧ ¬ D.IsLoop e})
      exact ⟨(hA j).1, (hA j).2.1, (hA j).2.2.1,
        (hA j).2.2.2.1, (hA j).2.2.2.2.1, (hA j).2.2.2.2.2.1⟩
  · intro i j hij
    have hij' : i.1 ≠ j.1 := fun h => hij (Subtype.ext h)
    by_cases hi : D.IsLoop i.1 <;> by_cases hj : D.IsLoop j.1
    · rw [hCB i hi, hCB j hj]
      exact hBB _ _ (fun h => hij' (congrArg
        (fun z : {e : Set S // e ∈ ringEdges D F ∧ D.IsLoop e} => z.1) h))
    · rw [hCB i hi, hCA j hj]
      intro x hx
      have hy := (hA ⟨j.1, j.2, hj⟩).2.2.2.2.2.2 ⟨i.1, i.2, hi⟩ ⟨hx.2, hx.1⟩
      exact ⟨hy.2, hy.1⟩
    · rw [hCA i hi, hCB j hj]
      exact (hA ⟨i.1, i.2, hi⟩).2.2.2.2.2.2 ⟨j.1, j.2, hj⟩
    · rw [hCA i hi, hCA j hj]
      exact hAA _ _ (fun h => hij' (congrArg
        (fun z : {e : Set S // e ∈ ringEdges D F ∧ ¬ D.IsLoop e} => z.1) h))

end GraphMinor.GM08
