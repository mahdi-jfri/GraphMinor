module

public import GraphMinor.GM08.Section11Side
public import GraphMinor.GM08.Section12LensesDisc
public import GraphMinor.GM08.Section12EdgeRest
import GraphMinor.GM08.Section9DiscContext

/-!
# Non-loop discs avoiding the foundation and loop discs

Protect all vertices, foundation discs, and the loop discs already
chosen. A remaining non-loop edge meets this protected set only at
its two ends. Apply the finite lens construction. Every other drawing
edge is in a foundation disc, in a loop disc, or in the finite line
family, so each new disc meets the drawing only in its own closed edge.
This verifies the non-loop thickening step on VIII, page 272.
-/

public section

namespace GraphMinor.GM08

open Set Surface

universe u

/-- Choose the non-loop edge discs after the loop discs have been
chosen. This is the remaining geometric step in the derived portrait
construction used in VIII, Section 12. -/
theorem exists_nonloop_disc_family {S : Type u} [TopologicalSpace S]
    (hS : IsClosedDisc (univ : Set S)) (D : Drawing S) (hp : D.IsProper)
    {t : ℕ} {F : Fin t → Set S} (hF : IsFoundation D univ F)
    (B : {e : Set S // e ∈ ringEdges D F ∧ D.IsLoop e} → Set S)
    (hB : ∀ i, IsClosedDisc (B i) ∧ discBd (B i) = closure i.1 ∧
      B i ∩ D.U = closure i.1) :
    ∃ A : {e : Set S // e ∈ ringEdges D F ∧ ¬ D.IsLoop e} → Set S,
      (∀ i, IsClosedDisc (A i) ∧ closure i.1 ⊆ A i ∧
        A i ∩ D.U = closure i.1 ∧
        (∀ j, A i ∩ (F j ∪ insideSet (F j)) ⊆ closure i.1) ∧
        A i ∩ D.V ⊆ discBd (A i) ∧ A i ∩ bd S ⊆ D.V ∧
        ∀ j, A i ∩ B j ⊆ closure i.1 ∩ closure j.1) ∧
      ∀ i j, i ≠ j → A i ∩ A j ⊆ closure i.1 ∩ closure j.1 := by
  classical
  have : T2Space S := (isSurface_of_closedDisc_univ hS).2.1
  let L := {e : Set S // e ∈ ringEdges D F ∧ D.IsLoop e}
  let Q := {e : Set S // e ∈ ringEdges D F ∧ ¬ D.IsLoop e}
  have : Finite L := (D.finite_edges.subset (fun _ he => he.1.1)).to_subtype
  have : Finite Q := (D.finite_edges.subset (fun _ he => he.1.1)).to_subtype
  have hex : ∀ i : Q, ∃ a b, a ≠ b ∧ closure i.1 ∩ D.V = {a, b} ∧
      IsLineWithEnds (closure i.1) a b := fun i =>
    exists_line_ends_of_not_loop i.2.1.1 i.2.2
  choose a b hab hcap hline using hex
  let Z := (D.V ∪ ⋃ j, F j ∪ insideSet (F j)) ∪ ⋃ i : L, B i
  have hZ : IsClosed Z := (D.finite_V.isClosed.union
    (isClosed_iUnion_of_finite fun j => isClosed_ring hS (hF.isOArc j))).union
    (isClosed_iUnion_of_finite fun i => (hB i).1.isClosed)
  have hends : ∀ i : Q, ({a i, b i} : Set S) ⊆ closure i.1 :=
    fun i => insert_subset (hline i).left_mem (singleton_subset_iff.mpr (hline i).right_mem)
  have hLineZ : ∀ i : Q, closure i.1 ∩ Z ⊆ {a i, b i} := by
    rintro i x ⟨hx, (hxV | hxF) | hxB⟩
    · exact hcap i ▸ And.intro hx hxV
    · obtain ⟨j, hxj⟩ := mem_iUnion.mp hxF
      have hxRing : x ∈ F j := hxj.resolve_right
        (disjoint_left.mp (hF.closure_disjoint_inside hS i.2.1 j) hx)
      have hxV := hF.isNormal j ⟨hxRing, D.closure_subset_U i.2.1.1 hx⟩
      exact hcap i ▸ And.intro hx hxV
    · obtain ⟨j, hxj⟩ := mem_iUnion.mp hxB
      have hxjcl : x ∈ closure j.1 := (hB j).2.2 ▸
        And.intro hxj (D.closure_subset_U i.2.1.1 hx)
      have hij : i.1 ≠ j.1 := fun h => i.2.2 (h.symm ▸ j.2.2)
      exact hcap i ▸ And.intro hx
        (closure_edges_inter_subset_vertices D i.2.1.1 j.2.1.1 hij ⟨hx, hxjcl⟩)
  have hLineBd : ∀ i : Q, closure i.1 ∩ bd S ⊆ {a i, b i} := by
    intro i x hx
    exact hcap i ▸ And.intro hx.1 (hp ⟨hx.2, D.closure_subset_U i.2.1.1 hx.1⟩)
  have hLines : ∀ i j : Q, i ≠ j → closure i.1 ∩ closure j.1 ⊆
      {a i, b i} ∩ {a j, b j} := by
    intro i j hij x hx
    have hxV := closure_edges_inter_subset_vertices D i.2.1.1 j.2.1.1
      (fun h => hij (Subtype.ext h)) hx
    exact ⟨hcap i ▸ And.intro hx.1 hxV, hcap j ▸ And.intro hx.2 hxV⟩
  obtain ⟨A, hA, hAA⟩ := exists_edge_lens_family_in_disc hS
    (fun i : Q => closure i.1) a b hline hab hZ hLineZ hLineBd hLines
  have hAZ : ∀ i : Q, A i ∩ Z ⊆ closure i.1 := fun i x hx => hends i ((hA i).2.2.1 hx)
  have hAloop : ∀ i : Q, ∀ j : L, A i ∩ B j ⊆ closure i.1 ∩ closure j.1 := by
    intro i j x hx
    have hxe := hAZ i ⟨hx.1, .inr (mem_iUnion.mpr ⟨j, hx.2⟩)⟩
    exact ⟨hxe, (hB j).2.2 ▸ And.intro hx.2 (D.closure_subset_U i.2.1.1 hxe)⟩
  have hAU : ∀ i : Q, A i ∩ D.U = closure i.1 := by
    intro i
    apply Subset.antisymm
    · rintro x ⟨hxA, hxU⟩
      by_cases hxV : x ∈ D.V
      · exact hAZ i ⟨hxA, .inl (.inl hxV)⟩
      · obtain ⟨e, he, hxe⟩ := D.exists_edge_of_mem hxU hxV
        by_cases hei : e = i.1
        · exact hei ▸ subset_closure hxe
        · rcases mem_ringEdges_or_inside (F := F) he with heR | ⟨j, hj⟩
          · by_cases heL : D.IsLoop e
            · let j : L := ⟨e, heR, heL⟩
              have hxB : x ∈ B j := discBd_subset _ ((hB j).2.1.symm ▸ subset_closure hxe)
              exact (hAloop i j ⟨hxA, hxB⟩).1
            · let j : Q := ⟨e, heR, heL⟩
              have hji : j ≠ i := fun h => hei (congrArg Subtype.val h)
              exact ((hA i).2.2.2.2.2.2 j hji ⟨hxA, subset_closure hxe⟩).1
          · exact hAZ i ⟨hxA, .inl (.inr (mem_iUnion.mpr ⟨j, .inr (hj hxe)⟩))⟩
    · intro x hx
      exact ⟨(hA i).2.1 hx, D.closure_subset_U i.2.1.1 hx⟩
  refine ⟨A, ?_, hAA⟩
  intro i
  refine ⟨(hA i).1, (hA i).2.1, hAU i, ?_, ?_, ?_, hAloop i⟩
  · intro j x hx
    exact hAZ i ⟨hx.1, .inl (.inr (mem_iUnion.mpr ⟨j, hx.2⟩))⟩
  · intro x hx
    have hxEnd := (hA i).2.2.1 ⟨hx.1, .inl (.inl hx.2)⟩
    rcases hxEnd with h | h
    · exact h.symm ▸ (hA i).2.2.2.1
    · exact h.symm ▸ (hA i).2.2.2.2.1
  · intro x hx
    have hxEnd := (hA i).2.2.2.2.2.1 hx
    exact (show {a i, b i} ⊆ D.V from fun y hy =>
      (show y ∈ closure i.1 ∩ D.V from (hcap i).symm ▸ hy).2) hxEnd

end GraphMinor.GM08
