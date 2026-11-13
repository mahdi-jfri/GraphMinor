module

public import GraphMinor.GM08.Section12FoundationDiscs
public import GraphMinor.GM08.Section12Painting
public import GraphMinor.GM08.Section12EdgeRest

/-!
# The painting from a foundation and its edge discs

Combine the ring discs with the thickened remaining edges. Their
intersections are nodes because the remaining closed edges miss every
ring interior. Applying the disc painting construction gives the cells,
their closures, and the unchanged boundary vertices. This is the
painting assertion on VIII, page 272, used in Section 12.
-/

public section

namespace GraphMinor.GM08

open Set Surface

universe u

/-- Foundation discs and thickened remaining edges give the painting
of a derived portrait in VIII, Section 12. The sum index records which
cells receive smaller rooted graph labels and which receive `*`. -/
theorem exists_foundation_painting {S : Type u} [TopologicalSpace S]
    (hS : IsClosedDisc (univ : Set S)) (D : Drawing S)
    {t : ℕ} {F : Fin t → Set S} (hF : IsFoundation D univ F)
    (C : ringEdges D F → Set S)
    (hC : ∀ i, IsClosedDisc (C i) ∧ closure i.1 ⊆ C i ∧
      C i ∩ D.U = closure i.1 ∧
      (∀ j, C i ∩ (F j ∪ insideSet (F j)) ⊆ closure i.1) ∧
      C i ∩ D.V ⊆ discBd (C i) ∧ C i ∩ bd S ⊆ D.V)
    (hCC : ∀ i j, i ≠ j → C i ∩ C j ⊆ closure i.1 ∩ closure j.1) :
    let B : Fin t ⊕ ringEdges D F → Set S :=
      Sum.elim (fun i => F i ∪ insideSet (F i)) C
    ∃ P : PaintingInDisc S,
      P.N = ringNodes D F ∧ P.U = ringNodes D F ∪ ⋃ i, B i ∧
      P.cells = range (fun i => B i \ ringNodes D F) ∧
      (∀ i, closure (B i \ ringNodes D F) = B i) ∧
      Function.Injective (fun i => B i \ ringNodes D F) ∧
      P.U ∩ bd S = D.V ∩ bd S := by
  classical
  have : T2Space S := t2Space_of_univ hS
  have : Finite (ringEdges D F) := (D.finite_edges.subset (sep_subset _ _)).to_subtype
  let B : Fin t ⊕ ringEdges D F → Set S :=
    Sum.elim (fun i => F i ∪ insideSet (F i)) C
  have hB : ∀ i, IsClosedDisc (B i) := by
    intro i
    cases i with
    | inl i => exact (hF.ring_disc hS i).1
    | inr i => exact (hC i).1
  have hBN : ∀ i, B i ∩ ringNodes D F ⊆ discBd (B i) := by
    intro i
    cases i with
    | inl i =>
      change (F i ∪ insideSet (F i)) ∩ ringNodes D F ⊆
        discBd (F i ∪ insideSet (F i))
      rw [hF.ring_inter_nodes hS i, (hF.ring_disc hS i).2]
      exact inter_subset_right
    | inr i => exact fun x hx => (hC i).2.2.2.2.1 ⟨hx.1, hx.2.1⟩
  have hRE : ∀ i j, (F i ∪ insideSet (F i)) ∩ C j ⊆ ringNodes D F := by
    intro i j x hx
    have hxcl := (hC j).2.2.2.1 i ⟨hx.2, hx.1⟩
    have hxF : x ∈ F i := hx.1.resolve_right
      (disjoint_left.mp (hF.closure_disjoint_inside hS j.2 i) hxcl)
    exact hF.ends_subset_nodes hS j.2
      ⟨hxcl, hF.isNormal i ⟨hxF, D.closure_subset_U j.2.1 hxcl⟩⟩
  have hBB : ∀ i j, i ≠ j → B i ∩ B j ⊆ ringNodes D F := by
    intro i j hij
    cases i with
    | inl i =>
      cases j with
      | inl j => exact hF.ring_discs_inter_nodes hS (fun h => hij (congrArg Sum.inl h))
      | inr j => exact hRE i j
    | inr i =>
      cases j with
      | inl j => exact fun x hx => hRE j i ⟨hx.2, hx.1⟩
      | inr j =>
        intro x hx
        have hxcl := hCC i j (fun h => hij (congrArg Sum.inr h)) hx
        exact hF.ends_subset_nodes hS i.2 ⟨hxcl.1,
          closure_edges_inter_subset_vertices D i.2.1 j.2.1
            (fun h => hij (congrArg Sum.inr (Subtype.ext h))) hxcl⟩
  have hbd : ∀ i, B i ∩ bd S ⊆ ringNodes D F := by
    intro i
    cases i with
    | inl i => exact hF.ring_disc_inter_bd_nodes hS i
    | inr i =>
      intro x hx
      change x ∈ C i ∩ bd S at hx
      have hxV := (hC i).2.2.2.2.2 hx
      have hxcl : x ∈ closure i.1 := by
        rw [← (hC i).2.2.1]
        exact ⟨hx.1, D.V_subset_U hxV⟩
      exact hF.ends_subset_nodes hS i.2 ⟨hxcl, hxV⟩
  obtain ⟨P, hPN, hPU, hPc, hPcl⟩ := exists_painting_of_discs
    (ringNodes D F) (D.finite_V.subset (sep_subset _ _)) B hB hBN hBB hbd
  refine ⟨P, hPN, hPU, hPc, hPcl, injective_disc_cells hB hBN hBB, ?_⟩
  rw [hPU]
  apply Subset.antisymm
  · rintro x ⟨hxN | hxB, hxbd⟩
    · exact ⟨hxN.1, hxbd⟩
    · obtain ⟨i, hxi⟩ := mem_iUnion.mp hxB
      exact ⟨(hbd i ⟨hxi, hxbd⟩).1, hxbd⟩
  · rintro x ⟨hxV, hxbd⟩
    exact ⟨.inl ⟨hxV, fun i => hF.not_inside_of_bd hS hxbd i⟩, hxbd⟩

end GraphMinor.GM08
