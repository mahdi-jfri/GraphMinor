module

public import GraphMinor.GM16.TangentDisc

/-!
# Drawing finitely many loops at one boundary vertex

For the small torso drawing in XVI (1.3), page 51, nested closed discs
that touch at one boundary vertex give disjoint loop arcs at that vertex.
Each smaller disc meets the preceding boundary only there, so the loop
boundaries have no other intersection.
-/

public section
namespace GraphMinor.GM16
open Set Surface
universe w

/-- Finitely many loop arcs can be drawn at a boundary point of a disc,
meeting each other and the original boundary only at that point. -/
theorem exists_nested_loop_arcs
    {S : Type w} [TopologicalSpace S] [T2Space S]
    (n : ℕ) {D : Set S} (hD : IsClosedDisc D) {v : S} (hvD : v ∈ discBd D) :
    ∃ C : Fin n → Set S,
      (∀ i, IsOArc (C i) ∧ C i ⊆ D ∧ v ∈ C i ∧ C i ∩ discBd D = {v}) ∧
      Pairwise (fun i j => C i ∩ C j = {v}) := by
  induction n generalizing D with
  | zero => exact ⟨Fin.elim0, fun i => Fin.elim0 i, fun i => Fin.elim0 i⟩
  | succ n ih =>
    obtain ⟨E, hE, hED, _, hvE, hmeet⟩ := exists_tangent_disc hD isOpen_univ hvD (mem_univ v)
    obtain ⟨C, hC, hCC⟩ := ih hE hvE
    let C' : Fin (n + 1) → Set S := Fin.cases (discBd E) C
    have hOuter : ∀ i, C i ∩ discBd D = {v} := by
      intro i
      ext x
      constructor
      · rintro ⟨hxC, hxD⟩
        exact hmeet ▸ And.intro ((hC i).2.1 hxC) hxD
      · rintro rfl
        exact ⟨(hC i).2.2.1, hvD⟩
    refine ⟨C', ?_, ?_⟩
    · intro i
      refine Fin.cases ?_ (fun j => ?_) i
      · refine ⟨hE.isOArc_discBd, (discBd_subset E).trans hED, hvE, ?_⟩
        ext x
        constructor
        · rintro ⟨hxE, hxD⟩
          exact hmeet ▸ And.intro (discBd_subset E hxE) hxD
        · rintro rfl
          exact ⟨hvE, hvD⟩
      · exact ⟨(hC j).1, (hC j).2.1.trans hED, (hC j).2.2.1, hOuter j⟩
    · intro i
      refine Fin.cases ?_ (fun k => ?_) i
      · intro j
        refine Fin.cases ?_ (fun l => ?_) j
        · intro hne
          exact (hne rfl).elim
        · intro _
          change discBd E ∩ C l = {v}
          rw [inter_comm]
          exact (hC l).2.2.2
      · intro j
        refine Fin.cases ?_ (fun l => ?_) j
        · intro _
          change C k ∩ discBd E = {v}
          exact (hC k).2.2.2
        · intro hne
          exact hCC (fun hkl => hne (congrArg Fin.succ hkl))

/-- All the loop arcs at one vertex can be placed in any prescribed
open neighborhood of that vertex. -/
theorem exists_loop_arcs_in_neighborhood
    {S : Type w} [TopologicalSpace S] [T2Space S]
    (n : ℕ) {D U : Set S} (hD : IsClosedDisc D) (hU : IsOpen U)
    {v : S} (hvD : v ∈ discBd D) (hvU : v ∈ U) :
    ∃ C : Fin n → Set S,
      (∀ i, IsOArc (C i) ∧ C i ⊆ D ∧ C i ⊆ U ∧
        v ∈ C i ∧ C i ∩ discBd D = {v}) ∧
      Pairwise (fun i j => C i ∩ C j = {v}) := by
  obtain ⟨E, hE, hED, hEU, hvE, hmeet⟩ := exists_tangent_disc hD hU hvD hvU
  obtain ⟨C, hC, hCC⟩ := exists_nested_loop_arcs n hE hvE
  refine ⟨C, ?_, hCC⟩
  intro i
  refine ⟨(hC i).1, (hC i).2.1.trans hED, (hC i).2.1.trans hEU,
    (hC i).2.2.1, ?_⟩
  ext x
  constructor
  · rintro ⟨hxC, hxD⟩
    exact hmeet ▸ And.intro ((hC i).2.1 hxC) hxD
  · rintro rfl
    exact ⟨(hC i).2.2.1, hvD⟩

end GraphMinor.GM16
