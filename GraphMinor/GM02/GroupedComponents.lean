module

public import GraphMinor.GM02.DeletedComponents
public import GraphMinor.GM02.BagSeparation
import GraphMinor.GM02.ComponentWeights
import GraphMinor.GM02.FiniteRegions

/-!
# Grouping components into two balanced sides

Apply the component-weight argument of II (2.6) to the components supplied
by (2.5). Their disjoint union counts give the bounds on both sides. No
walk avoiding the separator can join components placed on different sides.
-/

public section
namespace GraphMinor.GM02
open Graph Set Relation Classical
universe u v

/-- The component grouping in II (2.6), pages 313–314, with the weaker
two-thirds hypothesis used by algorithm (3.1), page 316. -/
theorem exists_grouped_components_of_two_thirds {α : Type u} {β : Type v}
    {G : Graph α β} {X Q : Set α} (hG : (V(G)).Finite) (hQG : Q ⊆ V(G))
    (hbound : ∀ a ∈ V(G) \ X,
      3 * (deletedComponent G X a ∩ Q).ncard ≤ 2 * (Q \ X).ncard) :
    ∃ Y Y', Y ∪ Y' = V(G) \ X ∧ Disjoint Y Y' ∧ Separates G X Y Y' ∧
      3 * (Y ∩ Q).ncard ≤ 2 * (Q \ X).ncard ∧
      3 * (Y' ∩ Q).ncard ≤ 2 * (Q \ X).ncard := by
  let C := deletedComponents G X hG
  have hQ := hG.subset hQG
  have hdis := deletedComponents_disjoint (X := X) hG
  have hcover := deletedComponents_cover (X := X) hG
  have htotal : (∑ A ∈ C, (A ∩ Q).ncard) = (Q \ X).ncard := by
    have hcount := ncard_regions_inter C id hQ hdis
    change ((⋃ A ∈ C, A) ∩ Q).ncard = (∑ A ∈ C, (A ∩ Q).ncard) at hcount
    rw [← hcount]
    rw [hcover]
    congr 1
    ext a
    exact ⟨fun h => ⟨h.2, h.1.2⟩, fun h => ⟨⟨hQG h.1, h.2⟩, h.1⟩⟩
  have hc : ∀ A ∈ C, 3 * (A ∩ Q).ncard ≤ 2 * ∑ B ∈ C, (B ∩ Q).ncard := by
    intro A hA
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.1 hA
    rw [htotal]
    exact hbound a ((hG.sdiff (t := X)).mem_toFinset.1 ha)
  obtain ⟨s, hs, hlo, hhi⟩ := exists_two_thirds_weight_partition_of_two_thirds C
    (fun A => (A ∩ Q).ncard) hc
  let Y : Set α := ⋃ A ∈ s, A
  let Y' : Set α := ⋃ A ∈ C \ s, A
  have hcount : (Y ∩ Q).ncard = ∑ A ∈ s, (A ∩ Q).ncard :=
    ncard_regions_inter s id hQ (fun A hA B hB => hdis A (hs hA) B (hs hB))
  have hcount' : (Y' ∩ Q).ncard = ∑ A ∈ C \ s, (A ∩ Q).ncard :=
    ncard_regions_inter (C \ s) id hQ (fun A hA B hB =>
      hdis A (Finset.mem_sdiff.1 hA).1 B (Finset.mem_sdiff.1 hB).1)
  have hsum := Finset.sum_sdiff hs (f := fun A => (A ∩ Q).ncard)
  have hunion : Y ∪ Y' = V(G) \ X := by
    rw [← hcover]
    ext a
    simp only [Y, Y', Set.mem_union, Set.mem_iUnion]
    constructor
    · rintro (⟨A, hA, ha⟩ | ⟨A, hA, ha⟩)
      · exact ⟨A, hs hA, ha⟩
      · exact ⟨A, (Finset.mem_sdiff.1 hA).1, ha⟩
    · rintro ⟨A, hA, ha⟩
      by_cases hAs : A ∈ s
      · exact Or.inl ⟨A, hAs, ha⟩
      · exact Or.inr ⟨A, Finset.mem_sdiff.2 ⟨hA, hAs⟩, ha⟩
  have hYY' : Disjoint Y Y' := by
    apply Set.disjoint_left.2
    intro a ha ha'
    obtain ⟨A, hA, haA⟩ := Set.mem_iUnion.1 ha |>.imp fun _ h => Set.mem_iUnion.1 h
    obtain ⟨B, hB, haB⟩ := Set.mem_iUnion.1 ha' |>.imp fun _ h => Set.mem_iUnion.1 h
    exact Set.disjoint_left.1 (hdis A (hs hA) B (Finset.mem_sdiff.1 hB).1
      (fun heq => (Finset.mem_sdiff.1 hB).2 (heq ▸ hA))) haA haB
  refine ⟨Y, Y', hunion, hYY', ?_, ?_, ?_⟩
  · intro a ha b hb haX hbX hp
    obtain ⟨A, hA, haA⟩ := Set.mem_iUnion.1 ha |>.imp fun _ h => Set.mem_iUnion.1 h
    obtain ⟨B, hB, hbB⟩ := Set.mem_iUnion.1 hb |>.imp fun _ h => Set.mem_iUnion.1 h
    have heqa := deletedComponent_eq_of_mem hG (hs hA) haA
    have heqb := deletedComponent_eq_of_mem hG (Finset.mem_sdiff.1 hB).1 hbB
    have heq : A = B := heqa.symm.trans ((deletedComponent_eq_of_reachable hp).trans heqb)
    exact (Finset.mem_sdiff.1 hB).2 (heq ▸ hA)
  · rw [hcount]
    rwa [htotal] at hhi
  · rw [hcount']
    rw [htotal] at hlo hsum
    omega

/-- The component grouping for the half-balanced separator in II (2.6). -/
theorem exists_grouped_components {α : Type u} {β : Type v}
    {G : Graph α β} {X Q : Set α} (hG : (V(G)).Finite) (hQG : Q ⊆ V(G))
    (hhalf : ∀ a ∈ V(G) \ X,
      2 * (deletedComponent G X a ∩ Q).ncard ≤ (Q \ X).ncard) :
    ∃ Y Y', Y ∪ Y' = V(G) \ X ∧ Disjoint Y Y' ∧ Separates G X Y Y' ∧
      3 * (Y ∩ Q).ncard ≤ 2 * (Q \ X).ncard ∧
      3 * (Y' ∩ Q).ncard ≤ 2 * (Q \ X).ncard := by
  apply exists_grouped_components_of_two_thirds hG hQG
  intro a ha
  have hh := hhalf a ha
  omega

end GraphMinor.GM02
