module

public import GraphMinor.GM02.CrossingPathLists
import GraphMinor.GM02.CrossingSchemeSupports

/-!
# Recovering supports and reservations from the list encoding

For II (2.8), an internal listed vertex belongs to both new supports.
An original terminal outside the separator belongs to its prescribed side.
For original terminals in the separator, the marked set records the first
support. The marked nonterminals are exactly the first reserved set.
-/

public section
namespace GraphMinor.GM02
open Graph Set Classical
universe u v

/-- Listed vertices are exactly the vertices used by both new terminations. -/
theorem CrossingScheme.listed_vertices_eq {α : Type u} {β : Type v}
    {G H H' : Graph α β} {A₀ : Termination V(G)} (C : CrossingScheme G H H' A₀) :
    (⋃ p, {a | a ∈ C.pathListArrangement.paths p}) = C.left.support ∩ C.right.support := by
  ext a
  constructor
  · intro ha
    obtain ⟨p, hp⟩ := Set.mem_iUnion.1 ha
    obtain ⟨haP, haBool⟩ := List.mem_filter.1 hp
    have haX := of_decide_eq_true haBool
    exact (C.inter_support_iff haX.1).2 ⟨C.pairPath_support_subset p haP, haX.2⟩
  · intro ha
    have haX := C.inter_support_subset ha
    have haU : a ∈ C.left.support ∪ C.right.support := Or.inl ha.1
    rw [← C.path_union.choose_spec.2.2.1] at haU
    obtain ⟨p, hp⟩ := Set.mem_iUnion.1 haU
    refine Set.mem_iUnion.2 ⟨p, ?_⟩
    exact List.mem_filter.2 ⟨hp, by simpa using haX⟩

/-- The marked set restricted to original terminals records exactly their
membership in the first support inside the separator. -/
theorem CrossingScheme.original_marked_iff {α : Type u} {β : Type v}
    {G H H' : Graph α β} {A₀ : Termination V(G)} (C : CrossingScheme G H H' A₀)
    {a : α} (ha : a ∈ A₀.support) :
    a ∈ C.pathListArrangement.marked ↔ a ∈ V(H) ∩ V(H') ∧ a ∈ C.left.support := by
  constructor
  · intro hm
    rcases hm with hz | ht
    · have hu : a ∈ C.reservedLeft ∪ C.reservedRight := Or.inl hz
      rw [C.reserved_union] at hu
      exact (hu.2 (Or.inl (Or.inl ha))).elim
    · exact ⟨ht.1.2, ht.2⟩
  · intro h
    exact Or.inr ⟨⟨ha, h.1⟩, h.2⟩

/-- The first support is determined by the list encoding and the fixed
original terminal locations. -/
theorem CrossingScheme.left_support_eq_of_encoding {α : Type u} {β : Type v}
    {G H H' : Graph α β} {A₀ : Termination V(G)} {C D : CrossingScheme G H H' A₀}
    (h : C.pathListArrangement = D.pathListArrangement) : C.left.support = D.left.support := by
  have hlisted : C.left.support ∩ C.right.support = D.left.support ∩ D.right.support := by
    rw [← C.listed_vertices_eq, ← D.listed_vertices_eq, h]
  have hmarked := congrArg PathListArrangement.marked h
  have hone : ∀ (C D : CrossingScheme G H H' A₀),
      C.left.support ∩ C.right.support = D.left.support ∩ D.right.support →
      C.pathListArrangement.marked = D.pathListArrangement.marked →
      C.left.support ⊆ D.left.support := by
    intro C D hi hm a ha
    by_cases ha₀ : a ∈ A₀.support
    · by_cases haX : a ∈ V(H) ∩ V(H')
      · have ham := (C.original_marked_iff ha₀).2 ⟨haX, ha⟩
        rw [hm] at ham
        exact ((D.original_marked_iff ha₀).1 ham).2
      · have hay : a ∈ C.left.support \ (V(H) ∩ V(H')) := ⟨ha, haX⟩
        rw [C.left_support, ← D.left_support] at hay
        exact hay.1
    · have hu : a ∈ C.left.support ∪ C.right.support := Or.inl ha
      rw [C.support_union_eq] at hu
      have hab : a ∈ C.left.support ∩ C.right.support := hu.resolve_left ha₀
      rw [hi] at hab
      exact hab.1
  exact Set.Subset.antisymm (hone C D hlisted hmarked) (hone D C hlisted.symm hmarked.symm)

/-- The second support follows from the common path vertices and the
first support, since original terminals occur on just one side. -/
theorem CrossingScheme.right_support_eq_of_encoding {α : Type u} {β : Type v}
    {G H H' : Graph α β} {A₀ : Termination V(G)} {C D : CrossingScheme G H H' A₀}
    (h : C.pathListArrangement = D.pathListArrangement) : C.right.support = D.right.support := by
  have hl := CrossingScheme.left_support_eq_of_encoding h
  have hi : C.left.support ∩ C.right.support = D.left.support ∩ D.right.support := by
    rw [← C.listed_vertices_eq, ← D.listed_vertices_eq, h]
  have hone : ∀ (C D : CrossingScheme G H H' A₀), C.left.support = D.left.support →
      C.left.support ∩ C.right.support = D.left.support ∩ D.right.support →
      C.right.support ⊆ D.right.support := by
    intro C D hl hi a ha
    by_cases ha₀ : a ∈ A₀.support
    · have hu := D.original_support_subset ha₀
      rcases hu with hal | har
      · rw [← hl] at hal
        exact ((C.inter_support_subset ⟨hal, ha⟩).2 ha₀).elim
      · exact har
    · have hu : a ∈ C.left.support ∪ C.right.support := Or.inr ha
      rw [C.support_union_eq] at hu
      have hab := hu.resolve_left ha₀
      rw [hi] at hab
      exact hab.2
  exact Set.Subset.antisymm (hone C D hl hi) (hone D C hl.symm hi.symm)

/-- Removing original terminals from the marked set recovers the first
reserved set, by condition (iii). -/
theorem CrossingScheme.reservedLeft_eq_marked_sdiff {α : Type u} {β : Type v}
    {G H H' : Graph α β} {A₀ : Termination V(G)} (C : CrossingScheme G H H' A₀) :
    C.reservedLeft = C.pathListArrangement.marked \ A₀.support := by
  ext a
  constructor
  · intro ha
    have hu : a ∈ C.reservedLeft ∪ C.reservedRight := Or.inl ha
    rw [C.reserved_union] at hu
    exact ⟨Or.inl ha, fun h => hu.2 (Or.inl (Or.inl h))⟩
  · rintro ⟨hz | ht, hn⟩
    · exact hz
    · exact (hn ht.1.1).elim

/-- Equal list encodings recover both reserved sets. -/
theorem CrossingScheme.reserved_eq_of_encoding {α : Type u} {β : Type v}
    {G H H' : Graph α β} {A₀ : Termination V(G)} {C D : CrossingScheme G H H' A₀}
    (h : C.pathListArrangement = D.pathListArrangement) :
    C.reservedLeft = D.reservedLeft ∧ C.reservedRight = D.reservedRight := by
  have hl : C.reservedLeft = D.reservedLeft := by
    rw [C.reservedLeft_eq_marked_sdiff, D.reservedLeft_eq_marked_sdiff, h]
  have hsL := CrossingScheme.left_support_eq_of_encoding h
  have hsR := CrossingScheme.right_support_eq_of_encoding h
  have hu : C.reservedLeft ∪ C.reservedRight = D.reservedLeft ∪ D.reservedRight := by
    rw [C.reserved_union, D.reserved_union, hsL, hsR]
  refine ⟨hl, ?_⟩
  ext a
  constructor
  · intro ha
    have hau : a ∈ D.reservedLeft ∪ D.reservedRight := hu ▸ Or.inr ha
    rcases hau with hal | har
    · rw [← hl] at hal
      exact (Set.disjoint_left.1 C.reserved_disjoint hal ha).elim
    · exact har
  · intro ha
    have hau : a ∈ C.reservedLeft ∪ C.reservedRight := hu.symm ▸ Or.inr ha
    rcases hau with hal | har
    · rw [hl] at hal
      exact (Set.disjoint_left.1 D.reserved_disjoint hal ha).elim
    · exact har

end GraphMinor.GM02
