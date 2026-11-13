module

public import GraphMinor.GM02.CrossingScheme

/-!
# Support constraints for crossing schemes

In the counting argument for II (2.8), every original terminal occurs on
one side, while every additional used separator vertex occurs on both.
The path condition supplies the original endpoints, and condition (ii)
then forces these alternatives by parity.
-/

public section
namespace GraphMinor.GM02
open Graph Set Classical
universe u v

/-- The endpoints of every original pair belong to the union of the new
supports, by the path condition in a crossing scheme. -/
theorem CrossingScheme.original_support_subset {α : Type u} {β : Type v}
    {G H H' : Graph α β} {A₀ : Termination V(G)} (C : CrossingScheme G H H' A₀) :
    A₀.support ⊆ C.left.support ∪ C.right.support := by
  obtain ⟨P, _, _, hcover, _⟩ := C.path_union
  intro a ha
  obtain ⟨p, hpa⟩ := Set.mem_iUnion.1 ha
  obtain ⟨hp, hap⟩ := Set.mem_iUnion.1 hpa
  have hout : s(p.out.1, p.out.2) = p := p.out_eq
  change a ∈ p at hap
  rw [← hout, Sym2.mem_iff] at hap
  have haP : a ∈ (P ⟨p, hp⟩).support := by
    rcases hap with rfl | rfl
    · exact (P ⟨p, hp⟩).start_mem_support
    · exact (P ⟨p, hp⟩).end_mem_support
  rw [← hcover]
  exact Set.mem_iUnion.2 ⟨⟨p, hp⟩, haP⟩

/-- At a separator vertex, membership in both new supports is equivalent
to membership in their union but not in the original support. -/
theorem CrossingScheme.inter_support_iff {α : Type u} {β : Type v}
    {G H H' : Graph α β} {A₀ : Termination V(G)} (C : CrossingScheme G H H' A₀)
    {a : α} (ha : a ∈ V(H) ∩ V(H')) :
    (a ∈ C.left.support ∧ a ∈ C.right.support) ↔
      (a ∈ C.left.support ∪ C.right.support ∧ a ∉ A₀.support) := by
  obtain ⟨n, hn⟩ := C.even_support a ha
  by_cases h₀ : a ∈ A₀.support <;>
    by_cases hl : a ∈ C.left.support <;>
    by_cases hr : a ∈ C.right.support <;>
    simp [h₀, hl, hr] at hn ⊢ <;> omega

/-- A vertex used by both new terminations lies in the separator and is
not an original terminal. This combines conditions (i) and (ii). -/
theorem CrossingScheme.inter_support_subset {α : Type u} {β : Type v}
    {G H H' : Graph α β} {A₀ : Termination V(G)} (C : CrossingScheme G H H' A₀) :
    C.left.support ∩ C.right.support ⊆ (V(H) ∩ V(H')) \ A₀.support := by
  intro a ha
  have haX : a ∈ V(H) ∩ V(H') := by
    by_contra hn
    have hl : a ∈ C.left.support \ (V(H) ∩ V(H')) := ⟨ha.1, hn⟩
    have hr : a ∈ C.right.support \ (V(H) ∩ V(H')) := ⟨ha.2, hn⟩
    rw [C.left_support] at hl
    rw [C.right_support] at hr
    exact hl.2.2 hr.2.1
  exact ⟨haX, ((C.inter_support_iff haX).1 ha).2⟩

/-- New vertices of the path union are exactly the vertices used by both
new terminations. No one-sided nonterminal endpoint is permitted. -/
theorem CrossingScheme.support_union_eq {α : Type u} {β : Type v}
    {G H H' : Graph α β} {A₀ : Termination V(G)} (C : CrossingScheme G H H' A₀) :
    C.left.support ∪ C.right.support = A₀.support ∪ (C.left.support ∩ C.right.support) := by
  apply Set.Subset.antisymm
  · intro a ha
    by_cases h₀ : a ∈ A₀.support
    · exact Or.inl h₀
    · have hx : a ∈ V(H) ∩ V(H') := by
        by_contra hn
        rcases ha with hl | hr
        · have h : a ∈ C.left.support \ (V(H) ∩ V(H')) := ⟨hl, hn⟩
          rw [C.left_support] at h
          exact h₀ h.1
        · have h : a ∈ C.right.support \ (V(H) ∩ V(H')) := ⟨hr, hn⟩
          rw [C.right_support] at h
          exact h₀ h.1
      exact Or.inr ((C.inter_support_iff hx).2 ⟨ha, h₀⟩)
  · intro a ha
    exact ha.elim (fun h => C.original_support_subset h) (fun h => Or.inl h.1)

end GraphMinor.GM02
