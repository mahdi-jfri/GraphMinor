module

public import GraphMinor.GM02.Termination

/-!
# Restricting a termination to closed vertex sets

For the small-separator count in II (2.8), each path component is closed
under the matching pairs. Restricting either termination to that component
therefore restricts its support by intersection. The support on each
component has even size, since each retained pair contributes two vertices.
-/

@[expose] public section
namespace GraphMinor.GM02
open Set Classical
universe u

/-- Retain the pairs whose endpoints lie in a specified set. -/
noncomputable def Termination.restrict {α : Type u} {vertices : Set α}
    (A : Termination vertices) (S : Set α) : Termination vertices where
  pairs := A.pairs.filter (fun p => ∀ a ∈ p, a ∈ S)
  not_diag _ hp := A.not_diag _ (Finset.mem_filter.1 hp).1
  vertex_mem _ hp := A.vertex_mem _ (Finset.mem_filter.1 hp).1
  disjoint _ hp _ hq := A.disjoint _ (Finset.mem_filter.1 hp).1 _ (Finset.mem_filter.1 hq).1

/-- On a set closed under pairs, restriction intersects the support. -/
theorem Termination.restrict_support {α : Type u} {vertices : Set α}
    (A : Termination vertices) (S : Set α)
    (hclosed : ∀ p ∈ A.pairs, ∀ a ∈ p, a ∈ S → ∀ b ∈ p, b ∈ S) :
    (A.restrict S).support = A.support ∩ S := by
  ext a
  constructor
  · intro ha
    obtain ⟨p, hpa⟩ := Set.mem_iUnion.1 ha
    obtain ⟨hp, hap⟩ := Set.mem_iUnion.1 hpa
    obtain ⟨hpA, hpS⟩ := Finset.mem_filter.1 hp
    exact ⟨Set.mem_iUnion.2 ⟨p, Set.mem_iUnion.2 ⟨hpA, hap⟩⟩, hpS a hap⟩
  · rintro ⟨haA, haS⟩
    obtain ⟨p, hpa⟩ := Set.mem_iUnion.1 haA
    obtain ⟨hp, hap⟩ := Set.mem_iUnion.1 hpa
    exact Set.mem_iUnion.2 ⟨p, Set.mem_iUnion.2
      ⟨Finset.mem_filter.2 ⟨hp, hclosed p hp a hap haS⟩, hap⟩⟩

/-- A matching has an even number of support vertices on a pair-closed set. -/
theorem Termination.even_support_inter {α : Type u} {vertices : Set α}
    (A : Termination vertices) (S : Set α)
    (hclosed : ∀ p ∈ A.pairs, ∀ a ∈ p, a ∈ S → ∀ b ∈ p, b ∈ S) :
    Even (A.support ∩ S).ncard := by
  rw [← A.restrict_support S hclosed, (A.restrict S).support_ncard]
  exact ⟨(A.restrict S).index, by omega⟩

end GraphMinor.GM02
