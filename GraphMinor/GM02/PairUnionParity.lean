module

public import GraphMinor.GM02.PairPathUnionDegree
public import GraphMinor.GM02.TerminationDegree

/-!
# Parity of endpoints in two matchings

The contracted paths in II (2.9) are the union of the two side
terminations. Comparing their degrees with matching degrees gives the
endpoint parity condition. It also shows that each original terminal
remains an endpoint on at least one side.
-/

public section
namespace GraphMinor.GM02
open Graph SimpleGraph Set Classical
universe u
variable {α : Type u} {V V₁ V₂ : Set α} (A : Termination V) (L : Termination V₁) (R : Termination V₂)

/-- Every original endpoint occurs among the endpoints of the component union. -/
theorem IsPairPathUnion.original_support_subset
    (hU : IsPairPathUnion A (L.pairGraph ⊔ R.pairGraph) (L.support ∪ R.support)) :
    A.support ⊆ L.support ∪ R.support := by
  intro a ha
  obtain ⟨p, hp⟩ := Set.mem_iUnion.1 ha
  obtain ⟨hp, hap⟩ := Set.mem_iUnion.1 hp
  rw [← hU.choose_spec.2.2.1]
  exact Set.mem_iUnion.2 ⟨⟨p, hp⟩, hU.endpoint_mem ⟨p, hp⟩ hap⟩

/-- An original endpoint belongs to one side, and an internal endpoint to both.
This is the degree identity used in condition (ii) of II (2.9). -/
theorem IsPairPathUnion.endpoint_degree_identity
    (hU : IsPairPathUnion A (L.pairGraph ⊔ R.pairGraph) (L.support ∪ R.support))
    (hdis : Disjoint (L.pairs : Set (Sym2 α)) (R.pairs : Set (Sym2 α)))
    {a : α} (ha : a ∈ L.support ∪ R.support) :
    (if a ∈ L.support then 1 else 0) + (if a ∈ R.support then 1 else 0) =
      (if a ∈ A.support then 1 else 2) := by
  exact (L.union_neighborSet_ncard R hdis a).symm.trans (hU.neighborSet_ncard ha)

/-- Endpoint membership has even total multiplicity across the original and
both side terminations. -/
theorem IsPairPathUnion.even_support
    (hU : IsPairPathUnion A (L.pairGraph ⊔ R.pairGraph) (L.support ∪ R.support))
    (hdis : Disjoint (L.pairs : Set (Sym2 α)) (R.pairs : Set (Sym2 α))) (a : α) :
    Even ((if a ∈ A.support then 1 else 0) +
      (if a ∈ L.support then 1 else 0) + (if a ∈ R.support then 1 else 0)) := by
  by_cases ha : a ∈ L.support ∪ R.support
  · have hd := hU.endpoint_degree_identity A L R hdis ha
    split_ifs at hd ⊢ <;> simp_all
  · have haA : a ∉ A.support := fun h => ha (hU.original_support_subset A L R h)
    have haL : a ∉ L.support := fun h => ha (Or.inl h)
    have haR : a ∉ R.support := fun h => ha (Or.inr h)
    simp only [ite_eq_right haA, ite_eq_right haL, ite_eq_right haR]
    exact ⟨0, rfl⟩

end GraphMinor.GM02
