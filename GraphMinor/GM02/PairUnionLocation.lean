module

public import GraphMinor.GM02.PairUnionParity

/-!
# Locations of side endpoints

Outside the separator, only one side can contain a vertex. The degree
identity therefore forces every side endpoint there to be an original
terminal. Conversely, an original terminal occurs on some side, and the
location of the vertex determines that side. This proves condition (i)
in the forward construction of corrected II (2.9).
-/

public section
namespace GraphMinor.GM02
open Graph SimpleGraph Set Classical
universe u
variable {α : Type u} {V V₁ V₂ Y Z : Set α} (A : Termination V) (L : Termination V₁) (R : Termination V₂)

/-- In a union of two matching path systems, endpoints outside the separator
are exactly the original terminals in the corresponding exclusive side. -/
theorem IsPairPathUnion.support_diff_inter
    (hU : IsPairPathUnion A (L.pairGraph ⊔ R.pairGraph) (L.support ∪ R.support))
    (hdis : Disjoint (L.pairs : Set (Sym2 α)) (R.pairs : Set (Sym2 α)))
    (hL : L.support ⊆ Y) (hR : R.support ⊆ Z) :
    L.support \ (Y ∩ Z) = A.support ∩ (Y \ Z) := by
  ext a
  constructor
  · rintro ⟨haL, haX⟩
    have haY := hL haL
    have haZ : a ∉ Z := fun hz => haX ⟨haY, hz⟩
    have haR : a ∉ R.support := fun hr => haZ (hR hr)
    have hd := hU.endpoint_degree_identity A L R hdis (Or.inl haL)
    have haA : a ∈ A.support := by
      by_contra hn
      simp only [ite_eq_left haL, ite_eq_right haR, ite_eq_right hn] at hd
      contradiction
    exact ⟨haA, haY, haZ⟩
  · rintro ⟨haA, haY, haZ⟩
    have haL : a ∈ L.support := by
      rcases hU.original_support_subset A L R haA with h | h
      · exact h
      · exact (haZ (hR h)).elim
    exact ⟨haL, fun hx => haZ hx.2⟩

end GraphMinor.GM02
