module

public import GraphMinor.GM02.CrossingScheme
import Mathlib.Data.Set.Finite.Powerset

/-!
# Finiteness of crossing schemes

For II (2.8), the endpoints of every pair in a crossing scheme lie in the
original support or in the separator. This is a fixed finite set. Both
reserved sets lie in the separator as well. The four finite choices
therefore determine a scheme, since its remaining fields are propositions.
-/

public section
namespace GraphMinor.GM02
open Graph Set Classical
universe u v

private theorem finite_endpoint_pairs {α : Type u} {S : Set α} (hS : S.Finite) :
    {p : Sym2 α | ∀ v ∈ p, v ∈ S}.Finite := by
  have heq : {p : Sym2 α | ∀ v ∈ p, v ∈ S} =
      (fun p : α × α => s(p.1, p.2)) '' (S ×ˢ S) := by
    ext p
    induction p using Sym2.inductionOn with
    | hf a b =>
      constructor
      · intro h
        exact ⟨(a, b), ⟨h a (Sym2.mem_mk_left _ _), h b (Sym2.mem_mk_right _ _)⟩, rfl⟩
      · rintro ⟨⟨c, d⟩, ⟨hc, hd⟩, heq⟩ v hv
        rw [← heq] at hv
        rcases Sym2.mem_iff.1 hv with rfl | rfl
        · exact hc
        · exact hd
  rw [heq]
  exact (hS.prod hS).image _

/-- Only finitely many terminations have all endpoints in a finite set. -/
theorem finite_terminations_supported {α : Type u} {vertices S : Set α} (hS : S.Finite) :
    Finite {A : Termination vertices // A.support ⊆ S} := by
  let P : Set (Sym2 α) := {p | ∀ v ∈ p, v ∈ S}
  have hP : P.Finite := finite_endpoint_pairs hS
  let _ : Finite {D : Set (Sym2 α) // D ⊆ P} := hP.finite_subsets.to_subtype
  let f : {A : Termination vertices // A.support ⊆ S} → {D : Set (Sym2 α) // D ⊆ P} :=
    fun A => ⟨A.val.pairs, fun p hp v hv =>
      A.property (Set.mem_iUnion.2 ⟨p, Set.mem_iUnion.2 ⟨hp, hv⟩⟩)⟩
  apply Finite.of_injective f
  intro A B heq
  apply Subtype.ext
  apply Termination.ext_pairs
  apply Finset.coe_injective
  exact congrArg Subtype.val heq

/-- Both new supports are contained in the old support and separator,
by condition (i) of a crossing scheme. -/
theorem CrossingScheme.supports_subset {α : Type u} {β : Type v}
    {G H H' : Graph α β} {A₀ : Termination V(G)} (C : CrossingScheme G H H' A₀) :
    C.left.support ⊆ A₀.support ∪ (V(H) ∩ V(H')) ∧
      C.right.support ⊆ A₀.support ∪ (V(H) ∩ V(H')) := by
  constructor
  · intro a ha
    by_cases hx : a ∈ V(H) ∩ V(H')
    · exact Or.inr hx
    · have h : a ∈ C.left.support \ (V(H) ∩ V(H')) := ⟨ha, hx⟩
      rw [C.left_support] at h
      exact Or.inl h.1
  · intro a ha
    by_cases hx : a ∈ V(H) ∩ V(H')
    · exact Or.inr hx
    · have h : a ∈ C.right.support \ (V(H) ∩ V(H')) := ⟨ha, hx⟩
      rw [C.right_support] at h
      exact Or.inl h.1

/-- The four choices determine a crossing scheme. -/
theorem CrossingScheme.ext_data {α : Type u} {β : Type v}
    {G H H' : Graph α β} {A₀ : Termination V(G)}
    {C D : CrossingScheme G H H' A₀}
    (hl : C.left = D.left) (hr : C.right = D.right)
    (hz : C.reservedLeft = D.reservedLeft) (hz' : C.reservedRight = D.reservedRight) : C = D := by
  cases C
  cases D
  cases hl
  cases hr
  cases hz
  cases hz'
  rfl

/-- Finiteness in II (2.8) already follows from condition (i) and the
reserved-set bounds. The sharper numerical bound also uses the paths. -/
theorem finite_crossingSchemes {α : Type u} {β : Type v}
    {G H H' : Graph α β} (A₀ : Termination V(G))
    (hX : (V(H) ∩ V(H')).Finite) : Finite (CrossingScheme G H H' A₀) := by
  let S := A₀.support ∪ (V(H) ∩ V(H'))
  let TS := {A : Termination V(G) // A.support ⊆ S}
  let RS := {Z : Set α // Z ⊆ V(H) ∩ V(H')}
  let _ : Finite TS := finite_terminations_supported (A₀.support_finite.union hX)
  let _ : Finite RS := hX.finite_subsets.to_subtype
  let f : CrossingScheme G H H' A₀ → TS × TS × RS × RS := fun C =>
    (⟨C.left, C.supports_subset.1⟩, ⟨C.right, C.supports_subset.2⟩,
      ⟨C.reservedLeft, C.reservedLeft_subset⟩, ⟨C.reservedRight, C.reservedRight_subset⟩)
  apply Finite.of_injective f
  intro C D heq
  exact CrossingScheme.ext_data
    (congrArg (fun p => p.1.val) heq)
    (congrArg (fun p => p.2.1.val) heq)
    (congrArg (fun p => p.2.2.1.val) heq)
    (congrArg (fun p => p.2.2.2.val) heq)

end GraphMinor.GM02
