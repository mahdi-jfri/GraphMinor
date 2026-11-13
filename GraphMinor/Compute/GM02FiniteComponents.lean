module

public import GraphMinor.GM02.DeletedComponents
public import Mathlib.Combinatorics.Graph.Simple

/-!
# Finite component sets for constructing balanced sides

For the successful-output path of II (3.1), represent a deleted component
by a vertex finset. Two remaining vertices in one component have equal
component sets. Consequently, components are equal or disjoint. These
facts let a vertex scan accumulate whole components without double
counting terminals.
-/

@[expose] public section
namespace GraphMinor.Compute
open Graph Set Relation GraphMinor.GM02 Classical

/-- The finite vertex set of a component after deleting a proposed separator. -/
noncomputable def gm02FiniteComponent {n : ℕ} (G : SimpleGraph (Fin n))
    (X : Finset (Fin n)) (a : Fin n) : Finset (Fin n) :=
  (Set.toFinite (deletedComponent (Graph.ofSimpleGraph G) (X : Set (Fin n)) a)).toFinset

/-- Finite and set representations give exactly the same component. -/
theorem mem_gm02FiniteComponent {n : ℕ} (G : SimpleGraph (Fin n)) (X : Finset (Fin n))
    (a b : Fin n) : b ∈ gm02FiniteComponent G X a ↔
      b ∈ deletedComponent (Graph.ofSimpleGraph G) (X : Set (Fin n)) a :=
  Set.Finite.mem_toFinset _

/-- Every component vertex avoids the deleted set. -/
theorem gm02FiniteComponent_disjoint {n : ℕ} (G : SimpleGraph (Fin n))
    (X : Finset (Fin n)) (a : Fin n) : Disjoint (gm02FiniteComponent G X a) X := by
  apply Finset.disjoint_left.2
  intro b hb hbX
  exact ((mem_gm02FiniteComponent G X a b).1 hb).1.2 hbX

/-- A vertex outside the deleted set belongs to its own component. -/
theorem self_mem_gm02FiniteComponent {n : ℕ} (G : SimpleGraph (Fin n))
    (X : Finset (Fin n)) (a : Fin n) (ha : a ∉ X) : a ∈ gm02FiniteComponent G X a :=
  (mem_gm02FiniteComponent G X a a).2 ⟨⟨Set.mem_univ _, ha⟩, ReflTransGen.refl⟩

/-- The start vertex must avoid deletion whenever its component is nonempty. -/
theorem gm02FiniteComponent_start_not_mem {n : ℕ} (G : SimpleGraph (Fin n))
    (X : Finset (Fin n)) (a b : Fin n) (hb : b ∈ gm02FiniteComponent G X a) : a ∉ X := by
  have hb' := (mem_gm02FiniteComponent G X a b).1 hb
  have hp := hb'.2
  rcases hp.cases_head with heq | ⟨c, hac, _⟩
  · exact heq ▸ hb'.1.2
  · obtain ⟨e, he⟩ := hac
    rw [Graph.induce_isLink] at he
    exact he.2.1.2

/-- Membership in a component identifies the two component sets. -/
theorem gm02FiniteComponent_eq_of_mem {n : ℕ} (G : SimpleGraph (Fin n))
    (X : Finset (Fin n)) (a b : Fin n) (hb : b ∈ gm02FiniteComponent G X a) :
    gm02FiniteComponent G X b = gm02FiniteComponent G X a := by
  have he := deletedComponent_eq_of_reachable ((mem_gm02FiniteComponent G X a b).1 hb).2
  apply Finset.ext
  intro v
  simp only [mem_gm02FiniteComponent]
  rw [he]

/-- Distinct deleted components have disjoint finite vertex sets. -/
theorem gm02FiniteComponent_eq_or_disjoint {n : ℕ} (G : SimpleGraph (Fin n))
    (X : Finset (Fin n)) (a b : Fin n) :
    gm02FiniteComponent G X a = gm02FiniteComponent G X b ∨
      Disjoint (gm02FiniteComponent G X a) (gm02FiniteComponent G X b) := by
  by_cases h : gm02FiniteComponent G X a = gm02FiniteComponent G X b
  · exact Or.inl h
  · apply Or.inr
    apply Finset.disjoint_left.2
    intro v hva hvb
    exact h ((gm02FiniteComponent_eq_of_mem G X a v hva).symm.trans
      (gm02FiniteComponent_eq_of_mem G X b v hvb))

/-- Coercing the finite component recovers exactly its vertex set. -/
theorem coe_gm02FiniteComponent {n : ℕ} (G : SimpleGraph (Fin n))
    (X : Finset (Fin n)) (a : Fin n) :
    (gm02FiniteComponent G X a : Set (Fin n)) =
      deletedComponent (Graph.ofSimpleGraph G) (X : Set (Fin n)) a := Set.Finite.coe_toFinset _

/-- Finite component terminal counts agree with the set cardinalities used
by the component test. -/
theorem gm02FiniteComponent_count {n : ℕ} (G : SimpleGraph (Fin n))
    (Q X : Finset (Fin n)) (a : Fin n) :
    (gm02FiniteComponent G X a ∩ Q).card =
      (deletedComponent (Graph.ofSimpleGraph G) (X : Set (Fin n)) a ∩ (Q : Set (Fin n))).ncard := by
  rw [← Set.ncard_coe_finset, Finset.coe_inter, coe_gm02FiniteComponent]

end GraphMinor.Compute
