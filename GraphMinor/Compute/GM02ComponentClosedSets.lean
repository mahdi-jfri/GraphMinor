module

public import GraphMinor.Compute.GM02FiniteComponents

/-!
# Unions of whole deleted components

The grouping step for II (3.1) maintains a set containing each component
that it meets. Adding a component preserves this condition. If its start
vertex was outside the old set, the added component is disjoint from that
set, so their terminal counts add without duplication.
-/

public section
namespace GraphMinor.Compute
open Classical
variable {n : ℕ} (G : SimpleGraph (Fin n)) (X Y : Finset (Fin n))

/-- A deleted component contains the whole component of each of its vertices. -/
theorem gm02FiniteComponent_closed (a : Fin n) :
    ∀ b ∈ gm02FiniteComponent G X a, gm02FiniteComponent G X b ⊆ gm02FiniteComponent G X a := by
  intro b hb
  rw [gm02FiniteComponent_eq_of_mem G X a b hb]

/-- Unions of component-closed sets remain component-closed. -/
theorem gm02Union_closed {Z : Finset (Fin n)}
    (hY : ∀ a ∈ Y, gm02FiniteComponent G X a ⊆ Y)
    (hZ : ∀ a ∈ Z, gm02FiniteComponent G X a ⊆ Z) :
    ∀ a ∈ Y ∪ Z, gm02FiniteComponent G X a ⊆ Y ∪ Z := by
  intro a ha b hb
  rcases Finset.mem_union.1 ha with haY | haZ
  · exact Finset.mem_union_left _ (hY a haY hb)
  · exact Finset.mem_union_right _ (hZ a haZ hb)

/-- A component starting outside a closed set cannot meet that set. -/
theorem gm02FiniteComponent_disjoint_closed (a : Fin n) (haX : a ∉ X) (haY : a ∉ Y)
    (hclosed : ∀ b ∈ Y, gm02FiniteComponent G X b ⊆ Y) :
    Disjoint Y (gm02FiniteComponent G X a) := by
  apply Finset.disjoint_left.2
  intro b hbY hbC
  have he := gm02FiniteComponent_eq_of_mem G X a b hbC
  have haC : a ∈ gm02FiniteComponent G X b := he.symm ▸ self_mem_gm02FiniteComponent G X a haX
  exact haY (hclosed b hbY haC)

/-- Terminal counts add when a new component starts outside a closed side. -/
theorem gm02Union_component_count (Q : Finset (Fin n)) (a : Fin n)
    (haX : a ∉ X) (haY : a ∉ Y)
    (hclosed : ∀ b ∈ Y, gm02FiniteComponent G X b ⊆ Y) :
    ((Y ∪ gm02FiniteComponent G X a) ∩ Q).card =
      (Y ∩ Q).card + (gm02FiniteComponent G X a ∩ Q).card := by
  rw [Finset.union_inter_distrib_right]
  apply Finset.card_union_of_disjoint
  exact (gm02FiniteComponent_disjoint_closed G X Y a haX haY hclosed).mono
    Finset.inter_subset_left Finset.inter_subset_left

/-- Two terminal weights below a third have combined weight below two thirds. -/
theorem gm02SmallComponent_union_bound (Q : Finset (Fin n)) (a : Fin n)
    (haX : a ∉ X) (haY : a ∉ Y)
    (hclosed : ∀ b ∈ Y, gm02FiniteComponent G X b ⊆ Y)
    (hY : 3 * (Y ∩ Q).card < (Q \ X).card)
    (hC : 3 * (gm02FiniteComponent G X a ∩ Q).card < (Q \ X).card) :
    3 * ((Y ∪ gm02FiniteComponent G X a) ∩ Q).card < 2 * (Q \ X).card := by
  rw [gm02Union_component_count G X Y Q a haX haY hclosed]
  omega

end GraphMinor.Compute
