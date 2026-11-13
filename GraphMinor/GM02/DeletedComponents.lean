module

public import GraphMinor.GM02.BranchRegions

/-!
# The components after a separator is removed

For II (2.6), list the distinct component vertex sets of the graph after
deleting the separator. They form a finite disjoint cover of the remaining
vertices. A walk between two remaining vertices puts them in the same
member of this cover.
-/

@[expose] public section
namespace GraphMinor.GM02
open Graph Set Relation Classical
universe u v

/-- Component vertex sets after deleting a set, without repeated sets. -/
noncomputable def deletedComponents {α : Type u} {β : Type v}
    (G : Graph α β) (X : Set α) (hG : (V(G)).Finite) : Finset (Set α) :=
  (hG.sdiff (t := X)).toFinset.image (deletedComponent G X)

/-- Two remaining vertices joined by a walk have the same component. -/
theorem deletedComponent_eq_of_reachable {α : Type u} {β : Type v}
    {G : Graph α β} {X : Set α} {a b : α}
    (hp : ReflTransGen (G.induce (V(G) \ X)).Adj a b) :
    deletedComponent G X a = deletedComponent G X b := by
  have hrev := (inferInstance : Std.Symm (ReflTransGen (G.induce (V(G) \ X)).Adj)).symm _ _ hp
  ext z
  exact ⟨fun hz => ⟨hz.1, hrev.trans hz.2⟩, fun hz => ⟨hz.1, hp.trans hz.2⟩⟩

/-- Distinct components after deletion are disjoint. -/
theorem deletedComponents_disjoint {α : Type u} {β : Type v}
    {G : Graph α β} {X : Set α} (hG : (V(G)).Finite) :
    ∀ A ∈ deletedComponents G X hG, ∀ B ∈ deletedComponents G X hG,
      A ≠ B → Disjoint A B := by
  intro A hA B hB hne
  obtain ⟨a, _, rfl⟩ := Finset.mem_image.1 hA
  obtain ⟨b, _, rfl⟩ := Finset.mem_image.1 hB
  apply Set.disjoint_left.2
  intro z ha hb
  have hea := deletedComponent_eq_of_reachable ha.2
  have heb := deletedComponent_eq_of_reachable hb.2
  exact hne (hea.trans heb.symm)

/-- All and only the remaining vertices occur in the components. -/
theorem deletedComponents_cover {α : Type u} {β : Type v}
    {G : Graph α β} {X : Set α} (hG : (V(G)).Finite) :
    (⋃ C ∈ deletedComponents G X hG, C) = V(G) \ X := by
  ext a
  constructor
  · intro ha
    obtain ⟨C, hC⟩ := Set.mem_iUnion.1 ha
    obtain ⟨hC, haC⟩ := Set.mem_iUnion.1 hC
    obtain ⟨b, _, rfl⟩ := Finset.mem_image.1 hC
    exact haC.1
  · intro ha
    apply Set.mem_iUnion.2 ⟨deletedComponent G X a, ?_⟩
    apply Set.mem_iUnion.2
    refine ⟨Finset.mem_image.2 ⟨a, ?_, rfl⟩, ha, ReflTransGen.refl⟩
    exact (hG.sdiff (t := X)).mem_toFinset.2 ha

/-- A remaining vertex belongs to exactly its own component. -/
theorem deletedComponent_eq_of_mem {α : Type u} {β : Type v}
    {G : Graph α β} {X C : Set α} (hG : (V(G)).Finite)
    (hC : C ∈ deletedComponents G X hG) {a : α} (ha : a ∈ C) :
    deletedComponent G X a = C := by
  obtain ⟨b, _, rfl⟩ := Finset.mem_image.1 hC
  exact (deletedComponent_eq_of_reachable ha.2).symm

end GraphMinor.GM02
