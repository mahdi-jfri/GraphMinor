module

public import GraphMinor.GM02.IncidenceAugment

/-!
# Bags for the incidence augmentation

The empty augmentation has the old bags with vertex names copied into
the left summand. Because the original edges are retained, their two
ends still occur together in a bag after other edge vertices are added.
The new edge vertex has no neighbors outside those two ends.
-/

public section
namespace GraphMinor.GM02
open Graph Set Classical
universe u v w

/-- Copying vertex names gives a decomposition of the empty augmentation with the same width. -/
theorem incidenceAugment_empty_treeWidthLE {α : Type u} {β : Type v}
    (G : Graph α β) (w : ℕ) (hW : TreeWidthLE G w) : TreeWidthLE (incidenceAugment G ∅) w := by
  obtain ⟨ι, hι, T, X, hD, hw⟩ := hW
  let X' : ι → Set (α ⊕ β) := fun i => Sum.inl '' X i
  have hXV : ∀ i, X i ⊆ V(G) := fun i => hD.iUnion_eq ▸ Set.subset_iUnion X i
  refine ⟨ι, hι, T, X', ⟨hD.isTree, ?_, ?_, ?_⟩, ?_⟩
  · apply Set.Subset.antisymm
    · intro a ha
      obtain ⟨i, y, hy, rfl⟩ := Set.mem_iUnion.1 ha
      exact Or.inl ⟨y, hXV i hy, rfl⟩
    · rintro a (⟨y, hy, rfl⟩ | ⟨e, he, _⟩)
      · rw [← hD.iUnion_eq] at hy
        obtain ⟨i, hi⟩ := Set.mem_iUnion.1 hy
        exact Set.mem_iUnion.2 ⟨i, y, hi, rfl⟩
      · exact he.elim
  · intro e a b hab
    have hr := (incidenceAugment_isLink_iff G ∅ e a b).1 hab |>.2.2.2
    rcases a with a | f <;> rcases b with b | g
    · obtain ⟨c, hc⟩ := hr.2
      obtain ⟨i, hai, hbi⟩ := hD.edge_mem hc
      exact ⟨i, ⟨a, hai, rfl⟩, ⟨b, hbi, rfl⟩⟩
    · exact hr.1.elim
    · exact hr.1.elim
    · exact hr.elim
  · intro i j k hp a ha
    obtain ⟨y, hy, rfl⟩ := ha.1
    obtain ⟨z, hz, hzy⟩ := ha.2
    have heq : z = y := Sum.inl.inj hzy
    subst z
    exact ⟨y, hD.inter_subset hp ⟨hy, hz⟩, rfl⟩
  · intro i
    exact (Set.ncard_image_of_injective (X i) Sum.inl_injective).le.trans (hw i)

/-- The ends of every original host edge still occur together in an augmentation bag. -/
theorem incidenceAugment_ends_in_bag {α : Type u} {β : Type v} {ι : Type w}
    (G : Graph α β) (S : Set β) {T : SimpleGraph ι} {X : ι → Set (α ⊕ β)}
    (hD : IsTreeDecomposition (incidenceAugment G S) T X)
    {e : β} {a b : α} (hab : G.IsLink e a b) :
    ∃ i, Sum.inl a ∈ X i ∧ Sum.inl b ∈ X i := by
  by_cases heq : a = b
  · subst b
    have ha : Sum.inl a ∈ V(incidenceAugment G S) := Or.inl ⟨a, hab.left_mem, rfl⟩
    rw [← hD.iUnion_eq] at ha
    obtain ⟨i, hi⟩ := Set.mem_iUnion.1 ha
    exact ⟨i, hi, hi⟩
  · apply hD.edge_mem
    apply (incidenceAugment_isLink_iff G S s(Sum.inl a, Sum.inl b) _ _).2
    exact ⟨rfl, Or.inl ⟨a, hab.left_mem, rfl⟩, Or.inl ⟨b, hab.right_mem, rfl⟩, heq, ⟨e, hab⟩⟩

/-- An edge vertex has neighbors only among the two original ends of its host edge. -/
theorem incidenceAugment_neighbors {α : Type u} {β : Type v} (G : Graph α β) (S : Set β)
    {e : β} {a b : α} (hab : G.IsLink e a b) :
    ∀ f x, (incidenceAugment G S).IsLink f (Sum.inr e) x → x ∈ ({Sum.inl a, Sum.inl b} : Set (α ⊕ β)) := by
  intro f x hfx
  have hr := (incidenceAugment_isLink_iff G S f (Sum.inr e) x).1 hfx |>.2.2.2
  rcases x with y | g
  · rcases hr.2.eq_or_eq_of_isLink hab with h | h
    · exact Or.inl (congrArg Sum.inl h)
    · exact Or.inr (congrArg Sum.inl h)
  · exact hr.elim

end GraphMinor.GM02
