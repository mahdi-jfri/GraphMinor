module

public import GraphMinor.GM08.Defs

/-!
# Adding one leaf at each graft root

To put a cylinder drawing's hoops off its boundary, add a collar and
extend each root to a new leaf on the new boundary. The old vertices
and edges retain their labels in the left summands. The right summands
label the new leaves and their incident edges by the original roots.
This file gives the finite graft for that construction in the deduction
of VIII (17.2) from VII (9.3).
-/

@[expose] public section

namespace GraphMinor.GM08

open Set Graph

universe u v

/-- The links after adding a new leaf at every root. Old edges have
their original ends, and the new edge labelled by a root joins its
old vertex to its new leaf. This is the collar construction for
VIII (17.2), page 284. -/
def rootLeafLink {α : Type u} {β : Type v} (X : Graft α β) :
    β ⊕ α → α ⊕ α → α ⊕ α → Prop
  | .inl e, .inl x, .inl y => X.G.IsLink e x y
  | .inr t, .inl x, .inr y => t ∈ X.T ∧ x = t ∧ y = t
  | .inr t, .inr y, .inl x => t ∈ X.T ∧ x = t ∧ y = t
  | _, _, _ => False

/-- Add a single pendant edge and leaf at each root, using disjoint
summands for all new labels. This graph is used to extend roots through
a collar in the proof of VIII (17.2). -/
def rootLeafGraph {α : Type u} {β : Type v} (X : Graft α β) :
    Graph (α ⊕ α) (β ⊕ α) where
  vertexSet := Sum.inl '' V(X.G) ∪ Sum.inr '' X.T
  edgeSet := Sum.inl '' E(X.G) ∪ Sum.inr '' X.T
  IsLink := rootLeafLink X
  isLink_symm := by
    intro e he
    refine ⟨?_⟩
    intro x y h
    cases e <;> cases x <;> cases y <;> simp only [rootLeafLink] at h ⊢
    · exact h.symm
    · exact h
    · exact h
  eq_or_eq_of_isLink_of_isLink := by
    intro e x y z w h h'
    cases e <;> cases x <;> cases y <;> cases z <;> cases w <;>
      simp only [rootLeafLink] at h h' ⊢
    · exact (h.left_eq_or_eq h').imp (congrArg Sum.inl) (congrArg Sum.inl)
    all_goals simp_all
  edge_mem_iff_exists_isLink := by
    intro e
    cases e with
    | inl e =>
      constructor
      · intro he
        have heG : e ∈ E(X.G) := by simpa using he
        obtain ⟨x, y, hl⟩ := X.G.exists_isLink_of_mem_edgeSet heG
        exact ⟨.inl x, .inl y, hl⟩
      · rintro ⟨x, y, hl⟩
        cases x <;> cases y <;> simp only [rootLeafLink] at hl
        exact .inl (mem_image_of_mem Sum.inl hl.edge_mem)
    | inr t =>
      constructor
      · intro ht
        have htT : t ∈ X.T := by simpa using ht
        exact ⟨.inl t, .inr t, htT, rfl, rfl⟩
      · rintro ⟨x, y, hl⟩
        cases x <;> cases y <;> simp only [rootLeafLink] at hl
        all_goals exact .inr (mem_image_of_mem Sum.inr hl.1)
  left_mem_of_isLink := by
    intro e x y h
    cases e <;> cases x <;> cases y <;> simp only [rootLeafLink] at h
    · exact .inl (mem_image_of_mem Sum.inl h.left_mem)
    · exact .inl (mem_image_of_mem Sum.inl (h.2.1.symm ▸ X.T_subset h.1))
    · exact .inr (mem_image_of_mem Sum.inr (h.2.2.symm ▸ h.1))

/-- The graft obtained by adding one leaf at each root, and taking the
new leaves as its roots. It has the same number of roots as the original
graft, as required for the collar construction in VIII (17.2). -/
def rootLeafGraft {α : Type u} {β : Type v} (X : Graft α β) :
    Graft (α ⊕ α) (β ⊕ α) where
  G := rootLeafGraph X
  T := Sum.inr '' X.T
  T_subset := subset_union_right
  finite_G := by
    have hT := X.finite_G.1.subset X.T_subset
    exact ⟨(X.finite_G.1.image Sum.inl).union (hT.image Sum.inr),
      (X.finite_G.2.image Sum.inl).union (hT.image Sum.inr)⟩

@[simp] theorem inl_mem_rootLeafGraph_vertexSet {α : Type u} {β : Type v}
    (X : Graft α β) (x : α) : Sum.inl x ∈ V(rootLeafGraph X) ↔ x ∈ V(X.G) := by
  simp [rootLeafGraph]

@[simp] theorem inr_mem_rootLeafGraph_vertexSet {α : Type u} {β : Type v}
    (X : Graft α β) (x : α) : Sum.inr x ∈ V(rootLeafGraph X) ↔ x ∈ X.T := by
  simp [rootLeafGraph]

@[simp] theorem inl_mem_rootLeafGraph_edgeSet {α : Type u} {β : Type v}
    (X : Graft α β) (e : β) : Sum.inl e ∈ E(rootLeafGraph X) ↔ e ∈ E(X.G) := by
  simp [rootLeafGraph]

@[simp] theorem inr_mem_rootLeafGraph_edgeSet {α : Type u} {β : Type v}
    (X : Graft α β) (x : α) : Sum.inr x ∈ E(rootLeafGraph X) ↔ x ∈ X.T := by
  simp [rootLeafGraph]

@[simp] theorem inl_not_mem_rootLeafGraft_roots {α : Type u} {β : Type v}
    (X : Graft α β) (x : α) : Sum.inl x ∉ (rootLeafGraft X).T := by
  simp [rootLeafGraft]

@[simp] theorem inr_mem_rootLeafGraft_roots {α : Type u} {β : Type v}
    (X : Graft α β) (x : α) : Sum.inr x ∈ (rootLeafGraft X).T ↔ x ∈ X.T := by
  simp [rootLeafGraft]

/-- Extending each root to a new leaf preserves the graft index. -/
theorem rootLeafGraft_index {α : Type u} {β : Type v} (X : Graft α β) :
    (rootLeafGraft X).index = X.index := by
  exact ncard_image_of_injective X.T Sum.inr_injective

end GraphMinor.GM08
