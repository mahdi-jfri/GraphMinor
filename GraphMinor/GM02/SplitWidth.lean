module

public import GraphMinor.GM02.TreeDecomposition

/-!
# Adding all split terminals to each bag

Delete the branch vertices from the old bags, copy the remaining
vertices, and add all split terminals to every bag. Edges with a terminal
end are then covered by any bag containing the other end. Old edges use
the old edge-cover condition. This is the bag argument of II (4.4),
applied also to the corrected split graph in (4.6).
-/

public section
namespace GraphMinor.GM02
open Graph Set Classical
universe u v v'

private theorem old_mem_expandedBag {A : Type*} {k : ℕ} (S : Set A) (a : A) :
    (Sum.inl a : A ⊕ (Fin k × Bool)) ∈ Sum.inl '' S ∪ range Sum.inr ↔ a ∈ S := by
  simp

private theorem expandedBag_ncard_le {A : Type*} {k : ℕ} (S : Set A) :
    (Sum.inl '' S ∪ range (Sum.inr : Fin k × Bool → A ⊕ (Fin k × Bool))).ncard ≤
      S.ncard + 2 * k := by
  refine (Set.ncard_union_le _ _).trans ?_
  rw [Set.ncard_image_of_injective _ Sum.inl_injective]
  have hr : (range (Sum.inr : Fin k × Bool → A ⊕ (Fin k × Bool))).ncard = 2 * k := by
    rw [← Set.image_univ, Set.ncard_image_of_injective _ Sum.inr_injective, Set.ncard_univ,
      Nat.card_eq_fintype_card, Fintype.card_prod, Fintype.card_fin, Fintype.card_bool, Nat.mul_comm]
  rw [hr]

/-- The bag argument of II (4.4) applies whenever old adjacencies are retained and all new vertices are split terminals. -/
theorem treeWidthLE_split_bound {A : Type u} {B : Type v} {C : Type v'} {k w : ℕ}
    (G : Graph A B) (F : Graph (A ⊕ (Fin k × Bool)) C) (D : Set A)
    (hV : V(G).Finite)
    (hFV : V(F) = Sum.inl '' (V(G) \ D) ∪ range Sum.inr)
    (hAdj : ∀ a b, F.Adj (Sum.inl a) (Sum.inl b) → G.Adj a b)
    (hW : TreeWidthLE G w) : TreeWidthLE F (w + 2 * k) := by
  obtain ⟨ι, hι, T, X, hD, hw⟩ := hW
  let : Nonempty ι := hD.isTree.connected.nonempty
  have hXV : ∀ i, X i ⊆ V(G) := fun i => hD.iUnion_eq ▸ Set.subset_iUnion X i
  let X' : ι → Set (A ⊕ (Fin k × Bool)) := fun i => Sum.inl '' (X i \ D) ∪ range Sum.inr
  have hinr : ∀ i p, (Sum.inr p : A ⊕ (Fin k × Bool)) ∈ X' i := fun _ p => Or.inr ⟨p, rfl⟩
  have hcover : ∀ a ∈ V(F), ∃ i, a ∈ X' i := by
    intro a ha
    rw [hFV] at ha
    rcases ha with ⟨y, ⟨hyG, hyD⟩, rfl⟩ | ⟨p, rfl⟩
    · rw [← hD.iUnion_eq] at hyG
      obtain ⟨i, hi⟩ := Set.mem_iUnion.1 hyG
      exact ⟨i, Or.inl ⟨y, ⟨hi, hyD⟩, rfl⟩⟩
    · exact ⟨Classical.arbitrary ι, hinr _ p⟩
  refine ⟨ι, hι, T, X', ⟨hD.isTree, ?_, ?_, ?_⟩, ?_⟩
  · apply Set.Subset.antisymm
    · intro a ha
      obtain ⟨i, hi⟩ := Set.mem_iUnion.1 ha
      rw [hFV]
      rcases hi with ⟨y, ⟨hy, hyD⟩, rfl⟩ | ⟨p, rfl⟩
      · exact Or.inl ⟨y, ⟨hXV i hy, hyD⟩, rfl⟩
      · exact Or.inr ⟨p, rfl⟩
    · intro a ha
      obtain ⟨i, hi⟩ := hcover a ha
      exact Set.mem_iUnion.2 ⟨i, hi⟩
  · intro e a b hab
    rcases a with a | p <;> rcases b with b | q
    · obtain ⟨f, hf⟩ := hAdj a b ⟨e, hab⟩
      obtain ⟨i, hai, hbi⟩ := hD.edge_mem hf
      have ha := hab.left_mem
      have hb := hab.right_mem
      rw [hFV, old_mem_expandedBag] at ha hb
      exact ⟨i, Or.inl ⟨a, ⟨hai, ha.2⟩, rfl⟩, Or.inl ⟨b, ⟨hbi, hb.2⟩, rfl⟩⟩
    · obtain ⟨i, hi⟩ := hcover _ hab.left_mem
      exact ⟨i, hi, hinr i q⟩
    · obtain ⟨i, hi⟩ := hcover _ hab.right_mem
      exact ⟨i, hinr i p, hi⟩
    · exact ⟨Classical.arbitrary ι, hinr _ p, hinr _ q⟩
  · intro i j l hp a ha
    rcases a with a | p
    · have hi := (old_mem_expandedBag (X i \ D) a).1 ha.1
      have hl := (old_mem_expandedBag (X l \ D) a).1 ha.2
      exact (old_mem_expandedBag (X j \ D) a).2 ⟨hD.inter_subset hp ⟨hi.1, hl.1⟩, hi.2⟩
    · exact hinr j p
  · intro i
    have h₁ := expandedBag_ncard_le (k := k) (X i \ D)
    have h₂ := Set.ncard_le_ncard (Set.sdiff_subset : X i \ D ⊆ X i) (hV.subset (hXV i))
    have h₃ := hw i
    exact h₁.trans ((Nat.add_le_add_right h₂ _).trans (by omega))

end GraphMinor.GM02
