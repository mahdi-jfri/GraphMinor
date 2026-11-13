module

public import GraphMinor.GM05.ExpansionBags
import GraphMinor.GM05.SubtreeSelection
import GraphMinor.GM05.SubtreeTransversal

/-!
# Packing connected families or hitting one family

This is the tree-decomposition step in Graph Minors V, proof of (8.8),
pages 111–112. For each family, consider the subtrees of bags meeting its
members. If every family packs `m*k` such subtrees, (8.6) selects `k` per
family, all disjoint. Otherwise (8.7) hits one family's subtrees with fewer
than `m*k` tree vertices. The union of their bags hits that whole family.
-/

public section

namespace GraphMinor.GM05

open Graph Set SimpleGraph
open scoped BigOperators

/-- The combined use of Graph Minors V, (8.6) and (8.7), in the proof of
(8.8), pages 111–112. For `m` families of connected subgraphs in a graph
of width at most `w`, either one can pack `k` members of each family all
disjoint, or `(m*k-1)*(w+1)` vertices meet every member of one family. -/
theorem lemma_8_8_pack_families_or_hit {α β : Type*} {G : Graph α β} {m k w : ℕ}
    (F : Fin m → Set (Graph α β))
    (hF : ∀ i C, C∈F i → C≤G ∧ GraphConnected C)
    (hw : TreeWidthLE (simpleShadow G) w) :
    (∃ C : Fin m → Fin k → Graph α β, (∀ i a,C i a∈F i) ∧
      Pairwise (fun p q : (_ : Fin m) × Fin k ↦ Disjoint V(C p.1 p.2) V(C q.1 q.2))) ∨
      ∃ i X, X⊆V(G) ∧ X.ncard≤(m*k-1)*(w+1) ∧ ∀ C∈F i,(X∩V(C)).Nonempty := by
  classical
  obtain ⟨ι,_,T,χ,htd,hwidth⟩ := hw
  let A (i : Fin m) : Set (Set ι) := {S | ∃ C∈F i,S=bagMeetingSet χ C}
  have hA : ∀ i S, S∈A i → (T.induce S).Connected := by
    rintro i S ⟨C,hC,rfl⟩
    exact bagMeetingSet_connected htd (hF i C hC).1 (hF i C hC).2
  by_cases hpack : ∀ i, ∃ S : Fin (m*k) → Set ι, (∀ a,S a∈A i) ∧
      Pairwise (fun a b ↦ Disjoint (S a) (S b))
  · obtain ⟨B,hB,hdisj⟩ := theorem_8_6_proof htd.isTree A hA (fun _ ↦ k) (by simp) hpack
    have hex : ∀ i a, ∃ C∈F i,B i a=bagMeetingSet χ C := hB
    choose C hC hBC using hex
    left
    refine ⟨C,hC,?_⟩
    intro p q hpq
    have hd := hdisj hpq
    change Disjoint (B p.1 p.2) (B q.1 q.2) at hd
    rw [hBC p.1 p.2,hBC q.1 q.2] at hd
    exact disjoint_vertices_of_disjoint_bagMeetingSet htd (hF p.1 _ (hC p.1 p.2)).1 hd
  · obtain ⟨i,hi⟩ := not_forall.mp hpack
    rcases theorem_8_7_proof htd.isTree (A i) (hA i) (m*k) with hpacki|hhit
    · exact (hi hpacki).elim
    · obtain ⟨Y,hY,hmeet⟩ := hhit
      let X := ⋃ t∈Y,χ t
      obtain ⟨hX,hsize⟩ := union_bags_bound htd hwidth Y
      right
      refine ⟨i,X,hX,hsize.trans (Nat.mul_le_mul_right (w+1) (by omega)),?_⟩
      intro C hC
      obtain ⟨t,htY,htC⟩ := hmeet (bagMeetingSet χ C) ⟨C,hC,rfl⟩
      obtain ⟨x,hxχ,hxC⟩ := htC
      exact ⟨x,mem_iUnion₂.mpr ⟨t,htY,hxχ⟩,hxC⟩

end GraphMinor.GM05
