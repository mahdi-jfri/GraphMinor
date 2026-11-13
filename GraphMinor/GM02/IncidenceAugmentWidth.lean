module

public import GraphMinor.GM02.IncidenceAugmentBags
import GraphMinor.GM02.IncidenceAugmentDelete
import GraphMinor.GM02.AttachVertexDecomposition

/-!
# Width of the incidence augmentation

Add the selected edge vertices one at a time. The original edge's ends
occur together in an existing bag. Attach a leaf bag containing those
two ends and the new edge vertex. Its size is at most three, so the
augmentation has width at most the larger of the old width and two.
-/

public section
namespace GraphMinor.GM02
open Graph Set Classical
universe u v

/-- Adding vertices on finitely many host edges costs no width above two. -/
theorem incidenceAugment_treeWidthLE {α : Type u} {β : Type v}
    (G : Graph α β) (w : ℕ) (hW : TreeWidthLE G w)
    (S : Set β) (hS : S.Finite) (hSE : S ⊆ E(G)) :
    TreeWidthLE (incidenceAugment G S) (max w 2) := by
  revert hSE
  induction S, hS using Set.Finite.induction_on with
  | empty =>
    intro _
    obtain ⟨ι, hι, T, X, hD, hw⟩ := incidenceAugment_empty_treeWidthLE G w hW
    exact ⟨ι, hι, T, X, hD, fun i => (hw i).trans (Nat.add_le_add_right (Nat.le_max_left w 2) 1)⟩
  | @insert e S he hS ih =>
    intro hSE
    have heG : e ∈ E(G) := hSE (Or.inl rfl)
    obtain ⟨a, b, hab⟩ := G.exists_isLink_of_mem_edgeSet heG
    obtain ⟨ι, hι, T, X, hD, hw⟩ := ih (fun f hf => hSE (Or.inr hf))
    let : Fintype ι := hι
    obtain ⟨t₀, ha, hb⟩ := incidenceAugment_ends_in_bag G S hD hab
    have hB : ({Sum.inl a, Sum.inl b} : Set (α ⊕ β)) ⊆ X t₀ := by
      intro y hy
      rcases hy with hy | hy
      · exact hy ▸ ha
      · exact (Set.mem_singleton_iff.1 hy) ▸ hb
    have hDel := incidenceAugment_delete_vertex G S e he
    have hDdel : IsTreeDecomposition ((incidenceAugment G (insert e S)).deleteVerts {Sum.inr e}) T X :=
      hDel.symm ▸ hD
    have hv : Sum.inr e ∈ V(incidenceAugment G (insert e S)) :=
      Or.inr ⟨e, Or.inl rfl, rfl⟩
    have hNew := attachVertex_isTreeDecomposition hv hDdel t₀ {Sum.inl a, Sum.inl b} hB
      (incidenceAugment_neighbors G (insert e S) hab)
    refine ⟨Option ι, inferInstance, GM10.attachLeaf T t₀, _, hNew, ?_⟩
    intro t
    cases t with
    | some t => exact hw t
    | none =>
      have hpair : ({Sum.inl a, Sum.inl b} : Set (α ⊕ β)).ncard ≤ 2 := by
        simpa only [Set.ncard_singleton] using Set.ncard_insert_le (Sum.inl a : α ⊕ β) {Sum.inl b}
      have hcard := Set.ncard_insert_le (Sum.inr e : α ⊕ β) {Sum.inl a, Sum.inl b}
      have hmax : 2 ≤ max w 2 := Nat.le_max_right w 2
      exact hcard.trans ((Nat.add_le_add_right hpair 1).trans (Nat.add_le_add_right hmax 1))

end GraphMinor.GM02
