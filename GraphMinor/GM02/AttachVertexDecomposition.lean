module

public import GraphMinor.GM02.TreeDecomposition
public import GraphMinor.GM10.TreeWidthBasic

/-!
# A leaf bag for a new vertex

To add a vertex whose neighbors lie in one old bag, attach a new leaf
bag containing that vertex and its neighbors. The old bags are unchanged.
A vertex appearing in both the new bag and an old bag also appears in
the attachment bag, so the tree-path condition persists. This supplies
the leaf bags for edge vertices in the corrected split construction.
-/

public section
namespace GraphMinor.GM02
open Graph Set Classical
universe u v w

/-- Attach a leaf bag for a vertex whose neighbors lie in a single existing bag. -/
theorem attachVertex_isTreeDecomposition {α : Type u} {β : Type v} {ι : Type w}
    [Fintype ι] {G : Graph α β} {v : α} (hv : v ∈ V(G)) {T : SimpleGraph ι} {X : ι → Set α}
    (hD : IsTreeDecomposition (G.deleteVerts {v}) T X)
    (t₀ : ι) (B : Set α) (hB : B ⊆ X t₀)
    (hneigh : ∀ e x, G.IsLink e v x → x ∈ B) :
    IsTreeDecomposition G (GM10.attachLeaf T t₀) (fun t : Option ι => t.elim (insert v B) X) := by
  have hXV : ∀ t, X t ⊆ V(G) \ {v} := by
    intro t y hy
    have hm : y ∈ V(G.deleteVerts {v}) := hD.iUnion_eq ▸ Set.mem_iUnion.2 ⟨t, hy⟩
    simpa only [Graph.vertexSet_deleteVerts] using hm
  have hvnot : ∀ t, v ∉ X t := fun t h => (hXV t h).2 rfl
  have hBV : B ⊆ V(G) := fun y hy => (hXV t₀ (hB hy)).1
  refine ⟨GM10.isTree_attachLeaf hD.isTree t₀, ?_, ?_, ?_⟩
  · ext y
    simp only [Set.mem_iUnion]
    constructor
    · rintro ⟨t, ht⟩
      cases t with
      | none => exact ht.elim (fun h => h ▸ hv) (fun h => hBV h)
      | some t => exact (hXV t ht).1
    · intro hy
      by_cases hyv : y = v
      · exact ⟨none, Or.inl hyv⟩
      · have hy' : y ∈ V(G.deleteVerts {v}) := by
          rw [Graph.vertexSet_deleteVerts]
          exact ⟨hy, hyv⟩
        rw [← hD.iUnion_eq] at hy'
        obtain ⟨t, ht⟩ := Set.mem_iUnion.1 hy'
        exact ⟨some t, ht⟩
  · intro e a b hab
    by_cases hav : a = v
    · subst a
      exact ⟨none, Or.inl rfl, Or.inr (hneigh e b hab)⟩
    · by_cases hbv : b = v
      · subst b
        exact ⟨none, Or.inr (hneigh e a hab.symm), Or.inl rfl⟩
      · have hret : (G.deleteVerts {v}).IsLink e a b := (Graph.deleteVerts_isLink G {v}).2 ⟨hab, hav, hbv⟩
        obtain ⟨t, hat, hbt⟩ := hD.edge_mem hret
        exact ⟨some t, hat, hbt⟩
  · intro a t b hp y hy
    cases t with
    | none =>
      have he := GM10.eq_or_eq_of_onTreePath_of_unique_adj
        (GM10.isTree_attachLeaf hD.isTree t₀).connected
        (fun w₁ w₂ h₁ h₂ =>
          (GM10.adj_attachLeaf_none_iff.1 h₁).trans (GM10.adj_attachLeaf_none_iff.1 h₂).symm) hp
      rcases he with he | he
      · subst a; exact hy.1
      · subst b; exact hy.2
    | some t =>
      have hp' := GM10.onTreePath_projAttach_of_some hp
      cases a with
      | none =>
        cases b with
        | none =>
          have he := GM10.onTreePath_self_iff.1 hp
          cases he
        | some b =>
          apply hD.inter_subset hp'
          exact ⟨hB (hy.1.resolve_left (fun he => hvnot b (he ▸ hy.2))), hy.2⟩
      | some a =>
        cases b with
        | none =>
          apply hD.inter_subset hp'
          exact ⟨hy.1, hB (hy.2.resolve_left (fun he => hvnot a (he ▸ hy.1)))⟩
        | some b => exact hD.inter_subset hp' hy

end GraphMinor.GM02
