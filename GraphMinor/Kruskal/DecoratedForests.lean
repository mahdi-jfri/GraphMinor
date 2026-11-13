module

public import GraphMinor.Kruskal.DecoratedEmbeddings

/-!
# Explicit address maps for labelled forests

Higman's extension of labelled Kruskal matches a finite list of source
components to distinct target components. Converting that matching to
indices gives an address embedding for each component, with comparisons
of all its prescribed vertex labels. Component counts may vary along
the sequence.
-/

public section

namespace GraphMinor.Kruskal

open LabelledTree

/-- Sequences of finite labelled forests have a pair with injectively
matched component indices and label-preserving address embeddings. -/
theorem exists_labelled_forest_addressEmbedding {L : Type*} {r : L → L → Prop}
    [IsPreorder L r] (hr : WellQuasiOrdered r) (n : ℕ → ℕ)
    (t : ∀ i, Fin (n i) → OrderedTree) (f : ∀ i, Fin (n i) → List ℕ → L) :
    ∃ i j, i < j ∧ ∃ σ : Fin (n i) ↪ Fin (n j),
      ∀ k, ∃ φ : OrderedTree.AddressEmbedding (t i k) (t j (σ k)),
        ∀ p, r (f i k p.val) (f j (σ k) (φ.vertices p).val) := by
  obtain ⟨i, j, hij, he⟩ := LabelledTree.wellQuasiOrdered_forestEmbeds hr
    (fun i ↦ List.ofFn fun k : Fin (n i) ↦ decorate (t i k) (f i k))
  obtain ⟨ψ⟩ := LabelledTree.exists_branchAddressEmbedding he
  let σ : Fin (n i) ↪ Fin (n j) := {
    toFun k := ⟨(ψ.indices ⟨k.val, by simpa only [List.length_ofFn] using k.isLt⟩).val,
      by simpa only [List.length_ofFn] using
        (ψ.indices ⟨k.val, by simpa only [List.length_ofFn] using k.isLt⟩).isLt⟩
    inj' := by
      intro k l hkl
      have heq : ψ.indices ⟨k.val, by simpa only [List.length_ofFn] using k.isLt⟩ =
          ψ.indices ⟨l.val, by simpa only [List.length_ofFn] using l.isLt⟩ :=
        Fin.ext (congrArg (fun z : Fin (n j) ↦ z.val) hkl)
      exact Fin.ext (congrArg
        (fun z : Fin (List.ofFn fun k : Fin (n i) ↦ decorate (t i k) (f i k)).length ↦ z.val)
        (ψ.indices.injective heq)) }
  refine ⟨i, j, hij, σ, ?_⟩
  intro k
  let k' : Fin (List.ofFn fun k : Fin (n i) ↦ decorate (t i k) (f i k)).length :=
    ⟨k.val, by simpa only [List.length_ofFn] using k.isLt⟩
  have φ : LabelledTree.AddressEmbedding r (decorate (t i k) (f i k))
      (decorate (t j (σ k)) (f j (σ k))) := by
    have hφ := ψ.branches k'
    simp only [Fin.getElem_fin, List.getElem_ofFn] at hφ
    exact hφ
  exact exists_addressEmbedding_of_decoratedAddress φ

end GraphMinor.Kruskal
