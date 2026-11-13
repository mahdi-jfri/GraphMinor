module

public import GraphMinor.Kruskal.DecorateTree
public import GraphMinor.Kruskal.LabelledEmbeddingAddresses

/-!
# Comparing prescribed labels on tree addresses

Decorate the trees, apply labelled Kruskal, and transfer the resulting
address map back to the original shapes. The transfer does not change
any address values, so the comparisons hold for the prescribed labels.
-/

public section

namespace GraphMinor.Kruskal

open LabelledTree

/-- A recursive embedding of decorated trees yields an address map which
compares the prescribed labels on the original trees. -/
theorem exists_addressEmbedding_of_decoratedAddress {L : Type*} {r : L → L → Prop}
    {s t : OrderedTree} {f g : List ℕ → L}
    (φ : LabelledTree.AddressEmbedding r (decorate s f) (decorate t g)) :
    ∃ φ : OrderedTree.AddressEmbedding s t,
      ∀ p, r (f p.val) (g (φ.vertices p).val) := by
  let ψ := φ.underlying.changeTrees (shape_decorate s f) (shape_decorate t g)
  refine ⟨ψ, ?_⟩
  intro p
  let p' : {p // p ∈ (decorate s f).shape.addresses} :=
    ⟨p.val, by simpa only [shape_decorate] using p.property⟩
  have hlabel := φ.labels p'
  have hp : p'.val ∈ s.addresses := p.property
  have hq : (φ.underlying.vertices p').val ∈ t.addresses := by
    simpa only [shape_decorate] using (φ.underlying.vertices p').property
  rw [labelAt_decorate s f p'.val hp,
    labelAt_decorate t g (φ.underlying.vertices p').val hq] at hlabel
  exact hlabel

/-- Forget the decorated shapes while retaining the label comparisons
supplied by a recursive labelled embedding. -/
theorem exists_addressEmbedding_of_decorate {L : Type*} {r : L → L → Prop}
    {s t : OrderedTree} {f g : List ℕ → L}
    (h : LabelledTree.Embeds r (decorate s f) (decorate t g)) :
    ∃ φ : OrderedTree.AddressEmbedding s t,
      ∀ p, r (f p.val) (g (φ.vertices p).val) := by
  obtain ⟨φ⟩ := h.exists_labelledAddressEmbedding
  exact exists_addressEmbedding_of_decoratedAddress φ

/-- Labelled Kruskal compares trees with any prescribed address labels
from a well-quasi-order. It supplies the actual injective address map and
its label comparisons, rather than only an unlabelled containment witness. -/
theorem exists_labelled_addressEmbedding {L : Type*} {r : L → L → Prop}
    [IsPreorder L r] (hr : WellQuasiOrdered r)
    (t : ℕ → OrderedTree) (f : ℕ → List ℕ → L) :
    ∃ i j, i < j ∧ ∃ φ : OrderedTree.AddressEmbedding (t i) (t j),
      ∀ p, r (f i p.val) (f j (φ.vertices p).val) := by
  obtain ⟨i, j, hij, he⟩ := LabelledTree.wellQuasiOrdered_embeds hr
    (fun n ↦ decorate (t n) (f n))
  obtain ⟨φ, hφ⟩ := exists_addressEmbedding_of_decorate he
  exact ⟨i, j, hij, φ, hφ⟩

end GraphMinor.Kruskal
