module

public import GraphMinor.GM02.TreeDecomposition
public import GraphMinor.GM02.FeasibilityVertices

/-!
# Width after restriction to actual vertices

Recursive child graphs use a smaller vertex set inside the parent type.
Pull each bag back to that subtype. Conversely, take the image of each
subtype bag. These operations preserve bag sizes and the tree-path
condition. Edge coverage in the reverse direction uses vertex coverage
for loops and the simple shadow for edges with distinct ends.
-/

public section
namespace GraphMinor.GM02
open Graph Set SimpleGraph Classical
universe u v t

/-- Pull decomposition bags back to the actual vertex subtype. -/
theorem IsTreeDecomposition.onVertices {α : Type u} {β : Type v} {ι : Type t}
    {G : Graph α β} {T : SimpleGraph ι} {B : ι → Set α}
    (hD : IsTreeDecomposition G T B) :
    IsTreeDecomposition (Graph.ofSimpleGraph ((pathGraph G).induce V(G))) T
      (fun i => Subtype.val ⁻¹' B i) := by
  refine ⟨hD.isTree, ?_, ?_, ?_⟩
  · ext a
    simp only [Set.mem_iUnion, Set.mem_preimage]
    change (∃ i, a.val ∈ B i) ↔ True
    exact ⟨fun _ => trivial, fun _ => Set.mem_iUnion.1 (hD.iUnion_eq.symm ▸ a.property)⟩
  · intro e a b he
    have hab := (Graph.ofSimpleGraph_adj_iff a b).1 ⟨e, he⟩
    obtain ⟨f, hf⟩ := hab.1
    exact hD.edge_mem hf
  · intro i j k hp a ha
    exact hD.inter_subset hp ha

/-- Images of subtype bags give bags for the original graph. -/
theorem IsTreeDecomposition.of_onVertices {α : Type u} {β : Type v} {ι : Type t}
    {G : Graph α β} {T : SimpleGraph ι} {B : ι → Set V(G)}
    (hD : IsTreeDecomposition (Graph.ofSimpleGraph ((pathGraph G).induce V(G))) T B) :
    IsTreeDecomposition G T (fun i => Subtype.val '' B i) := by
  refine ⟨hD.isTree, ?_, ?_, ?_⟩
  · ext a
    constructor
    · intro ha
      obtain ⟨i, b, _, rfl⟩ := Set.mem_iUnion.1 ha
      exact b.property
    · intro ha
      have hb : (⟨a, ha⟩ : V(G)) ∈ ⋃ i, B i := by
        rw [hD.iUnion_eq]
        trivial
      obtain ⟨i, hi⟩ := Set.mem_iUnion.1 hb
      exact Set.mem_iUnion.2 ⟨i, ⟨⟨a, ha⟩, hi, rfl⟩⟩
  · intro e a b he
    let a' : V(G) := ⟨a, he.left_mem⟩
    let b' : V(G) := ⟨b, he.right_mem⟩
    by_cases hab : a = b
    · have ha : a' ∈ ⋃ i, B i := by rw [hD.iUnion_eq]; trivial
      obtain ⟨i, hi⟩ := Set.mem_iUnion.1 ha
      exact ⟨i, ⟨a', hi, rfl⟩, hab ▸ ⟨a', hi, rfl⟩⟩
    · have hadj : ((pathGraph G).induce V(G)).Adj a' b' := ⟨⟨e, he⟩, hab⟩
      have hlink : (Graph.ofSimpleGraph ((pathGraph G).induce V(G))).IsLink s(a', b') a' b' :=
        ⟨rfl, (SimpleGraph.mem_edgeSet _).2 hadj⟩
      obtain ⟨i, hi, hj⟩ := hD.edge_mem hlink
      exact ⟨i, ⟨a', hi, rfl⟩, ⟨b', hj, rfl⟩⟩
  · intro i j k hp a ha
    obtain ⟨b, hb, rfl⟩ := ha.1
    obtain ⟨c, hc, hcb⟩ := ha.2
    have he : c = b := Subtype.val_injective hcb
    exact ⟨b, hD.inter_subset hp ⟨hb, he ▸ hc⟩, rfl⟩

/-- The subtype change preserves all bag-width bounds. -/
theorem treeWidthLE_onVertices_iff {α : Type u} {β : Type v} (G : Graph α β) (w : ℕ) :
    TreeWidthLE (Graph.ofSimpleGraph ((pathGraph G).induce V(G))) w ↔ TreeWidthLE G w := by
  constructor
  · rintro ⟨ι, hι, T, B, hD, hw⟩
    refine ⟨ι, hι, T, fun i => Subtype.val '' B i, hD.of_onVertices, ?_⟩
    intro i
    rw [Set.ncard_image_of_injective _ Subtype.val_injective]
    exact hw i
  · rintro ⟨ι, hι, T, B, hD, hw⟩
    refine ⟨ι, hι, T, fun i => Subtype.val ⁻¹' B i, hD.onVertices, ?_⟩
    intro i
    have hsub : B i ⊆ Set.range (Subtype.val : V(G) → α) := by
      intro a ha
      exact ⟨⟨a, hD.iUnion_eq ▸ Set.mem_iUnion.2 ⟨i, ha⟩⟩, rfl⟩
    rw [Set.ncard_preimage_of_injective_subset_range Subtype.val_injective hsub]
    exact hw i

end GraphMinor.GM02
