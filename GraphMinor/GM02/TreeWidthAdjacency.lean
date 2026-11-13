module

public import GraphMinor.GM02.TreeDecomposition

/-!
# Tree-width depends only on distinct-vertex adjacency

The underlying-simple-graph reduction in II (3.2), page 318, forgets loops
and parallel edges. A decomposition only needs a bag containing the ends
of each edge. Distinct adjacent ends are unchanged by this reduction.
For a loop, vertex coverage alone supplies the bag. Thus the bag conditions
and width bounds are identical on graphs with the same vertex set and
the same adjacency between distinct vertices.
-/

public section
namespace GraphMinor.GM02
open Graph Set Classical
universe u v v' t

/-- Transfer the vertex bags across deletion of loops or duplicate edges. -/
theorem IsTreeDecomposition.of_distinct_adj {α : Type u} {β : Type v} {β' : Type v'}
    {ι : Type t} {G : Graph α β} {H : Graph α β'} {T : SimpleGraph ι} {B : ι → Set α}
    (hD : IsTreeDecomposition G T B) (hV : V(G) = V(H))
    (hAdj : ∀ a b, a ≠ b → H.Adj a b → G.Adj a b) : IsTreeDecomposition H T B := by
  refine ⟨hD.isTree, hD.iUnion_eq.trans hV, ?_, hD.inter_subset⟩
  intro e a b he
  by_cases hab : a = b
  · have haG : a ∈ V(G) := hV.symm ▸ he.left_mem
    obtain ⟨i, hi⟩ := Set.mem_iUnion.1 (hD.iUnion_eq.symm ▸ haG)
    exact ⟨i, hi, hab ▸ hi⟩
  · obtain ⟨f, hf⟩ := hAdj a b hab ⟨e, he⟩
    exact hD.edge_mem hf

/-- Forgetting loops and parallel edges preserves every bag-width bound. -/
theorem treeWidthLE_iff_of_distinct_adj {α : Type u} {β : Type v} {β' : Type v'}
    (G : Graph α β) (H : Graph α β') (hV : V(G) = V(H))
    (hAdj : ∀ a b, a ≠ b → (G.Adj a b ↔ H.Adj a b)) (w : ℕ) :
    TreeWidthLE G w ↔ TreeWidthLE H w := by
  constructor
  · rintro ⟨ι, hι, T, B, hD, hw⟩
    exact ⟨ι, hι, T, B, hD.of_distinct_adj hV (fun a b hab => (hAdj a b hab).2), hw⟩
  · rintro ⟨ι, hι, T, B, hD, hw⟩
    exact ⟨ι, hι, T, B, hD.of_distinct_adj hV.symm (fun a b hab => (hAdj a b hab).1), hw⟩

/-- The numerical tree-width is unchanged when only loops or duplicate
edges are removed, as needed for the final step of II (3.2). -/
theorem treeWidth_eq_of_distinct_adj {α : Type u} {β : Type v} {β' : Type v'}
    (G : Graph α β) (H : Graph α β') (hV : V(G) = V(H))
    (hAdj : ∀ a b, a ≠ b → (G.Adj a b ↔ H.Adj a b))
    (hVG : V(G).Finite) (hEG : E(G).Finite) (hVH : V(H).Finite) (hEH : E(H).Finite) :
    treeWidth G hVG hEG = treeWidth H hVH hEH := by
  apply Nat.le_antisymm
  · apply (treeWidth_le_iff G hVG hEG _).2
    apply (treeWidthLE_iff_of_distinct_adj G H hV hAdj _).2
    exact (treeWidth_le_iff H hVH hEH _).1 le_rfl
  · apply (treeWidth_le_iff H hVH hEH _).2
    apply (treeWidthLE_iff_of_distinct_adj G H hV hAdj _).1
    exact (treeWidth_le_iff G hVG hEG _).1 le_rfl

end GraphMinor.GM02
