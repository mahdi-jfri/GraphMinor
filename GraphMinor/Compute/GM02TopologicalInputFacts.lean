module

public import GraphMinor.Compute.GM02TopologicalInput

/-!
# Size and edge numbering of the plain topological input

The supplied vertex and edge counts agree with the actual multigraphs.
The pattern edge list gives a canonical enumeration of its edges and
their endpoints. Isomorphism to a subgraph of a fixed graph therefore
bounds both supplied pattern counts by the corresponding fixed counts.
-/

public section
namespace GraphMinor.Compute
open Graph Set Classical

private theorem ncard_nat_Iio (n : ℕ) : (Set.Iio n).ncard = n := by
  let e : Set.Iio n ≃ Fin n :=
    { toFun := fun x => ⟨x.val, x.property⟩
      invFun := fun x => ⟨x.val, x.isLt⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  rw [← Nat.card_coe_set_eq, Nat.card_congr e, Nat.card_fin]

/-- The supplied host vertex count is its actual number of vertices. -/
theorem GM02EdgeListInput.ncard_vertices (x : GM02EdgeListInput) : V(x.graph).ncard = x.n :=
  ncard_nat_Iio _

/-- The supplied edge-list length counts all actual host edges. -/
theorem GM02EdgeListInput.ncard_edges (x : GM02EdgeListInput) : E(x.graph).ncard = x.edges.length :=
  ncard_nat_Iio _

/-- The pattern vertex count includes precisely its given isolated and incident vertices. -/
theorem GM02TopologicalInput.ncard_vertices (x : GM02TopologicalInput) : V(x.H).ncard = x.vertices.card := by
  change (x.vertices.image Fin.val : Set ℕ).ncard = _
  rw [Set.ncard_coe_finset, Finset.card_image_of_injective _ Fin.val_injective]

/-- The supplied pattern edge count counts loops and parallel copies separately. -/
theorem GM02TopologicalInput.ncard_edges (x : GM02TopologicalInput) : E(x.H).ncard = x.edges.length := by
  rw [x.pattern_edges]
  exact ncard_nat_Iio _

/-- The chosen size is the sum of the paper's sizes of its two input graphs. -/
theorem GM02TopologicalInput.size_eq (x : GM02TopologicalInput) :
    gm02TopologicalSize x = V(x.G.graph).ncard + E(x.G.graph).ncard + V(x.H).ncard + E(x.H).ncard := by
  rw [x.G.ncard_vertices, x.G.ncard_edges, x.ncard_vertices, x.ncard_edges]
  rfl

/-- List positions canonically enumerate the actual edges of the pattern. -/
@[expose] def GM02TopologicalInput.edgeEquiv (x : GM02TopologicalInput) : Fin x.edges.length ≃ E(x.H) where
  toFun e := ⟨e.val, ((x.pattern_edges).ge e.isLt)⟩
  invFun e := ⟨e.val, ((x.pattern_edges).le e.property)⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- The canonical enumeration retains each supplied edge position as its edge name. -/
theorem GM02TopologicalInput.edgeEquiv_val (x : GM02TopologicalInput) (e : Fin x.edges.length) :
    (x.edgeEquiv e).val = e.val := rfl

/-- The prescribed endpoints are exactly the words supplied at the edge position. -/
@[expose] def GM02TopologicalInput.ends (x : GM02TopologicalInput) (e : Fin x.edges.length) : ℕ × ℕ :=
  ((x.edges[e.val]'e.isLt).1.val, (x.edges[e.val]'e.isLt).2.val)

/-- The endpoint pair is read directly from its supplied list position. -/
theorem GM02TopologicalInput.ends_def (x : GM02TopologicalInput) (e : Fin x.edges.length) :
    x.ends e = ((x.edges[e.val]'e.isLt).1.val, (x.edges[e.val]'e.isLt).2.val) := rfl

/-- The canonical pattern edge enumeration has its supplied endpoints. -/
theorem GM02TopologicalInput.ends_isLink (x : GM02TopologicalInput) (e : Fin x.edges.length) :
    x.H.IsLink (x.edgeEquiv e).val (x.ends e).1 (x.ends e).2 := by
  have hm := x.ends_mem (x.edges[e.val]'e.isLt) (List.getElem_mem e.isLt)
  exact ⟨⟨e.isLt, rfl⟩, Finset.mem_image.2 ⟨_, hm.1, rfl⟩, Finset.mem_image.2 ⟨_, hm.2, rfl⟩⟩

/-- Isomorphism to a subgraph bounds the supplied pattern edge count by the fixed graph's edge count. -/
theorem GM02TopologicalInput.edges_le_of_iso_subgraph {A B : Type*} (x : GM02TopologicalInput)
    {H₀ K : Graph A B} (hE : E(H₀).Finite) (hK : K ≤ H₀) (φ : Iso x.H K) :
    x.edges.length ≤ E(H₀).ncard := by
  have heq : E(x.H).ncard = E(K).ncard := by
    rw [← Nat.card_coe_set_eq, ← Nat.card_coe_set_eq]
    exact Nat.card_congr φ.edgeEquiv
  rw [← x.ncard_edges, heq]
  exact Set.ncard_le_ncard hK.edgeSet_mono hE

/-- Isomorphism to a subgraph also bounds the supplied pattern vertex count. -/
theorem GM02TopologicalInput.vertices_le_of_iso_subgraph {A B : Type*} (x : GM02TopologicalInput)
    {H₀ K : Graph A B} (hV : V(H₀).Finite) (hK : K ≤ H₀) (φ : Iso x.H K) :
    x.vertices.card ≤ V(H₀).ncard := by
  have heq : V(x.H).ncard = V(K).ncard := by
    rw [← Nat.card_coe_set_eq, ← Nat.card_coe_set_eq]
    exact Nat.card_congr φ.vertexEquiv
  rw [← x.ncard_vertices, heq]
  exact Set.ncard_le_ncard hK.vertexSet_mono hV

end GraphMinor.Compute
