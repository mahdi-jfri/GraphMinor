module

public import GraphMinor.GM05.ExpansionDefs
import GraphMinor.GM05.CopyContractionClasses

/-!
# Expansions of a graph with no vertices

Such a graph also has no edges. The empty subgraph of any host contracts
to an isomorphic empty graph. It therefore gives arbitrarily many
pairwise vertex-disjoint expansions. This handles the empty fixed graph
in Graph Minors V, (8.8).
-/

public section

namespace GraphMinor.GM05

open Graph Set

/-- The empty subgraph is an expansion of every graph with no vertices. -/
theorem exists_empty_expansion {α β α' β' : Type*} {H : Graph α' β'}
    (hV : V(H)=∅) (G : Graph α β) :
    ∃ A, IsHExpansion H G A ∧ V(A)=∅ := by
  have hE : E(H)=∅ := by
    apply eq_empty_iff_forall_notMem.mpr
    intro e he
    obtain ⟨x,y,hxy⟩ := exists_isLink_of_mem_edgeSet he
    exact notMem_empty x (hV ▸ hxy.left_mem)
  let A := Graph.noEdge (∅ : Set α) β
  have hVA : V(contract A ∅)=∅ := by
    rw [contract_vertexSet_eq]
    change contractionClass A ∅ '' (∅ : Set α)=∅
    exact image_empty _
  let : IsEmpty V(H) := ⟨fun x ↦ notMem_empty x.1 (hV ▸ x.2)⟩
  let : IsEmpty E(H) := ⟨fun e ↦ notMem_empty e.1 (hE ▸ e.2)⟩
  let : IsEmpty V(contract A ∅) := ⟨fun x ↦ notMem_empty x.1 (hVA ▸ x.2)⟩
  let : IsEmpty E(contract A ∅) := ⟨fun e ↦ e.2.1⟩
  let φ : Iso H (contract A ∅) := {
    vertexEquiv := Equiv.equivOfIsEmpty _ _
    edgeEquiv := Equiv.equivOfIsEmpty _ _
    isLink_iff := fun e _ _ ↦ isEmptyElim e }
  exact ⟨A,⟨Graph.noEdge_le_iff.mpr (empty_subset _),∅,empty_subset _,⟨φ⟩⟩,rfl⟩

/-- A graph with no vertices has a packing of any prescribed number of
expansions in every host. -/
theorem hasDisjointExpansions_of_empty_vertices {α β α' β' : Type*} {H : Graph α' β'}
    (hV : V(H)=∅) (G : Graph α β) (k : ℕ) : HasDisjointExpansions H G k := by
  obtain ⟨A,hA,hVA⟩ := exists_empty_expansion hV G
  refine ⟨fun _ ↦ A,fun _ ↦ hA,?_⟩
  intro i j hij
  rw [hVA]
  exact empty_disjoint _

end GraphMinor.GM05
