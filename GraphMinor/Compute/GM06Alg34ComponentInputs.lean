module

public import GraphMinor.Compute.GM06Alg34SplitBlock
public import GraphMinor.Compute.GM06Alg34InducedData

/-!
# Finite component inputs for the branching reduction

Enumerate the endpoint graph's components by their least labels and
compute the induced payload on each component. When no division block
is split, every nonempty block belongs wholly to one such component.
Thus restricting the division to a component keeps its own blocks and
discards the others, as prescribed by VI (3.3)(iv), page 121.
-/

@[expose] public section
namespace GraphMinor.Compute.GM06DrawingData

open Set Surface GM06

/-- The complete finite drawing payload for the component of a supplied label. -/
def componentData (x : GM06DrawingData) (a : Fin x.n) : GM06DrawingData :=
  x.inducedData (x.componentVertices a)

/-- The list of component problems in canonical root order. -/
def componentInputs (x : GM06DrawingData) : List GM06DrawingData :=
  x.componentRoots.map x.componentData

/-- With no split block, every two supplied labels of a block are reachable. -/
theorem block_reachable_of_no_split (x : GM06DrawingData)
    (hs : x.hasSplitBlock = false) {L : List (Fin x.n)} (hL : L ∈ x.division)
    {a b : Fin x.n} (ha : a ∈ L) (hb : b ∈ L) : x.vertexGraph.Reachable a b := by
  by_contra hab
  have ht := (x.hasSplitBlock_iff).mpr ⟨L, hL, a, ha, b, hb, hab⟩
  rw [hs] at ht
  cases ht

/-- A nonempty block is contained in the component of any of its labels. -/
theorem block_subset_component_of_no_split (x : GM06DrawingData)
    (hs : x.hasSplitBlock = false) {L : List (Fin x.n)} (hL : L ∈ x.division)
    {a : Fin x.n} (ha : a ∈ L) : block L ⊆ block (x.componentVertices a) := by
  intro b hb
  exact (x.mem_componentVertices_iff a b).mpr (x.block_reachable_of_no_split hs hL ha hb)

/-- An unsplit block meeting a component lies wholly in that component. -/
theorem block_subset_component_of_meets (x : GM06DrawingData)
    (hs : x.hasSplitBlock = false) {L : List (Fin x.n)} (hL : L ∈ x.division)
    (a : Fin x.n) (hmeet : (block L ∩ block (x.componentVertices a)).Nonempty) :
    block L ⊆ block (x.componentVertices a) := by
  obtain ⟨b, hb, hab⟩ := hmeet
  intro c hc
  exact (x.mem_componentVertices_iff a c).mpr
    (((x.mem_componentVertices_iff a b).mp hab).trans
      (x.block_reachable_of_no_split hs hL hb hc))

/-- Each nonempty unsplit block belongs to a canonical component. -/
theorem block_subset_root_component (x : GM06DrawingData)
    (hs : x.hasSplitBlock = false) {L : List (Fin x.n)} (hL : L ∈ x.division)
    (hne : L ≠ []) : ∃ a ∈ x.componentRoots, block L ⊆ block (x.componentVertices a) := by
  obtain ⟨b, hb⟩ := List.exists_mem_of_ne_nil L hne
  obtain ⟨a, ha, hba⟩ := x.exists_componentRoot b
  refine ⟨a, ha, fun c hc => (x.mem_componentVertices_iff a c).mpr ?_⟩
  exact hba.symm.trans (x.block_reachable_of_no_split hs hL hb hc)

end GraphMinor.Compute.GM06DrawingData
