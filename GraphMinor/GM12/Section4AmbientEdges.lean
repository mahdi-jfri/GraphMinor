module

public import GraphMinor.GM12.Defs
public import GraphMinor.Statement
import Mathlib.Combinatorics.Graph.Subgraph

/-!
# Ambient edge types in controlled minor models

Graph Minors XII, page 249, defines the edge map only on the edges of the
target graph. `ControlsMinor` instead asks for a map on its whole ambient
edge type. If the host edge type is empty, unused target edge labels can
therefore prevent a model. The lemmas here give the obstruction explicitly.
-/

public section

namespace GraphMinor.GM12

/-- The empty graph with empty ambient types has a controlled model in every
host. All requirements concern an empty vertex or edge set. -/
theorem controlsMinor_empty_target {α β : Type*} (G : Hypergraph α β) (θ : ℕ)
    (T : Set (Hypergraph α β × Hypergraph α β)) :
    ControlsMinor G θ T (⊥ : Graph Empty Empty) := by
  refine ⟨Empty.elim, Empty.elim, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro v
    exact v.elim
  · intro v
    exact v.elim
  · intro e
    exact e.elim
  · intro e
    exact e.elim
  · intro e
    exact e.elim
  · simp
  · intro A B hm ho v
    exact v.elim

/-- A nonempty ambient target edge type requires an inhabitant of the host
edge type, even when none of the target edge labels is used. -/
theorem not_controlsMinor_empty_host_edge_type {α γ δ : Type*} [Nonempty δ]
    (G : Hypergraph α Empty) (θ : ℕ)
    (T : Set (Hypergraph α Empty × Hypergraph α Empty)) (L : Graph γ δ) :
    ¬ ControlsMinor G θ T L := by
  rintro ⟨_, b, _⟩
  exact (b (Classical.choice ‹Nonempty δ›)).elim

/-- The targets in the ambient-edge obstruction are isomorphic: both have
empty vertex and edge sets. The maps are the unique maps between empty sets. -/
def empty_target_iso : Iso (⊥ : Graph Empty Unit) (⊥ : Graph Empty Empty) where
  vertexEquiv := Equiv.refl _
  edgeEquiv := by
    letI : IsEmpty (⊥ : Graph Empty Unit).edgeSet :=
      ⟨fun e => Set.notMem_empty _ e.property⟩
    exact Equiv.equivOfIsEmpty _ _
  isLink_iff e := by
    exact (Set.notMem_empty _ e.property).elim

end GraphMinor.GM12
