module

public import GraphMinor.Surface.TopologyStatements
public import GraphMinor.Statement
import GraphMinor.GM05.GraphDrawingContraction
import GraphMinor.GM09.DiscDrawing
import GraphMinor.Planar.Defs

/-!
# Minors of a drawn graph can be drawn

For GM V, (8.14), restrict the graph drawing to the subgraph in the
minor witness, contract its selected edges by the surface construction,
and transport the resulting drawing along the witness isomorphism.
-/

public section
namespace GraphMinor.GM05
open Graph Surface
universe u v u' v'

/-- The minor-drawing step in GM V, proof of (8.14), page 113, for
finite graph drawings on any closed surface. -/
theorem graphDrawing_isIsoMinor {α : Type u} {β : Type v}
    {α' : Type u'} {β' : Type v'} {G : Graph α β} {H : Graph α' β'}
    {S : Type} [TopologicalSpace S] (hS : IsClosedSurface S) (Γ : GraphDrawing G S)
    (hminor : IsIsoMinor H G) : Nonempty (GraphDrawing H S) := by
  let : T2Space S := hS.2.1
  obtain ⟨A,hA,C,-,⟨φ⟩⟩ := hminor
  obtain ⟨ΓA,-,-,-,-,-,-,-⟩ := GM09.GraphDrawing.ofSubgraph Γ hA
  obtain ⟨Δ⟩ := graphDrawing_contract hS ΓA C
  exact ⟨GraphDrawing.ofIso φ Δ⟩

end GraphMinor.GM05
