module

public import GraphMinor.GM05.ULiftGraph
public import GraphMinor.GM05.ExpansionDefs
import GraphMinor.GM05.DisjointExpansionMinor
import GraphMinor.GM05.CopyPacking
import GraphMinor.Minor.Basic

/-!
# Expansions under universe relabelling

For GM V, (8.14), an expansion in the geometric host gives a minor
in its lifted subgraph. Extract a contraction witness there, retaining
only lifted vertices of the old expansion. Conversely a packing in
the lifted host gives a minor of the disjoint copy graph, which
transports back to the original host and gives a packing there.
-/

public section
namespace GraphMinor.GM05
open Set Graph
universe u v r s u' v'

/-- Lift an expansion without adding vertices outside the lifted
original expansion, as needed for GM V, (8.14), in arbitrary host universes. -/
theorem exists_ulift_expansion {α : Type u} {β : Type v} {α' : Type u'} {β' : Type v'}
    {H : Graph α' β'} {G A : Graph α β} (hA : IsHExpansion H G A) :
    ∃ B, IsHExpansion H (uliftGraph.{u,v,r,s} G) B ∧
      ∀ x ∈ V(B), x.down ∈ V(A) := by
  have hminor : IsIsoMinor H A := ⟨A,le_rfl,hA.2⟩
  have hlift : IsIsoMinor H (uliftGraph.{u,v,r,s} A) :=
    Iso.isIsoMinor_right hminor (uliftGraphIso A)
  obtain ⟨B,hBA,F,hF,hiso⟩ := hlift
  exact ⟨B,⟨hBA.trans (uliftGraph_mono hA.1),F,hF,hiso⟩,
    fun _ hx ↦ hBA.vertexSet_mono hx⟩

/-- A packing in the lifted host gives a packing in the original
finite host. This transfers the no-two-expansions part of GM V, (8.14). -/
theorem disjointExpansions_of_ulift {α : Type u} {β : Type v} [Nonempty β]
    {α' : Type u'} {β' : Type v'} {H : Graph α' β'} {G : Graph α β} {k : ℕ}
    (hVH : V(H).Finite) (hEH : E(H).Finite) (hVG : V(G).Finite) (hEG : E(G).Finite)
    (hp : HasDisjointExpansions H (uliftGraph.{u,v,r,s} G) k) :
    HasDisjointExpansions H G k := by
  have hfinite := uliftGraph_finite.{u,v,r,s} G hVG hEG
  have hminor := copy_minor_of_disjoint_expansions hVH hEH hfinite.1 hfinite.2 hp
  have hback : IsIsoMinor (graphCopies k H) G :=
    Iso.isIsoMinor_right hminor (uliftGraphIso G).symm
  exact disjointExpansions_of_copy_minor hVH hEH hVG hEG hback

end GraphMinor.GM05
