module

public import GraphMinor.GM01.RootedGraphs
public import GraphMinor.GM01.Defs
import GraphMinor.GM01.RootedModelMinor
import GraphMinor.GM01.RootedEmbeddings
import GraphMinor.GM01.SubgraphIso
import GraphMinor.Minor.Basic

/-!
# Forgetting the root of a finite subgraph-source model

The packing in Graph Minors I, (5.2), page 61, retains ordinary
forest-tree minors inside selected fork intervals. A rooted model
of a finite simple-subgraph source also gives its ordinary minor.
Transfer the source through the explicit subtype isomorphism,
forget the root by the proved model conversion, then return through
that same isomorphism.
-/

public section

namespace GraphMinor.GM01

open Set Graph SimpleGraph

/-- Forget the root of a finite simple-subgraph-source model, as used
for the selected forest minors in GM01 (5.2), page 61. -/
theorem RootedMinorModel.isIsoMinor_of_subgraph_source {α β ν : Type*} [Nonempty β]
    {H : (⊤ : SimpleGraph ν).Subgraph} (hH : H.verts.Finite) (r : H.verts)
    (G : RootedGraph α β) (hV : V(G.graph).Finite) (hE : E(G.graph).Finite)
    (M : RootedMinorModel (⟨toGraph H,r⟩ : RootedGraph ν (Sym2 ν)) G) :
    IsIsoMinor (toGraph H) G.graph := by
  let : Finite H.verts := hH.to_subtype
  let M' : RootedMinorModel
      (⟨Graph.ofSimpleGraph H.coe,⟨r,mem_univ _⟩⟩ : RootedGraph H.verts (Sym2 H.verts)) G :=
    M.comapSource (subgraphSimpleGraphIso H) rfl
  obtain ⟨ηv,ηe,hModel⟩ := M'.exists_isMinorModel_of_simple H.coe r G
  have hSimple : IsIsoMinor (Graph.ofSimpleGraph H.coe) G.graph :=
    isIsoMinor_of_isMinorModel _ G.graph Set.finite_univ (Set.toFinite _) hV hE ηv ηe hModel
  exact (subgraphSimpleGraphIso H).symm.isIsoMinor_left hSimple

end GraphMinor.GM01
