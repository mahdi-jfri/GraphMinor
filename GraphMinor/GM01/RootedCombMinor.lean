module

public import GraphMinor.GM01.CombRootLong
public import GraphMinor.GM01.RootAnOrdinaryModel
import GraphMinor.GM01.RootedEmbeddings
import GraphMinor.GM01.SubgraphIso
import Lean.Elab.Tactic.Omega

/-!
# A rooted comb from the ordinary tail minor

In Graph Minors I, (4.1), page 55, the bypass may enter the final block
at an arbitrary vertex, while the retained long comb is an ordinary
minor. Root its model at some source vertex by taking a path to the
first branch. The long-side lemma supplies a rooted shorter comb there.
Composing the two actual models gives the shorter comb at the original
target root, with no assumption about where the bypass entered.
-/

public section

namespace GraphMinor.GM01

open Set Graph SimpleGraph

/-- A sufficiently long ordinary comb minor in a connected rooted target
gives a shorter rooted comb minor at its distinguished vertex. This is
the arbitrary-tail-entry step needed for GM01 (4.1), page 55. -/
theorem rootedPathComb_of_long_minor {α β : Type*} {γ m N : ℕ}
    (hm : 0 < m) (hN : 2 * m + 1 ≤ N) (G : RootedGraph α β)
    (hconn : GraphConnected G.graph)
    {ηv : (pathComb γ N).verts → Set α} {ηe : Sym2 (pathComb γ N).verts → β}
    (hmodel : IsMinorModel (Graph.ofSimpleGraph (pathComb γ N).coe) G.graph ηv ηe) :
    HasRootedMinor (rootedPathComb γ m hm) G := by
  let : Nonempty (pathComb γ N).verts :=
    ⟨⟨Sum.inl ⟨0, by omega⟩, pathComb_spine_mem γ N _⟩⟩
  obtain ⟨r, ⟨M⟩⟩ := exists_rooted_model_of_ordinary G hconn hmodel
  let e := subgraphSimpleGraphIso (pathComb γ N)
  let e' : GraphMinor.Iso (toGraph (pathComb γ N))
      (Graph.ofSimpleGraph (pathComb γ N).coe) :=
    { vertexEquiv := e.vertexEquiv.symm
      edgeEquiv := e.edgeEquiv.symm
      isLink_iff := fun edge x y ↦ by
        simpa only [Equiv.apply_symm_apply] using
          (e.isLink_iff (e.edgeEquiv.symm edge) (e.vertexEquiv.symm x)
            (e.vertexEquiv.symm y)).symm }
  have hrooted : HasRootedMinor
      (⟨toGraph (pathComb γ N), r⟩ : RootedGraph (PathCombVertex N) (Sym2 (PathCombVertex N))) G :=
    ⟨M.comapSource e' rfl⟩
  exact (rootedPathComb_of_long_comb hm hN r).trans hrooted

end GraphMinor.GM01
