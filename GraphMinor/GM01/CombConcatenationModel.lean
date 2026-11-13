module

public import GraphMinor.GM01.CombConcatenation
import GraphMinor.GM01.RootedGraphEmbeddings
import GraphMinor.GM01.RootedEmbeddings
import GraphMinor.GM01.SubgraphIso

/-!
# Transferring the longer comb to the joined source

For Graph Minors I, (4.10), page 58, the two combs joined by a spine
edge form a comb of summed length. The inverse consecutive-interval
vertex identification preserves adjacency and the first spine root.
Singleton branches give the corresponding rooted model. This lets the
joined branch construction conclude the printed longer-comb minor.
-/

public section

namespace GraphMinor.GM01

open Set Graph SimpleGraph

/-- The two joined source combs rooted at the first spine vertex of
the first comb, as in the contraction for GM01 (4.10), page 58. -/
@[expose] def rootedConcatenatedComb (γ a b : ℕ) (ha : 0 < a) (hb : 0 < b) :
    RootedGraph ((pathComb γ a).verts ⊕ (pathComb γ b).verts)
      (Sym2 ((pathComb γ a).verts ⊕ (pathComb γ b).verts)) :=
  ⟨Graph.ofSimpleGraph (concatenatedComb γ a b ha hb),
    ⟨Sum.inl (rootedPathComb γ a ha).root, mem_univ _⟩⟩

/-- The rooted longer comb is a rooted minor of its two joined source
pieces. Its vertex map is the inverse consecutive-interval identification. -/
noncomputable def rootedModelOfCombConcatenation (γ a b : ℕ) (ha : 0 < a) (hb : 0 < b) :
    RootedMinorModel (rootedPathComb γ (a + b) (by omega)) (rootedConcatenatedComb γ a b ha hb) := by
  let e := combConcatenationEquiv γ a b
  let G := rootedConcatenatedComb γ a b ha hb
  let r : (pathComb γ (a + b)).verts := (rootedPathComb γ (a + b) (by omega)).root
  have hAdj : ∀ {u v}, (pathComb γ (a + b)).coe.Adj u v → G.graph.Adj (e.symm u) (e.symm v) := by
    intro u v huv
    apply (Graph.ofSimpleGraph_adj_iff _ _).mpr
    apply (combConcatenationEquiv_adj_iff ha hb (e.symm u) (e.symm v)).mp
    simpa only [e, Equiv.apply_symm_apply] using huv
  have hroot : G.root.val = e.symm r := by
    apply e.injective
    rw [Equiv.apply_symm_apply]
    rfl
  let M := rootedModelOfGraphEmbedding (pathComb γ (a + b)).coe G e.symm.toEmbedding
    (fun _ ↦ mem_univ _) hAdj r hroot
  let iso := subgraphSimpleGraphIso (pathComb γ (a + b))
  let iso' : GraphMinor.Iso (toGraph (pathComb γ (a + b)))
      (Graph.ofSimpleGraph (pathComb γ (a + b)).coe) :=
    { vertexEquiv := iso.vertexEquiv.symm
      edgeEquiv := iso.edgeEquiv.symm
      isLink_iff := fun edge u v ↦ by
        simpa only [Equiv.apply_symm_apply] using
          (iso.isLink_iff (iso.edgeEquiv.symm edge) (iso.vertexEquiv.symm u)
            (iso.vertexEquiv.symm v)).symm }
  exact M.comapSource iso' rfl

end GraphMinor.GM01
