module

public import GraphMinor.GM01.RootedSubdivisionAttachment
public import GraphMinor.GM01.SubgraphIso
import GraphMinor.GM01.RootedEmbeddings

/-!
# Rooted subdivision contraction in the ambient source vertex type

The comb trees of Graph Minors I use their ambient vertex type with a
specified vertex set. The finite subdivision contraction uses the
subtype of actual vertices. The explicit graph isomorphism between
these two presentations transports the chosen source root and retains
the internal target attachment vertex from the contraction for (4.9).
-/

public section

namespace GraphMinor.GM01

open Set Graph SimpleGraph Function

/-- The controlled subdivision contraction with the source in its
ambient vertex type, for the contraction of `D` in GM01 (4.9), page 58. -/
noncomputable def rootedSubgraphSubdivisionAtVertex {α β ν : Type*}
    (S : (⊤ : SimpleGraph ν).Subgraph) [Finite S.verts]
    {G : Graph α β} (c : S.verts → α) (hc : Injective c)
    (hcentres : ∀ v, c v ∈ V(G)) (P : S.coe.edgeSet → Graph α β)
    (hPaths : ∀ e : S.coe.edgeSet, ∃ a b, e.val = s(a,b) ∧
      GraphMinor.GM09.IsGraphPathWithEnds G (P e) (c a) (c b) ∧
      V(P e) ∩ range c = {c a,c b})
    (hInter : ∀ e f : S.coe.edgeSet, e ≠ f → V(P e) ∩ V(P f) ⊆ range c)
    (root : S.verts) (x : V(G))
    (hx : x.val = c root ∨ ∃ e : S.coe.edgeSet,
      root ∈ e.val ∧ x.val ∈ V(P e) ∧ x.val ∉ range c) :
    RootedMinorModel (⟨toGraph S, root⟩ : RootedGraph ν (Sym2 ν))
      (⟨G, x⟩ : RootedGraph α β) := by
  let M := rootedModelOfFiniteSubdivisionAtVertex c hc hcentres P hPaths hInter root x hx
  let e := subgraphSimpleGraphIso S
  let e' : GraphMinor.Iso (toGraph S) (Graph.ofSimpleGraph S.coe) :=
    { vertexEquiv := e.vertexEquiv.symm
      edgeEquiv := e.edgeEquiv.symm
      isLink_iff := fun edge a b ↦ by
        simpa only [Equiv.apply_symm_apply] using
          (e.isLink_iff (e.edgeEquiv.symm edge) (e.vertexEquiv.symm a)
            (e.vertexEquiv.symm b)).symm }
  exact M.comapSource e' rfl

/-- Every source centre is retained in its own branch after transporting
the controlled contraction to the ambient source vertex type. -/
theorem rootedSubgraphSubdivisionAtVertex_centre_mem {α β ν : Type*}
    (S : (⊤ : SimpleGraph ν).Subgraph) [Finite S.verts]
    {G : Graph α β} (c : S.verts → α) (hc : Injective c)
    (hcentres : ∀ v, c v ∈ V(G)) (P : S.coe.edgeSet → Graph α β)
    (hPaths : ∀ e : S.coe.edgeSet, ∃ a b, e.val = s(a,b) ∧
      GraphMinor.GM09.IsGraphPathWithEnds G (P e) (c a) (c b) ∧
      V(P e) ∩ range c = {c a,c b})
    (hInter : ∀ e f : S.coe.edgeSet, e ≠ f → V(P e) ∩ V(P f) ⊆ range c)
    (root : S.verts) (x : V(G))
    (hx : x.val = c root ∨ ∃ e : S.coe.edgeSet,
      root ∈ e.val ∧ x.val ∈ V(P e) ∧ x.val ∉ range c) (w : S.verts) :
    c w ∈ (rootedSubgraphSubdivisionAtVertex S c hc hcentres P hPaths hInter root x hx).branch w := by
  unfold rootedSubgraphSubdivisionAtVertex
  change c w ∈ (rootedModelOfFiniteSubdivisionAtVertex c hc hcentres P hPaths hInter root x hx).branch
    ⟨w, mem_univ _⟩
  exact rootedModelOfFiniteSubdivisionAtVertex_centre_mem c hc hcentres P hPaths hInter root x hx w

end GraphMinor.GM01
