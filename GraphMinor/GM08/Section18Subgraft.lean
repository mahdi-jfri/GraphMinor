module

public import GraphMinor.GM08.Defs
public import GraphMinor.GM08.Section11Iso
import GraphMinor.GM08.Section12Pullback
import GraphMinor.GM08.Section12Subspace
import GraphMinor.GM08.Section9Transport
import GraphMinor.GM12.Section3SubspaceDrawing
import GraphMinor.GM16.DrawingGraphPaths

/-!
# The part of a graft drawn in a smaller surface

Let `Γ` draw a graft `X` in `Σ`, and let `J` be a subdrawing of `Γ`. The
vertices and edges of `X` drawn in `J` form a subgraph of `X`. If `J` lies in
the image of a closed embedding `f : Σ' → Σ`, we read `J` in `Σ'`. This gives a
drawing of the subgraph in `Σ'`, whose roots are the vertices drawn at images
of boundary points of `Σ'`. Both steps of (18.3) on page 287 cut a graft into
pieces in this way.
-/

@[expose] public section

namespace GraphMinor.GM08

open Set Graph GraphMinor.Surface

universe u v w w'

/-- **The subgraft drawn by a subdrawing.** Let `gd` draw `X` in `S`, and let
`J` be a subdrawing of `gd.drawing` inside the image of a closed embedding
`f : S' → S`, such that every point of `J` at the image of a boundary point of
`S'` is a vertex. For a set `T'` of vertices drawn in `J`, made of exactly the
vertices drawn at images of boundary points of `S'`, the vertices and edges of
`X` drawn in `J` form a graft with roots `T'` that embeds in `S'`. -/
theorem exists_subgraft_embedsGraft {α : Type u} {β : Type v} {S : Type w}
    [TopologicalSpace S] [Nonempty S] {X : Graft α β} (gd : GraftDrawing X.G X.T S)
    {J : Drawing S} (hJ : J.IsSubdrawing gd.drawing) {S' : Type w'} [TopologicalSpace S']
    {f : S' → S} (hf : Topology.IsClosedEmbedding f) (hU : J.U ⊆ range f)
    (hprop : ∀ y, f y ∈ J.U → y ∈ bd S' → f y ∈ J.V) (T' : Set α)
    (hT'V : T' ⊆ {v ∈ V(X.G) | gd.iso.fv v ∈ J.V})
    (hT' : ∀ v ∈ V(X.G), gd.iso.fv v ∈ J.V → (gd.iso.fv v ∈ f '' bd S' ↔ v ∈ T')) :
    ∃ Y : Graft α β, Y.G ≤ X.G ∧ V(Y.G) = {v ∈ V(X.G) | gd.iso.fv v ∈ J.V} ∧
      E(Y.G) = {e ∈ E(X.G) | gd.iso.fe e ∈ J.E} ∧ Y.T = T' ∧ EmbedsGraft S' Y := by
  classical
  obtain ⟨G', hG'X, hG'V, hG'E, hbij⟩ :=
    exists_subgraph_of_iso gd.iso (GM16.toGraph_le_of_isSubdrawing hJ)
  have hK : IsClosed (range f) := hf.isClosed_range
  let J₁ := GM12.drawingInSubspace J (range f) hU
  let i₁ := (isGraphBij_drawingInSubspace J hK hU).toIso
  let e : range f ≃ₜ S' := hf.isEmbedding.toHomeomorph.symm
  let J₂ := GM07.mapDrawingHomeo e J₁
  let i₂ := (isGraphBij_mapDrawingHomeo e J₁).toIso
  have hinv : ∀ (g : E(J.toGraph)) (y z : V(J.toGraph)),
      J.toGraph.IsLink g.1 y.1 z.1 ↔
        J₁.toGraph.IsLink (i₁.edgeEquiv.symm g).1 (i₁.vertexEquiv.symm y).1
          (i₁.vertexEquiv.symm z).1 := by
    intro g y z
    have h := i₁.isLink_iff (i₁.edgeEquiv.symm g) (i₁.vertexEquiv.symm y) (i₁.vertexEquiv.symm z)
    simp only [Equiv.apply_symm_apply] at h
    exact h.symm
  let a : GraphMinor.Iso G' J₂.toGraph := {
    vertexEquiv := hbij.toIso.vertexEquiv.trans (i₁.vertexEquiv.symm.trans i₂.vertexEquiv)
    edgeEquiv := hbij.toIso.edgeEquiv.trans (i₁.edgeEquiv.symm.trans i₂.edgeEquiv)
    isLink_iff := fun g y z => (hbij.toIso.isLink_iff g y z).trans
      ((hinv _ _ _).trans (i₂.isLink_iff _ _ _)) }
  have he : ∀ z : range f, f (e z) = z.1 := fun z => by
    obtain ⟨_, y, rfl⟩ := z
    simp [e]
  have hJ₂U : J₂.U = f ⁻¹' J.U := by
    ext y
    constructor
    · rintro ⟨z, hz, rfl⟩
      change f (e z) ∈ J.U
      rw [he]
      rw [GM12.drawingInSubspace_U] at hz
      exact hz
    · intro hy
      refine ⟨⟨f y, y, rfl⟩, ?_, ?_⟩
      · rw [GM12.drawingInSubspace_U]
        exact hy
      · exact hf.injective (by rw [he])
  have hJ₂V : J₂.V = f ⁻¹' J.V := by
    ext y
    constructor
    · rintro ⟨z, hz, rfl⟩
      change f (e z) ∈ J.V
      rw [he]
      rw [GM12.drawingInSubspace_V] at hz
      exact hz
    · intro hy
      refine ⟨⟨f y, y, rfl⟩, ?_, ?_⟩
      · rw [GM12.drawingInSubspace_V]
        exact hy
      · exact hf.injective (by rw [he])
  have ha : ∀ (v : α) (hv : v ∈ V(G')), f (a.vertexEquiv ⟨v, hv⟩).1 = gd.iso.fv v := by
    intro v hv
    change f (e (i₁.vertexEquiv.symm (hbij.toIso.vertexEquiv ⟨v, hv⟩)).1) = _
    rw [he]
    have h1 : (i₁.vertexEquiv (i₁.vertexEquiv.symm (hbij.toIso.vertexEquiv ⟨v, hv⟩))).1 =
        (hbij.toIso.vertexEquiv ⟨v, hv⟩).1 := by rw [Equiv.apply_symm_apply]
    exact h1
  have hTV : T' ⊆ V(G') := fun v hv => hG'V ▸ hT'V hv
  let Y : Graft α β := ⟨G', T', hTV, ⟨X.finite_G.1.subset hG'X.vertexSet_mono,
    X.finite_G.2.subset hG'X.edgeSet_mono⟩⟩
  refine ⟨Y, hG'X, hG'V, hG'E, rfl, ⟨{
    drawing := J₂
    iso := a
    isProper := ?_
    T_subset_V := hTV
    mem_bd_iff := ?_ }⟩⟩
  · rintro y ⟨hyb, hyU⟩
    rw [hJ₂U] at hyU
    rw [hJ₂V]
    exact hprop y hyU hyb
  · intro v hv
    have hvX : v ∈ {v ∈ V(X.G) | gd.iso.fv v ∈ J.V} := hG'V ▸ hv
    constructor
    · intro hb
      exact (hT' v hvX.1 hvX.2).mp ⟨_, hb, ha v hv⟩
    · intro hvT
      obtain ⟨y, hy, hfy⟩ := (hT' v hvX.1 hvX.2).mpr hvT
      have : (a.vertexEquiv ⟨v, hv⟩).1 = y := hf.injective (by rw [ha v hv, hfy])
      rw [this]
      exact hy
