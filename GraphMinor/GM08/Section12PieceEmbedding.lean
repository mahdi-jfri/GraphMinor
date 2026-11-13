module

public import GraphMinor.GM08.Defs
public import GraphMinor.GM08.Section12Subspace
import GraphMinor.GM08.Section9Transport
import GraphMinor.GM07.Section3
import GraphMinor.GM08.Section9DiscContext
import GraphMinor.Surface.PlaneDisc

/-!
# Embedding a foundation piece in the ambient disc

Read a drawing in the closed disc that supports it, then carry that
disc to the ambient disc by a homeomorphism. Its boundary vertices
become exactly the roots of its graft. This supplies the embedding
condition on the smaller labels in VIII, Section 12, page 274.
-/

public section

namespace GraphMinor.GM08

open Set Surface

universe u v w

/-- A graph drawn in a closed disc with precisely its roots on the
boundary is disc-embeddable. This is the change of ambient disc used
for the foundation labels of VIII, Section 12. -/
theorem embedsGraft_of_drawing_in_disc {α : Type u} {β : Type v}
    {S : Type w} [TopologicalSpace S]
    (hS : IsClosedDisc (univ : Set S)) (X : Graft α β)
    (D : Drawing S) {B : Set S} (hB : IsClosedDisc B)
    (hDU : D.U ⊆ B) (hNormal : D.IsNormal (discBd B))
    (a : Iso X.G D.toGraph)
    (hroots : ∀ x (hx : x ∈ Graph.vertexSet X.G),
      (a.vertexEquiv ⟨x, hx⟩).1 ∈ discBd B ↔ x ∈ X.T) :
    EmbedsGraft S X := by
  classical
  have : T2Space S := (isSurface_of_closedDisc_univ hS).2.1
  have hBclosed : IsClosed B := hB.isClosed
  obtain ⟨s⟩ := hS
  obtain ⟨b⟩ := hB
  let e : B ≃ₜ S := b.symm.trans (s.trans (Homeomorph.Set.univ S))
  let J := GM12.drawingInSubspace D B hDU
  let c := (isGraphBij_drawingInSubspace D hBclosed hDU).toIso
  let d := (isGraphBij_mapDrawingHomeo e J).toIso
  let a' : Iso X.G (GM07.mapDrawingHomeo e J).toGraph := {
    vertexEquiv := a.vertexEquiv.trans (c.vertexEquiv.symm.trans d.vertexEquiv)
    edgeEquiv := a.edgeEquiv.trans (c.edgeEquiv.symm.trans d.edgeEquiv)
    isLink_iff := fun f x y => by
      have hc := (c.isLink_iff (c.edgeEquiv.symm (a.edgeEquiv f))
        (c.vertexEquiv.symm (a.vertexEquiv x))
        (c.vertexEquiv.symm (a.vertexEquiv y))).symm
      simp only [Equiv.apply_symm_apply] at hc
      exact (a.isLink_iff f x y).trans (hc.trans (d.isLink_iff _ _ _)) }
  have hbd : ∀ x : B, x ∈ bd B ↔ x.1 ∈ discBd B := by
    intro x
    constructor
    · exact fun hx => mem_image_of_mem Subtype.val hx
    · rintro ⟨y, hy, hyx⟩
      exact Subtype.ext hyx ▸ hy
  have hp : J.IsProper := by
    intro x hx
    rw [GM12.drawingInSubspace_V]
    have hxU := hx.2
    change x ∈ (GM12.drawingInSubspace D B hDU).U at hxU
    rw [GM12.drawingInSubspace_U] at hxU
    exact hNormal ⟨(hbd x).mp hx.1, hxU⟩
  have hce : ∀ x : Graph.vertexSet D.toGraph,
      ((c.vertexEquiv.symm x).1 : S) = x.1 := by
    intro x
    have h := congrArg Subtype.val (c.vertexEquiv.apply_symm_apply x)
    exact h
  have he : ∀ x : B, e x ∈ bd S ↔ x ∈ bd B := by
    intro x
    rw [← image_bd_homeomorph e]
    exact e.injective.mem_set_image
  refine ⟨{
    drawing := GM07.mapDrawingHomeo e J
    iso := a'
    isProper := GM07.IsProper.map_homeo e hp
    T_subset_V := X.T_subset
    mem_bd_iff := ?_ }⟩
  intro x hx
  change e (c.vertexEquiv.symm (a.vertexEquiv ⟨x, hx⟩)).1 ∈ bd S ↔ x ∈ X.T
  rw [he, hbd, hce]
  exact hroots x hx

end GraphMinor.GM08
