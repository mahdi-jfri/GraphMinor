module

public import GraphMinor.GM08.Defs
public import GraphMinor.GM08.Section11Iso

/-!
# Reading old vertex labels after a cut

At a lifted drawing vertex, apply the cutting map and then the inverse
of the old drawing's vertex bijection. The resulting label lies in the
original graph. Two lifted vertices have the same label exactly when
they have the same image under the cut, and an old root is recognized
by its boundary image. These are the label facts in VIII (15.4).
-/

public section

namespace GraphMinor.GM08

open Set GraphMinor.Surface Graph

universe u v w

/-- Decode original vertex labels from a lifted drawing, preserving
fibres and the boundary test for old roots. This supplies the labelled
quotient map in the short-tube reconstruction of VIII (15.4), page 282. -/
theorem exists_vertex_decoder_of_drawing {S Y : Type w}
    [TopologicalSpace S] [TopologicalSpace Y] [Nonempty S]
    {α : Type u} {β : Type v} [Nonempty α] {X : Graft α β}
    (gd : GraftDrawing X.G X.T S) (H : Drawing Y) {ψ : Y → S}
    (hV : H.V = ψ ⁻¹' gd.drawing.V) :
    ∃ f : Y → α,
      (∀ y ∈ H.V, f y ∈ V(X.G)) ∧
      (∀ y ∈ H.V, gd.iso.fv (f y) = ψ y) ∧
      (∀ y ∈ H.V, ∀ z ∈ H.V, f y = f z ↔ ψ y = ψ z) ∧
      ∀ y ∈ H.V, f y ∈ X.T ↔ ψ y ∈ bd S := by
  classical
  let f : Y → α := fun y => if hy : ψ y ∈ gd.drawing.V then
    (gd.iso.vertexEquiv.symm ⟨ψ y, hy⟩).1 else Classical.arbitrary α
  have hold : ∀ y ∈ H.V, ψ y ∈ gd.drawing.V := by
    intro y hy
    have hy' : y ∈ ψ ⁻¹' gd.drawing.V := hV ▸ hy
    exact hy'
  have hmem : ∀ y ∈ H.V, f y ∈ V(X.G) := by
    intro y hy
    simp only [f, hold y hy, ↓reduceDIte]
    exact (gd.iso.vertexEquiv.symm ⟨ψ y, hold y hy⟩).2
  have hcoord : ∀ y ∈ H.V, gd.iso.fv (f y) = ψ y := by
    intro y hy
    rw [gd.iso.fv_of_mem (hmem y hy)]
    simp only [f, hold y hy, ↓reduceDIte]
    change (gd.iso.vertexEquiv (gd.iso.vertexEquiv.symm ⟨ψ y, hold y hy⟩)).1 = ψ y
    rw [Equiv.apply_symm_apply]
  refine ⟨f, hmem, hcoord, ?_, ?_⟩
  · intro y hy z hz
    constructor
    · intro he
      exact (hcoord y hy).symm.trans ((congrArg gd.iso.fv he).trans (hcoord z hz))
    · intro he
      apply gd.iso.fv_injOn (hmem y hy) (hmem z hz)
      rw [hcoord y hy, hcoord z hz, he]
  · intro y hy
    have h := gd.mem_bd_iff (f y) (hmem y hy)
    rw [← gd.iso.fv_of_mem (hmem y hy), hcoord y hy] at h
    exact h.symm

end GraphMinor.GM08
