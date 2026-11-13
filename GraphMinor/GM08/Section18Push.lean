module

public import GraphMinor.GM08.Section11Transport
import GraphMinor.GM08.Section12Subspace
import GraphMinor.GM08.Section15ImageIso
import GraphMinor.GM07.CuffShift
import GraphMinor.GM12.Section3SubspaceDrawing
import GraphMinor.GM19.RadialExists

/-!
# Pushing a drawing forward by a map that is injective on it

Let `J` be a drawing in a compact Hausdorff space `Σ`, and let `φ` be a
continuous map to a Hausdorff space that is injective on `U(J)`. Read `J` in
the subspace `U(J)`. There `φ` is a closed embedding, so the image of `J` is a
drawing, and pulling it back gives `J` again. VII's matched pull-back then
gives the bijection of the two drawing graphs. The split step of (18.3),
page 287, uses this to move the inner piece of a graft into a cylinder.
-/

@[expose] public section

namespace GraphMinor.GM08

open Set Topology Graph GraphMinor.Surface

universe u

/-- Two drawings with the same support and vertices are equal. -/
theorem drawing_eq_of_U_V {S : Type*} [TopologicalSpace S] {G H : Drawing S}
    (hU : G.U = H.U) (hV : G.V = H.V) : G = H := by
  cases G
  cases H
  subst hU hV
  rfl

/-- **Pushing a drawing forward.** If `φ` is continuous and injective on
`U(J)`, then `φ(J)` is a drawing, and `φ` gives an isomorphism of the drawing
graphs. -/
theorem exists_push_drawing {S Z : Type u} [TopologicalSpace S] [TopologicalSpace Z]
    [CompactSpace S] [T2Space S] [T2Space Z] (J : Drawing S) (hne : J.U.Nonempty)
    {φ : S → Z} (hφ : Continuous φ) (hinj : InjOn φ J.U) :
    ∃ D' : Drawing Z, D'.U = φ '' J.U ∧ D'.V = φ '' J.V ∧
      ∃ i : GraphMinor.Iso J.toGraph D'.toGraph,
        ∀ v : V(J.toGraph), (i.vertexEquiv v).1 = φ v.1 := by
  classical
  set K := J.U with hKdef
  have hK : IsClosed K := J.isClosed_U
  have : CompactSpace K := isCompact_iff_compactSpace.mp hK.isCompact
  have : Nonempty K := hne.to_subtype
  let ψ : K → Z := fun x => φ x.1
  have hψc : Continuous ψ := hφ.comp continuous_subtype_val
  have hψi : Function.Injective ψ := fun x y h => Subtype.ext (hinj x.2 y.2 h)
  have hψ : IsClosedEmbedding ψ := hψc.isClosedEmbedding hψi
  let J₁ := GM12.drawingInSubspace J K subset_rfl
  obtain ⟨D', hU', hV'⟩ := GM19.exists_drawing_image J₁ hψ
  obtain ⟨G, hGU, hGV, hm⟩ := GM07.exists_pull_drawing hψ D'
    (by rw [hU']; exact image_subset_range _ _)
  have hGJ : G = J₁ := drawing_eq_of_U_V
    (by rw [hGU, hU', preimage_image_eq _ hψi])
    (by rw [hGV, hV', preimage_image_eq _ hψi])
  rw [hGJ] at hm
  have hJ₁U : (Subtype.val : K → S) '' J₁.U = J.U := by
    rw [GM12.drawingInSubspace_U]
    rw [image_preimage_eq_of_subset (by rw [Subtype.range_coe])]
  have hJ₁V : (Subtype.val : K → S) '' J₁.V = J.V := by
    rw [GM12.drawingInSubspace_V]
    rw [image_preimage_eq_of_subset (by rw [Subtype.range_coe]; exact J.V_subset_U)]
  have himU : ψ '' J₁.U = φ '' J.U := by rw [← hJ₁U, image_image]
  have himV : ψ '' J₁.V = φ '' J.V := by rw [← hJ₁V, image_image]
  refine ⟨D', hU'.trans himU, hV'.trans himV, ?_⟩
  let i₁ := (isGraphBij_drawingInSubspace J hK subset_rfl).toIso
  let i₂ := (isGraphBij_of_matched_embedding hψ.isEmbedding hm).toIso
  have hinv : ∀ (g : E(J.toGraph)) (y z : V(J.toGraph)),
      J.toGraph.IsLink g.1 y.1 z.1 ↔
        J₁.toGraph.IsLink (i₁.edgeEquiv.symm g).1 (i₁.vertexEquiv.symm y).1
          (i₁.vertexEquiv.symm z).1 := by
    intro g y z
    have h := i₁.isLink_iff (i₁.edgeEquiv.symm g) (i₁.vertexEquiv.symm y) (i₁.vertexEquiv.symm z)
    simp only [Equiv.apply_symm_apply] at h
    exact h.symm
  refine ⟨{
    vertexEquiv := i₁.vertexEquiv.symm.trans i₂.vertexEquiv
    edgeEquiv := i₁.edgeEquiv.symm.trans i₂.edgeEquiv
    isLink_iff := fun g y z => (hinv g y z).trans (i₂.isLink_iff _ _ _) }, ?_⟩
  intro v
  change ψ (i₁.vertexEquiv.symm v).1 = φ v.1
  have h1 : (i₁.vertexEquiv (i₁.vertexEquiv.symm v)).1 = v.1 := by rw [Equiv.apply_symm_apply]
  change φ (i₁.vertexEquiv.symm v).1.1 = φ v.1
  rw [← h1]
  rfl

end GraphMinor.GM08
