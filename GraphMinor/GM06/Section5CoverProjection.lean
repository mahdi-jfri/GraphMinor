module

public import GraphMinor.GM06.Defs
public import Mathlib.Topology.IsLocalHomeomorph
import Mathlib.Topology.Covering.Basic
import Mathlib.Topology.OpenPartialHomeomorph.Constructions

/-!
# Local sheets of the angular cover

The radial-angular projection is a local homeomorphism, including
at the cuffs: keep the radial coordinate and use a local inverse of
the circle exponential. Continuous sections over an open part of the
cylinder therefore have open images in the cover. This is used to
identify the chosen strip component with the cut-disc sheet in the
one-path proof of VI Section 5.
-/

public section
namespace GraphMinor.GM06
open Set Topology GraphMinor.Surface

private def cylinderBaseCoordinates : ClosedCylinder ≃ₜ Icc (1 : ℝ) 2 × Circle where
  toFun p := (⟨p.1.1, p.2.1⟩, p.1.2)
  invFun p := ⟨(p.1.1, p.2), p.1.2, mem_univ _⟩
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

/-- The universal angular projection is a local homeomorphism at
both interior points and cuff points. -/
theorem isLocalHomeomorph_cylinderCoverProjection : IsLocalHomeomorph cylinderCoverProjection := by
  intro p
  obtain ⟨e, he, hfun⟩ := Circle.isCoveringMap_exp.isLocalHomeomorph p.2
  let E := ((OpenPartialHomeomorph.refl (Icc (1 : ℝ) 2)).prod e).trans
    cylinderBaseCoordinates.symm.toOpenPartialHomeomorph
  refine ⟨E, ?_, ?_⟩
  · exact ⟨⟨mem_univ _, he⟩, mem_univ _⟩
  · funext q
    apply Subtype.ext
    apply Prod.ext
    · rfl
    · change Circle.exp q.2 = e q.2
      exact congr_fun hfun q.2

/-- The angular projection sends open sets of the cover to open sets
of the cylinder. -/
theorem isOpenMap_cylinderCoverProjection : IsOpenMap cylinderCoverProjection :=
  isLocalHomeomorph_cylinderCoverProjection.isOpenMap

end GraphMinor.GM06
