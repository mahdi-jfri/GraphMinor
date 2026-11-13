module

public import GraphMinor.GM06.Defs
public import GraphMinor.GM06.Section5CapDrawing
public import Mathlib.Topology.IsLocalHomeomorph
import Mathlib.Topology.OpenPartialHomeomorph.Constructions
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import GraphMinor.GM06.Section5AnnulusInterior
import GraphMinor.GM06.Section5RegionInterior
import GraphMinor.Surface.Cuffs

/-!
# Local charts for the angular cylinder cover

In the lifted region argument for VI (5.5), page 130, the angular
projection is a local homeomorphism, including at cuff points.
The circle exponential supplies the angular chart, while the
radial coordinate remains unchanged.
-/

public section
namespace GraphMinor.GM06
open Set Topology GraphMinor.Surface

/-- The angular-cover projection is a local homeomorphism at every
point, including the points on either cuff. -/
theorem isLocalHomeomorph_cylinderCoverProjection :
    IsLocalHomeomorph cylinderCoverProjection := by
  let e : ClosedCylinder ≃ₜ (Icc (1 : ℝ) 2 × Circle) :=
    { toFun := fun p => (⟨p.1.1, p.2.1⟩, p.1.2)
      invFun := fun p => ⟨(p.1.1, p.2), p.1.2, trivial⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      continuous_toFun := by fun_prop
      continuous_invFun := by fun_prop }
  intro p
  obtain ⟨a, ha, he⟩ := Circle.isCoveringMap_exp.isLocalHomeomorph p.2
  let k := (OpenPartialHomeomorph.refl (Icc (1 : ℝ) 2)).prod a
  refine ⟨k.trans e.symm.toOpenPartialHomeomorph, ⟨⟨trivial, ha⟩, trivial⟩, ?_⟩
  funext q
  apply Subtype.ext
  apply Prod.ext
  · rfl
  · exact congrFun he q.2

/-- Away from its cuffs, the capped-cylinder embedding is a local
homeomorphism into the sphere. -/
theorem isLocalHomeomorphOn_cylinderToSphere_off_boundary :
    IsLocalHomeomorphOn cylinderToSphere (bd ClosedCylinder)ᶜ := by
  let U : Set ClosedCylinder := (bd ClosedCylinder)ᶜ
  have hUo : IsOpen U :=
    (cuff_statement ClosedCylinder isSurface_closedCylinder).1.isOpen_compl
  have hEmb : IsOpenEmbedding (U.domRestrict cylinderToSphere) := by
    refine ⟨isClosedEmbedding_cylinderToSphere.isEmbedding.comp IsEmbedding.subtypeVal, ?_⟩
    have heq : range (U.domRestrict cylinderToSphere) = cylinderToSphere '' U := by
      ext y
      constructor
      · rintro ⟨x, rfl⟩
        exact ⟨x.1, x.2, rfl⟩
      · rintro ⟨x, hx, rfl⟩
        exact ⟨⟨x, hx⟩, rfl⟩
    rw [heq]
    exact isOpen_image_cylinderToSphere_compl_boundary
  apply (isLocalHomeomorphOn_iff_isOpenEmbedding_restrict _).mpr
  exact fun x hx => ⟨U, hUo.mem_nhds hx, hEmb⟩

/-- At every off-cuff point, the angular cover followed by the
sphere embedding has a local homeomorphism chart. -/
theorem isLocalHomeomorphOn_cover_to_sphere_off_boundary :
    IsLocalHomeomorphOn (fun p => cylinderToSphere (cylinderCoverProjection p))
      (cylinderCoverProjection ⁻¹' (bd ClosedCylinder)ᶜ) :=
  isLocalHomeomorphOn_cylinderToSphere_off_boundary.comp
    isLocalHomeomorph_cylinderCoverProjection.isLocalHomeomorphOn (fun _ h => h)

end GraphMinor.GM06
