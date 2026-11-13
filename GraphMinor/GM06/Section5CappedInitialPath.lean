module

public import GraphMinor.GM06.Section5CapDrawing
public import GraphMinor.Surface.DiscGrow
import GraphMinor.GM06.Section5ProperPaths

/-!
# The capped linkage path at the initial cuff

For the three-direction barrier in VI (5.7), page 133, capping
preserves subdrawing inclusion and path parametrizations. The
linkage path meets the initial cuff only at its initial vertex.
Consequently its capped image has exactly that one intersection
with the capped cuff. The two angular cuff arcs also retain their
injectivity and common-end conditions under the sphere embedding.
-/

public section
namespace GraphMinor.GM06
open Set Topology GraphMinor.Surface unitInterval

/-- A linkage path meets the first cuff only at its initial vertex. -/
theorem CylinderLinkage.U_inter_cuff1
    {k : ℕ} {G : Drawing ClosedCylinder} (L : CylinderLinkage k G)
    (hG : IsCylinderSection5Drawing k G) (i : Fin k) :
    (L.pathDrawing i).U ∩ cylinderCuff1 = {cylinderM1Point k i} := by
  ext x
  constructor
  · rintro ⟨hxP, hxC⟩
    have hxBd : x ∈ bd ClosedCylinder := by rw [bd_closedCylinder]; exact Or.inl hxC
    have hh : x ∈ {cylinderM1Point k i, L.curve i 1} :=
      L.U_inter_boundary hG i ▸ (show x ∈ (L.pathDrawing i).U ∩ bd ClosedCylinder from ⟨hxP, hxBd⟩)
    rcases hh with hh | hh
    · exact hh
    · have hxend : x = L.curve i 1 := mem_singleton_iff.mp hh
      have htC : L.curve i 1 ∈ cylinderCuff2 := by
        obtain ⟨j, hj⟩ := L.curve_one_mem i
        rw [← hj]
        rfl
      exact False.elim (disjoint_left.mp disjoint_cylinderCuffs hxC (hxend.symm ▸ htC))
  · rintro rfl
    refine ⟨?_, rfl⟩
    rw [← (L.curve_parametrizes i).2.1]
    exact ⟨0, (L.curve_parametrizes i).2.2.1⟩

/-- Capping preserves the vertex and edge inclusions of a subdrawing. -/
theorem cylinderSphereDrawing_isSubdrawing
    {P G : Drawing ClosedCylinder} (hP : P.IsSubdrawing G) :
    (cylinderSphereDrawing P).IsSubdrawing (cylinderSphereDrawing G) := by
  constructor
  · rw [cylinderSphereDrawing_V, cylinderSphereDrawing_V]
    exact image_mono hP.1
  · rw [cylinderSphereDrawing_E, cylinderSphereDrawing_E]
    exact image_mono hP.2

/-- A cylinder curve viewed in the capped sphere. -/
@[expose] noncomputable def cylinderSphereCurve (f : Curve ClosedCylinder) :
    Curve (OnePoint EuclideanPlane) :=
  ⟨cylinderToSphere ∘ f, continuous_cylinderToSphere.comp f.continuous⟩

/-- Capping preserves an injective parametrization and its two ends. -/
theorem cylinderSphereCurve_parametrizesSet
    {f : Curve ClosedCylinder} {X : Set ClosedCylinder} {s t : ClosedCylinder}
    (hf : ParametrizesSet f X s t) :
    ParametrizesSet (cylinderSphereCurve f) (cylinderToSphere '' X)
      (cylinderToSphere s) (cylinderToSphere t) := by
  refine ⟨injective_cylinderToSphere.comp hf.1, ?_, ?_, ?_⟩
  · change range (cylinderToSphere ∘ f) = _
    rw [range_comp, hf.2.1]
  · change cylinderToSphere (f 0) = _
    rw [hf.2.2.1]
  · change cylinderToSphere (f 1) = _
    rw [hf.2.2.2]

/-- The capped path and capped initial cuff have exactly their
initial point in common. -/
theorem CylinderLinkage.capped_U_inter_cuff1
    {k : ℕ} {G : Drawing ClosedCylinder} (L : CylinderLinkage k G)
    (hG : IsCylinderSection5Drawing k G) (i : Fin k) :
    (cylinderSphereDrawing (L.pathDrawing i)).U ∩ cylinderToSphere '' cylinderCuff1 =
      {cylinderToSphere (cylinderM1Point k i)} := by
  rw [cylinderSphereDrawing_U, ← image_inter injective_cylinderToSphere,
    L.U_inter_cuff1 hG i, image_singleton]

/-- The two initial cuff arcs keep their common-end and intersection
conditions when mapped to the sphere. -/
theorem isTwoArcs_cylinderToSphere {g h : I → ClosedCylinder} (hgh : IsTwoArcs g h) :
    IsTwoArcs (cylinderToSphere ∘ g) (cylinderToSphere ∘ h) := by
  refine ⟨⟨continuous_cylinderToSphere.comp hgh.arc_left.1,
      injective_cylinderToSphere.comp hgh.arc_left.2⟩,
    ⟨continuous_cylinderToSphere.comp hgh.arc_right.1,
      injective_cylinderToSphere.comp hgh.arc_right.2⟩,
    congrArg cylinderToSphere hgh.zero, congrArg cylinderToSphere hgh.one, ?_⟩
  intro r s hrs
  exact hgh.meet r s (injective_cylinderToSphere hrs)

end GraphMinor.GM06
