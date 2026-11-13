module

public import GraphMinor.GM06.Section5CapDrawing
public import GraphMinor.GM06.Section5CollapseBoundaryCrossings
import GraphMinor.GM06.Section5AnnulusInterior
import GraphMinor.GM06.Section5CollapseChartFibers
import Mathlib.Topology.ContinuousOn

/-!
# Extending the rectangular collapse across the two caps

The rotations of VI (5.7), page 133, are interpreted on the sphere.
A boundary-fixing cylinder homotopy extends across both caps by the
identity. Closed-set pasting gives continuity. The extension has
exactly the old exceptional fibre in the annulus, and is injective
elsewhere. Its support is the image of the old rectangular support,
so its frontier and all cap points remain fixed.

This supplies a sphere map for the fixed-boundary argument in
Lemma 8 of our proof of VI (5.7) (outlined in `Alg57Algorithm.lean`). It makes no assertion about
orientation signs of arbitrary surface homeomorphisms.
-/

public section
namespace GraphMinor.GM06
open Set Topology GraphMinor.Surface

private theorem glue_closed_chart_homotopy
    {S K : Type*} [TopologicalSpace S] [TopologicalSpace K] [Nonempty K]
    {D : Set S} (hD : IsClosed D) (e : K ≃ₜ D)
    (H : C(unitInterval × K, K))
    (hfix : ∀ x, (e x).val ∈ frontier D → ∀ t, H (t, x) = x) :
    ∃ F : C(unitInterval × S, S),
      (∀ t x, F (t, (e x).val) = (e (H (t, x))).val) ∧
      ∀ y ∉ D, ∀ t, F (t, y) = y := by
  classical
  let x₀ : K := Classical.choice inferInstance
  let J : S → K := fun y => if hy : y ∈ D then e.symm ⟨y, hy⟩ else x₀
  have hJe (x : K) : J (e x).val = x := by
    simp only [J, dite_eq_left (e x).property]
    exact e.symm_apply_apply x
  have hJc : ContinuousOn J D := by
    rw [continuousOn_iff_continuous_domRestrict]
    apply e.symm.continuous.congr
    intro y
    simp only [J, Set.domRestrict_apply, dite_eq_left y.property]
  let F : unitInterval × S → S := fun q =>
    if q.2 ∈ D then (e (H (q.1, J q.2))).val else q.2
  have hF1 : ContinuousOn F (univ ×ˢ D) := by
    have hc : ContinuousOn (fun q : unitInterval × S => (e (H (q.1, J q.2))).val)
        (univ ×ˢ D) :=
      (continuous_subtype_val.comp e.continuous).continuousOn.comp
        (H.continuous.continuousOn.comp
          (continuousOn_fst.prodMk (hJc.comp continuousOn_snd (fun q hq => hq.2)))
          (fun _ _ => mem_univ _)) (fun _ _ => mem_univ _)
    apply hc.congr
    rintro ⟨t, y⟩ ⟨_, hy⟩
    exact ite_eq_left hy
  have hF2 : ContinuousOn F (univ ×ˢ (interior D)ᶜ) := by
    apply continuousOn_snd.congr
    rintro ⟨t, y⟩ ⟨_, hy⟩
    change (if y ∈ D then _ else y) = y
    split_ifs with hyD
    · have hyfr : y ∈ frontier D := by
        rw [hD.frontier_eq]
        exact ⟨hyD, hy⟩
      have hJy : (e (J y)).val = y := by
        simp only [J, dite_eq_left hyD, e.apply_symm_apply]
      rw [hfix (J y) (hJy.symm ▸ hyfr) t, hJy]
    · rfl
  have hcover : (univ ×ˢ D) ∪ (univ ×ˢ (interior D)ᶜ) =
      (univ : Set (unitInterval × S)) := by
    ext ⟨t, y⟩
    simp only [mem_union, mem_prod, mem_univ, true_and, iff_true]
    by_cases hy : y ∈ interior D
    · exact Or.inl (interior_subset hy)
    · exact Or.inr hy
  have hc : Continuous F := by
    rw [← continuousOn_univ, ← hcover]
    exact hF1.union_of_isClosed hF2 (isClosed_univ.prod hD)
      (isClosed_univ.prod isOpen_interior.isClosed_compl)
  refine ⟨⟨F, hc⟩, ?_, ?_⟩
  · intro t x
    change (if (e x).val ∈ D then _ else _) = _
    rw [ite_eq_left (e x).property, hJe]
  · intro y hy t
    exact ite_eq_right hy

/-- An annulus point on the frontier of the full cylinder image must
be a cuff point. An interior cylinder point has an open annulus
neighbourhood in the sphere. -/
theorem mem_boundary_of_cylinder_image_frontier {x : ClosedCylinder}
    (hx : cylinderToSphere x ∈ frontier (range cylinderToSphere)) :
    x ∈ bd ClosedCylinder := by
  by_contra hn
  have hsub : cylinderToSphere '' (bd ClosedCylinder)ᶜ ⊆ range cylinderToSphere :=
    image_subset_range _ _
  have hi : cylinderToSphere x ∈ interior (range cylinderToSphere) :=
    interior_mono hsub (by
      rw [isOpen_image_cylinderToSphere_compl_boundary.interior_eq]
      exact ⟨x, hn, rfl⟩)
  exact hx.2 hi

/-- A cylinder homotopy fixing both cuffs extends continuously to
the sphere, fixing every point of both caps. -/
theorem exists_capped_cylinder_homotopy
    (H : C(unitInterval × ClosedCylinder, ClosedCylinder))
    (hbd : ∀ x ∈ bd ClosedCylinder, ∀ t, H (t, x) = x) :
    ∃ K : C(unitInterval × OnePoint EuclideanPlane, OnePoint EuclideanPlane),
      (∀ t x, K (t, cylinderToSphere x) = cylinderToSphere (H (t, x))) ∧
      ∀ y ∉ range cylinderToSphere, ∀ t, K (t, y) = y := by
  let : Nonempty ClosedCylinder := ⟨cylinderM1Point 1 0⟩
  let e : ClosedCylinder ≃ₜ range cylinderToSphere :=
    isClosedEmbedding_cylinderToSphere.isEmbedding.toHomeomorph
  have hfix : ∀ x, (e x).val ∈ frontier (range cylinderToSphere) →
      ∀ t, H (t, x) = x := fun x hx =>
    hbd x (mem_boundary_of_cylinder_image_frontier hx)
  exact glue_closed_chart_homotopy isClosedEmbedding_cylinderToSphere.isClosed_range e H hfix

/-- The extension of an identity-outside cylinder homotopy is also
the identity outside the image of that support, including both caps. -/
theorem capped_homotopy_eq_outside_support
    {H : C(unitInterval × ClosedCylinder, ClosedCylinder)}
    {K : C(unitInterval × OnePoint EuclideanPlane, OnePoint EuclideanPlane)}
    (hK : ∀ t x, K (t, cylinderToSphere x) = cylinderToSphere (H (t, x)))
    (hoff : ∀ y ∉ range cylinderToSphere, ∀ t, K (t, y) = y)
    {D : Set ClosedCylinder} (hout : ∀ x ∉ D, ∀ t, H (t, x) = x) :
    ∀ y ∉ cylinderToSphere '' D, ∀ t, K (t, y) = y := by
  intro y hy t
  by_cases hyr : y ∈ range cylinderToSphere
  · obtain ⟨x, rfl⟩ := hyr
    have hxD : x ∉ D := fun hx => hy ⟨x, hx, rfl⟩
    rw [hK, hout x hxD t]
  · exact hoff y hyr t

/-- The sphere extension has exactly the same exceptional fibre,
embedded in the cylinder image. No cap point enters that fibre. -/
theorem fibre_of_capped_cylinder_collapse
    {π : ClosedCylinder → ClosedCylinder}
    {πS : OnePoint EuclideanPlane → OnePoint EuclideanPlane}
    (hπS : ∀ x, πS (cylinderToSphere x) = cylinderToSphere (π x))
    (hoff : ∀ y ∉ range cylinderToSphere, πS y = y)
    {s : ClosedCylinder} {A : Set ClosedCylinder} (hfibre : π ⁻¹' {s} = A) :
    πS ⁻¹' {cylinderToSphere s} = cylinderToSphere '' A := by
  ext y
  constructor
  · intro hy
    have hyr : y ∈ range cylinderToSphere := by
      by_contra hn
      have he : y = cylinderToSphere s := (hoff y hn).symm.trans hy
      exact hn (he ▸ mem_range_self s)
    obtain ⟨x, rfl⟩ := hyr
    have hx : π x = s := injective_cylinderToSphere ((hπS x).symm.trans hy)
    exact ⟨x, hfibre ▸ hx, rfl⟩
  · rintro ⟨x, hx, rfl⟩
    have hxs : π x = s := show x ∈ π ⁻¹' {s} from hfibre.symm ▸ hx
    change πS (cylinderToSphere x) = cylinderToSphere s
    rw [hπS, hxs]

/-- Injectivity away from the collapsed cylinder set extends across
the fixed caps. Cylinder images stay in the annulus, so the two
parts cannot acquire a new identification. -/
theorem injOn_of_capped_cylinder_collapse
    {π : ClosedCylinder → ClosedCylinder}
    {πS : OnePoint EuclideanPlane → OnePoint EuclideanPlane}
    (hπS : ∀ x, πS (cylinderToSphere x) = cylinderToSphere (π x))
    (hoff : ∀ y ∉ range cylinderToSphere, πS y = y)
    {A : Set ClosedCylinder} (hi : InjOn π Aᶜ) :
    InjOn πS (cylinderToSphere '' A)ᶜ := by
  intro x hx y hy heq
  by_cases hxr : x ∈ range cylinderToSphere
  · obtain ⟨a, rfl⟩ := hxr
    by_cases hyr : y ∈ range cylinderToSphere
    · obtain ⟨b, rfl⟩ := hyr
      have ha : a ∉ A := fun h => hx ⟨a, h, rfl⟩
      have hb : b ∉ A := fun h => hy ⟨b, h, rfl⟩
      rw [hπS, hπS] at heq
      exact congrArg cylinderToSphere (hi ha hb (injective_cylinderToSphere heq))
    · rw [hπS, hoff y hyr] at heq
      exact False.elim (hyr ⟨π a, heq⟩)
  · rw [hoff x hxr] at heq
    by_cases hyr : y ∈ range cylinderToSphere
    · obtain ⟨b, rfl⟩ := hyr
      rw [hπS] at heq
      exact False.elim (hxr ⟨π b, heq.symm⟩)
    · rwa [hoff y hyr] at heq

/-- Surjectivity of the cylinder collapse extends to surjectivity
of the sphere map, with the two caps fixed. -/
theorem surjective_of_capped_cylinder_collapse
    {π : ClosedCylinder → ClosedCylinder}
    {πS : OnePoint EuclideanPlane → OnePoint EuclideanPlane}
    (hπS : ∀ x, πS (cylinderToSphere x) = cylinderToSphere (π x))
    (hoff : ∀ y ∉ range cylinderToSphere, πS y = y)
    (hs : Function.Surjective π) : Function.Surjective πS := by
  intro y
  by_cases hyr : y ∈ range cylinderToSphere
  · obtain ⟨b, rfl⟩ := hyr
    obtain ⟨a, rfl⟩ := hs b
    exact ⟨cylinderToSphere a, hπS a⟩
  · exact ⟨y, hoff y hyr⟩

/-- The actual cylinder collapse and its homotopy have a capped
extension with the same endpoints and fixed support boundary.
This is the map used when reading the new positive rotation on
the sphere; it also fixes the entire support frontier throughout. -/
theorem exists_capped_cylinder_collapse
    (π : C(ClosedCylinder, ClosedCylinder))
    (H : C(unitInterval × ClosedCylinder, ClosedCylinder))
    (h0 : ∀ x, H (0, x) = x) (h1 : ∀ x, H (1, x) = π x)
    (hbd : ∀ x ∈ bd ClosedCylinder, ∀ t, H (t, x) = x)
    {D : Set ClosedCylinder} (hout : ∀ x ∉ D, ∀ t, H (t, x) = x) :
    ∃ (πS : C(OnePoint EuclideanPlane, OnePoint EuclideanPlane))
      (K : C(unitInterval × OnePoint EuclideanPlane, OnePoint EuclideanPlane)),
      (∀ x, πS (cylinderToSphere x) = cylinderToSphere (π x)) ∧
      (∀ y ∉ range cylinderToSphere, πS y = y) ∧
      (∀ y, K (0, y) = y) ∧ (∀ y, K (1, y) = πS y) ∧
      (∀ t x, K (t, cylinderToSphere x) = cylinderToSphere (H (t, x))) ∧
      (∀ y ∉ cylinderToSphere '' D, ∀ t, K (t, y) = y) ∧
      ∀ y ∈ frontier (cylinderToSphere '' D), ∀ t, K (t, y) = y := by
  obtain ⟨K, hK, hKoff⟩ := exists_capped_cylinder_homotopy H hbd
  let πS : C(OnePoint EuclideanPlane, OnePoint EuclideanPlane) :=
    ⟨fun y => K (1, y), K.continuous.comp (continuous_const.prodMk continuous_id)⟩
  have hKout := capped_homotopy_eq_outside_support hK hKoff hout
  refine ⟨πS, K, ?_, ?_, ?_, fun _ => rfl, hK, hKout,
    collapse_homotopy_fixes_frontier K _ hKout⟩
  · intro x
    change K (1, cylinderToSphere x) = _
    rw [hK, h1]
  · intro y hy
    exact hKoff y hy 1
  · intro y
    by_cases hyr : y ∈ range cylinderToSphere
    · obtain ⟨x, rfl⟩ := hyr
      rw [hK, h0]
    · exact hKoff y hyr 0

/-- Retained points have singleton fibres throughout the capped
rectangular homotopy. Fixed cap points cannot meet annulus points,
and the remaining assertion is the exact rectangle calculation. -/
theorem capped_rectangle_homotopy_eq_iff_off_segment
    {D : Set ClosedCylinder} (e : Section5CollapseRectangle ≃ₜ D)
    (H : C(unitInterval × ClosedCylinder, ClosedCylinder))
    (K : C(unitInterval × OnePoint EuclideanPlane, OnePoint EuclideanPlane))
    (hchart : ∀ t z, H (t, (e z).val) = (e (section5RectangleCollapseHomotopy (t, z))).val)
    (hout : ∀ x ∉ D, ∀ t, H (t, x) = x)
    (hK : ∀ t x, K (t, cylinderToSphere x) = cylinderToSphere (H (t, x)))
    (hoff : ∀ y ∉ range cylinderToSphere, ∀ t, K (t, y) = y)
    {w : OnePoint EuclideanPlane}
    (hw : w ∉ cylinderToSphere '' ((fun z => (e z).val) '' {z | z.1.1 = 0 ∧ z.2.1 ≤ 1}))
    (t : unitInterval) (x : OnePoint EuclideanPlane) : K (t, x) = K (t, w) ↔ x = w := by
  constructor
  · intro heq
    by_cases hwr : w ∈ range cylinderToSphere
    · obtain ⟨v, rfl⟩ := hwr
      have hv : v ∉ (fun z => (e z).val) '' {z | z.1.1 = 0 ∧ z.2.1 ≤ 1} :=
        fun h => hw ⟨v, h, rfl⟩
      by_cases hxr : x ∈ range cylinderToSphere
      · obtain ⟨y, rfl⟩ := hxr
        rw [hK, hK] at heq
        exact congrArg cylinderToSphere
          ((rectangle_homotopy_eq_iff_of_off_segment e H hchart hout hv t y).mp
            (injective_cylinderToSphere heq))
      · rw [hoff x hxr t, hK] at heq
        exact False.elim (hxr ⟨H (t, v), heq.symm⟩)
    · by_cases hxr : x ∈ range cylinderToSphere
      · obtain ⟨y, rfl⟩ := hxr
        rw [hK, hoff w hwr t] at heq
        exact False.elim (hwr ⟨H (t, y), heq⟩)
      · rwa [hoff x hxr t, hoff w hwr t] at heq
  · rintro rfl
    rfl

/-- The capped rectangular homotopy keeps all finite points finite.
Infinity is a fixed cap point with a singleton fibre at every stage. -/
theorem capped_rectangle_homotopy_ne_infty
    {D : Set ClosedCylinder} (e : Section5CollapseRectangle ≃ₜ D)
    (H : C(unitInterval × ClosedCylinder, ClosedCylinder))
    (K : C(unitInterval × OnePoint EuclideanPlane, OnePoint EuclideanPlane))
    (hchart : ∀ t z, H (t, (e z).val) = (e (section5RectangleCollapseHomotopy (t, z))).val)
    (hout : ∀ x ∉ D, ∀ t, H (t, x) = x)
    (hK : ∀ t x, K (t, cylinderToSphere x) = cylinderToSphere (H (t, x)))
    (hoff : ∀ y ∉ range cylinderToSphere, ∀ t, K (t, y) = y)
    (t : unitInterval) {x : OnePoint EuclideanPlane} (hx : x ≠ OnePoint.infty) :
    K (t, x) ≠ OnePoint.infty := by
  have hinf : (OnePoint.infty : OnePoint EuclideanPlane) ∉ range cylinderToSphere := by
    rintro ⟨p, hp⟩
    exact OnePoint.coe_ne_infty (cylToPlane p) hp
  have hinfSeg : (OnePoint.infty : OnePoint EuclideanPlane) ∉
      cylinderToSphere '' ((fun z => (e z).val) '' {z | z.1.1 = 0 ∧ z.2.1 ≤ 1}) :=
    fun h => hinf (image_subset_range _ _ h)
  intro heq
  apply hx
  apply (capped_rectangle_homotopy_eq_iff_off_segment e H K hchart hout hK hoff hinfSeg t x).mp
  exact heq.trans (hoff OnePoint.infty hinf t).symm

end GraphMinor.GM06
