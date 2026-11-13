module

public import GraphMinor.GM06.Defs
import GraphMinor.GM06.Section4
import GraphMinor.GM06.Section4PathTools
import GraphMinor.GM06.Section5CylinderShear
import GraphMinor.GM06.Section5PathHomeomorph
import GraphMinor.GM06.Section5SinglePathCoordinates

/-!
# Coordinates for an arbitrary spanning cylinder path

For Reduction 3 of VI, page 129, normalize the two cuff ends by a
radius-preserving angular shear. The image path alone is then a
one-path Section 5 drawing. Its cylinder coordinates, followed by
the inverse shear, give coordinates on the original cylinder whose
seam follows the original path with its prescribed parameter.
-/

public section

namespace GraphMinor.GM06

open Set GraphMinor.Surface GraphMinor.GM07

/-- A proper spanning path with specified parametrization is the seam
of a cylinder homeomorphism. This supplies coordinates around the
edge contracted in Reduction 3. -/
theorem exists_cylinder_coordinates_of_spanning_path
    {P : Drawing ClosedCylinder} {s t : ClosedCylinder}
    (hP : IsPathDrawing P s t) (hs : s ∈ cylinderCuff1) (ht : t ∈ cylinderCuff2)
    (hB : P.U ∩ bd ClosedCylinder = {s, t})
    (f : Curve ClosedCylinder) (hf : ParametrizesSet f P.U s t) :
    ∃ H : Circle × unitInterval ≃ₜ ClosedCylinder,
      ∀ u : unitInterval, H (1, u) = f u := by
  obtain ⟨α, hrad, hαs, hαt⟩ := exists_cylinder_shear_normalizing_ends hs ht
  let Q := mapDrawingHomeo α P
  let g : Curve ClosedCylinder := ⟨α ∘ f, α.continuous.comp f.continuous⟩
  have hgs : g 0 = α s := congrArg α hf.2.2.1
  have hgt : g 1 = α t := congrArg α hf.2.2.2
  have hends := isPathDrawing_end_vertices hP
  have hαbd {x : ClosedCylinder} : α x ∈ bd ClosedCylinder ↔ x ∈ bd ClosedCylinder := by
    rw [bd_closedCylinder]
    change ((α x).1.1 = 1 ∨ (α x).1.1 = 2) ↔ (x.1.1 = 1 ∨ x.1.1 = 2)
    rw [hrad]
  have hQUbd : Q.U ∩ bd ClosedCylinder = {α s, α t} := by
    ext x
    constructor
    · rintro ⟨⟨y, hy, rfl⟩, hybd⟩
      have hyEnd : y ∈ ({s, t} : Set ClosedCylinder) := hB ▸ ⟨hy, hαbd.mp hybd⟩
      rcases mem_insert_iff.mp hyEnd with he | he
      · exact Or.inl (congrArg α he)
      · exact Or.inr (mem_singleton_iff.mpr (congrArg α (mem_singleton_iff.mp he)))
    · rintro (he | he)
      · rw [he]
        exact ⟨⟨s, P.V_subset_U hends.1, rfl⟩, hαbd.mpr (by rw [bd_closedCylinder]; exact Or.inl hs)⟩
      · have he' := mem_singleton_iff.mp he
        rw [he']
        exact ⟨⟨t, P.V_subset_U hends.2, rfl⟩, hαbd.mpr (by rw [bd_closedCylinder]; exact Or.inr ht)⟩
  have hproper : Q.IsProper := by
    rintro x ⟨hxbd, hxQ⟩
    have hxEnd : x ∈ ({α s, α t} : Set ClosedCylinder) := hQUbd ▸ ⟨hxQ, hxbd⟩
    rcases mem_insert_iff.mp hxEnd with he | he
    · exact ⟨s, hends.1, he.symm⟩
    · exact ⟨t, hends.2, (mem_singleton_iff.mp he).symm⟩
  have hboundary : Q.V ∩ bd ClosedCylinder = cylinderM1 1 ∪ cylinderM2 1 := by
    ext x
    constructor
    · intro hx
      have hxEnd : x ∈ ({α s, α t} : Set ClosedCylinder) :=
        hQUbd ▸ ⟨Q.V_subset_U hx.1, hx.2⟩
      rcases mem_insert_iff.mp hxEnd with he | he
      · exact Or.inl ⟨0, hαs.symm.trans he.symm⟩
      · exact Or.inr ⟨0, hαt.symm.trans (mem_singleton_iff.mp he).symm⟩
    · rintro (⟨j, hj⟩ | ⟨j, hj⟩)
      · have hj0 : j = 0 := Subsingleton.elim _ _
        subst j
        have hx : α s = x := hαs.trans hj
        exact ⟨⟨s, hends.1, hx⟩, hx ▸ hαbd.mpr (by rw [bd_closedCylinder]; exact Or.inl hs)⟩
      · have hj0 : j = 0 := Subsingleton.elim _ _
        subst j
        have hx : α t = x := hαt.trans hj
        exact ⟨⟨t, hends.2, hx⟩, hx ▸ hαbd.mpr (by rw [bd_closedCylinder]; exact Or.inr ht)⟩
  have hg : ParametrizesSet g Q.U (α s) (α t) := by
    refine ⟨α.injective.comp hf.1, ?_, hgs, hgt⟩
    change range (α ∘ f) = α '' P.U
    rw [range_comp, hf.2.1]
  let M : CylinderLinkage 1 Q := {
    pathDrawing := fun _ => Q
    curve := fun _ => g
    isSubdrawing := fun _ => ⟨⟨subset_rfl, subset_rfl⟩, subset_rfl⟩
    isPath := by
      intro j
      have hj : j = 0 := Subsingleton.elim _ _
      subst j
      rw [← hαs, hgt]
      exact isPathDrawing_map_homeo α hP
    curve_parametrizes := by
      intro j
      have hj : j = 0 := Subsingleton.elim _ _
      subst j
      rw [← hαs, hgt]
      exact hg
    curve_one_mem := fun _ => ⟨0, hαt.symm.trans hgt.symm⟩
    pairwise_disjoint := fun _ _ hne => False.elim (hne (Subsingleton.elim _ _)) }
  obtain ⟨H, hH⟩ := exists_cylinder_coordinates_of_single_path M
    ⟨by norm_num, hproper, hboundary⟩ (θ := windingNumber g) (fun _ => rfl)
  refine ⟨H.trans α.symm, ?_⟩
  intro u
  change α.symm (H (1, u)) = f u
  rw [hH]
  exact α.symm_apply_apply (f u)

end GraphMinor.GM06
