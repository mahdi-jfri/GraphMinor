module

public import GraphMinor.GM06.Alg57InputRep
public import GraphMinor.GM06.Alg511PolarReflection
import GraphMinor.GM06.Section5SmallPolar
import GraphMinor.Surface.InvarianceOfDomain
import Mathlib.Data.Finset.Sort

/-!
# Positively oriented input rotations exist

The counterclockwise rows of VI (5.7) use the plane orientation.
A small polar chart at a finite sphere point avoids infinity and
therefore lifts to a plane disc. Its boundary parametrization or
its inverse is positive. In the second case mirror the polar disc.
Mirroring preserves the radial graph germs. Sorting their finite
labels in the chosen positive chart gives a row with the required
ordinary geometric interpretation, without any reduction data.
-/

public section
namespace GraphMinor.GM06
open Set Topology Metric GraphMinor.Surface GraphMinor.GM11 unitInterval

private theorem angularMirror_zero_apply (w : Circle) : alg511AngularMirror 0 w = w⁻¹ := by
  change Circle.exp 0 * w⁻¹ = w⁻¹
  rw [Circle.exp_zero, one_mul]

private theorem polar_rim_injective : Function.Injective (polarDiscPoint 1) := by
  intro a b hab
  apply Subtype.ext
  have hh := congrArg (fun x : ClosedUnitDisc => planeOf.symm x.val) hab
  simpa only [polarDiscPoint, planeOf.symm_apply_apply, Icc.coe_one, Complex.ofReal_one, one_mul] using hh

private theorem polar_rim_range : range (polarDiscPoint 1) = {x : ClosedUnitDisc | x.val ∈ UnitCircle} := by
  ext x
  constructor
  · rintro ⟨w, rfl⟩
    simp [polarDiscPoint, UnitCircle]
  · intro hx
    have hxnorm : ‖x.val‖ = 1 := mem_sphere_zero_iff_norm.mp hx
    let w : Circle := ⟨planeOf.symm x.val, mem_sphere_zero_iff_norm.mpr (by rw [planeOf.symm.norm_map]; exact hxnorm)⟩
    refine ⟨w, Subtype.ext ?_⟩
    simp only [polarDiscPoint, Icc.coe_one, Complex.ofReal_one, one_mul, w, planeOf.apply_symm_apply]

/-- A finite polar disc has a positive orientation after at most
one reflection of its parameter disc. This fixes only this local
chart and makes no assertion about general surface homeomorphisms. -/
theorem positive_polar_or_mirror
    (Φ : C(ClosedUnitDisc, OnePoint EuclideanPlane))
    (hinj : Function.Injective Φ)
    (hfinite : range Φ ⊆ range ((↑) : EuclideanPlane → OnePoint EuclideanPlane)) :
    GM06PositivePolar Φ ∨ GM06PositivePolar
      (Φ.comp ⟨alg511DiscMirror 0, (alg511DiscMirror 0).continuous⟩) := by
  let e : EuclideanPlane ≃ₜ range ((↑) : EuclideanPlane → OnePoint EuclideanPlane) :=
    OnePoint.isOpenEmbedding_coe.isEmbedding.toHomeomorph
  let Ψ : C(ClosedUnitDisc, EuclideanPlane) :=
    ⟨fun z => e.symm ⟨Φ z, hfinite (mem_range_self z)⟩,
      e.symm.continuous.comp (Φ.continuous.subtype_mk (fun z => hfinite (mem_range_self z)))⟩
  have hcoe : ∀ z, (Ψ z : OnePoint EuclideanPlane) = Φ z := by
    intro z
    exact congrArg Subtype.val (e.apply_symm_apply ⟨Φ z, hfinite (mem_range_self z)⟩)
  let Z : C(ClosedUnitDisc, ℂ) := ⟨fun z => complexPlane.symm (Ψ z), complexPlane.symm.continuous.comp Ψ.continuous⟩
  have hZi : Function.Injective Z := by
    intro a b hab
    apply hinj
    rw [← hcoe a, ← hcoe b]
    exact congrArg (fun p : EuclideanPlane => (p : OnePoint EuclideanPlane)) (complexPlane.symm.injective hab)
  let D := range Z
  let E : ClosedUnitDisc ≃ₜ D := Continuous.homeoOfEquivCompactToT2
    (f := Equiv.ofInjective Z hZi) Z.continuous.rangeFactorization
  have hD : IsClosedDisc D := ⟨E⟩
  let φ : Circle → ℂ := fun w => Z (polarDiscPoint 1 w)
  have hφc : Continuous φ := Z.continuous.comp (by
    change Continuous (fun w => polarDiscPoint 1 w)
    exact (polarRimMap (ContinuousMap.id ClosedUnitDisc)).continuous)
  have hφi : Function.Injective φ := hZi.comp polar_rim_injective
  have hφrange : range φ = discBd D := by
    rw [disc_boundary D E]
    change range (Z ∘ polarDiscPoint 1) = Z '' {x : ClosedUnitDisc | x.val ∈ UnitCircle}
    rw [range_comp, polar_rim_range]
  have hcentre : Z polarCentre ∈ discInt D := by
    refine ⟨mem_range_self _, ?_⟩
    rw [← hφrange]
    rintro ⟨w, hw⟩
    exact polarDiscPoint_one_ne_centre w (hZi hw)
  rcases isPosParam_or_inv hD hφc hφi hφrange with hp | hp
  · exact Or.inl ⟨Ψ, fun z => (hcoe z).symm, hp.2.2.2 _ hcentre⟩
  · let Ψ' := Ψ.comp ⟨alg511DiscMirror 0, (alg511DiscMirror 0).continuous⟩
    refine Or.inr ⟨Ψ', fun z => (hcoe (alg511DiscMirror 0 z)).symm, ?_⟩
    have hcentre' : complexPlane.symm (Ψ' polarCentre) = Z polarCentre := by
      change complexPlane.symm (Ψ (alg511DiscMirror 0 polarCentre)) = _
      rw [alg511DiscMirror_centre]
      rfl
    have hφ' : (fun w => complexPlane.symm (Ψ' (polarDiscPoint 1 w))) = fun w => φ w⁻¹ := by
      funext w
      change complexPlane.symm (Ψ (alg511DiscMirror 0 (polarDiscPoint 1 w))) = _
      rw [alg511DiscMirror_polarDiscPoint, angularMirror_zero_apply]
      rfl
    rw [hcentre', hφ']
    exact hp.2.2.2 _ hcentre

/-- At a finite vertex with at least two ends, a positive polar
chart supplies all actual half-edge rays and their rim bijection. -/
theorem exists_positive_polar_halfedge_chart
    {Γ : Drawing (OnePoint EuclideanPlane)}
    {γ : Set (OnePoint EuclideanPlane) → I → OnePoint EuclideanPlane}
    (hγ : EdgePar Γ γ) {v : OnePoint EuclideanPlane} (hv : v ∈ Γ.V)
    (hvfinite : v ∈ range ((↑) : EuclideanPlane → OnePoint EuclideanPlane))
    (htwo : 2 ≤ Nat.card (halfEdges Γ γ v)) :
    ∃ (Φ : C(ClosedUnitDisc, OnePoint EuclideanPlane))
      (d : halfEdges Γ γ v ≃ {w : Circle | ∃ e ∈ Γ.E, polarRimMap Φ w ∈ e}),
      IsPolar Γ v Φ ∧ GM06PositivePolar Φ ∧
      ∀ a, ∀ t : I, 0 < t → Φ (polarDiscPoint t (d a).1) ∈ range (spoke γ a.1) := by
  have hS := IsSphere.isClosedSurface (show IsSphere (OnePoint EuclideanPlane) from ⟨Homeomorph.refl _⟩)
  obtain ⟨Φ, hΦ⟩ := exists_isPolar_of_sectors hS.1 hγ hv htwo
  obtain ⟨Ψ, hΨ, hfinite, d, hd⟩ := exists_polar_chart_with_halfedge_equiv hS.1 hγ hv hΦ
    OnePoint.isOpen_range_coe hvfinite
  rcases positive_polar_or_mirror Ψ hΨ.inj hfinite with hp | hp
  · exact ⟨Ψ, d, hΨ, hp, hd⟩
  · let Ψ' := Ψ.comp ⟨alg511DiscMirror 0, (alg511DiscMirror 0).continuous⟩
    have hΨ' : IsPolar Γ v Ψ' := alg511_isPolar_comp_discMirror hΨ 0
    have hmirror (t : I) (w : Circle) : Ψ' (polarDiscPoint t w) = Ψ (polarDiscPoint t w⁻¹) := by
      change Ψ (alg511DiscMirror 0 (polarDiscPoint t w)) = _
      rw [alg511DiscMirror_polarDiscPoint, angularMirror_zero_apply]
    let W := {w : Circle | ∃ e ∈ Γ.E, polarRimMap Ψ w ∈ e}
    let W' := {w : Circle | ∃ e ∈ Γ.E, polarRimMap Ψ' w ∈ e}
    let eW : W ≃ W' := {
      toFun := fun w => ⟨w.val⁻¹, by
        obtain ⟨e, he, hw⟩ := w.property
        refine ⟨e, he, ?_⟩
        change Ψ' (polarDiscPoint 1 w.val⁻¹) ∈ e
        rw [hmirror, inv_inv]
        exact hw⟩
      invFun := fun w => ⟨w.val⁻¹, by
        obtain ⟨e, he, hw⟩ := w.property
        refine ⟨e, he, ?_⟩
        change Ψ' (polarDiscPoint 1 w.val) ∈ e at hw
        rw [hmirror] at hw
        exact hw⟩
      left_inv := fun w => Subtype.ext (inv_inv w.val)
      right_inv := fun w => Subtype.ext (inv_inv w.val) }
    refine ⟨Ψ', d.trans eW, hΨ', hp, ?_⟩
    intro a t ht
    change Ψ' (polarDiscPoint t (d a).val⁻¹) ∈ _
    rw [hmirror, inv_inv]
    exact hd a t ht

/-- All finite vertices have positively interpreted counterclockwise
rows, with exactly the shared original and cuff directed labels. -/
theorem exists_successor_positive_rotation_row
    {Γ : Drawing (OnePoint EuclideanPlane)} {m : ℕ} (edge : Fin m ≃ Γ.E)
    {γ : Set (OnePoint EuclideanPlane) → I → OnePoint EuclideanPlane}
    (hγ : EdgePar Γ γ) {v : OnePoint EuclideanPlane} (hv : v ∈ Γ.V)
    (hvfinite : v ∈ range ((↑) : EuclideanPlane → OnePoint EuclideanPlane)) :
    ∃ row : List ℕ, GM06SuccessorRotationRowRep edge γ v row := by
  classical
  by_cases htwo : 2 ≤ Nat.card (halfEdges Γ γ v)
  · obtain ⟨Φ, d, hp, hpos, hd⟩ := exists_positive_polar_halfedge_chart hγ hv hvfinite htwo
    obtain ⟨row, z, hnd, hmem, hz, hzi, hs, _⟩ :=
      exists_polar_rotation_row d (halfEdgeLabel edge) (halfEdgeLabel_injective edge)
    refine ⟨row, hnd, hmem, Or.inr ⟨Φ, z, hp, hpos, hzi, hs, ?_, ?_⟩⟩
    · intro a t ht
      rw [hz a]
      exact hd a t ht
    · exact polar_rotation_row_edge_labels hγ hp d hd edge row z hmem hz
  · let H := halfEdges Γ γ v
    let : Fintype H := (finite_halfEdges Γ γ v).fintype
    let e : Fin (Fintype.card H) ≃ H := (Fintype.equivFin H).symm
    let row := List.ofFn (fun i => halfEdgeLabel edge (e i))
    have hnd : row.Nodup := List.nodup_ofFn_ofInjective
      ((halfEdgeLabel_injective edge).comp e.injective)
    have hmem (r : ℕ) : r ∈ row ↔ ∃ a : H, halfEdgeLabel edge a = r := by
      rw [List.mem_ofFn]
      constructor
      · rintro ⟨i, hi⟩
        exact ⟨e i, hi⟩
      · rintro ⟨a, ha⟩
        obtain ⟨i, rfl⟩ := e.surjective a
        exact ⟨i, ha⟩
    refine ⟨row, hnd, hmem, Or.inl ?_⟩
    change row.length ≤ 1
    rw [show row.length = Fintype.card H from List.length_ofFn]
    have hcard : Nat.card H = Fintype.card H := Nat.card_eq_fintype_card
    change ¬ 2 ≤ Nat.card H at htwo
    omega

end GraphMinor.GM06
