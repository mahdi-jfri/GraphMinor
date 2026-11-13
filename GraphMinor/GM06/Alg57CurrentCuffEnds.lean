module

public import GraphMinor.GM06.Alg57CurrentDrawingRep
public import GraphMinor.GM06.Alg57SourceCuffCalibration
import GraphMinor.GM06.Alg57CuffFace
import GraphMinor.GM06.Section5AnnulusInterior

/-!
# The signed cuff ends of the actual current drawing

For the source comparison in Lemma 8 of VI (5.7), page 133, the
current drawing relation already supplies the concrete inner cuff
curves and their permanent labels. Construct their two directed
ends at the selected source. Their words are the forward end of
the following gap and the reverse end of the preceding gap. They
remain distinct when the two gaps are the same loop for k = 1.
The pointwise exponential equations and the source's complex
coordinate are derived from these actual input parametrizations.
-/

public section
namespace GraphMinor.GM06
open Set Metric Topology GraphMinor.Surface GraphMinor.GM11 GraphMinor.Compute unitInterval

/-- The current arrays determine the two actual signed inner cuff
ends, their exact permanent words, and their exponential half-spokes. -/
theorem GM06CurrentDrawingRep.inner_cuff_ends
    {k : ℕ} {x : GM06SuccessorInput} {G : Drawing ClosedCylinder}
    {L : CylinderLinkage k G} (rep : GM06CurrentDrawingRep x G L) (i : Fin k) :
    let q : ℂ := ((1 / 2 : ℝ) : ℂ) * Complex.exp
      (((2 * ((i.val + 1 : ℕ) : ℝ) * Real.pi / k : ℝ) : ℂ) * Complex.I)
    ∃ minus plus : halfEdges (cylinderSphereDrawing rep.cuffed) rep.par
        (cylinderToSphere (cylinderM1Point k i)),
      minus ≠ plus ∧
      minus.val = (cylinderToSphere '' (initialCuffGapCurve k (finPredCycle i) '' Ioo 0 1), true) ∧
      plus.val = (cylinderToSphere '' (initialCuffGapCurve k i '' Ioo 0 1), false) ∧
      gm06PersistentHalfEdgeLabel rep.label minus = 2 * (rep.tagged.length + (finPredCycle i).val) + 1 ∧
      gm06PersistentHalfEdgeLabel rep.label plus = 2 * (rep.tagged.length + i.val) ∧
      cylinderToSphere (cylinderM1Point k i) = toSph q ∧ ‖q‖ = 1 / 2 ∧
      (∀ t, spoke rep.par minus.val t = toSph (q * Complex.exp
        (((Real.pi / k : ℝ) : ℂ) * (t : ℂ) * (Circle.exp (-(Real.pi / 2)) : ℂ)))) ∧
      ∀ t, spoke rep.par plus.val t = toSph (q * Complex.exp
        (((Real.pi / k : ℝ) : ℂ) * (t : ℂ) * (Circle.exp (Real.pi / 2) : ℂ))) := by
  classical
  dsimp only
  let q : ℂ := ((1 / 2 : ℝ) : ℂ) * Complex.exp
    (((2 * ((i.val + 1 : ℕ) : ℝ) * Real.pi / k : ℝ) : ℂ) * Complex.I)
  obtain ⟨fminus, hfminus, hlminus⟩ := rep.inner_labels (finPredCycle i)
  obtain ⟨fplus, hfplus, hlplus⟩ := rep.inner_labels i
  have hplus0 : initialCuffGapCurve k i 0 = cylinderM1Point k i := by
    have hh := initialCuffGapCurve_forward_half i 0
    simpa only [halfPar_zero, endOf, Bool.false_eq_true, ite_false, Icc.coe_zero,
      mul_zero, add_zero, cylinderM1Point] using hh
  have hminus1 : initialCuffGapCurve k (finPredCycle i) 1 = cylinderM1Point k i := by
    have hh := initialCuffGapCurve_backward_half i.pos i 0
    simpa only [halfPar_zero, endOf, ite_true, Icc.coe_zero,
      mul_zero, sub_zero, cylinderM1Point] using hh
  let minus : halfEdges (cylinderSphereDrawing rep.cuffed) rep.par
      (cylinderToSphere (cylinderM1Point k i)) :=
    ⟨(fminus.val, true), fminus.property, by
      change rep.par fminus.val 1 = _
      rw [hfminus, rep.inner_par, hminus1]⟩
  let plus : halfEdges (cylinderSphereDrawing rep.cuffed) rep.par
      (cylinderToSphere (cylinderM1Point k i)) :=
    ⟨(fplus.val, false), fplus.property, by
      change rep.par fplus.val 0 = _
      rw [hfplus, rep.inner_par, hplus0]⟩
  have hlabelsminus : gm06PersistentHalfEdgeLabel rep.label minus =
      2 * (rep.tagged.length + (finPredCycle i).val) + 1 := by
    change 2 * rep.label fminus + 1 = _
    rw [hlminus]
  have hlabelsplus : gm06PersistentHalfEdgeLabel rep.label plus =
      2 * (rep.tagged.length + i.val) := by
    change 2 * rep.label fplus + 0 = _
    rw [hlplus, add_zero]
  have hsource : cylinderToSphere (cylinderM1Point k i) = toSph q := by
    change cylinderToSphere (cylinderPoint 1 (by simp)
      (2 * ((i.val + 1 : ℕ) : ℝ) * Real.pi / k)) = _
    rw [cylinderToSphere_cylinderPoint]
  have hq : ‖q‖ = 1 / 2 := by
    dsimp only [q]
    rw [norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one, Complex.norm_real,
      Real.norm_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2)]
  refine ⟨minus, plus, ?_, ?_, ?_, hlabelsminus, hlabelsplus, hsource, hq, ?_, ?_⟩
  · intro heq
    have hh := congrArg (fun a : halfEdges (cylinderSphereDrawing rep.cuffed) rep.par
      (cylinderToSphere (cylinderM1Point k i)) => a.val.2) heq
    cases hh
  · exact Prod.ext hfminus rfl
  · exact Prod.ext hfplus rfl
  · intro t
    change rep.par fminus.val (halfPar true t) = _
    rw [hfminus, rep.inner_par]
    exact cylinderToSphere_backward_cuff_half i.pos i t
  · intro t
    change rep.par fplus.val (halfPar false t) = _
    rw [hfplus, rep.inner_par]
    exact cylinderToSphere_forward_cuff_half i t


/-- Every point on an ordinary edge of a proper cylinder drawing
has a finite complex coordinate strictly outside the inner cuff. -/
theorem exists_complex_coordinate_of_proper_cylinder_edge
    {G : Drawing ClosedCylinder} (hG : G.IsProper) {e : Set ClosedCylinder}
    (he : e ∈ G.E) {y : OnePoint EuclideanPlane} (hy : y ∈ cylinderToSphere '' e) :
    ∃ z : ℂ, toSph z = y ∧ 1 / 2 < ‖z‖ := by
  obtain ⟨p, hp, rfl⟩ := hy
  have hoff : p ∉ bd ClosedCylinder := fun hbd =>
    (he.2.1 hp).2 (hG ⟨hbd, (he.2.1 hp).1⟩)
  have hnorm := mem_image_of_mem cylToPlane (show p ∈ (bd ClosedCylinder)ᶜ from hoff)
  rw [image_cylToPlane_compl_boundary] at hnorm
  refine ⟨complexPlane.symm (cylToPlane p), ?_, ?_⟩
  · change (complexPlane (complexPlane.symm (cylToPlane p)) : OnePoint EuclideanPlane) = _
    rw [complexPlane.apply_symm_apply]
    rfl
  · rw [LinearIsometryEquiv.norm_map]
    exact hnorm.1

/-- The signed cuff order holds in every positive polar source
chart. Shrink into the exponential neighbourhood, retaining all
end directions, and derive the ordinary rim coordinate from the
proper cylinder drawing. No source-row order is a premise. -/
theorem source_signed_cuff_order
    {Γ : Drawing (OnePoint EuclideanPlane)}
    {γ : Set (OnePoint EuclideanPlane) → I → OnePoint EuclideanPlane}
    (hγ : EdgePar Γ γ) {q : ℂ} (hqnorm : ‖q‖ = 1 / 2)
    {p : OnePoint EuclideanPlane} (hpc : p = toSph q) (hpV : p ∈ Γ.V)
    {scale : ℝ} (hscale : 0 < scale)
    {Φ : C(ClosedUnitDisc, OnePoint EuclideanPlane)} (hp : IsPolar Γ p Φ)
    (hpos : GM06PositivePolar Φ)
    (d : halfEdges Γ γ p ≃ {w : Circle | ∃ e ∈ Γ.E, polarRimMap Φ w ∈ e})
    (hd : ∀ a, ∀ t : I, 0 < t → Φ (polarDiscPoint t (d a).val) ∈ range (spoke γ a.val))
    (minus plus a : halfEdges Γ γ p)
    (hmp : minus ≠ plus) (hma : minus ≠ a) (hpa : plus ≠ a)
    (hminus : ∀ t, spoke γ minus.val t = toSph (q * Complex.exp
      ((scale : ℂ) * (t : ℂ) * (Circle.exp (-(Real.pi / 2)) : ℂ))))
    (hplus : ∀ t, spoke γ plus.val t = toSph (q * Complex.exp
      ((scale : ℂ) * (t : ℂ) * (Circle.exp (Real.pi / 2) : ℂ))))
    {G : Drawing ClosedCylinder} (hG : G.IsProper) {e : Set ClosedCylinder}
    (he : e ∈ G.E) (ha : a.val.1 = cylinderToSphere '' e) :
    CircleCyclic (d minus).val (d a).val (d plus).val := by
  have hq : q ≠ 0 := by
    intro hh
    rw [hh, norm_zero] at hqnorm
    norm_num at hqnorm
  let l : ℝ := min (scale / 2) (1 / 2)
  have hl : 0 < l := lt_min (half_pos hscale) (by norm_num)
  have hl1 : l < 1 := (min_le_right _ _).trans_lt (by norm_num)
  have hls : l < scale := (min_le_left _ _).trans_lt (half_lt_self hscale)
  have hpO : p ∈ interior (range (expChart q l)) := by
    rw [hpc]
    exact toSph_mem_interior_range_expChart hq hl
  obtain ⟨Φ', d', hp', hpos', hsub, hval, hd'⟩ :=
    exists_small_labeled_positive_polar_chart hp hpos d hd isOpen_interior hpO
  have hmem : Φ' (polarDiscPoint 1 (d' a).val) ∈ cylinderToSphere '' e := by
    rw [← ha]
    exact polar_rim_mem_edge_of_halfedge_ray hγ hp' a (d' a).val (hd' a)
  obtain ⟨y, hy, hynorm⟩ := exists_complex_coordinate_of_proper_cylinder_edge hG he hmem
  have horder := source_signed_cuff_order_of_expChart hγ hq hpc hpV hl hl1 hls hp' hpos'
    (hsub.trans interior_subset) d' hd' minus plus a hmp hma hpa hminus hplus
    hy.symm (by rw [hqnorm]; exact hynorm)
  simpa only [hval] using horder

end GraphMinor.GM06
