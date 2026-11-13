module

public import GraphMinor.GM06.Alg57CollapsedRayOrder
public import GraphMinor.GM06.Alg57SourceGermContacts
import Mathlib.Data.Finset.Lattice.Fold
import GraphMinor.GM06.Section5PolarDiscInterior

/-!
# Retained directed ends in the actual source chart

For Lemma 8 in the implementation of VI (5.7), page 133, the
pointwise quotient equation gives an entire short source ray on
each retained directed end. Reparametrize by the positive factor
sin(θ/2), and use the actual spoke equation of the contraction.
A finite minimum gives one radius that works for all retained ends.
Their contacts with any smaller positive polar rim therefore have
exactly the half-angle cyclic order, including both ends of loops.
-/

public section
namespace GraphMinor.GM06
open Set Metric Topology GraphMinor.Surface GraphMinor.GM11 unitInterval

/-- The contraction's pointwise spoke equation and target chart
put a short half-angle ray on the actual retained source end. -/
theorem retained_source_short_ray
    {π : C(OnePoint EuclideanPlane, OnePoint EuclideanPlane)}
    {Φ Ψ : C(ClosedUnitDisc, OnePoint EuclideanPlane)} (w : Circle)
    (hmap : ∀ x, Ψ (section5CollapsedRadiusDiscPoint x) =
      π (Φ (section5RotateDisc w x)))
    {g g' : I → OnePoint EuclideanPlane} (hg : ∀ t, g' t = π (g t))
    (θ : ℝ) (hθ0 : 0 < θ) (hθP : θ < 2 * Real.pi)
    (hray : ∀ t : I, 0 < t →
      Φ (polarDiscPoint t (w * Circle.exp θ)) ∈ g '' Ioo (0 : I) 1)
    (r : I) (hr0 : 0 < (r : ℝ)) (hr : (r : ℝ) ≤ Real.sin (θ / 2)) :
    Ψ (polarDiscPoint r (Circle.exp (θ / 2))) ∈ g' '' Ioo (0 : I) 1 := by
  have hs := (section5RadiusCollapse_half_angle_bounds hθ0 hθP).2.2
  let t : I := ⟨(r : ℝ) / Real.sin (θ / 2),
    (div_pos hr0 hs).le, (div_le_one hs).mpr hr⟩
  have ht : 0 < t := div_pos hr0 hs
  have hpoint : section5CollapsedRadiusDiscPoint (polarDiscPoint t (Circle.exp θ)) =
      polarDiscPoint r (Circle.exp (θ / 2)) := by
    rw [section5CollapsedRadiusDiscPoint_ray t θ hθ0 hθP]
    congr 1
    apply Subtype.ext
    exact div_mul_cancel₀ _ hs.ne'
  have hactual : Ψ (polarDiscPoint r (Circle.exp (θ / 2))) =
      π (Φ (polarDiscPoint t (w * Circle.exp θ))) := by
    rw [← hpoint, hmap, section5RotateDisc_polarDiscPoint]
  obtain ⟨u, hu, hueq⟩ := hray t ht
  exact ⟨u, hu, (hg u).trans ((congrArg π hueq).trans hactual.symm)⟩

/-- Finitely many retained angles have a common positive source
radius, with their actual short-spoke parametrizations retained. -/
theorem exists_uniform_retained_source_radius
    {J : Type*} [Fintype J]
    {π : C(OnePoint EuclideanPlane, OnePoint EuclideanPlane)}
    {Φ Ψ : C(ClosedUnitDisc, OnePoint EuclideanPlane)} (w : Circle)
    (hmap : ∀ x, Ψ (section5CollapsedRadiusDiscPoint x) =
      π (Φ (section5RotateDisc w x)))
    (g g' : J → I → OnePoint EuclideanPlane) (hg : ∀ j t, g' j t = π (g j t))
    (θ : J → ℝ) (hθ0 : ∀ j, 0 < θ j) (hθP : ∀ j, θ j < 2 * Real.pi)
    (hray : ∀ j, ∀ t : I, 0 < t →
      Φ (polarDiscPoint t (w * Circle.exp (θ j))) ∈ g j '' Ioo (0 : I) 1) :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ 1 ∧ ∀ j, ∀ r : I,
      0 < (r : ℝ) → (r : ℝ) ≤ δ →
      Ψ (polarDiscPoint r (Circle.exp (θ j / 2))) ∈ g' j '' Ioo (0 : I) 1 := by
  classical
  let δ : ℝ := Finset.univ.inf' (by simp : (Finset.univ : Finset (Option J)).Nonempty)
    (fun j => match j with | none => 1 | some j => Real.sin (θ j / 2))
  have hδ : 0 < δ := by
    apply (Finset.lt_inf'_iff _).2
    intro j _
    cases j with
    | none => exact zero_lt_one
    | some j => exact (section5RadiusCollapse_half_angle_bounds (hθ0 j) (hθP j)).2.2
  have hδ1 : δ ≤ 1 := Finset.inf'_le _ (Finset.mem_univ (none : Option J))
  refine ⟨δ, hδ, hδ1, ?_⟩
  intro j r hr0 hr
  have hδj : δ ≤ Real.sin (θ j / 2) :=
    Finset.inf'_le _ (Finset.mem_univ (some j))
  exact retained_source_short_ray w hmap (hg j) (θ j) (hθ0 j) (hθP j)
    (hray j) r hr0 (hr.trans hδj)

/-- Three retained source ends have exactly the cyclic order of
their explicit coordinate directions. Unique contacts follow from
their actual short-spoke images, not from a supplied order. -/
theorem retained_source_direction_cyclic_iff
    {Γ : Drawing (OnePoint EuclideanPlane)}
    {γ : Set (OnePoint EuclideanPlane) → I → OnePoint EuclideanPlane}
    (hγ : EdgePar Γ γ) {p : OnePoint EuclideanPlane} (hpV : p ∈ Γ.V)
    {Ψ Φ : C(ClosedUnitDisc, OnePoint EuclideanPlane)} (hp : IsPolar Γ p Φ)
    (d : halfEdges Γ γ p ≃ {w : Circle | ∃ e ∈ Γ.E, polarRimMap Φ w ∈ e})
    (hd : ∀ a, ∀ t : I, 0 < t → Φ (polarDiscPoint t (d a).val) ∈ range (spoke γ a.1))
    (f : C(Circle, ℂ)) (v : C(Circle, Circle))
    (hf : ∀ w, ‖f w‖ ≤ 1) (hf0 : ∀ w, f w ≠ 0)
    (hmap : ∀ w, Ψ (discPt (f w)) = Φ (polarDiscPoint 1 w))
    (hv : ∀ w, f w = (‖f w‖ : ℂ) * v w)
    (hvpos : 0 < wind (fun w => (v w : ℂ)) 0)
    {δ : ℝ} (hδ : ∀ w, ‖f w‖ ≤ δ)
    (a b c : halfEdges Γ γ p) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (u : halfEdges Γ γ p → Circle)
    (hray : ∀ j ∈ ({a, b, c} : Set (halfEdges Γ γ p)), ∀ r : I,
      0 < (r : ℝ) → (r : ℝ) ≤ δ →
      Ψ (polarDiscPoint r (u j)) ∈ spoke γ j.1 '' Ioo (0 : I) 1) :
    CircleCyclic (d a).val (d b).val (d c).val ↔ CircleCyclic (u a) (u b) (u c) := by
  have hcontact (j : halfEdges Γ γ p) (hj : j ∈ ({a, b, c} : Set _)) :=
    source_coordinate_ray_contact hγ hpV hp d hd f v hf hf0 hmap hv hvpos hδ j (u j) (hray j hj)
  have ha := hcontact a (by simp)
  have hb := hcontact b (by simp)
  have hc := hcontact c (by simp)
  have hinj : Function.Injective (fun j => (d j).val) := Subtype.val_injective.comp d.injective
  have hiff := circleCyclic_iff_positive_loop_contacts v hvpos
    (fun w hw => (ha.2 w).mp (hw.trans ha.1))
    (fun w hw => (hb.2 w).mp (hw.trans hb.1))
    (fun w hw => (hc.2 w).mp (hw.trans hc.1))
    (hinj.ne hab) (hinj.ne hac) (hinj.ne hbc)
  simpa only [ha.1, hb.1, hc.1] using hiff


/-- Excluding a directed end's midpoint from an old target chart
turns its positive ray containment into strict short-spoke
containment, as required by the unique-contact argument. -/
theorem polar_ray_mem_short_spoke_of_midpoint_exclusion
    {Γ : Drawing (OnePoint EuclideanPlane)}
    {γ : Set (OnePoint EuclideanPlane) → I → OnePoint EuclideanPlane}
    {p : OnePoint EuclideanPlane} {Φ : C(ClosedUnitDisc, OnePoint EuclideanPlane)}
    (hp : IsPolar Γ p Φ) (a : halfEdges Γ γ p) (u : Circle)
    (hray : ∀ t : I, 0 < t → Φ (polarDiscPoint t u) ∈ range (spoke γ a.val))
    (hmid : spoke γ a.val 1 ∉ range Φ) :
    ∀ t : I, 0 < t → Φ (polarDiscPoint t u) ∈ spoke γ a.val '' Ioo (0 : I) 1 := by
  intro t ht
  obtain ⟨r, hr⟩ := hray t ht
  have hr0 : 0 < r := unitInterval.pos_iff_ne_zero.mpr (by
    intro heq
    subst r
    have hpoint : Φ (polarDiscPoint t u) = Φ polarCentre := by
      rw [← hr, spoke_zero, a.property.2, hp.centre]
    have hh := congrArg (fun x : ClosedUnitDisc => ‖x.val‖) (hp.inj hpoint)
    rw [norm_polarDiscPoint] at hh
    have hz : ‖(polarCentre : ClosedUnitDisc).val‖ = 0 := by simp [polarCentre]
    rw [hz] at hh
    exact (show (0 : ℝ) < (t : ℝ) from ht).ne' hh)
  have hr1 : r < 1 := lt_of_le_of_ne r.property.2 (by
    intro heq
    subst r
    exact hmid ⟨polarDiscPoint t u, hr.symm⟩)
  exact ⟨r, ⟨hr0, hr1⟩, hr⟩

/-- There is an open neighbourhood of a drawing vertex excluding
every edge midpoint and any given closed set missing the vertex.
The edge midpoints form a finite set, even in the presence of loops. -/
theorem exists_vertex_neighbourhood_avoiding_midpoints
    {Γ : Drawing (OnePoint EuclideanPlane)}
    {γ : Set (OnePoint EuclideanPlane) → I → OnePoint EuclideanPlane}
    (hγ : EdgePar Γ γ) {p : OnePoint EuclideanPlane} (hp : p ∈ Γ.V)
    {C : Set (OnePoint EuclideanPlane)} (hC : IsClosed C) (hpC : p ∉ C) :
    ∃ O : Set (OnePoint EuclideanPlane), IsOpen O ∧ p ∈ O ∧ Disjoint O C ∧
      ∀ a : halfEdges Γ γ p, spoke γ a.val 1 ∉ O := by
  let B := (fun e => γ e (halfPar false 1)) '' Γ.E
  have hB : B.Finite := Γ.finite_edges.image _
  have hpB : p ∉ B := by
    rintro ⟨e, he, hep⟩
    change γ e (halfPar false 1) = p at hep
    have ht : halfPar false 1 ∈ Ioo (0 : I) 1 := halfPar_mem_Ioo false zero_lt_one
    exact edge_notMem_V he ((hγ.image e he).subset (mem_image_of_mem (γ e) ht))
      (hep.symm ▸ hp)
  refine ⟨Cᶜ ∩ Bᶜ, hC.isOpen_compl.inter hB.isClosed.isOpen_compl,
    ⟨hpC, hpB⟩, ?_, ?_⟩
  · exact disjoint_left.mpr (fun _ hx hy => hx.1 hy)
  · intro a ha
    apply ha.2
    refine ⟨a.val.1, a.property.1, ?_⟩
    change γ a.val.1 (halfPar false 1) = γ a.val.1 (halfPar a.val.2 1)
    apply congrArg (γ a.val.1)
    apply Subtype.ext
    simp only [halfPar_coe, Bool.false_eq_true, ite_false, Icc.coe_one]
    cases a.val.2 <;> norm_num

end GraphMinor.GM06
