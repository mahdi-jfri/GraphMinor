module

public import GraphMinor.GM06.Alg57CuffCapRegions
import GraphMinor.GM06.Alg511CuffEnumeration
import GraphMinor.GM06.Alg511CuffParam
import GraphMinor.GM06.Section5NextContact
import GraphMinor.GM06.Section5Red

/-!
# Edges on the cap side of a cuff

In the cuff-adjacency argument of VI (5.7), page 133, an augmented
edge contained in a closed cap must be a cuff gap. An ordinary open
edge cannot lie at an extreme radius, because properness excludes
boundary points from its interior. The opposite cuff has the wrong
radius. The exact cuff-edge enumeration then identifies the gap.
At a given cuff vertex, its two directed possibilities are exactly
the forward current gap and the reverse previous gap.
-/

public section
namespace GraphMinor.GM06
open Set Metric Topology GraphMinor.Surface GraphMinor.GM11 unitInterval

/-- An augmented edge confined to an extreme radius is a gap of
that cuff. The Boolean selects the outer cuff. -/
theorem cuff_edge_of_cap_side {k : ℕ} {G F : Drawing ClosedCylinder}
    (hG : IsCylinderSection5Drawing k G) (hGF : G.IsSubdrawing F)
    (hFU : F.U = G.U ∪ bd ClosedCylinder) (hFV : F.V = G.V)
    (outer : Bool) (e : (cylinderSphereDrawing F).E)
    (hside : ∀ p : ClosedCylinder, cylinderToSphere p ∈ e.val →
      if outer then 2 ≤ p.val.1 else p.val.1 ≤ 1) :
    ∃ j : Fin k, e.val = cylinderToSphere ''
      ((if outer then alg511OuterCuffGapCurve k j else initialCuffGapCurve k j) '' Ioo 0 1) := by
  obtain ⟨raw, hrawG, hrawI, hrawO⟩ := alg511_exists_cuff_edge_equiv hG hGF hFU hFV
  have he : e.val ∈ (image cylinderToSphere) '' F.E := by
    simpa only [cylinderSphereDrawing_E] using e.property
  obtain ⟨f, hf, hfe⟩ := he
  obtain ⟨a, ha⟩ := raw.surjective ⟨f, hf⟩
  cases a with
  | inl a =>
    have hfEq : f = a.val := (congrArg Subtype.val ha).symm.trans (hrawG a)
    obtain ⟨p, hp⟩ := a.property.1
    have hpe : cylinderToSphere p ∈ e.val := by
      rw [← hfe, hfEq]
      exact mem_image_of_mem _ hp
    have hs := hside p hpe
    have hpbd : p ∈ bd ClosedCylinder := by
      rw [bd_closedCylinder]
      cases outer
      · left
        change p.val.1 = 1
        simp only [Bool.false_eq_true, ↓reduceIte] at hs
        linarith [p.property.1.1]
      · right
        change p.val.1 = 2
        simp only [↓reduceIte] at hs
        linarith [p.property.1.2]
    have hpV : p ∈ G.V := hG.2.1 ⟨hpbd, (a.property.2.1 hp).1⟩
    exact False.elim ((a.property.2.1 hp).2 hpV)
  | inr a =>
    cases a with
    | inl j =>
      have hfEq : f = initialCuffGapCurve k j '' Ioo 0 1 :=
        (congrArg Subtype.val ha).symm.trans (hrawI j)
      cases outer
      · exact ⟨j, hfe.symm.trans (congrArg (image cylinderToSphere) hfEq)⟩
      · let t : I := ⟨1 / 2, by norm_num⟩
        have hpe : cylinderToSphere (initialCuffGapCurve k j t) ∈ e.val := by
          rw [← hfe, hfEq]
          exact mem_image_of_mem _ ⟨t, ⟨by change (0 : ℝ) < 1 / 2; norm_num, by change (1 / 2 : ℝ) < 1; norm_num⟩, rfl⟩
        have hs := hside _ hpe
        change 2 ≤ (1 : ℝ) at hs
        norm_num at hs
    | inr j =>
      have hfEq : f = alg511OuterCuffGapCurve k j '' Ioo 0 1 :=
        (congrArg Subtype.val ha).symm.trans (hrawO j)
      cases outer
      · let t : I := ⟨1 / 2, by norm_num⟩
        have hpe : cylinderToSphere (alg511OuterCuffGapCurve k j t) ∈ e.val := by
          rw [← hfe, hfEq]
          exact mem_image_of_mem _ ⟨t, ⟨by change (0 : ℝ) < 1 / 2; norm_num, by change (1 / 2 : ℝ) < 1; norm_num⟩, rfl⟩
        have hs := hside _ hpe
        norm_num [alg511OuterCuffGapCurve, alg511CuffSwap, initialCuffGapCurve, cylinderPoint] at hs
      · exact ⟨j, hfe.symm.trans (congrArg (image cylinderToSphere) hfEq)⟩

/-- An augmented edge in the closed inner cap is an inner cuff gap. -/
theorem cuff_edge_eq_inner_of_closed_cap {k : ℕ} {G F : Drawing ClosedCylinder}
    (hG : IsCylinderSection5Drawing k G) (hGF : G.IsSubdrawing F)
    (hFU : F.U = G.U ∪ bd ClosedCylinder) (hFV : F.V = G.V)
    (e : (cylinderSphereDrawing F).E)
    (he : e.val ⊆ toSph '' closedBall (0 : ℂ) (1 / 2)) :
    ∃ j : Fin k, e.val = cylinderToSphere '' (initialCuffGapCurve k j '' Ioo 0 1) := by
  apply cuff_edge_of_cap_side hG hGF hFU hFV false e
  intro p hp
  obtain ⟨z, hz, heq⟩ := he hp
  have hn := norm_eq_of_cylinderToSphere_eq heq.symm
  have hz' := mem_closedBall_zero_iff.mp hz
  change p.val.1 ≤ 1
  linarith

/-- An augmented edge in the closed exterior cap is an outer cuff gap. -/
theorem cuff_edge_eq_outer_of_closed_cap {k : ℕ} {G F : Drawing ClosedCylinder}
    (hG : IsCylinderSection5Drawing k G) (hGF : G.IsSubdrawing F)
    (hFU : F.U = G.U ∪ bd ClosedCylinder) (hFV : F.V = G.V)
    (e : (cylinderSphereDrawing F).E)
    (he : e.val ⊆ (toSph '' ball (0 : ℂ) 1)ᶜ) :
    ∃ j : Fin k, e.val = cylinderToSphere '' (alg511OuterCuffGapCurve k j '' Ioo 0 1) := by
  apply cuff_edge_of_cap_side hG hGF hFU hFV true e
  intro p hp
  change 2 ≤ p.val.1
  by_contra hlt
  have hnorm : ‖complexPlane.symm (cylToPlane p)‖ < 1 := by
    rw [LinearIsometryEquiv.norm_map, norm_cylToPlane]
    linarith
  apply he hp
  refine ⟨complexPlane.symm (cylToPlane p), mem_ball_zero_iff.mpr hnorm, ?_⟩
  change ((complexPlane (complexPlane.symm (cylToPlane p)) : EuclideanPlane) : OnePoint EuclideanPlane) = _
  rw [LinearIsometryEquiv.apply_symm_apply]
  rfl

/-- At an inner cuff vertex, a cap-side dart is one of its two
prescribed inner cuff ends. -/
theorem inner_cap_dart_at_source {k : ℕ} {G F : Drawing ClosedCylinder}
    (hG : IsCylinderSection5Drawing k G) (hGF : G.IsSubdrawing F)
    (hFU : F.U = G.U ∪ bd ClosedCylinder) (hFV : F.V = G.V)
    {γ : Set (OnePoint EuclideanPlane) → I → OnePoint EuclideanPlane}
    (hγI : ∀ j : Fin k, ∀ t, γ (cylinderToSphere '' (initialCuffGapCurve k j '' Ioo 0 1)) t =
      cylinderToSphere (initialCuffGapCurve k j t))
    (i : Fin k) (d : DrawingDart (cylinderSphereDrawing F))
    (hv : dartVertex γ d = cylinderToSphere (cylinderM1Point k i))
    (he : d.val.1 ⊆ toSph '' closedBall (0 : ℂ) (1 / 2)) :
    d.val = (cylinderToSphere '' (initialCuffGapCurve k i '' Ioo 0 1), false) ∨
      d.val = (cylinderToSphere '' (initialCuffGapCurve k (finPredCycle i) '' Ioo 0 1), true) := by
  obtain ⟨j, hj⟩ := cuff_edge_eq_inner_of_closed_cap hG hGF hFU hFV ⟨d.val.1, d.property⟩ he
  change d.val.1 = cylinderToSphere '' (initialCuffGapCurve k j '' Ioo 0 1) at hj
  cases hb : d.val.2
  · have hv' : cylinderM1Point k j = cylinderM1Point k i := by
      apply injective_cylinderToSphere
      simpa only [dartVertex, hb, endOf, Bool.false_eq_true, ↓reduceIte, hj, hγI,
        (initialCuffGapCurve_props hG j).1] using hv
    have hji := cylinderM1Point_injective hG.1 hv'
    left
    exact Prod.ext (by simpa only [hji] using hj) hb
  · have hv' : cylinderM1Point k (finSuccCycle j) = cylinderM1Point k i := by
      apply injective_cylinderToSphere
      simpa only [dartVertex, hb, endOf, Bool.false_eq_true, ↓reduceIte, hj, hγI,
        (initialCuffGapCurve_props hG j).2.1] using hv
    have hji := cylinderM1Point_injective hG.1 hv'
    have hpred : j = finPredCycle i := by rw [← hji, finPredCycle_finSuccCycle]
    right
    exact Prod.ext (by simpa only [hpred] using hj) hb

private theorem m2_injective {k : ℕ} (hk : 0 < k) : Function.Injective (cylinderM2Point k) := by
  intro i j hij
  apply cylinderM1Point_injective hk
  apply Subtype.ext
  have hh := congrArg (fun p : ClosedCylinder => p.val.2) hij
  simpa only [cylinderM1Point, cylinderM2Point, cylinderPoint] using
    congrArg (fun z => ((1 : ℝ), z)) hh

/-- At an outer cuff vertex, a cap-side dart is one of its two
prescribed outer cuff ends. -/
theorem outer_cap_dart_at_target {k : ℕ} {G F : Drawing ClosedCylinder}
    (hG : IsCylinderSection5Drawing k G) (hGF : G.IsSubdrawing F)
    (hFU : F.U = G.U ∪ bd ClosedCylinder) (hFV : F.V = G.V)
    {γ : Set (OnePoint EuclideanPlane) → I → OnePoint EuclideanPlane}
    (hγO : ∀ j : Fin k, ∀ t, γ (cylinderToSphere '' (alg511OuterCuffGapCurve k j '' Ioo 0 1)) t =
      cylinderToSphere (alg511OuterCuffGapCurve k j t))
    (i : Fin k) (d : DrawingDart (cylinderSphereDrawing F))
    (hv : dartVertex γ d = cylinderToSphere (cylinderM2Point k i))
    (he : d.val.1 ⊆ (toSph '' ball (0 : ℂ) 1)ᶜ) :
    d.val = (cylinderToSphere '' (alg511OuterCuffGapCurve k i '' Ioo 0 1), false) ∨
      d.val = (cylinderToSphere '' (alg511OuterCuffGapCurve k (finPredCycle i) '' Ioo 0 1), true) := by
  obtain ⟨j, hj⟩ := cuff_edge_eq_outer_of_closed_cap hG hGF hFU hFV ⟨d.val.1, d.property⟩ he
  change d.val.1 = cylinderToSphere '' (alg511OuterCuffGapCurve k j '' Ioo 0 1) at hj
  cases hb : d.val.2
  · have hv' : cylinderM2Point k j = cylinderM2Point k i := by
      apply injective_cylinderToSphere
      simpa only [dartVertex, hb, endOf, Bool.false_eq_true, ↓reduceIte, hj, hγO,
        (alg511_outer_gap_ends hG j).1] using hv
    have hji := m2_injective hG.1 hv'
    left
    exact Prod.ext (by simpa only [hji] using hj) hb
  · have hv' : cylinderM2Point k (finSuccCycle j) = cylinderM2Point k i := by
      apply injective_cylinderToSphere
      simpa only [dartVertex, hb, endOf, Bool.false_eq_true, ↓reduceIte, hj, hγO,
        (alg511_outer_gap_ends hG j).2] using hv
    have hji := m2_injective hG.1 hv'
    have hpred : j = finPredCycle i := by rw [← hji, finPredCycle_finSuccCycle]
    right
    exact Prod.ext (by simpa only [hpred] using hj) hb

end GraphMinor.GM06
