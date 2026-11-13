module

public import GraphMinor.GM06.Alg57EdgeChain
public import GraphMinor.GM06.Alg57FaceRegions
public import GraphMinor.GM06.Section5PolarDiscInterior
public import GraphMinor.GM11.Walks

/-!
# The counterclockwise rotation at a vertex

This file states what it means that a rotation `R` on the darts of a drawing in the sphere is
the actual counterclockwise order at a vertex `v` (`IsCcwStar`), in the form of the rotation
rows of the input of VI (5.7) (`GM06SuccessorRotationRowRep`): there is a positive polar chart at
`v` and a direction `z a` for each dart `a` at `v`, such that the ray of `z a` runs along the
edge of `a`, the rays of the darts are all the rays in `U(Γ)`, and `R` sends each dart to the
next one counterclockwise.

From this we read off the corners at `v`: the next direction after `z a` is `z (R.rot a)`
(`IsCcwStar.next_eq`), and the edge of each dart runs out along its ray
(`IsCcwStar.runsOut`).
-/

@[expose] public section

namespace GraphMinor.GM06

open Set Metric Topology GraphMinor.Surface GraphMinor.GM11 unitInterval Equiv

/-! ### The curves of the darts -/

section Curves

variable {S : Type*} [TopologicalSpace S]

/-- The parametrization `γ e` of an edge, extended to the reals. -/
noncomputable def edgeCurve (γ : Set S → I → S) (e : Set S) (t : ℝ) : S :=
  γ e (projIcc 0 1 zero_le_one t)

/-- The curve along the edge of a dart, starting at the vertex of the dart. -/
noncomputable def dartCurve {Γ : Drawing S} (γ : Set S → I → S) (a : DrawingDart Γ) (t : ℝ) : S :=
  edgeCurve γ a.1.1 (if a.1.2 then 1 - t else t)

theorem edgeCurve_of_mem (γ : Set S → I → S) (e : Set S) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    edgeCurve γ e t = γ e ⟨t, ht⟩ := by
  simp only [edgeCurve, projIcc_of_mem _ ht]

theorem dartCurve_zero {Γ : Drawing S} (γ : Set S → I → S) (a : DrawingDart Γ) :
    dartCurve γ a 0 = dartVertex γ a := by
  rcases a with ⟨⟨e, b⟩, he⟩
  cases b
  · simp only [dartCurve, Bool.false_eq_true, ↓reduceIte]
    rw [edgeCurve_of_mem γ e ⟨le_rfl, zero_le_one⟩]
    rfl
  · simp only [dartCurve, ↓reduceIte, sub_zero]
    rw [edgeCurve_of_mem γ e ⟨zero_le_one, le_rfl⟩]
    rfl

theorem dartCurve_flip {Γ : Drawing S} (γ : Set S → I → S) (a : DrawingDart Γ) (t : ℝ) :
    dartCurve γ (dartFlip Γ a) t = dartCurve γ a (1 - t) := by
  rcases a with ⟨⟨e, b⟩, he⟩
  cases b <;> simp [dartCurve]

/-- The spoke of a dart is the start of its curve, at half speed. -/
theorem spoke_eq_dartCurve {Γ : Drawing S} (γ : Set S → I → S) (a : DrawingDart Γ) (s : I) :
    spoke γ a.1 s = dartCurve γ a (s / 2) := by
  rcases a with ⟨⟨e, b⟩, he⟩
  have hs := s.2
  cases b
  · simp only [dartCurve, Bool.false_eq_true, ↓reduceIte, spoke]
    rw [edgeCurve_of_mem γ e ⟨by linarith [hs.1], by linarith [hs.2]⟩]
    congr 1
  · simp only [dartCurve, ↓reduceIte, spoke]
    rw [edgeCurve_of_mem γ e ⟨by linarith [hs.2], by linarith [hs.1]⟩]
    congr 1

end Curves

section Sphere

variable {Γ : Drawing (OnePoint EuclideanPlane)}
  {γ : Set (OnePoint EuclideanPlane) → I → OnePoint EuclideanPlane}

theorem isEdgeCurve_edgeCurve (hγ : EdgePar Γ γ) {e : Set (OnePoint EuclideanPlane)}
    (he : e ∈ Γ.E) : IsEdgeCurve Γ e (edgeCurve γ e) where
  cont := (hγ.cont e he).comp continuous_projIcc
  inj := by
    intro s hs t ht hst
    rw [edgeCurve_of_mem γ e ⟨hs.1.le, hs.2.le⟩, edgeCurve_of_mem γ e ⟨ht.1.le, ht.2.le⟩] at hst
    have := hγ.inj e he (show (⟨s, hs.1.le, hs.2.le⟩ : I) ∈ Ioo 0 1 from ⟨hs.1, hs.2⟩)
      (show (⟨t, ht.1.le, ht.2.le⟩ : I) ∈ Ioo 0 1 from ⟨ht.1, ht.2⟩) hst
    exact congrArg Subtype.val this
  image := by
    calc edgeCurve γ e '' Ioo 0 1 = γ e '' Ioo (0 : I) 1 := by
          ext y
          constructor
          · rintro ⟨s, hs, rfl⟩
            exact ⟨⟨s, hs.1.le, hs.2.le⟩, ⟨hs.1, hs.2⟩, (edgeCurve_of_mem γ e _).symm⟩
          · rintro ⟨s, hs, rfl⟩
            exact ⟨s.1, ⟨hs.1, hs.2⟩, edgeCurve_of_mem γ e s.2⟩
      _ = e := hγ.image e he
  zero := by
    rw [edgeCurve_of_mem γ e ⟨le_rfl, zero_le_one⟩]
    exact hγ.zero e he
  one := by
    rw [edgeCurve_of_mem γ e ⟨zero_le_one, le_rfl⟩]
    exact hγ.one e he

theorem isEdgeCurve_dartCurve (hγ : EdgePar Γ γ) (a : DrawingDart Γ) :
    IsEdgeCurve Γ a.1.1 (dartCurve γ a) := by
  rcases a with ⟨⟨e, b⟩, he⟩
  cases b
  · convert isEdgeCurve_edgeCurve hγ he using 1
    funext t; simp [dartCurve]
  · convert (isEdgeCurve_edgeCurve hγ he).rev using 1
    funext t; simp [dartCurve]

/-- A point of the curve of a dart, early on, lies in the spoke of no other dart. -/
theorem eq_of_dartCurve_mem_spoke (hγ : EdgePar Γ γ) {a b : DrawingDart Γ} {t : ℝ}
    (ht : t ∈ Ioo (0 : ℝ) (1 / 2)) (hb : dartCurve γ a t ∈ range (spoke γ b.1)) : a = b := by
  obtain ⟨s, hs⟩ := hb
  have hA := isEdgeCurve_dartCurve hγ a
  have hB := isEdgeCurve_dartCurve hγ b
  have htI : t ∈ Ioo (0 : ℝ) 1 := ⟨ht.1, by linarith [ht.2]⟩
  have hae : dartCurve γ a t ∈ a.1.1 := hA.mem_edge htI
  rw [spoke_eq_dartCurve] at hs
  have hs0 : (0 : ℝ) < s := by
    rcases eq_or_lt_of_le s.2.1 with h | h
    · exfalso
      rw [← h, zero_div, dartCurve_zero] at hs
      exact edge_notMem_V a.2 hae (hs ▸ dartVertex_mem hγ b)
    · exact h
  have hsI : (s : ℝ) / 2 ∈ Ioo (0 : ℝ) 1 := ⟨by positivity, by linarith [s.2.2]⟩
  have hbe : dartCurve γ b (s / 2) ∈ b.1.1 := hB.mem_edge hsI
  have hee : a.1.1 = b.1.1 := Γ.edge_eq_of_mem a.2 b.2 hae (hs ▸ hbe)
  rcases a with ⟨⟨e, ba⟩, hea⟩
  rcases b with ⟨⟨f, bb⟩, hfb⟩
  simp only at hee
  subst hee
  have hE := isEdgeCurve_edgeCurve hγ hea
  have hs2 : (s : ℝ) / 2 ≤ 1 / 2 := by linarith [s.2.2]
  cases ba <;> cases bb <;> simp only [dartCurve, Bool.false_eq_true, ↓reduceIte] at hs
  · rfl
  · exfalso
    have := hE.inj htI ⟨by linarith, by linarith⟩ hs.symm
    linarith [ht.2]
  · exfalso
    have := hE.inj ⟨by linarith [ht.2], by linarith [ht.1]⟩ ⟨by positivity, by linarith⟩ hs.symm
    linarith [ht.2]
  · rfl

/-- `R` is the counterclockwise rotation at `v`, read in a positive polar chart `Φ` with a
direction `z a` for each dart `a` at `v`. This is the meaning of a rotation row in the input of
VI (5.7) (`GM06SuccessorRotationRowRep`). -/
structure IsCcwStar (Γ : Drawing (OnePoint EuclideanPlane))
    (γ : Set (OnePoint EuclideanPlane) → I → OnePoint EuclideanPlane)
    (R : DartRotation (DrawingDart Γ)) (v : OnePoint EuclideanPlane)
    (Φ : C(ClosedUnitDisc, OnePoint EuclideanPlane)) (z : DrawingDart Γ → Circle) : Prop where
  polar : IsPolar Γ v Φ
  pos : GM06PositivePolar Φ
  inj : ∀ a b, dartVertex γ a = v → dartVertex γ b = v → z a = z b → a = b
  spoke : ∀ a, dartVertex γ a = v → ∀ t : I, 0 < t →
    Φ (polarDiscPoint t (z a)) ∈ range (spoke γ a.1)
  dirs : ∀ w : Circle, ∀ e ∈ Γ.E, polarRimMap Φ w ∈ e → ∃ a, dartVertex γ a = v ∧ z a = w
  succ : ∀ a b, dartVertex γ a = v → dartVertex γ b = v →
    ¬ CircleCyclic (z a) (z b) (z (R.rot a))

namespace IsCcwStar

variable {R : DartRotation (DrawingDart Γ)} {v : OnePoint EuclideanPlane}
  {Φ : C(ClosedUnitDisc, OnePoint EuclideanPlane)} {z : DrawingDart Γ → Circle}

/-- A ray of a polar chart misses the vertices. -/
theorem rim_notMem_V (hp : IsPolar Γ v Φ) (w : Circle) : polarRimMap Φ w ∉ Γ.V := by
  intro hV
  have hn : IsGammaNice Γ {polarRimMap Φ w} :=
    ⟨{{polarRimMap Φ w}}, singleton_subset_iff.mpr (Or.inl (Or.inl ⟨_, hV, rfl⟩)), by simp⟩
  have := (polar_ray_mem_iff hp hn w (t := ⟨1 / 2, by norm_num, by norm_num⟩)
    (by change (0 : ℝ) < 1 / 2; norm_num)).mpr rfl
  have h2 := polarDiscPoint_direction_eq (r := ⟨1 / 2, by norm_num, by norm_num⟩) (s := 1)
    (by change (0 : ℝ) < 1 / 2; norm_num) (hp.inj this)
  have h3 := congrArg (fun x : ClosedUnitDisc => ‖x.1‖) (hp.inj this)
  simp only [norm_polarDiscPoint] at h3
  norm_num at h3

theorem rimDirs_eq (h : IsCcwStar Γ γ R v Φ z) (hγ : EdgePar Γ γ) :
    rimDirs Γ Φ = z '' {a | dartVertex γ a = v} := by
  ext w
  constructor
  · intro hw
    have hU : polarRimMap Φ w ∈ Γ.U := hw
    obtain ⟨e, he, hwe⟩ := Γ.exists_edge_of_mem hU (rim_notMem_V h.polar w)
    obtain ⟨a, ha, rfl⟩ := h.dirs w e he hwe
    exact ⟨a, ha, rfl⟩
  · rintro ⟨a, ha, rfl⟩
    obtain ⟨s, hs⟩ := h.spoke a ha 1 one_pos
    show polarRimMap Φ (z a) ∈ Γ.U
    change Φ (polarDiscPoint 1 (z a)) ∈ Γ.U
    rw [← hs]
    rcases eq_or_lt_of_le s.2.1 with h0 | h0
    · exfalso
      have hs0 : s = 0 := Subtype.ext h0.symm
      rw [hs0, spoke_zero] at hs
      have : Φ (polarDiscPoint 1 (z a)) = Φ polarCentre := by
        rw [← hs, h.polar.centre]; exact ha
      exact polarDiscPoint_one_ne_centre _ (h.polar.inj this)
    · exact (a.2.2.1 (spoke_mem_edge hγ a.2 h0)).1

theorem rimDirs_finite (h : IsCcwStar Γ γ R v Φ z) (hγ : EdgePar Γ γ) :
    (rimDirs Γ Φ).Finite := by
  rw [h.rimDirs_eq hγ]
  exact (Set.toFinite _).image _

theorem mem_rimDirs (h : IsCcwStar Γ γ R v Φ z) (hγ : EdgePar Γ γ) {a : DrawingDart Γ}
    (ha : dartVertex γ a = v) : z a ∈ rimDirs Γ Φ := by
  rw [h.rimDirs_eq hγ]; exact ⟨a, ha, rfl⟩

/-- **The next direction after a dart is the direction of the next dart.** -/
theorem next_eq (h : IsCcwStar Γ γ R v Φ z) (hγ : EdgePar Γ γ) (hR : IsDrawingRotation Γ γ R)
    {a : DrawingDart Γ} (ha : dartVertex γ a = v) :
    z a * Circle.exp (gap (rimDirs Γ Φ) (z a)) = z (R.rot a) := by
  have hD := h.rimDirs_finite hγ
  have hra : dartVertex γ (R.rot a) = v := (hR.vertex_rot a).trans ha
  obtain ⟨b, hb, hbz⟩ : z a * Circle.exp (gap (rimDirs Γ Φ) (z a)) ∈ z '' {a | dartVertex γ a = v} :=
    h.rimDirs_eq hγ ▸ mul_exp_gap_mem hD (h.mem_rimDirs hγ ha)
  rw [← hbz]
  congr 1
  by_contra hne
  have hg := gap_pos hD (z a)
  have hgle := gap_le_two_pi hD (z a)
  by_cases hrot : R.rot a = a
  · -- a single dart at `v`
    obtain ⟨n, hn⟩ := hR.reach a b (ha.trans hb.symm)
    have : (R.rot ^ n) a = a := Perm.zpow_apply_eq_self_of_apply_eq_self hrot n
    exact hne (by rw [← hn, this, hrot])
  · have hθb : angleTo (z a) (z b) = gap (rimDirs Γ Φ) (z a) :=
      angleTo_eq ⟨hg, hgle⟩ hbz
    have hθr : gap (rimDirs Γ Φ) (z a) ≤ angleTo (z a) (z (R.rot a)) :=
      gap_le_angleTo hD _ (h.mem_rimDirs hγ hra)
    have hθr' : angleTo (z a) (z (R.rot a)) < 2 * Real.pi := by
      refine lt_of_le_of_ne (angleTo_le _ _) fun h2 => hrot ?_
      apply h.inj _ _ hra ha
      rw [← mul_exp_angleTo (z a) (z (R.rot a)), h2, Circle.exp_two_pi, mul_one]
    have hlt : gap (rimDirs Γ Φ) (z a) < angleTo (z a) (z (R.rot a)) := by
      refine lt_of_le_of_ne hθr fun h2 => hne ?_
      apply h.inj _ _ hb hra
      rw [hbz, h2, mul_exp_angleTo]
    apply h.succ a b ha hb
    exact ⟨_, _, hg, hlt, hθr', hbz, (mul_exp_angleTo _ _).symm⟩

/-- The direction before a dart is the direction of the dart before it. -/
theorem prev_eq (h : IsCcwStar Γ γ R v Φ z) (hγ : EdgePar Γ γ) (hR : IsDrawingRotation Γ γ R)
    {a : DrawingDart Γ} (ha : dartVertex γ a = v) :
    z (R.rot.symm a) * Circle.exp (gap (rimDirs Γ Φ) (z (R.rot.symm a))) = z a := by
  have : dartVertex γ (R.rot.symm a) = v := by
    rw [← ha, ← hR.vertex_rot (R.rot.symm a), Equiv.apply_symm_apply]
  rw [h.next_eq hγ hR this, Equiv.apply_symm_apply]

/-- **The edge of a dart runs out along its ray.** -/
theorem runsOut (h : IsCcwStar Γ γ R v Φ z) (hγ : EdgePar Γ γ)
    {Ψ : C(ClosedUnitDisc, EuclideanPlane)} (hΨ : ∀ x, Φ x = (Ψ x : OnePoint EuclideanPlane))
    {a : DrawingDart Γ} (ha : dartVertex γ a = v) :
    ∃ δ, RunsOut Ψ (z a) (dartCurve γ a) 0 δ := by
  have hG := isEdgeCurve_dartCurve hγ a
  have hp : IsPolar Γ (dartCurve γ a 0) Φ := by rw [dartCurve_zero, ha]; exact h.polar
  obtain ⟨δ₀, hδ₀, hδ₀G⟩ : ∃ δ₀, 0 < δ₀ ∧ δ₀ < 1 / 2 ∧
      ∀ t ∈ Icc (0 : ℝ) δ₀, dartCurve γ a t ∈ range Φ := by
    have hpre := (isOpen_interior.preimage hG.cont).mem_nhds
      (show (0 : ℝ) ∈ dartCurve γ a ⁻¹' interior (range Φ) from hp.nhd)
    obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp hpre
    refine ⟨min (ε / 2) (1 / 4), lt_min (half_pos hε) (by norm_num),
      (min_le_right _ _).trans_lt (by norm_num), fun t ht => interior_subset (hball ?_)⟩
    rw [mem_ball, Real.dist_eq, sub_zero, abs_lt]
    constructor <;> linarith [ht.1, ht.2, min_le_left (ε / 2) (1 / 4)]
  obtain ⟨hδ₀h, hδ₀G⟩ := hδ₀G
  refine ⟨_, runsOut_of_on_ray hΨ hG.cont hδ₀ hp (hG.injOn_Icc_zero a.2 (by linarith)) ?_⟩
  intro t ht
  have htI : t ∈ Ioo (0 : ℝ) 1 := ⟨ht.1, by linarith [ht.2]⟩
  have hne : dartCurve γ a t ≠ dartCurve γ a 0 := by
    intro he
    rw [dartCurve_zero] at he
    exact edge_notMem_V a.2 (hG.mem_edge htI) (he ▸ dartVertex_mem hγ a)
  obtain ⟨r, w, hr, hr1, hGt⟩ := chart_point_polar hp hΨ (hδ₀G t ⟨ht.1.le, by linarith [ht.2]⟩)
    hne
  refine ⟨r, hr, hr1, ?_⟩
  have hwD : w ∈ rimDirs Γ Φ := by
    show polarRimMap Φ w ∈ Γ.U
    rw [← chart_ray_mem_iff h.polar hΨ (isGammaNice_U Γ) w hr hr1, ← hGt]
    exact (a.2.2.1 (hG.mem_edge htI)).1
  rw [h.rimDirs_eq hγ] at hwD
  obtain ⟨b, hb, rfl⟩ := hwD
  have hspoke := h.spoke b hb ⟨r, hr.le, hr1⟩ hr
  rw [← discPt_mul, ← toSph_chartC hΨ] at hspoke
  simp only at hspoke
  rw [← hGt] at hspoke
  have hab := eq_of_dartCurve_mem_spoke hγ ⟨ht.1, by linarith [ht.2]⟩ hspoke
  have hzz : z b = z a := by rw [hab]
  rw [← hzz]
  exact hGt

end IsCcwStar

end Sphere

end GraphMinor.GM06
