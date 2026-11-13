module

public import GraphMinor.GM06.Alg57OnePathEnd
public import GraphMinor.GM06.Alg57RegionIncidence
public import GraphMinor.GM06.Alg57OnePathConnected

/-!
# The lifted incidence for `k = 1` read from one face orbit

The lifted incidence of `Alg57OnePathDarts` and `Alg57OnePathEnd` speaks of the corner `ρ d` after a
dart `d` of `G⁺`. Here we replace "the corner after `d` is `R₁`" by "`d` is in the face orbit of
the reverse inner gap dart `c̄₁`" (`cornerLabel_eq_region_iff_faceOf`). The two agree because the
face orbits are the regions (Lemma 3, `IsCornerLabel.sphere_faceOrbits`) and the orbit of `c̄₁` is
`R₁` (`face_reverse_inner_gap`). This holds for every `k`.

For `k = 1` with no reduction the rotation of `G⁺` is connected
(`isPreconnected_cylinderSphereDrawing_U_of_no_reduction'`), so the lifted incidence takes the face
form: `lifted_face_vertex` (inner vertices of `P₁`), `lifted_face_edge` (inner points of edges of
`P₁`) and `lifted_face_end` (the end of `P₁`). At the start both lifts are always incident
(`coverLift_zero_mem_closure`). These statements have no side sets and no corner label.
-/

@[expose] public section

namespace GraphMinor.GM06

open Set Topology GraphMinor.Surface GraphMinor.GM11 unitInterval

section FaceForm

variable {k : ℕ} {G F : Drawing ClosedCylinder}
  {γ : Set (OnePoint EuclideanPlane) → I → OnePoint EuclideanPlane}
  {R : DartRotation (DrawingDart (cylinderSphereDrawing F))}

/-- **The corner after `d` is `Rᵢ` exactly when `d` is in the face orbit of `c̄ᵢ`.** Here `ρ` is a
corner label read from counterclockwise stars, as `exists_cornerLabel` gives. -/
theorem cornerLabel_eq_region_iff_faceOf (hG : IsCylinderSection5Drawing k G)
    (hFU : F.U = G.U ∪ bd ClosedCylinder) (hγ : EdgePar (cylinderSphereDrawing F) γ)
    (hR : IsDrawingRotation (cylinderSphereDrawing F) γ R)
    (hccw : IsCcwRotation (cylinderSphereDrawing F) γ R) (hc : R.Connected)
    (hV : ∀ v ∈ (cylinderSphereDrawing F).V, ∃ d : DrawingDart (cylinderSphereDrawing F),
      dartVertex γ d = v)
    (i : Fin k)
    (he : cylinderToSphere '' (initialCuffGapCurve k i '' Ioo 0 1) ∈ (cylinderSphereDrawing F).E)
    (hγe : ∀ t, γ (cylinderToSphere '' (initialCuffGapCurve k i '' Ioo 0 1)) t =
      cylinderToSphere (initialCuffGapCurve k i t))
    {ρ : DrawingDart (cylinderSphereDrawing F) → Set (OnePoint EuclideanPlane)}
    (hform : ∀ d, ∃ (Φ : C(ClosedUnitDisc, OnePoint EuclideanPlane))
      (z : DrawingDart (cylinderSphereDrawing F) → Circle),
      IsCcwStar (cylinderSphereDrawing F) γ R (dartVertex γ d) Φ z ∧
        ρ d = cornerRegion (cylinderSphereDrawing F) Φ (z d))
    (d : DrawingDart (cylinderSphereDrawing F)) :
    ρ d = cylinderToSphere '' (cylinderRegion k G i \ bd ClosedCylinder) ↔
      R.faceOf d = R.faceOf (reverseInnerGapDart k i F he) := by
  have hS : IsClosedSurface (OnePoint EuclideanPlane) :=
    (GM11.IsSphere.isClosedSurface (S := OnePoint EuclideanPlane) ⟨Homeomorph.refl _⟩).1
  have hinf := infty_notMem_cylinderSphereDrawing_U F
  obtain ⟨ρ', hρ', hform'⟩ := exists_cornerLabel hinf hγ hR hccw
  -- the two corner labels agree, since both are read from counterclockwise stars
  have heq : ∀ d, ρ d = ρ' d := by
    intro d
    obtain ⟨Φ, z, hst, h⟩ := hform' d
    rw [h]
    exact cornerLabel_eq_star hinf hγ hform d hst
  have hbij := (hρ'.sphere_faceOrbits hinf hγ hR hc hV ⟨_, he⟩).1
  -- the label of a face is the corner after any dart of it, read in an edge chart
  have hL : ∀ (d : DrawingDart (cylinderSphereDrawing F)) (a : ℝ), a ∈ Ioo (0 : ℝ) 1 →
      ∀ (Φm : C(ClosedUnitDisc, OnePoint EuclideanPlane)) (Ψm : C(ClosedUnitDisc, EuclideanPlane)),
      IsPolar (cylinderSphereDrawing F) (dartCurve γ d a) Φm →
      (∀ x, Φm x = (Ψm x : OnePoint EuclideanPlane)) →
      0 < wind (fun w : Circle => chartC Ψm w) (chartC Ψm 0) →
      (rimDirs (cylinderSphereDrawing F) Φm).Finite →
      ∀ (Wm : Circle), Wm ∈ rimDirs (cylinderSphereDrawing F) Φm → ∀ (δ : ℝ),
      RunsOut Ψm Wm (dartCurve γ d) a δ →
      (hρ'.label (R.faceOf d)).1 = cornerRegion (cylinderSphereDrawing F) Φm Wm := by
    intro d a ha Φm Ψm hpm hΨm hposm hDm Wm hWm δ hrunm
    rw [hρ'.label_faceOf]
    obtain ⟨Φ, z, hst, hρd⟩ := hform' d
    rw [hρd]
    obtain ⟨Ψ, hΨ, hw⟩ := hst.pos
    have hpos : 0 < wind (fun w : Circle => chartC Ψ w) (chartC Ψ 0) := by
      rw [wind_chartC]; exact hw
    obtain ⟨δu, hrunu⟩ := hst.runsOut hγ hΨ rfl
    have hpu : IsPolar (cylinderSphereDrawing F) (dartCurve γ d 0) Φ := by
      rw [dartCurve_zero]; exact hst.polar
    exact cornerRegion_start_eq_mid hS hinf d.2 (isEdgeCurve_dartCurve hγ d) hpu hΨ hpos
      (hst.rimDirs_finite hγ) (hst.mem_rimDirs hγ rfl) hrunu ha hpm hΨm hposm hDm hWm hrunm
  have hface := face_reverse_inner_gap i hG hFU he hγe hρ'.label hL
  rw [heq d, ← hρ'.label_faceOf d, reverseInnerGapDart, ← hface]
  exact Subtype.ext_iff.symm.trans hbij.1.eq_iff

end FaceForm

section OnePath

variable {G : Drawing ClosedCylinder} {θ : ℝ} {D : Set (ℝ × ℝ)}
  (L : CylinderLinkage 1 G) (hG : IsCylinderSection5Drawing 1 G) (hθ : L.HasTheta θ)
  (hD : IsClosedDisc D) (hBd : discBd D = liftedStripBoundary hG.1 L 1)
  (hstrip : D ⊆ {p : ℝ × ℝ | 1 ≤ p.1 ∧ p.1 ≤ 2})
  (hno : ¬ Section5AnyReductionApplies 1 G L)
  {H : Drawing ClosedCylinder} (hGH : G.IsSubdrawing H) (hFU : H.U = G.U ∪ bd ClosedCylinder)
  (hFV : H.V = G.V)
  {γ : Set (OnePoint EuclideanPlane) → I → OnePoint EuclideanPlane}
  {R : DartRotation (DrawingDart (cylinderSphereDrawing H))}
  (hγ : EdgePar (cylinderSphereDrawing H) γ) (hR : IsDrawingRotation (cylinderSphereDrawing H) γ R)
  (hccw : IsCcwRotation (cylinderSphereDrawing H) γ R)
  (heI : ∀ j : Fin 1, cylinderToSphere '' (initialCuffGapCurve 1 j '' Ioo 0 1) ∈
    (cylinderSphereDrawing H).E)
  (hγI : ∀ j : Fin 1, ∀ t, γ (cylinderToSphere '' (initialCuffGapCurve 1 j '' Ioo 0 1)) t =
    cylinderToSphere (initialCuffGapCurve 1 j t))
  (heO : ∀ j : Fin 1, cylinderToSphere '' (alg511OuterCuffGapCurve 1 j '' Ioo 0 1) ∈
    (cylinderSphereDrawing H).E)
  (hγO : ∀ j : Fin 1, ∀ t, γ (cylinderToSphere '' (alg511OuterCuffGapCurve 1 j '' Ioo 0 1)) t =
    cylinderToSphere (alg511OuterCuffGapCurve 1 j t))
  (hV : ∀ v ∈ (cylinderSphereDrawing H).V, ∃ a : DrawingDart (cylinderSphereDrawing H),
    dartVertex γ a = v)

include hno hFU hγ hR hccw hγI hV in
/-- The data behind the face form: side sets around the two lifts, a corner label read from
counterclockwise stars, and the translation of "the corner after `d` is `R₁`" into the face orbit
of `c̄₁`. -/
theorem exists_sides_and_label :
    ∃ U₁ U₂ : Set CylinderCover, IsOpen U₁ ∧ IsOpen U₂ ∧ Disjoint U₁ U₂ ∧
      (∀ t, coverLift L hG 1 t ∈ U₁) ∧ (∀ t, coverLift L hG 2 t ∈ U₂) ∧
      ∃ ρ : DrawingDart (cylinderSphereDrawing H) → Set (OnePoint EuclideanPlane),
        (∀ d, ∃ (Φ : C(ClosedUnitDisc, OnePoint EuclideanPlane))
          (z : DrawingDart (cylinderSphereDrawing H) → Circle),
          IsCcwStar (cylinderSphereDrawing H) γ R (dartVertex γ d) Φ z ∧
            ρ d = cornerRegion (cylinderSphereDrawing H) Φ (z d)) ∧
        ∀ d, ρ d = cylinderToSphere '' (cylinderRegion 1 G 0 \ bd ClosedCylinder) ↔
          R.faceOf d = R.faceOf (reverseInnerGapDart 1 0 H (heI 0)) := by
  obtain ⟨U₁, U₂, hU₁, hU₂, hU, h₁, h₂⟩ := exists_side_sets L hG
  obtain ⟨ρ, -, hform⟩ := exists_cornerLabel (infty_notMem_cylinderSphereDrawing_U H) hγ hR hccw
  have hc := DartRotation.connected_of_isPreconnected_U hγ hR
    (isPreconnected_cylinderSphereDrawing_U_of_no_reduction' L one_pos hG hno hFU)
  exact ⟨U₁, U₂, hU₁, hU₂, hU, h₁, h₂, ρ, hform,
    cornerLabel_eq_region_iff_faceOf hG hFU hγ hR hccw hc hV 0 (heI 0) (hγI 0) hform⟩

include hθ hD hBd hstrip hno hGH hFU hFV hγ hR hccw hγI hV in
/-- **The lifted incidence at an inner vertex of `P₁`, face form.** Let `x = P₁(t)` be a vertex
of `P₁` other than its ends, `b` the dart at `x` along `P₁` forward and `a` the dart at `x` along
`P₁` backward. Then `Γ₁(t)` is in the closure of `R̃₁` exactly when some dart of the block
`b, R.rot b, …` before `a` is in the face orbit of `c̄₁`, and `Γ₂(t)` is in it exactly when some
dart of the block `a, R.rot a, …` before `b` is in that orbit. -/
theorem lifted_face_vertex {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1)
    {a b : DrawingDart (cylinderSphereDrawing H)}
    (hb : dartVertex γ b = spherePath L t) (hbX : b.1.1 ⊆ cylinderToSphere '' (L.pathDrawing 0).U)
    {t₁ : ℝ} (ht₁ : t₁ ∈ Icc (0 : ℝ) 1) (htt₁ : t < t₁)
    (hb1 : dartVertex γ (dartFlip _ b) = spherePath L t₁)
    (ha : dartVertex γ a = spherePath L t) (haX : a.1.1 ⊆ cylinderToSphere '' (L.pathDrawing 0).U)
    {t₂ : ℝ} (ht₂ : t₂ ∈ Icc (0 : ℝ) 1) (htt₂ : t₂ < t)
    (ha1 : dartVertex γ (dartFlip _ a) = spherePath L t₂) :
    (coverLift L hG 1 ⟨t, Ioo_subset_Icc_self ht⟩ ∈ closure (cylinderCoverRegion 1 G 0) ↔
      ∃ i, (∀ j ≤ i, R.rot^[j] b ≠ a) ∧
        R.faceOf (R.rot^[i] b) = R.faceOf (reverseInnerGapDart 1 0 H (heI 0))) ∧
    (coverLift L hG 2 ⟨t, Ioo_subset_Icc_self ht⟩ ∈ closure (cylinderCoverRegion 1 G 0) ↔
      ∃ i, (∀ j ≤ i, R.rot^[j] a ≠ b) ∧
        R.faceOf (R.rot^[i] a) = R.faceOf (reverseInnerGapDart 1 0 H (heI 0))) := by
  obtain ⟨U₁, U₂, hU₁, hU₂, hU, h₁, h₂, ρ, hform, hiff⟩ :=
    exists_sides_and_label L hG hno hFU hγ hR hccw heI hγI hV
  have h := lifted_incidence_vertex L hG hθ hD hBd hstrip hU₁ hU₂ hU h₁ h₂ hGH hFU hFV hγ hR hccw
    heI hγI hV hform ht hb hbX ht₁ htt₁ hb1 ha haX ht₂ htt₂ ha1
  simp only [hiff] at h
  exact h

include hθ hD hBd hstrip hno hGH hFU hFV hγ hR hccw hγI hV in
/-- **The lifted incidence inside an edge of `P₁`, face form.** Let `d` be the dart of an edge
of `P₁` that runs forward along `P₁`, and `P₁(s)` an inner point of that edge. Then `Γ₁(s)` is in
the closure of `R̃₁` exactly when `d` is in the face orbit of `c̄₁`, and `Γ₂(s)` is in it exactly
when the reverse of `d` is. -/
theorem lifted_face_edge {s : ℝ} (hs : s ∈ Ioo (0 : ℝ) 1)
    {d : DrawingDart (cylinderSphereDrawing H)}
    (hdX : d.1.1 ⊆ cylinderToSphere '' (L.pathDrawing 0).U)
    {t₀ t₁ : ℝ} (ht₀ : t₀ ∈ Icc (0 : ℝ) 1) (ht₁ : t₁ ∈ Icc (0 : ℝ) 1) (htt : t₀ < t₁)
    (hd0 : dartVertex γ d = spherePath L t₀) (hd1 : dartVertex γ (dartFlip _ d) = spherePath L t₁)
    (hsd : spherePath L s ∈ d.1.1) :
    (coverLift L hG 1 ⟨s, Ioo_subset_Icc_self hs⟩ ∈ closure (cylinderCoverRegion 1 G 0) ↔
      R.faceOf d = R.faceOf (reverseInnerGapDart 1 0 H (heI 0))) ∧
    (coverLift L hG 2 ⟨s, Ioo_subset_Icc_self hs⟩ ∈ closure (cylinderCoverRegion 1 G 0) ↔
      R.faceOf (dartFlip _ d) = R.faceOf (reverseInnerGapDart 1 0 H (heI 0))) := by
  obtain ⟨U₁, U₂, hU₁, hU₂, hU, h₁, h₂, ρ, hform, hiff⟩ :=
    exists_sides_and_label L hG hno hFU hγ hR hccw heI hγI hV
  have h := lifted_incidence_edge L hG hθ hD hBd hstrip hU₁ hU₂ hU h₁ h₂ hGH hFU hFV hγ hR hccw
    heI hγI hV hform hs hdX ht₀ ht₁ htt hd0 hd1 hsd
  simp only [hiff] at h
  exact h

include hθ hD hBd hstrip hno hGH hFU hFV hγ hR hccw hγI hγO hV in
/-- **The lifted incidence at the end of `P₁`, face form.** Let `a` be the dart of the last edge
of `P₁` at its end, and `c⁺, c⁻` the darts of the outer cuff loop (`false` and `true`). Then
`Γ₁(1)` is in the closure of `R̃₁` exactly when some dart of the block `c⁺, R.rot c⁺, …` before `a`
is in the face orbit of `c̄₁`, and `Γ₂(1)` is in it exactly when some dart of the block
`a, R.rot a, …` before `c⁻` is in that orbit. -/
theorem lifted_face_end {a : DrawingDart (cylinderSphereDrawing H)}
    (ha : dartVertex γ a = spherePath L 1) (haX : a.1.1 ⊆ cylinderToSphere '' (L.pathDrawing 0).U)
    {t₂ : ℝ} (ht₂ : t₂ ∈ Icc (0 : ℝ) 1) (htt₂ : t₂ < 1)
    (ha1 : dartVertex γ (dartFlip _ a) = spherePath L t₂) :
    (coverLift L hG 1 1 ∈ closure (cylinderCoverRegion 1 G 0) ↔
      ∃ i, (∀ j ≤ i, R.rot^[j]
          ⟨(cylinderToSphere '' (alg511OuterCuffGapCurve 1 0 '' Ioo 0 1), false), heO 0⟩ ≠ a) ∧
        R.faceOf (R.rot^[i]
          ⟨(cylinderToSphere '' (alg511OuterCuffGapCurve 1 0 '' Ioo 0 1), false), heO 0⟩) =
          R.faceOf (reverseInnerGapDart 1 0 H (heI 0))) ∧
    (coverLift L hG 2 1 ∈ closure (cylinderCoverRegion 1 G 0) ↔
      ∃ i, (∀ j ≤ i, R.rot^[j] a ≠
          ⟨(cylinderToSphere '' (alg511OuterCuffGapCurve 1 0 '' Ioo 0 1), true), heO 0⟩) ∧
        R.faceOf (R.rot^[i] a) = R.faceOf (reverseInnerGapDart 1 0 H (heI 0))) := by
  obtain ⟨U₁, U₂, hU₁, hU₂, hU, h₁, h₂, ρ, hform, hiff⟩ :=
    exists_sides_and_label L hG hno hFU hγ hR hccw heI hγI hV
  have h := lifted_incidence_end L hG hθ hD hBd hstrip hU₁ hU₂ hU h₁ h₂ hGH hFU hFV hγ hR hccw
    heI hγI heO hγO hV hform ha haX ht₂ htt₂ ha1
  simp only [hiff] at h
  exact h

end OnePath

end GraphMinor.GM06
