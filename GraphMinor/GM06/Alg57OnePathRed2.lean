module

public import GraphMinor.GM06.Alg57OnePathOffPath
import GraphMinor.Compute.GM06RotationPredecessors
import all GraphMinor.GM06.Alg57CutFaceLink
import GraphMinor.GM06.Section5OpenCutSheet
import GraphMinor.GM06.Section5CoverRegion
import GraphMinor.GM06.Alg57CurrentCutCopyUnique
import GraphMinor.Compute.GM06CutRowEncoding
import GraphMinor.GM06.Alg57SubdrawingRegions

/-!
# The one-path incidence when only Reduction 2 is excluded

The face-form incidence of `Alg57OnePathFaceForm`, its reading from the cut orbit in
`Alg57OnePathCutIncidence`, and the off-path statements of `Alg57OnePathOffPath` assume that no
reduction applies. Their proofs use this only to know that `G` together with the two cuffs is
connected, and that follows already when Reduction 2 does not apply
(`isConnected_drawing_and_cuffs_of_no_reduction2`). The Reduction 4 phase runs while Reduction 4
may still apply, so we restate these results under the weaker hypothesis. Each result here has the
name of the original with `_red2` added, and the same proof.
-/

@[expose] public section

namespace GraphMinor.GM06

open Set Topology GraphMinor.Surface GraphMinor.GM11 GraphMinor.Compute unitInterval

section Connected

variable {k : ℕ} {G F : Drawing ClosedCylinder}
  {γ : Set (OnePoint EuclideanPlane) → I → OnePoint EuclideanPlane}
  {R : DartRotation (DrawingDart (cylinderSphereDrawing F))}

/-- The sphere picture of `G` with its cuffs is connected when Reduction 2 does not apply. -/
theorem isPreconnected_sphere_U_of_red2 (L : CylinderLinkage k G)
    (hk : 0 < k) (hG : IsCylinderSection5Drawing k G)
    (hno : ∀ (G₁ : Drawing ClosedCylinder) (L₁ : CylinderLinkage k G₁),
      IsCylinderSection5Drawing k G₁ → ¬ Section5Reduction2Step k G L G₁ L₁)
    (hFU : F.U = G.U ∪ bd ClosedCylinder) : IsPreconnected (cylinderSphereDrawing F).U := by
  rw [cylinderSphereDrawing_U, hFU, union_comm]
  exact ((isConnected_drawing_and_cuffs_of_no_reduction2 L hk hG hno).image _
    continuous_cylinderToSphere.continuousOn).isPreconnected

/-- `region_incidence_of_no_reduction'` when only Reduction 2 is excluded. -/
theorem region_incidence_of_red2 (L : CylinderLinkage k G) (hk : 0 < k)
    (hG : IsCylinderSection5Drawing k G)
    (hno : ∀ (G₁ : Drawing ClosedCylinder) (L₁ : CylinderLinkage k G₁),
      IsCylinderSection5Drawing k G₁ → ¬ Section5Reduction2Step k G L G₁ L₁)
    (hFU : F.U = G.U ∪ bd ClosedCylinder) (hγ : EdgePar (cylinderSphereDrawing F) γ)
    (hR : IsDrawingRotation (cylinderSphereDrawing F) γ R)
    (hccw : IsCcwRotation (cylinderSphereDrawing F) γ R) (i : Fin k)
    (he : cylinderToSphere '' (initialCuffGapCurve k i '' Ioo 0 1) ∈ (cylinderSphereDrawing F).E)
    (hγe : ∀ t, γ (cylinderToSphere '' (initialCuffGapCurve k i '' Ioo 0 1)) t =
      cylinderToSphere (initialCuffGapCurve k i t)) :
    (∀ v : ClosedCylinder, cylinderToSphere v ∈ (cylinderSphereDrawing F).V →
      (v ∈ closure (cylinderRegion k G i) ↔
        ∃ d : DrawingDart (cylinderSphereDrawing F), dartVertex γ d = cylinderToSphere v ∧
          R.faceOf d = R.faceOf (reverseInnerGapDart k i F he))) ∧
    (∀ d : DrawingDart (cylinderSphereDrawing F),
      d.1.1 ⊆ cylinderToSphere '' closure (cylinderRegion k G i) ↔
        R.faceOf d = R.faceOf (reverseInnerGapDart k i F he) ∨
          R.faceOf (R.rev d) = R.faceOf (reverseInnerGapDart k i F he)) := by
  have hU := isPreconnected_sphere_U_of_red2 L hk hG hno hFU
  exact region_incidence_of_ccw hG hFU hγ hR hccw (DartRotation.connected_of_isPreconnected_U hγ hR hU)
    (exists_dart_of_isPreconnected_U hγ hU ⟨_, he⟩) i he hγe

end Connected

section OnePath

variable {G : Drawing ClosedCylinder} {θ : ℝ} {D : Set (ℝ × ℝ)}
  (L : CylinderLinkage 1 G) (hG : IsCylinderSection5Drawing 1 G) (hθ : L.HasTheta θ)
  (hD : IsClosedDisc D) (hBd : discBd D = liftedStripBoundary hG.1 L 1)
  (hstrip : D ⊆ {p : ℝ × ℝ | 1 ≤ p.1 ∧ p.1 ≤ 2})
  (hno : ∀ (G₁ : Drawing ClosedCylinder) (L₁ : CylinderLinkage 1 G₁),
    IsCylinderSection5Drawing 1 G₁ → ¬ Section5Reduction2Step 1 G L G₁ L₁)
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
theorem exists_sides_and_label_red2 :
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
    (isPreconnected_sphere_U_of_red2 L one_pos hG hno hFU)
  exact ⟨U₁, U₂, hU₁, hU₂, hU, h₁, h₂, ρ, hform,
    cornerLabel_eq_region_iff_faceOf hG hFU hγ hR hccw hc hV 0 (heI 0) (hγI 0) hform⟩

include hθ hD hBd hstrip hno hGH hFU hFV hγ hR hccw hγI hV in
/-- **The lifted incidence at an inner vertex of `P₁`, face form.** Let `x = P₁(t)` be a vertex
of `P₁` other than its ends, `b` the dart at `x` along `P₁` forward and `a` the dart at `x` along
`P₁` backward. Then `Γ₁(t)` is in the closure of `R̃₁` exactly when some dart of the block
`b, R.rot b, …` before `a` is in the face orbit of `c̄₁`, and `Γ₂(t)` is in it exactly when some
dart of the block `a, R.rot a, …` before `b` is in that orbit. -/
theorem lifted_face_vertex_red2 {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1)
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
    exists_sides_and_label_red2 L hG hno hFU hγ hR hccw heI hγI hV
  have h := lifted_incidence_vertex L hG hθ hD hBd hstrip hU₁ hU₂ hU h₁ h₂ hGH hFU hFV hγ hR hccw
    heI hγI hV hform ht hb hbX ht₁ htt₁ hb1 ha haX ht₂ htt₂ ha1
  simp only [hiff] at h
  exact h

include hθ hD hBd hstrip hno hGH hFU hFV hγ hR hccw hγI hV in
/-- **The lifted incidence inside an edge of `P₁`, face form.** Let `d` be the dart of an edge
of `P₁` that runs forward along `P₁`, and `P₁(s)` an inner point of that edge. Then `Γ₁(s)` is in
the closure of `R̃₁` exactly when `d` is in the face orbit of `c̄₁`, and `Γ₂(s)` is in it exactly
when the reverse of `d` is. -/
theorem lifted_face_edge_red2 {s : ℝ} (hs : s ∈ Ioo (0 : ℝ) 1)
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
    exists_sides_and_label_red2 L hG hno hFU hγ hR hccw heI hγI hV
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
theorem lifted_face_end_red2 {a : DrawingDart (cylinderSphereDrawing H)}
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
    exists_sides_and_label_red2 L hG hno hFU hγ hR hccw heI hγI hV
  have h := lifted_incidence_end L hG hθ hD hBd hstrip hU₁ hU₂ hU h₁ h₂ hGH hFU hFV hγ hR hccw
    heI hγI heO hγO hV hform ha haX ht₂ htt₂ ha1
  simp only [hiff] at h
  exact h

end OnePath

namespace GM06CurrentDrawingRep

variable {x : GM06SuccessorInput} {G : Drawing ClosedCylinder} {L : CylinderLinkage 1 G}
  (rep : GM06CurrentDrawingRep x G L)

local notation "cutTables" => gm06BuildCutTables x.vertexCount rep.tagged.length x.endpoints
  x.linkage x.innerCuff x.outerCuff
local notation "cutNext" => Equiv.trans dartMatePerm
  (Equiv.symm (gm06RotationPermutation (gm06SplitRotationRows cutTables x.rotations)))
local notation "gapCut" => gm06CutDart (2 * rep.tagged.length + 1) 0

include rep in
/-- The facts about the current drawing that the one-path statements use: its rotation, the
labels of the cuff gaps, and the old face orbit of `c̄₁` read numerically. -/
theorem one_path_setting_red2 (hG : IsCylinderSection5Drawing 1 G)
    (hno : ∀ (G₁ : Drawing ClosedCylinder) (L₁ : CylinderLinkage 1 G₁),
    IsCylinderSection5Drawing 1 G₁ → ¬ Section5Reduction2Step 1 G L G₁ L₁) :
    ∃ R : DartRotation (DrawingDart (cylinderSphereDrawing rep.cuffed)),
      IsDrawingRotation (cylinderSphereDrawing rep.cuffed) rep.par R ∧
      IsCcwRotation (cylinderSphereDrawing rep.cuffed) rep.par R ∧
      R.rev = dartFlip (cylinderSphereDrawing rep.cuffed) ∧
      (∀ d, persistentDartLabel rep.label (R.rot d) =
        gm06RotationPermutation x.rotations (persistentDartLabel rep.label d)) ∧
      ∃ (heI : ∀ j : Fin 1, cylinderToSphere '' (initialCuffGapCurve 1 j '' Ioo 0 1) ∈
          (cylinderSphereDrawing rep.cuffed).E)
        (heO : ∀ j : Fin 1, cylinderToSphere '' (alg511OuterCuffGapCurve 1 j '' Ioo 0 1) ∈
          (cylinderSphereDrawing rep.cuffed).E),
        (∀ v ∈ (cylinderSphereDrawing rep.cuffed).V,
          ∃ a : DrawingDart (cylinderSphereDrawing rep.cuffed), dartVertex rep.par a = v) ∧
        persistentDartLabel rep.label
          ⟨(cylinderToSphere '' (alg511OuterCuffGapCurve 1 0 '' Ioo 0 1), false), heO 0⟩ =
            2 * (rep.tagged.length + 1) ∧
        persistentDartLabel rep.label
          ⟨(cylinderToSphere '' (alg511OuterCuffGapCurve 1 0 '' Ioo 0 1), true), heO 0⟩ =
            2 * (rep.tagged.length + 1) + 1 ∧
        ∀ d, R.faceOf d = R.faceOf (reverseInnerGapDart 1 0 rep.cuffed (heI 0)) ↔
          ∃ n, (Equiv.trans dartMatePerm (Equiv.symm (gm06RotationPermutation x.rotations)))^[n]
            (gm06UncutDart gapCut) = persistentDartLabel rep.label d := by
  obtain ⟨R, hR, hccw, hrev, hrot⟩ := rep.exists_ccwRotation
  have heI : ∀ j : Fin 1, cylinderToSphere '' (initialCuffGapCurve 1 j '' Ioo 0 1) ∈
      (cylinderSphereDrawing rep.cuffed).E := fun j => by
    obtain ⟨f, hf, -⟩ := rep.inner_labels j
    exact hf ▸ f.property
  have heO : ∀ j : Fin 1, cylinderToSphere '' (alg511OuterCuffGapCurve 1 j '' Ioo 0 1) ∈
      (cylinderSphereDrawing rep.cuffed).E := fun j => by
    obtain ⟨f, hf, -⟩ := rep.outer_labels j
    exact hf ▸ f.property
  have hV := exists_dart_of_isPreconnected_U rep.edgePar
    (isPreconnected_sphere_U_of_red2 L one_pos hG hno rep.cuffed_U)
    ⟨_, heI 0⟩
  have hO : ∀ b : Bool, persistentDartLabel rep.label
      ⟨(cylinderToSphere '' (alg511OuterCuffGapCurve 1 0 '' Ioo 0 1), b), heO 0⟩ =
        2 * (rep.tagged.length + 1) + b.toNat := by
    intro b
    obtain ⟨f, hf, hl⟩ := rep.outer_labels 0
    have heq : (⟨cylinderToSphere '' (alg511OuterCuffGapCurve 1 0 '' Ioo 0 1), heO 0⟩ :
        (cylinderSphereDrawing rep.cuffed).E) = f := Subtype.ext hf.symm
    simp only [persistentDartLabel, heq, hl, Fin.val_zero]
  have hc : gm06UncutDart gapCut = 2 * (rep.tagged.length + (0 : Fin 1).val) + 1 := by
    simp [gm06UncutDart, gm06CutDart, Nat.add_div, Nat.add_mod]
    omega
  refine ⟨R, hR, hccw, hrev, hrot, heI, heO, hV, by simpa using hO false, by simpa using hO true,
    fun d => ?_⟩
  rw [faceOf_eq_iff_permanent_orbit rep.label x.rotations R hrev hrot, hc,
    rep.reverseInnerGapDart_label 0 (heI 0)]

section Copies

variable {θ : ℝ} {D : Set (ℝ × ℝ)} (hG : IsCylinderSection5Drawing 1 G)
  (hno : ∀ (G₁ : Drawing ClosedCylinder) (L₁ : CylinderLinkage 1 G₁),
    IsCylinderSection5Drawing 1 G₁ → ¬ Section5Reduction2Step 1 G L G₁ L₁) (hθ : L.HasTheta θ)
  (hD : IsClosedDisc D) (hBd : discBd D = liftedStripBoundary hG.1 L 1)
  (hstrip : D ⊆ {p : ℝ × ℝ | 1 ≤ p.1 ∧ p.1 ≤ 2})

include hθ hD hBd hstrip hno in
/-- **The lifted incidence at an inner vertex of `P₁`, read from the cut orbit.** Let `x = P₁(t)` be
a vertex of `P₁` other than its ends, at slot `v`, with backward path dart `a` and forward path
dart `b`, so that the cut position at `v` is `interior a b`. Then `Γ₁(t)` is in the closure of `R̃₁`
exactly when the cut face orbit of `c̄₁` contains a dart of the left copy of `v`, and `Γ₂(t)` is in
it exactly when that orbit contains a dart of the right copy. -/
theorem one_path_vertex_copy_iff_red2 {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1)
    {a b : DrawingDart (cylinderSphereDrawing rep.cuffed)}
    (hb : dartVertex rep.par b = spherePath L t)
    (hbX : b.1.1 ⊆ cylinderToSphere '' (L.pathDrawing 0).U)
    {t₁ : ℝ} (ht₁ : t₁ ∈ Icc (0 : ℝ) 1) (htt₁ : t < t₁)
    (hb1 : dartVertex rep.par (dartFlip _ b) = spherePath L t₁)
    (ha : dartVertex rep.par a = spherePath L t)
    (haX : a.1.1 ⊆ cylinderToSphere '' (L.pathDrawing 0).U)
    {t₂ : ℝ} (ht₂ : t₂ ∈ Icc (0 : ℝ) 1) (htt₂ : t₂ < t)
    (ha1 : dartVertex rep.par (dartFlip _ a) = spherePath L t₂)
    {v : ℕ} (hv : v < x.vertexCount)
    (hp : gm06CutPositionAt cutTables v =
      some (.interior (persistentDartLabel rep.label a) (persistentDartLabel rep.label b))) :
    (coverLift L hG 1 ⟨t, Ioo_subset_Icc_self ht⟩ ∈ closure (cylinderCoverRegion 1 G 0) ↔
      ∃ n, (cutNext)^[n] gapCut ∈
        (gm06SplitRotationRows cutTables x.rotations).getD (gm06CutVertex v true) []) ∧
    (coverLift L hG 2 ⟨t, Ioo_subset_Icc_self ht⟩ ∈ closure (cylinderCoverRegion 1 G 0) ↔
      ∃ n, (cutNext)^[n] gapCut ∈
        (gm06SplitRotationRows cutTables x.rotations).getD (gm06CutVertex v false) []) := by
  obtain ⟨R, hR, hccw, -, hrot, heI, heO, hV, -, -, hface⟩ := rep.one_path_setting_red2 hG hno
  obtain ⟨h1, h2⟩ := lifted_face_vertex_red2 L hG hθ hD hBd hstrip hno rep.subdrawing rep.cuffed_U
    rep.cuffed_V rep.edgePar hR hccw heI rep.inner_par hV ht hb hbX ht₁ htt₁ hb1 ha haX ht₂ htt₂
    ha1
  have hlt : v < x.rotations.length := rep.rows_length ▸ hv
  set row := x.rotations.getD v [] with hrow_def
  have hvr : x.rotations[v]? = some row := by
    rw [hrow_def, List.getD_eq_getElem _ _ hlt, List.getElem?_eq_getElem hlt]
  have hrow : row ∈ x.rotations := List.mem_of_getElem? hvr
  have hok := rep.cut_block_ok hG v row _ hvr hp
  have hlb : persistentDartLabel rep.label b ∈ row := (cutBlock_spec hok true).1
  have hla : persistentDartLabel rep.label a ∈ row := (cutBlock_spec hok true).2.1
  have hcopy := fun left => cut_orbit_mem_copy_iff cutTables x.rotations rep.rows_flatten_nodup
    (rep.cut_block_ok hG) (rep.cut_fits one_pos) (fun _ h => rep.cut_rows_mate hG h)
    (rep.reverse_inner_mem_cut hG 0) (rep.reverse_inner_cut_mate_not_first one_pos 0) hvr hp left
  simp only [Fin.val_zero, add_zero] at hcopy
  have hit := fun {d} (hd : persistentDartLabel rep.label d ∈ row) =>
    persistentDartLabel_rot_iterate rep.label x.rotations rep.rows_flatten_nodup R hrot hrow hd
  have hinj := persistentDartLabel_injective rep.label
  rw [splitRows_getD_of_position hlt hp, splitRows_getD_of_position hlt hp, hcopy true,
    hcopy false, h1, h2]
  simp only [cutFirst, cutLast]
  constructor
  · refine exists_congr fun i => and_congr (forall_congr' fun j => imp_congr_right fun _ => ?_) ?_
    · rw [← hit hlb j]; exact hinj.ne_iff.symm
    · rw [hface, hit hlb i]
  · refine exists_congr fun i => and_congr (forall_congr' fun j => imp_congr_right fun _ => ?_) ?_
    · rw [← hit hla j]; exact hinj.ne_iff.symm
    · rw [hface, hit hla i]

include hθ hD hBd hstrip hno in
/-- **The lifted incidence at the end of `P₁`, read from the cut orbit.** Let `P₁(1)` be at slot
`v`, with `a` the dart of the last edge of `P₁` at it, so that the cut position at `v` is the
terminal position with `a` and the two outer cuff ends. Then `Γ₁(1)` is in the closure of `R̃₁`
exactly when the cut face orbit of `c̄₁` contains a dart of the left copy of `v`, and `Γ₂(1)` is in
it exactly when that orbit contains a dart of the right copy. -/
theorem one_path_end_copy_iff_red2 {a : DrawingDart (cylinderSphereDrawing rep.cuffed)}
    (ha : dartVertex rep.par a = spherePath L 1)
    (haX : a.1.1 ⊆ cylinderToSphere '' (L.pathDrawing 0).U)
    {t₂ : ℝ} (ht₂ : t₂ ∈ Icc (0 : ℝ) 1) (htt₂ : t₂ < 1)
    (ha1 : dartVertex rep.par (dartFlip _ a) = spherePath L t₂)
    {v : ℕ} (hv : v < x.vertexCount)
    (hp : gm06CutPositionAt cutTables v =
      some (.terminal (persistentDartLabel rep.label a) (2 * (rep.tagged.length + 1))
        (2 * (rep.tagged.length + 1) + 1))) :
    (coverLift L hG 1 1 ∈ closure (cylinderCoverRegion 1 G 0) ↔
      ∃ n, (cutNext)^[n] gapCut ∈
        (gm06SplitRotationRows cutTables x.rotations).getD (gm06CutVertex v true) []) ∧
    (coverLift L hG 2 1 ∈ closure (cylinderCoverRegion 1 G 0) ↔
      ∃ n, (cutNext)^[n] gapCut ∈
        (gm06SplitRotationRows cutTables x.rotations).getD (gm06CutVertex v false) []) := by
  obtain ⟨R, hR, hccw, -, hrot, heI, heO, hV, hOf, hOt, hface⟩ := rep.one_path_setting_red2 hG hno
  obtain ⟨h1, h2⟩ := lifted_face_end_red2 L hG hθ hD hBd hstrip hno rep.subdrawing rep.cuffed_U
    rep.cuffed_V rep.edgePar hR hccw heI rep.inner_par heO rep.outer_par hV ha haX ht₂ htt₂ ha1
  have hlt : v < x.rotations.length := rep.rows_length ▸ hv
  set row := x.rotations.getD v [] with hrow_def
  have hvr : x.rotations[v]? = some row := by
    rw [hrow_def, List.getD_eq_getElem _ _ hlt, List.getElem?_eq_getElem hlt]
  have hrow : row ∈ x.rotations := List.mem_of_getElem? hvr
  have hok := rep.cut_block_ok hG v row _ hvr hp
  have hcopy := fun left => cut_orbit_mem_copy_iff cutTables x.rotations rep.rows_flatten_nodup
    (rep.cut_block_ok hG) (rep.cut_fits one_pos) (fun _ h => rep.cut_rows_mate hG h)
    (rep.reverse_inner_mem_cut hG 0) (rep.reverse_inner_cut_mate_not_first one_pos 0) hvr hp left
  simp only [Fin.val_zero, add_zero] at hcopy
  have hit := fun {d} (hd : persistentDartLabel rep.label d ∈ row) =>
    persistentDartLabel_rot_iterate rep.label x.rotations rep.rows_flatten_nodup R hrot hrow hd
  have hinj := persistentDartLabel_injective rep.label
  have hla : persistentDartLabel rep.label a ∈ row := (cutBlock_spec hok false).1
  have hcp : 2 * (rep.tagged.length + 1) ∈ row := (cutBlock_spec hok true).1
  rw [← hOf] at hcp
  rw [splitRows_getD_of_position hlt hp, splitRows_getD_of_position hlt hp, hcopy true,
    hcopy false, h1, h2]
  simp only [cutFirst, cutLast]
  rw [← hOt, ← hOf]
  constructor
  · refine exists_congr fun i => and_congr (forall_congr' fun j => imp_congr_right fun _ => ?_) ?_
    · rw [← hit hcp j]; exact hinj.ne_iff.symm
    · rw [hface, hit hcp i]
  · refine exists_congr fun i => and_congr (forall_congr' fun j => imp_congr_right fun _ => ?_) ?_
    · rw [← hit hla j]; exact hinj.ne_iff.symm
    · rw [hface, hit hla i]

include hθ hD hBd hstrip hno in
/-- **The lifted incidence inside an edge of `P₁`, read from the cut orbit.** Let `d` be the dart of
an edge of `P₁` that runs forward along `P₁`, and `P₁(s)` an inner point of that edge. Then `Γ₁(s)`
is in the closure of `R̃₁` exactly when the cut face orbit of `c̄₁` contains a copy of `d`, and
`Γ₂(s)` is in it exactly when that orbit contains a copy of the reverse of `d`. -/
theorem one_path_edge_copy_iff_red2 {s : ℝ} (hs : s ∈ Ioo (0 : ℝ) 1)
    {d : DrawingDart (cylinderSphereDrawing rep.cuffed)}
    (hdX : d.1.1 ⊆ cylinderToSphere '' (L.pathDrawing 0).U)
    {t₀ t₁ : ℝ} (ht₀ : t₀ ∈ Icc (0 : ℝ) 1) (ht₁ : t₁ ∈ Icc (0 : ℝ) 1) (htt : t₀ < t₁)
    (hd0 : dartVertex rep.par d = spherePath L t₀)
    (hd1 : dartVertex rep.par (dartFlip _ d) = spherePath L t₁)
    (hsd : spherePath L s ∈ d.1.1) :
    (coverLift L hG 1 ⟨s, Ioo_subset_Icc_self hs⟩ ∈ closure (cylinderCoverRegion 1 G 0) ↔
      ∃ n, gm06UncutDart ((cutNext)^[n] gapCut) = persistentDartLabel rep.label d) ∧
    (coverLift L hG 2 ⟨s, Ioo_subset_Icc_self hs⟩ ∈ closure (cylinderCoverRegion 1 G 0) ↔
      ∃ n, gm06UncutDart ((cutNext)^[n] gapCut) =
        gm06DartMate (persistentDartLabel rep.label d)) := by
  obtain ⟨R, hR, hccw, -, hrot, heI, heO, hV, -, -, hface⟩ := rep.one_path_setting_red2 hG hno
  obtain ⟨h1, h2⟩ := lifted_face_edge_red2 L hG hθ hD hBd hstrip hno rep.subdrawing rep.cuffed_U
    rep.cuffed_V rep.edgePar hR hccw heI rep.inner_par hV hs hdX ht₀ ht₁ htt hd0 hd1 hsd
  have hproj := fun e => rep.cut_face_orbit_projection_iff hG 0 e
  simp only [Fin.val_zero, add_zero] at hproj
  rw [h1, h2, hface, hface, ← hproj, ← hproj, persistentDartLabel_flip]
  exact ⟨Iff.rfl, Iff.rfl⟩

end Copies

section Off

variable {θ : ℝ} {D : Set (ℝ × ℝ)}

include rep in
/-- **A vertex of the cut drawing off the one path, read from the cut orbit.** Let `a` be a live
slot whose vertex is off `P₁`, and `p` the point of the cut disc over it. Then `p` is in `cutRc`
exactly when the cut face orbit of `c̄₁` contains a dart of the (only) copy of `a`. -/
theorem one_path_off_vertex_iff_red2 (hG : IsCylinderSection5Drawing 1 G)
    (hno : ∀ (G₁ : Drawing ClosedCylinder) (L₁ : CylinderLinkage 1 G₁),
    IsCylinderSection5Drawing 1 G₁ → ¬ Section5Reduction2Step 1 G L G₁ L₁) (hθ : L.HasTheta θ) (hD : IsClosedDisc D)
    (hBd : discBd D = liftedStripBoundary hG.1 L 1)
    (hstrip : D ⊆ {p : ℝ × ℝ | 1 ≤ p.1 ∧ p.1 ≤ 2})
    (a : Fin x.vertexCount) (ha : a ∈ rep.live) (haP : rep.vertex a ∉ (L.pathDrawing 0).U)
    {p : D} (hpa : cutProj D p = rep.vertex a) :
    p ∈ cutRc G D ↔ ∃ n, (cutNext)^[n] gapCut ∈
      (gm06SplitRotationRows cutTables x.rotations).getD (gm06CutVertex a.val true) [] := by
  rw [cutRc_iff_off_path L hG hθ hD hBd hstrip (hpa ▸ haP), hpa]
  obtain ⟨R, hR, hccw, -, hrot, heI, heO, hV, -, -, hface⟩ := rep.one_path_setting_red2 hG hno
  have hvS : cylinderToSphere (rep.vertex a) ∈ (cylinderSphereDrawing rep.cuffed).V := by
    rw [cylinderSphereDrawing_V, rep.cuffed_V]
    exact mem_image_of_mem _ (rep.vertex_mem a ha)
  rw [(region_incidence_of_red2 L one_pos hG hno rep.cuffed_U rep.edgePar hR hccw 0
    (heI 0) (rep.inner_par 0)).1 _ hvS]
  have hproj := fun e => rep.cut_face_orbit_projection_iff hG 0 e
  simp only [Fin.val_zero, add_zero] at hproj
  simp only [hface, hproj]
  -- the vertex is not split
  have hpos : gm06CutPositionAt cutTables a.val = none := by
    rcases h : gm06CutPositionAt cutTables a.val with _ | p
    · rfl
    · exfalso
      obtain ⟨j, hj⟩ := rep.exists_path_of_cut_position a p h
      rw [Subsingleton.elim j 0] at hj
      exact haP ((L.pathDrawing 0).V_subset_U hj)
  have hlt : a.val < x.rotations.length := by rw [rep.rows_length]; exact a.isLt
  set row := x.rotations.getD a.val [] with hrow_def
  have hvr : x.rotations[a.val]? = some row := by
    rw [hrow_def, List.getD_eq_getElem _ _ hlt, List.getElem?_eq_getElem hlt]
  have hslot : (gm06SplitRotationRows cutTables x.rotations).getD (gm06CutVertex a.val true) [] =
      row.map (fun d => gm06CutDart d 0) := by
    rw [splitRows_getD _ _ _ hlt true, hpos]
    have h := gm06SplitVertexRows_eq_selected none row
    simp only [gm06SplitVertexRows] at h
    exact (List.cons_eq_cons.mp h).1.symm
  rw [hslot]
  have hc : gapCut ∈ (gm06SplitRotationRows cutTables x.rotations).flatten := by
    have h := rep.reverse_inner_mem_cut hG 0
    simp only [Fin.val_zero, add_zero] at h
    exact h
  constructor
  · rintro ⟨d, hd, n, hn⟩
    refine ⟨n, ?_⟩
    have hlab : persistentDartLabel rep.label d ∈ row := (rep.label_mem_row_iff a ha d).mpr hd
    obtain ⟨v', row', r, hv', hr, hqr⟩ := exists_vertex_of_mem_split
      (cut_iterate_mem cutTables x.rotations rep.rows_flatten_nodup
        (fun _ h => rep.cut_rows_mate hG h) hc n)
    have hvv : v' = a.val := rows_index_eq_of_mem rep.rows_flatten_nodup hv' hvr
      (uncut_mem_of_mem_splitVertexRows hr hqr) (hn ▸ hlab)
    subst hvv
    rw [hvr] at hv'
    cases hv'
    rw [hpos] at hr
    simp only [gm06SplitVertexRows, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact hqr
    · exact absurd hqr List.not_mem_nil
  · rintro ⟨n, hn⟩
    obtain ⟨e, he, heq⟩ := List.mem_map.mp hn
    obtain ⟨-, h, hh⟩ := (rep.mem_row_iff a e).mp he
    refine ⟨⟨h.1, h.2.1⟩, h.2.2, n, ?_⟩
    rw [← heq, gm06UncutDart_cut e 0 (by decide)]
    exact hh.symm

include rep in
/-- **An edge of the cut drawing off the one path, read from the cut orbit.** Let `e` be an edge of
`G` not in `P₁`, and `d` a dart of `G⁺` along `e`. The points of the cut disc over `e` are in
`cutRc` exactly when the cut face orbit of `c̄₁` contains a copy of `d` or of its reverse. -/
theorem one_path_off_edge_iff_red2 (hG : IsCylinderSection5Drawing 1 G)
    (hno : ∀ (G₁ : Drawing ClosedCylinder) (L₁ : CylinderLinkage 1 G₁),
    IsCylinderSection5Drawing 1 G₁ → ¬ Section5Reduction2Step 1 G L G₁ L₁) (hθ : L.HasTheta θ) (hD : IsClosedDisc D)
    (hBd : discBd D = liftedStripBoundary hG.1 L 1)
    (hstrip : D ⊆ {p : ℝ × ℝ | 1 ≤ p.1 ∧ p.1 ≤ 2})
    {e : Set ClosedCylinder} (he : e ∈ G.E) (heP : e ∉ (L.pathDrawing 0).E)
    (d : DrawingDart (cylinderSphereDrawing rep.cuffed)) (hd : d.1.1 = cylinderToSphere '' e) :
    (fun p : D => radialCylinderProjection p.1) ⁻¹' e ⊆ cutRc G D ↔
      (∃ n, gm06UncutDart ((cutNext)^[n] gapCut) = persistentDartLabel rep.label d) ∨
        ∃ n, gm06UncutDart ((cutNext)^[n] gapCut) =
          gm06DartMate (persistentDartLabel rep.label d) := by
  have hdisj := deleted_edge_disjoint_subdrawing (L.isSubdrawing 0).1 he heP
  have hstep : (fun p : D => radialCylinderProjection p.1) ⁻¹' e ⊆ cutRc G D ↔
      e ⊆ closure (cylinderRegion 1 G 0) := by
    constructor
    · intro h y hy
      have hyP : y ∉ (L.pathDrawing 0).U := disjoint_left.mp hdisj hy
      obtain ⟨sh, -, hproj, hrange⟩ := exists_open_sheet_on_single_strip L hG hθ hD hBd hstrip
      have hmem : sh ⟨y, hyP⟩ ∈ range sh := mem_range_self _
      rw [hrange] at hmem
      obtain ⟨⟨q, hqD, hq⟩, -⟩ := hmem
      have hqy : radialCylinderProjection q = y := by
        have := hproj ⟨y, hyP⟩
        rw [← hq] at this
        exact this
      have hpe : (⟨q, hqD⟩ : D) ∈ (fun p : D => radialCylinderProjection p.1) ⁻¹' e := by
        change radialCylinderProjection q ∈ e
        rw [hqy]; exact hy
      have h' := (cutRc_iff_off_path L hG hθ hD hBd hstrip (p := ⟨q, hqD⟩)
        (by change radialCylinderProjection q ∉ _; rw [hqy]; exact hyP)).mp (h hpe)
      change radialCylinderProjection q ∈ _ at h'
      rwa [hqy] at h'
    · intro h p hp
      exact (cutRc_iff_off_path L hG hθ hD hBd hstrip (disjoint_left.mp hdisj hp)).mpr (h hp)
  obtain ⟨R, hR, hccw, hrev, hrot, heI, heO, hV, -, -, hface⟩ := rep.one_path_setting_red2 hG hno
  have hproj := fun e => rep.cut_face_orbit_projection_iff hG 0 e
  simp only [Fin.val_zero, add_zero] at hproj
  rw [hstep, ← image_subset_image_iff injective_cylinderToSphere, ← hd,
    (region_incidence_of_red2 L one_pos hG hno rep.cuffed_U rep.edgePar hR hccw 0
      (heI 0) (rep.inner_par 0)).2 d, hface, hface, hrev, persistentDartLabel_flip, hproj, hproj]

end Off

end GM06CurrentDrawingRep

end GraphMinor.GM06
