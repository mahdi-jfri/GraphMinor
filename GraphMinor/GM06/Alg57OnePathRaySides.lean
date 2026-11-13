module

public import GraphMinor.GM06.Alg57OnePathEnd
public import GraphMinor.GM06.Alg57OnePathFind4
public import GraphMinor.GM06.Section5CutRegionCoordinates
public import GraphMinor.GM06.Section5CutStripProjection
public import GraphMinor.GM06.Alg57SubdrawingRegions

/-!
# Which lift of a path vertex an edge reaches, for one path

Take one linkage path `P₁` and the cut disc `D` with the two lifts `Γ₁`, `Γ₂` of `P₁` on its
boundary. An edge `f` of `G` off `P₁` has one lift in `D`, the points over `f`. If `f` ends at a
vertex `x = P₁(t)`, the closure of this lift contains `Γ₁(t)` or `Γ₂(t)`, or both when `f` is a
loop that leaves `x` on both sides. Which one is a local question at `x`: it depends on the side
of `P₁` on which `f` leaves `x`.

We read the side from a counterclockwise star at `x`. `RaySides t side` says that there is such a
star in which the ray of each dart `d` along an edge off `P₁` is on side one exactly when
`side d` holds. From it we get both directions:

* `mem_closure_of_raySides`: the lift of the side of `d` is in the closure of the lift of `f`;
* `exists_dart_of_mem_closure_of_raySides`: every point of that closure over `x` is the lift of
  the side of some dart of `f` at `x`.

The first comes from points of the ray close to `x`; their lifts tend to the lift of their side
(`exists_nbhd_lift_mem_one`). The second comes from the converse: points of `f` close to `x` lie
on rays of the star, so their lifts are on the side of a dart of `f`.
-/

@[expose] public section

namespace GraphMinor.GM06

open Set Topology GraphMinor.Surface GraphMinor.GM11 unitInterval

variable {G : Drawing ClosedCylinder} {θ : ℝ} {D : Set (ℝ × ℝ)}

/-- The point of the lift `Γ₁` (for `left`) or `Γ₂` (otherwise) at parameter `t`, as a point of
the cut disc. -/
noncomputable def cutSidePoint (L : CylinderLinkage 1 G) (hG : IsCylinderSection5Drawing 1 G)
    (hBd : discBd D = liftedStripBoundary hG.1 L 1) (left : Bool) (t : I) : D :=
  ⟨liftedLinkageCurve hG.1 L (if left then 1 else 2) t, Surface.discBd_subset D (by
    rw [hBd]
    cases left
    · exact Or.inl (Or.inl (Or.inr (mem_range_self t)))
    · exact Or.inl (Or.inl (Or.inl (mem_range_self t))))⟩

theorem cutSidePoint_val (L : CylinderLinkage 1 G) (hG : IsCylinderSection5Drawing 1 G)
    (hBd : discBd D = liftedStripBoundary hG.1 L 1) (left : Bool) (t : I) :
    (cutSidePoint L hG hBd left t).1 = liftedLinkageCurve hG.1 L (if left then 1 else 2) t := rfl

theorem cutProj_cutSidePoint (L : CylinderLinkage 1 G) (hG : IsCylinderSection5Drawing 1 G)
    (hBd : discBd D = liftedStripBoundary hG.1 L 1) (left : Bool) (t : I) :
    cutProj D (cutSidePoint L hG hBd left t) = L.curve 0 t :=
  radialCylinderProjection_lift_one L hG.1 _ t

theorem cutCov_cutSidePoint (L : CylinderLinkage 1 G) (hG : IsCylinderSection5Drawing 1 G)
    (hBd : discBd D = liftedStripBoundary hG.1 L 1) (left : Bool) (t : I) :
    planeToCylinderCover (cutSidePoint L hG hBd left t).1 =
      coverLift L hG (if left then 1 else 2) t := rfl

section RaySides

variable (L : CylinderLinkage 1 G) (hG : IsCylinderSection5Drawing 1 G)
  {H : Drawing ClosedCylinder}
  {γ : Set (OnePoint EuclideanPlane) → I → OnePoint EuclideanPlane}
  {R : DartRotation (DrawingDart (cylinderSphereDrawing H))}

/-- **The rays at `P₁(t)` are on the named sides.** There is a counterclockwise star at the
vertex `P₁(t)` in which, for each dart `d` there along an edge of `G` off `P₁`, every point of the
ray of `d` is on side one exactly when `side d` holds. -/
def RaySides (D : Set (ℝ × ℝ)) (U₁ : Set CylinderCover) (γ : Set (OnePoint EuclideanPlane) → I →
    OnePoint EuclideanPlane) (R : DartRotation (DrawingDart (cylinderSphereDrawing H))) (t : I)
    (side : DrawingDart (cylinderSphereDrawing H) → Prop) : Prop :=
  ∃ (Φ : C(ClosedUnitDisc, OnePoint EuclideanPlane)) (Ψ : C(ClosedUnitDisc, EuclideanPlane))
    (z : DrawingDart (cylinderSphereDrawing H) → Circle),
    IsCcwStar (cylinderSphereDrawing H) γ R (cylinderToSphere (L.curve 0 t)) Φ z ∧
    (∀ x, Φ x = (Ψ x : OnePoint EuclideanPlane)) ∧
    ∀ d, dartVertex γ d = cylinderToSphere (L.curve 0 t) →
      ∀ f ∈ G.E, f ∉ (L.pathDrawing 0).E → d.1.1 = cylinderToSphere '' f →
      ∀ r : ℝ, 0 < r → r ≤ 1 →
        (side d → sphereSide D U₁ (toSph (chartC Ψ ((r : ℂ) * z d)))) ∧
        (¬ side d → ¬ sphereSide D U₁ (toSph (chartC Ψ ((r : ℂ) * z d))))

variable {L hG} (hθ : L.HasTheta θ) (hD : IsClosedDisc D)
  (hBd : discBd D = liftedStripBoundary hG.1 L 1)
  (hstrip : D ⊆ {p : ℝ × ℝ | 1 ≤ p.1 ∧ p.1 ≤ 2})
  {U₁ U₂ : Set CylinderCover} (hU₁ : IsOpen U₁) (hU₂ : IsOpen U₂) (hU : Disjoint U₁ U₂)
  (h₁ : ∀ t, coverLift L hG 1 t ∈ U₁) (h₂ : ∀ t, coverLift L hG 2 t ∈ U₂)
  (hGH : G.IsSubdrawing H) (hγ : EdgePar (cylinderSphereDrawing H) γ)

/-- Open sets of the cut disc come from open sets of the cover. -/
theorem exists_cover_open_of_open (hD : IsClosedDisc D)
    (hstrip : D ⊆ {p : ℝ × ℝ | 1 ≤ p.1 ∧ p.1 ≤ 2}) {O : Set D} (hO : IsOpen O) :
    ∃ W : Set CylinderCover, IsOpen W ∧ ∀ p : D, p ∈ O ↔ planeToCylinderCover p.1 ∈ W := by
  obtain ⟨W, hW, hWO⟩ :=
    (isClosedEmbedding_single_strip_coverMap hD hstrip).isInducing.isOpen_iff.mp hO
  exact ⟨W, hW, fun p => by rw [← hWO]; rfl⟩

/-- Points of the ray of a direction come as close to the centre of a star as we like. -/
theorem exists_ray_mem_of_open {Φ : C(ClosedUnitDisc, OnePoint EuclideanPlane)}
    {Ψ : C(ClosedUnitDisc, EuclideanPlane)} {Γ : Drawing (OnePoint EuclideanPlane)}
    {c : OnePoint EuclideanPlane} (hp : IsPolar Γ c Φ)
    (hΨ : ∀ x, Φ x = (Ψ x : OnePoint EuclideanPlane)) (w : Circle)
    {V : Set (OnePoint EuclideanPlane)} (hV : IsOpen V) (hcV : c ∈ V) :
    ∃ r : ℝ, 0 < r ∧ r ≤ 1 ∧ toSph (chartC Ψ ((r : ℂ) * w)) ∈ V := by
  have hcont : Continuous fun r : ℝ => toSph (chartC Ψ ((r : ℂ) * w)) :=
    continuous_toSph.comp (continuous_chartC.comp (by fun_prop))
  have h0 : toSph (chartC Ψ (((0 : ℝ) : ℂ) * w)) = c := by
    simp only [Complex.ofReal_zero, zero_mul]
    exact toSph_chartC_zero hp hΨ
  have hmem : (fun r : ℝ => toSph (chartC Ψ ((r : ℂ) * w))) ⁻¹' V ∈ 𝓝 (0 : ℝ) := by
    apply hcont.continuousAt.preimage_mem_nhds
    show V ∈ 𝓝 (toSph (chartC Ψ (((0 : ℝ) : ℂ) * w)))
    rw [h0]
    exact hV.mem_nhds hcV
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp hmem
  refine ⟨min (ε / 2) 1, lt_min (half_pos hε) one_pos, min_le_right _ _, hball ?_⟩
  show dist (min (ε / 2) 1) 0 < ε
  rw [Real.dist_eq, sub_zero, abs_of_pos (lt_min (half_pos hε) one_pos)]
  exact lt_of_le_of_lt (min_le_left _ _) (half_lt_self hε)

include hθ hD hstrip hU₁ hU₂ hU h₁ h₂ hγ in
/-- **The lift of the side of a dart is an end of the lift of its edge.** Let `f` be an edge of
`G` off `P₁` with a dart `d` at the vertex `P₁(t)`. If the rays at `P₁(t)` are on the sides named
by `side`, then the point of `Γ₁(t)` (when `side d`) or of `Γ₂(t)` (otherwise) is in the closure
of the points of `D` over `f`. -/
theorem mem_closure_of_raySides {t : I} {side : DrawingDart (cylinderSphereDrawing H) → Prop}
    (hrs : RaySides L D U₁ γ R t side) {f : Set ClosedCylinder} (hf : f ∈ G.E)
    (hfP : f ∉ (L.pathDrawing 0).E) {d : DrawingDart (cylinderSphereDrawing H)}
    (hd : dartVertex γ d = cylinderToSphere (L.curve 0 t)) (hdf : d.1.1 = cylinderToSphere '' f)
    {left : Bool} (hside : side d ↔ left = true) :
    cutSidePoint L hG hBd left t ∈ closure (cutProj D ⁻¹' f) := by
  obtain ⟨Φ, Ψ, z, hst, hΨ, hray⟩ := hrs
  rw [mem_closure_iff]
  intro O hO hpO
  obtain ⟨W, hW, hOW⟩ := exists_cover_open_of_open hD hstrip hO
  have hpW : planeToCylinderCover (cutSidePoint L hG hBd left t).1 ∈ W := (hOW _).mp hpO
  rw [cutCov_cutSidePoint] at hpW
  -- the neighbourhood of `P₁(t)` where lifts are near the two lifts
  obtain ⟨N₀, hN₀, hxN₀, hN₀lift⟩ :=
    exists_nbhd_lift_mem L hG hθ hD hBd hstrip t hU₁ hU₂ (h₁ t) (h₂ t)
  -- the neighbourhood where lifts on the side of `d` are in `W`
  obtain ⟨N, hN, hxN, hNlift⟩ : ∃ N : Set ClosedCylinder, IsOpen N ∧ L.curve 0 t ∈ N ∧
      ∀ q ∈ planeToCylinderCover '' D, cylinderCoverProjection q ∈ N →
        q ∈ (if left then U₁ else U₂) → q ∈ W := by
    cases left
    · exact exists_nbhd_lift_mem_two L hG hθ hD hBd hstrip hU₁ h₁ hU t hW hpW
    · exact exists_nbhd_lift_mem_one L hG hθ hD hBd hstrip hU₂ h₂ hU t hW hpW
  obtain ⟨V, hV, hVN⟩ := isClosedEmbedding_cylinderToSphere.isInducing.isOpen_iff.mp
    (hN.inter hN₀)
  have hxV : cylinderToSphere (L.curve 0 t) ∈ V := by
    change L.curve 0 t ∈ cylinderToSphere ⁻¹' V
    rw [hVN]
    exact ⟨hxN, hxN₀⟩
  obtain ⟨r, hr, hr1, hrV⟩ := exists_ray_mem_of_open hst.polar hΨ (z d) hV hxV
  -- the ray point is over a point `c` of `f`
  have hrf := hst.ray_mem_edge hγ hΨ hd hr hr1
  rw [hdf] at hrf
  obtain ⟨c, hcf, hcr⟩ := hrf
  have hcNN : c ∈ N ∩ N₀ := by
    have hcV : cylinderToSphere c ∈ V := hcr ▸ hrV
    rw [← hVN]
    exact hcV
  obtain ⟨hs1, hs2⟩ := hray d hd f hf hfP hdf r hr hr1
  -- a lift of `c` on the side of `d`
  obtain ⟨q, ⟨p, hpD, rfl⟩, hqc, hqU⟩ : OnSide D (if left then U₁ else U₂) c := by
    cases left
    · have hnot : ¬ OnSide D U₁ c := fun h =>
        (hs2 (fun h' => by simp at hside; exact absurd h' hside)) ⟨c, hcr, h⟩
      obtain ⟨p, hp⟩ := surjective_single_strip_projection L hG hθ hD hBd hstrip c
      have hp' : cylinderCoverProjection (planeToCylinderCover p.1) = c := hp
      have hq := hN₀lift (planeToCylinderCover p.1) ⟨p.1, p.2, rfl⟩ (by
        rw [hp']; exact hcNN.2)
      rcases hq with hq | hq
      · exact absurd ⟨_, ⟨p.1, p.2, rfl⟩, hp', hq⟩ hnot
      · exact ⟨_, ⟨p.1, p.2, rfl⟩, hp', hq⟩
    · obtain ⟨c', hc', hside1⟩ := hs1 (hside.mpr rfl)
      rw [← hcr] at hc'
      rw [injective_cylinderToSphere hc'] at hside1
      exact hside1
  have hqW := hNlift _ ⟨p, hpD, rfl⟩ (by rw [hqc]; exact hcNN.1) hqU
  refine ⟨⟨p, hpD⟩, (hOW ⟨p, hpD⟩).mpr hqW, ?_⟩
  change cylinderCoverProjection (planeToCylinderCover p) ∈ f
  rw [hqc]
  exact hcf

include hθ hD hstrip hU₁ hU₂ hU h₁ h₂ hGH hγ in
/-- **Every end of the lift of an edge over `P₁(t)` is the lift of the side of one of its darts.**
Let `f` be an edge of `G` off `P₁`, and `p` a point of the closure of the points of `D` over `f`,
with projection `P₁(t)`. If the rays at `P₁(t)` are on the sides named by `side`, then some dart
`d` of `f` at `P₁(t)` has `p` on `Γ₁` when `side d`, and on `Γ₂` otherwise. -/
theorem exists_dart_of_mem_closure_of_raySides {t : I}
    {side : DrawingDart (cylinderSphereDrawing H) → Prop}
    (hrs : RaySides L D U₁ γ R t side) {f : Set ClosedCylinder} (hf : f ∈ G.E)
    (hfP : f ∉ (L.pathDrawing 0).E) {p : D} (hp : p ∈ closure (cutProj D ⁻¹' f))
    (hpx : cutProj D p = L.curve 0 t) :
    ∃ d : DrawingDart (cylinderSphereDrawing H),
      dartVertex γ d = cylinderToSphere (L.curve 0 t) ∧ d.1.1 = cylinderToSphere '' f ∧
      (side d → p = cutSidePoint L hG hBd true t) ∧
      (¬ side d → p = cutSidePoint L hG hBd false t) := by
  obtain ⟨Φ, Ψ, z, hst, hΨ, hray⟩ := hrs
  have hfS : cylinderToSphere '' f ∈ (cylinderSphereDrawing H).E := by
    rw [cylinderSphereDrawing_E]
    exact mem_image_of_mem _ (hGH.2 hf)
  have hfP' : Disjoint f (L.pathDrawing 0).U :=
    deleted_edge_disjoint_subdrawing (L.isSubdrawing 0).1 hf hfP
  have hfV : ∀ c ∈ f, c ∉ G.V := fun c hc => (hf.2.1 hc).2
  -- points of `f` in the star lie on a ray of a dart of `f`
  have honray : ∀ c ∈ f, cylinderToSphere c ∈ range Φ →
      ∃ d, dartVertex γ d = cylinderToSphere (L.curve 0 t) ∧ d.1.1 = cylinderToSphere '' f ∧
        ∃ r : ℝ, 0 < r ∧ r ≤ 1 ∧ cylinderToSphere c = toSph (chartC Ψ ((r : ℂ) * z d)) := by
    intro c hc hcΦ
    have hcx : cylinderToSphere c ≠ cylinderToSphere (L.curve 0 t) := by
      intro h
      rw [injective_cylinderToSphere h] at hc
      exact disjoint_left.mp hfP' hc ((L.curve_parametrizes 0).2.1 ▸ mem_range_self t)
    obtain ⟨r, hr, hr1, u, hu⟩ := exists_chart_polar hst.polar hΨ hcΦ hcx
    have hcU : cylinderToSphere c ∈ (cylinderSphereDrawing H).U := by
      rw [cylinderSphereDrawing_U]
      exact mem_image_of_mem _ (hGH.U_subset (hf.2.1 hc).1)
    rw [hu] at hcU
    have hrim := (chart_ray_mem_iff hst.polar hΨ (isGammaNice_U _) u hr hr1).mp hcU
    have hudir : u ∈ rimDirs (cylinderSphereDrawing H) Φ := hrim
    rw [hst.rimDirs_eq hγ] at hudir
    obtain ⟨d, hd, rfl⟩ := hudir
    have hdray := hst.ray_mem_edge hγ hΨ hd hr hr1
    have hde : d.1.1 = cylinderToSphere '' f :=
      (cylinderSphereDrawing H).edge_eq_of_mem d.2 hfS hdray
        (hu ▸ mem_image_of_mem _ hc)
    exact ⟨d, hd, hde, r, hr, hr1, hu⟩
  have hpt : p.1 = liftedLinkageCurve hG.1 L 1 t ∨ p.1 = liftedLinkageCurve hG.1 L 2 t :=
    eq_lift_of_proj_eq_curve L hG hθ hD hBd hstrip p.2 hpx
  by_contra hno
  -- the open set of lifts near `p` over the star, on the side of `p`
  have hside : ∃ U : Set CylinderCover, IsOpen U ∧ planeToCylinderCover p.1 ∈ U ∧
      ∀ c ∈ f, cylinderToSphere c ∈ range Φ → OnSide D U c → False := by
    rcases hpt with h1 | h2
    · refine ⟨U₁, hU₁, by rw [h1]; exact h₁ t, fun c hc hcΦ hcU => ?_⟩
      obtain ⟨d, hd, hdf, r, hr, hr1, hcr⟩ := honray c hc hcΦ
      have hnd : ¬ side d := fun hs =>
        hno ⟨d, hd, hdf, fun _ => Subtype.ext h1, fun hs' => absurd hs hs'⟩
      exact (hray d hd f hf hfP hdf r hr hr1).2 hnd ⟨c, hcr, hcU⟩
    · refine ⟨U₂, hU₂, by rw [h2]; exact h₂ t, fun c hc hcΦ hcU => ?_⟩
      obtain ⟨d, hd, hdf, r, hr, hr1, hcr⟩ := honray c hc hcΦ
      have hsd : side d := by
        by_contra hs
        exact hno ⟨d, hd, hdf, fun hs' => absurd hs' hs, fun _ => Subtype.ext h2⟩
      obtain ⟨c', hc', h1⟩ := (hray d hd f hf hfP hdf r hr hr1).1 hsd
      rw [← hcr] at hc'
      rw [injective_cylinderToSphere hc'] at h1
      exact not_onSide_two_of_onSide_one L hG hθ hD hBd hstrip hU₁ hU₂ hU h₁ h₂
        (disjoint_left.mp hfP' hc) h1 hcU
  obtain ⟨U, hU', hpU, hcontra⟩ := hside
  set W : Set CylinderCover := U ∩ (fun q => cylinderToSphere (cylinderCoverProjection q)) ⁻¹'
    interior (range Φ)
  have hWo : IsOpen W := hU'.inter (isOpen_interior.preimage
    (continuous_cylinderToSphere.comp continuous_cylinderCoverProjection))
  have hpW : planeToCylinderCover p.1 ∈ W := by
    refine ⟨hpU, ?_⟩
    simp only [mem_preimage]
    change cylinderToSphere (cutProj D p) ∈ interior (range Φ)
    rw [hpx]
    exact hst.polar.nhd
  set O : Set D := {p' | planeToCylinderCover p'.1 ∈ W}
  have hO : IsOpen O := hWo.preimage (continuous_planeToCylinderCover.comp continuous_subtype_val)
  obtain ⟨p', hp'O, hp'f⟩ := (mem_closure_iff.mp hp) O hO hpW
  exact hcontra (cutProj D p') hp'f (interior_subset hp'O.2)
    ⟨planeToCylinderCover p'.1, ⟨p'.1, p'.2, rfl⟩, rfl, hp'O.1⟩

end RaySides

end GraphMinor.GM06
