module

public import GraphMinor.GM06.Alg57OnePathRaySides
public import GraphMinor.GM06.Alg57OnePathDarts

/-!
# The sides of the rays at an inner vertex of the one path

Let `x = P₁(t)` be a vertex of `P₁` other than its ends, with `b` the dart of `P₁` at `x` going
forward and `a` the dart going backward. In a small path chart at `x` the left wedge, from the
direction of `b` counterclockwise to that of `a`, is on side one (`left_side_one`), and the right
wedge is not (`right_wedge_not_sideOne`). The darts of the block `b, R.rot b, …` before `a` point
into the left wedge (`IsCcwStar.arc_iff_block`). So the rays at `x` are on the sides named by
this block: `raySides_inner`.
-/

@[expose] public section

namespace GraphMinor.GM06

open Set Topology GraphMinor.Surface GraphMinor.GM11 unitInterval

variable {G : Drawing ClosedCylinder} {θ : ℝ} {D : Set (ℝ × ℝ)}
  (L : CylinderLinkage 1 G) (hG : IsCylinderSection5Drawing 1 G) (hθ : L.HasTheta θ)
  (hD : IsClosedDisc D) (hBd : discBd D = liftedStripBoundary hG.1 L 1)
  (hstrip : D ⊆ {p : ℝ × ℝ | 1 ≤ p.1 ∧ p.1 ≤ 2})
  {U₁ U₂ : Set CylinderCover} (hU₁ : IsOpen U₁) (hU₂ : IsOpen U₂) (hU : Disjoint U₁ U₂)
  (h₁ : ∀ t, coverLift L hG 1 t ∈ U₁) (h₂ : ∀ t, coverLift L hG 2 t ∈ U₂)
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
  (hV : ∀ v ∈ (cylinderSphereDrawing H).V, ∃ a : DrawingDart (cylinderSphereDrawing H),
    dartVertex γ a = v)

/-- A dart along an edge off `P₁` is not a dart along `P₁`. -/
theorem dart_ne_of_off_path {d c : DrawingDart (cylinderSphereDrawing H)}
    {f : Set ClosedCylinder} (hf : f ∈ G.E) (hfP : f ∉ (L.pathDrawing 0).E)
    (hdf : d.1.1 = cylinderToSphere '' f) (hcX : c.1.1 ⊆ cylinderToSphere '' (L.pathDrawing 0).U) :
    d ≠ c := by
  rintro rfl
  obtain ⟨y, hy⟩ := hf.2.2.1.nonempty
  have hdisj := deleted_edge_disjoint_subdrawing (L.isSubdrawing 0).1 hf hfP
  obtain ⟨y', hy', he⟩ := hcX (hdf ▸ mem_image_of_mem cylinderToSphere hy)
  rw [injective_cylinderToSphere he] at hy'
  exact disjoint_left.mp hdisj hy hy'

include hθ hD hBd hstrip hU₁ hU₂ hU h₁ h₂ hGH hFU hFV hγ hR hccw heI hγI hV in
/-- **The sides of the rays at an inner vertex of `P₁`.** At `x = P₁(t)`, with `b` the forward
and `a` the backward dart of `P₁`, the rays are on side one exactly for the darts of the block
`b, R.rot b, …` before `a`. -/
theorem raySides_inner {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1)
    {a b : DrawingDart (cylinderSphereDrawing H)}
    (hb : dartVertex γ b = spherePath L t) (hbX : b.1.1 ⊆ cylinderToSphere '' (L.pathDrawing 0).U)
    {t₁ : ℝ} (ht₁ : t₁ ∈ Icc (0 : ℝ) 1) (htt₁ : t < t₁)
    (hb1 : dartVertex γ (dartFlip _ b) = spherePath L t₁)
    (ha : dartVertex γ a = spherePath L t) (haX : a.1.1 ⊆ cylinderToSphere '' (L.pathDrawing 0).U)
    {t₂ : ℝ} (ht₂ : t₂ ∈ Icc (0 : ℝ) 1) (htt₂ : t₂ < t)
    (ha1 : dartVertex γ (dartFlip _ a) = spherePath L t₂) :
    RaySides L D U₁ γ R ⟨t, Ioo_subset_Icc_self ht⟩
      (fun d => ∃ i, (∀ j ≤ i, R.rot^[j] b ≠ a) ∧ R.rot^[i] b = d) := by
  have hS : IsClosedSurface (OnePoint EuclideanPlane) :=
    (GM11.IsSphere.isClosedSurface (S := OnePoint EuclideanPlane) ⟨Homeomorph.refl _⟩).1
  have hX := isGammaNice_spherePath L hGH
  have hXf := (image_spherePath L).symm
  have hf := continuous_spherePath L
  have hinj := injOn_spherePath L
  set tt : unitInterval := ⟨t, Ioo_subset_Icc_self ht⟩
  have h0 : tt ≠ 0 := fun h => ht.1.ne' (congrArg Subtype.val h)
  have h1 : tt ≠ 1 := fun h => ht.2.ne (congrArg Subtype.val h)
  have hxt : spherePath L t = cylinderToSphere (L.curve 0 tt) :=
    spherePath_of_mem L (Ioo_subset_Icc_self ht)
  obtain ⟨N, hN, hxN, hdich, -⟩ :=
    sphere_sideDich' L hG hθ hD hBd hstrip hU₁ hU₂ hU h₁ h₂ h0 h1
  rw [← hxt] at hxN
  obtain ⟨O₂, hO₂, hxO₂, hsmall⟩ := exists_isPathChart_of_small hX (spherePath_subset_U L hGH) hf
    hinj (image_spherePath L).subset (image_spherePath L).symm.subset ht
  obtain ⟨Φ₀, z, hst₀⟩ := hccw (spherePath L t) ⟨b, hb⟩
  obtain ⟨Φ, hst, hsub⟩ := hst₀.exists_small hS (hN.inter hO₂) ⟨hxN, hxO₂⟩
  obtain ⟨Ψ, hΨ, hw⟩ := hst.pos
  have hpos : 0 < wind (fun w : Circle => chartC Ψ w) (chartC Ψ 0) := by
    rw [wind_chartC]; exact hw
  obtain ⟨F, B, hc⟩ := hsmall hst.polar hΨ hpos (hst.rimDirs_finite hγ)
    (hsub.trans inter_subset_right)
  have hzb : z b = F := (hst.dir_eq hγ hc ht hX hf hinj hXf hb hbX ht₁ hb1).1 htt₁
  have hza : z a = B := (hst.dir_eq hγ hc ht hX hf hinj hXf ha haX ht₂ ha1).2 htt₂
  have hab : b ≠ a := by
    rintro rfl
    exact hc.ne (hzb.symm.trans hza)
  have hND : SideDich (cylinderToSphere '' (L.pathDrawing 0).U) (sphereSide D U₁) (range Φ) :=
    hdich.mono (hsub.trans inter_subset_left)
  have hleft := (left_side_one L hG hθ hD hBd hstrip hU₁ hU₂ hU h₁ h₂ hGH hFU hFV hγ hR hccw heI
    hγI hV).1 ht hc hND
  have hright := right_wedge_not_sideOne L hG hθ hD hBd hstrip hU₁ hU₂ hU h₁ h₂ hGH hFU hFV hγ hR
    hccw heI hγI hV ht hc hND
  refine ⟨Φ, Ψ, z, hxt ▸ hst, hΨ, fun d hd f hf hfP hdf r hr hr1 => ?_⟩
  rw [← hxt] at hd
  have hdb : z d ≠ F := fun h =>
    dart_ne_of_off_path L hf hfP hdf hbX (hst.inj _ _ hd hb (h.trans hzb.symm))
  have hda : z d ≠ B := fun h =>
    dart_ne_of_off_path L hf hfP hdf haX (hst.inj _ _ hd ha (h.trans hza.symm))
  have hiff := hst.arc_iff_block hγ hR ha hb hd hab
  rw [hzb, hza] at hiff
  constructor
  · intro hs
    rcases hiff.mpr hs with h | h
    · exact absurd h hdb
    · exact hleft _ (mem_wedgeSet_of_lt hr hr1 h)
  · intro hs
    rcases right_of_not_left hc.ne (fun h => hs (hiff.mp h)) with h | h
    · exact absurd h hda
    · exact hright _ (mem_wedgeSet_of_lt hr hr1 h)

end GraphMinor.GM06
