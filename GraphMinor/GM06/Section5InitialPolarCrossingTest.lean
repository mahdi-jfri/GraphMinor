module

public import GraphMinor.GM06.Section5CapDrawing
public import GraphMinor.GM06.Section5PolarRay
public import GraphMinor.GM11.LocalCone
public import GraphMinor.GM06.Section2Dual
public import GraphMinor.Surface.DiscGrow
import GraphMinor.GM06.Section5ClockwisePolarCrossing
import GraphMinor.GM06.Section5ClockwiseSideFrontier
import GraphMinor.GM06.Section5CoverLocalHomeomorph
import GraphMinor.GM06.Section5InitialPolarBarrier
import GraphMinor.GM06.Section5InitialCuffHalfArcs
import GraphMinor.GM06.Section5CuffPolar
import GraphMinor.GM06.Section5PolarCuffSides
import GraphMinor.GM06.Section5PolarSubdrawingEnds

/-!
# A geometric crossing test for the corrected clockwise reduction

For VI (5.7), page 133, construct the local inverse cover chart,
its closed clockwise side, and a polar chart with the three
linkage-and-cuff directions. The increasing-angle cuff direction
lies outside that side. The proved local crossing criterion then
recognizes every clockwise edge using the rim order. All charts
and side properties are constructed from the Section 5 drawing,
also when the linkage has only one path.
-/

public section
namespace GraphMinor.GM06
open Set Topology Real GraphMinor.Surface GraphMinor.GM11 unitInterval

/-- The local crossing test retains its rays on the specified two
cuff arcs, so those directions can be matched with input half-edge labels. -/
theorem exists_initial_polar_clockwise_crossing_test_with_cuff_rays
    {k : ℕ} {G F : Drawing ClosedCylinder} {θ : ℝ}
    (L : CylinderLinkage k G) (hG : IsCylinderSection5Drawing k G)
    (hGF : G.IsSubdrawing F) (hbdF : bd ClosedCylinder ⊆ F.U)
    (hθ : L.HasTheta θ) (i : Fin k)
    (g h : I → ClosedCylinder) (hgh : IsTwoArcs g h)
    (hg0 : g 0 = cylinderM1Point k i) (hcover : range g ∪ range h = cylinderCuff1)
    (hhAngle : ∀ t : I, h t = cylinderPoint 1 (by norm_num)
      ((cylinderInitialLift k i).2 + π * (t : ℝ)))
    {Φ : C(ClosedUnitDisc, OnePoint EuclideanPlane)}
    (hp : IsPolar (cylinderSphereDrawing F) (cylinderToSphere (cylinderM1Point k i)) Φ)
    {A : Set (OnePoint EuclideanPlane)} (hAo : IsOpen A)
    (hsA : cylinderToSphere (cylinderM1Point k i) ∈ A) :
    ∃ Ψ : C(ClosedUnitDisc, OnePoint EuclideanPlane),
      IsPolar (cylinderSphereDrawing F) (cylinderToSphere (cylinderM1Point k i)) Ψ ∧
      range Ψ ⊆ A ∧
      (∃ a : I, (0 : ℝ) < a ∧ ∀ x, Ψ x = Φ (discScale a x)) ∧
      ∃ p q c : Circle, p ≠ q ∧ p ≠ c ∧ q ≠ c ∧
        range (polarRayMap Ψ p) ⊆ range (cylinderToSphere ∘ g) ∧
        range (polarRayMap Ψ c) ⊆ range (cylinderToSphere ∘ h) ∧
        polarRimMap Ψ p ∈ cylinderToSphere '' cylinderCuff1 ∧
        polarRimMap Ψ c ∈ cylinderToSphere '' cylinderCuff1 ∧
        polarRimMap Ψ q ∈ (cylinderSphereDrawing (L.pathDrawing i)).U ∧
        ∀ e ∈ G.E, Disjoint e (⋃ j, (L.pathDrawing j).U) →
          (IsClockwiseInitialEdge L i e ↔ ∃ w : Circle,
            polarRimMap Ψ w ∈ cylinderToSphere '' e ∧ CrossesOn (univ : Set Circle) p q w c) := by
  obtain ⟨η, hsη, hηraw⟩ := isLocalHomeomorph_cylinderCoverProjection (cylinderInitialLift k i)
  have hη : (η : CylinderCover → ClosedCylinder) = cylinderCoverProjection := hηraw.symm
  obtain ⟨B, O, hB, hOo, hsO, _, hmem, hfr⟩ :=
    exists_closed_local_clockwise_side_with_frontier L hG hθ i η hη hsη
  have hg0' : g 0 = cylinderM1Point k i := hg0
  obtain ⟨Ψ, hΨ, hΨOA, hscale, p, q, c, hpq, hpc, hqc, hpg, hch, hqP, hbar⟩ :=
    exists_initial_polar_barrier_directions L hG hGF hbdF i g h hgh hg0' hcover hp
      (hOo.inter hAo) ⟨hsO, hsA⟩
  have hΨO : range Ψ ⊆ O := fun y hy => (hΨOA hy).1
  have hsmall (y : ClosedCylinder) (hyΦ : cylinderToSphere y ∈ range Ψ) : y ∈ η.target :=
    (hmem y (hΨO hyΦ)).1
  obtain ⟨y, hcy, hyOutside⟩ := polar_positive_cuff_direction_not_mem_preceding_strip
    L hG hθ i hΨ h hgh.arc_right (hgh.zero.trans hg0') π pi_pos hhAngle c hch η hη hsη hsmall
  have hyCuff : y ∈ cylinderCuff1 := by
    obtain ⟨r, hr⟩ := hch (mem_range_self 1)
    have hry : h r = y := injective_cylinderToSphere (hr.trans hcy)
    have hrCuff : h r ∈ cylinderCuff1 := hcover ▸ Or.inr (mem_range_self r)
    exact hry ▸ hrCuff
  have hyOff : y ∉ ⋃ j, (L.pathDrawing j).U := by
    intro hyL
    obtain ⟨j, hyj⟩ := mem_iUnion.mp hyL
    have hyBd : y ∈ bd ClosedCylinder := by rw [bd_closedCylinder]; exact Or.inl hyCuff
    have hyV : y ∈ G.V := hG.2.1 ⟨hyBd, (L.isSubdrawing j).2 hyj⟩
    have hyVF : cylinderToSphere y ∈ (cylinderSphereDrawing F).V := by
      rw [cylinderSphereDrawing_V]
      exact ⟨y, hGF.1 hyV, rfl⟩
    exact polar_rim_not_mem_vertices hΨ c (hcy.symm ▸ hyVF)
  have hcB : polarRimMap Ψ c ∉ B := by
    intro hcBin
    have hyB : cylinderToSphere y ∈ B := hcy ▸ hcBin
    have hyΦ : cylinderToSphere y ∈ range Ψ := hcy ▸ mem_range_self (polarDiscPoint 1 c)
    exact hyOutside (((hmem y (hΨO hyΦ)).2 hyOff).mp hyB)
  have hCuff (w : Circle) (f : I → ClosedCylinder)
      (hf : range (polarRayMap Ψ w) ⊆ range (cylinderToSphere ∘ f))
      (hfC : range f ⊆ cylinderCuff1) : polarRimMap Ψ w ∈ cylinderToSphere '' cylinderCuff1 := by
    obtain ⟨r, hr⟩ := hf (mem_range_self 1)
    exact ⟨f r, hfC (mem_range_self r), hr⟩
  have hpC := hCuff p g hpg (fun y hy => hcover ▸ Or.inl hy)
  have hcC := hCuff c h hch (fun y hy => hcover ▸ Or.inr hy)
  refine ⟨Ψ, hΨ, fun y hy => (hΨOA hy).2, hscale, p, q, c, hpq, hpc, hqc, hpg, hch, hpC, hcC, hqP, ?_⟩
  intro e he hoff
  exact clockwise_edge_iff_polar_crossing_of_local_side L hG hGF hbdF hθ i η hη hsη
    hΨ hB hOo hsO hΨO hmem hfr p q c hpq hpc hqc hbar hcB he hoff

/-- Arbitrarily small initial polar charts give a four-point
crossing test for the corrected clockwise edge condition. -/
theorem exists_initial_polar_clockwise_crossing_test
    {k : ℕ} {G F : Drawing ClosedCylinder} {θ : ℝ}
    (L : CylinderLinkage k G) (hG : IsCylinderSection5Drawing k G)
    (hGF : G.IsSubdrawing F) (hbdF : bd ClosedCylinder ⊆ F.U)
    (hθ : L.HasTheta θ) (i : Fin k)
    {Φ : C(ClosedUnitDisc, OnePoint EuclideanPlane)}
    (hp : IsPolar (cylinderSphereDrawing F) (cylinderToSphere (cylinderM1Point k i)) Φ)
    {A : Set (OnePoint EuclideanPlane)} (hAo : IsOpen A)
    (hsA : cylinderToSphere (cylinderM1Point k i) ∈ A) :
    ∃ Ψ : C(ClosedUnitDisc, OnePoint EuclideanPlane),
      IsPolar (cylinderSphereDrawing F) (cylinderToSphere (cylinderM1Point k i)) Ψ ∧
      range Ψ ⊆ A ∧
      (∃ a : I, (0 : ℝ) < a ∧ ∀ x, Ψ x = Φ (discScale a x)) ∧
      ∃ p q c : Circle, p ≠ q ∧ p ≠ c ∧ q ≠ c ∧
        polarRimMap Ψ p ∈ cylinderToSphere '' cylinderCuff1 ∧
        polarRimMap Ψ c ∈ cylinderToSphere '' cylinderCuff1 ∧
        polarRimMap Ψ q ∈ (cylinderSphereDrawing (L.pathDrawing i)).U ∧
        ∀ e ∈ G.E, Disjoint e (⋃ j, (L.pathDrawing j).U) →
          (IsClockwiseInitialEdge L i e ↔ ∃ w : Circle,
            polarRimMap Ψ w ∈ cylinderToSphere '' e ∧ CrossesOn (univ : Set Circle) p q w c) := by
  obtain ⟨g, h, hgh, hg0, hcover, _, hhAngle⟩ :=
    exists_initial_cuff_half_arcs (cylinderInitialLift k i).2
  obtain ⟨Ψ, hΨ, hΨA, hscale, p, q, c, hpq, hpc, hqc, _, _, hpC, hcC, hqP, htest⟩ :=
    exists_initial_polar_clockwise_crossing_test_with_cuff_rays L hG hGF hbdF hθ i
      g h hgh (hg0.trans (by rfl)) hcover hhAngle hp hAo hsA
  exact ⟨Ψ, hΨ, hΨA, hscale, p, q, c, hpq, hpc, hqc, hpC, hcC, hqP, htest⟩

end GraphMinor.GM06
