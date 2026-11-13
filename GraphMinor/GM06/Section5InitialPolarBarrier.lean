module

public import GraphMinor.GM06.Section5CapDrawing
public import GraphMinor.GM06.Section5PolarThreeBarrierDirections
import GraphMinor.GM06.Section5CappedInitialPath
import GraphMinor.GM06.Section5CappedCuffSubdrawings
import GraphMinor.GM11.Walks

/-!
# The three barrier directions of a Section 5 initial vertex

For VI (5.7), page 133, cap the augmented drawing and choose a
polar chart at the initial vertex. The initial cuff contributes
two directions and its linkage path contributes one. Every other
linkage path and the opposite cuff miss the centre, so the polar
chart misses those subdrawings entirely. The complete linkage-and-
cuff barrier therefore has exactly the three expected directions.
-/

public section
namespace GraphMinor.GM06
open Set Topology GraphMinor.Surface GraphMinor.GM11 unitInterval

/-- The actual Section 5 linkage and cuffs meet a sufficiently small
initial polar rim in exactly three distinct directions. -/
theorem exists_initial_polar_barrier_directions
    {k : ℕ} {G F : Drawing ClosedCylinder} (L : CylinderLinkage k G)
    (hG : IsCylinderSection5Drawing k G) (hGF : G.IsSubdrawing F)
    (hbdF : bd ClosedCylinder ⊆ F.U) (i : Fin k)
    (g h : I → ClosedCylinder) (hgh : IsTwoArcs g h)
    (hg0 : g 0 = cylinderM1Point k i) (hcover : range g ∪ range h = cylinderCuff1)
    {Φ : C(ClosedUnitDisc, OnePoint EuclideanPlane)}
    (hp : IsPolar (cylinderSphereDrawing F) (cylinderToSphere (cylinderM1Point k i)) Φ)
    {O : Set (OnePoint EuclideanPlane)} (hOo : IsOpen O)
    (hsO : cylinderToSphere (cylinderM1Point k i) ∈ O) :
    ∃ Ψ : C(ClosedUnitDisc, OnePoint EuclideanPlane),
      IsPolar (cylinderSphereDrawing F) (cylinderToSphere (cylinderM1Point k i)) Ψ ∧
      range Ψ ⊆ O ∧
      (∃ a : I, (0 : ℝ) < a ∧ ∀ x, Ψ x = Φ (discScale a x)) ∧
      ∃ p q c : Circle, p ≠ q ∧ p ≠ c ∧ q ≠ c ∧
        range (polarRayMap Ψ p) ⊆ range (cylinderToSphere ∘ g) ∧
        range (polarRayMap Ψ c) ⊆ range (cylinderToSphere ∘ h) ∧
        polarRimMap Ψ q ∈ (cylinderSphereDrawing (L.pathDrawing i)).U ∧
        ∀ w : Circle, polarRimMap Ψ w ∈
          cylinderToSphere '' ((⋃ j, (L.pathDrawing j).U) ∪ bd ClosedCylinder) ↔
            w = p ∨ w = q ∨ w = c := by
  have hsph : IsSphere (OnePoint EuclideanPlane) := ⟨Homeomorph.refl _⟩
  have hS := GM11.IsSphere.isClosedSurface hsph
  let : ConnectedSpace (OnePoint EuclideanPlane) := hS.2
  let : LocallyConnectedSpace (OnePoint EuclideanPlane) := IsClosedSurface.locallyConnectedSpace hS.1
  obtain ⟨C₁, C₂, hC₁F, hC₂F, hC₁U, hC₂U, _, _⟩ := exists_capped_cuff_subdrawings F hbdF
  have hPiF := cylinderSphereDrawing_isSubdrawing ((L.isSubdrawing i).1.trans hGF)
  have hfS : ParametrizesSet (cylinderSphereCurve (L.curve i))
      (cylinderSphereDrawing (L.pathDrawing i)).U
      (cylinderToSphere (cylinderM1Point k i)) (cylinderToSphere (L.curve i 1)) := by
    rw [cylinderSphereDrawing_U]
    exact cylinderSphereCurve_parametrizesSet (L.curve_parametrizes i)
  have hcovS : range (cylinderToSphere ∘ g) ∪ range (cylinderToSphere ∘ h) = C₁.U := by
    rw [range_comp, range_comp, ← image_union, hcover, hC₁U]
  have hPC : (cylinderSphereDrawing (L.pathDrawing i)).U ∩ C₁.U =
      {cylinderToSphere (cylinderM1Point k i)} := by
    rw [hC₁U]
    exact L.capped_U_inter_cuff1 hG i
  obtain ⟨Ψ, hΨ, hΨO, hscale, p, q, c, hpq, hpc, hqc, hpg, hch, hqP, hthree⟩ :=
    exists_polar_chart_with_three_barrier_directions hS.1 hPiF hC₁F
      (cylinderSphereCurve (L.curve i)) hfS (cylinderToSphere ∘ g) (cylinderToSphere ∘ h)
      (isTwoArcs_cylinderToSphere hgh) (congrArg cylinderToSphere hg0) hcovS hPC hp hOo hsO
  have hstart : cylinderM1Point k i ∈ (L.pathDrawing i).U := by
    rw [← (L.curve_parametrizes i).2.1]
    exact ⟨0, (L.curve_parametrizes i).2.2.1⟩
  have hmiss (j : Fin k) (hji : j ≠ i) :
      Disjoint (range Ψ) (cylinderSphereDrawing (L.pathDrawing j)).U := by
    apply disjoint_polar_chart_subdrawing_of_centre_not_mem
      (cylinderSphereDrawing_isSubdrawing ((L.isSubdrawing j).1.trans hGF)) hΨ
    rw [cylinderSphereDrawing_U]
    rintro ⟨y, hyj, hys⟩
    have hy : y = cylinderM1Point k i := injective_cylinderToSphere hys
    exact disjoint_left.mp (L.pairwise_disjoint hji) (hy ▸ hyj) hstart
  have hmissC₂ : Disjoint (range Ψ) C₂.U := by
    apply disjoint_polar_chart_subdrawing_of_centre_not_mem hC₂F hΨ
    rw [hC₂U]
    rintro ⟨y, hyC, hys⟩
    have hy : y = cylinderM1Point k i := injective_cylinderToSphere hys
    exact disjoint_left.mp disjoint_cylinderCuffs
      (show cylinderM1Point k i ∈ cylinderCuff1 from rfl) (hy ▸ hyC)
  refine ⟨Ψ, hΨ, hΨO, hscale, p, q, c, hpq, hpc, hqc, hpg, hch, hqP, ?_⟩
  intro w
  have hbar : polarRimMap Ψ w ∈ cylinderToSphere '' ((⋃ j, (L.pathDrawing j).U) ∪ bd ClosedCylinder) ↔
      polarRimMap Ψ w ∈ (cylinderSphereDrawing (L.pathDrawing i)).U ∪ C₁.U := by
    constructor
    · rintro ⟨y, hyL | hyBd, hyw⟩
      · obtain ⟨j, hyj⟩ := mem_iUnion.mp hyL
        by_cases hji : j = i
        · subst j
          left
          rw [cylinderSphereDrawing_U]
          exact ⟨y, hyj, hyw⟩
        · have hwj : polarRimMap Ψ w ∈ (cylinderSphereDrawing (L.pathDrawing j)).U := by
            rw [cylinderSphereDrawing_U]
            exact ⟨y, hyj, hyw⟩
          exact False.elim (disjoint_left.mp (hmiss j hji)
            (mem_range_self (polarDiscPoint 1 w)) hwj)
      · rw [bd_closedCylinder] at hyBd
        rcases hyBd with hy₁ | hy₂
        · right
          rw [hC₁U]
          exact ⟨y, hy₁, hyw⟩
        · have hw₂ : polarRimMap Ψ w ∈ C₂.U := hC₂U.symm ▸ ⟨y, hy₂, hyw⟩
          exact False.elim (disjoint_left.mp hmissC₂ (mem_range_self (polarDiscPoint 1 w)) hw₂)
    · rintro (hwP | hwC)
      · rw [cylinderSphereDrawing_U] at hwP
        obtain ⟨y, hyP, hyw⟩ := hwP
        exact ⟨y, Or.inl (mem_iUnion.mpr ⟨i, hyP⟩), hyw⟩
      · rw [hC₁U] at hwC
        obtain ⟨y, hyC, hyw⟩ := hwC
        refine ⟨y, Or.inr ?_, hyw⟩
        rw [bd_closedCylinder]
        exact Or.inl hyC
  exact hbar.trans (hthree w)

end GraphMinor.GM06
