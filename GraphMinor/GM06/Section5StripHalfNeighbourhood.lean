module

public import GraphMinor.Surface.Defs
import GraphMinor.GM06.Section5DiscBoundaryGerm
import GraphMinor.GM16.RectangularDisc
import GraphMinor.Surface.PlaneOrientation

/-!
# A half-neighbourhood at the bottom of a strip disc

For the adjacent-strip argument in VI (5.1), page 129, a closed disc
in the radial strip whose boundary near a point lies on the bottom
cuff fills a half-neighbourhood there. Enclose the compact disc in a
rectangle and apply the local boundary comparison. Near the chosen
point the rectangle agrees with the radial strip.
-/

public section
namespace GraphMinor.GM06
open Set Topology GraphMinor.Surface

/-- A closed disc in the radial strip fills the strip near a bottom
boundary point if no other disc boundary approaches that point. -/
theorem exists_strip_half_neighbourhood_of_boundary_germ
    {Q N : Set (ℝ × ℝ)} {c : ℝ × ℝ} (hQ : IsClosedDisc Q)
    (hstrip : Q ⊆ {p : ℝ × ℝ | 1 ≤ p.1 ∧ p.1 ≤ 2}) (hcQ : c ∈ Q)
    (hN : IsOpen N) (hcN : c ∈ N)
    (hbd : N ∩ discBd Q ⊆ {p : ℝ × ℝ | p.1 = 1}) :
    ∃ O : Set (ℝ × ℝ), IsOpen O ∧ c ∈ O ∧
      {p : ℝ × ℝ | 1 ≤ p.1 ∧ p.1 ≤ 2} ∩ O ⊆ Q := by
  obtain ⟨a, ha⟩ := hQ.isCompact.bddBelow_image continuous_snd.continuousOn
  obtain ⟨b, hb⟩ := hQ.isCompact.bddAbove_image continuous_snd.continuousOn
  have haQ : ∀ p ∈ Q, a ≤ p.2 := fun p hp => ha (mem_image_of_mem Prod.snd hp)
  have hbQ : ∀ p ∈ Q, p.2 ≤ b := fun p hp => hb (mem_image_of_mem Prod.snd hp)
  have hab : a - 1 < b + 1 := by linarith only [haQ c hcQ, hbQ c hcQ]
  let R := Icc (1 : ℝ) 2 ×ˢ Icc (a - 1) (b + 1)
  obtain ⟨hR, hRb⟩ := GM16.isClosedDisc_real_rectangle_with_boundary (by norm_num : (1 : ℝ) < 2) hab
  have hQR : Q ⊆ R := by
    intro p hp
    refine ⟨hstrip hp, ?_, ?_⟩
    · linarith only [haQ p hp]
    · linarith only [hbQ p hp]
  have hbdR : N ∩ discBd Q ⊆ discBd R := by
    intro p hp
    have hp1 : p.1 = 1 := hbd hp
    rw [hRb]
    constructor
    · exact subset_closure (hQR (discBd_subset Q hp.2))
    · intro hpint
      rw [interior_prod_eq, interior_Icc, interior_Icc] at hpint
      have hlt : 1 < p.1 := hpint.1.1
      rw [hp1] at hlt
      exact lt_irrefl _ hlt
  have hman (p : ℝ × ℝ) : IsManifoldPoint p := by
    let e : ℂ ≃ₜ (ℝ × ℝ) := Complex.equivRealProdCLM.toHomeomorph
    have hh := isManifoldPoint_of_isOpenEmbedding e.isOpenEmbedding
      (isManifoldPoint_complex (e.symm p))
    simpa only [e.apply_symm_apply] using hh
  obtain ⟨V, hV, hcV, hRV⟩ := exists_nhds_nested_disc_of_boundary_germ hman hR hQ hQR hcQ hN hcN hbdR
  let A := {p : ℝ × ℝ | a - 1 < p.2 ∧ p.2 < b + 1}
  have hA : IsOpen A := (isOpen_lt continuous_const continuous_snd).inter
    (isOpen_lt continuous_snd continuous_const)
  have hcA : c ∈ A := by constructor <;> linarith only [haQ c hcQ, hbQ c hcQ]
  refine ⟨V ∩ A, hV.inter hA, ⟨hcV, hcA⟩, ?_⟩
  rintro p ⟨hpstrip, hpV, hpA⟩
  exact hRV ⟨⟨hpstrip, hpA.1.le, hpA.2.le⟩, hpV⟩

end GraphMinor.GM06
