module

public import GraphMinor.GM21.Section6Restrict
import GraphMinor.GM21.Section6Supports
import GraphMinor.GM17.CuffOrder
import GraphMinor.GM06.DiscRegions
import GraphMinor.Surface.DiscArcs
import GraphMinor.Surface.NormalWord
import GraphMinor.Surface.CutIArc
import GraphMinor.Surface.AddCrosscap

/-!
# Graph Minors XXI, Section 6: the two discs cut off by a line

In the proofs of (6.6) and (6.7) of *Graph Minors XXI* (pages 27–28 of the preprint), a proper line
`F` with ends `a, b ∈ V(Γ)` and no other point in `U(Γ)` cuts the disc `Σ` into two closed discs
$\Delta_1, \Delta_2$, "the closed disc bounded by $F \cup J_i$", where $J_1, J_2$ are the two lines
in $bd(\Sigma)$ with ends $a, b$.

This file proves:
* `exists_disc_sides`: the two discs exist and are sides of `F` (`IsSideOfLine`). Reading `bd(Σ)`
  by angles, with the ends of `F` at angles `θx < θy < θx + 2π`, the first disc meets `bd(Σ)` in the
  angles `[θx, θy]` and the second in the angles `[θy, θx + 2π]`. It comes from `disc_iArc`.
* `componentsIn_diff_pair`: a circle without two points has two components, the two open arcs.
  `disc_iArc` gives the two discs, and this lemma says which arc of `bd(Σ)` each one contains.
-/

@[expose] public section

namespace GraphMinor
namespace GM21
namespace Side

open Set Topology Function GraphMinor.Surface GraphMinor.GM19 GraphMinor.GM17
  GraphMinor.GM21.Supports

universe w

variable {S : Type w} [TopologicalSpace S]

/-! ## Angles -/

section Angles

variable {Θ : Set S} (f : Circle ≃ₜ Θ)

/-- The points with angles in `[s, e]` are those with angles in `(s, e)` and the two ends. -/
theorem image_Icc_eq_union {s e : ℝ} (hse : s ≤ e) :
    cuffPoint f '' Icc s e = cuffPoint f '' Ioo s e ∪ {cuffPoint f s, cuffPoint f e} := by
  ext x
  constructor
  · rintro ⟨t, ht, rfl⟩
    rcases eq_or_lt_of_le ht.1 with h | h
    · exact Or.inr (Or.inl (by rw [h]))
    rcases eq_or_lt_of_le ht.2 with h' | h'
    · exact Or.inr (Or.inr (by rw [h']; rfl))
    exact Or.inl ⟨t, ⟨h, h'⟩, rfl⟩
  · rintro (⟨t, ht, rfl⟩ | rfl | rfl)
    · exact ⟨t, Ioo_subset_Icc_self ht, rfl⟩
    · exact ⟨s, ⟨le_rfl, hse⟩, rfl⟩
    · exact ⟨e, ⟨hse, le_rfl⟩, rfl⟩

/-- Removing the points of angles `θx < θy < θx + 2π` from a circle leaves the points with angles
in `(θx, θy)` and those with angles in `(θy, θx + 2π)`. -/
theorem diff_pair_eq {θx θy : ℝ} (hxy : θx < θy) (hyx : θy < θx + 2 * Real.pi) :
    Θ \ {cuffPoint f θx, cuffPoint f θy} =
      cuffPoint f '' Ioo θx θy ∪ cuffPoint f '' Ioo θy (θx + 2 * Real.pi) := by
  have hinj := cuffPoint_injOn_Ico f θx
  have hpi := Real.pi_pos
  have hx : θx ∈ Ico θx (θx + 2 * Real.pi) := ⟨le_rfl, by linarith⟩
  have hy : θy ∈ Ico θx (θx + 2 * Real.pi) := ⟨hxy.le, hyx⟩
  ext z
  constructor
  · rintro ⟨hzΘ, hz⟩
    obtain ⟨t, ht, rfl⟩ := exists_cuffPoint_mem_Ico f θx hzΘ
    have h1 : t ≠ θx := fun h => hz (Or.inl (by rw [h]))
    have h2 : t ≠ θy := fun h => hz (Or.inr (by rw [h]; rfl))
    rcases lt_or_gt_of_ne h2 with h | h
    · exact Or.inl ⟨t, ⟨lt_of_le_of_ne ht.1 h1.symm, h⟩, rfl⟩
    · exact Or.inr ⟨t, ⟨h, ht.2⟩, rfl⟩
  · have key : ∀ t ∈ Ico θx (θx + 2 * Real.pi), t ≠ θx → t ≠ θy →
        cuffPoint f t ∈ Θ \ {cuffPoint f θx, cuffPoint f θy} := by
      intro t ht h1 h2
      refine ⟨cuffPoint_mem f t, ?_⟩
      rintro (h | h)
      · exact h1 (hinj ht hx h)
      · exact h2 (hinj ht hy h)
    rintro (⟨t, ht, rfl⟩ | ⟨t, ht, rfl⟩)
    · exact key t ⟨ht.1.le, by linarith [ht.2]⟩ ht.1.ne' ht.2.ne
    · exact key t ⟨by linarith [ht.1], ht.2⟩ (by linarith [ht.1]) ht.1.ne'

/-- The two components of a circle without the points of angles `θx < θy < θx + 2π`. -/
theorem componentsIn_diff_pair [T2Space S] {θx θy : ℝ} (hxy : θx < θy)
    (hyx : θy < θx + 2 * Real.pi) :
    componentsIn (Θ \ {cuffPoint f θx, cuffPoint f θy}) =
      {cuffPoint f '' Ioo θx θy, cuffPoint f '' Ioo θy (θx + 2 * Real.pi)} := by
  have hinj := cuffPoint_injOn_Ico f θx
  have hpi := Real.pi_pos
  have hcont := cuffPoint_continuous f
  have hcl : ∀ {s e : ℝ}, s ≤ e → e ≤ θx + 2 * Real.pi →
      closure (cuffPoint f '' Ioo s e) ∩ (Θ \ {cuffPoint f θx, cuffPoint f θy}) ⊆
        cuffPoint f '' Ioo s e ∪ {cuffPoint f s, cuffPoint f e} := by
    intro s e hse _ z hz
    rw [← image_Icc_eq_union f hse]
    exact closure_minimal (image_mono Ioo_subset_Icc_self)
      ((isCompact_Icc.image hcont).isClosed) hz.1
  apply Supports.componentsIn_of_pieces (toFinite _)
  · rintro p (rfl | rfl)
    · exact (isConnected_Ioo hxy).image _ hcont.continuousOn
    · exact (isConnected_Ioo hyx).image _ hcont.continuousOn
  · have hdisj : Disjoint (cuffPoint f '' Ioo θx θy)
        (cuffPoint f '' Ioo θy (θx + 2 * Real.pi)) := by
      rw [disjoint_left]
      rintro _ ⟨s, hs, rfl⟩ ⟨t, ht, heq⟩
      have := hinj ⟨by linarith [ht.1], ht.2⟩ ⟨hs.1.le, by linarith [hs.2]⟩ heq
      linarith [hs.2, ht.1]
    rintro p (rfl | rfl) q (rfl | rfl) hne
    · exact (hne rfl).elim
    · exact hdisj
    · exact hdisj.symm
    · exact (hne rfl).elim
  · rintro p (rfl | rfl) z hz
    · rcases hcl hxy.le (by linarith) hz with h | h | h
      · exact h
      · exact (hz.2.2 (Or.inl h)).elim
      · exact (hz.2.2 (Or.inr h)).elim
    · rcases hcl hyx.le le_rfl hz with h | h | h
      · exact h
      · exact (hz.2.2 (Or.inr h)).elim
      · rw [GM17.cuffPoint_add_two_pi] at h
        exact (hz.2.2 (Or.inl h)).elim
  · rw [diff_pair_eq f hxy hyx, sUnion_pair]

end Angles

/-! ## The two discs -/

section Discs

/-- A closed disc is a surface. -/
theorem isSurface_of_isClosedDiscSpace {X : Type w} [TopologicalSpace X]
    (hX : GM06.IsClosedDiscSpace X) : IsSurface X := by
  obtain ⟨d⟩ := nonempty_disc_homeo
  obtain ⟨e⟩ := hX
  exact isSurface_of_homeo (d.trans e) (isSurface_model 0 0 1).1

/-- A closed disc is connected. -/
theorem connectedSpace_of_isClosedDiscSpace {X : Type w} [TopologicalSpace X]
    (hX : GM06.IsClosedDiscSpace X) : ConnectedSpace X := by
  obtain ⟨e⟩ := hX
  have : ConnectedSpace ClosedUnitDisc :=
    Subtype.connectedSpace ((convex_closedBall (0 : EuclideanPlane) 1).isConnected ⟨0, by simp⟩)
  exact e.surjective.connectedSpace e.continuous

/-- **The two discs cut off by a line** (Graph Minors XXI, proofs of (6.6) and (6.7), pages 28–29 of
the preprint): "let $\Delta_i \subseteq \Sigma$ be the closed disc bounded by $F \cup J_i$". Let `F`
be a line in a disc `Σ` whose ends are the vertices at angles `θx < θy < θx + 2π` of `bd(Σ)`, with
no other point in `bd(Σ)` or in `U(Γ)`. Then `F` cuts `Σ` into two closed discs, which are sides of
`F`. The first meets `bd(Σ)` in the points with angles in `[θx, θy]`, and the second in those with
angles in `[θy, θx + 2π]`. -/
theorem exists_disc_sides (hD : GM06.IsClosedDiscSpace S) {Γ : Surface.Drawing S} (f : Circle ≃ₜ bd S)
    {F : Set S} {θx θy : ℝ} (hxy : θx < θy) (hyx : θy < θx + 2 * Real.pi)
    (hF : IsLineWithEnds F (cuffPoint f θx) (cuffPoint f θy))
    (hFbd : F ∩ bd S = {cuffPoint f θx, cuffPoint f θy})
    (hxV : cuffPoint f θx ∈ Γ.V) (hyV : cuffPoint f θy ∈ Γ.V)
    (hFU : F ∩ Γ.U ⊆ {cuffPoint f θx, cuffPoint f θy}) :
    ∃ Δ₁ Δ₂ : Set S, IsSideOfLine Γ Δ₁ Δ₂ F (cuffPoint f θx) (cuffPoint f θy) ∧
      GM06.IsClosedDiscSpace Δ₁ ∧ GM06.IsClosedDiscSpace Δ₂ ∧
      Δ₁ ∩ bd S = cuffPoint f '' Icc θx θy ∧
      Δ₂ ∩ bd S = cuffPoint f '' Icc θy (θx + 2 * Real.pi) := by
  have : T2Space S := GM06.t2Space_of_isClosedDiscSpace hD
  have hpi := Real.pi_pos
  set x := cuffPoint f θx with hx
  set y := cuffPoint f θy with hy
  have hne : x ≠ y := by
    intro h
    have := cuffPoint_injOn_Ico f θx ⟨le_rfl, by linarith⟩ ⟨hxy.le, hyx⟩ h
    linarith
  obtain ⟨A₁, A₂, Δ₁, Δ₂, hA, hcomp, hD₁, hD₂, hun, hint, hbd₁, hbd₂, -⟩ :=
    disc_iArc (univ : Set S) F x y hD.isClosedDisc_univ (subset_univ _) hne hF
      (by rw [GM06.discBd_univ]; exact hFbd)
  rw [GM06.discBd_univ, componentsIn_diff_pair f hxy hyx] at hcomp
  set P := cuffPoint f '' Ioo θx θy
  set Q := cuffPoint f '' Ioo θy (θx + 2 * Real.pi)
  have hPQ : bd S \ {x, y} = P ∪ Q := diff_pair_eq f hxy hyx
  have hPbd : P ⊆ bd S := fun z hz => (hPQ ▸ Or.inl hz : z ∈ bd S \ {x, y}).1
  have hQbd : Q ⊆ bd S := fun z hz => (hPQ ▸ Or.inr hz : z ∈ bd S \ {x, y}).1
  have hdiscBd : ∀ D : Set S, discBd D ⊆ D := by
    rintro D _ ⟨z, -, rfl⟩
    exact z.2
  -- A side meets `bd(Σ)` in its arc and the ends of `F`.
  have hside : ∀ {D D' A A' : Set S}, D ∩ D' = F → discBd D = A ∪ F → discBd D' = A' ∪ F →
      bd S \ {x, y} ⊆ A ∪ A' → A ⊆ bd S → D ∩ bd S = A ∪ {x, y} := by
    intro D D' A A' hDD' hbdD hbdD' hcov hAbd
    have hFD : F ⊆ D := hDD' ▸ inter_subset_left
    ext z
    constructor
    · rintro ⟨hzD, hzbd⟩
      by_cases hz : z ∈ ({x, y} : Set S)
      · exact Or.inr hz
      rcases hcov ⟨hzbd, hz⟩ with h | h
      · exact Or.inl h
      · have hzD' : z ∈ D' := hdiscBd D' (hbdD' ▸ Or.inl h)
        have hzF : z ∈ F := hDD' ▸ ⟨hzD, hzD'⟩
        exact (hz (hFbd ▸ ⟨hzF, hzbd⟩)).elim
    · rintro (h | h)
      · exact ⟨hdiscBd D (hbdD ▸ Or.inl h), hAbd h⟩
      · have hzF : z ∈ F ∩ bd S := hFbd ▸ h
        exact ⟨hFD hzF.1, hzF.2⟩
  have hmk : ∀ {D D' : Set S}, IsClosedDisc D → IsClosedDisc D' → D ∪ D' = univ → D ∩ D' = F →
      IsSideOfLine Γ D D' F x y := by
    intro D D' hD hD' hu hi
    refine ⟨isSurface_of_isClosedDiscSpace hD, isSurface_of_isClosedDiscSpace hD', hu, hi,
      ⟨hF, ?_, ?_, ?_⟩, hxV, hyV, hFU⟩
    · exact (hFbd.symm ▸ Or.inl rfl : x ∈ F ∩ bd S).2
    · exact (hFbd.symm ▸ Or.inr rfl : y ∈ F ∩ bd S).2
    · rw [disjoint_left]
      rintro z ⟨hzF, hz⟩ hzbd
      exact hz (hFbd ▸ ⟨hzF, hzbd⟩)
  have hIccP : P ∪ {x, y} = cuffPoint f '' Icc θx θy := (image_Icc_eq_union f hxy.le).symm
  have hIccQ : Q ∪ {x, y} = cuffPoint f '' Icc θy (θx + 2 * Real.pi) := by
    rw [image_Icc_eq_union f hyx.le, GM17.cuffPoint_add_two_pi, pair_comm]
  rcases pair_eq_pair_iff.mp hcomp with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · refine ⟨Δ₁, Δ₂, hmk hD₁ hD₂ hun hint, hD₁, hD₂, ?_, ?_⟩
    · rw [hside hint hbd₁ hbd₂ hPQ.subset hPbd, hIccP]
    · rw [hside (by rw [inter_comm]; exact hint) hbd₂ hbd₁ (hPQ ▸ by
        rw [union_comm]) hQbd, hIccQ]
  · refine ⟨Δ₂, Δ₁, hmk hD₂ hD₁ (by rw [union_comm]; exact hun)
      (by rw [inter_comm]; exact hint), hD₂, hD₁, ?_, ?_⟩
    · rw [hside (by rw [inter_comm]; exact hint) hbd₂ hbd₁ hPQ.subset hPbd, hIccP]
    · rw [hside hint hbd₁ hbd₂ (hPQ ▸ by rw [union_comm]) hQbd, hIccQ]

end Discs

end Side
end GM21
end GraphMinor
