module

public import GraphMinor.GM08.Defs6to18
import GraphMinor.GM08.Section9Foundation
import GraphMinor.GM08.Section9DiscContext
import GraphMinor.GM08.Section6
import GraphMinor.GM11.OArcCircuit

/-!
# The two-ring uncrossing step for the disc foundation

Distinct maximal bosses have disjoint nonempty edge sets. Neither of
their minimal rings can enter the other boss disc, since (6.4) would
then put one nonempty edge set inside the other. The same argument
excludes overlap with the other boss interior. Thus (6.5) applies,
shrinking the two rings to rings with disjoint interiors. This is the
repeated uncrossing step on page 267 used in Section 12.
-/

public section

namespace GraphMinor.GM08

open Set Surface

universe u

/-- A boss edge set is nonempty: the boss circuit has an edge, and all
of its edges lie inside every minimal ring. This is used when choosing
and uncrossing the foundation for Section 12. -/
theorem IsBoss.bossDelta_nonempty {S : Type u} [TopologicalSpace S]
    [T2Space S] [ConnectedSpace S] {D : Drawing S} {Δ : Set S}
    (hΔ : IsClosedDisc Δ) (hDU : D.U ⊆ Δ) (hbd : D.IsNormal (discBd Δ))
    {C : DiscCircuit D Δ} (hC : IsBoss D Δ C) : (bossDelta D Δ C).Nonempty := by
  obtain ⟨B, -, hBD, hBU⟩ := GM11.exists_circuit_of_oArc C.isOArc_U C.U_sub_drawing
  obtain ⟨e, he⟩ := drawing_edges_nonempty_of_oArc C.isOArc_U (by rw [hBU])
  exact ⟨e, hC.circuit_edges_subset_bossDelta hΔ hDU hbd hBD hBU he⟩

/-- A minimal ring of one boss cannot enter the other boss disc when
their boss edge sets are disjoint. Otherwise the enclosure conclusion
of (6.4) contradicts their disjoint nonempty edge sets. -/
theorem not_ring_inside_disjoint_boss {S : Type u} [TopologicalSpace S]
    [T2Space S] [ConnectedSpace S] {D : Drawing S} {Δ : Set S}
    (hΔ : IsClosedDisc Δ) (hDU : D.U ⊆ Δ) (hbd : D.IsNormal (discBd Δ))
    {C₁ C₂ : DiscCircuit D Δ} {F₁ F₂ : Set S}
    (hB₁ : IsBoss D Δ C₁) (hB₂ : IsBoss D Δ C₂)
    (hF₁ : IsMinimalCRing C₁ F₁) (hF₂ : IsMinimalCRing C₂ F₂)
    (hdis : Disjoint (bossDelta D Δ C₁) (bossDelta D Δ C₂)) :
    ∀ y ∈ F₁, ¬ InsideOArc Δ C₂.U y := by
  intro y hy hin
  have henc := oArcEncloses_of_isBoss_meets_inside hΔ hB₂ hB₁ hF₂.1 hF₁.1 ⟨y, hy, hin⟩
  have hsub := edgesInsideOArc_mono_of_oArcEncloses (D := D) hΔ hF₂.1.1 hF₁.1.1
    hF₂.1.2.1 hF₁.1.2.1 henc
  rw [← bossDelta_eq_edgesInside_of_isMinimalCRing hΔ hF₁,
    ← bossDelta_eq_edgesInside_of_isMinimalCRing hΔ hF₂] at hsub
  obtain ⟨e, he⟩ := hB₁.bossDelta_nonempty hΔ hDU hbd
  exact disjoint_left.mp hdis he (hsub he)

/-- Disjoint boss edge sets give the side condition of (6.5) for their
minimal rings. This justifies each uncrossing in the foundation
construction on page 267, used by Section 12. -/
theorem boundDisjointOpenDiscs_ring_boss {S : Type u} [TopologicalSpace S]
    [T2Space S] [ConnectedSpace S] {D : Drawing S} {Δ : Set S}
    (hΔ : IsClosedDisc Δ) (hDU : D.U ⊆ Δ) (hbd : D.IsNormal (discBd Δ))
    {C₁ C₂ : DiscCircuit D Δ} {F₁ F₂ : Set S}
    (hB₁ : IsBoss D Δ C₁) (hB₂ : IsBoss D Δ C₂)
    (hF₁ : IsMinimalCRing C₁ F₁) (hF₂ : IsMinimalCRing C₂ F₂)
    (hdis : Disjoint (bossDelta D Δ C₁) (bossDelta D Δ C₂)) :
    BoundDisjointOpenDiscs Δ F₁ C₂.U := by
  have hin := not_ring_inside_disjoint_boss hΔ hDU hbd hB₁ hB₂ hF₁ hF₂ hdis
  by_contra hn
  obtain ⟨z, hzF, hzC⟩ := not_disjoint_iff.mp hn
  obtain ⟨B, hB, -⟩ := disc_oArc Δ F₁ hΔ hF₁.1.1 hF₁.1.2.1
  have hzB := (insideOArc_iff_mem_discInt hΔ hB).mp hzF
  have hzC' := (insideOArc_iff_mem_discInt hΔ C₂.isInside).mp hzC
  have hsep : Disjoint (discInt C₂.ins) (discBd B) := by
    rw [hB.2.2.1]
    exact disjoint_left.mpr fun x hxC hxF => hin x hxF
      ((insideOArc_iff_mem_discInt hΔ C₂.isInside).mpr hxC)
  have hCB := subset_of_discInt_meets hΔ C₂.isInside.1 hB.1 C₂.isInside.2.1 hB.2.1
    hsep ⟨z, hzC'.1, hzB⟩
  have henc : OArcEncloses Δ F₁ C₂.U := by
    rw [oArcEncloses_iff_subset hΔ hB]
    exact (C₂.isInside.2.2.1 ▸ discBd_subset C₂.ins).trans hCB.1
  obtain ⟨F, hF, henc₂, henc₁⟩ := exists_cRing_enclosed_of_oArcEncloses hΔ hF₂.1 hF₁.1 henc
  have hsub₂ := edgesInsideOArc_mono_of_oArcEncloses (D := D) hΔ hF₂.1.1 hF.1
    hF₂.1.2.1 hF.2.1 henc₂
  have hsub₁ := edgesInsideOArc_mono_of_oArcEncloses (D := D) hΔ hF₁.1.1 hF.1
    hF₁.1.2.1 hF.2.1 henc₁
  have heq := hsub₂.eq_of_not_ssubset (hF₂.2 F hF)
  have hsub : bossDelta D Δ C₂ ⊆ bossDelta D Δ C₁ := by
    rw [bossDelta_eq_edgesInside_of_isMinimalCRing hΔ hF₂,
      bossDelta_eq_edgesInside_of_isMinimalCRing hΔ hF₁, ← heq]
    exact hsub₁
  obtain ⟨e, he⟩ := hB₂.bossDelta_nonempty hΔ hDU hbd
  exact disjoint_left.mp hdis (hsub he) he

end GraphMinor.GM08
