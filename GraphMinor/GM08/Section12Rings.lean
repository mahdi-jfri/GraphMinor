module

public import GraphMinor.GM08.Defs6to18
import GraphMinor.GM08.Section12Uncross
import GraphMinor.GM08.Section6

/-!
# Uncrossing the foundation rings in VIII, Section 12

A ring enclosed by a minimal ring is itself minimal: its enclosed
edge set is a subset, so minimality makes the two edge sets equal.
Consequently (6.5) can be applied repeatedly to a finite family without
losing the minimal-ring conditions required by the foundation.
-/

public section

namespace GraphMinor.GM08

open Set Surface

universe u

/-- Shrinking a minimal ring to another ring preserves minimality.
This is the invariant in the repeated applications of VIII (6.5) on
page 267, used in the foundation of the disc induction. -/
theorem IsMinimalCRing.of_enclosed {S : Type u} [TopologicalSpace S]
    {D : Drawing S} {Δ F F' : Set S} (hΔ : IsClosedDisc Δ)
    {C : DiscCircuit D Δ} (hF : IsMinimalCRing C F) (hF' : IsCRing C F')
    (henc : OArcEncloses Δ F F') : IsMinimalCRing C F' := by
  have hsub := edgesInsideOArc_mono_of_oArcEncloses (D := D) hΔ hF.1.1 hF'.1
    hF.1.2.1 hF'.2.1 henc
  have heq := hsub.eq_of_not_ssubset (hF.2 F' hF')
  refine ⟨hF', fun G hG => ?_⟩
  rw [heq]
  exact hF.2 G hG

/-- One application of (6.5) to two minimal rings of bosses with
disjoint edge sets preserves minimality and shrinks both rings.
This is the repeated uncrossing step of VIII, page 267. -/
theorem uncross_disjoint_boss_rings {S : Type u} [TopologicalSpace S]
    [T2Space S] [ConnectedSpace S] {D : Drawing S} {Δ : Set S}
    (hΔ : IsClosedDisc Δ) (hDU : D.U ⊆ Δ) (hbd : D.IsNormal (discBd Δ))
    {C₁ C₂ : DiscCircuit D Δ} {F₁ F₂ : Set S}
    (hB₁ : IsBoss D Δ C₁) (hB₂ : IsBoss D Δ C₂)
    (hF₁ : IsMinimalCRing C₁ F₁) (hF₂ : IsMinimalCRing C₂ F₂)
    (hdis : Disjoint (bossDelta D Δ C₁) (bossDelta D Δ C₂)) :
    ∃ F₁' F₂', IsMinimalCRing C₁ F₁' ∧ IsMinimalCRing C₂ F₂' ∧
      OArcEncloses Δ F₁ F₁' ∧ OArcEncloses Δ F₂ F₂' ∧
      BoundDisjointOpenDiscs Δ F₁' F₂' := by
  obtain ⟨F₁', F₂', h₁, h₂, he₁, he₂, hd⟩ := theorem_6_5_proof hΔ hF₁.1 hF₂.1
    (boundDisjointOpenDiscs_ring_boss hΔ hDU hbd hB₁ hB₂ hF₁ hF₂ hdis)
    (boundDisjointOpenDiscs_ring_boss hΔ hDU hbd hB₂ hB₁ hF₂ hF₁ hdis.symm)
  exact ⟨F₁', F₂', hF₁.of_enclosed hΔ h₁ he₁, hF₂.of_enclosed hΔ h₂ he₂, he₁, he₂, hd⟩

/-- Shrinking both boundary rings preserves disjointness of their
inside discs. This keeps all earlier disjoint pairs disjoint during
the finite uncrossing construction on VIII, page 267. -/
theorem boundDisjointOpenDiscs_of_enclosed {S : Type u} [TopologicalSpace S]
    {Δ F₁ F₂ G₁ G₂ : Set S} (hΔ : IsClosedDisc Δ)
    (hF₁Δ : F₁ ⊆ Δ) (hF₂Δ : F₂ ⊆ Δ) (hG₁Δ : G₁ ⊆ Δ) (hG₂Δ : G₂ ⊆ Δ)
    (hF₁ : IsOArc F₁) (hF₂ : IsOArc F₂) (hG₁ : IsOArc G₁) (hG₂ : IsOArc G₂)
    (he₁ : OArcEncloses Δ F₁ G₁) (he₂ : OArcEncloses Δ F₂ G₂)
    (hd : BoundDisjointOpenDiscs Δ F₁ F₂) : BoundDisjointOpenDiscs Δ G₁ G₂ := by
  obtain ⟨B₁, hB₁, -⟩ := disc_oArc Δ F₁ hΔ hF₁Δ hF₁
  obtain ⟨B₂, hB₂, -⟩ := disc_oArc Δ F₂ hΔ hF₂Δ hF₂
  obtain ⟨E₁, hE₁, -⟩ := disc_oArc Δ G₁ hΔ hG₁Δ hG₁
  obtain ⟨E₂, hE₂, -⟩ := disc_oArc Δ G₂ hΔ hG₂Δ hG₂
  have hm₁ := (insideDisc_subset_of_oArcEncloses hΔ hB₁ hE₁ he₁).2
  have hm₂ := (insideDisc_subset_of_oArcEncloses hΔ hB₂ hE₂ he₂).2
  exact hd.mono
    (fun x hx => (insideOArc_iff_mem_discInt hΔ hB₁).mpr
      (hm₁ ((insideOArc_iff_mem_discInt hΔ hE₁).mp hx)))
    (fun x hx => (insideOArc_iff_mem_discInt hΔ hB₂).mpr
      (hm₂ ((insideOArc_iff_mem_discInt hΔ hE₂).mp hx)))

end GraphMinor.GM08
