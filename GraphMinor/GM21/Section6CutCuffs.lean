module

public import GraphMinor.GM21.Section6CutSpaces
import GraphMinor.GM19.CutTwo
import GraphMinor.GM11.RadialChord

/-!
# Graph Minors XXI, (6.3), claim (2): two vertices on each cuff of the cut surface

A presentation asks that every cuff hold at least two vertices of the drawing. For the drawing
`Γ' = ψ⁻¹(Γ)` on the surface `Σ'` cut along a proper line `F` with ends in `V(Γ)` this follows from
the same property of `Γ`, by `GM19.two_of_sheets`: the cut is one to one off `F`, and over the open
arc `F \ {a, b}` it has two sheets, the two lifts of `F`.
-/

@[expose] public section

namespace GraphMinor
namespace GM21
namespace CutLine

open Set Function Topology GraphMinor.Surface

variable {S S' : Type} [TopologicalSpace S] [TopologicalSpace S']
  {ψ : S' → S} {F : Set S} {a b : S} {X Y : Set S'} {a₁ b₁ a₂ b₂ : S'}

namespace IsLineCut

variable (h : IsLineCut ψ F a b X Y a₁ b₁ a₂ b₂)
include h

/-- **Each cuff of the cut surface holds two vertices of `Γ'`.** -/
theorem two_le_ncard_cuff (hS : IsSurface S) (hF : IsProperLineInSurface F a b) {Γ : Drawing S}
    (habV : a ∈ Γ.V ∧ b ∈ Γ.V) (hcuff : ∀ C ∈ cuffs S, 2 ≤ (Γ.V ∩ C).ncard) {Γ' : Drawing S'}
    (hV : Γ'.V = ψ ⁻¹' Γ.V) : ∀ C ∈ cuffs S', 2 ≤ (Γ'.V ∩ C).ncard := by
  have : T2Space S := hS.2.1
  have : T2Space S' := h.t2Space
  have hFc : IsClosed F := hF.1.isCompact.isClosed
  set K := GM11.lineDrawing hF.1 hF.ne with hK
  have hKE : arcComponentsIn (K.U \ K.V) = {F \ {a, b}} := GM11.lineDrawing_E hF.1 hF.ne
  have hXc : IsClosed X := h.lineX.isCompact.isClosed
  have hYc : IsClosed Y := h.lineY.isCompact.isClosed
  intro C hC
  obtain ⟨p, hp, q, hq, hpq⟩ := GM19.two_of_sheets (K := K) (A := Γ.V) hS h.surface h.continuous
    h.injOn_compl
    (by
      rintro _ ⟨z, hz, rfl⟩
      rw [h.bd_eq hS hF] at hz
      exact hz)
    (by
      intro e he J _ hJc hJe
      rw [hKE] at he
      subst he
      have hJXY : J ⊆ X ∪ Y := by
        rw [h.union]
        exact fun z hz => (hJe (mem_image_of_mem ψ hz)).1
      have hdis : J ∩ (X ∩ Y) = ∅ := by
        rw [h.disjoint.inter_eq, inter_empty]
      rcases (isPreconnected_iff_subset_of_disjoint_closed.mp hJc) _ _ hXc hYc hJXY hdis with
        hJ | hJ
      · exact h.bijX.injOn.mono hJ
      · exact h.bijY.injOn.mono hJ)
    (by
      intro e he
      rw [hKE] at he
      subst he
      exact ⟨a, b, by rw [GM11.closure_sdiff_pair hF.1]; exact hF.1⟩)
    (by
      intro x hx
      have : x ∈ F ∩ bd S := hx
      rw [hF.inter_bd_eq] at this
      exact this)
    (by
      rintro x (rfl | rfl)
      exacts [habV.1, habV.2])
    (by
      rintro ⟨C₀, hC₀⟩
      obtain ⟨p, q, hp, hq, hpq⟩ := (one_lt_ncard_iff (Γ.finite_V.inter_of_left C₀)).mp
        (hcuff C₀ hC₀)
      exact ⟨p, hp, q, hq, hpq⟩)
    ⟨C, hC⟩
  have hfin : (Γ'.V ∩ C).Finite := Γ'.finite_V.inter_of_left C
  have hsub : ({p, q} : Set S') ⊆ Γ'.V ∩ C := by
    rintro x (rfl | rfl)
    · exact ⟨hV ▸ hp.1, hp.2⟩
    · exact ⟨hV ▸ hq.1, hq.2⟩
  calc 2 = ({p, q} : Set S').ncard := (ncard_pair hpq).symm
    _ ≤ (Γ'.V ∩ C).ncard := ncard_le_ncard hsub hfin

end IsLineCut

end CutLine
end GM21
end GraphMinor
