module

public import GraphMinor.GM07.CutStages
import Mathlib.Data.Set.Card

/-!
# Roots in the disc cut

The new boundary is the preimage of the old boundary and the cutting
arc. A vertex on the arc has another lift, and a vertex off it has none.
Thus the roots of the cut graft are precisely the points over old roots
or in nontrivial fibres. This is the root rule for the reconstruction
in VIII (15.4).
-/

public section

namespace GraphMinor.GM08

open Set GraphMinor.Surface

universe w

/-- Every fibre of an arc cutting map has size at most two. This is
the pairing used in the short-tube reconstruction of VIII (15.4),
page 282. -/
theorem cutting_fibre_ncard_le_two {S Y : Type w} [TopologicalSpace S]
    [TopologicalSpace Y] {ψ : Y → S} {F : Set S} (hc : IsCutting ψ F) (x : S) :
    (ψ ⁻¹' {x}).ncard ≤ 2 := by
  by_cases hx : x ∈ F
  · exact (hc.2.2.2.1 x hx).le
  · have hsub : (ψ ⁻¹' {x}).Subsingleton := by
      intro y hy z hz
      have hy' : ψ y = x := hy
      have hz' : ψ z = x := hz
      exact hc.2.2.1 (show ψ y ∈ Fᶜ from hy'.symm ▸ hx)
        (show ψ z ∈ Fᶜ from hz'.symm ▸ hx) (hy'.trans hz'.symm)
    exact ((ncard_le_one hsub.finite).mpr hsub).trans (by decide)

/-- The boundary root rule of an arc cut: a lifted vertex is a new root
exactly when it lies over an old root or has another vertex in its fibre.
This is the hypothesis proved from the cut for the identification chain
in VIII (15.4), page 282. -/
theorem arc_cut_root_rule {S Y : Type w} [TopologicalSpace S]
    [TopologicalSpace Y] {ψ : Y → S} {F V : Set S}
    (hcut : GM07.IsCutAlongSet F ψ) (hc : IsCutting ψ F) :
    ∀ y ∈ ψ ⁻¹' V, y ∈ ψ ⁻¹' V ∩ bd Y ↔
      ψ y ∈ V ∩ bd S ∨ ∃ z ∈ ψ ⁻¹' V, z ≠ y ∧ ψ z = ψ y := by
  intro y hy
  have hbd : y ∈ bd Y ↔ ψ y ∈ bd S ∨ ψ y ∈ F := by
    rw [← hcut.preimage_bd]
    rfl
  constructor
  · rintro ⟨_, hb⟩
    rcases hbd.mp hb with hold | hF
    · exact .inl ⟨hy, hold⟩
    · have htwo : 1 < (ψ ⁻¹' {ψ y}).ncard := by rw [hc.2.2.2.1 _ hF]; decide
      obtain ⟨z, hz, hzy⟩ := exists_ne_of_one_lt_ncard htwo y
      have he : ψ z = ψ y := hz
      have hzV : ψ z ∈ V := he.symm ▸ hy
      exact .inr ⟨z, hzV, hzy, he⟩
  · rintro (hold | ⟨z, hz, hzy, he⟩)
    · exact ⟨hy, hbd.mpr (.inl hold.2)⟩
    · refine ⟨hy, hbd.mpr (.inr ?_)⟩
      by_contra hn
      exact hzy (hc.2.2.1 (show ψ z ∈ Fᶜ from he.symm ▸ hn) hn he)

end GraphMinor.GM08
