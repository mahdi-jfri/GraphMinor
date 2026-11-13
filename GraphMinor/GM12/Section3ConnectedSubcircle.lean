module

public import GraphMinor.GM12.Section3ConnectedSubline
import GraphMinor.GM11.RadialChord

/-!
# Proper connected compact parts of a circle are lines

In the connected-intersection case used by XII (3.1), page 245,
choose a point of the circle outside the intersection. The complementary
arc construction places the whole intersection in one closed arc.
The interval minimum and maximum then give its line parametrization.
-/

public section

namespace GraphMinor.GM12

open Set Surface GM11

/-- A proper compact preconnected subset of a circle with at least
two points is a line. -/
theorem isLineWithEnds_of_compact_preconnected_subset_oArc
    {S : Type*} [TopologicalSpace S] [T2Space S]
    {F T : Set S} {x y : S} (hF : IsOArc F) (hTF : T ⊆ F)
    (hne : T ≠ F) (hTc : IsCompact T) (hTp : IsPreconnected T)
    (hx : x ∈ T) (hy : y ∈ T) (hxy : x ≠ y) :
    ∃ a b, a ≠ b ∧ IsLineWithEnds T a b := by
  have hnot : ¬ F ⊆ T := fun h => hne (Subset.antisymm hTF h)
  obtain ⟨z, hzF, hzT⟩ := not_subset.mp hnot
  obtain ⟨e⟩ := hF
  let p : Circle → S := fun w => (e w).val
  have hpc : Continuous p := continuous_subtype_val.comp e.continuous
  have hpi : Function.Injective p := fun s t he => e.injective (Subtype.ext he)
  let K := p ⁻¹' T
  let cx := e.symm ⟨x, hTF hx⟩
  let cy := e.symm ⟨y, hTF hy⟩
  let cz := e.symm ⟨z, hzF⟩
  have hpx : p cx = x := congrArg Subtype.val (e.apply_symm_apply _)
  have hpy : p cy = y := congrArg Subtype.val (e.apply_symm_apply _)
  have hpz : p cz = z := congrArg Subtype.val (e.apply_symm_apply _)
  have hxK : cx ∈ K := by change p cx ∈ T; rwa [hpx]
  have hyK : cy ∈ K := by change p cy ∈ T; rwa [hpy]
  have hzK : cz ∉ K := by change p cz ∉ T; rwa [hpz]
  have hcxy : cx ≠ cy := fun h => hxy (hpx.symm.trans ((congrArg p h).trans hpy))
  obtain ⟨a, b, hab, hcover, _, _, hinterior, _⟩ :=
    exists_circle_chord (hTc.isClosed.preimage hpc) hzK hxK hyK hcxy
  have hKb : K ⊆ range b := by
    intro w hw
    have hwcover : w ∈ range a ∪ range b := hcover.symm ▸ mem_univ w
    rcases hwcover with ⟨t, rfl⟩ | hwB
    · by_cases ht0 : t = 0
      · exact ⟨0, hab.zero.trans (congrArg a ht0.symm)⟩
      · by_cases ht1 : t = 1
        · exact ⟨1, hab.one.trans (congrArg a ht1.symm)⟩
        · exact (hinterior t ht0 ht1 hw).elim
    · exact hwB
  let q : unitInterval → S := fun t => p (b t)
  have hq : Continuous q := hpc.comp hab.arc_right.1
  have hqi : Function.Injective q := hpi.comp hab.arc_right.2
  have hTq : T ⊆ range q := by
    intro w hw
    let cw := e.symm ⟨w, hTF hw⟩
    have hpw : p cw = w := congrArg Subtype.val (e.apply_symm_apply _)
    have hcw : cw ∈ K := by change p cw ∈ T; rwa [hpw]
    obtain ⟨t, ht⟩ := hKb hcw
    exact ⟨t, (congrArg p ht).trans hpw⟩
  exact isLineWithEnds_of_compact_preconnected_subset_line
    (isLine_range hq hqi) hTq hTc hTp hx hy hxy

end GraphMinor.GM12
