module

public import GraphMinor.GM06.Defs
public import GraphMinor.GM07.Section11c
import Mathlib.Topology.Order.IntermediateValue

/-!
# Restricting an interval parameterization

The minimum argument in VI (4.2), claim (2), replaces a cuff interval
by a smaller one. A restricted parameterization has exactly the image
of the parameter interval between the cut points and stays injective
when those points differ.
-/

public section

namespace GraphMinor.GM06

open Set GraphMinor.Surface

universe u

/-- Restricting an injective curve between distinct parameters stays
injective, in either orientation. -/
theorem injective_subPathSeg_of_ne
    {S : Type u} [TopologicalSpace S] {f : Curve S}
    (hf : Function.Injective f) {s t : unitInterval} (hst : s ≠ t) :
    Function.Injective (GM07.subPathSeg f s t) := by
  intro x y hxy
  have he := congrArg Subtype.val (hf hxy)
  dsimp [GM07.subPathSeg] at he
  apply Subtype.ext
  have hn : (t : ℝ) - (s : ℝ) ≠ 0 := sub_ne_zero.mpr
    (Ne.symm (Subtype.val_injective.ne hst))
  have hmul : ((x : ℝ) - (y : ℝ)) * ((t : ℝ) - (s : ℝ)) = 0 := by
    nlinarith only [he]
  exact sub_eq_zero.mp ((mul_eq_zero.mp hmul).resolve_right hn)

/-- The restricted curve covers exactly the closed interval between
its two cut parameters. -/
theorem range_subPathSeg_eq_image_uIcc
    {S : Type u} [TopologicalSpace S] (f : Curve S) (s t : unitInterval) :
    range (GM07.subPathSeg f s t) = f '' uIcc s t := by
  let ι := GM07.subPathSeg (ContinuousMap.id unitInterval) s t
  have hι0 : ι 0 = s := GM07.subPathSeg_zero _ _ _
  have hι1 : ι 1 = t := GM07.subPathSeg_one _ _ _
  have hsub : range ι ⊆ uIcc s t := by
    rintro x ⟨v, rfl⟩
    rcases le_total s t with hle | hle
    · rw [uIcc_of_le hle]
      constructor
      · change (s : ℝ) ≤ (1 - (v : ℝ)) * (s : ℝ) + (v : ℝ) * (t : ℝ)
        have h : (s : ℝ) ≤ (t : ℝ) := hle
        nlinarith only [h, v.2.1]
      · change (1 - (v : ℝ)) * (s : ℝ) + (v : ℝ) * (t : ℝ) ≤ (t : ℝ)
        have h : (s : ℝ) ≤ (t : ℝ) := hle
        nlinarith only [h, v.2.2]
    · rw [uIcc_of_ge hle]
      constructor
      · change (t : ℝ) ≤ (1 - (v : ℝ)) * (s : ℝ) + (v : ℝ) * (t : ℝ)
        have h : (t : ℝ) ≤ (s : ℝ) := hle
        nlinarith only [h, v.2.2]
      · change (1 - (v : ℝ)) * (s : ℝ) + (v : ℝ) * (t : ℝ) ≤ (s : ℝ)
        have h : (t : ℝ) ≤ (s : ℝ) := hle
        nlinarith only [h, v.2.1]
  have hsurj : uIcc s t ⊆ range ι := by
    intro x hx
    have hxin : x ∈ uIcc (ι 0) (ι 1) := by rw [hι0, hι1]; exact hx
    obtain ⟨v, _, hv⟩ := intermediate_value_uIcc ι.continuous.continuousOn hxin
    exact ⟨v, hv⟩
  have hrange : range ι = uIcc s t := Subset.antisymm hsub hsurj
  change range (f ∘ ι) = _
  rw [range_comp, hrange]

/-- Removing the two ends of a restricted injective curve gives the
image of the open parameter interval. -/
theorem range_subPathSeg_sdiff_ends_eq_image_Ioo
    {S : Type u} [TopologicalSpace S] {f : Curve S} (hf : Function.Injective f)
    {p q : unitInterval} (hpq : p < q) :
    range (GM07.subPathSeg f p q) \ {f p, f q} = f '' Ioo p q := by
  rw [range_subPathSeg_eq_image_uIcc, uIcc_of_le hpq.le]
  ext x
  constructor
  · rintro ⟨⟨r, hr, rfl⟩, hends⟩
    refine ⟨r, ⟨?_, ?_⟩, rfl⟩
    · exact lt_of_le_of_ne hr.1 (fun h => hends (Or.inl (congrArg f h.symm)))
    · exact lt_of_le_of_ne hr.2 (fun h => hends (Or.inr (congrArg f h)))
  · rintro ⟨r, hr, rfl⟩
    refine ⟨⟨r, ⟨hr.1.le, hr.2.le⟩, rfl⟩, ?_⟩
    rintro (he | he)
    · exact (ne_of_gt hr.1) (hf he)
    · exact (ne_of_lt hr.2) (hf he)

end GraphMinor.GM06
