module

public import GraphMinor.Surface.CrossCut
import GraphMinor.Surface.Circle
import Mathlib.Topology.Homeomorph.Lemmas
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Tactic.Linarith

/-!
# Compact subsets of a connected proper open circle set

For the corner enclosure of VI (5.5), page 130, remove a direction
outside the region and use interval coordinates on the punctured
circle. The region becomes an interval. Enlarge the least and
greatest compact-set coordinates slightly within this open interval,
and parameterize the resulting closed arc.
-/

public section
namespace GraphMinor.GM06
open Set Topology GraphMinor.Surface

/-- A compact subset of a proper preconnected open circle set lies
in a closed arc within that set, missing the two ends of the arc. -/
theorem exists_arc_enclosing_compact_in_open_circle_set
    {W K : Set Circle} (hW : IsOpen W) (hWp : IsPreconnected W)
    {z : Circle} (hz : z ∉ W) (hK : IsCompact K) (hne : K.Nonempty) (hKW : K ⊆ W) :
    ∃ a : unitInterval → Circle, IsArcMap a ∧ range a ⊆ W ∧
      K ⊆ range a ∧ a 0 ∉ K ∧ a 1 ∉ K := by
  have hpun : W ⊆ ({z} : Set Circle)ᶜ := by
    intro w hw he
    exact hz (mem_singleton_iff.mp he ▸ hw)
  obtain ⟨e₀⟩ := nonempty_homeomorph_Ioo_nextSegment (finite_singleton z) (mem_singleton z)
  let e : Ioo (0 : ℝ) 1 ≃ₜ ↥(({z} : Set Circle)ᶜ) :=
    e₀.trans (Homeomorph.setCongr (nextSegment_singleton z))
  let f : Ioo (0 : ℝ) 1 → Circle := fun t => (e t).1
  have hfc : Continuous f := continuous_subtype_val.comp e.continuous
  have hfi : Function.Injective f := fun x y he => e.injective (Subtype.ext he)
  have hfemb : IsEmbedding f := IsEmbedding.subtypeVal.comp e.isEmbedding
  have hfr : range f = ({z} : Set Circle)ᶜ := by
    ext w
    constructor
    · rintro ⟨t, rfl⟩; exact (e t).2
    · intro hw; exact ⟨e.symm ⟨w, hw⟩, congrArg Subtype.val (e.apply_symm_apply _)⟩
  let U := f ⁻¹' W
  let B := f ⁻¹' K
  have hUo : IsOpen U := hW.preimage hfc
  have hUp : IsPreconnected U := by
    change IsPreconnected (e ⁻¹' (Subtype.val ⁻¹' W))
    apply (e.isPreconnected_preimage).mpr
    apply (IsInducing.subtypeVal.isPreconnected_image).mp
    rw [Subtype.image_preimage_coe, inter_eq_right.mpr hpun]
    exact hWp
  have hBc : IsCompact B := hfemb.isInducing.isCompact_preimage' hK (by
    rw [hfr]; exact hKW.trans hpun)
  have hBne : B.Nonempty := by
    obtain ⟨w, hw⟩ := hne
    obtain ⟨t, ht⟩ := (hfr.symm ▸ hpun (hKW hw) : w ∈ range f)
    refine ⟨t, ?_⟩
    change f t ∈ K
    rw [ht]; exact hw
  have hBU : B ⊆ U := fun _ hb => hKW hb
  obtain ⟨u, huB, humin⟩ := hBc.exists_isLeast hBne
  obtain ⟨v, hvB, hvmax⟩ := hBc.exists_isGreatest hBne
  obtain ⟨u₀, u₁, huu, huint⟩ := mem_nhds_iff_exists_Ioo_subset.mp (hUo.mem_nhds (hBU huB))
  obtain ⟨v₀, v₁, hvv, hvint⟩ := mem_nhds_iff_exists_Ioo_subset.mp (hUo.mem_nhds (hBU hvB))
  obtain ⟨l, hul, hlu⟩ := exists_between huu.1
  obtain ⟨r, hvr, hrv⟩ := exists_between hvv.2
  have hlU : l ∈ U := huint ⟨hul, hlu.trans huu.2⟩
  have hrU : r ∈ U := hvint ⟨hvv.1.trans hvr, hrv⟩
  have hlr : l < r := hlu.trans_le ((humin hvB).trans hvr.le)
  let j := (iccHomeoI (l : ℝ) (r : ℝ) hlr).symm
  let b : unitInterval → Ioo (0 : ℝ) 1 := fun t =>
    ⟨(j t).1, lt_of_lt_of_le l.2.1 (j t).2.1, lt_of_le_of_lt (j t).2.2 r.2.2⟩
  have hbc : Continuous b := (continuous_subtype_val.comp j.continuous).subtype_mk _
  have hbi : Function.Injective b := by
    intro t t' he
    apply j.injective
    apply Subtype.ext
    have hh := congrArg (fun x : Ioo (0 : ℝ) 1 => x.1) he
    exact hh
  have hb0 : b 0 = l := by
    apply Subtype.ext
    simp [b, j, iccHomeoI_symm_apply_coe]
  have hb1 : b 1 = r := by
    apply Subtype.ext
    simp [b, j, iccHomeoI_symm_apply_coe]
  have hbr (t) : b t ∈ Icc l r := (j t).2
  have hbs (t : Ioo (0 : ℝ) 1) (ht : t ∈ Icc l r) : ∃ c, b c = t := by
    refine ⟨j.symm ⟨t.1, ht⟩, ?_⟩
    apply Subtype.ext
    change (j (j.symm ⟨t.1, ht⟩)).1 = t.1
    exact congrArg Subtype.val (j.apply_symm_apply ⟨t.1, ht⟩)
  let a := f ∘ b
  refine ⟨a, ⟨hfc.comp hbc, hfi.comp hbi⟩, ?_, ?_, ?_, ?_⟩
  · rintro w ⟨t, rfl⟩
    exact hUp.ordConnected.out hlU hrU (hbr t)
  · intro w hw
    obtain ⟨t, ht⟩ := (hfr.symm ▸ hpun (hKW hw) : w ∈ range f)
    have htB : t ∈ B := by
      change f t ∈ K
      rw [ht]; exact hw
    obtain ⟨c, hc⟩ := hbs t ⟨hlu.le.trans (humin htB), (hvmax htB).trans hvr.le⟩
    exact ⟨c, by change f (b c) = w; rw [hc, ht]⟩
  · intro hh
    have hlB : l ∈ B := by
      change f l ∈ K
      simpa only [a, Function.comp_apply, hb0] using hh
    exact hlu.not_ge (humin hlB)
  · intro hh
    have hrB : r ∈ B := by
      change f r ∈ K
      simpa only [a, Function.comp_apply, hb1] using hh
    exact hvr.not_ge (hvmax hrB)

end GraphMinor.GM06
