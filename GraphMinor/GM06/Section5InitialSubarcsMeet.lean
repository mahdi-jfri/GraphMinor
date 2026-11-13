module

public import GraphMinor.Surface.CrossCut
import Mathlib.Topology.Homeomorph.Lemmas
import Mathlib.Topology.Order.IntermediateValue

/-!
# Initial subarcs of the same arc overlap positively

For the direction labels in VI (5.7), page 133, two radial arcs
assigned to the same directed end both start at its endpoint.
The inverse parametrization of that end maps each arc to a
strictly increasing interval map starting at zero. Their parameter
intervals share a positive point, so the two arcs meet away from
the initial vertex.
-/

public section
namespace GraphMinor.GM06
open Set Topology GraphMinor.Surface
universe u

/-- Two nondegenerate initial subarcs of one arc meet at positive
parameters on both subarcs. -/
theorem exists_positive_meeting_of_initial_subarcs
    {S : Type u} [TopologicalSpace S] [T2Space S]
    (f g h : C(unitInterval, S)) (hf : IsArcMap f)
    (hg : IsArcMap g) (hh : IsArcMap h)
    (hgf : range g ⊆ range f) (hhf : range h ⊆ range f)
    (hg0 : g 0 = f 0) (hh0 : h 0 = f 0) :
    ∃ r s : unitInterval, 0 < r ∧ 0 < s ∧ g r = h s := by
  let e : unitInterval ≃ₜ range f := Continuous.homeoOfEquivCompactToT2
    (f := Equiv.ofInjective f hf.2) f.continuous.rangeFactorization
  have hpar (a : C(unitInterval, S)) (ha : IsArcMap a)
      (haf : range a ⊆ range f) (ha0 : a 0 = f 0) :
      ∃ ψ : C(unitInterval, unitInterval), ψ 0 = 0 ∧ 0 < ψ 1 ∧
        range ψ = Icc 0 (ψ 1) ∧ ∀ t, f (ψ t) = a t := by
    let ψ : C(unitInterval, unitInterval) :=
      ⟨fun t => e.symm ⟨a t, haf (mem_range_self t)⟩,
        e.symm.continuous.comp (a.continuous.subtype_mk (fun t => haf (mem_range_self t)))⟩
    have hψ (t) : f (ψ t) = a t :=
      congrArg Subtype.val (e.apply_symm_apply ⟨a t, haf (mem_range_self t)⟩)
    have hψ0 : ψ 0 = 0 := hf.2 ((hψ 0).trans ha0)
    have hi : Function.Injective ψ := by
      intro r s hrs
      apply ha.2
      rw [← hψ r, ← hψ s, hrs]
    have hm : StrictMono ψ := ψ.continuous.strictMono_of_inj_boundedOrder
      (by change ψ 0 ≤ ψ 1; rw [hψ0]; exact bot_le) hi
    have hpos : 0 < ψ 1 := by
      have ht := hm (show (0 : unitInterval) < 1 from zero_lt_one)
      rwa [hψ0] at ht
    have hrange : range ψ = Icc 0 (ψ 1) := by
      have ht := ψ.continuous.image_Icc_of_strictMono hm
        (a := (0 : unitInterval)) (b := 1)
      rw [show Icc (0 : unitInterval) 1 = univ from Icc_bot_top, image_univ, hψ0] at ht
      exact ht
    exact ⟨ψ, hψ0, hpos, hrange, hψ⟩
  obtain ⟨ψ, hψ0, hψpos, hψrange, hψ⟩ := hpar g hg hgf hg0
  obtain ⟨χ, hχ0, hχpos, hχrange, hχ⟩ := hpar h hh hhf hh0
  let δ := min (ψ 1) (χ 1)
  have hδ : 0 < δ := lt_min hψpos hχpos
  have hδψ : δ ∈ range ψ := hψrange.symm ▸ ⟨hδ.le, min_le_left _ _⟩
  have hδχ : δ ∈ range χ := hχrange.symm ▸ ⟨hδ.le, min_le_right _ _⟩
  obtain ⟨r, hr⟩ := hδψ
  obtain ⟨s, hs⟩ := hδχ
  have hr0 : 0 < r := unitInterval.pos_iff_ne_zero.mpr (by
    rintro rfl
    exact hδ.ne' (hr.symm.trans hψ0))
  have hs0 : 0 < s := unitInterval.pos_iff_ne_zero.mpr (by
    rintro rfl
    exact hδ.ne' (hs.symm.trans hχ0))
  exact ⟨r, s, hr0, hs0, (hψ r).symm.trans
    ((congrArg f (hr.trans hs.symm)).trans (hχ s))⟩

end GraphMinor.GM06
