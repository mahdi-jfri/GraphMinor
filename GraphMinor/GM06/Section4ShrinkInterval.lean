module

public import GraphMinor.GM06.Defs
import GraphMinor.GM06.Section4OpenSubarc
import GraphMinor.GM06.Section4IntervalRestriction
import GraphMinor.GM06.Section4FiniteInterval
import GraphMinor.GM06.Section4Subarc

/-!
# Shrinking a cuff interval around finitely many retained vertices

In VI (4.2), claim (2), a minimum candidate cannot contain unnecessary
vertices beyond the first or last vertex of its chosen component. We
choose new cut points in its parameter interval outside the finite
vertex set. The smaller cuff interval retains the chosen points and
lies strictly between the prescribed parameter limits.
-/

public section

namespace GraphMinor.GM06

open Set GraphMinor.Surface

universe u

/-- Restrict a cuff interval around a nonempty finite set, with new ends
outside the full finite vertex set. The prescribed parameter limits let
the minimum-size argument exclude a point beyond the retained set. -/
theorem exists_restricted_cuff_interval
    {S : Type u} [TopologicalSpace S] [T2Space S]
    {C A V W : Set S} (hC : IsOArc C) {s t : S}
    (hA : A ∈ componentsIn (C \ {s, t}))
    (f : Curve S) (hf : ParametrizesSet f (closure A) s t)
    (hV : V.Finite) (hW : W.Finite) (hWne : W.Nonempty) (hWA : W ⊆ A)
    {l r : unitInterval} (hWlr : f ⁻¹' W ⊆ Ioo l r) :
    ∃ s' ∈ A \ V, ∃ t' ∈ A \ V, s' ≠ t' ∧
      ∃ B ∈ componentsIn (C \ {s', t'}), W ⊆ B ∧ B ⊆ A ∧
        B ⊆ f '' Ioo l r ∧ IsLineWithEnds (closure B) s' t' := by
  have hpre := preimage_component_of_parametrizes_closure hA f hf
  have hVf : (f ⁻¹' V).Finite := Set.Finite.preimage hf.1.injOn hV
  have hWf : (f ⁻¹' W).Finite := Set.Finite.preimage hf.1.injOn hW
  have hWfn : (f ⁻¹' W).Nonempty := by
    obtain ⟨w, hw⟩ := hWne
    have hwr : w ∈ range f := hf.2.1.symm ▸ subset_closure (hWA hw)
    obtain ⟨v, hv⟩ := hwr
    exact ⟨v, by change f v ∈ W; rw [hv]; exact hw⟩
  obtain ⟨p, hp, q, hq, hpq, hWpq⟩ :=
    exists_inner_interval_cover_finite hVf hWf hWfn hWlr
  have hp01 : p ∈ Ioo (0 : unitInterval) 1 :=
    ⟨lt_of_le_of_lt bot_le hp.1.1, lt_of_lt_of_le hp.1.2 le_top⟩
  have hq01 : q ∈ Ioo (0 : unitInterval) 1 :=
    ⟨lt_of_le_of_lt bot_le hq.1.1, lt_of_lt_of_le hq.1.2 le_top⟩
  have hpA : f p ∈ A := by change p ∈ f ⁻¹' A; rw [hpre]; exact hp01
  have hqA : f q ∈ A := by change q ∈ f ⁻¹' A; rw [hpre]; exact hq01
  let k := GM07.subPathSeg f p q
  let L := range k
  let B := L \ {f p, f q}
  have hki : Function.Injective k := injective_subPathSeg_of_ne hf.1 hpq.ne
  have hL : IsLineWithEnds L (f p) (f q) := by
    simpa only [L, k, GM07.subPathSeg_zero, GM07.subPathSeg_one] using
      IsArcMap.isLineWithEnds ⟨k.continuous, hki⟩
  have hLA : L ⊆ A := by
    rw [show L = range (GM07.subPathSeg f p q) from rfl, range_subPathSeg_eq_image_uIcc,
      uIcc_of_le hpq.le]
    rintro x ⟨v, hv, rfl⟩
    change v ∈ f ⁻¹' A
    rw [hpre]
    exact ⟨hp01.1.trans_le hv.1, hv.2.trans_lt hq01.2⟩
  have hAC : A ⊆ C := by
    obtain ⟨x, _, rfl⟩ := hA
    exact (connectedComponentIn_subset _ x).trans sdiff_subset
  have hBcomp : B ∈ componentsIn (C \ {f p, f q}) :=
    cuff_line_sdiff_ends_mem_componentsIn hC hL (hLA.trans hAC)
  have hBimage : B = f '' Ioo p q := range_subPathSeg_sdiff_ends_eq_image_Ioo hf.1 hpq
  refine ⟨f p, ⟨hpA, hp.2⟩, f q, ⟨hqA, hq.2⟩, hf.1.ne hpq.ne, B, hBcomp,
    ?_, sdiff_subset.trans hLA, ?_, ?_⟩
  · intro w hw
    have hwr : w ∈ range f := hf.2.1.symm ▸ subset_closure (hWA hw)
    obtain ⟨v, hv⟩ := hwr
    rw [hBimage]
    exact ⟨v, hWpq (by change f v ∈ W; rw [hv]; exact hw), hv⟩
  · rw [hBimage]
    exact image_mono fun v hv => ⟨hp.1.1.trans hv.1, hv.2.trans hq.1.2⟩
  · rw [show closure B = L from closure_line_sdiff_ends_eq hL]
    exact hL

end GraphMinor.GM06
