module

public import GraphMinor.Surface.CutEdges
import Mathlib.Data.Set.Card

/-!
# The old boundary contribution to a cut vertex

A vertex on a cuff has two free side ends in a word presentation.
An interior vertex has none. This supplies the old-boundary term in
the vertex fibre calculation for VIII (18.2).
-/

public section

namespace GraphMinor.GM08

open Set GraphMinor.Surface

universe u

open Classical in
/-- In a surface word presentation, a graph vertex has two free side
ends if it is on the boundary and none otherwise. This is the boundary
contribution to the Euler calculation in VIII (18.2), page 286. -/
theorem word_free_ends_at_vertex_ncard {S : Type u} [TopologicalSpace S] [T2Space S]
    {W : ℕ → List Letter} {f : ℕ × ℂ → S} {V : Set S} {E : Set (Set S)}
    {A : Set S → unitInterval → S} {lab : Set S → ℕ}
    (hw : WordEdges W f V E A lab) {v : S} (hv : v ∈ V) :
    {a : SE W | f (spe W a) = v ∧ prtL W ∅ a = a}.ncard =
      if v ∈ bd S then 2 else 0 := by
  classical
  have hfixed_bd : ∀ a : SE W, prtL W ∅ a = a → f (spe W a) ∈ bd S := by
    intro a ha
    obtain ⟨k, e, hget⟩ : ∃ k e, (W a.1.1)[a.1.2.1]? = some (k, e) :=
      ⟨_, _, List.getElem?_eq_getElem a.2⟩
    have hfree : FreeSide W a.1.1 a.1.2.1 :=
      ((prtL_eq_iff hw.paired a hget).mp ha).resolve_left (notMem_empty k)
    rw [hw.bd_eq]
    exact ⟨spe W a, ⟨a.1.1, a.1.2.1, eo a.1.2.2, a.2, hfree, eo_mem _, rfl⟩, rfl⟩
  by_cases hbd : v ∈ bd S
  · rw [ite_eq_left hbd]
    obtain ⟨x, hx, hfx⟩ := hw.bd_eq ▸ hbd
    obtain ⟨i, p, t, hp, hfree, ht, rfl⟩ := hx
    obtain ⟨k, e, hget⟩ : ∃ k e, (W i)[p]? = some (k, e) :=
      ⟨_, _, List.getElem?_eq_getElem hp⟩
    obtain ⟨b, hbt⟩ := hw.corner_of_side hget ht (hfx.symm ▸ hv)
    let c : SE W := ⟨(i, p, b), hp⟩
    have hc : prtL W ∅ c = c := (prtL_eq_iff hw.paired c hget).mpr (Or.inr hfree)
    have hcv : f (spe W c) = v := by change f (spt W i p (eo b)) = v; rw [hbt]; exact hfx
    obtain ⟨d, hdc, hd, hcd, hends⟩ := exists_free_end hw.fin hw.paired hc
    have hdv : f (spe W d) = v :=
      ((hw.pres.2.2 _ (spe_mem c) _ (spe_mem d)).mpr hcd).symm.trans hcv
    have heq : {a : SE W | f (spe W a) = v ∧ prtL W ∅ a = a} = {c, d} := by
      ext a
      constructor
      · rintro ⟨hav, ha⟩
        exact hends a ((hw.pres.2.2 _ (spe_mem c) _ (spe_mem a)).mp (hcv.trans hav.symm)) ha
      · rintro (rfl | rfl)
        · exact ⟨hcv, hc⟩
        · exact ⟨hdv, hd⟩
    rw [heq, ncard_pair hdc.symm]
  · rw [ite_eq_right hbd]
    have heq : {a : SE W | f (spe W a) = v ∧ prtL W ∅ a = a} = ∅ := by
      apply eq_empty_iff_forall_notMem.mpr
      rintro a ⟨hav, ha⟩
      exact hbd (hav ▸ hfixed_bd a ha)
    rw [heq, ncard_empty]

end GraphMinor.GM08
