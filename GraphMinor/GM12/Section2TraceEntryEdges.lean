module

public import GraphMinor.GM12.Section2TraceParameters
import GraphMinor.GM12.Section2TraceReverse
import GraphMinor.GM12.Section2EntryIntervals
import GraphMinor.GM12.Section2EntryEnds
import GraphMinor.GM11.RadialRegions
import GraphMinor.GM11.Walks

/-!
# Every incoming germ is recorded by the trace

For the restriction argument in XII (2.1), pages 243--244, a curve
can be read on a shorter terminal interval than the one used in its
trace. The two intervals have the same region and hub near their
common vertex. Entry uniqueness identifies their incoming edges.
Removing the first region visit proves the assertion for any visit
in the trace interval.
-/

public section

namespace GraphMinor.GM12

open Set Surface GM11

/-- An entry edge read at any vertex parameter after the start of a
trace interval is one of that walk's edges. Its chosen interval may
start before or after the corresponding recorded region interval. -/
theorem traceSteps_mem_edges_of_entersLike
    {S : Type*} [TopologicalSpace S] [T2Space S]
    (hS : IsClosedSurface S) (hConn : ConnectedSpace S)
    {Γ K : Drawing S} (hK : (PaintingOrDrawing.drawing Γ).IsRadialDrawing K)
    {f : ℝ → S} (hf : Continuous f) {a b : ℝ} {u z : S}
    (W : GraphWalk K.toGraph u z) (hW : TraceSteps Γ K f a b W)
    {s d : ℝ} (hs : s ∈ Ioc a b) (hds : d < s)
    {r e : Set S} {v w : S} (hr : r ∈ Γ.R) (hv : v ∈ Γ.V)
    (hw : w ∈ r ∩ K.V) (he : e ∈ K.E) (hfs : f s = v)
    (hfr : ∀ t ∈ Ioo d s, f t ∈ r) (hentry : EntersLike f d s e r v w) :
    e ∈ W.edges := by
  cases hWcase : W with
  | nil hu =>
    rw [hWcase] at hW
    exact (not_lt_of_ge (hs.2.trans_eq hW.1.symm) hs.1).elim
  | cons hlink rest =>
    rw [hWcase] at hW
    cases hrestcase : rest with
    | nil hu => rw [hrestcase] at hW; exact hW.elim
    | @cons _ x _ e₀ hlink' tail =>
      rw [hrestcase] at hW
      obtain ⟨c, hac, hfa, hu, hfc, hwK, r₀, hr₀, hwr₀, hfr₀, _, henter₀, htail⟩ := hW
      have hcs : c ≤ s := by
        by_contra hn
        exact region_subset hr₀ (hfr₀ s ⟨hs.1, lt_of_not_ge hn⟩)
          (Γ.V_subset_U (hfs.symm ▸ hv))
      by_cases hsc : s = c
      · subst s
        have hxv : x = v := hfc.symm.trans hfs
        rw [← hxv] at hv hentry hfs
        let m := (max a d + c) / 2
        have hmc : m < c := by dsimp [m]; linarith [max_lt hac hds]
        have ham : a < m := (le_max_left a d).trans_lt (by dsimp [m]; linarith [max_lt hac hds])
        have hdm : d < m := (le_max_right a d).trans_lt (by dsimp [m]; linarith [max_lt hac hds])
        have hrr : r₀ = r := region_eq_of_mem hr₀ hr (hfr₀ m ⟨ham, hmc⟩) (hfr m ⟨hdm, hmc⟩)
        subst r₀
        have hww := hub_unique (show PreRad (.drawing Γ) K from ⟨hK.1, hK.2.1⟩)
          hr hw.1 hw.2 hwr₀ hwK
        subst w
        have hends := (entersLike_isLink hS ⟨hK.1, hK.2.1⟩ hr hv hwr₀ hwK he hfs hentry).2.2.2
        have hends₀ := (entersLike_isLink hS ⟨hK.1, hK.2.1⟩ hr hv hwr₀ hwK hlink'.1 hfc henter₀).2.2.2
        have heq := entersLike_edge_unique_overlapping_intervals hS hConn hK hr hv
          ⟨hwr₀, hwK⟩ he hlink'.1 hends hends₀ hf hds hac hfs hfr hfr₀ hentry henter₀
        simp only [GraphWalk.edges, List.mem_cons]
        exact Or.inr (Or.inl heq)
      · have hcs' : c < s := lt_of_le_of_ne hcs (Ne.symm hsc)
        have hmem := traceSteps_mem_edges_of_entersLike hS hConn hK hf tail htail
          ⟨hcs', hs.2⟩ hds hr hv hw he hfs hfr hentry
        simp only [GraphWalk.edges, List.mem_cons]
        exact Or.inr (Or.inr hmem)
termination_by W.length

decreasing_by
  simp_all only [GraphWalk.length, GraphWalk.edges, List.length_cons]
  omega

/-- Every outgoing germ at a vertex parameter before the end of a
trace interval is recorded as well. Reverse the parameter interval
and use the incoming-germ assertion. -/
theorem traceSteps_mem_edges_of_leavesLike
    {S : Type*} [TopologicalSpace S] [T2Space S]
    (hS : IsClosedSurface S) (hConn : ConnectedSpace S)
    {Γ K : Drawing S} (hK : (PaintingOrDrawing.drawing Γ).IsRadialDrawing K)
    {f : ℝ → S} (hf : Continuous f) {a b : ℝ} {u z : S}
    (W : GraphWalk K.toGraph u z) (hW : TraceSteps Γ K f a b W)
    {s d : ℝ} (hs : s ∈ Ico a b) (hsd : s < d)
    {r e : Set S} {v w : S} (hr : r ∈ Γ.R) (hv : v ∈ Γ.V)
    (hw : w ∈ r ∩ K.V) (he : e ∈ K.E) (hfs : f s = v)
    (hfr : ∀ t ∈ Ioo s d, f t ∈ r) (hleave : LeavesLike f s d e r v w) :
    e ∈ W.edges := by
  have hmem := traceSteps_mem_edges_of_entersLike hS hConn hK
    (hf.comp continuous_neg) W.reverse (traceSteps_reverse W hW)
    (s := -s) (d := -d) ⟨neg_lt_neg hs.2, neg_le_neg hs.1⟩ (neg_lt_neg hsd)
    hr hv hw he (by simpa only [Function.comp_apply, neg_neg] using hfs)
    (fun t ht => hfr (-t) ⟨by linarith [ht.2], by linarith [ht.1]⟩) hleave
  simpa only [GraphWalk.edges_reverse, List.mem_reverse] using hmem

end GraphMinor.GM12
