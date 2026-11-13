module

public import GraphMinor.Surface.Defs
import Mathlib.Topology.Order.IntermediateValue

/-!
# A portion of a curve crossing a closed band

For the region argument in Graph Minors VI (4.2), claim (2), a plane
curve from inside the hole to outside the cylinder has a portion in the
closed annulus joining its two boundary circles. We first prove the
scalar fact, taking the first upper-level hit and the last lower-level
hit before it.
-/

public section

namespace GraphMinor.GM06

open Set

/-- A continuous function starting below a band and ending above it has
a closed subinterval crossing the band and staying inside it. -/
theorem exists_subinterval_crossing_band
    (a : C(unitInterval, ℝ)) {lo hi : ℝ} (hlohi : lo < hi)
    (ha0 : a 0 ≤ lo) (ha1 : hi ≤ a 1) :
    ∃ s t : unitInterval, s < t ∧ a s = lo ∧ a t = hi ∧
      ∀ v ∈ Icc s t, a v ∈ Icc lo hi := by
  have hupper : (a ⁻¹' {hi}).Nonempty := by
    obtain ⟨v, _, hv⟩ := intermediate_value_Icc
      (show (0 : unitInterval) ≤ 1 from zero_le_one) a.continuous.continuousOn
      (show hi ∈ Icc (a 0) (a 1) from ⟨ha0.trans hlohi.le, ha1⟩)
    exact ⟨v, hv⟩
  obtain ⟨t, ht⟩ := (isClosed_singleton.preimage a.continuous).isCompact.exists_isLeast hupper
  have hat : a t = hi := ht.1
  have hbound : ∀ v ≤ t, a v ≤ hi := by
    intro v hvt
    by_contra hn
    have hav : hi ≤ a v := (not_le.mp hn).le
    obtain ⟨w, hw, haw⟩ := intermediate_value_Icc
      (show (0 : unitInterval) ≤ v from bot_le) a.continuous.continuousOn
      (show hi ∈ Icc (a 0) (a v) from ⟨ha0.trans hlohi.le, hav⟩)
    have htw : t ≤ w := ht.2 haw
    have hvt' : v = t := le_antisymm hvt (htw.trans hw.2)
    exact hn (hvt' ▸ hat.le)
  let L := a ⁻¹' {lo} ∩ Iic t
  have hLc : IsCompact L :=
    ((isClosed_singleton.preimage a.continuous).inter isClosed_Iic).isCompact
  have hLn : L.Nonempty := by
    obtain ⟨v, hv, hav⟩ := intermediate_value_Icc
      (show (0 : unitInterval) ≤ t from bot_le) a.continuous.continuousOn
      (show lo ∈ Icc (a 0) (a t) from ⟨ha0, by rw [hat]; exact hlohi.le⟩)
    exact ⟨v, hav, hv.2⟩
  obtain ⟨s, hs⟩ := hLc.exists_isGreatest hLn
  have has : a s = lo := hs.1.1
  have hst : s < t := lt_of_le_of_ne hs.1.2 (fun h =>
    hlohi.ne (has.symm.trans ((congrArg a h).trans hat)))
  refine ⟨s, t, hst, has, hat, ?_⟩
  intro v hv
  refine ⟨?_, hbound v hv.2⟩
  by_contra hn
  have hav : a v ≤ lo := (not_le.mp hn).le
  obtain ⟨w, hw, haw⟩ := intermediate_value_Icc hv.2 a.continuous.continuousOn
    (show lo ∈ Icc (a v) (a t) from ⟨hav, by rw [hat]; exact hlohi.le⟩)
  have hws : w ≤ s := hs.2 ⟨haw, hw.2⟩
  have hvs : v = s := le_antisymm (hw.1.trans hws) hv.1
  exact hn (hvs ▸ has.ge)

end GraphMinor.GM06
