module

public import GraphMinor.Surface.Defs
public import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import GraphMinor.GM11.Regions

/-!
# Compact drawing pieces on a rim away from an attachment

For the local enclosure in VI (5.5), page 130, the two separation
sides meet only at the attachment, which the rim avoids. A region
of the retained side has its frontier in that side. Thus intersecting
the discarded side on the rim with a region is the same as
intersecting it with the region closure. This proves compactness
without counting the local drawing rays.
-/

public section
namespace GraphMinor.GM06
open Set Topology GraphMinor.Surface

/-- On a compact rim avoiding the attachment, the part of a closed
other side in any retained region is compact. -/
theorem isCompact_rim_piece_in_region
    {S : Type*} [TopologicalSpace S] [T2Space S] [LocallyConnectedSpace S] {T : Drawing S}
    {H : Set S} (hH : IsClosed H) {s : S} (hover : H ∩ T.U ⊆ {s})
    (ψ : C(Circle, S)) (hs : s ∉ range ψ)
    {r : Set S} (hr : r ∈ T.R) :
    IsCompact (ψ ⁻¹' (H ∩ r)) := by
  have he : ψ ⁻¹' (H ∩ r) = ψ ⁻¹' (H ∩ closure r) := by
    ext w
    constructor
    · intro hw
      exact ⟨hw.1, subset_closure hw.2⟩
    · rintro ⟨hwH, hwcl⟩
      refine ⟨hwH, ?_⟩
      rcases GraphMinor.GM11.closure_region_subset hr hwcl with hwr | hwT
      · exact hwr
      · have heq : ψ w = s := hover ⟨hwH, hwT⟩
        exact False.elim (hs ⟨w, heq⟩)
  rw [he]
  exact ((hH.inter isClosed_closure).preimage ψ.continuous).isCompact

end GraphMinor.GM06
