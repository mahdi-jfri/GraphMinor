module

public import GraphMinor.Surface.Defs
import Mathlib.Order.Interval.Set.Infinite
import Mathlib.Topology.Order.Compact

/-!
# Choosing cut points outside a finite set

The minimum-size argument of Graph Minors VI (4.2), claim (2), shrinks
an interval while retaining the boundary vertices of a component. A
finite set inside an open interval has cut points on either side,
chosen outside the whole vertex set. These give the new interval ends.
-/

public section

namespace GraphMinor.GM06

open Set

/-- A nonempty finite set in an open parameter interval fits strictly
between two cut points avoiding any prescribed finite set. -/
theorem exists_inner_interval_cover_finite
    {V W : Set unitInterval} (hV : V.Finite) (hW : W.Finite) (hWne : W.Nonempty)
    {l r : unitInterval} (hWlr : W ⊆ Ioo l r) :
    ∃ p ∈ Ioo l r \ V, ∃ q ∈ Ioo l r \ V,
      p < q ∧ W ⊆ Ioo p q := by
  obtain ⟨wlo, hwlo⟩ := hW.isCompact.exists_isLeast hWne
  obtain ⟨whi, hwhi⟩ := hW.isCompact.exists_isGreatest hWne
  obtain ⟨p, hp, hpV⟩ := (Ioo_infinite (hWlr hwlo.1).1).exists_notMem_finite hV
  obtain ⟨q, hq, hqV⟩ := (Ioo_infinite (hWlr hwhi.1).2).exists_notMem_finite hV
  have hpq : p < q := hp.2.trans_le (hwlo.2 hwhi.1) |>.trans hq.1
  refine ⟨p, ⟨⟨hp.1, hp.2.trans (hWlr hwlo.1).2⟩, hpV⟩,
    q, ⟨⟨(hWlr hwhi.1).1.trans hq.1, hq.2⟩, hqV⟩, hpq, ?_⟩
  intro w hw
  exact ⟨hp.2.trans_le (hwlo.2 hw), (hwhi.2 hw).trans_lt hq.1⟩

end GraphMinor.GM06
