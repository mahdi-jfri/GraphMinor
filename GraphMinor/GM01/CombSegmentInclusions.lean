module

public import GraphMinor.GM01.CombShiftRanges

/-!
# Inclusion between represented comb intervals

Graph Minors I, (4.14), page 59, joins the middle cells to the two
outer pieces through the ends. A path through the first end and its
next spine edge remains in the first three cells. Containment of
cell intervals implies containment of their represented supports,
for both centres and replacing paths.
-/

public section

namespace GraphMinor.GM01

open Set Graph SimpleGraph

/-- Containment of source cell intervals gives containment of their
subdivision supports, as used for the joins in GM01 (4.14), page 59. -/
theorem combSegmentSupport_mono {α β : Type*} {γ L m m' : ℕ}
    (c : (pathComb γ L).verts → α) (P : (pathComb γ L).coe.edgeSet → Graph α β)
    (offset offset' : ℕ) (hbound : offset + m ≤ L) (hbound' : offset' + m' ≤ L)
    (hlo : offset' ≤ offset) (hhi : offset + m ≤ offset' + m') :
    combSegmentSupport c P offset hbound ⊆ combSegmentSupport c P offset' hbound' := by
  intro x hx
  apply (mem_combSegmentSupport_iff c P offset' hbound' x).mpr
  rcases (mem_combSegmentSupport_iff c P offset hbound x).mp hx with ⟨v, hv, hv', hvx⟩ | ⟨e, hxe, hEnds⟩
  · exact Or.inl ⟨v, hlo.trans hv, hv'.trans_le hhi, hvx⟩
  · refine Or.inr ⟨e, hxe, ?_⟩
    intro v hv
    have h := hEnds v hv
    exact ⟨hlo.trans h.1, h.2.trans_le hhi⟩

end GraphMinor.GM01
