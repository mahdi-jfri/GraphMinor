module

public import GraphMinor.GM11.Defs
import GraphMinor.GM11.Ties
import GraphMinor.Surface.DiscGrow
import Mathlib.Topology.Order.IntermediateValue

/-!
# Ends of a line in a drawing

For the line case of the tie selection in XII (7.3), page 262,
we need a path along a line in the drawing. First its ends must
be vertices. A subline containing an end of a larger line has
that point as an end too: in interval coordinates its parameter
map is strictly monotone or strictly antitone. An end of the
whole line therefore cannot lie in the interior of a drawing
edge. A circle edge is excluded because a line contains no circle.
-/

public section

namespace GraphMinor.GM12

open Set Topology Surface GM11

private theorem interval_end_preimage
    {g : unitInterval → unitInterval} (hg : Continuous g) (hi : Function.Injective g)
    {t : unitInterval} (ht : g t = 0 ∨ g t = 1) : t = 0 ∨ t = 1 := by
  rcases hg.strictMono_of_inj_boundedOrder' hi with hm | hm
  · rcases ht with ht | ht
    · left
      apply hi
      exact ht.trans (le_antisymm ((hm.monotone (show (0 : unitInterval) ≤ t from bot_le)).trans_eq ht) bot_le).symm
    · right
      apply hi
      have h := hm.monotone (show t ≤ (1 : unitInterval) from le_top)
      rw [ht] at h
      exact ht.trans (le_antisymm le_top h).symm
  · rcases ht with ht | ht
    · right
      apply hi
      exact ht.trans (le_antisymm ((hm.antitone (show t ≤ (1 : unitInterval) from le_top)).trans_eq ht) bot_le).symm
    · left
      apply hi
      have h := hm.antitone (show (0 : unitInterval) ≤ t from bot_le)
      rw [ht] at h
      exact ht.trans (le_antisymm le_top h).symm

/-- If a subline contains an end of a larger line, that point is
one of the ends of the subline. -/
theorem line_end_mem_pair_of_subset
    {S : Type*} [TopologicalSpace S] {L M : Set S} {a b p q z : S}
    (hM : IsLineWithEnds M a b) (hL : IsLineWithEnds L p q)
    (hsub : L ⊆ M) (hz : z = a ∨ z = b) (hzL : z ∈ L) : z = p ∨ z = q := by
  obtain ⟨e, he0, he1⟩ := hM
  obtain ⟨f, hf, hfr, hf0, hf1⟩ := hL.exists_arc
  let g : unitInterval → unitInterval := fun t => e.symm ⟨f t, hsub (hfr ▸ mem_range_self t)⟩
  have hgc : Continuous g := e.symm.continuous.comp (hf.1.subtype_mk _)
  have hgi : Function.Injective g := by
    intro s t hst
    apply hf.2
    exact congrArg (fun u : M => u.1) (e.symm.injective hst)
  obtain ⟨t, ht⟩ := hfr.symm ▸ hzL
  have hgt : g t = 0 ∨ g t = 1 := by
    rcases hz with hz | hz
    · left
      apply e.injective
      exact (e.apply_symm_apply _).trans (Subtype.ext (ht.trans (hz.trans he0.symm)))
    · right
      apply e.injective
      exact (e.apply_symm_apply _).trans (Subtype.ext (ht.trans (hz.trans he1.symm)))
  rcases interval_end_preimage hgc hgi hgt with rfl | rfl
  · exact Or.inl (ht.symm.trans hf0)
  · exact Or.inr (ht.symm.trans hf1)

/-- When the whole point set of a drawing is a line, both ends
of that line are vertices of the drawing. -/
theorem line_ends_mem_vertices
    {S : Type*} [TopologicalSpace S] [T2Space S] [ConnectedSpace S]
    {N : Drawing S} {a b : S} (hLine : IsLineWithEnds N.U a b) :
    a ∈ N.V ∧ b ∈ N.V := by
  have hend : ∀ z ∈ N.U, z = a ∨ z = b → z ∈ N.V := by
    intro z hz hends
    by_contra hzV
    obtain ⟨e, he, hze⟩ := N.exists_edge_of_mem hz hzV
    have hcl : closure e ⊆ N.U := closure_minimal (fun x hx => (he.2.1 hx).1) N.isClosed_U
    rcases N.edge_cond e he with ⟨p, q, _, hcap, hL⟩ | ⟨_, _, hO⟩
    · have hzp := line_end_mem_pair_of_subset hLine hL hcl hends (subset_closure hze)
      have hzcap : z ∈ closure e ∩ N.V := hcap.symm ▸ hzp
      exact hzV hzcap.2
    · exact not_isOArc_of_subset_line (IsLineWithEnds.isLine hLine) hO hcl
  exact ⟨hend a hLine.left_mem (Or.inl rfl), hend b hLine.right_mem (Or.inr rfl)⟩

end GraphMinor.GM12
