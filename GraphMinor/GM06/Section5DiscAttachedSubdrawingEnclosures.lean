module

public import GraphMinor.GM06.Defs
public import GraphMinor.Surface.DiscGrow
import GraphMinor.GM06.Section5DiscBoundaryPuncturedBarrier
import GraphMinor.GM06.Section5DiscSpaceAttachedEnclosures
import GraphMinor.GM06.Section5SeparationGeometry
import GraphMinor.GM11.Walks

/-!
# Enclosing the discarded side attached to a cut-disc boundary

For VI (5.5), page 130, the retained closed side contains the
cut boundary and meets the discarded subdrawing only at one
boundary vertex. The punctured boundary component barrier stays
in the retained side by connectedness. Its other graph-separation
side contains every discarded point away from the attachment.
Apply the constructed finite disc enclosures to that actual side.
-/

public section
namespace GraphMinor.GM06
open Set Topology GraphMinor.Surface

/-- A subdrawing attached to a closed retained side only at one
disc-boundary vertex has finite actual disc enclosures meeting
the full drawing and the boundary only there. -/
theorem exists_disc_space_enclosures_for_attached_subdrawing
    {S : Type} [TopologicalSpace S] [T2Space S] (hDisc : IsClosedDiscSpace S)
    {Γ H : Drawing S} (hHΓ : H.IsSubdrawing Γ) (hbdΓ : bd S ⊆ Γ.U)
    {s w : S} (hsV : s ∈ Γ.V) (hwV : w ∈ Γ.V)
    (hsb : s ∈ bd S) (hwb : w ∈ bd S) (hsw : s ≠ w)
    {A : Set S} (hAc : IsClosed A) (hbdA : bd S ⊆ A)
    (hcover : Γ.U ⊆ A ∪ H.U) (hover : A ∩ H.U ⊆ {s}) :
    ∃ F : Set (Set S), F.Finite ∧
      (∀ D ∈ F, IsClosedDisc D ∧ discBd D ∩ Γ.U ⊆ {s} ∧ D ∩ bd S ⊆ {s}) ∧
      H.U \ {s} ⊆ ⋃ D ∈ F, discInt D := by
  obtain ⟨T, R, hTΓ, hbdT, hsT, hTp, hscl, hsep, hRT⟩ :=
    exists_punctured_barrier_containing_disc_boundary hDisc Γ hbdΓ hsV hwV hsb hwb hsw
  have hRΓ : R.IsSubdrawing Γ := ⟨hsep.1.vertexSet_mono, hsep.1.edgeSet_mono⟩
  have hsets := point_sets_of_graph_separation hsep
  have hcoverP : T.U \ {s} ⊆ A ∪ H.U := fun x hx => hcover (hTΓ.U_subset hx.1)
  have hinter : (T.U \ {s}) ∩ (A ∩ H.U) = ∅ := by
    apply eq_empty_iff_forall_notMem.mpr
    rintro x ⟨hxP, hxAH⟩
    exact hxP.2 (hover hxAH)
  have hPA : T.U \ {s} ⊆ A := by
    rcases isPreconnected_iff_subset_of_disjoint_closed.mp hTp.isPreconnected
      A H.U hAc H.isClosed_U hcoverP hinter with h | h
    · exact h
    · have hwP : w ∈ T.U \ {s} := ⟨hbdT hwb, hsw.symm⟩
      exact False.elim (hsw.symm (hover ⟨hbdA hwb, h hwP⟩))
  have hHT : H.U ∩ T.U ⊆ {s} := by
    rintro x ⟨hxH, hxT⟩
    by_cases hxs : x = s
    · exact hxs
    · exact hover ⟨hPA ⟨hxT, hxs⟩, hxH⟩
  have hHR : H.U \ {s} ⊆ R.U \ {s} := by
    rintro x ⟨hxH, hxs⟩
    have hxΓ := hHΓ.U_subset hxH
    rw [← hsets.1] at hxΓ
    exact ⟨hxΓ.resolve_right (fun hxT => hxs (hHT ⟨hxH, hxT⟩)), hxs⟩
  have hΓTR : Γ.U ⊆ T.U ∪ R.U := by rw [union_comm, hsets.1]
  obtain ⟨F, hF, hdisc, hcov⟩ := exists_disc_space_discs_enclosing_attached_side
    hDisc hTΓ hRΓ hsV hwV hsb hwb hsw (T.V_subset_U hsT) hTp hscl hbdT hRT hΓTR
  exact ⟨F, hF, hdisc, hHR.trans hcov⟩

end GraphMinor.GM06
