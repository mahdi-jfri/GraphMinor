module

public import GraphMinor.GM06.Defs
public import GraphMinor.Surface.DiscGrow
import GraphMinor.GM06.Section5RetainedPuncturedBarrier
import GraphMinor.GM06.Section5SphereRegions
import GraphMinor.GM06.Section5DiscSphereEmbedding

/-!
# A punctured barrier containing the cut-disc boundary

For the one-path Reduction 2 argument of VI (5.5), page 130,
the cut boundary minus the chosen initial copy is connected. Its
actual component in the vertex-deleted graph therefore gives a
punctured barrier containing the whole boundary. A boundary arc
starting at the attachment proves accumulation of the puncture
there. This replaces the two-linkage-path cuff argument on the cut disc.
-/

public section
namespace GraphMinor.GM06
open Set Topology GraphMinor.Surface

/-- Construct the actual cuff replacement barrier on a closed disc
from its boundary with one attachment point removed. -/
theorem exists_punctured_barrier_containing_disc_boundary
    {S : Type} [TopologicalSpace S] [T2Space S] (hDisc : IsClosedDiscSpace S)
    (Γ : Drawing S) (hbdΓ : bd S ⊆ Γ.U)
    {s w : S} (hs : s ∈ Γ.V) (hw : w ∈ Γ.V)
    (hsb : s ∈ bd S) (hwb : w ∈ bd S) (hsw : s ≠ w) :
    ∃ T R : Drawing S, T.IsSubdrawing Γ ∧ bd S ⊆ T.U ∧ s ∈ T.V ∧
      IsConnected (T.U \ {s}) ∧ s ∈ closure (T.U \ {s}) ∧
      IsGraphSeparation Γ.toGraph R.toGraph T.toGraph ∧ R.U ∩ T.U ⊆ {s} := by
  have hX := (isPathConnected_oArc_diff hDisc.isOArc_bd hsb).isConnected
  have hXΓ : bd S \ {s} ⊆ Γ.U := fun x hx => hbdΓ hx.1
  obtain ⟨T, R, hTΓ, hsT, hXT, hconn, hsep, hover⟩ :=
    exists_punctured_barrier_separation_containing_preconnected_set Γ hs hX.isPreconnected
      hXΓ (fun h => h.2 rfl) (show w ∈ bd S \ {s} from ⟨hwb, hsw.symm⟩) hw
  have hbdT : bd S ⊆ T.U := by
    intro x hxb
    by_cases he : x = s
    · exact he ▸ T.V_subset_U hsT
    · exact hXT ⟨hxb, he⟩
  obtain ⟨a, _, hab, ha0, _, hrange⟩ := hDisc.isOArc_bd.exists_arcs hsb hwb hsw
  have h0cl : (0 : unitInterval) ∈ closure (Ioo (0 : unitInterval) 1) := by
    rw [closure_Ioo (show (0 : unitInterval) ≠ 1 from zero_ne_one)]
    exact ⟨bot_le, le_top⟩
  have hsub : a '' Ioo (0 : unitInterval) 1 ⊆ T.U \ {s} := by
    rintro x ⟨t, ht, rfl⟩
    refine ⟨hbdT (hrange ▸ Or.inl (mem_range_self t)), ?_⟩
    intro he
    exact ht.1.ne' (hab.arc_left.2 (he.trans ha0.symm))
  have hscl : s ∈ closure (T.U \ {s}) := by
    have hh := mem_closure_image hab.arc_left.1.continuousAt h0cl
    rw [ha0] at hh
    exact closure_mono hsub hh
  exact ⟨T, R, hTΓ, hbdT, hsT, hconn, hscl, hsep, hover⟩

end GraphMinor.GM06
