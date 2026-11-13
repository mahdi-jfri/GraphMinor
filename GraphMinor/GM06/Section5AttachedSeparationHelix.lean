module

public import GraphMinor.GM06.Defs
import GraphMinor.GM06.Section5AdjoinBoundary
import GraphMinor.GM06.Section5MultiplePathPuncturedBarrier
import GraphMinor.GM06.Section5InitialVertexPolar
import GraphMinor.GM06.Section5BarrierHelixAvoidance
import GraphMinor.GM06.Section5SeparationGeometry
import GraphMinor.GM06.Section5SeparationHelices
import GraphMinor.GM06.Section4PathTools

/-!
# Reduction 2 with at least two linkage paths

For VI (5.5), page 130, adjoin the cuffs and choose the actual
punctured component barrier containing them. The discarded side
meets that barrier only at the separation vertex: connectedness
keeps its puncture on the retained side. Construct the finite
sphere enclosures, pull them back to the cylinder, and perform
their helix detours. The new helix avoids the discarded side except
at the attachment and therefore is an old-drawing helix with the
same potential as in the retained drawing.
-/

public section
namespace GraphMinor.GM06
open Set Topology GraphMinor.Surface

/-- The case of VI (5.5), Reduction 2, with at least two paths.
The enclosure discs and all detours are constructed from the actual
separation, with no assumed enclosure or avoidance step. -/
theorem theorem_5_5_red2_of_two_le
    {k : ℕ} {G G₁ G₂ : Drawing ClosedCylinder}
    (L : CylinderLinkage k G) (L₁ : CylinderLinkage k G₁)
    (hk : 1 < k) (hG : IsCylinderSection5Drawing k G) (hG₁ : IsCylinderSection5Drawing k G₁)
    (i : Fin k) (hsep : IsGraphSeparation G.toGraph G₁.toGraph G₂.toGraph)
    (hover : G₁.V ∩ G₂.V ⊆ {cylinderM1Point k i})
    (f : Curve ClosedCylinder) (hf : IsHelix k G₁ f) :
    ∃ g : Curve ClosedCylinder, IsHelix k G g ∧ curvePhi k G g ≤ curvePhi k G₁ f := by
  let s := cylinderM1Point k i
  have h₁ : G₁.IsSubdrawing G := ⟨hsep.1.vertexSet_mono, hsep.1.edgeSet_mono⟩
  have h₂ : G₂.IsSubdrawing G := ⟨hsep.2.1.vertexSet_mono, hsep.2.1.edgeSet_mono⟩
  have hgeom := discarded_side_meets_retained_and_boundary_only_at_initial hG hG₁ i hsep hover
  have hsets := point_sets_of_graph_separation hsep
  obtain ⟨Γ, hGΓ, hΓU, _⟩ := exists_drawing_adjoining_boundary L hG
  have h₁Γ : G₁.IsSubdrawing Γ := ⟨h₁.1.trans hGΓ.1, h₁.2.trans hGΓ.2⟩
  have hbdΓ : bd ClosedCylinder ⊆ Γ.U := hΓU ▸ subset_union_right
  obtain ⟨T, R, hTΓ, hbdT, hsT, hTp, hscl, hRT, hRTmeet⟩ :=
    exists_multiple_path_punctured_cuff_barrier_separation L₁ hk h₁Γ hbdΓ i
  have hRΓ : R.IsSubdrawing Γ := ⟨hRT.1.vertexSet_mono, hRT.1.edgeSet_mono⟩
  have hRTsets := point_sets_of_graph_separation hRT
  let A := G₁.U ∪ bd ClosedCylinder
  let B := G₂.U
  have hAB : A ∩ B ⊆ {s} := by
    rintro x ⟨hx | hx, hxB⟩
    · exact hgeom.1 ⟨hx, hxB⟩
    · exact hgeom.2 ⟨hxB, hx⟩
  have hcover : T.U \ {s} ⊆ A ∪ B := by
    intro x hx
    have hxΓ := hTΓ.U_subset hx.1
    rw [hΓU, ← hsets.1] at hxΓ
    rcases hxΓ with (hx | hx) | hx
    · exact Or.inl (Or.inl hx)
    · exact Or.inr hx
    · exact Or.inl (Or.inr hx)
  have hinter : (T.U \ {s}) ∩ (A ∩ B) = ∅ := by
    apply eq_empty_iff_forall_notMem.mpr
    rintro x ⟨hx, hxAB⟩
    exact hx.2 (hAB hxAB)
  have hPA : T.U \ {s} ⊆ A := by
    rcases isPreconnected_iff_subset_of_disjoint_closed.mp hTp.isPreconnected A B
      (G₁.isClosed_U.union (isClosed_bd ClosedCylinder)) G₂.isClosed_U hcover hinter with h | h
    · exact h
    · let a := cylinderM2Point k i
      have ha2 : a ∈ cylinderCuff2 := rfl
      have has : a ≠ s := by
        intro he
        have hs2 : s ∈ cylinderCuff2 := he ▸ ha2
        change (1 : ℝ) = 2 at hs2
        norm_num at hs2
      have habd : a ∈ bd ClosedCylinder := by rw [bd_closedCylinder]; exact Or.inr ha2
      have haP : a ∈ T.U \ {s} := ⟨hbdT habd, has⟩
      exact False.elim (has (hgeom.2 ⟨h haP, habd⟩))
  have hT₂ : T.U ∩ G₂.U ⊆ {s} := by
    rintro x ⟨hxT, hx₂⟩
    by_cases hxs : x = s
    · exact hxs
    · exact hAB ⟨hPA ⟨hxT, hxs⟩, hx₂⟩
  have h₂R : G₂.U \ {s} ⊆ R.U := by
    rintro x ⟨hx₂, hxs⟩
    have hxΓ := hGΓ.U_subset (h₂.U_subset hx₂)
    rw [← hRTsets.1] at hxΓ
    exact hxΓ.resolve_right (fun hxT => hxs (hT₂ ⟨hxT, hx₂⟩))
  obtain ⟨Φ, hp⟩ := exists_polar_at_initial_vertex_of_cuffs L₁ hk h₁Γ hbdΓ i
  have hs₁ : s ∈ G₁.V := (L₁.isSubdrawing i).1.1 (isPathDrawing_end_vertices (L₁.isPath i)).1
  have hΓcover : Γ.U ⊆ T.U ∪ R.U := by rw [union_comm, hRTsets.1]
  obtain ⟨g, hg, havoidR, hφ⟩ := exists_helix_avoiding_other_side_of_punctured_barrier
    h₁Γ hTΓ hRΓ hs₁ (T.V_subset_U hsT) hTp hscl hbdT hRTmeet hΓcover hp f hf
  have havoid₂ : range g ∩ G₂.U ⊆ {s} := by
    intro x hx
    by_cases hxs : x = s
    · exact hxs
    · exact havoidR ⟨hx.1, h₂R ⟨hx.2, hxs⟩⟩
  obtain ⟨hgOld, heq⟩ := helix_of_separation_avoids_discarded_side hsep hs₁ g hg havoid₂
  exact ⟨g, hgOld, heq.le.trans hφ⟩

end GraphMinor.GM06
