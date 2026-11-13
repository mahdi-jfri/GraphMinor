module

public import GraphMinor.GM06.Section5CapDrawing
public import GraphMinor.GM11.LocalCone
import GraphMinor.GM06.Section5CylinderAttachedEnclosures
import GraphMinor.GM06.Section5MixedDiscAvoidance

/-!
# Helix avoidance from an actual punctured barrier

For Reduction 2 in VI (5.5), page 130, construct the finite disc
cover of the other barrier side and perform its ordinary and attached
detours. Each boundary meets the full augmented drawing only at
the attachment, so all detours preserve earlier avoidance. The
resulting helix misses that other side away from the attachment.
-/

public section
namespace GraphMinor.GM06
open Set Topology GraphMinor.Surface GraphMinor.GM11

/-- Actual cylinder enclosures and their finite detours avoid the
other side of a cuff-containing punctured barrier. -/
theorem exists_helix_avoiding_other_side_of_punctured_barrier
    {k : ℕ} {G Γ T H : Drawing ClosedCylinder}
    (hGΓ : G.IsSubdrawing Γ) (hT : T.IsSubdrawing Γ) (hH : H.IsSubdrawing Γ)
    {s : ClosedCylinder} (hsG : s ∈ G.V) (hsT : s ∈ T.U)
    (hTp : IsConnected (T.U \ {s})) (hscl : s ∈ closure (T.U \ {s}))
    (hbdT : bd ClosedCylinder ⊆ T.U) (hover : H.U ∩ T.U ⊆ {s})
    (hcover : Γ.U ⊆ T.U ∪ H.U)
    {Φ : C(ClosedUnitDisc, OnePoint EuclideanPlane)}
    (hp : IsPolar (cylinderSphereDrawing Γ) (cylinderToSphere s) Φ)
    (f : Curve ClosedCylinder) (hf : IsHelix k G f) :
    ∃ g : Curve ClosedCylinder, IsHelix k G g ∧ range g ∩ H.U ⊆ {s} ∧
      curvePhi k G g ≤ curvePhi k G f := by
  obtain ⟨F, hF, hdisc, hcov⟩ := exists_cylinder_discs_enclosing_attached_side
    hT hH hsT hTp hscl hbdT hover hcover hp
  have hbd : ∀ D ∈ F, discBd D ∩ (G.U ∪ (H.U \ {s})) ⊆ {s} := by
    intro D hD y hy
    apply (hdisc D hD).2
    refine ⟨hy.1, ?_⟩
    rcases hy.2 with hyG | hyH
    · exact hGΓ.U_subset hyG
    · exact hH.U_subset hyH.1
  obtain ⟨g, hg, hga, hφ⟩ := exists_helix_avoiding_finitely_enclosed_set_with_attachment
    hsG hF (H.U \ {s}) (fun h => h.2 rfl) (fun D hD => (hdisc D hD).1) hbd hcov f hf
  refine ⟨g, hg, ?_, hφ⟩
  intro y hy
  by_contra hys
  exact disjoint_left.mp hga hy.1 ⟨hy.2, hys⟩

end GraphMinor.GM06
