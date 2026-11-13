module

public import GraphMinor.GM08.Defs
public import GraphMinor.GM08.Section15Defs
public import GraphMinor.GM08.Section14
import GraphMinor.GM08.Section15CylinderCut
import GraphMinor.GM08.Section15ArcPullback
import GraphMinor.GM08.Section15ArcReconstruction
import GraphMinor.GM07.CutStages

/-!
# The disc graft obtained by opening a cylinder

Cut a normal proper arc joining distinct cuffs. The surface is a disc,
the drawing lifts, and its boundary-rooted graft has the counted index.
Identifying the paired boundary vertices recovers the original graft.
This is the disc-graft construction in the short-tube proof of (15.4)
when the framing boundaries are the cuffs.
-/

public section

namespace GraphMinor.GM08

open Set GraphMinor.Surface

universe w

/-- A normal proper cuff-joining arc opens a boundary-rooted cylinder
graft into a disc graft with the stated index bound. The original is
recovered by root identifications and an isomorphism, as in the
short-tube step of VIII (15.4), page 282. -/
theorem exists_disc_graft_of_normal_cylinder_arc {S : Type w} [TopologicalSpace S]
    (hS : IsCylinder S) {G : Drawing S} (hG : G.IsProper)
    {F C D : Set S} {u v : S} (hC : C ∈ cuffs S) (hD : D ∈ cuffs S)
    (hCD : C ≠ D) (hu : u ∈ C) (hv : v ∈ D) (hF : IsLineWithEnds F u v)
    (hbd : F ∩ bd S = {u, v}) (hn : G.IsNormal F)
    (X : Graft S (Set S)) (hXG : X.G = G.toGraph) (hXT : X.T = G.V ∩ bd S) :
    ∃ (Y : Type w) (_ : TopologicalSpace Y) (A : Graft Y (Set S)),
      IsClosedDisc (univ : Set Y) ∧ EmbedsGraft Y A ∧
      A.index ≤ X.index + 2 * (G.V ∩ F).ncard ∧
      ∃ (n : ℕ) (Z : Graft Y (Set S)), ObtainedByVertexIdChain n A Z ∧ IsGraftIso Z X := by
  have : T2Space S := hS.t2Space
  have huv : u ≠ v := fun he => disjoint_left.mp (cuffs_disjoint hC hD hCD) hu (he ▸ hv)
  obtain ⟨Y, tY, ψ, hY, hdisc, hc, _⟩ :=
    exists_disc_cut_of_cylinder_arc hS hC hD hCD hu hv hF hbd
  have hcut := GM07.IsCutAlongSet.of_isCutting hY hS.1 hF.isCompact.isClosed hc
  obtain ⟨G', hp, hG', he⟩ :=
    exists_pullback_drawing_of_normal_arc hS.1 huv hF hbd.subset hcut G hG hn
  obtain ⟨A, hdraw, hindex, n, Z, hchain, hiso⟩ :=
    exists_graft_reconstruction_of_arc_cut hS.1 hcut hc hp hG' he X hXG hXT
  exact ⟨Y, tY, A, hdisc, hdraw, hindex, n, Z, hchain, hiso⟩

end GraphMinor.GM08
