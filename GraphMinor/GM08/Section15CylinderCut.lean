module

public import GraphMinor.GM08.Section15Defs
public import GraphMinor.Surface.TopologyStatements
import GraphMinor.Surface.CutIArc
import Lean.Elab.Tactic.Omega

/-!
# Opening a cylinder into a disc

Cut a proper arc joining the two cuffs. The arc-cut theorem leaves the
handle and crosscap counts fixed and removes one cuff. The classification
of the source cylinder forces the cut surface to be a disc. This is the
surface construction used to open short tubes in VIII (15.4).
-/

public section

namespace GraphMinor.GM08

open Set GraphMinor.Surface

universe w

/-- A cylinder cut along a proper arc joining its distinct cuffs is a
disc. This is the topological step behind the inclusion of short tubes
in `W(ℬ)` in Graph Minors VIII (15.4), page 282. -/
theorem exists_disc_cut_of_cylinder_arc {S : Type w} [TopologicalSpace S]
    (hS : IsCylinder S) {F C D : Set S} {u v : S}
    (hC : C ∈ cuffs S) (hD : D ∈ cuffs S) (hCD : C ≠ D)
    (hu : u ∈ C) (hv : v ∈ D) (hF : IsLineWithEnds F u v)
    (hbd : F ∩ bd S = {u, v}) :
    ∃ (T : Type w) (_ : TopologicalSpace T) (ψ : T → S),
      IsSurface T ∧ IsClosedDisc (univ : Set T) ∧ IsCutting ψ F ∧
      ∃ A B : Set T, Disjoint A B ∧ A ∪ B = ψ ⁻¹' F ∧
        IsLine A ∧ IsLine B ∧ BijOn ψ A F ∧ BijOn ψ B F := by
  have : ConnectedSpace S := hS.connectedSpace
  have huv : u ≠ v := fun he =>
    disjoint_left.mp (cuffs_disjoint hC hD hCD) hu (he ▸ hv)
  obtain ⟨T, tT, ψ, hT, hcut, hdiff, _, hlifts⟩ :=
    cutIArc S F u v hS.1 inferInstance huv hbd hF
  have hc : connectedComponentIn (bd S) u = C := by
    obtain ⟨x, hx, rfl⟩ := hC
    exact (connectedComponentIn_eq hu).symm
  have hd : connectedComponentIn (bd S) v = D := by
    obtain ⟨x, hx, rfl⟩ := hD
    exact (connectedComponentIn_eq hv).symm
  obtain ⟨_, a, b, c, ⟨eS⟩, ⟨eT⟩⟩ := hdiff (by rw [hc, hd]; exact hCD)
  obtain ⟨eC⟩ := hS.2
  obtain ⟨hcc, hgen, _⟩ := (modelCriterion.2 a b (c + 1) 0 0 2).mp ⟨eS.symm.trans eC⟩
  have ha : a = 0 := by omega
  have hb : b = 0 := by omega
  have hc' : c = 1 := by omega
  subst a b c
  obtain ⟨eD⟩ := nonempty_disc_homeo
  exact ⟨T, tT, ψ, hT,
    ⟨eD.symm.trans (eT.symm.trans (Homeomorph.Set.univ T).symm)⟩, hcut, hlifts⟩

end GraphMinor.GM08
