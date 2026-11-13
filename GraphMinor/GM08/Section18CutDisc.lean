module

public import GraphMinor.GM11.Defs
public import GraphMinor.Surface.TopologyStatements
import GraphMinor.GM08.Section18CutSide
import GraphMinor.Surface.CutComp
import GraphMinor.GM07.Section8

/-!
# Excluding a disc component of a circle cut

For a two-sided cut, each component contains one entire lift of the circle.
A disc component maps injectively to a disc containing the original circle,
which makes that circle planar. A one-sided cut is connected. Thus a
non-planar circle has no disc component after cutting. This excludes one
of the outcomes needed in VIII (18.2).
-/

public section

namespace GraphMinor.GM08

open Set Topology GraphMinor.Surface GraphMinor.GM11

universe w

private theorem component_eq_univ {T : Type w} [TopologicalSpace T] [ConnectedSpace T]
    {C : Set T} (hC : C ∈ spaceComponents T) : C = univ := by
  rw [spaceComponents_eq] at hC
  obtain ⟨x, rfl⟩ := hC
  exact PreconnectedSpace.connectedComponent_eq_univ x

private theorem not_cutHasDisc_of_connected {T : Type w} [TopologicalSpace T]
    [ConnectedSpace T] : ¬ CutHasDisc T := by
  rintro ⟨C, D, hne, hcomps, _⟩
  have hC : C ∈ spaceComponents T := hcomps ▸ (Or.inl rfl : C ∈ ({C, D} : Set (Set T)))
  have hD : D ∈ spaceComponents T := hcomps ▸ (Or.inr rfl : D ∈ ({C, D} : Set (Set T)))
  exact hne ((component_eq_univ hC).trans (component_eq_univ hD).symm)

private theorem isPlanar_of_disc_side {S T : Type w} [TopologicalSpace S]
    [TopologicalSpace T] [T2Space S] {ψ : T → S} {F : Set S}
    (hcut : IsCutting ψ F) {W A B : Set T} (hW : IsClosedDisc W)
    (hlifts : A ∪ B = ψ ⁻¹' F) (hBW : Disjoint B W) (hA : BijOn ψ A F)
    (hAW : A ⊆ W) : IsPlanar F := by
  obtain ⟨himage, _⟩ := isClosedDisc_image_cut_side hcut hW hlifts hBW hA.injOn
  refine ⟨ψ '' W, himage, ?_⟩
  intro z hz
  obtain ⟨y, hy, rfl⟩ := hA.surjOn hz
  exact ⟨y, hAW hy, rfl⟩

/-- A non-planar circle cannot give a disc component under a circle cut.
The lift data are those of `Surface.cutOArc`; the proof is a local step
in VIII (18.2), page 286. -/
theorem not_cutHasDisc_of_circle_lifts {S T : Type w} [TopologicalSpace S]
    [TopologicalSpace T] [ConnectedSpace S] (hS : IsSurface S) (hT : IsSurface T)
    {ψ : T → S} {F : Set S} (hcut : IsCutting ψ F)
    (hnot : ¬ IsPlanar F)
    (hlifts : (∃ A B : Set T, Disjoint A B ∧ A ∪ B = ψ ⁻¹' F ∧ IsOArc A ∧ IsOArc B ∧
      BijOn ψ A F ∧ BijOn ψ B F) ∨ IsOArc (ψ ⁻¹' F)) : ¬ CutHasDisc T := by
  have : CompactSpace T := hT.1
  have : T2Space S := hS.2.1
  rcases hlifts with ⟨A, B, _, hun, hA, hB, hbA, hbB⟩ | hpre
  · obtain ⟨x, hx⟩ := (GM07.IsOArc.isConnected hA).nonempty
    obtain ⟨y, hy⟩ := (GM07.IsOArc.isConnected hB).nonempty
    rcases cut_comps hcut hT hA.isPreconnected hB.isPreconnected hun hx hy with hconn |
      ⟨W₁, W₂, _, hcomps, hAW, hBW, _, _, _, hdis, _, _⟩
    · let := hconn
      exact not_cutHasDisc_of_connected
    · rintro ⟨C, D, _, hCD, hdisc⟩
      have hC : C ∈ spaceComponents T := hCD ▸ (Or.inl rfl : C ∈ ({C, D} : Set (Set T)))
      rw [hcomps] at hC
      rcases hC with rfl | rfl
      · exact hnot (isPlanar_of_disc_side hcut hdisc hun
          (hdis.symm.mono_left hBW) hbA hAW)
      · exact hnot (isPlanar_of_disc_side hcut hdisc (union_comm A B ▸ hun)
          (hdis.mono_left hAW) hbB hBW)
  · have hconn := connected_of_cut hcut hT hpre.isPreconnected rfl
      (GM07.IsOArc.isConnected hpre).nonempty
    let := hconn
    exact not_cutHasDisc_of_connected

end GraphMinor.GM08
