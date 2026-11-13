module

public import GraphMinor.GM08.Section18Complexity
public import GraphMinor.GM07.Defs
import GraphMinor.GM08.Section18CylinderCutSide
import GraphMinor.GM08.Section18CutDisc
import GraphMinor.Surface.CutOArc
import GraphMinor.GM07.Section8

/-!
# Cutting a non-near-planar circle off the boundary

The circle-cut theorem gives simpler components, a cylinder side, or a
disc side. A disc side makes the circle planar. A cylinder side has an
old cuff as its other cuff and makes the circle planar after capping
that cuff. Both contradict non-near-planarity. Consequently all components
are simpler and the surface measure drops, as required in this case of
VIII (18.2).
-/

public section

namespace GraphMinor.GM08

open Set GraphMinor.Surface GraphMinor.GM11

universe w

private theorem component_eq_univ {T : Type w} [TopologicalSpace T] [ConnectedSpace T]
    {C : Set T} (hC : C ∈ spaceComponents T) : C = univ := by
  rw [spaceComponents_eq] at hC
  obtain ⟨x, rfl⟩ := hC
  exact PreconnectedSpace.connectedComponent_eq_univ x

private theorem not_cutHasCopy_of_connected {S T : Type w} [TopologicalSpace S]
    [TopologicalSpace T] [ConnectedSpace T] : ¬ CutHasCopy T S ClosedCylinder := by
  rintro ⟨C, D, hne, hcomps, _, _⟩
  have hC : C ∈ spaceComponents T := hcomps ▸ (Or.inl rfl : C ∈ ({C, D} : Set (Set T)))
  have hD : D ∈ spaceComponents T := hcomps ▸ (Or.inr rfl : D ∈ ({C, D} : Set (Set T)))
  exact hne ((component_eq_univ hC).trans (component_eq_univ hD).symm)

private theorem not_cylinder_copy_of_circle_lifts {S T : Type w}
    [TopologicalSpace S] [TopologicalSpace T] [ConnectedSpace S]
    (hS : IsSurface S) (hT : IsSurface T) {ψ : T → S} {F : Set S}
    (hcut : IsCutting ψ F) (hFc : IsClosed F) (hnp : ¬ GM07.IsNearPlanar F)
    (hlifts : (∃ A B : Set T, Disjoint A B ∧ A ∪ B = ψ ⁻¹' F ∧ IsOArc A ∧ IsOArc B ∧
      BijOn ψ A F ∧ BijOn ψ B F) ∨ IsOArc (ψ ⁻¹' F)) :
    ¬ CutHasCopy T S ClosedCylinder := by
  have : CompactSpace T := hT.1
  have : T2Space S := hS.2.1
  rcases hlifts with ⟨A, B, _, hun, hA, hB, hbA, hbB⟩ | hpre
  · obtain ⟨x, hx⟩ := (GM07.IsOArc.isConnected hA).nonempty
    obtain ⟨y, hy⟩ := (GM07.IsOArc.isConnected hB).nonempty
    rcases cut_comps hcut hT hA.isPreconnected hB.isPreconnected hun hx hy with hconn |
      ⟨W₁, W₂, _, hcomps, hAW, hBW, hW₁, hW₂, _, hdis, hc₁, hc₂⟩
    · let := hconn
      exact not_cutHasCopy_of_connected
    · rintro ⟨C, D, _, hCD, ⟨e⟩, _⟩
      obtain ⟨ecyl⟩ := nonempty_cyl_homeo
      have hmodel : Nonempty (C ≃ₜ SurfaceModel 0 0 2) := ⟨e.trans ecyl.symm⟩
      have hC : C ∈ spaceComponents T := hCD ▸ (Or.inl rfl : C ∈ ({C, D} : Set (Set T)))
      rw [hcomps] at hC
      rcases hC with rfl | rfl
      · let := hc₁
        exact hnp (isNearPlanar_of_cylinder_cut_side hS hT hcut hFc hW₁ hmodel hun
          (hdis.symm.mono_left hBW) hAW hA hbA)
      · let := hc₂
        exact hnp (isNearPlanar_of_cylinder_cut_side hS hT hcut hFc hW₂ hmodel
          (union_comm A B ▸ hun) (hdis.mono_left hAW) hBW hB hbB)
  · have hconn := connected_of_cut hcut hT hpre.isPreconnected rfl
      (GM07.IsOArc.isConnected hpre).nonempty
    let := hconn
    exact not_cutHasCopy_of_connected

/-- The boundary-disjoint circle case of VIII (18.2), page 286, on a
surface which may have cuffs. The cut is the actual circle-cut construction. -/
theorem exists_cut_complexity_lt_of_non_nearPlanar_oArc {S : Type w}
    [TopologicalSpace S] [ConnectedSpace S] (hS : IsSurface S) {F : Set S}
    (hF : IsOArc F) (hoff : Disjoint F (bd S)) (hnp : ¬ GM07.IsNearPlanar F) :
    ∃ (T : Type w) (_ : TopologicalSpace T) (ψ : T → S),
      IsSurface T ∧ IsCutting ψ F ∧ surfaceComplexity T < surfaceComplexity S := by
  have : T2Space S := hS.2.1
  obtain ⟨T, tT, ψ, hT, hcut, hcase, hlifts⟩ := cutOArc S F hS inferInstance hF hoff
  let := tT
  have hFc := (GM07.IsOArc.isSolid hF).2
  have hcopy := not_cylinder_copy_of_circle_lifts hS hT hcut hFc hnp hlifts
  have hdisc := not_cutHasDisc_of_circle_lifts hS hT hcut (fun hp => hnp (Or.inl hp)) hlifts
  have hsimpler : CutIsSimpler T S := hcase.resolve_right (fun h => h.elim hcopy hdisc)
  obtain ⟨x⟩ := (inferInstance : Nonempty S)
  obtain ⟨y, _⟩ := hcut.2.1 x
  have : Nonempty T := ⟨y⟩
  exact ⟨T, tT, ψ, hT, hcut, surfaceComplexity_lt_of_cutIsSimpler hsimpler⟩

end GraphMinor.GM08
