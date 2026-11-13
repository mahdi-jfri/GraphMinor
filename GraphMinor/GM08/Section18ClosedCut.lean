module

public import GraphMinor.GM08.Section18Complexity
public import GraphMinor.GM07.Defs
import GraphMinor.GM08.Section18CutComponent
import GraphMinor.GM08.Section18CutDisc
import GraphMinor.Surface.CutOArc
import GraphMinor.GM07.Section8

/-!
# The circle cut on a closed surface

Cut along a non-planar circle in a closed connected surface. A disc
component would make the circle planar. The cylinder-copy outcome would
leave a component homeomorphic to the original closed surface, but every
component of a cut has boundary. Thus every component is simpler, and the
maximum of their measures decreases. This is the boundary-disjoint circle
case of VIII (18.2) for closed surfaces.
-/

public section

namespace GraphMinor.GM08

open Set GraphMinor.Surface GraphMinor.GM11

universe w

/-- The closed-surface, boundary-disjoint circle case of VIII (18.2),
page 286: the actual circle cut has strictly smaller surface measure. -/
theorem exists_cut_complexity_lt_of_closed_nonplanar_oArc {S : Type w}
    [TopologicalSpace S] [ConnectedSpace S] (hS : IsClosedSurface S)
    {F : Set S} (hF : IsOArc F) (hnp : ¬ IsPlanar F) :
    ∃ (T : Type w) (_ : TopologicalSpace T) (ψ : T → S),
      IsSurface T ∧ IsCutting ψ F ∧ surfaceComplexity T < surfaceComplexity S := by
  have hbd : bd S = ∅ := eq_empty_iff_forall_notMem.mpr (fun x hx => hx (hS.2.2 x))
  have hdis : Disjoint F (bd S) := by rw [hbd]; exact disjoint_empty _
  obtain ⟨T, tT, ψ, hT, hcut, hcase, hlifts⟩ :=
    cutOArc S F hS.isSurface inferInstance hF hdis
  let := tT
  have hFne := (GM07.IsOArc.isConnected hF).nonempty
  have hcopy : ¬ CutHasCopy T S ClosedCylinder := by
    rintro ⟨C, D, _, hcomps, _, hD⟩
    have hDmem : D ∈ spaceComponents T :=
      hcomps ▸ (Or.inr rfl : D ∈ ({C, D} : Set (Set T)))
    exact not_homeomorph_closed_component_of_cut hS.isSurface hT hS hcut hFne hDmem hD
  have hnodisc := not_cutHasDisc_of_circle_lifts hS.isSurface hT hcut hnp hlifts
  have hsimpler : CutIsSimpler T S := hcase.resolve_right (fun h => h.elim hcopy hnodisc)
  obtain ⟨x⟩ := (inferInstance : Nonempty S)
  obtain ⟨y, _⟩ := hcut.2.1 x
  have : Nonempty T := ⟨y⟩
  exact ⟨T, tT, ψ, hT, hcut, surfaceComplexity_lt_of_cutIsSimpler hsimpler⟩

/-- The closed-surface case of VIII (18.2), page 286. On a closed surface
only type (i) of the schism definition is possible, so the circle cut above
applies. The surface with cuffs still requires the other schism cases. -/
theorem theorem_18_2_closed {S : Type w} [TopologicalSpace S] [ConnectedSpace S]
    (hS : IsClosedSurface S) {F : Set S} (hF : GM07.IsSchism F) :
    ∃ (T : Type w) (_ : TopologicalSpace T) (ψ : T → S),
      IsSurface T ∧ IsCutting ψ F ∧ surfaceComplexity T < surfaceComplexity S := by
  have hnoCuff : ∀ C : Set S, C ∈ cuffs S → False := by
    rintro C ⟨x, hx, _⟩
    exact hx (hS.2.2 x)
  rcases hF with hi | hii | hiii | hiv | hv | hvi
  · exact exists_cut_complexity_lt_of_closed_nonplanar_oArc hS hi.1
      (fun hp => hi.2.1 (Or.inl hp))
  · obtain ⟨_, C, hC, _⟩ := hii
    exact (hnoCuff C hC).elim
  · obtain ⟨_, C, hC, _⟩ := hiii
    exact (hnoCuff C hC).elim
  · obtain ⟨_, _, A, B, C, D, _, _, _, _, hC, _⟩ := hiv
    exact (hnoCuff C hC).elim
  · obtain ⟨_, _, A, B, C, D, E, H, _, _, _, _, _, _, hD, _⟩ := hv
    exact (hnoCuff D hD).elim
  · obtain ⟨x, A, P, C, D, u, _, _, _, _, _, hC, _⟩ := hvi
    exact (hnoCuff C hC).elim

end GraphMinor.GM08
