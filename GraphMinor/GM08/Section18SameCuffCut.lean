module

public import GraphMinor.GM08.Section18Complexity
public import GraphMinor.GM07.Defs
import GraphMinor.GM08.Section18ArcDiscSide
import GraphMinor.Surface.CutIArc

/-!
# Cutting a schism arc with both ends on one cuff

The proper-arc cut theorem gives simpler components or a disc side and an
unchanged copy. A disc side makes the cutting arc together with its cuff
near-planar, contradicting type (iii) of the schism definition. Hence the
components are simpler and the maximum measure drops. This is the
same-cuff arc case of VIII (18.2).
-/

public section

namespace GraphMinor.GM08

open Set GraphMinor.Surface

universe w

private theorem component_eq_univ {T : Type w} [TopologicalSpace T] [ConnectedSpace T]
    {C : Set T} (hC : C ∈ spaceComponents T) : C = univ := by
  rw [spaceComponents_eq] at hC
  obtain ⟨x, rfl⟩ := hC
  exact PreconnectedSpace.connectedComponent_eq_univ x

private theorem not_disc_copy_of_arc_lifts {S T : Type w}
    [TopologicalSpace S] [TopologicalSpace T] [ConnectedSpace S]
    (hS : IsSurface S) (hT : IsSurface T) {ψ : T → S} {F : Set S}
    (hcut : IsCutting ψ F) {u v : S} (hF : IsLineWithEnds F u v)
    (hbd : F ∩ bd S = {u, v}) {C : Set S} (hC : C ∈ cuffs S) (hu : u ∈ C)
    (hnp : ¬ GM07.IsNearPlanar (F ∪ C))
    {A B : Set T} (hun : A ∪ B = ψ ⁻¹' F) (hA : IsLine A) (hB : IsLine B)
    (hbA : BijOn ψ A F) (hbB : BijOn ψ B F) : ¬ CutHasCopy T S ClosedUnitDisc := by
  have : CompactSpace T := hT.1
  have : T2Space S := hS.2.1
  obtain ⟨eA⟩ := hA
  obtain ⟨eB⟩ := hB
  have : ConnectedSpace A := eA.surjective.connectedSpace eA.continuous
  have : ConnectedSpace B := eB.surjective.connectedSpace eB.continuous
  have hpA : IsPreconnected A := (isConnected_iff_connectedSpace.mpr inferInstance).2
  have hpB : IsPreconnected B := (isConnected_iff_connectedSpace.mpr inferInstance).2
  rcases cut_comps hcut hT hpA hpB hun (eA 0).2 (eB 0).2 with hconn |
    ⟨W₁, W₂, _, hcomps, hAW, hBW, hW₁, hW₂, _, hdis, _, _⟩
  · let := hconn
    rintro ⟨E, D, hne, hED, _, _⟩
    have hE : E ∈ spaceComponents T := hED ▸ (Or.inl rfl : E ∈ ({E, D} : Set (Set T)))
    have hD : D ∈ spaceComponents T := hED ▸ (Or.inr rfl : D ∈ ({E, D} : Set (Set T)))
    exact hne ((component_eq_univ hE).trans (component_eq_univ hD).symm)
  · rintro ⟨E, D, _, hED, ⟨e⟩, _⟩
    have hE : E ∈ spaceComponents T := hED ▸ (Or.inl rfl : E ∈ ({E, D} : Set (Set T)))
    rw [hcomps] at hE
    rcases hE with rfl | rfl
    · exact hnp (isNearPlanar_union_cuff_of_arc_disc_side hS hT hcut hF hbd hC hu
        hW₁ ⟨e.symm⟩ hun (hdis.symm.mono_left hBW) hAW hbA)
    · exact hnp (isNearPlanar_union_cuff_of_arc_disc_side hS hT hcut hF hbd hC hu
        hW₂ ⟨e.symm⟩ (union_comm A B ▸ hun) (hdis.mono_left hAW) hBW hbB)

/-- The same-cuff proper arc case of VIII (18.2), page 286: cutting a
type (iii) schism gives a surface of strictly smaller measure. -/
theorem exists_cut_complexity_lt_of_same_cuff_arc {S : Type w}
    [TopologicalSpace S] [ConnectedSpace S] (hS : IsSurface S)
    {F C : Set S} {u v : S} (hC : C ∈ cuffs S) (hu : u ∈ C) (hv : v ∈ C)
    (hne : u ≠ v) (hF : IsLineWithEnds F u v) (hbd : F ∩ bd S = {u, v})
    (hnp : ¬ GM07.IsNearPlanar (F ∪ C)) :
    ∃ (T : Type w) (_ : TopologicalSpace T) (ψ : T → S),
      IsSurface T ∧ IsCutting ψ F ∧ surfaceComplexity T < surfaceComplexity S := by
  obtain ⟨T, tT, ψ, hT, hcut, _, hsame, A, B, _, hun, hA, hB, hbA, hbB⟩ :=
    cutIArc S F u v hS inferInstance hne hbd hF
  let := tT
  have hcomponent : ∀ x ∈ C, connectedComponentIn (bd S) x = C := by
    intro x hx
    obtain ⟨y, hy, rfl⟩ := hC
    exact (connectedComponentIn_eq hx).symm
  have heq : connectedComponentIn (bd S) u = connectedComponentIn (bd S) v := by
    rw [hcomponent u hu, hcomponent v hv]
  have hcase := hsame heq
  have hcopy := not_disc_copy_of_arc_lifts hS hT hcut hF hbd hC hu hnp hun hA hB hbA hbB
  have hsimpler := hcase.resolve_right hcopy
  obtain ⟨x⟩ := (inferInstance : Nonempty S)
  obtain ⟨y, _⟩ := hcut.2.1 x
  have : Nonempty T := ⟨y⟩
  exact ⟨T, tT, ψ, hT, hcut, surfaceComplexity_lt_of_cutIsSimpler hsimpler⟩

end GraphMinor.GM08
