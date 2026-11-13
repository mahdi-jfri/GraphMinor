module

public import GraphMinor.GM11.LocalCone
import GraphMinor.GM06.Section5DiscardedRegionEnclosure
import GraphMinor.GM11.Regions
import GraphMinor.GM11.Section5b

/-!
# Finitely many enclosures for the discarded side

For Reduction 2 in VI (5.5), page 130, choose an enclosure in
each retained region that meets the discarded side. There are
finitely many such regions. Their discs cover every discarded
point except the attachment, and each boundary meets the full
drawing only possibly at that point.
-/

public section
namespace GraphMinor.GM06
open Set Topology GraphMinor.Surface GraphMinor.GM11

/-- Construct a finite family of actual region enclosures for the
other side of an attached separation. -/
theorem exists_finite_discarded_region_enclosures
    {S : Type*} [TopologicalSpace S] [T2Space S] [ConnectedSpace S]
    (hS : IsClosedSurface S) (hsph : IsSphere S)
    {Γ T H : Drawing S} (hT : T.IsSubdrawing Γ) (hH : H.IsSubdrawing Γ) {s : S}
    {Φ : C(ClosedUnitDisc, S)} (hp : IsPolar Γ s Φ)
    (hsT : s ∈ T.U) (hTp : IsPreconnected (T.U \ {s}))
    (hscl : s ∈ closure (T.U \ {s})) (hover : H.U ∩ T.U ⊆ {s})
    (hcover : Γ.U ⊆ T.U ∪ H.U) :
    ∃ F : Set (Set S), F.Finite ∧
      (∀ D ∈ F, IsClosedDisc D ∧ discBd D ∩ Γ.U ⊆ {s} ∧ D ∩ T.U ⊆ {s} ∧
        ∃ r ∈ T.R, (H.U ∩ r).Nonempty ∧ D ⊆ r ∪ {s}) ∧
      H.U \ {s} ⊆ ⋃ D ∈ F, discInt D := by
  classical
  let J := {r : Set S // r ∈ T.R ∧ (H.U ∩ r).Nonempty}
  have hJ : Finite J := ((finite_R hS T).subset (fun _ hr => hr.1)).to_subtype
  have hex (j : J) := exists_disc_enclosing_discarded_region_piece
    hS hsph hT hH hp hsT hTp hscl hover hcover j.2.1
  choose D hD using hex
  let F := range D
  refine ⟨F, Set.finite_range D, ?_, ?_⟩
  · rintro E ⟨j, rfl⟩
    refine ⟨(hD j).1, (hD j).2.2.2, ?_, j.1, j.2.1, j.2.2, (hD j).2.1⟩
    rintro y ⟨hyD, hyT⟩
    exact ((hD j).2.1 hyD).resolve_left (fun hyr => region_subset j.2.1 hyr hyT)
  · rintro y ⟨hyH, hys⟩
    have hyT : y ∉ T.U := fun hyT => hys (hover ⟨hyH, hyT⟩)
    obtain ⟨r, hr, hyr⟩ := exists_region_of_notMem hyT
    let j : J := ⟨r, hr, y, hyH, hyr⟩
    exact mem_iUnion₂.mpr ⟨D j, mem_range_self j, (hD j).2.2.1 ⟨hyH, hyr⟩⟩

end GraphMinor.GM06
