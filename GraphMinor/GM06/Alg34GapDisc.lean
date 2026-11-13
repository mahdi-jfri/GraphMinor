module

public import GraphMinor.GM06.Alg34GapInputRep
public import GraphMinor.GM06.DiscRegions
import GraphMinor.GM06.Section3Induce
import GraphMinor.Compute.GM06Alg34DiscRep

/-!
# The single-cuff layout of represented disc input

A closed disc has one connected boundary circle and hence one cuff.
The representation bijection forces exactly one cuff list and one gap
region list in the supplied data. These are the numeric layout facts
used by the augmented RAM parser.
-/

public section
namespace GraphMinor.GM06

open Set Surface Compute

universe u
variable {S : Type u} [TopologicalSpace S]

/-- A closed disc's only cuff is its boundary circle. -/
theorem alg34_gap_disc_cuffs_eq (hS : IsClosedDiscSpace S) : cuffs S = {bd S} := by
  have hconn : IsConnected (bd S) := isConnected_of_isOArc hS.isOArc_bd
  ext C
  constructor
  · rintro ⟨p, hp, rfl⟩
    exact hconn.2.connectedComponentIn hp
  · rintro rfl
    obtain ⟨p, hp⟩ := hconn.1
    exact ⟨p, hp, hconn.2.connectedComponentIn hp⟩

end GraphMinor.GM06

namespace GraphMinor.Compute.GM06DrawingRep

open Set Surface GM06

universe u
variable {S : Type u} [TopologicalSpace S]
  {x : GM06DrawingData} {G : Drawing S} {Δ : Set (Set S)}

/-- Every cuff label of a represented disc denotes its boundary circle. -/
theorem disc_cuff_eq_bd (h : GM06DrawingRep x G Δ) (hS : IsClosedDiscSpace S)
    (c : Fin x.cuffs.length) : (h.cuff c).val = bd S :=
  mem_singleton_iff.mp ((alg34_gap_disc_cuffs_eq hS) ▸ (h.cuff c).property)

end GraphMinor.Compute.GM06DrawingRep

namespace GraphMinor.Compute.GM06GapInputRep

open Surface GM06

universe u
variable {S : Type u} [TopologicalSpace S]
  {X : GM06GapInput} {G : Drawing S} {Δ : Set (Set S)}

/-- The augmented representation of a disc has exactly one supplied gap region list. -/
theorem disc_gapRegions_singleton (h : GM06GapInputRep X G Δ) (hS : IsClosedDiscSpace S) :
    ∃ R, X.gapRegions = [R] :=
  List.length_eq_one_iff.mp (h.gap_count.trans (h.drawing.cuffs_length_one hS))

end GraphMinor.Compute.GM06GapInputRep
