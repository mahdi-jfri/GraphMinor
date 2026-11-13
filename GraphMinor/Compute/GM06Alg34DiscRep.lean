module

public import GraphMinor.Compute.GM06Alg34Array

/-!
# Disc input facts used by the crossing program

A disc has one cuff, so its representation has one cyclic list. The
Section 3 instance condition says that every vertex on that list belongs
to the division. The finite division itself satisfies the division laws,
by injective transport along the supplied vertex bijection.
-/

public section
namespace GraphMinor.Compute

open Set Surface GM06

universe u

private theorem gm06_disc_cuffs {S : Type u} [TopologicalSpace S]
    (hS : IsClosedDiscSpace S) : Surface.cuffs S = {Surface.bd S} := by
  have hconn : IsConnected (Surface.bd S) := isConnected_of_isOArc hS.isOArc_bd
  ext C
  constructor
  · rintro ⟨p, hp, rfl⟩
    exact hconn.2.connectedComponentIn hp
  · rintro rfl
    obtain ⟨p, hp⟩ := hconn.1
    exact ⟨p, hp, hconn.2.connectedComponentIn hp⟩

namespace GM06DrawingRep

/-- A represented disc has exactly one supplied cuff list, even when
there are no boundary vertices. -/
theorem cuffs_length_one {x : GM06DrawingData} {S : Type u} [TopologicalSpace S]
    {G : Drawing S} {Δ : Set (Set S)} (h : GM06DrawingRep x G Δ)
    (hS : IsClosedDiscSpace S) : x.cuffs.length = 1 := by
  have hc := Nat.card_congr h.cuff
  rw [Nat.card_fin, gm06_disc_cuffs hS] at hc
  exact hc.trans Nat.card_unique

/-- The unique cuff list can be read directly from the supplied data. -/
theorem exists_cuff_list {x : GM06DrawingData} {S : Type u} [TopologicalSpace S]
    {G : Drawing S} {Δ : Set (Set S)} (h : GM06DrawingRep x G Δ)
    (hS : IsClosedDiscSpace S) : ∃ L : List (Fin x.n), x.cuffs = [L] := by
  have hlen := h.cuffs_length_one hS
  cases hc : x.cuffs with
  | nil =>
    simp only [hc, List.length_nil] at hlen
    cases hlen
  | cons L Ls =>
    have hz : Ls.length = 0 := by rw [hc, List.length_cons] at hlen; omega
    have hLs := List.length_eq_zero_iff.mp hz
    exact ⟨L, congrArg (List.cons L) hLs⟩

/-- The supplied block sets form a division whenever the represented
sets form a division. -/
theorem division_isDivision {x : GM06DrawingData} {S : Type u} [TopologicalSpace S]
    {G : Drawing S} {Δ : Set (Set S)} (h : GM06DrawingRep x G Δ)
    (hΔ : IsDivision Δ) : IsDivision x.divisionSet :=
  alg34_division_of_image h.vertexEmbedding (h.division_map_eq.symm ▸ hΔ)

/-- Every supplied cuff label belongs to a division block in a Section 3
disc instance. This is precisely the instance's boundary-vertex condition. -/
theorem cuff_mem_divisionUnion {x : GM06DrawingData} {I : DiscDivInstance.{u}}
    (h : GM06DrawingRep x I.G I.Δ) {L : List (Fin x.n)} (hcuffs : x.cuffs = [L])
    {a : Fin x.n} (ha : a ∈ L) : a ∈ divisionUnion x.divisionSet := by
  let i : Fin x.cuffs.length := ⟨0, by rw [hcuffs]; exact Nat.zero_lt_succ 0⟩
  have hget : x.cuffs[i] = L := by
    change x.cuffs.get i = L
    simp only [List.get_eq_getElem, i, hcuffs, List.getElem_cons_zero]
  have hi : a ∈ GM06DrawingData.block x.cuffs[i] := hget.symm ▸ ha
  have hp := (h.cuff_vertices i).subset ⟨a, hi, rfl⟩
  have hC : (h.cuff i).val = Surface.bd I.S :=
    mem_singleton_iff.mp ((gm06_disc_cuffs I.hDisc).subset (h.cuff i).property)
  have hpU : (h.vertex a).val ∈ divisionUnion I.Δ :=
    I.hΔ_eq.symm.subset ⟨hp.1, hC.subset hp.2⟩
  obtain ⟨δ, hδ, haδ⟩ := hpU
  obtain ⟨B, hB, hBδ⟩ := h.division.subset hδ
  obtain ⟨b, hb, hba⟩ := hBδ.symm.subset haδ
  have hba' : b = a := h.vertex.injective (Subtype.ext hba)
  subst b
  exact ⟨GM06DrawingData.block B, ⟨B, hB, rfl⟩, hb⟩

end GM06DrawingRep
end GraphMinor.Compute
