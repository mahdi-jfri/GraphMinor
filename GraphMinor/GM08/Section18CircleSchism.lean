module

public import GraphMinor.GM07.Defs
import GraphMinor.GM08.Section18TwoCuffs
import GraphMinor.GM07.Section8
import GraphMinor.GM07.GoodEdge
import GraphMinor.GM07.CuffCollar
import GraphMinor.GM07.AlphaExists

/-!
# Extracting a schism from a non-near-planar circle

A circle with at most one boundary contact is already a schism. If it meets
two cuffs, trim an arc between them. Otherwise all contacts lie on one cuff.
The chord lemma of VII Section 8 then produces a proper arc whose union
with that cuff is not near-planar. These are the circle cases of the
schism discussion used by VIII (18.1).
-/

public section

namespace GraphMinor.GM08

open Set GraphMinor.Surface GraphMinor.GM11

universe w

/-- A normal non-near-planar circle contains a normal schism with no larger
vertex count. This supplies the circle case in VIII (18.1), page 285. -/
theorem exists_normal_schism_of_non_nearPlanar_oArc {S : Type w} [TopologicalSpace S]
    [ConnectedSpace S] (hS : IsSurface S) (a b c : ℕ) (h3 : 3 ≤ 3 * a + 3 * b + c)
    (he : Nonempty (S ≃ₜ SurfaceModel a b c)) (G : Drawing S) (hG : G.IsProper)
    {F : Set S} (hF : IsOArc F) (hnF : G.IsNormal F) (hnot : ¬ GM07.IsNearPlanar F) :
    ∃ P : Set S, P ⊆ F ∧ GM07.IsSchism P ∧ G.IsNormal P ∧
      (G.V ∩ P).ncard ≤ (G.V ∩ F).ncard := by
  have : T2Space S := hS.2.1
  by_cases hsmall : (F ∩ bd S).Finite ∧ (F ∩ bd S).ncard ≤ 1
  · exact ⟨F, Subset.rfl, Or.inl ⟨hF, hnot, hsmall.1, hsmall.2⟩, hnF, le_rfl⟩
  have hmeet : (F ∩ bd S).Nonempty := by
    by_contra hn
    have heq : F ∩ bd S = ∅ := not_nonempty_iff_eq_empty.mp hn
    exact hsmall ⟨heq ▸ finite_empty, by rw [heq]; simp⟩
  obtain ⟨x, hxF, hxbd⟩ := hmeet
  let C := connectedComponentIn (bd S) x
  have hC : C ∈ cuffs S := ⟨x, hxbd, rfl⟩
  have hxC : x ∈ C := mem_connectedComponentIn hxbd
  by_cases htwo : ∃ D ∈ cuffs S, C ≠ D ∧ (F ∩ D).Nonempty
  · obtain ⟨D, hD, hCD, hmD⟩ := htwo
    exact exists_normal_schism_of_meets_two_cuffs hS G (GM07.IsOArc.isSolid hF).2
      (GM07.IsOArc.isArcConnected hF) hnF hC hD hCD ⟨x, hxF, hxC⟩ hmD
  have hFbdC : F ∩ bd S ⊆ C := by
    rintro y ⟨hyF, hybd⟩
    let D := connectedComponentIn (bd S) y
    have hD : D ∈ cuffs S := ⟨y, hybd, rfl⟩
    have hyD : y ∈ D := mem_connectedComponentIn hybd
    by_cases hCD : C = D
    · exact hCD.symm ▸ hyD
    · exact (htwo ⟨D, hD, hCD, y, hyF, hyD⟩).elim
  have hCb : C ⊆ bd S := connectedComponentIn_subset _ _
  have hCO : IsOArc C := (cuff_statement S hS).2.2 C hC
  have hsC : GM07.SurroundsCuff C C :=
    (GM07.isScriptASet_cuff hS h3 he hG hC le_rfl).2.2.2.1
  have hncap : ¬ GM07.IsPlanarInCappedCuff C F := fun hp => hnot (Or.inr ⟨C, hC, hp⟩)
  rcases GM07.exists_chord_not_planarInCappedCuff_of_inter_nonempty hS hCO hF hsC hncap
    ⟨x, hxC, hxF⟩ with hsingle | ⟨P, u, v, hPF, huv, hP, hPC, hnPC⟩
  · obtain ⟨u, hu⟩ := hsingle
    have heq : F ∩ bd S = {u} := by
      rw [← hu]
      ext y
      exact ⟨fun hy => ⟨hFbdC hy, hy.1⟩, fun hy => ⟨hy.2, hCb hy.1⟩⟩
    exact (hsmall ⟨heq ▸ finite_singleton u, by rw [heq]; simp⟩).elim
  · have hPbd : P ∩ bd S = {u, v} := by
      rw [← hPC]
      ext y
      exact ⟨fun hy => ⟨hy.1, hFbdC ⟨hPF hy.1, hy.2⟩⟩,
        fun hy => ⟨hy.1, hCb hy.2⟩⟩
    have hendC : lineEnds P ⊆ C := by
      intro y hy
      have hyuv := GM07.lineEnds_subset hP hy
      have hyPC : y ∈ P ∩ C := hPC.symm.subset hyuv
      exact hyPC.2
    have hnnear : ¬ GM07.IsNearPlanar (P ∪ C) := by
      rw [union_comm]
      exact GM07.not_isNearPlanar_of_surroundsCuff_and_not_planarInCappedCuff
        hS hCO hsC hncap subset_union_left hnPC
    have hsch : GM07.IsSchism P := Or.inr (Or.inr (Or.inl
      ⟨⟨u, v, huv, hPbd, hP⟩, C, hC, hendC, hnnear⟩))
    exact ⟨P, hPF, hsch, fun y hy => hnF ⟨hPF hy.1, hy.2⟩,
      ncard_le_ncard (fun y hy => ⟨hy.1, hPF hy.2⟩) (G.finite_V.inter_of_left F)⟩

end GraphMinor.GM08
