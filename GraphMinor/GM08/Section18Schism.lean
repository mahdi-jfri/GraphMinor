module

public import GraphMinor.GM07.Defs
import GraphMinor.GM12.Section3LoopCuffClassification
import GraphMinor.GM12.Section3ThetaSurrounding
import GraphMinor.GM12.Section3ThetaCircles
import GraphMinor.GM07.Section8
import GraphMinor.GM07.GoodEdge
import GraphMinor.GM12.Section3SchismaticMinimum

/-!
# Schismatic sets away from the boundary

For the use of VII Section 8 in VIII (18.1), a schismatic set disjoint from
the boundary is already a schism. The two-loop and three-path cases use the
proved classifications of their surrounding cuffs. This file handles
surfaces with at least one cuff.
-/

public section

namespace GraphMinor.GM08

open Set GraphMinor.Surface GraphMinor.GM11

universe w

/-- A schismatic set away from the boundary is a schism, on a connected
surface with a cuff. This is the boundary-disjoint case of the discussion in
VII Section 8, pages 241–242, used by VIII (18.1), page 285. -/
theorem isSchism_of_isSchismatic_of_disjoint_boundary {S : Type w}
    [TopologicalSpace S] [T2Space S] [ConnectedSpace S]
    (hS : IsSurface S) (hcuffs : (cuffs S).Nonempty) {X : Set S}
    (hX : GM07.IsSchismatic X) (hoff : X ∩ bd S = ∅) : GM07.IsSchism X := by
  rcases hX.1 with ho | hx₁ | hx₂ | hx₃
  · exact Or.inl ⟨ho, hX.2.1, hoff ▸ finite_empty, by rw [hoff]; simp⟩
  · obtain ⟨A, B, P, u, v, hA, hB, hdis, hP, hu, hv, hPA, hPB, heq⟩ := hx₁
    obtain ⟨C, D, hsC, hsD, hCD⟩ := GM12.surrounding_cuffs_of_schismatic_x1
      hS hcuffs hA hB hdis hP hu hv hPA hPB (heq ▸ hX)
    refine Or.inr (Or.inr (Or.inr (Or.inl ⟨Or.inl ?_, hoff, A, B, C, D,
      hA, hB, ?_, ?_, hsC.1, hsD.1, hCD, hsC, hsD⟩)))
    · exact ⟨A, B, P, u, v, hA, hB, hdis, hP, hu, hv, hPA, hPB, heq⟩
    · rw [heq]; exact subset_union_left.trans subset_union_left
    · rw [heq]; exact subset_union_right.trans subset_union_left
  · obtain ⟨A, B, u, hA, hB, hAB, heq⟩ := hx₂
    obtain ⟨C, D, hsC, hsD, hCD⟩ := GM12.surrounding_cuffs_of_schismatic_x2
      hS hcuffs hA hB hAB (heq ▸ hX)
    refine Or.inr (Or.inr (Or.inr (Or.inl ⟨Or.inr ?_, hoff, A, B, C, D,
      hA, hB, ?_, ?_, hsC.1, hsD.1, hCD, hsC, hsD⟩)))
    · exact ⟨A, B, u, hA, hB, hAB, heq⟩
    · rw [heq]; exact subset_union_left
    · rw [heq]; exact subset_union_right
  · obtain ⟨P, Q, R, u, v, huv, hP, hQ, hR, hPQ, hPR, hQR, heq⟩ := hx₃
    obtain ⟨C, D, E, hsC, hsD, hsE, hCD, hCE, hDE⟩ :=
      GM12.surrounding_pairs_of_schismatic_theta hS hcuffs huv hP hQ hR hPQ hPR hQR (heq ▸ hX)
    have hoPQ := GM12.isOArc_union_of_lines_inter_eq_ends hP hQ hPQ
    have hoPR := GM12.isOArc_union_of_lines_inter_eq_ends hP hR hPR
    have hoQR := GM12.isOArc_union_of_lines_inter_eq_ends hQ hR hQR
    refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨?_, hoff,
      P ∪ Q, P ∪ R, Q ∪ R, C, D, E, hoPQ, hoPR, hoQR,
      ?_, ?_, ?_, hsC.1, hsD.1, hsE.1, hCD, hCE, hDE, hsC, hsD, hsE⟩))))
    · exact ⟨P, Q, R, u, v, huv, hP, hQ, hR, hPQ, hPR, hQR, heq⟩
    · rw [heq]; exact subset_union_left
    · rw [heq]; exact union_subset (subset_union_left.trans subset_union_left) subset_union_right
    · rw [heq]; exact union_subset (subset_union_right.trans subset_union_left) subset_union_right

/-- On a non-sphere, the boundary-disjoint schismatic set is a schism even
when there are no cuffs. In that case a schismatic set must be a circle. -/
theorem isSchism_of_isSchismatic_off_boundary {S : Type w}
    [TopologicalSpace S] [T2Space S] [ConnectedSpace S]
    (hS : IsSurface S) (hns : ¬ IsSphere S) {X : Set S}
    (hX : GM07.IsSchismatic X) (hoff : X ∩ bd S = ∅) : GM07.IsSchism X := by
  by_cases hcuffs : (cuffs S).Nonempty
  · exact isSchism_of_isSchismatic_of_disjoint_boundary hS hcuffs hX hoff
  · by_cases ho : IsOArc X
    · exact Or.inl ⟨ho, hX.2.1, hoff ▸ finite_empty, by rw [hoff]; simp⟩
    · have hsolid := (GM07.IsSchismatic.isSolid_and_isConnected hS hX).1
      have hplanar : IsPlanar X :=
        (GM07.theorem_5_1_of_not_isSphere hS (Or.inl hns) hsolid).mpr (by
          intro F hF hFX
          have hproper : F ⊂ X := ⟨hFX, fun hXF => ho (Subset.antisymm hXF hFX ▸ hF)⟩
          rcases hX.2.2 F hF hproper with hp | ⟨C, hC, _⟩
          · exact hp
          · exact (hcuffs ⟨C, hC⟩).elim)
      exact (hX.2.1 (Or.inl hplanar)).elim

/-- On a closed non-sphere surface, positive alpha is attained on a normal
schism. This is the closed-surface extraction step used in VIII (18.1). -/
theorem exists_normal_schism_at_alpha_of_closed_surface {S : Type w}
    [TopologicalSpace S] [ConnectedSpace S] (hS : IsClosedSurface S)
    (hns : ¬ IsSphere S) (G : Drawing S) (hpos : 0 < GM07.alpha G) :
    ∃ F : Set S, GM07.IsSchism F ∧ G.IsNormal F ∧ (F ∩ G.V).ncard = GM07.alpha G := by
  have : T2Space S := hS.2.1
  have : CompactSpace S := hS.1
  have hs : IsSurface S := hS.isSurface
  obtain ⟨F, hF, hNF, hcount⟩ := GM12.exists_normal_schismatic_at_alpha_of_extraction G
    (GM07.exists_candidate_of_alpha_pos hpos) (GM07.exists_schismatic_of_isAlphaCandidate hs hns G)
  have hbd : bd S = ∅ := eq_empty_iff_forall_notMem.mpr (fun x hx => hx (hS.2.2 x))
  exact ⟨F, isSchism_of_isSchismatic_off_boundary hs hns hF (by rw [hbd]; simp), hNF, hcount⟩

end GraphMinor.GM08
