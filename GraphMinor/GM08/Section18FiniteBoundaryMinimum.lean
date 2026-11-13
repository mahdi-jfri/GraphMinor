module

public import GraphMinor.GM07.Defs
import GraphMinor.GM08.Section18Minimum
import GraphMinor.GM08.Section18BoundaryPush
import GraphMinor.GM07.CutEdge
import GraphMinor.GM07.Section8
import GraphMinor.GM12.Section3SchismaticMinimum

/-!
# A minimum schismatic set with finite boundary contact

Apply the normal collar push one cuff at a time. A push fixes every
other cuff, so it preserves the contacts already treated. Planarity is
unchanged by each cuff shift. The resulting alpha candidate has the same
vertex count and meets the boundary only at drawing vertices. Schismatic
extraction retains these properties.
-/

public section

namespace GraphMinor.GM08

open Set GraphMinor.Surface GraphMinor.GM11

universe u

private theorem push_candidate_on_finite_cuffs {S : Type u} [TopologicalSpace S]
    [ConnectedSpace S] (hS : IsSurface S) {a b c : ℕ}
    (h3 : 3 ≤ 3 * a + 3 * b + c) (hm : Nonempty (S ≃ₜ SurfaceModel a b c))
    (hns : ¬ IsSphere S) (G : Drawing S) {X : Set S}
    (hX : GM07.IsAlphaCandidate G X) {𝒞 : Set (Set S)} (hfin : 𝒞.Finite)
    (hsub : 𝒞 ⊆ cuffs S) :
    ∃ Y, GM07.IsAlphaCandidate G Y ∧ (Y ∩ G.V).ncard = (X ∩ G.V).ncard ∧
      ∀ C ∈ 𝒞, Y ∩ C ⊆ G.V := by
  have : CompactSpace S := hS.1
  have : T2Space S := hS.2.1
  induction 𝒞, hfin using Set.Finite.induction_on with
  | empty => exact ⟨X, hX, rfl, fun _ h => h.elim⟩
  | @insert C 𝒞 hCnot hfin ih =>
    obtain ⟨Y, hY, hcard, htreated⟩ := ih ((subset_insert C 𝒞).trans hsub)
    have hC : C ∈ cuffs S := hsub (mem_insert C 𝒞)
    obtain ⟨h, H, hs, hfix, hnormal⟩ := exists_normal_cuff_push hS G hC
    obtain ⟨hn, hboundary, hcount⟩ := hnormal Y hY.2.2.1
    have hnew : GM07.IsAlphaCandidate G (h '' Y) := by
      refine ⟨GM07.isSolid_image_of_isClosedEmbedding hs.isClosedEmbedding hY.1,
        hY.2.1.image h hs.cont.continuousOn, hn, ?_⟩
      intro hp
      exact hY.2.2.2 ((hs.nearPlanar_iff hS h3 hm hns hY.1).mp hp)
    refine ⟨h '' Y, hnew, ?_, ?_⟩
    · rw [inter_comm, hcount, inter_comm, hcard]
    · rintro D (rfl | hD)
      · exact hboundary
      · rintro z ⟨⟨y, hy, he⟩, hzD⟩
        have hD' : D ∈ cuffs S := hsub (mem_insert_of_mem C hD)
        have hCD : C ≠ D := fun heq => hCnot (heq.symm ▸ hD)
        have hzbd : z ∈ bd S := GM07.connectedComponentIn_subset_of_cuff hD' hzD
        have hzC : z ∉ C := fun hzC => disjoint_left.mp (cuffs_disjoint hC hD' hCD) hzC hzD
        have hzz : h z = z := (hs.fix z hzbd hzC).1
        have hyz : y = z := hs.inj (he.trans hzz.symm)
        exact htreated D hD ⟨hyz ▸ hy, hzD⟩

/-- The minimum normal schismatic set in VIII (18.1) can be chosen to
meet the boundary only at drawing vertices, without increasing alpha.
In particular its boundary contact set is finite. -/
theorem exists_normal_schismatic_at_alpha_with_boundary_vertices {S : Type u}
    [TopologicalSpace S] [ConnectedSpace S] (hS : IsSurface S) {a b c : ℕ}
    (h3 : 3 ≤ 3 * a + 3 * b + c) (hm : Nonempty (S ≃ₜ SurfaceModel a b c))
    (hcyl : ¬ Nonempty (S ≃ₜ SurfaceModel 0 0 2))
    (G : Drawing S) (hp : G.IsProper) :
    ∃ X, GM07.IsSchismatic X ∧ G.IsNormal X ∧ (X ∩ G.V).ncard = GM07.alpha G ∧
      X ∩ bd S ⊆ G.V := by
  have : CompactSpace S := hS.1
  have : T2Space S := hS.2.1
  have hns : ¬ IsSphere S := GM07.not_isSphere_of_model hm (by omega)
  obtain ⟨X, hX, hnX, hcountX⟩ := exists_normal_schismatic_at_alpha hS h3 hm hcyl G hp
  obtain ⟨Y, hY, hcountY, hbdY⟩ := push_candidate_on_finite_cuffs hS h3 hm hns G
    (hX.isAlphaCandidate hS hnX) (cuff_statement S hS).2.1 Subset.rfl
  obtain ⟨Z, hZY, hZ, hnZ⟩ := GM07.exists_schismatic_of_isAlphaCandidate hS hns G Y hY
  have hle : (Z ∩ G.V).ncard ≤ GM07.alpha G := by
    rw [← hcountX, ← hcountY]
    exact ncard_le_ncard (inter_subset_inter_left G.V hZY) (G.finite_V.inter_of_right Y)
  have heq : (Z ∩ G.V).ncard = GM07.alpha G :=
    hle.antisymm (GM12.alpha_le_normal_schismatic_count hZ hnZ)
  refine ⟨Z, hZ, hnZ, heq, ?_⟩
  rintro x ⟨hxZ, hxbd⟩
  let C := connectedComponentIn (bd S) x
  have hC : C ∈ cuffs S := ⟨x, hxbd, rfl⟩
  exact hbdY C hC ⟨hZY hxZ, mem_connectedComponentIn hxbd⟩

end GraphMinor.GM08
