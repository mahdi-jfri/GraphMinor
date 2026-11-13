module

public import GraphMinor.GM07.Defs
import GraphMinor.GM08.Section18OneCuffCandidate
import GraphMinor.GM07.CuffShift
import GraphMinor.GM07.Section8
import GraphMinor.GM07.Section9MoveOff
import GraphMinor.GM07.CutEdge
import GraphMinor.GM12.Section3NormalEssentialCircle
import GraphMinor.GM12.Section3SchismaticMinimum

/-!
# Attainment of alpha for VIII (18.1)

The alpha candidate family is nonempty in each boundary case. With no
cuffs an essential circle supplies a candidate. With one cuff we cap it
and pull an essential circle back. With two cuffs a normal joining line
supplies a candidate. The minimum and the proved schismatic extraction
then give a normal schismatic set attaining alpha.
-/

public section

namespace GraphMinor.GM08

open Set GraphMinor.Surface GraphMinor.GM11

universe u

private theorem exists_candidate_closed {S : Type u} [TopologicalSpace S]
    [ConnectedSpace S] (hS : IsClosedSurface S) (hns : ¬ IsSphere S)
    (G : Drawing S) : ∃ X, GM07.IsAlphaCandidate G X := by
  have : T2Space S := hS.2.1
  have : CompactSpace S := hS.1
  have hs : IsSurface S := hS.isSurface
  have hbd : bd S = ∅ := eq_empty_iff_forall_notMem.mpr (fun x hx => hx (hS.2.2 x))
  obtain ⟨x⟩ := (inferInstance : Nonempty S)
  obtain ⟨B, hB, _, _⟩ := GM07.exists_disc_in_open (hS.2.2 x) isOpen_univ (mem_univ x)
  obtain ⟨D, hD, _, hDoff⟩ := GM07.exists_subdisc_disjoint_drawing hs G hB (by rw [hbd]; simp)
  have hnD : G.IsNormal (discBd D) := by
    rintro z ⟨hzD, hzG⟩
    exact (disjoint_left.mp hDoff (Surface.discBd_subset D hzD) hzG).elim
  obtain ⟨A, hA, hnA, _, hAnull⟩ := GM12.exists_normal_nonnull_oArc_outside_disc hS hns G hD hnD
  have hnnear : ¬ GM07.IsNearPlanar A := by
    rintro (hp | ⟨C, hC, _⟩)
    · exact hAnull ((GM07.isPlanar_iff_isNullHomotopicOArc_of_isOArc hs hA).mp hp)
    · obtain ⟨y, hy, _⟩ := hC
      exact (hbd ▸ hy : y ∈ (∅ : Set S)).elim
  have hsch : GM07.IsSchismatic A := ⟨Or.inl hA, hnnear, fun F hF hFA =>
    (GM07.not_ssubset_of_isOArc hA hF hFA).elim⟩
  exact ⟨A, hsch.isAlphaCandidate hs hnA⟩

/-- On the surfaces of VIII (18.1), alpha is attained on a normal
schismatic set, even when alpha is zero. This is the minimum-existence
step in the use of VII Section 8. -/
theorem exists_normal_schismatic_at_alpha {S : Type u} [TopologicalSpace S]
    [ConnectedSpace S] (hS : IsSurface S) {a b c : ℕ}
    (h3 : 3 ≤ 3 * a + 3 * b + c) (hm : Nonempty (S ≃ₜ SurfaceModel a b c))
    (hcyl : ¬ Nonempty (S ≃ₜ SurfaceModel 0 0 2))
    (G : Drawing S) (hp : G.IsProper) :
    ∃ X, GM07.IsSchismatic X ∧ G.IsNormal X ∧ (X ∩ G.V).ncard = GM07.alpha G := by
  classical
  have : T2Space S := hS.2.1
  have : CompactSpace S := hS.1
  have hns : ¬ IsSphere S := GM07.not_isSphere_of_model hm (by omega)
  have hex : ∃ X, GM07.IsAlphaCandidate G X := by
    by_cases hempty : cuffs S = ∅
    · have hbd : bd S = ∅ := by rw [← sUnion_cuffs, hempty, sUnion_empty]
      have hclosed : IsClosedSurface S := ⟨hS.1, inferInstance, fun x => by
        by_contra hx
        have hx' : x ∈ bd S := hx
        rw [hbd] at hx'
        exact notMem_empty x hx'⟩
      exact exists_candidate_closed hclosed hns G
    · obtain ⟨C, hC⟩ := nonempty_iff_ne_empty.mpr hempty
      by_cases hone : cuffs S = {C}
      · exact exists_alphaCandidate_of_one_cuff hS h3 hm hone G hp
      · have hother : ∃ D ∈ cuffs S, D ≠ C := by
          by_contra hn
          apply hone
          apply subset_antisymm
          · intro D hD
            have heq : D = C := by
              by_contra hne
              exact hn ⟨D, hD, hne⟩
            exact mem_singleton_iff.mpr heq
          · exact singleton_subset_iff.mpr hC
        obtain ⟨D, hD, hDC⟩ := hother
        exact GM07.exists_alphaCandidate hS h3 hm hcyl hp hC hD hDC.symm
  exact GM12.exists_normal_schismatic_at_alpha_of_extraction G hex
    (GM07.exists_schismatic_of_isAlphaCandidate hS hns G)

end GraphMinor.GM08
