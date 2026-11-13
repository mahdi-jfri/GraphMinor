module

public import GraphMinor.GM07.Defs
import GraphMinor.GM07.CutBounds
import GraphMinor.GM07.CylinderCap
import GraphMinor.GM07.Section5a
import GraphMinor.GM12.Section3NormalEssentialCircle
import GraphMinor.GM11.Section6

/-!
# A normal alpha candidate on a surface with one cuff

For the small-alpha alternative of VIII (18.1), cap the only cuff.
An essential normal circle outside the cap pulls back to a normal circle
which remains nonplanar after capping. It is therefore an alpha candidate.
-/

public section

namespace GraphMinor.GM08

open Set Topology GraphMinor.Surface GraphMinor.GM11

universe u

/-- The candidate family used in VIII (18.1) is nonempty on a one-cuff
surface other than the disc. The model bound also excludes the sphere
and cylinder, as in the statement of (18.1). -/
theorem exists_alphaCandidate_of_one_cuff {S : Type u} [TopologicalSpace S]
    [ConnectedSpace S] (hS : IsSurface S) {a b c : ℕ}
    (h3 : 3 ≤ 3 * a + 3 * b + c) (hm : Nonempty (S ≃ₜ SurfaceModel a b c))
    {C : Set S} (hC : cuffs S = {C}) (G : Drawing S) (hp : G.IsProper) :
    ∃ X, GM07.IsAlphaCandidate G X := by
  have : CompactSpace S := hS.1
  have : T2Space S := hS.2.1
  have hc : IsCuff C := by
    change C ∈ cuffs S
    rw [hC]
    exact mem_singleton C
  have hbd : bd S = C := by rw [← sUnion_cuffs, hC, sUnion_singleton]
  obtain ⟨T, tT, j, D, hcap, hbdT⟩ := GM07.exists_cappedCuff hS hc
  have : T2Space T := hcap.isSurface.2.1
  have : ConnectedSpace T := hcap.connectedSpace hS
  have htbd : bd T = ∅ := by rw [hbdT, hbd, sdiff_self, image_empty]
  have ht : IsClosedSurface T := ⟨hcap.isSurface.1, inferInstance, fun x => by
    by_contra hx
    have hxbd : x ∈ bd T := hx
    rw [htbd] at hxbd
    exact notMem_empty x hxbd⟩
  have hj := hcap.isEmbedding.continuous.isClosedEmbedding hcap.isEmbedding.injective
  obtain ⟨Γ, hΓ⟩ := GM07.exists_image_matched hj G
  have hu : j '' G.U = Γ.U := by simpa using hΓ.image_U
  have hv : j '' G.V = Γ.V := by simpa using hΓ.image_V
  have hnD : Γ.IsNormal (discBd D) := by
    rintro z ⟨hzD, hzΓ⟩
    rw [hcap.discBd_eq] at hzD
    obtain ⟨x, hx, rfl⟩ := hzD
    obtain ⟨y, hy, he⟩ := hu.symm ▸ hzΓ
    have heq : y = x := hcap.isEmbedding.injective he
    rw [← hv]
    exact ⟨x, hp ⟨hbd ▸ hx, heq ▸ hy⟩, rfl⟩
  obtain ⟨F, hF, hnF, hFD, hnull⟩ := GM12.exists_normal_nonnull_oArc_outside_disc
    ht (GM07.not_isSphere_cap hS h3 hm hcap) Γ hcap.isClosedDisc hnD
  have hFr : F ⊆ range j := by
    intro x hx
    by_cases hxD : x ∈ D
    · have hfront : x ∈ frontier D := by
        rw [frontier_eq_closure_inter_closure]
        exact ⟨subset_closure hxD, hFD hx⟩
      rw [IsClosedDisc.frontier_eq_discBd ht hcap.isClosedDisc, hcap.discBd_eq] at hfront
      exact image_subset_range _ _ hfront
    · have hh : x ∈ range j ∪ D := hcap.union_eq ▸ mem_univ x
      exact hh.resolve_right hxD
  let B := j ⁻¹' F
  have hB : IsOArc B := GM07.pull_oArc hcap.isEmbedding hF hFr
  have hBi : j '' B = F := image_preimage_eq_of_subset hFr
  have hnB : G.IsNormal B := by
    rintro x ⟨hxB, hxU⟩
    have hxV := hnF ⟨hxB, hu ▸ mem_image_of_mem j hxU⟩
    obtain ⟨y, hy, he⟩ := hv.symm ▸ hxV
    exact hcap.isEmbedding.injective he ▸ hy
  have hnnear : ¬ GM07.IsNearPlanar B := by
    rintro (⟨E, hE, hBE⟩ | ⟨C', hC', hplan⟩)
    · have himage := (GM07.isClosedDisc_image_of_injOn hE hj.continuous
        hcap.isEmbedding.injective.injOn).1
      have hpF : IsPlanar F := ⟨j '' E, himage, hBi ▸ image_mono hBE⟩
      exact hnull ((GM07.isPlanar_iff_isNullHomotopicOArc_of_isOArc ht.isSurface hF).mp hpF)
    · have hCC : C' = C := mem_singleton_iff.mp (hC ▸ hC')
      subst C'
      have hpF : IsPlanar F := hBi ▸ hplan.2.2 T j D hcap
      exact hnull ((GM07.isPlanar_iff_isNullHomotopicOArc_of_isOArc ht.isSurface hF).mp hpF)
  have hsch : GM07.IsSchismatic B := ⟨Or.inl hB, hnnear, fun A hA hAB =>
    (GM07.not_ssubset_of_isOArc hB hA hAB).elim⟩
  exact ⟨B, hsch.isAlphaCandidate hS hnB⟩

end GraphMinor.GM08
