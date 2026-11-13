module

public import GraphMinor.GM19.CutMap
public import GraphMinor.Surface.Dissection
import GraphMinor.GM08.Section18DiscLift
import GraphMinor.GM19.FragmentRegion

/-!
# The faces of a cut dissection

Lift the interior of each face and take its closure. The resulting
closed discs cover the cut surface, retain the face count, and have
disjoint interiors. Their boundaries lie over the original graph and
the face incidence bound is preserved. These are the face conditions
in the Euler argument for VIII (18.2).
-/

public section

namespace GraphMinor.GM08

open Set Topology GraphMinor.Surface

private theorem dense_preimage_of_cutMap {Y S : Type} [TopologicalSpace Y]
    [TopologicalSpace S] [T2Space S] (hY : IsSurface Y) {ψ : Y → S} {F A : Set S}
    (hcm : GM19.IsCutMap ψ F) (hF : IsClosed F) (hA : Dense A) : Dense (ψ ⁻¹' A) := by
  have : CompactSpace Y := hY.1
  have : T2Space Y := hY.2.1
  intro y
  rw [mem_closure_iff]
  intro N hN hyN
  obtain ⟨z, hzN, hzbd⟩ := (GM19.dense_interior' hY).inter_open_nonempty N hN ⟨y, hyN⟩
  have hzF : ψ z ∉ F := fun hz => hzbd (hcm.2.2.2.2 hz)
  let W := N ∩ ψ ⁻¹' Fᶜ
  have hW : IsOpen W := hN.inter (hF.isOpen_compl.preimage hcm.1)
  have himg : IsOpen (ψ '' W) := GM19.isOpen_image_of_isCutMap hcm inter_subset_right hW
  obtain ⟨x, hxW, hxA⟩ := hA.inter_open_nonempty (ψ '' W) himg
    ⟨ψ z, z, ⟨hzN, hzF⟩, rfl⟩
  obtain ⟨z', hz'W, hψz'⟩ := hxW
  exact ⟨z', hz'W.1, show ψ z' ∈ A from hψz'.symm ▸ hxA⟩

/-- The lifted face family satisfies all the face conditions of a
dissection and has the same number of faces. This is the face count
in VIII (18.2), page 286; the lifted edge graph is constructed separately. -/
theorem lifted_faces_of_dissection {S Y : Type} [TopologicalSpace S]
    [TopologicalSpace Y] [T2Space S] (hY : IsSurface Y)
    {V : Set S} {E 𝓕 : Set (Set S)} (hd : IsDissection V E 𝓕)
    {F : Set S} {ψ : Y → S} (hcm : GM19.IsCutMap ψ F) (hF : IsClosed F)
    (hFE : F ⊆ ⋃₀ E) :
    let 𝓕' := (fun Φ => closure (ψ ⁻¹' discInt Φ)) '' 𝓕
    𝓕'.Finite ∧ 𝓕'.ncard = 𝓕.ncard ∧
      (∀ Φ ∈ 𝓕', IsClosedDisc Φ) ∧ ⋃₀ 𝓕' = univ ∧
      (∀ Φ ∈ 𝓕', discBd Φ ⊆ ψ ⁻¹' ⋃₀ E) ∧
      (∀ Φ ∈ 𝓕', Disjoint (discInt Φ) (ψ ⁻¹' ⋃₀ E)) ∧
      (∀ Φ ∈ 𝓕', ∀ Ψ ∈ 𝓕', Φ ≠ Ψ → Disjoint (discInt Φ) Ψ) ∧
      ∀ y ∉ ψ ⁻¹' V, {Φ ∈ 𝓕' | y ∈ Φ}.encard ≤ 2 := by
  have : CompactSpace Y := hY.1
  have : T2Space Y := hY.2.1
  let L : Set S → Set Y := fun Φ => closure (ψ ⁻¹' discInt Φ)
  let 𝓕' := L '' 𝓕
  have hdata : ∀ Φ ∈ 𝓕, IsClosedDisc (L Φ) ∧ ψ '' L Φ = Φ ∧
      InjOn ψ (L Φ) ∧ ψ '' discBd (L Φ) = discBd Φ ∧ discInt (L Φ) = ψ ⁻¹' discInt Φ := by
    intro Φ hΦ
    exact isClosedDisc_closure_lift_of_cutMap hcm hF (hd.disc Φ hΦ)
      ((hd.int Φ hΦ).mono_right hFE)
  have hfin : 𝓕'.Finite := hd.fin.image L
  have hinj : InjOn L 𝓕 := by
    intro Φ hΦ Ψ hΨ heq
    exact (hdata Φ hΦ).2.1.symm.trans ((congrArg (fun Z => ψ '' Z) heq).trans (hdata Ψ hΨ).2.1)
  have hdisc : ∀ Φ ∈ 𝓕', IsClosedDisc Φ := by
    rintro Φ ⟨Ψ, hΨ, rfl⟩
    exact (hdata Ψ hΨ).1
  have hcover : ⋃₀ 𝓕' = univ := by
    let A := ⋃ Φ ∈ 𝓕, discInt Φ
    have hA : Dense A := by
      intro x
      obtain ⟨Φ, hΦ, hxΦ⟩ := hd.cover.symm.subset (mem_univ x)
      apply closure_mono (show discInt Φ ⊆ A from fun z hz => mem_iUnion₂.mpr ⟨Φ, hΦ, hz⟩)
      exact (hd.disc Φ hΦ).subset_closure_discInt hxΦ
    have hclosed : IsClosed (⋃₀ 𝓕') := hfin.isClosed_sUnion (fun Φ hΦ => (hdisc Φ hΦ).isClosed)
    have hsub : ψ ⁻¹' A ⊆ ⋃₀ 𝓕' := by
      intro y hy
      obtain ⟨Φ, hΦ, hyΦ⟩ := mem_iUnion₂.mp hy
      exact ⟨L Φ, mem_image_of_mem L hΦ, subset_closure hyΦ⟩
    exact eq_univ_of_forall (fun y => closure_minimal hsub hclosed (dense_preimage_of_cutMap hY hcm hF hA y))
  refine ⟨hfin, hinj.ncard_image, hdisc, hcover, ?_, ?_, ?_, ?_⟩
  · rintro Φ ⟨Ψ, hΨ, rfl⟩ y hy
    have hybd : ψ y ∈ discBd Ψ := (hdata Ψ hΨ).2.2.2.1.subset (mem_image_of_mem ψ hy)
    exact hd.bd Ψ hΨ hybd
  · rintro Φ ⟨Ψ, hΨ, rfl⟩
    rw [(hdata Ψ hΨ).2.2.2.2]
    exact disjoint_left.mpr (fun y hy hyE => disjoint_left.mp (hd.int Ψ hΨ) hy hyE)
  · rintro Φ ⟨A, hA, rfl⟩ Ψ ⟨B, hB, rfl⟩ hne
    apply disjoint_left.mpr
    intro y hyA hyB
    rw [(hdata A hA).2.2.2.2] at hyA
    have hyB' : ψ y ∈ B := (hdata B hB).2.1.subset (mem_image_of_mem ψ hyB)
    exact disjoint_left.mp (hd.disj A hA B hB (fun hh => hne (congrArg L hh))) hyA hyB'
  · intro y hyV
    have hsub : {Φ ∈ 𝓕' | y ∈ Φ} ⊆ L '' {Φ ∈ 𝓕 | ψ y ∈ Φ} := by
      rintro Φ ⟨⟨Ψ, hΨ, rfl⟩, hy⟩
      exact ⟨Ψ, ⟨hΨ, (hdata Ψ hΨ).2.1.subset (mem_image_of_mem ψ hy)⟩, rfl⟩
    exact (encard_le_encard hsub).trans ((encard_image_le L _).trans (hd.count (ψ y) hyV))

end GraphMinor.GM08
