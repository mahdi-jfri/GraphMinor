module

public import GraphMinor.GM19.CutMap
public import GraphMinor.GM19.PullLift
public import GraphMinor.Surface.DiscGrow
import GraphMinor.GM19.Section5b
import GraphMinor.GM07.CutBounds

/-!
# Lifting a dissection face across a graph cut

The interior of a face misses the cutting graph. Its lift has one
closure point over each boundary point, because a disc interior is
connected near its boundary. The closure of the lift is therefore a
closed disc mapping homeomorphically onto the original face. This
preserves the faces in the Euler calculation of VIII (18.2).
-/

public section

namespace GraphMinor.GM08

universe w

open Set Topology GraphMinor.Surface GraphMinor.GM11

/-- A connected set approaching a point of the cutting set has at most
one lift in the closure over that point. Finite fibres and the closed-map
property separate any two proposed lifts. This is the local uniqueness
used when lifting edges and faces in VIII (18.2). -/
theorem eq_of_mem_closure_preimage_of_cutMap {Y S : Type w}
    [TopologicalSpace Y] [TopologicalSpace S] [CompactSpace Y] [T2Space Y] [T2Space S]
    {ψ : Y → S} {F : Set S} (hcm : GM19.IsCutMap ψ F) (hF : IsClosed F)
    {A : Set S} {v : S} (hA : A ⊆ Fᶜ) (hloc : GM19.IsConnectedNear A v)
    {y₁ y₂ : Y} (h₁ : ψ y₁ = v) (h₂ : ψ y₂ = v)
    (hc₁ : y₁ ∈ closure (ψ ⁻¹' A)) (hc₂ : y₂ ∈ closure (ψ ⁻¹' A)) :
    y₁ = y₂ := by
  by_contra hne
  have hfin : (ψ ⁻¹' {v}).Finite := hcm.2.2.2.1 v
  have hcomp : IsCompact (ψ ⁻¹' {v} \ {y₁}) := (hfin.subset sdiff_subset).isCompact
  obtain ⟨U₁, U₂, hU₁, hU₂, hy₁, hy₂, hdis⟩ :=
    SeparatedNhds.of_isCompact_isCompact (isCompact_singleton (x := y₁)) hcomp
      (by rw [disjoint_singleton_left]; exact fun hx => hx.2 rfl)
  have hy₁U : y₁ ∈ U₁ := hy₁ rfl
  have hcl_map : IsClosedMap ψ := GM19.isClosedMap_of_isCutMap hcm
  have hWo : IsOpen (ψ '' (U₁ ∪ U₂)ᶜ)ᶜ :=
    (hcl_map _ (hU₁.union hU₂).isClosed_compl).isOpen_compl
  have hvW : v ∈ (ψ '' (U₁ ∪ U₂)ᶜ)ᶜ := by
    rintro ⟨y, hy, hyv⟩
    by_cases hyy₁ : y = y₁
    · exact hy (Or.inl (hyy₁ ▸ hy₁U))
    · exact hy (Or.inr (hy₂ ⟨hyv, hyy₁⟩))
  obtain ⟨B, hBsub, hBc, W', hW', hsub⟩ := hloc _ (hWo.mem_nhds hvW)
  have hBF : B ⊆ Fᶜ := fun z hz => hA (hBsub hz).1
  have hcov : ψ ⁻¹' B ⊆ U₁ ∪ U₂ := by
    intro y hy
    by_contra hny
    exact (hBsub hy).2 ⟨y, hny, rfl⟩
  have hpt : ∀ {w : Y} {U : Set Y}, ψ w = v → IsOpen U → w ∈ U → w ∈ closure (ψ ⁻¹' A) →
      (ψ ⁻¹' B ∩ U).Nonempty := by
    intro w U hw hU hwU hc
    have hn : U ∩ ψ ⁻¹' W' ∈ 𝓝 w :=
      Filter.inter_mem (hU.mem_nhds hwU)
        (hcm.1.continuousAt.preimage_mem_nhds (hw.symm ▸ hW'))
    obtain ⟨p, ⟨hpU, hpW⟩, hpA⟩ := mem_closure_iff_nhds.mp hc _ hn
    exact ⟨p, hsub ⟨hpA, hpW⟩, hpU⟩
  have hy₂U : y₂ ∈ U₂ := hy₂ ⟨h₂, fun hx => hne hx.symm⟩
  obtain ⟨p, -, hp₁, hp₂⟩ :=
    GM19.isPreconnected_preimage_of_isCutMap hcm hF hBF hBc U₁ U₂ hU₁ hU₂ hcov
      (hpt h₁ hU₁ hy₁U hc₁) (hpt h₂ hU₂ hy₂U hc₂)
  exact disjoint_left.mp hdis hp₁ hp₂

/-- A face whose interior misses the cutting set lifts to a closed disc.
Its boundary maps onto the old face boundary. This is the face-lifting
step in the triangulation proof of VIII (18.2), page 286. -/
theorem isClosedDisc_closure_lift_of_cutMap {Y S : Type w}
    [TopologicalSpace Y] [TopologicalSpace S] [CompactSpace Y] [T2Space Y] [T2Space S]
    {ψ : Y → S} {F Δ : Set S} (hcm : GM19.IsCutMap ψ F) (hF : IsClosed F)
    (hΔ : IsClosedDisc Δ) (hoff : Disjoint (discInt Δ) F) :
    IsClosedDisc (closure (ψ ⁻¹' discInt Δ)) ∧
      ψ '' closure (ψ ⁻¹' discInt Δ) = Δ ∧
      InjOn ψ (closure (ψ ⁻¹' discInt Δ)) ∧
      ψ '' discBd (closure (ψ ⁻¹' discInt Δ)) = discBd Δ ∧
      discInt (closure (ψ ⁻¹' discInt Δ)) = ψ ⁻¹' discInt Δ := by
  have hA : discInt Δ ⊆ Fᶜ := fun x hx => disjoint_left.mp hoff hx
  have hcl : closure (discInt Δ) = Δ :=
    (closure_minimal (discInt_subset Δ) hΔ.isClosed).antisymm hΔ.subset_closure_discInt
  have himg : ψ '' closure (ψ ⁻¹' discInt Δ) = Δ := by
    have hsur : ψ '' (ψ ⁻¹' discInt Δ) = discInt Δ := hcm.2.1.image_preimage _
    have hh : ψ '' closure (ψ ⁻¹' discInt Δ) = closure (discInt Δ) := by
      apply subset_antisymm
      · simpa only [hsur] using image_closure_subset_closure_image (s := ψ ⁻¹' discInt Δ) hcm.1
      · simpa only [hsur] using (GM19.isClosedMap_of_isCutMap hcm).closure_image_subset (ψ ⁻¹' discInt Δ)
    exact hh.trans hcl
  have hinj : InjOn ψ (closure (ψ ⁻¹' discInt Δ)) := by
    intro x hx y hy hxy
    by_cases hxi : ψ x ∈ discInt Δ
    · exact hcm.2.2.1 (hA hxi) (hA (hxy ▸ hxi)) hxy
    · have hxΔ : ψ x ∈ Δ := himg.subset (mem_image_of_mem ψ hx)
      have hxbd : ψ x ∈ discBd Δ := by
        by_contra hn
        exact hxi ⟨hxΔ, hn⟩
      exact eq_of_mem_closure_preimage_of_cutMap hcm hF hA
        (GM19.isConnectedNear_discInt hΔ hxbd) rfl hxy.symm hx hy
  have hbij : Function.Bijective (fun x : ↥(closure (ψ ⁻¹' discInt Δ)) =>
      (⟨ψ x.1, himg.subset (mem_image_of_mem ψ x.2)⟩ : Δ)) := by
    constructor
    · intro x y hxy
      exact Subtype.ext (hinj x.2 y.2 (congrArg Subtype.val hxy))
    · rintro ⟨z, hz⟩
      obtain ⟨x, hx, hψx⟩ := himg.symm.subset hz
      exact ⟨⟨x, hx⟩, Subtype.ext hψx⟩
  have : CompactSpace ↥(closure (ψ ⁻¹' discInt Δ)) :=
    isCompact_iff_compactSpace.mp isClosed_closure.isCompact
  let H : ↥(closure (ψ ⁻¹' discInt Δ)) ≃ₜ Δ := Continuous.homeoOfEquivCompactToT2
    (f := Equiv.ofBijective _ hbij) ((hcm.1.comp continuous_subtype_val).subtype_mk _)
  have hdisc : IsClosedDisc (closure (ψ ⁻¹' discInt Δ)) := by
    obtain ⟨e⟩ := hΔ
    exact ⟨e.trans H.symm⟩
  have hboundary := (GM07.isClosedDisc_image_of_injOn hdisc hcm.1 hinj).2
  rw [himg] at hboundary
  have hbdimage : ψ '' discBd (closure (ψ ⁻¹' discInt Δ)) = discBd Δ := hboundary.symm
  have hinterior : discInt (closure (ψ ⁻¹' discInt Δ)) = ψ ⁻¹' discInt Δ := by
    ext y
    constructor
    · rintro ⟨hyZ, hynbd⟩
      refine ⟨himg.subset (mem_image_of_mem ψ hyZ), ?_⟩
      intro hybd
      obtain ⟨z, hz, heq⟩ := hbdimage.symm.subset hybd
      have hzy : z = y := hinj (Surface.discBd_subset _ hz) hyZ heq
      exact hynbd (hzy ▸ hz)
    · intro hy
      refine ⟨subset_closure hy, ?_⟩
      intro hybd
      exact hy.2 (hbdimage.subset (mem_image_of_mem ψ hybd))
  exact ⟨hdisc, himg, hinj, hbdimage, hinterior⟩

end GraphMinor.GM08
