module

public import GraphMinor.GM19.CutMap
public import GraphMinor.GM07.CutStages
import GraphMinor.Surface.CutComp

/-!
# Boundary of a finite-fibre cut

Off the cutting set, a finite-fibre cut map is a homeomorphism locally.
It therefore preserves interior points there. Over the cutting set its
points lie on the new boundary. Together these facts identify the new
boundary with the preimage of the old boundary and the cutting set.
This connects the schism cuts of VIII Section 18 to the proved drawing
pullback machinery.
-/

public section

namespace GraphMinor.GM08

open Set Topology Function GraphMinor.Surface

universe w

section

variable {Y S : Type w} [TopologicalSpace Y] [TopologicalSpace S]
    [CompactSpace Y] [T2Space S] {ψ : Y → S} {F : Set S}

theorem bd_lift_cutMap (hψ : GM19.IsCutMap ψ F) (hF : IsClosed F) {y : Y} (hy : ψ y ∈ bd S) (hyF : ψ y ∉ F) : y ∈ bd Y := by
  intro hi
  apply hy
  obtain ⟨h1, h2, h3, -, -⟩ := hψ
  have hO : IsOpen (ψ ⁻¹' F)ᶜ := (hF.preimage h1).isOpen_compl
  obtain ⟨U, hU, hx, hsub, ⟨e⟩⟩ := hi.exists_subset hO hyF
  have hcl : IsClosedMap ψ := h1.isClosedMap
  have hq : IsQuotientMap ψ := hcl.isQuotientMap h1 h2
  have he : ψ ⁻¹' (ψ '' U) = U := by
    apply subset_antisymm
    · rintro a ⟨b, hb, hab⟩
      have hb' : ψ b ∉ F := hsub hb
      have ha' : ψ a ∉ F := hab ▸ hb'
      rwa [h3 ha' hb' hab.symm]
    · exact subset_preimage_image ψ U
  have hV : IsOpen (ψ '' U) := by
    rw [← hq.isOpen_preimage, he]
    exact hU
  have hbij : Bijective ((ψ '' U).restrictPreimage ψ) := by
    constructor
    · rintro ⟨a, ha⟩ ⟨b, hb⟩ he'
      have he2 : ψ a = ψ b := congrArg Subtype.val he'
      have ha' : a ∈ U := he ▸ ha
      have hb' : b ∈ U := he ▸ hb
      exact Subtype.ext (h3 (hsub ha') (hsub hb') he2)
    · rintro ⟨w, hw⟩
      obtain ⟨y', rfl⟩ := h2 w
      exact ⟨⟨y', hw⟩, rfl⟩
  have hh : IsHomeomorph ((ψ '' U).restrictPreimage ψ) :=
    isHomeomorph_iff_continuous_isClosedMap_bijective.mpr ⟨h1.restrictPreimage, hcl.restrictPreimage _, hbij⟩
  exact ⟨ψ '' U, hV, mem_image_of_mem ψ hx, ⟨hh.homeomorph.symm.trans ((Homeomorph.setCongr he).trans e)⟩⟩

private theorem bd_of_bd_cutMap (hψ : GM19.IsCutMap ψ F) (hF : IsClosed F) {z : Y} (hz : z ∈ bd Y) (hzF : ψ z ∉ F) : ψ z ∈ bd S := by
  intro hi
  apply hz
  obtain ⟨h1, h2, h3, -, -⟩ := hψ
  obtain ⟨U, hU, hx, hsub, ⟨e⟩⟩ := hi.exists_subset hF.isOpen_compl hzF
  have hcl : IsClosedMap ψ := h1.isClosedMap
  have hbij : Bijective (U.restrictPreimage ψ) := by
    constructor
    · rintro ⟨a, ha⟩ ⟨b, hb⟩ he
      have he' : ψ a = ψ b := congrArg Subtype.val he
      exact Subtype.ext (h3 (fun h => hsub ha h) (fun h => hsub hb h) he')
    · rintro ⟨w, hw⟩
      obtain ⟨y, rfl⟩ := h2 w
      exact ⟨⟨y, hw⟩, rfl⟩
  have hh : IsHomeomorph (U.restrictPreimage ψ) :=
    isHomeomorph_iff_continuous_isClosedMap_bijective.mpr ⟨h1.restrictPreimage, hcl.restrictPreimage U, hbij⟩
  exact ⟨ψ ⁻¹' U, hU.preimage h1, hx, ⟨hh.homeomorph.trans e⟩⟩

end

/-- A finite-fibre cut map of surfaces has the exact boundary of a cut
along its closed cutting set. This supplies the boundary identification
for the cut construction in VIII Section 18, pages 285–286. -/
theorem isCutAlongSet_of_cutMap {S Y : Type w} [TopologicalSpace S]
    [TopologicalSpace Y] (hS : IsSurface S) (hY : IsSurface Y) {F : Set S}
    (hF : IsClosed F) {ψ : Y → S} (hc : GM19.IsCutMap ψ F) :
    GM07.IsCutAlongSet F ψ := by
  have : CompactSpace Y := hY.1
  have : T2Space Y := hY.2.1
  have : T2Space S := hS.2.1
  refine ⟨hY, hc.1.isClosedMap.isQuotientMap hc.1 hc.2.1, ?_, ?_, hc.2.2.2.1⟩
  · ext y
    constructor
    · rintro (hy | hy)
      · by_cases hyF : ψ y ∈ F
        · exact hc.2.2.2.2 hyF
        · exact bd_lift_cutMap hc hF hy hyF
      · exact hc.2.2.2.2 hy
    · intro hy
      by_cases hyF : ψ y ∈ F
      · exact Or.inr hyF
      · exact Or.inl (bd_of_bd_cutMap hc hF hy hyF)
  · intro x hx y hxy
    have hxF : ψ x ∉ F := fun h => hx (hc.2.2.2.2 h)
    exact hc.2.2.1 hxF (show ψ y ∈ Fᶜ from hxy ▸ hxF) hxy

end GraphMinor.GM08
