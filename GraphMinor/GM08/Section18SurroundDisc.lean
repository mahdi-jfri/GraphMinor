module

public import GraphMinor.GM07.Defs
import GraphMinor.GM07.CuffFinger
import GraphMinor.GM07.Section5a
import GraphMinor.GM11.PerimeterExists
import GraphMinor.Surface.DiscArcs
import GraphMinor.Surface.DiscGrow

/-!
# The disc bounded by an `O`-arc that surrounds a cuff

Let `F` be an `O`-arc that surrounds the cuff `C`. Paste a disc `D` onto `C`. Then `F` lies in a closed disc of the new
surface, so it bounds a closed disc `Δ` there. This disc contains `D`: the
interior of `D` misses `F`, so it lies inside `Δ` or outside it, and if it lay
outside, `Δ` would lie in `Σ` and `F` would be planar in `Σ`. This is the
disc between `C` and the `O`-arc of (18.1)(iv), used in the split step of
(18.3), page 287.
-/

@[expose] public section

namespace GraphMinor.GM08

open Set Topology GraphMinor.Surface

universe u

/-- An `O`-arc `F` that surrounds the cuff `C` bounds a closed disc of `Σ + Ĉ` that contains the pasted disc. -/
theorem exists_surrounding_disc {S : Type u} [TopologicalSpace S] (hS : IsSurface S)
    {C F : Set S} (hF : IsOArc F) (hsur : GM07.SurroundsCuff F C)
    {T : Type u} [TopologicalSpace T] {j : S → T} {D : Set T}
    (hcap : GM07.IsCappedCuff C T j D) :
    ∃ Δ : Set T, IsClosedDisc Δ ∧ discBd Δ = j '' F ∧ D ⊆ Δ := by
  have hT := hcap.isSurface
  have : T2Space T := hT.2.1
  have : CompactSpace S := hS.1
  have hman := hT.2.2
  have hj := hcap.isEmbedding
  obtain ⟨Δ₀, hΔ₀, hFΔ₀⟩ := hsur.2.1.2.2 T j D hcap
  have hO : IsOArc (j '' F) :=
    GM11.isOArc_image hF hj.continuous.continuousOn hj.injective.injOn
  obtain ⟨Δ, ⟨-, hΔ, hbΔ, -⟩, -⟩ := disc_oArc Δ₀ (j '' F) hΔ₀ hFΔ₀ hO
  refine ⟨Δ, hΔ, hbΔ, ?_⟩
  have hFC : ∀ x ∈ F, j x ∈ D → x ∈ C := fun x hx hxD => by
    have h1 : j x ∈ j '' C := hcap.inter_eq ▸ ⟨mem_range_self x, hxD⟩
    obtain ⟨y, hy, hyx⟩ := h1
    exact hj.injective hyx ▸ hy
  have hdis : Disjoint (discInt D) (frontier Δ) := by
    rw [disjoint_left]
    intro z hz hzf
    have hzb : z ∈ j '' F := hbΔ ▸ GM07.frontier_disc_subset hman hΔ hzf
    obtain ⟨x, hx, rfl⟩ := hzb
    have hxC := hFC x hx hz.1
    exact hz.2 (hcap.discBd_eq ▸ mem_image_of_mem j hxC)
  rcases GM07.inside_or_off hcap.isClosedDisc.isPreconnected_discInt hΔ.isClosed hdis with
    hin | hout
  · calc D ⊆ closure (discInt D) := hcap.isClosedDisc.subset_closure_discInt
      _ ⊆ Δ := closure_minimal (hin.trans interior_subset) hΔ.isClosed
  · exfalso
    have hΔj : Δ ⊆ range j := by
      intro z hz
      by_contra hzr
      have hzD : z ∈ D := (hcap.union_eq ▸ mem_univ z).resolve_left hzr
      have hzb : z ∉ discBd D := fun hb => hzr (by
        rw [hcap.discBd_eq] at hb
        exact image_subset_range _ _ hb)
      exact hout ⟨hzD, hzb⟩ hz
    have hpre := GM07.isClosedDisc_preimage_of_subset_range hj.continuous hj.injective hΔ hΔj
    refine hsur.2.2 ⟨j ⁻¹' Δ, hpre, fun x hx => ?_⟩
    have : j x ∈ discBd Δ := hbΔ ▸ mem_image_of_mem j hx
    exact discBd_subset Δ this

end GraphMinor.GM08
