module

public import GraphMinor.GM07.Defs
import GraphMinor.GM07.CutBounds
import GraphMinor.GM07.CapMap
import GraphMinor.Surface.DiscUnion
import GraphMinor.Surface.SurfacePull

/-!
# A disc attached to one cuff

A disc meeting a cuff in a boundary line becomes part of a larger disc
when that cuff is capped. Thus its union with the cuff is near-planar.
This is the obstruction that must be excluded for a disc side in the
same-cuff arc case of VIII (18.2).
-/

public section

namespace GraphMinor.GM08

open Set Topology GraphMinor.Surface GraphMinor.GM11

universe w

private theorem disc_image_embedding {S T : Type w} [TopologicalSpace S]
    [TopologicalSpace T] {j : S → T} (hj : IsEmbedding j) {Δ : Set S}
    (hΔ : IsClosedDisc Δ) :
    IsClosedDisc (j '' Δ) ∧ discBd (j '' Δ) = j '' discBd Δ := by
  obtain ⟨φ⟩ := hΔ
  let e := hj.homeomorphImage Δ
  refine ⟨⟨φ.trans e⟩, ?_⟩
  rw [disc_boundary (j '' Δ) (φ.trans e), disc_boundary Δ φ, image_image]
  rfl

/-- A disc attached to a cuff along a line is planar after that cuff is
capped. This supplies the disc-side obstruction for VIII (18.2), page 286. -/
theorem isPlanarInCappedCuff_disc_union_cuff {S : Type w} [TopologicalSpace S]
    (hS : IsSurface S) {C Δ L : Set S} {u v : S} (hC : C ∈ cuffs S)
    (hΔ : IsClosedDisc Δ) (hL : IsLineWithEnds L u v)
    (hinter : Δ ∩ C = L) (hLbd : L ⊆ discBd Δ) :
    GM07.IsPlanarInCappedCuff C (Δ ∪ C) := by
  have : T2Space S := hS.2.1
  obtain ⟨T, tT, j, D, hcap, _⟩ := GM07.exists_cappedCuff hS hC
  let := tT
  have : T2Space T := hcap.isSurface.2.1
  obtain ⟨himage, himagebd⟩ := disc_image_embedding hcap.isEmbedding hΔ
  have hjinter : j '' Δ ∩ D = j '' L := by
    rw [← hinter]
    apply Subset.antisymm
    · rintro x ⟨⟨y, hy, rfl⟩, hyD⟩
      have hyC : j y ∈ j '' C := hcap.inter_eq.subset ⟨mem_range_self y, hyD⟩
      obtain ⟨z, hz, hzy⟩ := hyC
      exact ⟨y, ⟨hy, hcap.isEmbedding.injective hzy ▸ hz⟩, rfl⟩
    · rintro x ⟨y, ⟨hy, hyC⟩, rfl⟩
      exact ⟨mem_image_of_mem j hy, Surface.discBd_subset D (hcap.discBd_eq ▸ mem_image_of_mem j hyC)⟩
  have hjLbd : j '' L ⊆ discBd (j '' Δ) := himagebd ▸ image_mono hLbd
  have hjLD : j '' L ⊆ discBd D := by
    rw [hcap.discBd_eq]
    exact image_mono (hinter ▸ inter_subset_right)
  obtain ⟨hunion, _⟩ := disc_union (j '' Δ) D (j '' L) (j u) (j v)
    himage hcap.isClosedDisc (IsLineWithEnds.map_of_embedding hcap.isEmbedding hL)
    hjinter hjLbd hjLD
  apply GM07.isPlanarInCappedCuff_of_cap hS hcap
  refine ⟨j '' Δ ∪ D, hunion, ?_⟩
  rw [image_union]
  exact union_subset_union_right _ (fun x hx => Surface.discBd_subset D (hcap.discBd_eq ▸ hx))

end GraphMinor.GM08
