module

public import GraphMinor.Surface.TopologyStatements
import GraphMinor.Surface.DiscArcs

/-!
# A disc side of a cut

If a cut has two lifts of its cutting set, a side meeting only one lift
maps injectively to the original surface. A disc side consequently gives
an embedded disc there, with its boundary carried to the boundary of the
image disc. These are local facts for excluding the disc-side cases in
VIII (18.2).
-/

public section

namespace GraphMinor.GM08

open Set Topology GraphMinor.Surface

universe w

/-- A side of a cut meeting only the injective lift of the cutting set
maps injectively into the original surface. -/
theorem injOn_cut_side {S T : Type w} [TopologicalSpace S] [TopologicalSpace T]
    {ψ : T → S} {F : Set S} (hcut : IsCutting ψ F) {W A B : Set T}
    (hlifts : A ∪ B = ψ ⁻¹' F) (hBW : Disjoint B W) (hA : InjOn ψ A) :
    InjOn ψ W := by
  intro x hx y hy hxy
  by_cases hxF : ψ x ∈ F
  · have hxA : x ∈ A := ((hlifts.symm ▸ hxF : x ∈ A ∪ B)).resolve_right
      (fun hxB => disjoint_left.mp hBW hxB hx)
    have hyF : ψ y ∈ F := hxy ▸ hxF
    have hyA : y ∈ A := ((hlifts.symm ▸ hyF : y ∈ A ∪ B)).resolve_right
      (fun hyB => disjoint_left.mp hBW hyB hy)
    exact hA hxA hyA hxy
  · exact hcut.2.2.1 hxF (fun hyF => hxF (hxy.symm ▸ hyF)) hxy

/-- A disc side of a cut, containing only one injective lift of the cutting
set, gives a disc in the original surface with the indicated boundary.
This is a local step for VIII (18.2), page 286. -/
theorem isClosedDisc_image_cut_side {S T : Type w} [TopologicalSpace S]
    [TopologicalSpace T] [T2Space S] {ψ : T → S} {F : Set S}
    (hcut : IsCutting ψ F) {W A B : Set T} (hW : IsClosedDisc W)
    (hlifts : A ∪ B = ψ ⁻¹' F) (hBW : Disjoint B W) (hA : InjOn ψ A) :
    IsClosedDisc (ψ '' W) ∧ discBd (ψ '' W) = ψ '' discBd W := by
  obtain ⟨φ⟩ := hW
  have : CompactSpace ClosedUnitDisc := isCompact_iff_compactSpace.mp (isCompact_closedBall _ _)
  have : CompactSpace W := φ.compactSpace
  let f : W → S := fun x => ψ x.1
  have hf : Continuous f := hcut.1.comp continuous_subtype_val
  have hinj : Function.Injective f := fun x y h =>
    Subtype.ext (injOn_cut_side hcut hlifts hBW hA x.2 y.2 h)
  let e₀ : W ≃ₜ range f := (hf.isClosedEmbedding hinj).isEmbedding.toHomeomorph
  have hrange : range f = ψ '' W := by
    ext x
    constructor
    · rintro ⟨y, rfl⟩
      exact ⟨y.1, y.2, rfl⟩
    · rintro ⟨y, hy, rfl⟩
      exact ⟨⟨y, hy⟩, rfl⟩
  let e : W ≃ₜ ψ '' W := e₀.trans (Homeomorph.setCongr hrange)
  refine ⟨⟨φ.trans e⟩, ?_⟩
  rw [disc_boundary (ψ '' W) (φ.trans e), disc_boundary W φ, image_image]
  rfl

end GraphMinor.GM08
