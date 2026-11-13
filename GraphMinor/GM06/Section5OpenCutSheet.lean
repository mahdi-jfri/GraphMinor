module

public import GraphMinor.GM06.Section5CoverDisc
import GraphMinor.GM06.Section5CutStripSurface
import GraphMinor.GM06.Section5CoverProjection
import Mathlib.Topology.Homeomorph.Defs
import Mathlib.Topology.Constructions

/-!
# The open sheet selected by the one-path cut disc

Off the linkage path the cut projection is a bijective quotient map,
so its inverse is continuous. Put that inverse into the angular cover.
It is a section of the local homeomorphism over the open path complement,
so its image is open in the cover. The image is exactly the cut disc
with its two seam copies removed. This identifies the sheet needed
for the one-path region argument in VI Section 5.
-/

public section
namespace GraphMinor.GM06
open Set Topology GraphMinor.Surface

/-- The inverse of the cut projection off the sole linkage path is
an open sheet of the angular cover, with its exact image in the cut disc. -/
theorem exists_open_sheet_on_single_strip
    {G : Drawing ClosedCylinder} {θ : ℝ} (L : CylinderLinkage 1 G)
    (hG : IsCylinderSection5Drawing 1 G) (hθ : L.HasTheta θ)
    {D : Set (ℝ × ℝ)} (hD : IsClosedDisc D)
    (hBd : discBd D = liftedStripBoundary hG.1 L 1)
    (hstrip : D ⊆ {p : ℝ × ℝ | 1 ≤ p.1 ∧ p.1 ≤ 2}) :
    ∃ s : C(↥((L.pathDrawing 0).Uᶜ), CylinderCover), IsOpenEmbedding s ∧
      (∀ x, cylinderCoverProjection (s x) = x.1) ∧
      range s = (planeToCylinderCover '' D) ∩
        cylinderCoverProjection ⁻¹' (L.pathDrawing 0).Uᶜ := by
  classical
  let S := (L.pathDrawing 0).Uᶜ
  let f : D → ClosedCylinder := fun p => radialCylinderProjection p.1
  have hS : IsOpen S := (L.pathDrawing 0).isClosed_U.isOpen_compl
  have hcut := isCutAlongSet_single_strip_projection L hG hθ hD hBd hstrip
  let fA := S.restrictPreimage f
  have hQ : IsQuotientMap fA := hcut.quotientMap.restrictPreimage_isOpen hS
  have hi : Function.Injective fA := by
    intro p q hpq
    apply Subtype.ext
    exact single_strip_projection_inj_off_path L hG hθ hD hBd hstrip p.2
      (congrArg Subtype.val hpq)
  let H : (f ⁻¹' S) ≃ₜ S := (Equiv.ofBijective fA ⟨hi, hQ.surjective⟩).toHomeomorphOfContinuousOpen
    hQ.continuous (hQ.isCoinducing.isOpenMap_of_injective hi)
  let s : C(S, CylinderCover) :=
    ⟨fun x => planeToCylinderCover (H.symm x).1.1,
      continuous_planeToCylinderCover.comp (continuous_subtype_val.comp
        (continuous_subtype_val.comp H.symm.continuous))⟩
  have hproj (x : S) : cylinderCoverProjection (s x) = x.1 := by
    have h := congrArg Subtype.val (H.apply_symm_apply x)
    change f (H.symm x).1 = x.1 at h
    exact h
  have hcomp : cylinderCoverProjection ∘ s = Subtype.val := by
    funext x
    exact hproj x
  have hopen : IsOpenEmbedding s :=
    IsLocalHomeomorph.isOpenEmbedding_of_comp isLocalHomeomorph_cylinderCoverProjection
      (hcomp ▸ hS.isOpenEmbedding_subtypeVal) s.continuous
  refine ⟨s, hopen, hproj, ?_⟩
  ext p
  constructor
  · rintro ⟨x, rfl⟩
    refine ⟨⟨(H.symm x).1.1, (H.symm x).1.2, rfl⟩, ?_⟩
    change cylinderCoverProjection (s x) ∈ S
    rw [hproj]
    exact x.2
  · rintro ⟨⟨q, hq, rfl⟩, hoff⟩
    let qA : f ⁻¹' S := ⟨⟨q, hq⟩, hoff⟩
    refine ⟨H qA, ?_⟩
    change planeToCylinderCover (H.symm (H qA)).1.1 = planeToCylinderCover q
    rw [H.symm_apply_apply]

end GraphMinor.GM06
