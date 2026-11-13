module

public import GraphMinor.GM06.Section5CapDrawing
public import GraphMinor.GM11.LocalCone
import GraphMinor.GM06.Section5FiniteDiscardedEnclosures
import GraphMinor.GM06.Section5CylinderComponentEnclosures
import GraphMinor.GM06.Section5CappedPuncture
import GraphMinor.Surface.SurfacePull
import GraphMinor.GM11.Regions

/-!
# Pulling attached discarded-side enclosures back to the cylinder

For VI (5.5), page 130, cap the cylinder and construct the finite
region enclosures in the sphere. The retained barrier contains the
cuffs. Any complementary region meeting the discarded drawing lies
in the open annulus, so its enclosing disc, with the attachment
possibly added, lies in the closed annulus. The closed embedding
then pulls back its disc, boundary and interior cover.
-/

public section
namespace GraphMinor.GM06
open Set Topology GraphMinor.Surface GraphMinor.GM11

/-- Cuff-containing punctured barriers give a finite cylinder-disc
cover of the discarded side away from its sole attachment. -/
theorem exists_cylinder_discs_enclosing_attached_side
    {Γ T H : Drawing ClosedCylinder} (hT : T.IsSubdrawing Γ) (hH : H.IsSubdrawing Γ)
    {s : ClosedCylinder} (hsT : s ∈ T.U) (hTp : IsConnected (T.U \ {s}))
    (hscl : s ∈ closure (T.U \ {s})) (hbdT : bd ClosedCylinder ⊆ T.U)
    (hover : H.U ∩ T.U ⊆ {s}) (hcover : Γ.U ⊆ T.U ∪ H.U)
    {Φ : C(ClosedUnitDisc, OnePoint EuclideanPlane)}
    (hp : IsPolar (cylinderSphereDrawing Γ) (cylinderToSphere s) Φ) :
    ∃ F : Set (Set ClosedCylinder), F.Finite ∧
      (∀ D ∈ F, IsClosedDisc D ∧ discBd D ∩ Γ.U ⊆ {s}) ∧
      H.U \ {s} ⊆ ⋃ D ∈ F, discInt D := by
  let : Nonempty ClosedCylinder := ⟨s⟩
  have hsph : IsSphere (OnePoint EuclideanPlane) := ⟨Homeomorph.refl _⟩
  have hS := IsSphere.isClosedSurface hsph
  let : ConnectedSpace (OnePoint EuclideanPlane) := hS.2
  have hTc : (cylinderSphereDrawing T).IsSubdrawing (cylinderSphereDrawing Γ) := by
    constructor
    · rw [cylinderSphereDrawing_V, cylinderSphereDrawing_V]; exact image_mono hT.1
    · rw [cylinderSphereDrawing_E, cylinderSphereDrawing_E]; exact image_mono hT.2
  have hHc : (cylinderSphereDrawing H).IsSubdrawing (cylinderSphereDrawing Γ) := by
    constructor
    · rw [cylinderSphereDrawing_V, cylinderSphereDrawing_V]; exact image_mono hH.1
    · rw [cylinderSphereDrawing_E, cylinderSphereDrawing_E]; exact image_mono hH.2
  have hsc : cylinderToSphere s ∈ (cylinderSphereDrawing T).U := by
    rw [cylinderSphereDrawing_U]; exact mem_image_of_mem _ hsT
  have hoverc : (cylinderSphereDrawing H).U ∩ (cylinderSphereDrawing T).U ⊆ {cylinderToSphere s} := by
    rw [cylinderSphereDrawing_U, cylinderSphereDrawing_U]
    rintro y ⟨⟨x, hxH, rfl⟩, z, hzT, hzx⟩
    have he : z = x := injective_cylinderToSphere hzx
    have hxs : x = s := hover ⟨hxH, he ▸ hzT⟩
    exact congrArg cylinderToSphere hxs
  have hcoverc : (cylinderSphereDrawing Γ).U ⊆
      (cylinderSphereDrawing T).U ∪ (cylinderSphereDrawing H).U := by
    rw [cylinderSphereDrawing_U, cylinderSphereDrawing_U, cylinderSphereDrawing_U, ← image_union]
    exact image_mono hcover
  obtain ⟨F, hF, hdisc, hcov⟩ := exists_finite_discarded_region_enclosures
    hS.1 hsph hTc hHc hp hsc
    (isConnected_punctured_cylinderSphereDrawing_of_source T s hTp).isPreconnected
    (mem_closure_punctured_cylinderSphereDrawing_of_source T s hscl) hoverc hcoverc
  have hsub (D) (hD : D ∈ F) : D ⊆ range cylinderToSphere := by
    obtain ⟨_, _, _, r, hr, hmeet, hDr⟩ := hdisc D hD
    have hrcuff : Disjoint r (cylinderToSphere '' bd ClosedCylinder) := by
      apply disjoint_left.mpr
      rintro y hyr ⟨x, hx, rfl⟩
      exact region_subset hr hyr (by rw [cylinderSphereDrawing_U]; exact mem_image_of_mem _ (hbdT hx))
    obtain ⟨y, hyH, hyr⟩ := hmeet
    have hyrange : y ∈ range cylinderToSphere := by
      rw [cylinderSphereDrawing_U] at hyH
      exact image_subset_range _ _ hyH
    have hrann := subset_open_annulus_of_preconnected_of_disjoint_cuffs
      (region_isPreconnected hr) hrcuff ⟨y, hyr, hyrange⟩
    intro z hz
    rcases hDr hz with hzr | hzs
    · exact image_subset_range _ _ (hrann hzr)
    · exact mem_singleton_iff.mp hzs ▸ mem_range_self s
  have hpull (D) (hD : D ∈ F) := isClosedDisc_preimage
    isClosedEmbedding_cylinderToSphere (hdisc D hD).1 (hsub D hD)
  refine ⟨(fun D => cylinderToSphere ⁻¹' D) '' F, hF.image _, ?_, ?_⟩
  · rintro _ ⟨D, hD, rfl⟩
    refine ⟨(hpull D hD).1, ?_⟩
    rw [(hpull D hD).2]
    rintro x ⟨hxb, hxΓ⟩
    have hxcap : cylinderToSphere x ∈ (cylinderSphereDrawing Γ).U := by
      rw [cylinderSphereDrawing_U]; exact mem_image_of_mem _ hxΓ
    exact injective_cylinderToSphere ((hdisc D hD).2.1 ⟨hxb, hxcap⟩)
  · rintro x ⟨hxH, hxs⟩
    have hxcap : cylinderToSphere x ∈ (cylinderSphereDrawing H).U \ {cylinderToSphere s} := by
      refine ⟨?_, fun he => hxs (injective_cylinderToSphere he)⟩
      rw [cylinderSphereDrawing_U]; exact mem_image_of_mem _ hxH
    obtain ⟨D, hD, hxD⟩ := mem_iUnion₂.mp (hcov hxcap)
    refine mem_iUnion₂.mpr ⟨cylinderToSphere ⁻¹' D, mem_image_of_mem _ hD, ?_⟩
    refine ⟨hxD.1, ?_⟩
    rw [(hpull D hD).2]
    exact hxD.2

end GraphMinor.GM06
