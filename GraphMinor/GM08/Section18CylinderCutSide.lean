module

public import GraphMinor.GM07.Defs
public import GraphMinor.Surface.TopologyStatements
import GraphMinor.GM08.Section18CutSide
import GraphMinor.GM08.Section18CylinderSide
import GraphMinor.Surface.CutTwoArc
import GraphMinor.GM07.LoopSides
import GraphMinor.GM07.CuffStep
import GraphMinor.GM07.CuffCollar
import GraphMinor.Surface.CutParallel

/-!
# A cylinder component of a circle cut

One cuff of a cylinder component is the lift of the cutting circle.
Its other cuff misses both lifts, and its image is a cuff of the original
surface. The component embeds in the original surface. Capping that other
cuff makes its image planar, so the cutting circle is near-planar. This
excludes cylinder components for non-near-planar circle cuts in VIII (18.2).
-/

public section

namespace GraphMinor.GM08

open Set Topology GraphMinor.Surface GraphMinor.GM11

universe w

/-- A cylinder side containing one whole lift of a circle cut lies in the
original surface, and capping one cuff of the original surface makes every
part of its image planar. This is the cylinder side in VIII (18.2), page 286. -/
theorem exists_cuff_planar_of_cylinder_cut_side {S T : Type w} [TopologicalSpace S]
    [TopologicalSpace T] (hS : IsSurface S) (hT : IsSurface T)
    {ψ : T → S} {F : Set S} (hcut : IsCutting ψ F) (hF : IsClosed F)
    {W A B : Set T} (hW : IsClopen W) [ConnectedSpace W]
    (hmodel : Nonempty (W ≃ₜ SurfaceModel 0 0 2))
    (hlifts : A ∪ B = ψ ⁻¹' F) (hBW : Disjoint B W) (hAW : A ⊆ W)
    (hA : IsOArc A) (hbA : BijOn ψ A F) :
    ∃ D ∈ cuffs S, (∀ Z ⊆ W, GM07.IsPlanarInCappedCuff D (ψ '' Z)) ∧
      ∀ z ∈ W, ψ z ∈ bd S → ψ z ∉ F → ψ z ∈ D := by
  have : CompactSpace T := hT.1
  have : T2Space T := hT.2.1
  have : T2Space S := hS.2.1
  have hSW : IsSurface W := isSurface_sub hT hW
  have : CompactSpace W := hSW.1
  let φ : W → S := fun x => ψ x.1
  have hφcont : Continuous φ := hcut.1.comp continuous_subtype_val
  have hφinj : Function.Injective φ := fun x y he =>
    Subtype.ext (injOn_cut_side hcut hlifts hBW hbA.injOn x.2 y.2 he)
  have hφ : IsEmbedding φ := (hφcont.isClosedEmbedding hφinj).isEmbedding
  have hAbd : A ⊆ bd T := fun x hx => hcut.2.2.2.2 (hlifts ▸ Or.inl hx)
  obtain ⟨C, hC, hAC⟩ := exists_cuff_sub hW.2 hA.isPreconnected
    (GM07.IsOArc.isConnected hA).nonempty hAW hAbd
  have hCO : IsOArc C := (cuff_statement W hSW).2.2 C hC
  have hCO' : IsOArc (Subtype.val '' C : Set T) :=
    isOArc_image hCO continuous_subtype_val.continuousOn Subtype.val_injective.injOn
  have heqA : (Subtype.val '' C : Set T) = A := (oarc_eq (Classical.choice hCO') hA hAC).symm
  have hcount : (cuffs W).ncard = 2 := GM07.ncard_cuffs_of_homeomorph_surfaceModel hmodel
  obtain ⟨E, hE, hEC⟩ := exists_ne_of_one_lt_ncard (s := cuffs W) (by rw [hcount]; omega) C
  have hEO : IsOArc E := (cuff_statement W hSW).2.2 E hE
  have hEoff : ∀ x ∈ E, ψ x.1 ∉ F := by
    intro x hx hxF
    have hxAB : x.1 ∈ A ∪ B := hlifts.symm ▸ hxF
    rcases hxAB with hxA | hxB
    · have hxC : x ∈ C := by
        have hxC' : x.1 ∈ Subtype.val '' C := heqA.symm ▸ hxA
        obtain ⟨y, hy, he⟩ := hxC'
        exact Subtype.val_injective he ▸ hy
      exact disjoint_left.mp (cuffs_disjoint hE hC hEC) hx hxC
    · exact disjoint_left.mp hBW hxB x.2
  have hEbd : φ '' E ⊆ bd S := by
    rintro _ ⟨x, hx, rfl⟩
    have hxbd : x ∈ bd W := by
      obtain ⟨z, hz, rfl⟩ := hE
      exact connectedComponentIn_subset _ _ hx
    exact bd_of_bd hcut hF ((mem_bd_sub hW.2).mp hxbd) (hEoff x hx)
  have hφEO : IsOArc (φ '' E) := isOArc_image hEO hφ.continuous.continuousOn hφ.injective.injOn
  have hD : φ '' E ∈ cuffs S := GM07.isCuff_of_isOArc_subset_bd hS hφEO hEbd
  have hb : BijOn φ E (φ '' E) := ⟨mapsTo_image φ E, hφ.injective.injOn, surjOn_image φ E⟩
  refine ⟨φ '' E, hD, fun Z hZ => ?_, fun z hz hzb hzF => ?_⟩
  swap
  · have hzT : z ∈ bd T := bd_lift hcut hF hzb hzF
    have hzW : (⟨z, hz⟩ : W) ∈ bd W := (mem_bd_sub hW.2).mpr hzT
    obtain ⟨⟨E', hE'⟩, hzE'⟩ := GM07.exists_cuff_of_bd hzW
    obtain ⟨x, y, -, hxy⟩ := Set.ncard_eq_two.mp hcount
    have hCm : C ∈ ({x, y} : Set (Set W)) := hxy ▸ hC
    have hEm : E ∈ ({x, y} : Set (Set W)) := hxy ▸ hE
    have hE'm : E' ∈ ({x, y} : Set (Set W)) := hxy ▸ hE'
    have hE'E : E' = E := by
      by_contra hne
      have hE'C : E' = C := by
        simp only [mem_insert_iff, mem_singleton_iff] at hCm hEm hE'm
        rcases hCm with rfl | rfl <;> rcases hEm with rfl | rfl <;>
          rcases hE'm with rfl | rfl <;> simp_all
      subst hE'C
      have : z ∈ Subtype.val '' E' := ⟨⟨z, hz⟩, hzE', rfl⟩
      rw [heqA] at this
      have hzpre : z ∈ ψ ⁻¹' F := hlifts ▸ (Or.inl this : z ∈ A ∪ B)
      exact hzF hzpre
    subst hE'E
    exact ⟨⟨z, hz⟩, hzE', rfl⟩
  have hp := isPlanarInCappedCuff_of_embedded_cylinder hSW hS hmodel hE hD hφ hb
    (Subtype.val ⁻¹' Z)
  have hZ' : φ '' (Subtype.val ⁻¹' Z) = ψ '' Z := by
    change (ψ ∘ Subtype.val) '' (Subtype.val ⁻¹' Z) = ψ '' Z
    rw [image_comp, Subtype.image_preimage_coe, inter_eq_right.mpr hZ]
  rwa [hZ'] at hp

/-- A cylinder side containing one whole lift of a circle cut makes the
original cutting circle near-planar. This is the cylinder-side exclusion
in VIII (18.2), page 286. -/
theorem isNearPlanar_of_cylinder_cut_side {S T : Type w} [TopologicalSpace S]
    [TopologicalSpace T] (hS : IsSurface S) (hT : IsSurface T)
    {ψ : T → S} {F : Set S} (hcut : IsCutting ψ F) (hF : IsClosed F)
    {W A B : Set T} (hW : IsClopen W) [ConnectedSpace W]
    (hmodel : Nonempty (W ≃ₜ SurfaceModel 0 0 2))
    (hlifts : A ∪ B = ψ ⁻¹' F) (hBW : Disjoint B W) (hAW : A ⊆ W)
    (hA : IsOArc A) (hbA : BijOn ψ A F) : GM07.IsNearPlanar F := by
  obtain ⟨D, hD, hp, -⟩ := exists_cuff_planar_of_cylinder_cut_side hS hT hcut hF hW hmodel
    hlifts hBW hAW hA hbA
  have hFA : ψ '' A = F := hbA.image_eq
  exact Or.inr ⟨D, hD, hFA ▸ hp A hAW⟩

end GraphMinor.GM08
