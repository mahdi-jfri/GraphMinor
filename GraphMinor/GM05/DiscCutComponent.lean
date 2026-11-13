module

public import GraphMinor.Surface.TopologyStatements
import GraphMinor.Surface.CutComp
import GraphMinor.Surface.CutIArc
import GraphMinor.Surface.ModelCriterion
import GraphMinor.Surface.Wedge

/-!
# A disc component of a circle cut

In the separating case of Graph Minors V, (8.10), a genus-zero
component with one cuff is a closed disc. The cutting map is injective
on this component: its boundary contains just one lift of the circle.
Its image is therefore a closed disc bounded by the original circle.
-/

public section

namespace GraphMinor.GM05

open Set Topology Surface

universe u

/-- The cutting map is injective on a part that misses the other
boundary lift. -/
theorem cutting_injOn_one_lift {Y S : Type u} [TopologicalSpace Y] [TopologicalSpace S]
    {ψ : Y → S} {C : Set S} (hψ : IsCutting ψ C) {X X' W : Set Y}
    (hu : X ∪ X'=ψ ⁻¹' C) (hb : BijOn ψ X C) (hd : Disjoint W X') : InjOn ψ W := by
  intro x hx y hy he
  by_cases hxc : ψ x ∈ C
  · have hxX : x ∈ X := by
      rcases (hu.symm ▸ hxc : x ∈ X ∪ X') with h|h
      · exact h
      · exact (Set.disjoint_left.mp hd hx h).elim
    have hyX : y ∈ X := by
      have hyc : y ∈ ψ ⁻¹' C := by change ψ y ∈ C; rw [← he]; exact hxc
      rcases (hu.symm ▸ hyc : y ∈ X ∪ X') with h|h
      · exact h
      · exact (Set.disjoint_left.mp hd hy h).elim
    exact hb.injOn hxX hyX he
  · apply hψ.2.2.1 hxc _ he
    change ψ y ∉ C
    rw [← he]
    exact hxc

/-- The intrinsic disc boundary of an open part is its intersection
with the ambient surface boundary. -/
theorem discBd_of_open {Y : Type u} [TopologicalSpace Y] {W : Set Y} (hW : IsOpen W) :
    discBd W=W ∩ bd Y := by
  ext x
  constructor
  · rintro ⟨y,hy,rfl⟩
    exact ⟨y.2,(mem_bd_sub hW).mp hy⟩
  · rintro ⟨hxW,hxbd⟩
    exact ⟨⟨x,hxW⟩,(mem_bd_sub hW).mpr hxbd,rfl⟩

/-- A disc component with just one lifted boundary circle maps to a
closed disc bounded by the original circle. This proves the disc
alternative in the separating calculation of GM V, (8.10). -/
theorem bounds_disc_of_cut_disc_component {Y S : Type u}
    [TopologicalSpace Y] [TopologicalSpace S] [T2Space S]
    (hY : IsSurface Y) {ψ : Y → S} {C : Set S} (hψ : IsCutting ψ C)
    {X X' W : Set Y} (hu : X ∪ X'=ψ ⁻¹' C) (hb : BijOn ψ X C)
    (hbd : bd Y=X ∪ X') (hW : IsClopen W) (hs : X ⊆ W) (hd : Disjoint W X')
    (eW : W ≃ₜ SurfaceModel 0 0 1) :
    ∃ D : Set S, IsClosedDisc D ∧ C=discBd D := by
  let : CompactSpace Y := hY.1
  let : ConnectedSpace (SurfaceModel 0 0 1) := (modelCriterion.1 0 0 1).2
  let : Nonempty W := eW.toEquiv.nonempty
  let : Nonempty Y := (inferInstance : Nonempty W).map Subtype.val
  obtain ⟨d⟩ := nonempty_disc_homeo
  have hdisc : IsClosedDisc W := ⟨(eW.trans d).symm⟩
  have hboundary : discBd W=X := by
    rw [discBd_of_open hW.2,hbd]
    apply Subset.antisymm
    · rintro x ⟨hw,hx|hx'⟩
      · exact hx
      · exact (Set.disjoint_left.mp hd hw hx').elim
    · intro x hx
      exact ⟨hs hx,Or.inl hx⟩
  have hi := cutting_injOn_one_lift hψ hu hb hd
  obtain ⟨hD,hbD⟩ := Surface.isClosedDisc_image_injOn hdisc hW.1.isCompact hψ.1.continuousOn hi
  refine ⟨ψ '' W,hD,?_⟩
  rw [hbD,hboundary,hb.image_eq]

end GraphMinor.GM05
