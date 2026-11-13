module

public import GraphMinor.Surface.TopologyStatements
public import GraphMinor.GM19.Defs2
import GraphMinor.GM19.FragmentOrient
import GraphMinor.Surface.CutComp

/-!
# Orienting the components of a cut surface

The orientability step of Graph Minors V, (8.10), uses the orientation
of the original surface on the interior of the cut surface. The
cutting map is injective there. The proved extension of an interior
orientation to a surface then orients each connected component.
-/

public section

namespace GraphMinor.GM05

open Set Topology Surface GM19

/-- A connected surface cut from an orientable surface is orientable.
Pull the orientation back on interior discs and extend it to the cuffs. -/
theorem orientable_of_cutting {Y S : Type} [TopologicalSpace Y] [TopologicalSpace S]
    [T2Space S] [ConnectedSpace Y] (hY : IsSurface Y)
    {ψ : Y → S} {C : Set S} (hψ : IsCutting ψ C) (hO : IsOrientableSurface S) :
    IsOrientableSurface Y := by
  let : T2Space Y := hY.2.1
  obtain ⟨ω⟩ := hO
  have hp : IsPartialOrientation {D : Set Y | D ⊆ (bd Y)ᶜ} (pullPos ψ ω.pos) :=
    (ω.isPartial univ).pull fun D hD ↦ ⟨hψ.1.continuousOn,?_,mem_univ _⟩
  · exact isOrientable_of_interior hY hp
  · intro x hx y hy he
    apply hψ.2.2.1 _ _ he
    · exact fun h ↦ hD hx (hψ.2.2.2.2 h)
    · exact fun h ↦ hD hy (hψ.2.2.2.2 h)

/-- The orientation of the original surface induces an orientation of
each connected open-and-closed part of the cut surface. -/
theorem orientable_cut_component {Y S : Type} [TopologicalSpace Y] [TopologicalSpace S]
    [T2Space S] (hY : IsSurface Y) {ψ : Y → S} {C : Set S}
    (hψ : IsCutting ψ C) (hO : IsOrientableSurface S)
    {W : Set Y} (hW : IsClopen W) [ConnectedSpace W] : IsOrientableSurface W := by
  let : T2Space Y := hY.2.1
  obtain ⟨ω⟩ := hO
  have hp : IsPartialOrientation {D : Set W | D ⊆ (bd W)ᶜ}
      (pullPos (ψ ∘ Subtype.val) ω.pos) :=
    (ω.isPartial univ).pull fun D hD ↦
      ⟨(hψ.1.comp continuous_subtype_val).continuousOn,?_,mem_univ _⟩
  · exact isOrientable_of_interior (isSurface_sub hY hW) hp
  · intro x hx y hy he
    apply Subtype.ext
    apply hψ.2.2.1 _ _ he
    · exact fun h ↦ hD hx ((mem_bd_sub hW.2).mpr (hψ.2.2.2.2 h))
    · exact fun h ↦ hD hy ((mem_bd_sub hW.2).mpr (hψ.2.2.2.2 h))

end GraphMinor.GM05
