module

public import GraphMinor.Surface.TopologyStatements
import GraphMinor.GM19.RadialExists
import GraphMinor.Surface.TriLocal

/-!
# Moving disc boundaries into a clopen part

A closed disc whose boundary lies in a clopen part lies entirely in
that part, since it is connected and meets its boundary. Pulling back
along the inclusion therefore preserves the ambient disc condition.
-/

public section
namespace GraphMinor.GM05
open Set Surface Topology

/-- The ambient disc condition restricts to an open-and-closed part. -/
theorem ambient_discs_clopen {S : Type} [TopologicalSpace S] {U r : Set S}
    (hU : IsClopen U)
    (H : ∀ F : Set S, F ⊆ r → IsOArc F → ∃ D : Set S, IsClosedDisc D ∧ F = discBd D) :
    ∀ F : Set U, F ⊆ Subtype.val ⁻¹' r → IsOArc F →
      ∃ D : Set U, IsClosedDisc D ∧ F = discBd D := by
  intro F hFr hF
  have hFi : IsOArc (Subtype.val '' F : Set S) := by
    obtain ⟨φ⟩ := hF
    exact ⟨φ.trans (IsEmbedding.subtypeVal.homeomorphImage F)⟩
  obtain ⟨D,hD,hbd⟩ := H _ (by rintro _ ⟨x,hx,rfl⟩; exact hFr hx) hFi
  obtain ⟨φ⟩ := hF
  let z : U := φ 1
  have hzF : z ∈ F := (φ 1).2
  have hzD : z.val ∈ D := Surface.discBd_subset D (hbd ▸ mem_image_of_mem _ hzF)
  have hDU : D ⊆ U := (hD.isPathConnected.isConnected.isPreconnected).subset_isClopen hU ⟨z.val,hzD,z.2⟩
  have hDrange : D ⊆ range (Subtype.val : U → S) := fun x hx ↦ ⟨⟨x,hDU hx⟩,rfl⟩
  let e : (Subtype.val ⁻¹' D : Set U) ≃ₜ D :=
    IsEmbedding.subtypeVal.homeomorphOfSubsetRange hDrange
  have hp : IsClosedDisc (Subtype.val ⁻¹' D : Set U) := by
    obtain ⟨ψ⟩ := hD
    exact ⟨ψ.trans e.symm⟩
  have hb := (GM19.isClosedDisc_image hp IsEmbedding.subtypeVal).2
  rw [image_preimage_eq_of_subset hDrange] at hb
  refine ⟨_,hp,?_⟩
  apply (Set.image_injective.mpr (Subtype.val_injective : Function.Injective (Subtype.val : U → S)))
  exact hbd.trans hb

end GraphMinor.GM05
