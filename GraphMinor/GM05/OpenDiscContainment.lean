module

public import GraphMinor.Surface.TopologyStatements
import GraphMinor.GM05.OpenDiscContainmentConnected
import GraphMinor.GM05.ClopenDiscContainment
import GraphMinor.GM05.SurfaceComponents
import GraphMinor.Surface.TriLocal
import GraphMinor.Surface.CutComp

/-!
# Disc containment with the spherical-component exception removed

Restrict the open connected set to its containing component. The circle
condition restricts there because a disc is connected. Apply the
connected result, then include the resulting open disc in the surface.
-/

public section
namespace GraphMinor.GM05
open Set Surface Topology

/-- Graph Minors V, (8.11), page 113:
"If $r$ is a connected open subset of a surface $\Sigma$, and every subset of $r$ homeomorphic to a circle bounds a closed disc in $\Sigma$, then there is an open disc $\Delta \subseteq \Sigma$ with $r \subseteq \Delta$."
The printed statement fails when `r` is a whole spherical component.
The additional condition excludes exactly those cases. The connected
proof uses the already proved GM VII (11.2) and the maximal flat-set
construction of GM XI instead of the omitted argument in GM V. -/
theorem theorem_8_11_proof {S : Type} [TopologicalSpace S]
    (hS : IsClosedSurface S) {r : Set S} (hr : IsConnected r) (hro : IsOpen r)
    (H : ∀ F : Set S, F ⊆ r → IsOArc F → ∃ D : Set S, IsClosedDisc D ∧ F = discBd D)
    (hex : ∀ x ∈ r, ¬(IsSphere (connectedComponent x) ∧ r = connectedComponent x)) :
    ∃ D : Set S, IsOpenDisc D ∧ r ⊆ D := by
  let : T2Space S := hS.2.1
  have hs : IsSurface S := ⟨hS.1,hS.2.1,fun x ↦ (hS.2.2 x).isManifoldPoint⟩
  let : LocallyConnectedSpace S := hs.locallyConnected
  obtain ⟨x,hx⟩ := hr.nonempty
  let U : Set S := connectedComponent x
  have hU : IsClopen U := ⟨isClosed_connectedComponent,isOpen_connectedComponent⟩
  let : ConnectedSpace U := isConnected_iff_connectedSpace.mp isConnected_connectedComponent
  have hrU : r ⊆ U := hr.isPreconnected.subset_connectedComponent hx
  have hrange : r ⊆ range (Subtype.val : U → S) := fun y hy ↦ ⟨⟨y,hrU hy⟩,rfl⟩
  have hc : IsConnected (Subtype.val ⁻¹' r : Set U) :=
    hr.preimage_of_isOpenMap Subtype.val_injective hU.2.isOpenMap_subtype_val hrange
  have ho : IsOpen (Subtype.val ⁻¹' r : Set U) := hro.preimage continuous_subtype_val
  have he : ¬(IsSphere U ∧ (Subtype.val ⁻¹' r : Set U) = univ) := by
    rintro ⟨hsph,he⟩
    apply hex x hx
    refine ⟨hsph,Subset.antisymm hrU ?_⟩
    intro y hy
    have hh : (⟨y,hy⟩ : U) ∈ (Subtype.val ⁻¹' r : Set U) := he.symm ▸ mem_univ _
    exact hh
  obtain ⟨D,hD,hsub⟩ := lemma_8_11_connected_surface (isClosedSurface_clopen hS hU)
    hc ho (ambient_discs_clopen hU H) he
  refine ⟨Subtype.val '' D,⟨hU.2.isOpenMap_subtype_val _ hD.1,?_⟩,?_⟩
  · obtain ⟨φ⟩ := hD.2
    exact ⟨φ.trans (IsEmbedding.subtypeVal.homeomorphImage D)⟩
  · intro y hy
    exact ⟨⟨y,hrU hy⟩,hsub hy,rfl⟩

end GraphMinor.GM05
