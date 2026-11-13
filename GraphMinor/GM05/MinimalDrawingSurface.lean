module

public import GraphMinor.Planar.Defs
public import GraphMinor.GM05.SurfaceDescent
import GraphMinor.GM05.GenusDeletion
import GraphMinor.GM05.SurfaceComponents
import GraphMinor.GM05.DrawingSupportTransport
import GraphMinor.GM05.EmptyDrawingPlanar
import GraphMinor.GM19.CapModel
import GraphMinor.Surface.CutComp

/-!
# Choosing a minimal drawing surface without unused components

For GM V, (8.14), minimize the well-founded genus multiset among closed
orientable surfaces drawing the fixed graph. This implies minimality
in the printed list order. Every drawing on the chosen surface uses
every component: otherwise deleting that component gives a smaller
multiset and the support embedding carries the graph to it.
-/

public section
namespace GraphMinor.GM05
open Set Topology Surface GM19
universe u v

/-- Multiset minimality rules out unused components for every drawing
of a nonplanar graph on that surface. -/
theorem drawing_uses_components_of_multiset_minimal {α : Type u} {β : Type v}
    {H : Graph α β} (hnp : ¬GraphMinor.IsPlanar H)
    {S : Type} [TopologicalSpace S] (hS : IsClosedSurface S) (hO : IsOrientableSurface S)
    (hmin : ∀ (T : Type) [TopologicalSpace T] (hT : IsClosedSurface T),
      IsOrientableSurface T → Nonempty (GraphDrawing H T) →
      ¬Multiset.IsDershowitzMannaLT (surfaceGenusList T hT : Multiset ℕ)
        (surfaceGenusList S hS : Multiset ℕ))
    (Γ : GraphDrawing H S) (x : S) :
    (Γ.drawing.U ∩ connectedComponent x).Nonempty := by
  classical
  let : T2Space S := hS.2.1
  let : CompactSpace S := hS.1
  let : Nonempty S := ⟨x⟩
  have hs : IsSurface S := ⟨hS.1,hS.2.1,fun x ↦ (hS.2.2 x).isManifoldPoint⟩
  let : LocallyConnectedSpace S := hs.locallyConnected
  by_contra hn
  let U : Set S := connectedComponent x
  have hU : IsClopen U := ⟨isClosed_connectedComponent,isOpen_connectedComponent⟩
  let : ConnectedSpace U := isConnected_iff_connectedSpace.mp isConnected_connectedComponent
  have hUR : Γ.drawing.U ⊆ Uᶜ := by
    intro y hy hyU
    exact hn ⟨y,hy,hyU⟩
  have hne : Γ.drawing.U.Nonempty := by
    by_contra he
    exact hnp (isPlanar_of_empty_drawing_support Γ (not_nonempty_iff_eq_empty.mp he))
  let R := ↥(Uᶜ)
  let : Nonempty R := ⟨⟨hne.choose,hUR hne.choose_spec⟩⟩
  have hR : IsClosedSurface R := isClosedSurface_clopen hS hU.compl
  let : T2Space R := hR.2.1
  have hRO : IsOrientableSurface R := isOrientable_of_embedding IsEmbedding.subtypeVal hO
  let j : Γ.drawing.U → R := fun y ↦ ⟨y.val,hUR y.prop⟩
  have hj : IsEmbedding j := IsEmbedding.subtypeVal.codRestrict _ _
  have hdraw := graphDrawing_of_support_embedding Γ j hj
  exact hmin R hR hRO hdraw
    (genus_multiset_delete_component hS hU (isClosedSurface_clopen hS hU) hR)

/-- The minimal-surface choice in GM V, proof of (8.14), strengthened
to discard unused components. The input is an actual drawing on some
closed orientable surface, not a genus-minimality assumption. -/
theorem exists_minimal_drawing_surface {α : Type u} {β : Type v}
    {H : Graph α β} (hnp : ¬GraphMinor.IsPlanar H)
    (hex : ∃ (S : Type) (_ : TopologicalSpace S) (_hS : IsClosedSurface S),
      IsOrientableSurface S ∧ Nonempty (GraphDrawing H S)) :
    ∃ (S : Type) (_ : TopologicalSpace S) (hS : IsClosedSurface S),
      IsOrientableSurface S ∧ Nonempty (GraphDrawing H S) ∧
      (∀ (T : Type) [TopologicalSpace T] (hT : IsClosedSurface T),
        IsOrientableSurface T → Nonempty (GraphDrawing H T) → ¬SurfaceGenusLT hT hS) ∧
      ∀ (Γ : GraphDrawing H S) (x : S), (Γ.drawing.U ∩ connectedComponent x).Nonempty := by
  classical
  let P : Set (Multiset ℕ) := {M | ∃ (S : Type) (_ : TopologicalSpace S) (hS : IsClosedSurface S),
    IsOrientableSurface S ∧ Nonempty (GraphDrawing H S) ∧ (surfaceGenusList S hS : Multiset ℕ)=M}
  have hp : P.Nonempty := by
    obtain ⟨S,τ,hS,hO,hD⟩ := hex
    exact ⟨_,S,τ,hS,hO,hD,rfl⟩
  obtain ⟨M,hM,hminimal⟩ := Multiset.wellFounded_isDershowitzMannaLT.has_min P hp
  obtain ⟨S,τ,hS,hO,hD,he⟩ := hM
  have hm : ∀ (T : Type) [TopologicalSpace T] (hT : IsClosedSurface T),
      IsOrientableSurface T → Nonempty (GraphDrawing H T) →
      ¬Multiset.IsDershowitzMannaLT (surfaceGenusList T hT : Multiset ℕ)
        (surfaceGenusList S hS : Multiset ℕ) := by
    intro T τT hT hTO hTD hlt
    exact hminimal _ ⟨T,τT,hT,hTO,hTD,rfl⟩ (he ▸ hlt)
  refine ⟨S,τ,hS,hO,hD,?_,?_⟩
  · intro T τT hT hTO hTD hlt
    exact hm T hT hTO hTD (genusListLT_multiset (surfaceGenusList_sorted T hT) hlt)
  · exact drawing_uses_components_of_multiset_minimal hnp hS hO hm

end GraphMinor.GM05
