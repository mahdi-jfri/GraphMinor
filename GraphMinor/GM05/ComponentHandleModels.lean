module

public import GraphMinor.Surface.TopologyStatements
import GraphMinor.GM19.Section5o
import Mathlib.Topology.Connected.Clopen

/-!
# Transporting explicit component handle models

GM V, page 112, describes each orientable component by its number of
handles. In the proof of (8.14), keep the homeomorphisms to those
library models as data. They restrict to clopen parts and combine in
disjoint unions. These lemmas concern the existing surface models and
do not introduce another notion of surface or drawing.
-/

public section
namespace GraphMinor.GM05
open Set Topology Surface

/-- A clopen embedding identifies the connected components of a point
and of its image. -/
theorem component_homeomorph_of_clopen_embedding {S T : Type}
    [TopologicalSpace S] [TopologicalSpace T] {f : S → T}
    (hf : IsOpenEmbedding f) (hr : IsClopen (range f)) (x : S) :
    Nonempty ((connectedComponent x) ≃ₜ connectedComponent (f x)) := by
  have hsub : connectedComponent (f x) ⊆ range f :=
    isPreconnected_connectedComponent.subset_isClopen hr ⟨f x,mem_connectedComponent,mem_range_self x⟩
  have hc : IsConnected (f ⁻¹' connectedComponent (f x)) :=
    isConnected_connectedComponent.preimage_of_isOpenMap hf.injective hf.isOpenMap hsub
  have he : f ⁻¹' connectedComponent (f x)=connectedComponent x := by
    apply Subset.antisymm
    · exact hc.isPreconnected.subset_connectedComponent mem_connectedComponent
    · exact hf.continuous.mapsTo_connectedComponent x
  let e := hf.isEmbedding.homeomorphOfSubsetRange hsub
  exact ⟨(Homeomorph.setCongr he.symm).trans e⟩

/-- A connected surface with a specified handle model has that model
on every connected component. -/
theorem component_handle_models_of_connected {S : Type} [TopologicalSpace S]
    [ConnectedSpace S] {g : ℕ} (e : S ≃ₜ SurfaceModel g 0 0) :
    ∀ x : S, ∃ a : ℕ, Nonempty ((connectedComponent x) ≃ₜ SurfaceModel a 0 0) := by
  intro x
  exact ⟨g,⟨(GM19.homeoComponent x).symm.trans e⟩⟩

/-- Explicit handle-model representations of components restrict to
an open-and-closed part of the same surface. -/
theorem component_handle_models_clopen {S : Type} [TopologicalSpace S]
    (hmodels : ∀ x : S,∃ g : ℕ,Nonempty ((connectedComponent x) ≃ₜ SurfaceModel g 0 0))
    {U : Set S} (hU : IsClopen U) :
    ∀ x : U,∃ g : ℕ,Nonempty ((connectedComponent x) ≃ₜ SurfaceModel g 0 0) := by
  intro x
  obtain ⟨g,⟨e⟩⟩ := hmodels x.val
  have hr : IsClopen (range (Subtype.val : U → S)) := by simpa only [Subtype.range_coe_subtype,Set.ofPred_mem_eq] using hU
  obtain ⟨f⟩ := component_homeomorph_of_clopen_embedding hU.2.isOpenEmbedding_subtypeVal hr x
  exact ⟨g,⟨f.trans e⟩⟩

/-- A disjoint union retains the specified handle models of all
components of its summands. -/
theorem component_handle_models_sum {S T : Type} [TopologicalSpace S] [TopologicalSpace T]
    (hS : ∀ x : S,∃ g : ℕ,Nonempty ((connectedComponent x) ≃ₜ SurfaceModel g 0 0))
    (hT : ∀ x : T,∃ g : ℕ,Nonempty ((connectedComponent x) ≃ₜ SurfaceModel g 0 0)) :
    ∀ x : S⊕T,∃ g : ℕ,Nonempty ((connectedComponent x) ≃ₜ SurfaceModel g 0 0) := by
  rintro (x|x)
  · obtain ⟨g,⟨e⟩⟩ := hS x
    obtain ⟨f⟩ := component_homeomorph_of_clopen_embedding (IsOpenEmbedding.inl : IsOpenEmbedding (Sum.inl : S → S⊕T)) isClopen_range_inl x
    exact ⟨g,⟨f.symm.trans e⟩⟩
  · obtain ⟨g,⟨e⟩⟩ := hT x
    obtain ⟨f⟩ := component_homeomorph_of_clopen_embedding (IsOpenEmbedding.inr : IsOpenEmbedding (Sum.inr : T → S⊕T)) isClopen_range_inr x
    exact ⟨g,⟨f.symm.trans e⟩⟩

end GraphMinor.GM05
