module

public import GraphMinor.Surface.TopologyStatements
import GraphMinor.GM05.CutComplement
import GraphMinor.Surface.SurfacePull
import GraphMinor.Surface.CutComp

/-!
# Connected circle cuts

For Graph Minors V, (8.10), a circle with connected complement has a
connected cut surface. Its interior is that complement, and the
interior is dense in a surface. Thus the two alternatives with two
components in the library cutting theorem cannot occur.
-/

public section

namespace GraphMinor.GM05

open Set Topology Surface

universe u

/-- If the complement of the circle is connected, its cut surface is
connected: its interior is a homeomorphic dense connected subset. -/
theorem connected_cut_of_complement {Y S : Type u}
    [TopologicalSpace Y] [TopologicalSpace S]
    (hY : IsSurface Y) (hS : IsClosedSurface S) {ψ : Y → S} {C : Set S}
    (hψ : IsCutting ψ C) (hC : IsClosed C) (hc : IsConnected Cᶜ) : ConnectedSpace Y := by
  let : CompactSpace Y := hY.1
  let : T2Space Y := hY.2.1
  let : T2Space S := hS.2.1
  obtain ⟨e⟩ := cutting_complement_homeomorph hψ
  have he : (bd Y)ᶜ=ψ ⁻¹' Cᶜ := by
    rw [cutting_boundary_eq hψ hC hS,preimage_compl]
  let f : ↥((bd Y)ᶜ) ≃ₜ ↥(Cᶜ) := (Homeomorph.setCongr he).trans e
  let : ConnectedSpace ↥(Cᶜ) := isConnected_iff_connectedSpace.mp hc
  let : ConnectedSpace ↥((bd Y)ᶜ) := f.connectedSpace_iff.mpr inferInstance
  have hi : IsConnected (bd Y)ᶜ := isConnected_iff_connectedSpace.mpr inferInstance
  have hdense : closure (bd Y)ᶜ=univ :=
    Set.eq_univ_iff_forall.mpr fun y ↦ mem_closure_compl_bd (hY.2.2 y)
  exact connectedSpace_iff_univ.mpr (hdense ▸ hi.closure)

private theorem spaceComponents_connected (Y : Type u) [TopologicalSpace Y] [ConnectedSpace Y] :
    spaceComponents Y={univ} := by
  rw [spaceComponents_eq]
  ext A
  simp only [mem_range,mem_singleton_iff]
  constructor
  · rintro ⟨y,rfl⟩
    exact PreconnectedSpace.connectedComponent_eq_univ y
  · intro hA
    obtain ⟨y⟩ := (inferInstance : Nonempty Y)
    exact ⟨y,(PreconnectedSpace.connectedComponent_eq_univ y).trans hA.symm⟩

private theorem no_two_components {Y : Type u} [TopologicalSpace Y] [ConnectedSpace Y]
    {A B : Set Y} (hne : A ≠ B) (h : spaceComponents Y={A,B}) : False := by
  have ha : A=univ := by
    have hm : A ∈ spaceComponents Y := h.symm ▸ mem_insert A {B}
    simpa only [spaceComponents_connected,mem_singleton_iff] using hm
  have hb : B=univ := by
    have hm : B ∈ spaceComponents Y := h.symm ▸ mem_insert_of_mem A (mem_singleton B)
    simpa only [spaceComponents_connected,mem_singleton_iff] using hm
  exact hne (ha.trans hb.symm)

/-- On a connected cut surface only the simpler-surface alternative of
the proved library circle-cut theorem can occur. -/
theorem simpler_cut_of_connected {Y S : Type u} [TopologicalSpace Y] [TopologicalSpace S]
    [ConnectedSpace Y]
    (h : CutIsSimpler Y S ∨ CutHasCopy Y S ClosedCylinder ∨ CutHasDisc Y) :
    IsSimplerThan Y S := by
  rcases h with h|h|h
  · have hu : (univ : Set Y) ∈ spaceComponents Y := by rw [spaceComponents_connected]; exact mem_singleton _
    obtain ⟨a,b,c,a',b',c',⟨e⟩,he,hrest⟩ := h.2 _ hu
    exact ⟨a,b,c,a',b',c',⟨(Homeomorph.Set.univ Y).symm.trans e⟩,he,hrest⟩
  · obtain ⟨A,B,hne,hab,-⟩ := h
    exact (no_two_components hne hab).elim
  · obtain ⟨A,B,hne,hab,-⟩ := h
    exact (no_two_components hne hab).elim

end GraphMinor.GM05
