module

public import GraphMinor.GM05.GraphComponents
import GraphMinor.GM06.Section3Basic

/-!
# Component indices of vertices and edges

For an enumeration of the components, assign each actual vertex and
edge its unique component index. Unused ambient labels receive a fixed
default index. The two ends of an edge have the same component index as
the edge. These maps combine component minor models in the proof of (8.8).
-/

public section

namespace GraphMinor.GM05

open Graph Set GM06

variable {α β : Type*} {H : Graph α β} {m : ℕ}

private lemma vertex_index_exists (C : Fin m → Graph α β)
    (hcover : ∀ D,IsGraphComponent D H → ∃ i,C i=D) {v : α} (hv : v∈V(H)) :
    ∃ i,v∈V(C i) := by
  obtain ⟨D,hD,hvD⟩ := exists_component_of_vertex hv
  obtain ⟨i,rfl⟩ := hcover D hD
  exact ⟨i,hvD⟩

private lemma edge_index_exists (C : Fin m → Graph α β)
    (hcover : ∀ D,IsGraphComponent D H → ∃ i,C i=D) {e : β} (he : e∈E(H)) :
    ∃ i,e∈E(C i) := by
  obtain ⟨D,hD,heD⟩ := exists_component_of_edge he
  obtain ⟨i,rfl⟩ := hcover D hD
  exact ⟨i,heD⟩

/-- The component index of a vertex, with a default for unused labels. -/
noncomputable def componentVertexIndex (C : Fin m → Graph α β)
    (hcover : ∀ D,IsGraphComponent D H → ∃ i,C i=D) (i₀ : Fin m) (v : α) : Fin m := by
  classical
  exact if hv : v∈V(H) then Classical.choose (vertex_index_exists C hcover hv) else i₀

/-- The component index of an edge, with a default for unused labels. -/
noncomputable def componentEdgeIndex (C : Fin m → Graph α β)
    (hcover : ∀ D,IsGraphComponent D H → ∃ i,C i=D) (i₀ : Fin m) (e : β) : Fin m := by
  classical
  exact if he : e∈E(H) then Classical.choose (edge_index_exists C hcover he) else i₀

/-- A vertex belongs to its assigned component. -/
theorem componentVertexIndex_mem (C : Fin m → Graph α β)
    (hcover : ∀ D,IsGraphComponent D H → ∃ i,C i=D) (i₀ : Fin m)
    {v : α} (hv : v∈V(H)) : v∈V(C (componentVertexIndex C hcover i₀ v)) := by
  simp only [componentVertexIndex,dite_eq_left hv]
  exact Classical.choose_spec (vertex_index_exists C hcover hv)

/-- An edge belongs to its assigned component. -/
theorem componentEdgeIndex_mem (C : Fin m → Graph α β)
    (hcover : ∀ D,IsGraphComponent D H → ∃ i,C i=D) (i₀ : Fin m)
    {e : β} (he : e∈E(H)) : e∈E(C (componentEdgeIndex C hcover i₀ e)) := by
  simp only [componentEdgeIndex,dite_eq_left he]
  exact Classical.choose_spec (edge_index_exists C hcover he)

/-- A vertex's assigned index is the index of every component containing it. -/
theorem componentVertexIndex_eq (C : Fin m → Graph α β) (hCi : ∀ i,IsGraphComponent (C i) H)
    (hinj : Function.Injective C) (hcover : ∀ D,IsGraphComponent D H → ∃ i,C i=D)
    (i₀ : Fin m) {v : α} (hv : v∈V(H)) {i : Fin m} (hi : v∈V(C i)) :
    componentVertexIndex C hcover i₀ v=i :=
  hinj ((hCi _).eq_of_mem_mem (hCi i) (componentVertexIndex_mem C hcover i₀ hv) hi)

/-- The component indices of the two ends equal the edge's component index. -/
theorem component_indices_of_link (C : Fin m → Graph α β) (hCi : ∀ i,IsGraphComponent (C i) H)
    (hinj : Function.Injective C) (hcover : ∀ D,IsGraphComponent D H → ∃ i,C i=D)
    (i₀ : Fin m) {e : β} {u v : α} (hl : H.IsLink e u v) :
    componentVertexIndex C hcover i₀ u=componentEdgeIndex C hcover i₀ e ∧
      componentVertexIndex C hcover i₀ v=componentEdgeIndex C hcover i₀ e := by
  have he := componentEdgeIndex_mem C hcover i₀ hl.edge_mem
  have hlC := ((hCi _).1.isLink_iff he).mpr hl
  exact ⟨componentVertexIndex_eq C hCi hinj hcover i₀ hl.left_mem hlC.left_mem,
    componentVertexIndex_eq C hCi hinj hcover i₀ hl.right_mem hlC.right_mem⟩

end GraphMinor.GM05
