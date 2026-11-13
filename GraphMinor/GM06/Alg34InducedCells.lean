module

public import GraphMinor.GM06.Alg34CellPartition
public import GraphMinor.GM06.Section3Induce

/-!
# Cells of the drawing induced by active vertices

An original vertex remains exactly when its label is active. An original
edge remains exactly when both endpoint labels are active. Thus the
point set of the induced drawing is the union of precisely the cells
selected by the finite active-cell test. This identifies its complement
using the supplied cell partition, before recomputing the new regions.
-/

@[expose] public section
namespace GraphMinor.Compute.GM06DrawingRep

open Set Surface GM06 GM11

universe u
variable {x : GM06DrawingData} {S : Type u} [TopologicalSpace S]
  {G : Drawing S} {Δ : Set (Set S)}

/-- The actual vertex subset denoted by a list of active finite labels. -/
def vertexImage (h : GM06DrawingRep x G Δ) (vs : List (Fin x.n)) : Set S :=
  (fun v => (h.vertex v).val) '' GM06DrawingData.block vs

/-- Injective vertex labels preserve membership in the active list. -/
theorem vertex_mem_image_iff (h : GM06DrawingRep x G Δ) (vs : List (Fin x.n)) (v : Fin x.n) :
    (h.vertex v).val ∈ h.vertexImage vs ↔ v ∈ vs := by
  constructor
  · rintro ⟨w, hw, heq⟩
    have hwv : w = v := h.vertex.injective (Subtype.ext heq)
    exact hwv ▸ hw
  · exact fun hv => ⟨v, hv, rfl⟩

/-- The active vertex image is contained in the represented drawing's vertices. -/
theorem vertexImage_subset (h : GM06DrawingRep x G Δ) (vs : List (Fin x.n)) :
    h.vertexImage vs ⊆ G.V := by
  rintro p ⟨v, _, rfl⟩
  exact (h.vertex v).property

/-- The induced drawing retains exactly the supplied edges whose two
endpoint labels are active, including loops. -/
theorem edge_mem_induced_iff [T1Space S] (h : GM06DrawingRep x G Δ)
    (vs : List (Fin x.n)) (e : Fin x.ends.length) :
    (h.edge e).val ∈ (induceDrawing G (h.vertexImage vs)).E ↔
      x.ends[e].1 ∈ vs ∧ x.ends[e].2 ∈ vs := by
  rw [induceDrawing_E]
  change ((h.edge e).val ∈ G.E ∧ closure (h.edge e).val ∩ G.V ⊆ h.vertexImage vs) ↔ _
  rw [and_iff_right (h.edge e).property, h.ends e, pair_subset_iff,
    h.vertex_mem_image_iff, h.vertex_mem_image_iff]

/-- The point set of the induced drawing is exactly the union selected
by the finite active-cell test on the supplied original drawing. -/
theorem induced_U_eq_active_cells [T1Space S] (h : GM06DrawingRep x G Δ)
    (vs : List (Fin x.n)) :
    (induceDrawing G (h.vertexImage vs)).U =
      ⋃ a ∈ {a | x.activeCell vs a = true}, h.cell a := by
  rw [induceDrawing_U G (h.vertexImage_subset vs)]
  ext p
  constructor
  · rintro (hp | hp)
    · obtain ⟨v, hv, rfl⟩ := hp
      exact mem_iUnion₂.mpr ⟨.inl v, by simpa [GM06DrawingData.activeCell, GM06DrawingData.block] using hv,
        Set.mem_singleton _⟩
    · obtain ⟨e, he, hpe⟩ := mem_iUnion₂.mp hp
      have heG : e ∈ G.E := (induceDrawing_E G (h.vertexImage vs)).subset he |>.1
      obtain ⟨a, ha⟩ := h.edge.surjective ⟨e, heG⟩
      have heq : (h.edge a).val = e := congrArg Subtype.val ha
      have hactive := (h.edge_mem_induced_iff vs a).mp (heq.symm ▸ he)
      refine mem_iUnion₂.mpr ⟨.inr (.inl a), ?_, ?_⟩
      · simpa only [mem_setOf_eq, GM06DrawingData.activeCell, decide_eq_true_eq] using hactive
      · change p ∈ (h.edge a).val
        rw [heq]
        exact hpe
  · intro hp
    obtain ⟨a, ha, hpa⟩ := mem_iUnion₂.mp hp
    rcases a with v | e | r
    · have hv : v ∈ vs := by simpa [GM06DrawingData.activeCell] using ha
      exact Or.inl ⟨v, hv, hpa.symm⟩
    · have he : x.ends[e].1 ∈ vs ∧ x.ends[e].2 ∈ vs := by
        simpa only [mem_setOf_eq, GM06DrawingData.activeCell, decide_eq_true_eq] using ha
      exact Or.inr (mem_iUnion₂.mpr ⟨(h.edge e).val, (h.edge_mem_induced_iff vs e).mpr he, hpa⟩)
    · simp [GM06DrawingData.activeCell] at ha

end GraphMinor.Compute.GM06DrawingRep
