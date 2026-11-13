module

public import GraphMinor.GM06.Alg34CellRep
import GraphMinor.GM06.Alg34Boundary

/-!
# The supplied drawing cells partition the disc

Vertex points, open edges, and regions are disjoint and cover the
ambient space. Their supplied labels are bijective in each kind.
Consequently overlapping labelled cells have the same label, and every
point lies in one labelled cell. These facts turn the closure table
into an exact finite test for closure incidence during region updates.
-/

public section
namespace GraphMinor.Compute.GM06DrawingRep

open Set Surface GM11

universe u
variable {x : GM06DrawingData} {S : Type u} [TopologicalSpace S]
  {G : Drawing S} {Δ : Set (Set S)}

private theorem alg34_vertex_not_edge (h : GM06DrawingRep x G Δ)
    (v : Fin x.n) (e : Fin x.ends.length) : (h.vertex v).val ∉ (h.edge e).val :=
  fun hp => ((h.edge e).property.2.1 hp).2 (h.vertex v).property

private theorem alg34_vertex_not_region (h : GM06DrawingRep x G Δ)
    (v : Fin x.n) (r : Fin x.regions.length) : (h.vertex v).val ∉ (h.region r).val :=
  fun hp => region_subset (h.region r).property hp (G.V_subset_U (h.vertex v).property)

private theorem alg34_edge_region_disjoint (h : GM06DrawingRep x G Δ)
    (e : Fin x.ends.length) (r : Fin x.regions.length) {p : S}
    (hp : p ∈ (h.edge e).val) : p ∉ (h.region r).val :=
  fun hpr => region_subset (h.region r).property hpr ((h.edge e).property.2.1 hp).1

/-- Two supplied cells containing the same point have the same label. -/
theorem cell_index_eq_of_mem (h : GM06DrawingRep x G Δ) {a b : GM06CellIndex x} {p : S}
    (ha : p ∈ h.cell a) (hb : p ∈ h.cell b) : a = b := by
  rcases a with v | e | r <;> rcases b with w | f | s
  · change p = (h.vertex v).val at ha
    change p = (h.vertex w).val at hb
    exact congrArg Sum.inl (h.vertex.injective (Subtype.ext (ha.symm.trans hb)))
  · change p = (h.vertex v).val at ha
    exact False.elim (alg34_vertex_not_edge h v f (ha ▸ hb))
  · change p = (h.vertex v).val at ha
    exact False.elim (alg34_vertex_not_region h v s (ha ▸ hb))
  · change p = (h.vertex w).val at hb
    exact False.elim (alg34_vertex_not_edge h w e (hb ▸ ha))
  · have heq := G.edge_eq_of_mem (h.edge e).property (h.edge f).property ha hb
    exact congrArg (Sum.inr ∘ Sum.inl) (h.edge.injective (Subtype.ext heq))
  · exact False.elim (alg34_edge_region_disjoint h e s ha hb)
  · change p = (h.vertex w).val at hb
    exact False.elim (alg34_vertex_not_region h w r (hb ▸ ha))
  · exact False.elim (alg34_edge_region_disjoint h f r hb ha)
  · have heq := region_eq_of_mem (h.region r).property (h.region s).property ha hb
    exact congrArg (Sum.inr ∘ Sum.inr) (h.region.injective (Subtype.ext heq))

/-- Every point of the ambient drawing space belongs to a supplied cell. -/
theorem exists_cell_of_point (h : GM06DrawingRep x G Δ) (p : S) :
    ∃ a : GM06CellIndex x, p ∈ h.cell a := by
  by_cases hpU : p ∈ G.U
  · by_cases hpV : p ∈ G.V
    · obtain ⟨v, hv⟩ := h.vertex.surjective ⟨p, hpV⟩
      exact ⟨.inl v, (congrArg Subtype.val hv).symm⟩
    · obtain ⟨e, he, hpe⟩ := G.exists_edge_of_mem hpU hpV
      obtain ⟨a, ha⟩ := h.edge.surjective ⟨e, he⟩
      refine ⟨.inr (.inl a), ?_⟩
      change p ∈ (h.edge a).val
      rw [congrArg Subtype.val ha]
      exact hpe
  · obtain ⟨r, hr, hpr⟩ := exists_region_of_notMem hpU
    obtain ⟨a, ha⟩ := h.region.surjective ⟨r, hr⟩
    refine ⟨.inr (.inr a), ?_⟩
    change p ∈ (h.region a).val
    rw [congrArg Subtype.val ha]
    exact hpr

/-- The finite supplied closure-incidence test agrees with actual
intersection of a cell with another cell's topological closure. -/
theorem cell_inter_closure_nonempty_iff [T1Space S] (h : GM06DrawingRep x G Δ)
    (a b : GM06CellIndex x) :
    (h.cell a ∩ closure (h.cell b)).Nonempty ↔ a ∈ x.cellClosure b := by
  rw [h.closure_cell b]
  constructor
  · rintro ⟨p, hpa, hpb⟩
    obtain ⟨c, hc, hpc⟩ := mem_iUnion₂.mp hpb
    exact h.cell_index_eq_of_mem hpa hpc ▸ hc
  · intro ha
    obtain ⟨p, hp⟩ := (h.cell_isConnected a).1
    exact ⟨p, hp, mem_iUnion₂.mpr ⟨a, ha, hp⟩⟩

end GraphMinor.Compute.GM06DrawingRep
