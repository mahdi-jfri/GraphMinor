module

public import GraphMinor.LRPlanarity.TreeNeighborhoodPlacement
public import GraphMinor.HP25.Web
import GraphMinor.LRPlanarity.TreeNeighborhoodDirections

/-!
# Vertex polygons for a straight plane drawing

Part IV, Section 7b of the planarity note includes every incident edge
normal among the supporting directions of the vertex polygon. Choose
these normals from the drawing, then shrink all polygons simultaneously.
The forbidden set at a vertex is the finite union of its nonincident edge
images. It is compact and misses the vertex, so the polygons can avoid
all those images and each other.
-/

public section
namespace GraphMinor.LRPlanarity

open Set Surface

/-- Part IV, Section 7b: the straight drawing supplies distinct incident
normal angles and small, disjoint vertex polygons avoiding nonincident
edges. All angles and polygons are constructed from the drawing. -/
theorem exists_straight_drawing_vertex_polygons {V : Type*} [Finite V]
    {G : SimpleGraph V} (drawing : HP25.PlaneEmbedding G univ)
    (hstraight : ∀ u v, G.Adj u v →
      drawing.line u v = segment ℝ (drawing.pt u) (drawing.pt v)) :
    ∃ (angle : ∀ u, {v // G.Adj u v} → ℝ) (directions : V → Finset ℝ) (r : V → ℝ),
      (∀ u v, eC (angle u v) =
        ‖drawing.pt v.val - drawing.pt u‖⁻¹ • (drawing.pt v.val - drawing.pt u)) ∧
      (∀ u, Function.Injective (fun v => eC (angle u v))) ∧
      (∀ u v, angle u v ∈ directions u) ∧
      (∀ u, 0 < r u ∧
        IsClosedDisc (vertexPolygonAt (drawing.pt u) (directions u) (r u)) ∧
        drawing.pt u ∈ interior (vertexPolygonAt (drawing.pt u) (directions u) (r u))) ∧
      Pairwise (fun u v => Disjoint
        (vertexPolygonAt (drawing.pt u) (directions u) (r u))
        (vertexPolygonAt (drawing.pt v) (directions v) (r v))) ∧
      (∀ u v, u ≠ v → r u + r v < dist (drawing.pt u) (drawing.pt v)) ∧
      (∀ u v w, G.Adj v w → v ≠ u → w ≠ u → Disjoint
        (vertexPolygonAt (drawing.pt u) (directions u) (r u)) (drawing.line v w)) := by
  classical
  let : Fintype V := Fintype.ofFinite V
  have hnormals := fun u => exists_incident_normal_angles drawing hstraight u
  choose angle hangle hinj using hnormals
  let directions : V → Finset ℝ := fun u =>
    (Set.toFinite (range (angle u))).toFinset
  have hmem : ∀ u v, angle u v ∈ directions u := by
    intro u v
    simpa only [directions, Set.Finite.mem_toFinset] using (mem_range_self v : angle u v ∈ range (angle u))
  let E : V → Type _ := fun u => {e : V × V // G.Adj e.1 e.2 ∧ e.1 ≠ u ∧ e.2 ≠ u}
  let K : V → Set ℂ := fun u => ⋃ e : E u, drawing.line e.val.1 e.val.2
  have hK : ∀ u, IsCompact (K u) := by
    intro u
    apply isCompact_iUnion
    intro e
    rw [hstraight _ _ e.property.1]
    rw [segment_eq_image]
    exact isCompact_Icc.image (by fun_prop)
  have hmiss : ∀ u, drawing.pt u ∉ K u := by
    intro u hx
    obtain ⟨e, he⟩ := mem_iUnion.mp hx
    rcases drawing.avoid _ (mem_univ _) _ (mem_univ _) e.property.1
      u (mem_univ _) he with hu | hu
    · exact e.property.2.1 hu.symm
    · exact e.property.2.2 hu.symm
  have hpt : Function.Injective drawing.pt := fun u v h =>
    drawing.injOn (mem_univ u) (mem_univ v) h
  obtain ⟨r, hr, hsep, hdist⟩ := exists_small_vertex_polygons_distance_bounds drawing.pt hpt directions K hK hmiss
  refine ⟨angle, directions, r, hangle, hinj, hmem,
    fun u => ⟨(hr u).1, (hr u).2.1, (hr u).2.2.1⟩, hsep, hdist, ?_⟩
  intro u v w hvw hvu hwu
  apply (hr u).2.2.2.mono_right
  exact subset_iUnion_of_subset (⟨(v, w), hvw, hvu, hwu⟩ : E u) subset_rfl

end GraphMinor.LRPlanarity
