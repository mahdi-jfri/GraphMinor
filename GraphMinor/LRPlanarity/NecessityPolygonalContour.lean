module

public import GraphMinor.LRPlanarity.Statements
import GraphMinor.LRPlanarity.TreeNeighborhoodPolygonalComponent
import GraphMinor.LRPlanarity.TreeNeighborhoodContourRecursion
import GraphMinor.LRPlanarity.TreeNeighborhoodBoundaryContour
import GraphMinor.LRPlanarity.TreeNeighborhoodContourEvents
import GraphMinor.LRPlanarity.TreeNeighborhoodContourMultiplicity
import GraphMinor.LRPlanarity.TreeNeighborhoodContourAppend
import GraphMinor.LRPlanarity.TreeNeighborhoodContourForest
import GraphMinor.LRPlanarity.TreeNeighborhoodForest

/-!
# Nonalternating contours from a polygonal plane drawing

Part IV, Sections 7b and 7c of the planarity note constructs the contour
on each rooted component by polygon-and-strip leaf attachments, and
excludes alternating pairs by the exterior K5 obstruction. Choose the
resulting local order independently on each component. The recursive
contour of a root uses only that component's orders. Finally concatenate
the root words, as required by the specified contour definition.
-/

public section
namespace GraphMinor.LRPlanarity

private theorem vertexContour_eq_of_descendant_orders {N : ℕ} {T : Forest N}
    {G : SimpleGraph (Fin N)} {first second : ContourOrder N}
    (hvalid : ValidContourOrder T G first) (root : Fin N)
    (hagree : ∀ v, T.Ancestor root v → first v = second v) (fuel : ℕ) :
    vertexContour first fuel root = vertexContour second fuel root := by
  have aux : ∀ fuel v, T.Ancestor root v → vertexContour first fuel v = vertexContour second fuel v := by
    intro fuel
    induction fuel with
    | zero => intro v _; rfl
    | succ fuel ih =>
      intro v hv
      rw [vertexContour,vertexContour,← hagree v hv]
      apply List.flatMap_congr
      intro event he
      cases event with
      | child w => exact ih w (hv.tail ((hvalid v).2 (.child w) |>.mp he))
      | port p => rfl
  exact aux fuel root Relation.ReflTransGen.refl

/-- Part IV, Sections 7b and 7c of the planarity note: every polygonal
plane drawing yields valid nonalternating contour orders for any DFS
forest. The proof reads each component neighborhood by leaf substitution
and then concatenates the independent component contours. -/
theorem polygonalContourStatement : PolygonalContourStatement := by
  intro N G T drawing hT hpolygonal
  classical
  obtain ⟨initial,hinitial⟩ := exists_validContourOrder T G
  let Root := {r : Fin N // T.parent r = none}
  have hcomponent : ∀ r : Root, ∃ order, ValidContourOrder T G order ∧
      (∀ v, ¬ T.Ancestor r.val v → order v = initial v) ∧
      Nonalternating (vertexContour order (N+1) r.val) := by
    intro r
    exact exists_polygonal_component_contour drawing hT hpolygonal r.val r.property initial hinitial
  choose component hcomponentValid hcomponentOutside hcomponentNonalt using hcomponent
  have hrootExists := fun v : Fin N => exists_root_ancestor hT v
  choose rootOf hrootOf hancestorOf using hrootExists
  let order : ContourOrder N := fun v => component ⟨rootOf v,hrootOf v⟩ v
  have hvalid : ValidContourOrder T G order := fun v => hcomponentValid ⟨rootOf v,hrootOf v⟩ v
  have hrootword : ∀ r : Root,
      vertexContour order (N+1) r.val = vertexContour (component r) (N+1) r.val := by
    intro r
    apply vertexContour_eq_of_descendant_orders hvalid r.val
    intro v hv
    have he : rootOf v = r.val := equal_depth_ancestors_eq hT (hancestorOf v) hv
      ((hT.1 _ (hrootOf v)).trans (hT.1 _ r.property).symm)
    have hsub : (⟨rootOf v,hrootOf v⟩ : Root) = r := Subtype.ext he
    change component ⟨rootOf v,hrootOf v⟩ v = component r v
    rw [hsub]
  refine ⟨order,hvalid,isPortWord_of_validContourOrder hT hvalid,?_⟩
  let roots := (Finset.univ.filter (fun v => T.parent v = none)).sort (· ≤ ·)
  have hrootmem : ∀ v, v ∈ roots → T.parent v = none := by
    intro v hv
    simpa only [roots,Finset.mem_sort,Finset.mem_filter,Finset.mem_univ,true_and] using hv
  have hwordmem : ∀ r, T.parent r = none → ∀ p : Port N,
      p ∈ vertexContour order (N+1) r ↔ T.BackEdge G p.edge ∧ T.Ancestor r p.edge.1 := by
    intro r hr p
    have hbudget : N ≤ T.depth r + (N+1) := Nat.le_succ_of_le (Nat.le_add_left N (T.depth r))
    rw [mem_vertexContour_iff hT hvalid (N+1) r hbudget p]
    constructor
    · rintro ⟨hb,ha⟩
      exact ⟨hb,(port_ancestor_iff_source hr p hb).mp ha⟩
    · rintro ⟨hb,ha⟩
      exact ⟨hb,(port_ancestor_iff_source hr p hb).mpr ha⟩
  change Nonalternating (roots.flatMap (vertexContour order (N+1)))
  apply nonalternating_flatMap
  · intro r hr b
    rw [hwordmem r (hrootmem r hr),hwordmem r (hrootmem r hr)]
  · intro r hr
    rw [hrootword ⟨r,hrootmem r hr⟩]
    exact hcomponentNonalt ⟨r,hrootmem r hr⟩

end GraphMinor.LRPlanarity
