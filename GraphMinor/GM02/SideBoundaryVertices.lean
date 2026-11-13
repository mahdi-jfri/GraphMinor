module

public import GraphMinor.GM02.SideRunRecords
public import GraphMinor.GM02.ChunkBoundaryEdges

/-!
# The contracted vertex order of an original path

For corrected II (2.9), retain the original starting vertex and the last
vertex of each maximal side run. The resulting list preserves both
original endpoints and is a sublist of the original support. It is thus
a simple ordered path skeleton for the crossing scheme's pair graph.
-/

@[expose] public section
namespace GraphMinor.GM02
open Graph SimpleGraph List Set Classical
universe u v

/-- Successive endpoints of the maximal side pieces of an original walk. -/
noncomputable def sideBoundaryVertices {α : Type u} {β : Type v} {G : Graph α β}
    (H : Graph α β) {a b : α} (p : (pathGraph G).Walk a b) : List α :=
  chunkBoundaryVertices a (sideRunRecords H p)

/-- The contracted list always contains its original starting vertex. -/
theorem sideBoundaryVertices_nonempty {α : Type u} {β : Type v} {G H : Graph α β}
    {a b : α} (p : (pathGraph G).Walk a b) : sideBoundaryVertices H p ≠ [] := List.cons_ne_nil _ _

/-- The contracted list starts at the original path's start. -/
theorem sideBoundaryVertices_head {α : Type u} {β : Type v} {G H : Graph α β}
    {a b : α} (p : (pathGraph G).Walk a b) :
    (sideBoundaryVertices H p).head (sideBoundaryVertices_nonempty p) = a := rfl

/-- The contracted list stays in the original order of vertices. -/
theorem sideBoundaryVertices_sublist {α : Type u} {β : Type v} {G H : Graph α β}
    {a b : α} (p : (pathGraph G).Walk a b) : sideBoundaryVertices H p <+ p.support := by
  have hs := chunkBoundaryVertices_sublist a (sideRunRecords H p) (sideRunRecords_nonempty p)
  rw [sideRunRecords_flatten] at hs
  exact hs

/-- A contracted simple path still has no repeated vertices. -/
theorem sideBoundaryVertices_nodup {α : Type u} {β : Type v} {G H : Graph α β}
    {a b : α} (p : (pathGraph G).Walk a b) (hp : p.IsPath) :
    (sideBoundaryVertices H p).Nodup := (sideBoundaryVertices_sublist p).nodup hp.support_nodup

/-- The contracted list ends at the original path's final vertex. -/
theorem sideBoundaryVertices_getLast {α : Type u} {β : Type v} {G H : Graph α β}
    {a b : α} (p : (pathGraph G).Walk a b) :
    (sideBoundaryVertices H p).getLast (sideBoundaryVertices_nonempty p) = b := by
  have he := chunkBoundaryVertices_getLastD a (sideRunRecords H p) (sideRunRecords_nonempty p)
  rw [sideRunRecords_flatten] at he
  have hleft : (sideBoundaryVertices H p).getLastD a =
      (sideBoundaryVertices H p).getLast (sideBoundaryVertices_nonempty p) := by
    simp only [List.getLastD_eq_getLast?, List.getLast?_eq_some_getLast
      (sideBoundaryVertices_nonempty p), Option.getD_some]
  have hright : p.support.getLastD a = b := by
    simp only [List.getLastD_eq_getLast?, List.getLast?_eq_some_getLast p.support_ne_nil,
      Option.getD_some, Walk.getLast_support]
  exact hleft.symm.trans (he.trans hright)

end GraphMinor.GM02
