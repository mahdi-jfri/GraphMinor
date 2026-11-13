module

public import GraphMinor.GM11.Defs

/-!
# Data for edge-labelled routes

In the route comparison on II, page 319, keep the host walk along with
its ends and its interior list. This record contains only that data.
The lemmas constructing routes prove that the list is its walk's actual
interior and prove all disjointness and absence of repetitions separately.
-/

@[expose] public section
namespace GraphMinor.GM02
open Graph Surface
universe u v

/-- The ends, interior list, and host walk of an edge-labelled route. -/
structure EdgeRoute {α : Type u} {β : Type v} (G : Graph α β) where
  /-- First vertex of the walk. -/
  start : α
  /-- Last vertex of the walk. -/
  finish : α
  /-- Interior vertices, in traversal order. -/
  inner : List α
  /-- The edge-labelled host walk. -/
  walk : GraphWalk G start finish

end GraphMinor.GM02
