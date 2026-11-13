module

public import GraphMinor.GM02.ColoredRuns
public import GraphMinor.GM02.SeparationEdgeColor
public import Mathlib.Combinatorics.SimpleGraph.Walk.Subwalks

/-!
# Walks belonging to maximal side runs

For the forward construction in corrected II (2.9), split the darts of
an original path into constant-side runs. Each run inherits the dart-chain
condition because it is contiguous. It therefore defines a nontrivial
subwalk of the original walk, and is a path whenever the original is.
-/

@[expose] public section
namespace GraphMinor.GM02
open Graph SimpleGraph Set Classical
universe u v

/-- The maximal side runs along an original walk. -/
noncomputable def sideRuns {α : Type u} {β : Type v} {G : Graph α β}
    (H : Graph α β) {a b : α} (p : (pathGraph G).Walk a b) :=
  coloredRuns (separationEdgeColor H) p.darts

/-- A run's darts form a walk between its first and last endpoints. -/
noncomputable def sideRunWalk {α : Type u} {β : Type v} {G : Graph α β}
    {H : Graph α β} {a b : α} (p : (pathGraph G).Walk a b)
    (r : List (pathGraph G).Dart) (hr : r ∈ sideRuns H p) :
    (pathGraph G).Walk (r.head (coloredRun_ne_nil hr)).fst
      (r.getLast (coloredRun_ne_nil hr)).snd :=
  Walk.ofDarts r (coloredRun_ne_nil hr)
    (p.isChain_dartAdj_darts.infix (coloredRun_infix hr))

/-- A side run has exactly its listed darts. -/
theorem sideRunWalk_darts {α : Type u} {β : Type v} {G H : Graph α β}
    {a b : α} (p : (pathGraph G).Walk a b) (r : List (pathGraph G).Dart)
    (hr : r ∈ sideRuns H p) : (sideRunWalk p r hr).darts = r := Walk.darts_ofDarts _ _

/-- Side runs contain at least one edge. -/
theorem sideRunWalk_not_nil {α : Type u} {β : Type v} {G H : Graph α β}
    {a b : α} (p : (pathGraph G).Walk a b) (r : List (pathGraph G).Dart)
    (hr : r ∈ sideRuns H p) : ¬(sideRunWalk p r hr).Nil := by
  intro hnil
  have hd := Walk.darts_eq_nil.2 hnil
  rw [sideRunWalk_darts] at hd
  exact coloredRun_ne_nil hr hd

/-- A run is a contiguous subwalk of the original walk. -/
theorem sideRunWalk_isSubwalk {α : Type u} {β : Type v} {G H : Graph α β}
    {a b : α} (p : (pathGraph G).Walk a b) (r : List (pathGraph G).Dart)
    (hr : r ∈ sideRuns H p) : (sideRunWalk p r hr).IsSubwalk p := by
  apply (Walk.isSubwalk_iff_darts_isInfix (sideRunWalk_not_nil p r hr)).2
  rw [sideRunWalk_darts]
  exact coloredRun_infix hr

/-- A side run of a path is itself a path. -/
theorem sideRunWalk_isPath {α : Type u} {β : Type v} {G H : Graph α β}
    {a b : α} (p : (pathGraph G).Walk a b) (hp : p.IsPath)
    (r : List (pathGraph G).Dart) (hr : r ∈ sideRuns H p) :
    (sideRunWalk p r hr).IsPath := by
  apply Walk.IsPath.mk'
  exact (Walk.isSubwalk_iff_support_isInfix.1 (sideRunWalk_isSubwalk p r hr)).nodup hp.support_nodup

end GraphMinor.GM02
