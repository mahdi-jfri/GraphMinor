module

public import GraphMinor.GM02.SideRunWalk

/-!
# Transferring a side run into its assigned graph

Every dart of a maximal side run has the color of its first dart. Thus
all its edges lie in the same side graph. Transfer the run walk to that
graph without changing its vertices, edges, or path property. This gives
the actual side pieces in the forward construction for corrected II (2.9).
-/

@[expose] public section
namespace GraphMinor.GM02
open Graph SimpleGraph Set Classical
universe u v

/-- Every edge of a true-colored run belongs to the first side. -/
theorem sideRunWalk_edges_left {α : Type u} {β : Type v} {G H : Graph α β}
    {a b : α} (p : (pathGraph G).Walk a b) (r : List (pathGraph G).Dart)
    (hr : r ∈ sideRuns H p) (hc : separationEdgeColor H (r.head (coloredRun_ne_nil hr)) = true) :
    ∀ e ∈ (sideRunWalk p r hr).edges, e ∈ (pathGraph H).edgeSet := by
  intro e he
  rw [Walk.edges, sideRunWalk_darts] at he
  obtain ⟨d, hd, rfl⟩ := List.mem_map.1 he
  have hdC := (coloredRun_color_eq_head hr hd).trans hc
  exact (SimpleGraph.mem_edgeSet _).2 (separationEdgeColor_left hdC)

/-- Every edge of a false-colored run belongs to the second side. -/
theorem sideRunWalk_edges_right {α : Type u} {β : Type v} {G H H' : Graph α β}
    (hsep : IsSeparation G H H') {a b : α} (p : (pathGraph G).Walk a b)
    (r : List (pathGraph G).Dart) (hr : r ∈ sideRuns H p)
    (hc : separationEdgeColor H (r.head (coloredRun_ne_nil hr)) = false) :
    ∀ e ∈ (sideRunWalk p r hr).edges, e ∈ (pathGraph H').edgeSet := by
  intro e he
  rw [Walk.edges, sideRunWalk_darts] at he
  obtain ⟨d, hd, rfl⟩ := List.mem_map.1 he
  have hdC := (coloredRun_color_eq_head hr hd).trans hc
  exact (SimpleGraph.mem_edgeSet _).2 (separationEdgeColor_right hsep hdC)

/-- Transfer a run assigned to the first side into that graph. -/
noncomputable def sideRunLeftWalk {α : Type u} {β : Type v} {G H : Graph α β}
    {a b : α} (p : (pathGraph G).Walk a b) (r : List (pathGraph G).Dart)
    (hr : r ∈ sideRuns H p) (hc : separationEdgeColor H (r.head (coloredRun_ne_nil hr)) = true) :=
  (sideRunWalk p r hr).transfer (pathGraph H) (sideRunWalk_edges_left p r hr hc)

/-- Transfer a run assigned to the second side into that graph. -/
noncomputable def sideRunRightWalk {α : Type u} {β : Type v} {G H H' : Graph α β}
    (hsep : IsSeparation G H H') {a b : α} (p : (pathGraph G).Walk a b)
    (r : List (pathGraph G).Dart) (hr : r ∈ sideRuns H p)
    (hc : separationEdgeColor H (r.head (coloredRun_ne_nil hr)) = false) :=
  (sideRunWalk p r hr).transfer (pathGraph H') (sideRunWalk_edges_right hsep p r hr hc)

/-- Transfer to the first side preserves the run's support. -/
theorem sideRunLeftWalk_support {α : Type u} {β : Type v} {G H : Graph α β}
    {a b : α} (p : (pathGraph G).Walk a b) (r : List (pathGraph G).Dart)
    (hr : r ∈ sideRuns H p) (hc : separationEdgeColor H (r.head (coloredRun_ne_nil hr)) = true) :
    (sideRunLeftWalk p r hr hc).support = (sideRunWalk p r hr).support :=
  Walk.support_transfer _ _

/-- Transfer to the second side preserves the run's support. -/
theorem sideRunRightWalk_support {α : Type u} {β : Type v} {G H H' : Graph α β}
    (hsep : IsSeparation G H H') {a b : α} (p : (pathGraph G).Walk a b)
    (r : List (pathGraph G).Dart) (hr : r ∈ sideRuns H p)
    (hc : separationEdgeColor H (r.head (coloredRun_ne_nil hr)) = false) :
    (sideRunRightWalk hsep p r hr hc).support = (sideRunWalk p r hr).support :=
  Walk.support_transfer _ _

/-- A transferred first-side run of a path remains a path. -/
theorem sideRunLeftWalk_isPath {α : Type u} {β : Type v} {G H : Graph α β}
    {a b : α} (p : (pathGraph G).Walk a b) (hp : p.IsPath)
    (r : List (pathGraph G).Dart) (hr : r ∈ sideRuns H p)
    (hc : separationEdgeColor H (r.head (coloredRun_ne_nil hr)) = true) :
    (sideRunLeftWalk p r hr hc).IsPath := (sideRunWalk_isPath p hp r hr).transfer _

/-- A transferred second-side run of a path remains a path. -/
theorem sideRunRightWalk_isPath {α : Type u} {β : Type v} {G H H' : Graph α β}
    (hsep : IsSeparation G H H') {a b : α} (p : (pathGraph G).Walk a b) (hp : p.IsPath)
    (r : List (pathGraph G).Dart) (hr : r ∈ sideRuns H p)
    (hc : separationEdgeColor H (r.head (coloredRun_ne_nil hr)) = false) :
    (sideRunRightWalk hsep p r hr hc).IsPath := (sideRunWalk_isPath p hp r hr).transfer _

end GraphMinor.GM02
