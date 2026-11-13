module

public import GraphMinor.GM02.Feasibility
public import GraphMinor.GM02.Separation

/-!
# Assigning path edges to sides of a separation

For the forward implication of corrected II (2.9), use the first side
whenever it contains an adjacency, and otherwise use the second. Graph
edges are partitioned by the separation, so every original path edge has
a side. This also works when parallel graph edges give adjacencies on both
sides: choosing the first is enough for paths.
-/

@[expose] public section
namespace GraphMinor.GM02
open Graph SimpleGraph Set Classical
universe u v

/-- True assigns a path dart to the first side, false to the second. -/
noncomputable def separationEdgeColor {α : Type u} {β : Type v}
    {G : Graph α β} (H : Graph α β) (d : (pathGraph G).Dart) : Bool :=
  decide (H.Adj d.fst d.snd)

/-- A true-colored dart is an adjacency in the first side. -/
theorem separationEdgeColor_left {α : Type u} {β : Type v}
    {G H : Graph α β} {d : (pathGraph G).Dart} (hc : separationEdgeColor H d = true) :
    (pathGraph H).Adj d.fst d.snd :=
  ⟨of_decide_eq_true hc, d.adj.ne⟩

/-- If the first side does not contain an adjacency, edge coverage puts
an edge realizing it in the second side. -/
theorem separationEdgeColor_right {α : Type u} {β : Type v}
    {G H H' : Graph α β} (hsep : IsSeparation G H H') {d : (pathGraph G).Dart}
    (hc : separationEdgeColor H d = false) : (pathGraph H').Adj d.fst d.snd := by
  have hnot : ¬H.Adj d.fst d.snd := by
    intro h
    have htrue : separationEdgeColor H d = true := decide_eq_true h
    rw [hc] at htrue
    contradiction
  obtain ⟨e, he⟩ := d.adj.1
  have heU : e ∈ E(H) ∪ E(H') := by
    rw [hsep.2.2.2.1]
    exact he.edge_mem
  rcases heU with heH | heH'
  · exact (hnot ((hsep.1.isLink_iff heH).2 he).adj).elim
  · exact ⟨((hsep.2.1.isLink_iff heH').2 he).adj, d.adj.ne⟩

end GraphMinor.GM02
