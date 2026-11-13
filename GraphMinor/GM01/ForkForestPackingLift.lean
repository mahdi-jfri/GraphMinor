module

public import GraphMinor.GM01.RootedForestFamilies
public import GraphMinor.GM01.RootedForks
import GraphMinor.GM01.ForkForestPacking
import GraphMinor.GM01.RootedForestFamilyLift

/-!
# The packed family in a component with a large rooted fork

Graph Minors I, (5.2), page 61, passes from the rooted fork minor
in the component to actual disjoint sets inside that component.
The proved source packing gives the sets in the fork, and the
family transfer lifts them through its actual rooted model. The
fork's root edge supplies a target edge label for the ordinary
minor conversion, so no nonemptiness hypothesis is added.
-/

public section

namespace GraphMinor.GM01

open Set Graph SimpleGraph

/-- The represented edge from the fork root to its binary arm gives
an actual target edge label. -/
theorem RootedMinorModel.rootedFork_nonempty_edge_labels {α β : Type*} {γ δ : ℕ}
    (hγ : 0 < γ) (hδ : 2 ≤ δ) (G : RootedGraph α β)
    (M : RootedMinorModel (rootedForkGraph γ δ hγ hδ) G) : Nonempty β := by
  let edge : E((rootedForkGraph γ δ hγ hδ).graph) := ⟨s(none,some (Sum.inr [])),rfl⟩
  exact ⟨(M.edgeMap edge).val⟩

/-- The actual sets `X'_0,…,X'_(Ω+1)` asserted in GM01 (5.2),
page 61, with all disjointness and minor conditions constructed inside
the component containing the rooted fork minor. -/
theorem exists_forest_family_of_large_rooted_fork {α β : Type*} {γ : ℕ} (hγ : 0 < γ)
    (Ω : ℕ) (G : RootedGraph α β) (hV : V(G.graph).Finite) (hE : E(G.graph).Finite)
    (hFork : HasRootedMinor (rootedForkGraph γ (3 * Ω + 6) hγ (by omega)) G) :
    Nonempty (RootedForestFamily G γ (Ω + 1)) := by
  obtain ⟨M⟩ := hFork
  let : Nonempty β := M.rootedFork_nonempty_edge_labels hγ (by omega) G
  obtain ⟨F⟩ := exists_forest_family_in_large_fork hγ Ω
  exact exists_rooted_forest_family_of_rooted_model (rootedFork γ (3 * Ω + 6) (by omega))
    (rootedFork_vertices_finite γ (3 * Ω + 6) (by omega))
    (rootedForkGraph γ (3 * Ω + 6) hγ (by omega)).root G hV hE M F

end GraphMinor.GM01
