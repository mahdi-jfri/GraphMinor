module

public import GraphMinor.Compute.GM06Alg34SingletonEdgeLoss
public import GraphMinor.Compute.GM06Alg34GapSingletonData
public import GraphMinor.Compute.GM06Alg34GapInteriorData
public import GraphMinor.Compute.GM06Alg34DualData
import GraphMinor.Compute.GM06Alg34DeletionSpace

/-!
# Work decrease for finite deletion and dual steps

Ordinary deletions lose a vertex and cannot gain edges. Singleton
exhaustion repeats these decreases. A dual step preserves the edge
count and exchanges the vertex and region counts. Its following
singleton deletion loses an edge in the connected dual, so the fixed
edge multiplier pays for the exchanged vertex count.
-/

public section
namespace GraphMinor.Compute

open GM06DrawingData

/-- Complete singleton exhaustion cannot increase its additive queue charge. -/
theorem gm06GapReduceSingletons_workWeight_le (C : ℕ) (X : GM06GapInput) :
    (gm06GapReduceSingletons X).drawing.workWeight C ≤ X.drawing.workWeight C := by
  induction X using gm06GapReduceSingletons.induct with
  | case1 X hnone => rw [gm06GapReduceSingletons, hnone]
  | case2 X v hfind ih =>
    rw [gm06GapReduceSingletons, hfind]
    exact ih.trans (X.drawing.singletonData_workWeight_lt C v).le

/-- Removing a boundary-disjoint component strictly lowers the queue charge. -/
theorem gm06InteriorComponentData_workWeight_lt (C : ℕ) (x : GM06DrawingData)
    (a : Fin x.n) :
    (x.interiorComponentData a).workWeight C < x.workWeight C := by
  have he : (x.interiorComponentData a).ends.length ≤ x.ends.length := by
    change (x.inducedData (x.interiorComponentSurvivors a)).ends.length ≤ _
    rw [x.inducedData_ends_length]
    simpa only [activeEdges, List.length_finRange] using
      (List.length_filter_le (fun e => x.activeCell (x.interiorComponentSurvivors a) (.inr (.inl e)))
        (List.finRange x.ends.length))
  exact x.workWeight_lt_of_mass C _ (by have ha := a.isLt; omega)
    (x.workMass_lt_of_vertices C _ (gm06InteriorComponentData_n_lt x a) he)

/-- A dual transition followed by singleton deletion strictly lowers the
queue charge when the old region count is within the fixed vertex bound. -/
theorem gm06DualSingleton_workWeight_lt (M : ℕ) (x : GM06DrawingData)
    (L : List (Fin x.n)) (hR : 0 < x.regions.length)
    (g : Fin L.length → Fin x.regions.length)
    (hn : 0 < x.n) (hr : x.regions.length ≤ M) (hE : 0 < x.ends.length)
    (hc : (x.dualData L hR g).vertexGraph.Preconnected)
    (v : Fin (x.dualData L hR g).n) :
    ((x.dualData L hR g).singletonData v).workWeight (M + 1) < x.workWeight (M + 1) := by
  let y := x.dualData L hR g
  have heq : y.ends.length = x.ends.length := x.dualData_edges_length L hR g
  have he := y.singletonData_edges_lt_of_preconnected hc (by omega) v
  have hv := gm06SingletonData_n_lt y v
  have hy : y.n = x.regions.length := rfl
  apply x.workWeight_lt_of_mass (M + 1) _ hn
  exact x.workMass_lt_of_edges M (y.singletonData v) (by omega) (by omega)

end GraphMinor.Compute
