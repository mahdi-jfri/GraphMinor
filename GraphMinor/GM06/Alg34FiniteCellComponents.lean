module

public import GraphMinor.GM06.Alg34CellPartition
public import GraphMinor.GM06.Alg34CellComponents

/-!
# Correctness of finite cell-component calculations

The supplied Boolean cell-incidence table agrees with topological
closure contact. Combine that fact with the finite-cell component
criterion. For any selected cells, graph reachability computed from
the input is exactly connected-component membership in their union.
This is used for the complement after singleton deletion.
-/

public section
namespace GraphMinor.Compute.GM06DrawingRep

open Set Surface GM06 Relation

universe u

/-- The Boolean incidence test obtained from the supplied closure lists
agrees exactly with closure contact of the represented cells. -/
theorem cellTouch_iff {x : GM06DrawingData} {S : Type u} [TopologicalSpace S] [T1Space S]
    {G : Drawing S} {Δ : Set (Set S)} (h : GM06DrawingRep x G Δ) (a b : GM06CellIndex x) :
    x.cellTouch a b = true ↔ alg34CellTouch h.cell a b := by
  simp only [GM06DrawingData.cellTouch, decide_eq_true_eq, alg34CellTouch,
    h.cell_inter_closure_nonempty_iff]

/-- For any selection of supplied cells, finite incidence reachability
is precisely connected-component membership in their actual union. -/
theorem finite_cell_component_iff {x : GM06DrawingData} {S : Type u}
    [TopologicalSpace S] [T1Space S] {G : Drawing S} {Δ : Set (Set S)}
    (h : GM06DrawingRep x G Δ) (K : Set (GM06CellIndex x))
    {a b : GM06CellIndex x} (ha : a ∈ K) (hb : b ∈ K) {p q : S}
    (hp : p ∈ h.cell a) (hq : q ∈ h.cell b) :
    q ∈ connectedComponentIn (⋃ c ∈ K, h.cell c) p ↔
      ReflTransGen (fun c d => c ∈ K ∧ d ∈ K ∧ x.cellTouch c d = true) a b := by
  have hR : (fun c d => c ∈ K ∧ d ∈ K ∧ alg34CellTouch h.cell c d) =
      (fun c d => c ∈ K ∧ d ∈ K ∧ x.cellTouch c d = true) := by
    funext c d
    exact propext (and_congr_right fun _ => and_congr_right fun _ => (h.cellTouch_iff c d).symm)
  have hcomp := alg34_cell_component_iff h.cell K K.toFinite
    (fun c _ => h.cell_isConnected c) ha hb hp hq
  rw [hR] at hcomp
  exact hcomp

end GraphMinor.Compute.GM06DrawingRep
