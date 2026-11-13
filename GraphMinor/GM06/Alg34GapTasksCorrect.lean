module

public import GraphMinor.GM06.Alg34GapComponentsCorrect
public import GraphMinor.Compute.GM06Alg34GapTaskQueueData

/-!
# Feasibility of canonical component work records

The queued parent/root records materialize exactly the augmented
component inputs. Consequently the conjunction of the queued answers
is the parent answer in the branching case of VI (3.3)(iv). Each record
also retains the proper drawing and boundary division conditions needed
for further reductions.
-/

public section
namespace GraphMinor.Compute.GM06GapInputRep

open Set Surface GM06
universe u
variable {S : Type u} [TopologicalSpace S] [T1Space S]
  {x : GM06DrawingData} {R : List (Fin x.regions.length)}
  {G : Drawing S} {Δ : Set (Set S)}

/-- Component work records have exactly the conjunction of feasible
answers specified by VI (3.3)(iv). -/
theorem componentTasks_feasible_iff (h : GM06GapInputRep ⟨x, [R]⟩ G Δ)
    (hs : x.hasSplitBlock = false) (hD : IsDivision Δ)
    (hbd : divisionUnion Δ = G.V ∩ bd S) (hk : 2 ≤ x.componentRoots.length) :
    IsFeasible x.graph x.divisionSet ↔
      ∀ T ∈ gm06GapComponentTasks x R,
        IsFeasible T.target.drawing.graph T.target.drawing.divisionSet := by
  have hb := h.componentGapInputs_feasible_iff hs hD hbd hk
  rw [← gm06GapComponentTasks_targets x R] at hb
  constructor
  · intro hf T hT
    exact hb.mp hf T.target (List.mem_map.mpr ⟨T, hT, rfl⟩)
  · intro hf
    apply hb.mpr
    intro Y hY
    obtain ⟨T, hT, rfl⟩ := List.mem_map.mp hY
    exact hf T hT

/-- Every queued task materializes a connected proper drawing and a
valid division covering precisely its boundary vertices. -/
theorem componentTask_valid (h : GM06GapInputRep ⟨x, [R]⟩ G Δ)
    (hS : IsClosedDiscSpace S) (hproper : G.IsProper) (hD : IsDivision Δ)
    (hbd : divisionUnion Δ = G.V ∩ bd S)
    {T : GM06GapComponentTask} (hT : T ∈ gm06GapComponentTasks x R) :
    ∃ G' : Drawing S, ∃ Δ' : Set (Set S),
      Nonempty (GM06GapInputRep T.target G' Δ') ∧ G'.IsProper ∧
        IsDivision Δ' ∧ divisionUnion Δ' = G'.V ∩ bd S ∧
        IsGraphConnected G'.toGraph := by
  obtain ⟨a, _, rfl⟩ := List.mem_map.mp hT
  exact ⟨_, _, h.componentGapData_valid hS hproper hD hbd a⟩

end GraphMinor.Compute.GM06GapInputRep
