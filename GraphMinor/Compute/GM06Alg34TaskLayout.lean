module

public import GraphMinor.Compute.GM06Alg34QueueBounds

/-!
# Finite layout conditions for pending task records

A pending record retains a single supplied parent cuff, a matching gap
list and fixed bounds on its parent and record lengths. These are plain
properties of the finite packet that allow its existing decoder to run.
Every record created from a matching bounded parent has these properties.
-/

@[expose] public section
namespace GraphMinor.Compute

/-- Finite parent layout and size conditions used when decoding a task. -/
def gm06TaskLayout (Q : ℕ) (T : GM06GapComponentTask) : Prop :=
  ∃ L, T.drawing.cuffs = [L] ∧ T.gaps.length = L.length ∧
    T.drawing.size ≤ 40 * (Q + 2) ^ 2 ∧ T.size ≤ gm06TaskRecordBound Q

/-- A task created from a matching uniformly bounded parent has the required layout. -/
theorem gm06TaskLayout_mk (Q : ℕ) (x : GM06DrawingData)
    (L : List (Fin x.n)) (R : List (Fin x.regions.length)) (a : Fin x.n)
    (hL : x.cuffs = [L]) (hlen : R.length = L.length)
    (hs : x.size ≤ 40 * (Q + 2) ^ 2) (hR : R.length ≤ Q) :
    gm06TaskLayout Q ⟨x, R, a⟩ :=
  ⟨L, hL, hlen, hs, gm06Task_size_le_recordBound Q x R a hs hR⟩

/-- Every task emitted for a parent with gap list `R` records exactly that parent input. -/
theorem gm06ComponentTask_input {X : GM06GapInput} {R : List (Fin X.drawing.regions.length)}
    (hR : X.gapRegions = [R]) {T : GM06GapComponentTask}
    (hT : T ∈ gm06GapComponentTasks X.drawing R) : T.input = X := by
  obtain ⟨a, _, rfl⟩ := List.mem_map.mp hT
  exact (congrArg (GM06GapInput.mk X.drawing) hR).symm

end GraphMinor.Compute
