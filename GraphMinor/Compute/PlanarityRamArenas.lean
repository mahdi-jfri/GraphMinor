module

public import GraphMinor.Compute.PlanarityRamBucket

/-!
# Allocating the solver arenas after the bucket phase

The node, block, summary and vertex-result arrays receive their final
capacities once. They lie above all search and outgoing arrays, so the
solver's required input representations survive allocation unchanged.
-/

@[expose] public section
namespace GraphMinor.Compute.PlanarityRam

private theorem solver_field_array_ge (f : Field) (hf : f ∈ solverFields) : 50 ≤ f.array := by
  cases f <;> simp [solverFields, Field.array] at hf ⊢

/-- Allocating the solver arenas leaves all earlier arrays unchanged. -/
theorem allocatedSolver_arrs_eq (N M : ℕ) (s : State) (a : ℕ) (ha : a < 50) :
    (allocatedState N M solverFields s).arrs a = s.arrs a := by
  apply allocatedState_arrs_of_not_mem
  intro f hf
  exact Nat.ne_of_lt (Nat.lt_of_lt_of_le ha (solver_field_array_ge f hf))

/-- The solver receives every arena at its final specified capacity. -/
theorem allocatedSolver_arenasAt (N M : ℕ) (s : State) :
    SolverArenasAt N M (allocatedState N M solverFields s) := by
  intro f hf
  rw [allocatedState_arrs_of_mem N M solverFields s f hf, List.length_replicate]

/-- Solver-arena allocation preserves the represented search. -/
theorem SearchAt.allocate_solver {N M : ℕ} {s : State} {search : LRPlanarity.Search}
    (h : SearchAt N M s search) :
    SearchAt N M (allocatedState N M solverFields s) search := by
  apply h.of_memory_eq
  · exact congrFun (allocatedState_regs N M solverFields s) 37
  · exact congrFun (allocatedState_regs N M solverFields s) 39
  · intro a ha
    exact allocatedSolver_arrs_eq N M s a (Nat.lt_trans ha (by decide))

/-- Solver outgoing chains depend only on their first and next arrays. -/
theorem OutgoingAt.of_memory_eq {N : ℕ} {s s' : State} {outgoing : Array (List ℕ)}
    (h : OutgoingAt N s outgoing)
    (hf : s'.arrs Field.outgoingFirst.array = s.arrs Field.outgoingFirst.array)
    (hn : s'.arrs Field.outgoingNext.array = s.arrs Field.outgoingNext.array) :
    OutgoingAt N s' outgoing := by
  intro v hv
  obtain ⟨p, hp, hc⟩ := h v hv
  refine ⟨p, by simpa only [hf] using hp, ?_⟩
  exact edgeChain_outgoing_iff.mp ((edgeChain_outgoing_iff.mpr hc).of_arr_eq hn)

/-- Solver allocation preserves all outgoing chains. -/
theorem OutgoingAt.allocate_solver {N M : ℕ} {s : State} {outgoing : Array (List ℕ)}
    (h : OutgoingAt N s outgoing) :
    OutgoingAt N (allocatedState N M solverFields s) outgoing :=
  h.of_memory_eq (allocatedSolver_arrs_eq N M s _ (by decide))
    (allocatedSolver_arrs_eq N M s _ (by decide))

/-- The thirteen solver allocations cost at most a fixed linear multiple. -/
theorem allocateSolver_exec (N M w : ℕ) (s : State)
    (hN : s.regs 30 = N) (hM : s.regs 36 = M)
    (hw : 2 * (N + M + 1) < 2 ^ w) :
    Exec w (allocateFields solverFields) s (allocatedState N M solverFields s)
      (allocationTime N M solverFields) ∧
    allocationTime N M solverFields ≤ 118 * (N + M + 1) := by
  refine ⟨allocateFields_exec solverFields N M w s hN hM hw, ?_⟩
  have ht := allocationTime_le solverFields N M
  have hlen : solverFields.length = 13 := rfl
  rw [hlen] at ht
  omega

end GraphMinor.Compute.PlanarityRam
