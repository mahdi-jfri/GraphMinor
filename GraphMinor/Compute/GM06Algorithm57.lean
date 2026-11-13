module

public import GraphMinor.Compute.GM06SuccessorLoopControl
public import GraphMinor.Compute.GM06Reduction4PhaseProgram
public import GraphMinor.Compute.GM06TerminalPhaseProgram

/-!
# The concrete RAM program for VI (5.7)

The algorithm on page 133 repeatedly applies the reductions, in
order 2, 1, 3, 4, and then uses the terminal valency criterion. This
command calls the two complete finite phases for Reduction 4 and
terminal witness construction. A positive terminal answer then runs
UNDO, returning ordinary path rows in the original input labels.

The outer count is fixed from the original vertex and edge counts.
A continuation flag leaves the remaining rounds idle after an answer.
The program keeps the ordinary six-field input in array 0. Its answer
is in register 0 and its positive witness encoding is in array 8.
-/

public section
namespace GraphMinor.Compute
open TwoPaths

/-- The concrete VI (5.7) program, using the two whole phase commands.
Input is the six-field successor code in array 0. Output is the
answer register 0 and, on success, original-label path rows in array 8. -/
@[expose] def gm06Algorithm57Prog : Cmd :=
  gm06Algorithm57ProgramOfPhases gm06Reduction4PhaseProg gm06TerminalPhaseProg

/-- The complete command first loads the input and initializes its
loop controls, then calls the actual loop body through the fixed
counting range. This equation exposes the program's control boundary. -/
theorem gm06Algorithm57Prog_eq :
    gm06Algorithm57Prog =
      .seq gm06InitializeSuccessorProg
        (.seq gm06InitSuccessorLoopControlProg
          (forUp 900 (.reg 905)
            (.ite (.reg 904)
              (gm06SuccessorLoopBody gm06Reduction4PhaseProg gm06TerminalPhaseProg) .skip))) := by
  rfl

set_option maxRecDepth 16384 in
set_option maxHeartbeats 2000000 in
private theorem algorithm_input_not_written : (0 : Arr) ∉ gm06Algorithm57Prog.writtenArrs := by
  decide

/-- Every actual execution preserves the original six-field input
code, independently of which reductions and terminal branch it takes. -/
theorem gm06Algorithm57Prog_input_preserved {w t : ℕ} {s sf : State}
    (he : Exec w gm06Algorithm57Prog s sf t) : sf.arrs 0 = s.arrs 0 :=
  he.arrs_eq_of_not_mem_writtenArrs algorithm_input_not_written

set_option maxRecDepth 16384 in
set_option maxHeartbeats 2000000 in
private theorem loop_core_not_written :
    (0 : Arr) ∉ (gm06SuccessorLoopProg gm06Reduction4PhaseProg gm06TerminalPhaseProg).writtenArrs ∧
      (2 : Arr) ∉ (gm06SuccessorLoopProg gm06Reduction4PhaseProg gm06TerminalPhaseProg).writtenArrs ∧
      (6 : Arr) ∉ (gm06SuccessorLoopProg gm06Reduction4PhaseProg gm06TerminalPhaseProg).writtenArrs ∧
      (7 : Arr) ∉ (gm06SuccessorLoopProg gm06Reduction4PhaseProg gm06TerminalPhaseProg).writtenArrs := by
  decide

/-- After loading, the original code, vertex count and two cuff lists
remain fixed throughout every execution of the concrete counting loop. -/
theorem gm06Algorithm57Loop_readonly {w t : ℕ} {s sf : State}
    (he : Exec w (gm06SuccessorLoopProg gm06Reduction4PhaseProg gm06TerminalPhaseProg) s sf t) :
    ∀ a ∈ [0, 2, 6, 7], sf.arrs a = s.arrs a := by
  intro a ha
  simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
  rcases ha with rfl | rfl | rfl | rfl
  · exact he.arrs_eq_of_not_mem_writtenArrs loop_core_not_written.1
  · exact he.arrs_eq_of_not_mem_writtenArrs loop_core_not_written.2.1
  · exact he.arrs_eq_of_not_mem_writtenArrs loop_core_not_written.2.2.1
  · exact he.arrs_eq_of_not_mem_writtenArrs loop_core_not_written.2.2.2

end GraphMinor.Compute
