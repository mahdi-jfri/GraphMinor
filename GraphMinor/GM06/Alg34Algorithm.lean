module

public import GraphMinor.GM06.Alg34ProgramExec
public import GraphMinor.Compute.GM06Alg34Polynomial

/-!
# Graph Minors VI, algorithm (3.4)

The supplied finite drawing and cuff-gap arrays determine feasibility.
The concrete Word RAM program checks crossings, performs the reductions
of (3.3), and passes to the dual when those reductions are exhausted.
The execution proof applies to every represented disc instance and all
initial scratch contents. Its degree-46 time bound uses the original
array size throughout the run.
-/

public section
namespace GraphMinor.GM06
open Compute
universe u

/-- Graph Minors VI, (3.4), page 121:

"(3.4) *Algorithm to decide if $\Delta$ is feasible in $G$.*"

The program reads only the supplied drawing and gap arrays. Its output
is Boolean and decides feasibility for every disc instance represented
by those arrays, in polynomial time with logarithmic machine words. -/
theorem algorithm_3_4_proof {X : GM06GapInput} {I : DiscDivInstance.{u}}
    (h : GM06GapInputRep X I.G I.Δ) {s : State}
    (hin : s.arrs 0 = X.drawing.words) (hgap : s.arrs 47 = X.discGapWords) :
    let size := X.drawing.size + X.discGapWords.length
    ∃ b s' t, Exec (wordSize 256 size) gm06Alg34Prog s s' t ∧
      t ≤ gm06Alg34TimeConstant * (size + 1) ^ 46 ∧
      s'.regs 0 = (if b then 1 else 0) ∧ (I.IsFeasibleInst ↔ b = true) := by
  obtain ⟨b, s', t, he, ht, hb, hf⟩ := gm06Alg34Prog_exec h hin hgap
  exact ⟨b, s', t, he, ht.trans (gm06Alg34_time_polynomial _), hb, hf⟩

end GraphMinor.GM06
