module

public import GraphMinor.Compute.GM13SocietyInput
public import GraphMinor.Compute.GM13ProgramsClosed

/-!
# Calling the cross algorithm with its exact output format

The closed two-paths program gives the simple (8.1) implementation. We retain
its exact path-list output, not only the correctness of its decoded cross.
The exact lengths let the multigraph caller read the two vertex lists before
writing their actual edge labels.
-/

@[expose] public section
namespace GraphMinor.Compute

/-- The simple (8.1) record contains the tag, both lengths, and both paths. -/
def gm13CrossCode {n : ℕ} {G : SimpleGraph (Fin n)} {omega : List (Fin n)}
    (c : CrossWitness G omega) : List ℕ :=
  [1, c.P.support.length, c.Q.support.length] ++
    c.P.support.map Fin.val ++ c.Q.support.map Fin.val

/-- Exact output of the simple cross call: a valid cross record, or tag zero
when no cross exists. -/
def GM13SimpleCrossOutput (x : Alg81Input) (out : List ℕ) : Prop :=
  (∃ c : CrossWitness x.G x.omega, c.IsValid ∧ out = gm13CrossCode c) ∨
    (out = [0] ∧ ¬ HasCrossInSociety x.G x.omega)

/-- The closed simple cross program provides its exact path-list record in
O(vε) time, with the proved external two-paths implementation. -/
theorem gm13SimpleCrossProgram :
    ∃ P : Cmd, ComputesArrRelInTime alg81Size encAlg81In
      GM13SimpleCrossOutput P (fun s => s) := by
  obtain ⟨P, C, c, hC, hc, hspec⟩ := gm13_twoPaths
  refine ⟨alg81Prog P, 1200 + 10 * C, 5 * c + 4, by omega, by omega, ?_⟩
  intro x s hin
  obtain ⟨s', t, hex, ht, _, hout⟩ := alg81Prog_exec hC hc hspec x le_rfl hin
  exact ⟨s', t, hex, ht, hout⟩

/-- The same exact simple record is available from a plain encoded
multigraph society, while the original input is retained in array zero. -/
theorem gm13SocietyCrossCall :
    ∃ P : Cmd, ComputesRelInTime GM13SocietyInput.size (fun x s => s.arrs 0 = x.enc)
      (fun x s => GM13SimpleCrossOutput x.simple (s.arrs 65) ∧ s.arrs 0 = x.enc)
      P (fun s => s) := by
  obtain ⟨P, hP⟩ := gm13SimpleCrossProgram
  exact ⟨gm13SocietyRunProg P, gm13SocietyRunProg_computes P GM13SimpleCrossOutput hP⟩

end GraphMinor.Compute
