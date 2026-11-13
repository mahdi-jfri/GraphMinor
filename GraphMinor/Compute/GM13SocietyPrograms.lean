module

public import GraphMinor.Compute.GM13SocietyCrossRestore

/-!
# Section 8 programs for societies with loops and parallel edges

The plain multigraph input is simplified before the existing simple program
runs. Its cross output is restored by writing the actual edge endpoints.
The time is bounded using the vertex and edge counts of the given graph.
-/

public section
namespace GraphMinor.Compute

/-- Graph Minors XIII, Algorithm (8.1), page 93, for every encoded society:
"A cross in $(G, \Omega)$ if one exists."

The input is the multigraph encoding and the supplied cyclic order. The
program deletes loops and parallel copies, calls the proved simple program,
and writes actual edge labels for both paths. Its bound is O(vε) in the
given multigraph. `algorithm_8_1_proved` is the simple-input version.
XIII, page 68: "Thus each edge has a head and a tail (the same, for a loop)." -/
theorem algorithm_8_1_full :
    ∃ P : Cmd, ComputesRelInTime GM13SocietyInput.size (fun x s => s.arrs 0 = x.enc)
      (fun x s => GM13ActualCrossOutput x s ∧ s.arrs 0 = x.enc) P (fun s => s) := by
  obtain ⟨P, hP⟩ := gm13SocietyCrossCall
  have hseq := hP.seq_same gm13CrossRestoreProg_computes
    (T := fun s => 2 * s) (fun x => by omega)
  exact ⟨.seq P gm13CrossRestoreProg,
    hseq.mono_time (K := 2) (by decide) (fun _ => le_rfl)⟩

/-- Graph Minors XIII, Algorithm (8.3), page 95, for every encoded society:
"A 4-linked core of $(G, \Omega)$."

The program simplifies the plain multigraph input and runs `gm13_algorithm_8_3`.
The decoded core has exactly the same vertex labels and edges. Path
preservation proves that it is a 4-linked core of the given society, with
O(vε) time measured in the original multigraph. `gm13_algorithm_8_3` is the
simple-input version. -/
theorem algorithm_8_3_full :
    ∃ P : Cmd, ComputesRelInTime GM13SocietyInput.size (fun x s => s.arrs 0 = x.enc)
      (fun x s => GM13.IsFourLinkedCore x.society
        (decAlg83Out x.simple (s.arrs 65)).toCoreGraph) P (fun s => s) := by
  have hcall := gm13SocietyRunProg_computes alg83Prog
    (fun x out => IsValidAlg83Output x (decAlg83Out x out)) gm13_algorithm_8_3
  obtain ⟨C, c, hC, hc, hrun⟩ := hcall
  refine ⟨gm13SocietyRunProg alg83Prog, C, c, hC, hc, ?_⟩
  intro x s hin
  obtain ⟨s', t, hex, ht, hout, _⟩ := hrun x s hin
  exact ⟨s', t, hex, ht, (x.isFourLinkedCore_iff _).mp hout.2.1⟩

end GraphMinor.Compute
