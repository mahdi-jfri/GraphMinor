module

public import GraphMinor.GM02.ClassRecognition

/-!
# Testing for a fixed planar minor

Graph Minors V, (1.8), is the algorithm of Graph Minors II, (1.1). The Word RAM
reads the multigraph encoding and returns zero exactly when the requested minor
exists. Loops and parallel edges are encoded.
-/

public section
namespace GraphMinor.Compute
open Graph Set Classical

/-- Graph Minors V, (1.8), page 94:
"If $H$ is any fixed planar graph, there is a polynomial time algorithm to test if an arbitrary graph has a minor isomorphic to $H$."

V cites this from II, and the proof is II (1.1) (`GM02.algorithm_1_1`). The
input is the multigraph encoding `x.G.enc`. Output zero means that `H` is a
minor, and output one means that it is not. The time is polynomial in
`(x.n + 1)²`. -/
theorem gm05_algorithm_1_8 (H : Graph ℕ (ℕ × ℕ × ℕ))
    (hV : V(H).Finite) (hE : E(H).Finite) (hPlanar : IsPlanar H) :
    ∃ (P : Cmd) (c : ℕ),
      ComputesRelInTime alg44Size (fun x s => s.arrs inArr = x.G.enc)
        (fun x s => s.regs outReg =
          if IsIsoMinor H x.G.toGMDigraph.toGraph then 0 else 1)
        P (fun n => (n + 1) ^ c) := by
  obtain ⟨P, c, hP⟩ := GM02.algorithm_1_1_proof H hV hE hPlanar
  refine ⟨P, c, ?_⟩
  simpa only [ite_not] using hP

end GraphMinor.Compute
