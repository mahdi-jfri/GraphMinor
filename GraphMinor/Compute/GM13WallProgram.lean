module

public import GraphMinor.Compute.GM13WallExecution
import GraphMinor.Compute.Join13Adapter72
import GraphMinor.Compute.Algorithm41Aux20

/-!
# The algorithm of Graph Minors XIII, (7.1)

We first run the planar minor test (4.4). A model gives a wall by the existing
linear construction. If the test fails, the threshold hypothesis bounds the
width, so the failure certificate of (3.3) cannot occur. This yields a
decomposition of the whole input with the stated width and running time.
-/

public section
namespace GraphMinor.Compute
open GraphMinor GM13

/-- Graph Minors XIII, (7.1), page 89:
"For $h \ge 2$, even, if every graph with branch-width $\ge \omega/3$ has a minor isomorphic to the elementary wall of height $h$, then there is an algorithm as in (7.2), with running time $O(v^2 + \varepsilon)$."
The integer threshold `(ω + 2) / 3` expresses branch-width at least `ω/3`.
The decomposition search uses `ω / 3`, so its output width is at most `ω`. -/
theorem gm13_algorithm_7_1 (h ω : ℕ) (hh : 2 ≤ h) (_he : Even h)
    (h71 : HasPlanarGridThreshold (elemWallEdges h) ((ω + 2) / 3)) :
    ∃ P : Cmd,
      ComputesArrRelInTime algorithm72Size encAlgorithm72In (IsAlgorithm72Output ω h)
        P (fun size => size) := by
  let c := (ω + 2) / 3
  let k := ω / 3
  have hk : 2 ≤ k := two_le_search_parameter71 hh h71
  have hkc : k ≤ c := by dsimp [k, c]; omega
  have hc : 2 ≤ c := hk.trans hkc
  rcases alg41Spec72_of_claim41
      (fun δ ξ B => ⟨alg41CoreProg δ ξ B, algorithm_4_1_core δ ξ B⟩)
      ((elemWallEdges h).length + elemWallNumVerts h) (3 * c) with ⟨P41, hP41⟩
  have hP33c : Alg33Spec c 11 12 13 20 10 (alg33MultiProg c 11 12 13 20 10) :=
    alg33Spec_of_algorithm_3_3 c hc 11 12 13 20 10
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  have hP33k : Alg33Spec k inArr 17 18 20 10 (alg33MultiProg k inArr 17 18 20 10) :=
    alg33Spec_of_algorithm_3_3 k hk inArr 17 18 20 10
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  rcases alg71Prog_exec h c k (by omega) hc hk hkc h71
      (fun G hno => width_of_no_wall71 G h71 hno)
      inArr outArr 10 20 10 _ P41 _ hP33c hP41 hP33k
      (by decide) (by decide) (by decide) (by decide) with
    ⟨C, cw, hC, hcw, hexec⟩
  refine ⟨alg72Prog h (by omega) inArr outArr 10 10
    (alg33MultiProg c 11 12 13 20 10) P41 (alg33MultiProg k inArr 17 18 20 10),
    C, cw, hC, hcw, fun x s hin => ?_⟩
  have hsize : (x.n + 1) ^ 2 + (x.G.numEdges + x.n + 1) = algorithm72Size x := by
    unfold algorithm72Size
    omega
  rcases hexec x.n x.G (wordSize cw (algorithm72Size x)) (by rw [hsize]) s hin with
    ⟨s', t, hex, ht, hout, _, _⟩
  refine ⟨s', t, hex, by simpa only [hsize] using ht, ?_⟩
  rcases hout with ⟨code, hout, hvalid⟩ | ⟨W, hW, hout⟩
  · exact Or.inl ⟨code, hout, hvalid.mono (by dsimp [k]; omega)⟩
  · exact Or.inr ⟨W, hW, hout⟩

end GraphMinor.Compute
