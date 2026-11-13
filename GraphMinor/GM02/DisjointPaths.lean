module

public import GraphMinor.GM02.TreeDecomposition
public import GraphMinor.GM02.DisjointPathsInput
public import GraphMinor.Compute.DPStatement
import GraphMinor.Compute.GM02DisjointPathsProgram
import GraphMinor.GM02.TerminatedAlgorithm

/-!
# Bounded tree-width disjoint paths in Graph Minors II

The paper derives (1.3) from (3.2) (page 318). When the `2k` ends are
distinct, the terminal pairs form a termination, and the paths exist exactly
when this terminated graph is feasible (`hasDisjointPaths_iff_feasible`). The
program first rewrites the disjoint-paths encoding into the input of (3.2)
(`dpTerminatedProg_exec`), then runs the program of (3.2). That program
cannot answer "tree-width above `w`", because the promise bounds the
tree-width by `w`.
-/

@[expose] public section

namespace GraphMinor.GM02

open GraphMinor.Compute

/-- Graph Minors II, (1.3), page 310:
"For any fixed integers $k, w$ there is a polynomial algorithm to solve the
DISJOINT CONNECTING PATHS problem (stated below) for $k$ paths, in graphs of
tree-width $\le w$."

The proof is the paper's: rewrite the input as a terminated graph and run the
program of (3.2) (`algorithm_3_2`). The number of paths is a natural number,
and a negative width bound gives an empty input promise. The `2k` ends must be
distinct (`IsTermination`), as in the paper's definition of a termination.
The time is polynomial in the number of vertices. -/
theorem algorithm_1_3_proof (k : ℕ) (w : ℤ) :
    ∃ (P : Cmd) (c : ℕ),
      ComputesRelInTime (dpSize (k := k))
        (fun x s => s.arrs inArr = encDPIn x ∧ IsTermination x ∧
          ∃ q : ℕ, (q : ℤ) ≤ w ∧ TreeWidthLE x.G.toGMDigraph.toGraph q)
        IsValidDPOutput P (fun n => (n + 1) ^ c) := by
  obtain ⟨P₃, c₃, C₃, cw₃, hC₃, hcw₃, run₃⟩ := algorithm_3_2_proof w k
  refine ⟨.seq (dpTerminatedProg k) P₃, c₃ + 2, C₃ + 400 + 100 * k, cw₃ + 4 * k + 23,
    by omega, by omega, fun x s ⟨hs, hx, q, hqw, hq⟩ => ?_⟩
  let W := wordSize (cw₃ + 4 * k + 23) (dpSize x)
  have hW : (4 * k + 20) * (x.n + 1) ^ 2 < 2 ^ W := by
    have h := gm02FixedPolynomialWordBound (D := 4 * k + 20) (d := 2)
      (c := cw₃ + 4 * k + 23) (n := x.n) (w := W) (by omega) le_rfl
    exact lt_of_le_of_lt (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) 2)) h
  obtain ⟨s₁, t₁, he₁, ht₁, hs₁⟩ := dpTerminatedProg_exec x hx hW hs
  let y := dpMultiInput x hx
  obtain ⟨s₂, t₂, he₂, ht₂, hout⟩ := run₃ y s₁ ⟨hs₁, by rw [dpMultiInput_index]⟩
  have hword : wordSize cw₃ (gm02MultiTerminatedSize y) ≤ W :=
    wordSize_mono_left (by omega) _
  refine ⟨s₂, t₁ + t₂, .seq he₁ (Exec.mono_wordSize hword he₂), ?_, ?_⟩
  · change t₁ + t₂ ≤ (C₃ + 400 + 100 * k) * (x.n + 1) ^ (c₃ + 2)
    change t₂ ≤ C₃ * (x.n + 1) ^ c₃ at ht₂
    have h1 : (x.n + 1) ^ 2 ≤ (x.n + 1) ^ (c₃ + 2) := Nat.pow_le_pow_right (by omega) (by omega)
    have h2 : (x.n + 1) ^ c₃ ≤ (x.n + 1) ^ (c₃ + 2) := Nat.pow_le_pow_right (by omega) (by omega)
    have h3 := Nat.mul_le_mul_left (400 + 100 * k) h1
    have h4 := Nat.mul_le_mul_left C₃ h2
    have e : (C₃ + 400 + 100 * k) * (x.n + 1) ^ (c₃ + 2) =
        C₃ * (x.n + 1) ^ (c₃ + 2) + (400 + 100 * k) * (x.n + 1) ^ (c₃ + 2) := by ring
    omega
  · have hiff := hasDisjointPaths_iff_feasible x hx
    rcases hout with ⟨h1, hf⟩ | ⟨h0, hf⟩ | ⟨-, hlt⟩
    · exact Or.inl ⟨hiff.2 hf, h1⟩
    · exact Or.inr ⟨fun h => hf (hiff.1 h), h0⟩
    · exfalso
      have hfin := y.G.isFinite_toGMDigraph
      have hle := (treeWidth_le_iff _ hfin.finite_V hfin.finite_E q).2
        (dpMultiInput_treeWidthLE x hx hq)
      have : ((treeWidth y.G.toGMDigraph.toGraph hfin.finite_V hfin.finite_E : ℕ) : ℤ) ≤ q := by
        exact_mod_cast hle
      omega

end GraphMinor.GM02
