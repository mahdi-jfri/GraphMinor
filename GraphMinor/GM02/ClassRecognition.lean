module

public import GraphMinor.GM02.TreeWidthRecognition

/-!
# Recognition of minor-closed classes in Graph Minors II

For a planar graph `H`, the paper (pages 318–320) proves (4.1), which is (1.1),
by running the program of (4.9) with `w` from (4.10). If the program finds
tree-width above `w`, then (4.10) says that `H` is a minor. On page 321 it
derives (5.5) from (4.10) and (5.4): a minor-closed class that misses a planar
graph `H` contains no graph with an `H` minor, so (4.10) bounds the tree-width
of its members.

The input is the multigraph encoding `x.G.enc`, and the time is polynomial in
`(n + 1)²`, where `n` is the number of vertices.
-/

public section

namespace GraphMinor.GM02

open GraphMinor.Compute Graph Set Classical

/-- Graph Minors II, (4.1), page 318:
"For any fixed planar graph $H$, there is a polynomial algorithm to decide if
 the input graph has a minor isomorphic to $H$."

The proof is the paper's: run the program of (4.9) for `H` with `w` from (4.10)
(`theorem_4_10`). The answer "tree-width above `w`" means that `H` is a minor,
by (4.10). Zero means that the minor exists and one means it does not. -/
theorem algorithm_4_1_proof
    (H : Graph ℕ (ℕ × ℕ × ℕ)) (hVH : V(H).Finite) (hEH : E(H).Finite)
    (hPlanar : IsPlanar H) :
    ∃ (P : Cmd) (c : ℕ),
      ComputesRelInTime alg44Size (fun x s => s.arrs inArr = x.G.enc)
        (fun x s => s.regs outReg =
          if ¬ IsIsoMinor H x.G.toGMDigraph.toGraph then 1 else 0)
        P (fun n => (n + 1) ^ c) := by
  obtain ⟨w, hw⟩ := theorem_4_10_proof H hPlanar (α := ℕ) (β := ℕ × ℕ × ℕ)
  obtain ⟨P, c, hP⟩ := exists_multiMinorScan {H} (by simp [hVH, hEH]) w
  obtain ⟨C, cw, hC, hcw, run⟩ := ComputesRelInTime.seq_isZero hP (by
    rintro x s (⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩) <;> omega)
  refine ⟨.seq P isZeroOutProg, c, C, cw, hC, hcw, fun x s hs => ?_⟩
  obtain ⟨s', t, he, ht, s₀, hout, hval⟩ := run x s hs
  refine ⟨s', t, he, ht, ?_⟩
  show s'.regs outReg = _
  have hfin := x.G.isFinite_toGMDigraph
  rw [hval]
  rcases hout with ⟨h1, H', hH', hm⟩ | ⟨h0, hno⟩ | ⟨h2, hlt⟩
  · rw [Finset.mem_singleton] at hH'
    subst hH'
    rw [ite_eq_right (by omega), ite_eq_right (not_not.2 hm)]
  · rw [ite_eq_left h0, ite_eq_left (hno H (Finset.mem_singleton_self H))]
  · rw [ite_eq_right (by omega), ite_eq_right]
    exact fun hno => hlt w le_rfl (hw _ hfin.finite_V hfin.finite_E hno)

/-- Graph Minors II, (1.1), page 310:
"For any fixed planar graph $H$, there is a polynomial algorithm to decide if
 the input graph has a minor isomorphic to $H$."

This is (4.1) (`algorithm_4_1`), as in the paper. The program returns zero
when `H` is a minor and one otherwise. -/
theorem algorithm_1_1_proof
    (H : Graph ℕ (ℕ × ℕ × ℕ)) (hVH : V(H).Finite) (hEH : E(H).Finite)
    (hPlanar : IsPlanar H) :
    ∃ (P : Cmd) (c : ℕ),
      ComputesRelInTime alg44Size (fun x s => s.arrs inArr = x.G.enc)
        (fun x s => s.regs outReg =
          if ¬ IsIsoMinor H x.G.toGMDigraph.toGraph then 1 else 0)
        P (fun n => (n + 1) ^ c) :=
  algorithm_4_1_proof H hVH hEH hPlanar

/-- Graph Minors II, (5.5), page 321:
"Let $\mathcal{F}$ be any set of graphs, membership of which is preserved under
isomorphism and under taking minors. Suppose that some planar graph is not in
$\mathcal{F}$. Then there is a polynomial algorithm to test if an arbitrary graph
is in $\mathcal{F}$."

The proof is the paper's: a member of the class has no minor isomorphic to the
planar graph `H` outside it, so (4.10) (`theorem_4_10`) bounds its tree-width,
and (5.4) (`algorithm_5_4`) applies. Minor closure under `IsIsoMinor` includes
preservation under isomorphism. The program returns one for members and zero
otherwise. -/
theorem algorithm_5_5_proof
    (ℱ : Set (Graph ℕ (ℕ × ℕ × ℕ)))
    (hclosed : ∀ ⦃G₁ G₂ : Graph ℕ (ℕ × ℕ × ℕ)⦄,
      V(G₁).Finite → E(G₁).Finite → V(G₂).Finite → E(G₂).Finite →
      IsIsoMinor G₁ G₂ → G₂ ∈ ℱ → G₁ ∈ ℱ)
    (H : Graph ℕ (ℕ × ℕ × ℕ)) (hVH : V(H).Finite) (hEH : E(H).Finite)
    (hPlanar : IsPlanar H) (hH : H ∉ ℱ) :
    ∃ (P : Cmd) (c : ℕ),
      ComputesRelInTime alg44Size (fun x s => s.arrs inArr = x.G.enc)
        (fun x s => s.regs outReg = if x.G.toGMDigraph.toGraph ∈ ℱ then 1 else 0)
        P (fun n => (n + 1) ^ c) := by
  obtain ⟨w, hw⟩ := theorem_4_10_proof H hPlanar (α := ℕ) (β := ℕ × ℕ × ℕ)
  exact algorithm_5_4_proof ℱ hclosed w fun G hG hV hE =>
    hw G hV hE fun hm => hH (hclosed hVH hEH hV hE hm hG)

end GraphMinor.GM02
