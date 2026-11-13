module

public import GraphMinor.Compute.Join13ExpandStream72

/-!
# Expanding the graph input for (7.2)

The wrapper allocates the endpoint array, reads the number of input triples,
and expands their multiplicities. It produces the exact edge order used by
`toMultiComputeDigraph`, without building a matrix of vertex pairs.
-/

@[expose] public section
namespace GraphMinor.Compute
open TwoPaths

/-- Expand a graph's encoded triples, using register 28 for its edge count. -/
def expandGraph72Prog (a_src a_ends r : ℕ) : Cmd :=
  .seq (.alloc a_ends (.op .mul (.const 2) (.reg 28)))
  (.seq (.assign r (.const 0))
  (.seq (.assign (r + 4) (.const 2))
  (.seq (.assign (r + 5) (.read a_src (.const 1)))
        (expandPairStream72Loop a_src a_ends r))))

/-- Graph expansion is linear in the number of vertices and individual edges. -/
theorem expandGraph72Prog_exec {w n : ℕ} (G : MultiDigraph n)
    (a_src a_ends r : ℕ) (hne : a_src ≠ a_ends) (s : State)
    (hw : 3 < 2 ^ w) (hn : n < 2 ^ w) (hm : 2 * G.numEdges < 2 ^ w)
    (henc : G.enc.length < 2 ^ w) (hsrc : s.arrs a_src = G.enc)
    (hrm : s.regs 28 = G.numEdges) :
    ∃ s' t, Exec w (expandGraph72Prog a_src a_ends r) s s' t ∧
      t ≤ 400 * (n + G.numEdges + 1) ∧
      s'.arrs a_ends = endpointWords72 G.toMultiComputeDigraph ∧
      Keeps [r, r + 1, r + 2, r + 3, r + 4, r + 5] [a_ends] s s' := by
  have h0 : 0 < 2 ^ w := by omega
  have h1 : 1 < 2 ^ w := by omega
  have h2 : 2 < 2 ^ w := by omega
  have hpairs : G.activePairsList.length ≤ G.numEdges := by
    rw [← G.sumEdgeMult_activePairsList]
    exact length_activePairs_le_sum72 G _ (fun p hp => (G.mem_activePairsList p).1 hp)
  let s₁ := s.setArr a_ends (List.replicate (2 * G.numEdges) 0)
  have hex₁ : Exec w (.alloc a_ends (.op .mul (.const 2) (.reg 28))) s s₁ (3 + 2 * G.numEdges) :=
    .alloc (by simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hrm, h2, hm,
      show G.numEdges < 2 ^ w by omega])
  let s₂ := s₁.setReg r 0
  have hex₂ : Exec w (.assign r (.const 0)) s₁ s₂ 2 := .assign (by simp [Expr.eval, checkWord, h0])
  let s₃ := s₂.setReg (r + 4) 2
  have hex₃ : Exec w (.assign (r + 4) (.const 2)) s₂ s₃ 2 := .assign (by simp [Expr.eval, checkWord, h2])
  let s₄ := s₃.setReg (r + 5) G.numActivePairs
  have hs₃ : s₃.arrs a_src = G.enc := by simp [s₃, s₂, s₁, hne, hsrc]
  have hex₄ : Exec w (.assign (r + 5) (.read a_src (.const 1))) s₃ s₄ 3 := by
    apply Exec.assign
    have hlen : 1 < (s₃.arrs a_src).length := by rw [hs₃, G.length_enc]; omega
    have hget : (s₃.arrs a_src)[1]'hlen = G.numActivePairs := by simp [hs₃, MultiDigraph.enc]
    have hp : G.numActivePairs < 2 ^ w := by change G.activePairsList.length < 2 ^ w; omega
    simp [Expr.eval, checkWord, h1, hlen, hget, hp]
  obtain ⟨s₅, t₅, hex₅, ht₅, hd₅, _, _, _, hk₅⟩ :=
    expandPairStream72Loop_exec G G.activePairsList a_src a_ends r hne
      [n, G.numActivePairs] [] [] 0 s₄ hw hn
      (by simpa [G.sumEdgeMult_activePairsList] using hm)
      (by simpa [MultiDigraph.enc] using henc)
      (by simpa [s₄, MultiDigraph.enc] using hs₃)
      (by simp [s₄, s₃, s₂, s₁, G.sumEdgeMult_activePairsList])
      (by simp [s₄, s₃, s₂]) (by simp [s₄, s₃]) (by simp [s₄, MultiDigraph.numActivePairs])
  refine ⟨s₅, (3 + 2 * G.numEdges) + (2 + (2 + (3 + t₅))),
    .seq hex₁ (.seq hex₂ (.seq hex₃ (.seq hex₄ hex₅))), ?_, ?_, ?_⟩
  · rw [G.sumEdgeMult_activePairsList] at ht₅
    omega
  · rw [endpointWords72_toMultiComputeDigraph]
    simpa using hd₅
  · refine ⟨fun j hj => ?_, fun a ha => ?_⟩
    · rw [hk₅.1 j hj]
      have hj0 : j ≠ r := by simp only [List.mem_cons, not_or] at hj; tauto
      have hj4 : j ≠ r + 4 := by simp only [List.mem_cons, not_or] at hj; tauto
      have hj5 : j ≠ r + 5 := by simp only [List.mem_cons, not_or] at hj; tauto
      simp [s₄, s₃, s₂, s₁, hj0, hj4, hj5]
    · rw [hk₅.2 a ha]
      have hne' : a ≠ a_ends := by simpa using ha
      simp [s₄, s₃, s₂, s₁, hne']

end GraphMinor.Compute
