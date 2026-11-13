module

public import GraphMinor.Compute.Algorithm99SpecBDPrepare
public import GraphMinor.Compute.Algorithm99SpecBDSort

/-!
# Output (i) for the caller of Algorithm (9.9)

The saved graph supplies the tail stream. The program extracts the returned
decomposition, sorts its leaf words into caller order, and writes the parent
and leaf arrays. The effective tree size is in register 30. This completes the
branch-decomposition output even when the code came from the compact graph.
-/

@[expose] public section
namespace GraphMinor.Compute

/-- Extract a decomposition code and write its leaf array in caller order. -/
def alg99SpecBDProg (a_G : ℕ) : Cmd :=
  .seq alg99PrepareBDProg (alg99SortBDProg a_G)

/-- The decomposition branch writes output (i) in linear time, preserving all
registers below 28. Its hypotheses are the valid code, the saved graph and
returned output arrays, the saved-graph address, and the word bounds. -/
theorem alg99SpecBDProg_exec {w n B : ℕ} (G : MultiDigraph n) (code : List ℕ)
    (hbd : IsValidBranchDecompCode B G code) (a_G : ℕ) (ha_G : 40 ≤ a_G)
    (hn : n + 1 < 2 ^ w) (hm : 3 + 3 * G.numEdges < 2 ^ w)
    (henc : G.enc.length < 2 ^ w) (s : State)
    (hsrc : s.arrs a_G = G.enc) (hout : s.arrs outArr = 0 :: code) :
    ∃ s' time, Exec w (alg99SpecBDProg a_G) s s' time ∧
      time ≤ 1400 * (n + G.numEdges + 1) ∧
      (∃ (t : ℕ) (par f_tau : ℕ → ℕ),
        s'.regs 30 = t ∧ (s'.arrs 2).length = t ∧
        (∀ z < t, (s'.arrs 2).getD z 0 = par z) ∧
        (s'.arrs 3).length = G.numEdges ∧
        (∀ e < G.numEdges, (s'.arrs 3).getD e 0 = f_tau e) ∧
        IsWrittenDigraphBD B G.toComputeDigraph t par f_tau) ∧
      (∀ j < 28, s'.regs j = s.regs j) := by
  let x := multiCoreInput72 G code hbd
  obtain ⟨s₁, t₁, he₁, ht₁, hpar, hτ, htree, hrm, ha₁, hr₁⟩ :=
    alg99PrepareBDProg_exec G code hbd hm s hout
  have hsrc₁ : s₁.arrs a_G = G.enc :=
    (ha₁ a_G (by omega) (by omega) (by omega)).trans hsrc
  have hτword : ∀ i : Fin G.numEdges, (x.τ i).1 < 2 ^ w := by
    intro i
    have htbound : x.t ≤ 2 * G.numEdges + 1 := x.ht_le
    exact (x.τ i).2.trans_le (by omega)
  obtain ⟨s₂, t₂, he₂, ht₂, hleaves, hparents, hregtree, hr₂⟩ :=
    alg99SortBDProg_exec G (fun i => (x.τ i).1) a_G ha_G (by omega) hn
      (by omega) henc hτword s₁ hsrc₁ hτ hrm
  refine ⟨s₂, t₁ + t₂, .seq he₁ he₂, by omega, ?_, ?_⟩
  refine ⟨x.t, (fun z => (s₂.arrs 2).getD z 0), (fun e => (s₂.arrs 3).getD e 0),
    hregtree.trans htree, ?_, (fun _ _ => rfl), ?_, (fun _ _ => rfl), ?_⟩
  · rw [hparents, hpar, List.length_ofFn]
  · rw [hleaves, List.length_ofFn]
    exact G.length_directedEdgesList
  · rw [hleaves, hparents, hpar]
    exact alg99_writtenBD_of_code G code hbd
  · intro j hj
    exact (hr₂ j hj).trans (hr₁ j hj)

/-- A code returned for the compact graph gives the same output (i) for the
original deleted graph, without an additional computation on its vertices. -/
theorem alg99SpecBDProg_exec_compact {w n B : ℕ} (G : MultiDigraph n)
    (Z : Finset (Fin n)) (code : List ℕ)
    (hbd : IsValidBranchDecompCode B ((G.deleteVertices Z).deleteVerticesCompact Z) code)
    (a_G : ℕ) (ha_G : 40 ≤ a_G)
    (hn : n + 1 < 2 ^ w) (hm : 3 + 3 * (G.deleteVertices Z).numEdges < 2 ^ w)
    (henc : (G.deleteVertices Z).enc.length < 2 ^ w) (s : State)
    (hsrc : s.arrs a_G = (G.deleteVertices Z).enc) (hout : s.arrs outArr = 0 :: code) :
    ∃ s' time, Exec w (alg99SpecBDProg a_G) s s' time ∧
      time ≤ 1400 * (n + (G.deleteVertices Z).numEdges + 1) ∧
      (∃ (t : ℕ) (par f_tau : ℕ → ℕ),
        s'.regs 30 = t ∧ (s'.arrs 2).length = t ∧
        (∀ z < t, (s'.arrs 2).getD z 0 = par z) ∧
        (s'.arrs 3).length = (G.deleteVertices Z).numEdges ∧
        (∀ e < (G.deleteVertices Z).numEdges, (s'.arrs 3).getD e 0 = f_tau e) ∧
        IsWrittenDigraphBD B (G.deleteVertices Z).toComputeDigraph t par f_tau) ∧
      (∀ j < 28, s'.regs j = s.regs j) :=
  alg99SpecBDProg_exec (G.deleteVertices Z) code (alg99_validBDCode_of_compact G Z code hbd)
    a_G ha_G hn hm henc s hsrc hout

end GraphMinor.Compute
