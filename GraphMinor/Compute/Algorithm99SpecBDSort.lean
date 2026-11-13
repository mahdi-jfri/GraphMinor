module

public import GraphMinor.Compute.Algorithm99OrderLeaves
public import GraphMinor.Compute.Join13Graph72
public import GraphMinor.Compute.Join13Project72
public import GraphMinor.Compute.Algorithm99State

/-!
# Preparing tails and reordering the decomposition leaf array

The saved graph is expanded into its individual endpoints, and a gather reads
the tail column. The stable counting sort then reorders the leaf words. The
parent array and effective tree-size register are preserved throughout.
-/

@[expose] public section
namespace GraphMinor.Compute
open TwoPaths

local macro "romega" : tactic => `(tactic| ((try dsimp only [Reg, Arr] at *); omega))

/-- Sort the prepared leaf array using the saved graph's tail stream. -/
def alg99SortBDProg (a_G : ℕ) : Cmd :=
  .seq (expandGraph72Prog a_G 11 80)
    (.seq (projectEndpoint72Prog 0 11 12 28 90)
      (.seq (.assign 29 (.op .add (.read a_G (.const 0)) (.const 1)))
        (.seq (alg99TailSortProg 12 90 29) (copyArrLoopProg 16 3 80 81))))

/-- The leaf-sorting stage takes linear time. The saved graph, parent array,
tree size in register 30, and every register below 28 are preserved. -/
theorem alg99SortBDProg_exec {w n : ℕ} (G : MultiDigraph n) (τ : Fin G.numEdges → ℕ)
    (a_G : ℕ) (ha_G : 40 ≤ a_G) (hw : 3 < 2 ^ w) (hn : n + 1 < 2 ^ w)
    (hm : 2 * G.numEdges < 2 ^ w) (henc : G.enc.length < 2 ^ w)
    (hτ : ∀ i, τ i < 2 ^ w) (s : State)
    (hsrc : s.arrs a_G = G.enc) (hvals : s.arrs 13 = List.ofFn τ)
    (hrm : s.regs 28 = G.numEdges) :
    ∃ s' t, Exec w (alg99SortBDProg a_G) s s' t ∧
      t ≤ 1000 * (n + G.numEdges + 1) ∧
      s'.arrs 3 = List.ofFn (fun e : Fin G.toComputeDigraph.numEdges =>
        τ (G.computeToMultiEdgeEquiv e)) ∧
      s'.arrs 2 = s.arrs 2 ∧ s'.regs 30 = s.regs 30 ∧
      (∀ j < 28, s'.regs j = s.regs j) := by
  obtain ⟨s₁, t₁, he₁, ht₁, hends, hk₁⟩ :=
    expandGraph72Prog_exec (w := w) G a_G 11 80 (by romega) s hw (by omega) hm henc hsrc hrm
  obtain ⟨s₂, t₂, he₂, ht₂, hk₂, hkeys⟩ :=
    projectEndpoint72Prog_exec (w := w) G.toMultiComputeDigraph 0 11 12 28 90
      (by decide) (by decide) s₁ (by omega) (by change n < 2 ^ w; omega) hm hends
      ((hk₁.1 28 (by decide)).trans hrm)
  have hsrc₂ : s₂.arrs a_G = G.enc :=
    (hk₂.2 a_G (by simp; romega)).trans ((hk₁.2 a_G (by simp; romega)).trans hsrc)
  let s₃ := s₂.setReg 29 (n + 1)
  have he₃ : Exec w (.assign 29 (.op .add (.read a_G (.const 0)) (.const 1))) s₂ s₃ 5 := by
    apply Exec.assign
    have hlen : 0 < (s₂.arrs a_G).length := by rw [hsrc₂, G.length_enc]; omega
    have hzero : (s₂.arrs a_G)[0]'hlen = n := by simp [hsrc₂, MultiDigraph.enc]
    simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hlen, hzero, hn,
      show 1 < 2 ^ w by omega, show n < 2 ^ w by omega]
  have hkeys₃ : s₃.arrs 12 = List.ofFn (fun i : Fin G.numEdges => (G.edgeEndpoints i).1.1) := by
    simpa [s₃, List.getD] using hkeys
  have hvals₃ : s₃.arrs 13 = List.ofFn τ := by
    simp only [s₃, State.setReg_arrs]
    exact (hk₂.2 13 (by decide)).trans ((hk₁.2 13 (by decide)).trans hvals)
  obtain ⟨s₄, t₄, he₄, ht₄, hsort, ha₄, hr₄⟩ :=
    alg99TailSortProg_exec_leaves G τ 12 90 29 (by omega) hn (by omega) hτ s₃
      hkeys₃ hvals₃ (by simp [s₃])
  have hwords₄ : ∀ v ∈ s₄.arrs 16, v < 2 ^ w := by
    rw [hsort]
    intro v hv
    obtain ⟨i, rfl⟩ := List.mem_ofFn.1 hv
    exact hτ _
  have hlen₄ : (s₄.arrs 16).length < 2 ^ w := by
    rw [hsort, List.length_ofFn]
    change G.directedEdgesList.length < 2 ^ w
    rw [G.length_directedEdgesList]
    omega
  obtain ⟨s₅, t₅, he₅, ht₅, hout, ha₅, hr₅⟩ :=
    copyArrLoopProg_exec (w := w) 16 3 80 81 (by decide) (by decide) (by omega)
      s₄ hlen₄ hwords₄
  refine ⟨s₅, t₁ + (t₂ + (5 + (t₄ + t₅))),
    .seq he₁ (.seq he₂ (.seq he₃ (.seq he₄ he₅))), ?_, hout.trans hsort, ?_, ?_, ?_⟩
  · rw [hsort, List.length_ofFn] at ht₅
    change t₂ ≤ 20 * (G.numEdges + 1) at ht₂
    change t₅ ≤ 8 + 15 * G.directedEdgesList.length at ht₅
    rw [G.length_directedEdgesList] at ht₅
    omega
  · rw [ha₅ 2 (by decide), ha₄ 2 (by decide) (by decide) (by decide)]
    simp only [s₃, State.setReg_arrs]
    exact (hk₂.2 2 (by decide)).trans (hk₁.2 2 (by decide))
  · rw [hr₅ 30 (by decide) (by decide), hr₄ 30 (by decide) (by decide) (by decide)]
    simp only [s₃, State.setReg_regs_ne _ _ (by decide : (30 : Reg) ≠ 29)]
    exact (hk₂.1 30 (by decide)).trans (hk₁.1 30 (by decide))
  · intro j hj
    rw [hr₅ j (by romega) (by romega), hr₄ j (by romega) (by romega) (by romega)]
    simp only [s₃, State.setReg_regs_ne _ _ (show j ≠ 29 by romega)]
    exact (hk₂.1 j (by simp; romega)).trans (hk₁.1 j (by simp; romega))

end GraphMinor.Compute
