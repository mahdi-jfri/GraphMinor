module

public import GraphMinor.Compute.GM02PortEdgePrefix
public import GraphMinor.Compute.GM02FullPortGraph
public import GraphMinor.Compute.CrossingOpsBasic

/-!
# Initializing the canonical split edge buffer

Compute the numeric vertex count and its square from the original
header. Allocate room for two header words and two words for every
ordered pair. Write the vertex-count header and initialize the scan
index, next free position, and emitted edge count.
-/

public section
namespace GraphMinor.Compute
open GraphMinor.Compute.Crossing

/-- Allocate the split edge buffer and initialize the counting scan metadata. -/
@[expose] def gm02InitPortEdgeBufferProg (K : ℕ) : Cmd :=
  .seq (.assign 66 (.op .add (.op .add (.reg 10) (.reg 11)) (.const (2 * K))))
    (.seq (.assign 65 (.op .mul (.reg 66) (.reg 66)))
      (.seq (.assign 69 (.op .add (.const 2) (.op .mul (.const 2) (.reg 65))))
        (.seq (.alloc 24 (.reg 69))
          (.seq (.write 24 (.const 0) (.reg 66))
            (.seq (.assign 64 (.const 0))
              (.seq (.assign 67 (.const 2)) (.assign 68 (.const 0))))))))

/-- Initialization creates exactly the empty canonical buffer and its scan counters. -/
theorem gm02InitPortEdgeBufferProg_exec {w K : ℕ} (x : GM02TopologicalInput) (s : State)
    (gflags hflags : List ℕ) (code : ℕ) (hn : s.regs 10 = x.G.n) (hm : s.regs 11 = x.G.edges.length)
    (hw : 2 < 2 ^ w) (hN : gm02FullPortSize x K < 2 ^ w)
    (hcap : 2 + 2 * (gm02FullPortSize x K * gm02FullPortSize x K) < 2 ^ w) :
    ∃ s', Exec w (gm02InitPortEdgeBufferProg K) s s'
        (28 + 2 * (gm02FullPortSize x K * gm02FullPortSize x K)) ∧
      s'.arrs 24 = gm02PortEdgeBuffer (gm02FullPortGraph x gflags hflags code K) 0 ∧
      s'.regs 64 = 0 ∧ s'.regs 65 = gm02FullPortSize x K * gm02FullPortSize x K ∧
      s'.regs 66 = gm02FullPortSize x K ∧ s'.regs 67 = 2 ∧ s'.regs 68 = 0 ∧
      (∀ a, a ≠ 24 → s'.arrs a = s.arrs a) ∧
      (∀ r, r ∉ [64, 65, 66, 67, 68, 69] → s'.regs r = s.regs r) := by
  let N := gm02FullPortSize x K
  let cap := 2 + 2 * (N * N)
  have hnw : x.G.n < 2 ^ w := by unfold gm02FullPortSize at hN; omega
  have hmw : x.G.edges.length < 2 ^ w := by unfold gm02FullPortSize at hN; omega
  have hsum : x.G.n + x.G.edges.length < 2 ^ w := by unfold gm02FullPortSize at hN; omega
  have hKw : 2 * K < 2 ^ w := by unfold gm02FullPortSize at hN; omega
  have hSq : N * N < 2 ^ w := by dsimp only [N]; omega
  have h2Sq : 2 * (N * N) < 2 ^ w := by dsimp only [N]; omega
  let s₀ := s.setReg 66 N
  have he₀ : Exec w (.assign 66 (.op .add (.op .add (.reg 10) (.reg 11)) (.const (2 * K)))) s s₀ 6 :=
    .assign (eval_add (eval_add (eval_reg hn hnw) (eval_reg hm hmw) hsum) (eval_const hKw) hN)
  let s₁ := s₀.setReg 65 (N * N)
  have he₁ : Exec w (.assign 65 (.op .mul (.reg 66) (.reg 66))) s₀ s₁ 4 :=
    .assign (eval_mul (eval_reg (State.setReg_regs_self ..) hN) (eval_reg (State.setReg_regs_self ..) hN) hSq)
  let s₂ := s₁.setReg 69 cap
  have he₂ : Exec w (.assign 69 (.op .add (.const 2) (.op .mul (.const 2) (.reg 65)))) s₁ s₂ 6 :=
    .assign (eval_add (eval_const hw)
      (eval_mul (eval_const hw) (eval_reg (State.setReg_regs_self ..) hSq) h2Sq) hcap)
  let s₃ := s₂.setArr 24 (List.replicate cap 0)
  have he₃ : Exec w (.alloc 24 (.reg 69)) s₂ s₃ (1 + cap) :=
    .alloc (eval_reg (State.setReg_regs_self ..) hcap)
  let s₄ := s₃.writeArr 24 0 N
  have hn₃ : s₃.regs 66 = N := by simp [s₃, s₂, s₁, s₀]
  have he₄ : Exec w (.write 24 (.const 0) (.reg 66)) s₃ s₄ 3 :=
    .write (eval_const (by omega)) (eval_reg hn₃ hN) (by simp [s₃, cap])
  let s₅ := s₄.setReg 64 0
  let s₆ := s₅.setReg 67 2
  let s₇ := s₆.setReg 68 0
  have he₅ : Exec w (.assign 64 (.const 0)) s₄ s₅ 2 := .assign (eval_const (by omega))
  have he₆ : Exec w (.assign 67 (.const 2)) s₅ s₆ 2 := .assign (eval_const hw)
  have he₇ : Exec w (.assign 68 (.const 0)) s₆ s₇ 2 := .assign (eval_const (by omega))
  have hex := Exec.seq he₀ (.seq he₁ (.seq he₂ (.seq he₃ (.seq he₄ (.seq he₅ (.seq he₆ he₇))))))
  refine ⟨s₇, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · convert hex using 1 <;> first | rfl | (dsimp only [cap, N]; omega)
  · change (List.replicate cap 0).set 0 N = _
    simp only [gm02PortEdgeBuffer, gm02PortEdgeWords, gm02EdgePrefix_zero, List.length_nil,
      Nat.sub_zero, flatEdges, List.flatMap_nil, List.append_nil]
    have hc : cap = (2 * (N * N) + 1) + 1 := by dsimp only [cap]; omega
    rw [hc, List.replicate_succ, List.set_cons_zero, List.replicate_succ]
    rfl
  · simp [s₇, s₆, s₅]
  · simp [s₇, s₆, s₅, s₄, s₃, s₂, s₁, N]
  · simp [s₇, s₆, s₅, s₄, s₃, s₂, s₁, s₀, N]
  · simp [s₇, s₆]
  · exact State.setReg_regs_self ..
  · intro a ha
    exact (State.writeArr_arrs_ne s₃ 0 N ha).trans (State.setArr_arrs_ne s₂ _ ha)
  · intro r hr
    have hne (a : ℕ) (ha : a ∈ [64, 65, 66, 67, 68, 69]) : r ≠ a := fun h => hr (h.symm ▸ ha)
    simp only [s₇, s₆, s₅, s₄, s₃, s₂, s₁, s₀, State.setReg_regs_ne _ _ (hne 68 (by decide)),
      State.setReg_regs_ne _ _ (hne 67 (by decide)), State.setReg_regs_ne _ _ (hne 64 (by decide)),
      State.writeArr_regs, State.setArr_regs, State.setReg_regs_ne _ _ (hne 69 (by decide)),
      State.setReg_regs_ne _ _ (hne 65 (by decide)), State.setReg_regs_ne _ _ (hne 66 (by decide))]

end GraphMinor.Compute
