module

public import GraphMinor.Compute.GM02TerminatedWords
public import GraphMinor.Compute.BitSet
public import GraphMinor.Compute.CrossingOpsBasic

/-!
# Copying the supplied terminal-pair block

The rank-rewrite routine reads endpoints after a two-word prefix. Copy
the terminal-pair suffix together with the two words immediately before
it. Those words are not interpreted as endpoints. Header-derived offsets
locate this block exactly, even when the graph and termination are empty.
-/

@[expose] public section
namespace GraphMinor.Compute
open GraphMinor.Compute.Crossing

/-- The endpoint suffix has two preceding words available in every valid
plain encoding, including an empty graph or empty termination. -/
theorem GM02SimpleTerminatedInput.exists_pair_block (x : GM02SimpleTerminatedInput) :
    ∃ pre : List ℕ, ∃ a : ℕ, pre.length = 1 + 2 * (edgeListOf x.G).length ∧
      x.enc = pre ++ [a, x.A.index] ++ flatEdges (edgeListOf x.A.pairGraph) := by
  let i := 1 + 2 * (edgeListOf x.G).length
  have hi : i < (encGraph x.G).length := by rw [length_encGraph]; dsimp [i]; omega
  let a := (encGraph x.G)[i]
  let pre := (encGraph x.G).take i
  have hd : (encGraph x.G).drop i = [a] := by
    rw [List.drop_eq_getElem_cons hi]
    have he : i + 1 = (encGraph x.G).length := by rw [length_encGraph]; dsimp [i]; omega
    rw [he, List.drop_length]
  have hs : encGraph x.G = pre ++ [a] := by
    calc
      encGraph x.G = (encGraph x.G).take i ++ (encGraph x.G).drop i := (List.take_append_drop i _).symm
      _ = _ := by rw [hd]
  refine ⟨pre, a, List.length_take_of_le (Nat.le_of_lt hi), ?_⟩
  simp only [GM02SimpleTerminatedInput.enc, hs, List.append_assoc, List.cons_append, List.nil_append]

/-- Copy the two-word-prefixed endpoint block, using header metadata 280
and 281 and scratch registers 283 through 287. -/
def gm02CopyPairBlockProg (src dst : Arr) : Cmd :=
  .seq (.assign 284 (.op .sub (.reg 280) (.const 2)))
    (.seq (.assign 283 (.op .add (.const 2) (.reg 281)))
      (readSliceProg src (.reg 284) dst (.reg 283) 285))

/-- The copy returns precisely the supplied endpoint words after its two
ignored header words, with a linear endpoint-count time bound. -/
theorem gm02CopyPairBlockProg_exec {w : ℕ} (x : GM02SimpleTerminatedInput)
    (src dst : Arr) (hne : src ≠ dst) (s : State) (hsrc : s.arrs src = x.enc)
    (hstart : s.regs 280 = 3 + 2 * (edgeListOf x.G).length) (hcount : s.regs 281 = 2 * x.A.index)
    (hn : x.n < 2 ^ w) (hlen : x.enc.length < 2 ^ w) :
    ∃ s' t a, Exec w (gm02CopyPairBlockProg src dst) s s' t ∧
      t ≤ 16 * (2 + 2 * x.A.index) + 17 ∧
      s'.arrs dst = [a, x.A.index] ++ flatEdges (edgeListOf x.A.pairGraph) ∧
      (∀ b, b ≠ dst → s'.arrs b = s.arrs b) ∧
      (∀ r < 283, s'.regs r = s.regs r) := by
  have hl := x.enc_length
  have hw : 1 < 2 ^ w := by omega
  have h2 : 2 < 2 ^ w := by omega
  obtain ⟨pre, a, hpre, henc⟩ := x.exists_pair_block
  let mid := [a, x.A.index] ++ flatEdges (edgeListOf x.A.pairGraph)
  have hmid : mid.length = 2 + 2 * x.A.index := by
    simp only [mid, List.length_append, List.length_cons, List.length_nil,
      length_flatEdges, gm02Termination_pairList_length]
  let s₁ := s.setReg 284 (1 + 2 * (edgeListOf x.G).length)
  have he₁ : Exec w (.assign 284 (.op .sub (.reg 280) (.const 2))) s s₁ 4 := by
    apply Exec.assign
    have he := eval_sub (eval_reg hstart (by omega)) (eval_const h2)
    have hsub : 3 + 2 * (edgeListOf x.G).length - 2 = 1 + 2 * (edgeListOf x.G).length := by omega
    simpa only [hsub] using he
  let s₂ := s₁.setReg 283 (2 + 2 * x.A.index)
  have he₂ : Exec w (.assign 283 (.op .add (.const 2) (.reg 281))) s₁ s₂ 4 := by
    apply Exec.assign
    exact eval_add (eval_const h2) (eval_reg (by simpa [s₁] using hcount) (by omega)) (by omega)
  have hwords : ∀ v ∈ mid, v < 2 ^ w := by
    intro v hv
    apply x.enc_all_lt hn hlen v
    rw [henc, List.append_assoc]
    exact List.mem_append.2 (Or.inr hv)
  obtain ⟨s', t, he, ht, hout, ha, hr⟩ := readSliceProg_exec src dst (.reg 284) 283 285 hne
    (by decide) pre mid [] hpre hmid hwords hw (by omega) (s := s₂)
    (eval_reg (by simp [s₂, s₁]) (by omega))
    (by simpa only [s₂, s₁, State.setReg_arrs, List.append_nil, List.append_assoc] using hsrc.trans henc)
    (by simp [s₂])
  refine ⟨s', _, a, Exec.seq he₁ (Exec.seq he₂ he), ?_, hout, ?_, ?_⟩
  · simp only [Expr.cost_reg] at ht
    omega
  · intro b hb
    exact ha b hb
  · intro r hrl
    dsimp only [Reg] at hrl
    rw [hr r (by omega)]
    simp [s₂, s₁, State.setReg_regs_ne (r := 283) (r' := r) _ _ (by dsimp only [Reg]; omega),
      State.setReg_regs_ne (r := 284) (r' := r) _ _ (by dsimp only [Reg]; omega)]

end GraphMinor.Compute
