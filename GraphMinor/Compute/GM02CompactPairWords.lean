module

public import GraphMinor.Compute.GM02PairBlock
public import GraphMinor.Compute.GM02RankEdgeWords
public import GraphMinor.Compute.GM02CompactTermination

/-!
# Producing compact terminal-pair words from the plain input

Copy the supplied endpoint block, recover its pair count from the parsed
endpoint length, and rewrite each endpoint by its compact vertex rank.
When all terminals survive deletion, the matching-graph identities prove
that these are exactly the canonical words of the compact termination.
The two passes use linear time in the original terminal index.
-/

@[expose] public section
namespace GraphMinor.Compute
open Classical GraphMinor.GM02

/-- Copy and rank the original terminal endpoints, using the parsed slice
metadata in 280 and 281. -/
def gm02CompactPairWordsProg (src block rank dst : Arr) : Cmd :=
  .seq (gm02CopyPairBlockProg src block)
    (.seq (.assign 22 (.op .div (.reg 281) (.const 2))) (gm02RankEdgeWordsProg block rank dst))

/-- The compact endpoint program writes the exact canonical pair suffix
for any deletion set that retains the original terminals. -/
theorem gm02CompactPairWordsProg_exec {w : ℕ} (x : GM02SimpleTerminatedInput)
    (Z : Finset (Fin x.n)) (hAZ : x.A.support ⊆ {v | v ∉ Z})
    (src block rank dst : Arr) (hsb : src ≠ block) (hrb : rank ≠ block)
    (hbd : block ≠ dst) (hrd : rank ≠ dst) (s : State)
    (hsrc : s.arrs src = x.enc)
    (hrank : s.arrs rank = List.ofFn (fun v : Fin x.n => compactRank Z v.val))
    (hstart : s.regs 280 = 3 + 2 * (edgeListOf x.G).length) (hcount : s.regs 281 = 2 * x.A.index)
    (hn : x.n < 2 ^ w) (hlen : x.enc.length < 2 ^ w) :
    ∃ s' t, Exec w (gm02CompactPairWordsProg src block rank dst) s s' t ∧
      t ≤ 63 + 70 * x.A.index ∧
      s'.arrs dst = flatEdges (edgeListOf (gm02CompactTermination Z (x.A.rebase hAZ)).pairGraph) ∧
      (∀ a, a ≠ block → a ≠ dst → s'.arrs a = s.arrs a) ∧
      (∀ r < 22, s'.regs r = s.regs r) := by
  have hl := x.enc_length
  obtain ⟨s₁, t₁, a, he₁, ht₁, hblock₁, ha₁, hr₁⟩ :=
    gm02CopyPairBlockProg_exec x src block hsb s hsrc hstart hcount hn hlen
  have hcount₁ : s₁.regs 281 = 2 * x.A.index := (hr₁ 281 (by decide)).trans hcount
  let s₂ := s₁.setReg 22 x.A.index
  have he₂ : Exec w (.assign 22 (.op .div (.reg 281) (.const 2))) s₁ s₂ 4 := by
    apply Exec.assign
    have hdiv : 2 * x.A.index / 2 = x.A.index := by omega
    simp [Expr.eval, BinOp.eval, BinOp.raw, hcount₁, hdiv,
      checkWord_of_lt (by omega : 2 * x.A.index < 2 ^ w),
      checkWord_of_lt (by omega : 2 < 2 ^ w), checkWord_of_lt (by omega : x.A.index < 2 ^ w)]
  obtain ⟨s₃, t₃, he₃, ht₃, hk₃, hout⟩ := gm02RankEdgeWordsProg_exec Z (edgeListOf x.A.pairGraph)
    block rank dst hbd hrd a x.A.index [] s₂ hn
    (by rw [gm02Termination_pairList_length]; omega)
    (by simpa only [s₂, State.setReg_arrs, List.append_nil] using hblock₁)
    (by simpa only [s₂, State.setReg_arrs] using (ha₁ rank hrb).trans hrank)
    (by simp [s₂, gm02Termination_pairList_length])
  have hpairs : flatEdges (edgeListOf (gm02CompactTermination Z (x.A.rebase hAZ)).pairGraph) =
      (flatEdges (edgeListOf x.A.pairGraph)).map (compactRank Z) :=
    gm02CompactTermination_pairWords Z (x.A.rebase hAZ)
  refine ⟨s₃, _, Exec.seq he₁ (Exec.seq he₂ he₃), ?_, hout.trans hpairs.symm, ?_, ?_⟩
  · rw [gm02Termination_pairList_length] at ht₃
    omega
  · intro b hbb hbd'
    rw [hk₃.2 b (by simpa only [List.mem_singleton] using hbd')]
    exact ha₁ b hbb
  · intro r hrl
    dsimp only [Reg] at hrl
    rw [hk₃.1 r (by simp only [List.mem_singleton]; omega)]
    have hr22 : r ≠ (22 : Reg) := by dsimp only [Reg]; omega
    rw [State.setReg_regs_ne _ _ hr22]
    exact hr₁ r (by dsimp only [Reg]; omega)

end GraphMinor.Compute
