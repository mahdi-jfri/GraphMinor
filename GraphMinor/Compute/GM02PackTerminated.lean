module

public import GraphMinor.Compute.GM02AllocateHeader
public import GraphMinor.Compute.GM02WriteTermIndex
public import GraphMinor.Compute.Algorithm33Multigraph

/-!
# Packing a plain recursive terminated input

The child edge words and terminal-pair words are already in compact
canonical order. Allocate the output, write the graph header, append the
edge words, write the terminal index, and append the pair words. Counts
and buffer lengths are held in registers 260 through 265. No answer or
linkage is copied into the input.
-/

@[expose] public section
namespace GraphMinor.Compute

/-- Assemble `[n,m]`, edge words, `[k]`, and terminal-pair words.
Registers 260–265 hold `n,m,k,edgeLength,pairLength,totalLength`. -/
def gm02PackTerminatedProg (edges pairs dst : Arr) : Cmd :=
  .seq (gm02AllocateHeaderProg dst 265 260 261)
    (.seq (.assign 271 (.const 2))
      (.seq (appendArrToDstProg edges dst 263 270)
        (.seq (gm02WriteTermIndexProg dst 271 262)
          (appendArrToDstProg pairs dst 264 270))))

/-- Packing uses linear time in the output length, changing only the
output array and registers at least 260. -/
theorem gm02PackTerminatedProg_exec {w n m k : ℕ} (edges pairs dst : Arr)
    (hed : edges ≠ dst) (hpd : pairs ≠ dst) (E P : List ℕ) (s : State)
    (he : s.arrs edges = E) (hp : s.arrs pairs = P)
    (hn : s.regs 260 = n) (hm : s.regs 261 = m) (hk : s.regs 262 = k)
    (hel : s.regs 263 = E.length) (hpl : s.regs 264 = P.length)
    (htotal : s.regs 265 = 3 + E.length + P.length)
    (hlen : 3 + E.length + P.length < 2 ^ w)
    (hnw : n < 2 ^ w) (hmw : m < 2 ^ w) (hkw : k < 2 ^ w)
    (hew : ∀ v ∈ E, v < 2 ^ w) (hpw : ∀ v ∈ P, v < 2 ^ w) :
    ∃ s' t, Exec w (gm02PackTerminatedProg edges pairs dst) s s' t ∧
      t ≤ 40 + 16 * (E.length + P.length) ∧
      s'.arrs dst = [n, m] ++ E ++ [k] ++ P ∧
      (∀ a, a ≠ dst → s'.arrs a = s.arrs a) ∧
      (∀ r < 260, s'.regs r = s.regs r) := by
  have hw : 1 < 2 ^ w := by omega
  obtain ⟨s₀, hex₀, ha₀, hr₀, hf₀⟩ := gm02AllocateHeaderProg_exec
    (extra := E.length + 1 + P.length) dst 265 260 261 s
    (by omega) hn hm (by omega) hnw hmw
  let s₁ := s₀.setReg 271 2
  have hex₁ : Exec w (.assign 271 (.const 2)) s₀ s₁ 2 :=
    Exec.assign (by simp [Expr.eval, checkWord_of_lt (by omega : 2 < 2 ^ w)])
  have he₁ : (s₁.arrs edges).take E.length = E := by simp [s₁, hf₀ edges hed, he]
  have hd₁ : s₁.arrs dst = [n, m] ++ List.replicate (E.length + (1 + P.length)) 0 := by
    simpa [s₁, Nat.add_assoc] using ha₀
  have hreg₁ (r : Reg) (hr : r ≠ 271) : s₁.regs r = s.regs r := by
    rw [State.setReg_regs_ne _ _ hr, hr₀]
  obtain ⟨s₂, t₂, hex₂, ht₂, hd₂, hpos₂, ha₂, hr₂⟩ :=
    appendArrToDstProg_exec edges dst 263 270 hed (by decide) [n, m] E rfl hew hw
      (rem_out := 1 + P.length) (by simp only [List.length_cons, List.length_nil]; omega)
      he₁ hd₁ (by rw [hreg₁ 263 (by decide), hel]) (by simp [s₁])
  have hk₂ : s₂.regs 262 = k := by
    rw [hr₂ 262 (by decide), hreg₁ 262 (by decide), hk]
  obtain ⟨s₃, hex₃, hd₃, hpos₃, hr₃, ha₃⟩ := gm02WriteTermIndexProg_exec
    (rest := P.length) dst 271 262 ([n, m] ++ E) s₂ hd₂ hpos₂ hk₂
      (by simp only [List.length_append, List.length_cons, List.length_nil]; omega) hkw
  have hp₃ : (s₃.arrs pairs).take P.length = P := by
    rw [ha₃ pairs hpd, ha₂ pairs hpd]
    simp [s₁, hf₀ pairs hpd, hp]
  have hpl₃ : s₃.regs 264 = P.length := by
    rw [hr₃ 264 (by decide), hr₂ 264 (by decide), hreg₁ 264 (by decide), hpl]
  obtain ⟨s₄, t₄, hex₄, ht₄, hd₄, _, ha₄, hr₄⟩ :=
    appendArrToDstProg_exec pairs dst 264 270 hpd (by decide) (([n, m] ++ E) ++ [k]) P
      rfl hpw hw (rem_out := 0)
      (by simp only [List.length_append, List.length_cons, List.length_nil]; omega)
      hp₃ (by simpa only [Nat.add_zero] using hd₃) hpl₃
      (by simpa only [List.length_append, List.length_singleton] using hpos₃)
  refine ⟨s₄, _, Exec.seq hex₀ (Exec.seq hex₁ (Exec.seq hex₂ (Exec.seq hex₃ hex₄))),
    ?_, ?_, ?_, ?_⟩
  · omega
  · simpa only [List.replicate_zero, List.append_nil] using hd₄
  · intro a ha
    rw [ha₄ a ha, ha₃ a ha, ha₂ a ha]
    exact hf₀ a ha
  · intro r hr
    dsimp only [Reg] at hr
    rw [hr₄ r (by try dsimp only [Reg]; omega), hr₃ r (by dsimp only [Reg]; omega), hr₂ r (by try dsimp only [Reg]; omega)]
    exact hreg₁ r (by dsimp only [Reg]; omega)

end GraphMinor.Compute
