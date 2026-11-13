module

public import GraphMinor.Compute.GM02TerminalPrefix
public import GraphMinor.Compute.BitSet
import GraphMinor.Compute.Algorithm94Init
import GraphMinor.Compute.CrossingOpsBasic

/-!
# Finalizing the terminal encoding suffix

Fill the active pair-count header and copy the used terminal words.
The result is the count followed by precisely the canonical terminal
pair words. Unused buffer capacity is excluded from the output suffix.
-/

public section
namespace GraphMinor.Compute
open GraphMinor.Compute.Crossing

/-- Fill the terminal count header and copy the used suffix into array 27. -/
@[expose] def gm02FinalizeTerminalBufferProg : Cmd :=
  .seq (.write 26 (.const 0) (.reg 76)) (readSliceProg 26 (.const 0) 27 (.reg 75) 80)

/-- Terminal finalization returns exactly the active pair-count and endpoint words in linear time. -/
theorem gm02FinalizeTerminalBufferProg_exec {w K : ℕ} (x : GM02TopologicalInput) (hflags : List ℕ)
    (hK : x.edges.length ≤ K) (s : State)
    (hbuf : s.arrs 26 = gm02TerminalBuffer x hflags K hK x.edges.length)
    (hpos : s.regs 75 = 1 + 2 * (gm02ActiveTerminalList x hflags K hK).length)
    (hcount : s.regs 76 = (gm02ActiveTerminalList x hflags K hK).length)
    (hw : 1 < 2 ^ w) (hN : gm02FullPortSize x K < 2 ^ w)
    (hcap : 1 + 2 * x.edges.length < 2 ^ w) :
    ∃ s' t, Exec w gm02FinalizeTerminalBufferProg s s' t ∧ t ≤ 28 + 32 * x.edges.length ∧
      s'.arrs 27 = [(gm02ActiveTerminalList x hflags K hK).length] ++
        flatEdges (gm02ActiveTerminalList x hflags K hK) ∧
      (∀ a, a ≠ 26 → a ≠ 27 → s'.arrs a = s.arrs a) ∧
      (∀ r, r < 80 ∨ 82 < r → s'.regs r = s.regs r) := by
  let L := gm02ActiveTerminalList x hflags K hK
  let rest := List.replicate (2 * (x.edges.length - L.length)) 0
  let words := [L.length] ++ flatEdges L
  have hL : L.length ≤ x.edges.length := by
    simpa only [gm02TerminalPrefix_full] using gm02TerminalPrefix_length_le x hflags K hK x.edges.length
  have hcntw : L.length < 2 ^ w := by omega
  have hwordsw : 1 + 2 * L.length < 2 ^ w := by omega
  let s₀ := s.writeArr 26 0 L.length
  have hbound : 0 < (s.arrs 26).length := by
    rw [hbuf]
    simp only [gm02TerminalBuffer, gm02TerminalWords, List.length_append, List.length_cons,
      List.length_nil, List.length_replicate, length_flatEdges]
    omega
  have he₀ : Exec w (.write 26 (.const 0) (.reg 76)) s s₀ 3 :=
    .write (eval_const (by omega)) (eval_reg hcount hcntw) hbound
  have hafter : s₀.arrs 26 = words ++ rest := by
    rw [show s₀.arrs 26 = (s.arrs 26).set 0 L.length from State.writeArr_arrs_self .., hbuf]
    simp only [gm02TerminalBuffer, gm02TerminalWords, gm02TerminalPrefix_full,
      List.cons_append, List.nil_append, List.set_cons_zero]
    rfl
  have hall : ∀ a ∈ words, a < 2 ^ w := by
    intro a ha
    change a ∈ [L.length] ++ flatEdges L at ha
    rcases List.mem_append.1 ha with ha | ha
    · have heq : a = L.length := List.mem_singleton.1 ha
      exact heq ▸ hcntw
    · exact all_lt_flatEdges L hN a ha
  have hwordlen : words.length = 1 + 2 * L.length := by
    simp only [words, List.length_append, List.length_cons, List.length_nil, length_flatEdges]
  obtain ⟨s₁, t₁, he₁, ht₁, hout, ha₁, hr₁⟩ := readSliceProg_exec_full 26 27 (.const 0) 75 80
    (by decide) (by decide) [] words rest rfl rfl hall hw
    (by simpa only [List.length_nil, Nat.zero_add, hwordlen] using hwordsw)
    (s := s₀) (eval_const (by omega)) (by simpa only [List.nil_append] using hafter)
    (by simpa only [s₀, State.writeArr_regs, hwordlen] using hpos)
  refine ⟨s₁, 3 + t₁, .seq he₀ he₁, ?_, hout, ?_, hr₁⟩
  · simp only [Expr.cost_const, hwordlen] at ht₁
    omega
  · intro a ha26 ha27
    exact (ha₁ a ha27).trans (State.writeArr_arrs_ne s 0 L.length ha26)

end GraphMinor.Compute
