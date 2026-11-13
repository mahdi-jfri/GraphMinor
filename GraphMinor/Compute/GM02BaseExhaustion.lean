module

public import GraphMinor.Compute.GM02FiniteTrie
public import GraphMinor.Compute.GM02TerminatedEncoding

/-!
# Exhaustion in the bounded cases of II (3.2)

On page 316 the routines A1 and A2 proceed by exhaustion when the
vertex count is at most four times the fixed width. There are only
finitely many numbered simple terminated graphs at such sizes. A fixed
prefix tree reads their plain encodings and writes their feasibility
bits. Its leaves contain fixed answers, and its input contains only the
graph and terminal pairs.
-/

public section
namespace GraphMinor.Compute
open Classical GraphMinor.GM02

/-- Complete encodings in the fixed finite range of the base case. -/
def gm02BaseComplete (N : ℕ) (words : List ℕ) : Prop :=
  ∃ x : GM02SimpleTerminatedInput, x.n ≤ N ∧ x.enc = words

/-- The feasibility table for the fixed finite range. -/
noncomputable def gm02BaseAnswer (N : ℕ) (words : List ℕ) : ℕ :=
  if ∃ x : GM02SimpleTerminatedInput,
    x.n ≤ N ∧ x.enc = words ∧ x.A.Feasible (Graph.ofSimpleGraph x.G) then 1 else 0

/-- Completion is detected exactly at the end of a valid input. -/
theorem gm02BaseComplete_take (N : ℕ) (x : GM02SimpleTerminatedInput) (hn : x.n ≤ N)
    (m : ℕ) (hm : m ≤ x.enc.length) :
    gm02BaseComplete N (x.enc.take m) ↔ m = x.enc.length := by
  constructor
  · rintro ⟨y, _, hy⟩
    have hp : y.enc ++ x.enc.drop m = x.enc := by rw [hy, List.take_append_drop]
    have hd := gm02SimpleTerminatedEncoding_prefix_free y x (x.enc.drop m) hp
    have hl := congrArg List.length hp
    rw [hd, List.length_append, List.length_nil, Nat.add_zero, hy,
      List.length_take_of_le hm] at hl
    exact hl
  · intro he
    subst m
    exact ⟨x, hn, List.take_length.symm⟩

/-- Injectivity ensures that the table bit is precisely feasibility. -/
theorem gm02BaseAnswer_enc (N : ℕ) (x : GM02SimpleTerminatedInput) (hn : x.n ≤ N) :
    gm02BaseAnswer N x.enc = if x.A.Feasible (Graph.ofSimpleGraph x.G) then 1 else 0 := by
  have hi : (∃ y : GM02SimpleTerminatedInput,
      y.n ≤ N ∧ y.enc = x.enc ∧ y.A.Feasible (Graph.ofSimpleGraph y.G)) ↔
      x.A.Feasible (Graph.ofSimpleGraph x.G) := by
    constructor
    · rintro ⟨y, _, he, hf⟩
      have hy := gm02SimpleTerminatedEncoding_injective he
      subst y
      exact hf
    · intro hf
      exact ⟨x, hn, rfl, hf⟩
  simp only [gm02BaseAnswer, hi]

/-- The bounded exhaustion program for both internal routines. -/
noncomputable def gm02BaseExhaustionProg (N : ℕ) (arr : Arr) (r_out r_tmp : Reg) : Cmd :=
  gm02FiniteTrieProg arr r_out r_tmp (N * N + N) (gm02BaseComplete N)
    (gm02BaseAnswer N) (3 + 2 * (N * N) + N) []

/-- The bounded exhaustion program returns the correct feasibility bit in
constant time for fixed `N`, preserving every input array. -/
theorem gm02BaseExhaustionProg_exec {w N : ℕ} (arr : Arr) (r_out r_tmp : Reg)
    (x : GM02SimpleTerminatedInput) (hn : x.n ≤ N)
    (hw : 4 + 2 * (N * N) + N < 2 ^ w) (rest : List ℕ) (s : State)
    (harr : s.arrs arr = x.enc ++ rest) :
    ∃ s' t, Exec w (gm02BaseExhaustionProg N arr r_out r_tmp) s s' t ∧
      t ≤ (4 + 2 * (N * N) + N) * (4 * (N * N + N) + 10) ∧
      s'.regs r_out = (if x.A.Feasible (Graph.ofSimpleGraph x.G) then 1 else 0) ∧
      (∀ r, r ≠ r_out → r ≠ r_tmp → s'.regs r = s.regs r) ∧ s'.arrs = s.arrs := by
  have hl := x.enc_length_le hn
  have hf : ∀ pref, gm02BaseAnswer N pref < 2 ^ w := by
    intro pref
    unfold gm02BaseAnswer
    split_ifs <;> omega
  rcases gm02FiniteTrieProg_exec arr r_out r_tmp (N * N + N)
      (gm02BaseComplete N) (gm02BaseAnswer N) hf x.enc rest
      (gm02BaseComplete_take N x hn) (fun v hv => x.enc_word_le hn hv)
      (by omega) (by omega) (3 + 2 * (N * N) + N) 0
      (Nat.zero_le _) (by omega) (by omega) s harr with
    ⟨s', t, he, ht, hout, hr, ha⟩
  refine ⟨s', t, he, ?_, ?_, hr, ha⟩
  · have heq : 3 + 2 * (N * N) + N + 1 = 4 + 2 * (N * N) + N := by omega
    simpa only [heq] using ht
  · exact hout.trans (gm02BaseAnswer_enc N x hn)

end GraphMinor.Compute
