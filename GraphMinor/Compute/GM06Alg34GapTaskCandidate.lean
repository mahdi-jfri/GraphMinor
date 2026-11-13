module

public import GraphMinor.Compute.GM06Alg34GapTaskAppend
public import GraphMinor.Compute.GM06Alg34GapTaskQueueData
public import GraphMinor.Compute.GM06Alg34VertexRootMaskLoop

/-!
# Emitting only canonical component work records

Read the completed component-root mask at the current source. Append
the full parent/root record precisely when the root flag is set.
Nonroots leave the queue unchanged. The source arrays and mask remain
fixed throughout the scan.
-/

@[expose] public section
namespace GraphMinor.Compute

/-- Emit the current source's component task exactly when its canonical root bit is set. -/
def gm06GapTaskCandidateProg : Cmd :=
  .ite (.read 40 (.reg 5001)) gm06GapTaskAppendProg .skip

/-- One source contributes exactly its canonical component record, or
no words, while preserving the parent arrays and unrelated counters. -/
theorem gm06GapTaskCandidateProg_exec {w cap : ℕ} (x : GM06DrawingData)
    (R : List (Fin x.regions.length)) (a : Fin x.n) {pfx : List ℕ}
    (hw : 1 < 2 ^ w) (hsize : x.size + R.length + 3 < 2 ^ w)
    {s : State} (hinput : s.arrs 0 = x.words) (hgap : s.arrs 47 = R.map Fin.val)
    (hmask : s.arrs 40 = gm06VertexRootMask x) (hsource : s.regs 5001 = a.val)
    (hend : pfx.length + (if x.isComponentRoot a then
      (⟨x, R, a⟩ : GM06GapComponentTask).words else []).length < 2 ^ w)
    (hbuf : IsPrefixBuffer 42 pfx ((if x.isComponentRoot a then
      (⟨x, R, a⟩ : GM06GapComponentTask).words else []).length + cap) s)
    (hpos : s.regs 7001 = pfx.length) :
    ∃ s' t, Exec w gm06GapTaskCandidateProg s s' t ∧
      t ≤ 20 * (x.size + R.length + 4) + 2 ∧
      IsPrefixBuffer 42 (pfx ++ if x.isComponentRoot a then
        (⟨x, R, a⟩ : GM06GapComponentTask).words else []) cap s' ∧
      s'.regs 7001 = (pfx ++ if x.isComponentRoot a then
        (⟨x, R, a⟩ : GM06GapComponentTask).words else []).length ∧
      (∀ A : ℕ, A ≠ 42 → s'.arrs A = s.arrs A) ∧
      (∀ q < 7500, q ≠ 7001 → q ≠ 7400 → s'.regs q = s.regs q) := by
  have hn : x.n < 2 ^ w := x.counts_le_size.1.trans_lt (by omega : x.size < 2 ^ w)
  have hmlen : a.val < (s.arrs 40).length := by simp [hmask, gm06VertexRootMask, a.isLt]
  have hmget : (s.arrs 40)[a.val]'hmlen = (if x.isComponentRoot a then 1 else 0) := by
    simp only [hmask, gm06VertexRootMask, List.getElem_ofFn]
  have htest : (Expr.read 40 (.reg 5001)).eval w s = some (if x.isComponentRoot a then 1 else 0) := by
    cases hp : x.isComponentRoot a <;>
      simp [Expr.eval, checkWord, hsource, a.isLt.trans hn, hmlen, hmget, hp, hw,
        Nat.zero_lt_of_lt hw]
  cases hp : x.isComponentRoot a with
  | false =>
    have ht0 : (Expr.read 40 (.reg 5001)).eval w s = some 0 := by
      simpa only [hp, Bool.false_eq_true, ↓reduceIte] using htest
    refine ⟨s, 3, .ite_false ht0 (.skip s), by omega, ?_, ?_, fun _ _ => rfl, fun _ _ _ _ => rfl⟩
    · simpa only [hp, Bool.false_eq_true, ↓reduceIte, List.append_nil, List.length_nil, Nat.zero_add] using hbuf
    · simpa only [hp, Bool.false_eq_true, ↓reduceIte, List.append_nil] using hpos
  | true =>
    have ht1 : (Expr.read 40 (.reg 5001)).eval w s = some 1 := by
      simpa only [hp, ↓reduceIte] using htest
    obtain ⟨s', t, he, ht, hb, hpos', harr, hreg⟩ :=
      gm06GapTaskAppendProg_exec (⟨x, R, a⟩ : GM06GapComponentTask) hw
        (by simpa only [gm06GapTask_size] using hsize)
        (by simpa only [hp, ↓reduceIte] using hend) hinput hgap hsource
        (by simpa only [hp, ↓reduceIte] using hbuf) hpos
    refine ⟨s', 2 + t, .ite_true ht1 (by decide) he, ?_, ?_, ?_, harr, hreg⟩
    · rw [gm06GapTask_size] at ht
      omega
    · simpa only [hp, ↓reduceIte] using hb
    · simpa only [hp, ↓reduceIte] using hpos'

end GraphMinor.Compute
