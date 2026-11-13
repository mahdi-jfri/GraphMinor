module

public import GraphMinor.Compute.GM06Alg34EmitBranch
public import GraphMinor.Compute.GM06Alg34VertexRootMaskLoop

/-!
# Emitting a branch exactly at a canonical component root

Read the saved root flag at the outer source label. A set flag builds
and emits that component input. An unset flag emits no words. The saved
parent and root mask survive both paths, so scanning all labels emits
each component exactly once in canonical order.
-/

@[expose] public section
namespace GraphMinor.Compute

/-- The record emitted by one scanned source, empty when it is not a root. -/
def gm06SelectedComponentRecordWords (x : GM06DrawingData) (a : Fin x.n) : List ℕ :=
  if x.isComponentRoot a then gm06ComponentRecordWords x a else []

/-- Emit a component branch exactly when its saved canonical root flag is set. -/
def gm06BranchCandidateProg : Cmd :=
  .ite (.read 40 (.reg 5001)) gm06EmitBranchProg .skip

/-- The saved root test emits exactly its selected record, with cubic
time and preservation of the parent state for later source labels. -/
theorem gm06BranchCandidateProg_exec (x : GM06DrawingData) (a : Fin x.n)
    {c cap : ℕ} (hc : 3 ≤ c) {pfx : List ℕ} {s : State}
    (hsaved : s.arrs 41 = x.words) (hlen : s.regs 5003 = x.words.length)
    (hsource : s.regs 5001 = a.val) (hmask : s.arrs 40 = gm06VertexRootMask x)
    (hend : pfx.length + (gm06SelectedComponentRecordWords x a).length < 2 ^ wordSize c x.size)
    (hbuf : IsPrefixBuffer 42 pfx ((gm06SelectedComponentRecordWords x a).length + cap) s)
    (hpos : s.regs 5002 = pfx.length) :
    ∃ s' t, Exec (wordSize c x.size) gm06BranchCandidateProg s s' t ∧
      t ≤ 1300 * (x.size + 2) ^ 3 + 2 ∧
      IsPrefixBuffer 42 (pfx ++ gm06SelectedComponentRecordWords x a) cap s' ∧
      s'.regs 5002 = (pfx ++ gm06SelectedComponentRecordWords x a).length ∧
      (∀ A : ℕ, 40 ≤ A → A ≠ 42 → s'.arrs A = s.arrs A) ∧
      (∀ q : ℕ, 5000 ≤ q → q < 5100 → q ≠ 5002 → q ≠ 5004 → s'.regs q = s.regs q) := by
  have hc1 : 1 ≤ c := by omega
  have hsize : x.size < 2 ^ wordSize c x.size := lt_two_pow_wordSize_of_le hc1 (Nat.le_succ _)
  have hn := x.counts_le_size.1.trans_lt hsize
  have hw : 1 < 2 ^ wordSize c x.size := by
    have hh := x.five_le_words_length
    have hh' := x.words_length_le_size
    omega
  have hl : a.val < (s.arrs 40).length := by rw [hmask]; simp only [gm06VertexRootMask, List.length_ofFn]; exact a.isLt
  have hg : (s.arrs 40)[a.val]'hl = if x.isComponentRoot a then 1 else 0 := by
    simp only [hmask, gm06VertexRootMask, List.getElem_ofFn]
  have hpow := Nat.le_self_pow (by decide : 3 ≠ 0) (x.size + 2)
  cases ht : x.isComponentRoot a with
  | false =>
    have he : (Expr.read 40 (.reg 5001)).eval (wordSize c x.size) s = some 0 := by
      simp [Expr.eval, checkWord, hsource, a.isLt.trans hn, hl, hg, ht, Nat.zero_lt_of_lt hw]
    refine ⟨s, 3, .ite_false he (.skip s), by omega, ?_, ?_, fun _ _ _ => rfl,
      fun _ _ _ _ _ => rfl⟩
    · simpa only [gm06SelectedComponentRecordWords, ht, Bool.false_eq_true, ↓reduceIte,
        List.length_nil, Nat.zero_add, List.append_nil] using hbuf
    · simpa only [gm06SelectedComponentRecordWords, ht, Bool.false_eq_true, ↓reduceIte,
        List.append_nil] using hpos
  | true =>
    have he : (Expr.read 40 (.reg 5001)).eval (wordSize c x.size) s = some 1 := by
      simp [Expr.eval, checkWord, hsource, a.isLt.trans hn, hl, hg, ht, hw]
    obtain ⟨s', t, hex, ht', hb', hp', ha', hr'⟩ :=
      gm06EmitBranchProg_exec x a hc hsaved hlen hsource
        (by simpa only [gm06SelectedComponentRecordWords, ht, ↓reduceIte] using hend)
        (by simpa only [gm06SelectedComponentRecordWords, ht, ↓reduceIte] using hbuf) hpos
    exact ⟨s', 2 + t, .ite_true he (by decide) hex, by omega,
      by simpa only [gm06SelectedComponentRecordWords, ht, ↓reduceIte] using hb',
      by simpa only [gm06SelectedComponentRecordWords, ht, ↓reduceIte] using hp', ha', hr'⟩

end GraphMinor.Compute
