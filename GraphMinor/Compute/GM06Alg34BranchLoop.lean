module

public import GraphMinor.Compute.GM06Alg34BranchCandidate

/-!
# Emitting every component branch in canonical order

Scan the supplied labels in order. The saved root bit selects each
component exactly once. At a root, restore the parent and emit its
computed component input. The queue invariant follows the finite list
of remaining sources and accounts for every output word.
-/

@[expose] public section
namespace GraphMinor.Compute

/-- The selected record at the head precedes the remaining component records. -/
theorem gm06ComponentQueueWords_cons (x : GM06DrawingData) (a : Fin x.n)
    (V : List (Fin x.n)) :
    gm06ComponentQueueWords x (a :: V) =
      gm06SelectedComponentRecordWords x a ++ gm06ComponentQueueWords x V := by
  cases hh : x.isComponentRoot a <;>
    simp only [gm06ComponentQueueWords, gm06SelectedComponentRecordWords, List.filter_cons,
      hh, Bool.false_eq_true, ↓reduceIte, List.flatMap_cons, List.nil_append]

/-- Emit branches for the consecutive sources counted in 5006, starting at 5001. -/
def gm06BranchLoopProg : Cmd :=
  .while (.reg 5006) (.seq gm06BranchCandidateProg
    (.seq (.assign 5001 (.op .add (.reg 5001) (.const 1)))
      (.assign 5006 (.op .sub (.reg 5006) (.const 1)))))

/-- The source scan emits exactly the canonical component records and
has a polynomial bound in the parent size times the number of sources. -/
theorem gm06BranchLoopProg_exec {i cap : ℕ} (x : GM06DrawingData)
    (V : List (Fin x.n)) {c : ℕ} (hc : 3 ≤ c)
    (hfit : i + V.length ≤ x.n) (hlabels : V.map Fin.val = List.range' i V.length)
    {pfx : List ℕ} {s : State} (hsaved : s.arrs 41 = x.words)
    (hlen : s.regs 5003 = x.words.length) (hmask : s.arrs 40 = gm06VertexRootMask x)
    (hsource : s.regs 5001 = i) (hleft : s.regs 5006 = V.length)
    (hend : pfx.length + (gm06ComponentQueueWords x V).length < 2 ^ wordSize c x.size)
    (hbuf : IsPrefixBuffer 42 pfx ((gm06ComponentQueueWords x V).length + cap) s)
    (hpos : s.regs 5002 = pfx.length) :
    ∃ s' t, Exec (wordSize c x.size) gm06BranchLoopProg s s' t ∧
      t ≤ (1300 * (x.size + 2) ^ 3 + 11) * V.length + 1 ∧
      IsPrefixBuffer 42 (pfx ++ gm06ComponentQueueWords x V) cap s' ∧
      s'.regs 5002 = (pfx ++ gm06ComponentQueueWords x V).length ∧
      s'.regs 5001 = i + V.length ∧ s'.regs 5006 = 0 ∧
      (∀ A : ℕ, 40 ≤ A → A ≠ 42 → s'.arrs A = s.arrs A) ∧
      (∀ q : ℕ, 5000 ≤ q → q < 5100 → q ≠ 5001 → q ≠ 5002 → q ≠ 5004 → q ≠ 5006 →
        s'.regs q = s.regs q) := by
  have hsize := lt_two_pow_wordSize_of_le (by omega : 1 ≤ c) (n := x.size) (Nat.le_succ _)
  have hn := x.counts_le_size.1.trans_lt hsize
  have hw : 1 < 2 ^ wordSize c x.size := by have hh := x.five_le_words_length; have hh' := x.words_length_le_size; omega
  induction V generalizing i s pfx with
  | nil =>
    have hz : s.regs 5006 = 0 := hleft
    refine ⟨s, 1, .while_false (by simp [Expr.eval, checkWord, hz, Nat.zero_lt_of_lt hw]),
      by simp, ?_, ?_, by simpa using hsource, hz, fun _ _ _ => rfl,
      fun _ _ _ _ _ _ _ => rfl⟩
    · simpa only [gm06ComponentQueueWords, List.filter_nil, List.flatMap_nil, List.append_nil,
        List.length_nil, Nat.zero_add] using hbuf
    · simpa only [gm06ComponentQueueWords, List.filter_nil, List.flatMap_nil, List.append_nil] using hpos
  | cons a V ih =>
    have hcons := List.cons.inj (by
      simpa only [List.map_cons, List.length_cons, List.range'_succ] using hlabels)
    have haval : a.val = i := hcons.1
    have htail : V.map Fin.val = List.range' (i + 1) V.length := hcons.2
    have hiw : i < 2 ^ wordSize c x.size := haval ▸ a.isLt.trans hn
    have hi1w : i + 1 < 2 ^ wordSize c x.size := (by simp only [List.length_cons] at hfit; omega : i + 1 ≤ x.n).trans_lt hn
    have hremw : V.length + 1 < 2 ^ wordSize c x.size := (by simp only [List.length_cons] at hfit; omega : V.length + 1 ≤ x.n).trans_lt hn
    have hrec := gm06ComponentQueueWords_cons x a V
    have hrecLen := congrArg List.length hrec
    simp only [List.length_append] at hrecLen
    obtain ⟨s₁, t₁, hex₁, ht₁, hb₁, hp₁, ha₁, hg₁⟩ :=
      gm06BranchCandidateProg_exec x a hc hsaved hlen (haval.symm ▸ hsource) hmask
        (by omega) (by simpa only [hrecLen, Nat.add_assoc] using hbuf) hpos
    have hsource₁ : s₁.regs 5001 = i :=
      (hg₁ 5001 (by decide) (by decide) (by decide) (by decide)).trans hsource
    let s₂ := s₁.setReg 5001 (i + 1)
    have hex₂ : Exec (wordSize c x.size) (.assign 5001 (.op .add (.reg 5001) (.const 1))) s₁ s₂ 4 :=
      .assign (by simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hsource₁, hiw, hi1w, hw])
    have hleft₂ : s₂.regs 5006 = V.length + 1 :=
      (hg₁ 5006 (by decide) (by decide) (by decide) (by decide)).trans hleft
    let s₃ := s₂.setReg 5006 V.length
    have hex₃ : Exec (wordSize c x.size) (.assign 5006 (.op .sub (.reg 5006) (.const 1))) s₂ s₃ 4 :=
      .assign (by simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hleft₂, hremw, hw,
        show V.length < 2 ^ wordSize c x.size by omega])
    obtain ⟨s₄, t₄, hex₄, ht₄, hb₄, hp₄, hi₄, hz₄, ha₄, hg₄⟩ :=
      ih (i := i + 1) (pfx := pfx ++ gm06SelectedComponentRecordWords x a)
        (s := s₃) (by simp only [List.length_cons] at hfit; omega) htail
        ((ha₁ 41 (by decide) (by decide)).trans hsaved)
        ((hg₁ 5003 (by decide) (by decide) (by decide) (by decide)).trans hlen)
        ((ha₁ 40 (by decide) (by decide)).trans hmask)
        (by simp [s₃, s₂]) (by simp [s₃])
        (by simp only [List.length_append]; omega) hb₁
        (by simpa [s₃, s₂] using hp₁)
    have hcond : (Expr.reg 5006).eval (wordSize c x.size) s = some (V.length + 1) := by
      simp [Expr.eval, checkWord, hleft, hremw]
    refine ⟨s₄, 1 + (t₁ + (4 + 4)) + t₄,
      .while_true hcond (Nat.succ_ne_zero _) (.seq hex₁ (.seq hex₂ hex₃)) hex₄, ?_, ?_, ?_, ?_, hz₄, ?_, ?_⟩
    · simp only [List.length_cons]
      rw [Nat.mul_succ]
      omega
    · simpa only [hrec, List.append_assoc] using hb₄
    · simpa only [hrec, List.append_assoc] using hp₄
    · simp only [List.length_cons]
      omega
    · intro A hA h42
      exact (ha₄ A hA h42).trans (ha₁ A hA h42)
    · intro q hq hq' h5001 h5002 h5004 h5006
      rw [hg₄ q hq hq' h5001 h5002 h5004 h5006]
      change (s₂.setReg 5006 V.length).regs q = _
      rw [State.setReg_regs_ne _ _ h5006, State.setReg_regs_ne _ _ h5001]
      exact hg₁ q hq hq' h5002 h5004

end GraphMinor.Compute
