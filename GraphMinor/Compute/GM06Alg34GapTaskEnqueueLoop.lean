module

public import GraphMinor.Compute.GM06Alg34GapTaskCandidate
import GraphMinor.Compute.GM06Alg34RowEnumeration

/-!
# Enqueuing canonical component tasks in source order

Scan consecutive source labels. Each canonical root contributes its
parent/root work record, and every nonroot contributes no words. The
recursive loop proof records the exact queue prefix and remaining
capacity while preserving the parent arrays and pending read cursor.
-/

@[expose] public section
namespace GraphMinor.Compute

/-- Scan the sources counted in 5006, beginning at source register 5001. -/
def gm06GapTaskEnqueueLoopProg : Cmd :=
  .while (.reg 5006) (.seq gm06GapTaskCandidateProg
    (.seq (.assign 5001 (.op .add (.reg 5001) (.const 1)))
      (.assign 5006 (.op .sub (.reg 5006) (.const 1)))))

/-- The source scan appends exactly the canonical component work records,
with linear scan overhead and linear copying cost for each emitted record. -/
theorem gm06GapTaskEnqueueLoopProg_exec {w i cap : ℕ} (x : GM06DrawingData)
    (R : List (Fin x.regions.length)) (V : List (Fin x.n))
    (hw : 1 < 2 ^ w) (hsize : x.size + R.length + 3 < 2 ^ w)
    (hfit : i + V.length ≤ x.n) (hlabels : V.map Fin.val = List.range' i V.length)
    {pfx : List ℕ} {s : State} (hinput : s.arrs 0 = x.words) (hgap : s.arrs 47 = R.map Fin.val)
    (hmask : s.arrs 40 = gm06VertexRootMask x) (hsource : s.regs 5001 = i)
    (hleft : s.regs 5006 = V.length)
    (hend : pfx.length + (gm06GapTaskQueueWords x R V).length < 2 ^ w)
    (hbuf : IsPrefixBuffer 42 pfx ((gm06GapTaskQueueWords x R V).length + cap) s)
    (hpos : s.regs 7001 = pfx.length) :
    ∃ s' t, Exec w gm06GapTaskEnqueueLoopProg s s' t ∧
      t ≤ (20 * (x.size + R.length + 4) + 11) * V.length + 1 ∧
      IsPrefixBuffer 42 (pfx ++ gm06GapTaskQueueWords x R V) cap s' ∧
      s'.regs 7001 = (pfx ++ gm06GapTaskQueueWords x R V).length ∧
      s'.regs 5001 = i + V.length ∧ s'.regs 5006 = 0 ∧
      (∀ A : ℕ, A ≠ 42 → s'.arrs A = s.arrs A) ∧
      (∀ q < 7500, q ≠ 5001 → q ≠ 5006 → q ≠ 7001 → q ≠ 7400 → s'.regs q = s.regs q) := by
  have hn : x.n < 2 ^ w := x.counts_le_size.1.trans_lt (by omega : x.size < 2 ^ w)
  induction V generalizing i s pfx with
  | nil =>
    have hz : s.regs 5006 = 0 := hleft
    have he : Exec w gm06GapTaskEnqueueLoopProg s s 1 :=
      .while_false (by simp [Expr.eval, checkWord, hz, Nat.zero_lt_of_lt hw])
    refine ⟨s, 1, he, by simp, ?_, ?_, by simpa using hsource, hz,
      fun _ _ => rfl, fun _ _ _ _ _ _ => rfl⟩
    · simpa only [gm06GapTaskQueueWords, List.filter_nil, List.flatMap_nil,
        List.length_nil, Nat.zero_add, List.append_nil] using hbuf
    · simpa only [gm06GapTaskQueueWords, List.filter_nil, List.flatMap_nil, List.append_nil] using hpos
  | cons a V ih =>
    have hcons := List.cons.inj (by
      simpa only [List.map_cons, List.length_cons, List.range'_succ] using hlabels)
    have haval : a.val = i := hcons.1
    have htail : V.map Fin.val = List.range' (i + 1) V.length := hcons.2
    let recWords := if x.isComponentRoot a then (⟨x, R, a⟩ : GM06GapComponentTask).words else []
    have hrec : gm06GapTaskQueueWords x R (a :: V) = recWords ++ gm06GapTaskQueueWords x R V :=
      gm06GapTaskQueueWords_cons x R a V
    have hrecLen := congrArg List.length hrec
    simp only [List.length_append] at hrecLen
    have hiw : i < 2 ^ w := haval ▸ a.isLt.trans hn
    have hi1w : i + 1 < 2 ^ w := (by simp only [List.length_cons] at hfit; omega : i + 1 ≤ x.n).trans_lt hn
    have hremw : V.length + 1 < 2 ^ w := (by simp only [List.length_cons] at hfit; omega : V.length + 1 ≤ x.n).trans_lt hn
    obtain ⟨s₁, t₁, he₁, ht₁, hb₁, hp₁, ha₁, hg₁⟩ :=
      gm06GapTaskCandidateProg_exec x R a (cap := (gm06GapTaskQueueWords x R V).length + cap)
        hw hsize hinput hgap hmask (haval.symm ▸ hsource) (by change pfx.length + recWords.length < 2 ^ w; omega)
        (by simpa only [hrecLen, Nat.add_assoc] using hbuf) hpos
    have hsource₁ : s₁.regs 5001 = i :=
      (hg₁ 5001 (by decide) (by decide) (by decide)).trans hsource
    let s₂ := s₁.setReg 5001 (i + 1)
    have he₂ : Exec w (.assign 5001 (.op .add (.reg 5001) (.const 1))) s₁ s₂ 4 :=
      .assign (by simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hsource₁, hiw, hi1w, hw])
    have hleft₂ : s₂.regs 5006 = V.length + 1 :=
      (hg₁ 5006 (by decide) (by decide) (by decide)).trans hleft
    let s₃ := s₂.setReg 5006 V.length
    have he₃ : Exec w (.assign 5006 (.op .sub (.reg 5006) (.const 1))) s₂ s₃ 4 :=
      .assign (by simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hleft₂, hremw, hw,
        show V.length < 2 ^ w by omega])
    obtain ⟨s₄, t₄, he₄, ht₄, hb₄, hp₄, hi₄, hz₄, ha₄, hg₄⟩ :=
      ih (i := i + 1) (pfx := pfx ++ recWords) (s := s₃)
        (by simp only [List.length_cons] at hfit; omega) htail
        ((ha₁ 0 (by decide)).trans hinput) ((ha₁ 47 (by decide)).trans hgap)
        ((ha₁ 40 (by decide)).trans hmask) (by simp [s₃, s₂]) (by simp [s₃])
        (by simp only [List.length_append]; omega) hb₁
        (by simpa [s₃, s₂] using hp₁)
    have hcond : (Expr.reg 5006).eval w s = some (V.length + 1) := by
      simp [Expr.eval, checkWord, hleft, hremw]
    refine ⟨s₄, 1 + (t₁ + (4 + 4)) + t₄,
      .while_true hcond (by omega) (.seq he₁ (.seq he₂ he₃)) he₄, ?_, ?_, ?_, ?_, hz₄, ?_, ?_⟩
    · have hbound : t₁ ≤ 20 * (x.size + R.length + 4) + 2 := ht₁
      have hbound₄ : t₄ ≤ (20 * (x.size + R.length + 4) + 11) * V.length + 1 := ht₄
      change _ ≤ (20 * (x.size + R.length + 4) + 11) * (V.length + 1) + 1
      rw [Nat.mul_add, Nat.mul_one]
      omega
    · simpa only [hrec, List.append_assoc] using hb₄
    · simpa only [hrec, List.append_assoc] using hp₄
    · simpa only [List.length_cons, Nat.add_assoc, Nat.add_comm 1] using hi₄
    · intro A hA
      exact (ha₄ A hA).trans (ha₁ A hA)
    · intro q hq h5001 h5006 h7001 h7400
      exact (hg₄ q hq h5001 h5006 h7001 h7400).trans
        (by simp only [s₃, s₂, State.setReg, Function.update_of_ne h5006,
          Function.update_of_ne h5001]; exact hg₁ q hq h7001 h7400)

end GraphMinor.Compute
