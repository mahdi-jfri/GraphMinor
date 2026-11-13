module

public import GraphMinor.Compute.GM06Alg34RootRecordStep

/-!
# Scanning canonical roots into the new region section

Visit consecutive packed labels, emitting their root-selected records.
The proof follows the remaining finite label list. A size budget of one
old vertex-and-edge boundary record per remaining label bounds the
output cursor. The accumulated stream retains the canonical root order.
-/

@[expose] public section
namespace GraphMinor.Compute

/-- Emit root-selected records counted by 188, starting at label 187. -/
def gm06RegionOutputLoopProg : Cmd :=
  .while (.reg 188) (.seq gm06RootRecordStepProg
    (.seq (.assign 187 (.op .add (.reg 187) (.const 1)))
      (.assign 188 (.op .sub (.reg 188) (.const 1)))))

/-- The complete counted scan emits exactly the canonical records of
its remaining labels, with a polynomial RAM time bound. -/
theorem gm06RegionOutputLoopProg_exec {w cap i : ℕ} (x : GM06DrawingData)
    (vs : List (Fin x.n)) (L : List (Fin x.cellCount)) (pfx : List ℕ) (hw : 1 < 2 ^ w)
    (hN : x.cellCount < 2 ^ w) (hsquare : x.cellCount * x.cellCount < 2 ^ w)
    (hfit : i + L.length ≤ x.cellCount) (hlabels : L.map Fin.val = List.range' i L.length)
    (hout : pfx.length + (L.length + 1) * (2 + x.n + x.ends.length) < 2 ^ w) {s : State}
    (hrootMask : s.arrs 36 = gm06RootMask x vs)
    (hmat : s.arrs 12 = gm06ClosureMatrixData x) (hc : s.regs 170 = x.cellCount)
    (hvertexMask : s.arrs 4 = gm06VertexMask vs) (hvertexRanks : s.arrs 5 = gm06VertexRanks vs)
    (hedgeMask : s.arrs 6 = gm06EdgeMask x vs) (hedgeRanks : s.arrs 7 = gm06EdgeRanks x vs)
    (hsize : s.regs 4 = x.cellCount) (hsource : s.regs 187 = i) (hleft : s.regs 188 = L.length)
    (hn : s.regs 100 = x.n) (hm : s.regs 101 = x.ends.length)
    (hlists : IsAdjList (x.complementGraph vs) 30 31 32 (adjListOf (x.complementGraph vs)) s)
    (hlen : (s.arrs 32).length = x.cellCount * x.cellCount)
    (hbuf : IsPrefixBuffer 10 pfx ((L.flatMap (gm06RootRecordWords x vs)).length + cap) s)
    (hcursor : s.regs 143 = pfx.length) :
    ∃ s' t, Exec w gm06RegionOutputLoopProg s s' t ∧
      t ≤ (26 * (x.cellCount * x.cellCount) + 23 * x.cellCount +
        (18 * x.cellCount + 72) * (x.n + x.ends.length) + 99) * L.length + 1 ∧
      IsPrefixBuffer 10 (pfx ++ L.flatMap (gm06RootRecordWords x vs)) cap s' ∧
      s'.regs 143 = (pfx ++ L.flatMap (gm06RootRecordWords x vs)).length ∧
      s'.regs 187 = i + L.length ∧ s'.regs 188 = 0 ∧
      (∀ j : ℕ, j ≠ 9 → j ≠ 10 → j ≠ 11 → j ≠ 33 → j ≠ 34 → s'.arrs j = s.arrs j) ∧
      (∀ q : ℕ, (q < 190 ∨ q = 203) → q ≠ 0 → q ≠ 105 → q ≠ 142 → q ≠ 143 →
        q ≠ 187 → q ≠ 188 → s'.regs q = s.regs q) := by
  induction L generalizing i pfx s with
  | nil =>
    have htest : (Expr.reg 188).eval w s = some 0 := by
      simp [Expr.eval, checkWord, hleft, Nat.zero_lt_of_lt hw]
    refine ⟨s, 1, Exec.while_false htest, by simp, by simpa using hbuf,
      by simpa using hcursor, by simpa using hsource, hleft,
      fun _ _ _ _ _ _ => rfl, fun _ _ _ _ _ _ _ _ => rfl⟩
  | cons a L ih =>
    have hcons := List.cons.inj (by
      simpa only [List.map_cons, List.length_cons, List.range'_succ] using hlabels)
    have haval : a.val = i := hcons.1
    have htail : L.map Fin.val = List.range' (i + 1) L.length := hcons.2
    have hiw : i < 2 ^ w := by rw [← haval]; exact a.isLt.trans hN
    have hi1w : i + 1 < 2 ^ w := (by simp only [List.length_cons] at hfit; omega : i + 1 ≤ x.cellCount).trans_lt hN
    have hLw : L.length < 2 ^ w := (by simp only [List.length_cons] at hfit; omega : L.length ≤ x.cellCount).trans_lt hN
    have hL1w : L.length + 1 < 2 ^ w :=
      (by simp only [List.length_cons] at hfit; omega : L.length + 1 ≤ x.cellCount).trans_lt hN
    have hbudget : 2 + x.n + x.ends.length ≤ (L.length + 1 + 1) * (2 + x.n + x.ends.length) := by
      simpa only [Nat.one_mul] using Nat.mul_le_mul_right (2 + x.n + x.ends.length)
        (show 1 ≤ L.length + 1 + 1 by omega)
    have houtHead : pfx.length + 2 + x.n + x.ends.length < 2 ^ w := by
      simp only [List.length_cons] at hout
      omega
    have hbufHead : IsPrefixBuffer 10 pfx
        ((gm06RootRecordWords x vs a).length + ((L.flatMap (gm06RootRecordWords x vs)).length + cap)) s := by
      simpa only [List.flatMap_cons, List.length_append, Nat.add_assoc] using hbuf
    obtain ⟨s₁, t₁, hex₁, ht₁, hbuf₁, hcursor₁, harr₁, hreg₁⟩ :=
      gm06RootRecordStepProg_exec x vs a pfx hw hN hsquare houtHead hrootMask hmat hc
        hvertexMask hvertexRanks hedgeMask hedgeRanks hsize (hsource.trans haval.symm)
        hn hm hlists hlen hbufHead hcursor
    have hindex₁ : s₁.regs 187 = i := (hreg₁ _ (Or.inl (by decide))
      (by decide) (by decide) (by decide) (by decide)).trans hsource
    have hleft₁ : s₁.regs 188 = L.length + 1 := (hreg₁ _ (Or.inl (by decide))
      (by decide) (by decide) (by decide) (by decide)).trans hleft
    let s₂ := s₁.setReg 187 (i + 1)
    let s₃ := s₂.setReg 188 L.length
    have hex₂ : Exec w (.assign 187 (.op .add (.reg 187) (.const 1))) s₁ s₂ 4 :=
      .assign (by simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hindex₁, hiw, hi1w, hw])
    have hex₃ : Exec w (.assign 188 (.op .sub (.reg 188) (.const 1))) s₂ s₃ 4 :=
      .assign (by simp [s₂, Expr.eval, BinOp.eval, BinOp.raw, checkWord, hleft₁, hL1w, hLw, hw])
    have hreg₃ : ∀ q : ℕ, q ≠ 187 → q ≠ 188 → s₃.regs q = s₁.regs q := by
      intro q hq₁ hq₂; simp [s₃, s₂, State.setReg, hq₁, hq₂]
    have hreg : ∀ q : ℕ, q = 4 ∨ q = 100 ∨ q = 101 ∨ q = 170 → s₃.regs q = s.regs q := by
      intro q hq
      apply Eq.trans (hreg₃ q (by rcases hq with rfl | rfl | rfl | rfl <;> decide)
        (by rcases hq with rfl | rfl | rfl | rfl <;> decide))
      apply hreg₁ q <;> rcases hq with rfl | rfl | rfl | rfl <;> decide
    have houtTail : (pfx ++ gm06RootRecordWords x vs a).length +
        (L.length + 1) * (2 + x.n + x.ends.length) < 2 ^ w := by
      have hchunk := gm06RootRecordWords_length_le x vs a
      simp only [List.length_cons] at hout
      rw [show L.length + 1 + 1 = 1 + (L.length + 1) by omega, Nat.add_mul, Nat.one_mul] at hout
      simp only [List.length_append]
      omega
    have hlists₃ : IsAdjList (x.complementGraph vs) 30 31 32 (adjListOf (x.complementGraph vs)) s₃ :=
      hlists.of_arrs_eq (harr₁ _ (by decide) (by decide) (by decide) (by decide) (by decide))
        (harr₁ _ (by decide) (by decide) (by decide) (by decide) (by decide))
        (harr₁ _ (by decide) (by decide) (by decide) (by decide) (by decide))
    obtain ⟨s₄, t₄, hex₄, ht₄, hbuf₄, hcursor₄, hindex₄, hleft₄, harr₄, hreg₄⟩ :=
      ih (i := i + 1) (pfx := pfx ++ gm06RootRecordWords x vs a) (s := s₃)
        (by simp only [List.length_cons] at hfit; omega) htail houtTail
        ((harr₁ _ (by decide) (by decide) (by decide) (by decide) (by decide)).trans hrootMask)
        ((harr₁ _ (by decide) (by decide) (by decide) (by decide) (by decide)).trans hmat)
        ((hreg _ (Or.inr (Or.inr (Or.inr rfl)))).trans hc)
        ((harr₁ _ (by decide) (by decide) (by decide) (by decide) (by decide)).trans hvertexMask)
        ((harr₁ _ (by decide) (by decide) (by decide) (by decide) (by decide)).trans hvertexRanks)
        ((harr₁ _ (by decide) (by decide) (by decide) (by decide) (by decide)).trans hedgeMask)
        ((harr₁ _ (by decide) (by decide) (by decide) (by decide) (by decide)).trans hedgeRanks)
        ((hreg _ (Or.inl rfl)).trans hsize) (by simp [s₃, s₂]) (by simp [s₃])
        ((hreg _ (Or.inr (Or.inl rfl))).trans hn) ((hreg _ (Or.inr (Or.inr (Or.inl rfl)))).trans hm)
        hlists₃ (by
          change (s₁.arrs 32).length = _
          rw [harr₁ 32 (by decide) (by decide) (by decide) (by decide) (by decide)]
          exact hlen)
        hbuf₁ ((hreg₃ _ (by decide) (by decide)).trans hcursor₁)
    have htest : (Expr.reg 188).eval w s = some (L.length + 1) := by
      simp [Expr.eval, checkWord, hleft, hL1w]
    refine ⟨s₄, 1 + (t₁ + (4 + 4)) + t₄,
      Exec.while_true htest (by omega) (Exec.seq hex₁ (Exec.seq hex₂ hex₃)) hex₄,
      ?_, ?_, ?_, ?_, hleft₄, ?_, ?_⟩
    · simp only [List.length_cons]
      rw [Nat.mul_succ]
      omega
    · simpa only [List.flatMap_cons, List.append_assoc] using hbuf₄
    · simpa only [List.flatMap_cons, List.append_assoc] using hcursor₄
    · simpa only [List.length_cons, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hindex₄
    · intro j hj₁ hj₂ hj₃ hj₄ hj₅
      exact (harr₄ j hj₁ hj₂ hj₃ hj₄ hj₅).trans (harr₁ j hj₁ hj₂ hj₃ hj₄ hj₅)
    · intro q hq hq₁ hq₂ hq₃ hq₄ hq₅ hq₆
      exact (hreg₄ q hq hq₁ hq₂ hq₃ hq₄ hq₅ hq₆).trans
        ((hreg₃ q hq₅ hq₆).trans (hreg₁ q hq hq₁ hq₂ hq₃ hq₄))

end GraphMinor.Compute
