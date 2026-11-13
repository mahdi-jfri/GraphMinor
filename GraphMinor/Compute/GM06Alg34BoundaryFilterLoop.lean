module

public import GraphMinor.Compute.GM06Alg34BoundaryFilterData

/-!
# Scanning one new region boundary list

The loop visits consecutive old labels, queries their closure hits,
and emits selected new labels. Its proof follows the remaining label
list and records the exact consecutive buffer writes. The two cell
kinds share this scan, with their respective offsets and rank tables.
-/

@[expose] public section
namespace GraphMinor.Compute

/-- The finite boundary selector for labels in one packed cell-kind range. -/
def gm06BoundarySelection {n : ℕ} (x : GM06DrawingData) (vs : List (Fin x.n))
    (a : Fin x.cellCount) (shift : ℕ) (hfit : shift + n ≤ x.cellCount)
    (active : Fin n → Bool) (v : Fin n) : Bool :=
  active v && x.regionClosureHit vs a (x.cellNumbering.symm
    ⟨shift + v.val, (Nat.add_lt_add_left v.isLt shift).trans_le hfit⟩)

/-- Scan the consecutive labels counted by 209, starting at 207. -/
def gm06BoundaryFilterLoopProg (mask ranks : ℕ) : Cmd :=
  .while (.reg 209) (.seq (gm06BoundaryEntryProg mask ranks)
    (.seq (.assign 207 (.op .add (.reg 207) (.const 1)))
      (.assign 209 (.op .sub (.reg 209) (.const 1)))))

/-- The boundary scan computes exactly the finite selection writes,
with at most `18 * N + 38` steps per old label and the final test. -/
theorem gm06BoundaryFilterLoopProg_exec {w n k i shift : ℕ} (x : GM06DrawingData)
    (vs : List (Fin x.n)) (a : Fin x.cellCount) (mask ranks : ℕ)
    (active : Fin n → Bool) (labels : Fin n → ℕ) (L : List (Fin n))
    (hmask9 : mask ≠ 9) (hranks9 : ranks ≠ 9)
    (hw : 1 < 2 ^ w) (hN : x.cellCount < 2 ^ w)
    (hsquare : x.cellCount * x.cellCount < 2 ^ w) (hfit : shift + n ≤ x.cellCount)
    (hk : k + L.length < 2 ^ w) (hlabel : ∀ v, active v = true → labels v < 2 ^ w)
    (ha : x.activeCell vs (x.cellNumbering.symm a) = false)
    (hlabels : L.map Fin.val = List.range' i L.length) {s : State}
    (hmarks : s.arrs 33 = gm06ComplementReachData x vs a)
    (hmat : s.arrs 12 = gm06ClosureMatrixData x) (hc : s.regs 170 = x.cellCount)
    (hmask : s.arrs mask = List.ofFn (fun u : Fin n => if active u then 1 else 0))
    (hranks : s.arrs ranks = List.ofFn labels) (hv : s.regs 207 = i)
    (hshift : s.regs 208 = shift) (hcount : s.regs 142 = k)
    (hleft : s.regs 209 = L.length) (hcap : k + L.length ≤ (s.arrs 9).length) :
    let selected := gm06BoundarySelection x vs a shift hfit active
    ∃ s' t, Exec w (gm06BoundaryFilterLoopProg mask ranks) s s' t ∧
      t ≤ (18 * x.cellCount + 38) * L.length + 1 ∧
      s'.arrs 9 = gm06BoundaryWrites selected labels L k (s.arrs 9) ∧
      s'.regs 142 = k + (gm06BoundaryWords selected labels L).length ∧
      s'.regs 207 = i + L.length ∧ s'.regs 209 = 0 ∧
      (∀ j : ℕ, j ≠ 9 → s'.arrs j = s.arrs j) ∧
      (∀ q : ℕ, q ≠ 0 → q ≠ 105 → q ≠ 142 → q ≠ 204 → q ≠ 205 → q ≠ 206 →
        q ≠ 207 → q ≠ 209 → s'.regs q = s.regs q) := by
  let selected := gm06BoundarySelection x vs a shift hfit active
  change ∃ (s' : State) (t : ℕ), _ ∧ _ ∧ s'.arrs 9 = gm06BoundaryWrites selected labels L k (s.arrs 9) ∧ _
  induction L generalizing i k s with
  | nil =>
    have htest : (Expr.reg 209).eval w s = some 0 := by
      simp [Expr.eval, checkWord, hleft, Nat.zero_lt_of_lt hw]
    refine ⟨s, 1, Exec.while_false htest, by simp, rfl, ?_, ?_, hleft,
      fun _ _ => rfl, fun _ _ _ _ _ _ _ _ _ => rfl⟩
    · simpa only [gm06BoundaryWords, List.filter_nil, List.map_nil, List.length_nil, Nat.add_zero] using hcount
    · simpa using hv
  | cons v L ih =>
    have hcons := List.cons.inj (by
      simpa only [List.map_cons, List.length_cons, List.range'_succ] using hlabels)
    have hvval : v.val = i := hcons.1
    have htail : L.map Fin.val = List.range' (i + 1) L.length := hcons.2
    have hn : n < 2 ^ w := (by omega : n ≤ x.cellCount).trans_lt hN
    have hiw : i < 2 ^ w := by rw [← hvval]; exact v.isLt.trans hn
    have hi1w : i + 1 < 2 ^ w := (by omega : i + 1 ≤ n).trans_lt hn
    have hkw : k + 1 < 2 ^ w := by simp only [List.length_cons] at hk; omega
    have hLw : L.length < 2 ^ w := by simp only [List.length_cons] at hk; omega
    have hL1w : L.length + 1 < 2 ^ w := by simp only [List.length_cons] at hk; omega
    obtain ⟨s₁, t₁, hex₁, ht₁, hbuf₁, hcount₁, harr₁, hreg₁⟩ :=
      gm06BoundaryEntryProg_exec x vs a mask ranks active labels v hw hN hsquare hfit hkw
        (hlabel v) ha hmarks hmat hc hmask hranks (hv.trans hvval.symm) hshift hcount
        (by simp only [List.length_cons] at hcap; omega)
    have hbuf : s₁.arrs 9 = if selected v then (s.arrs 9).set k (labels v) else s.arrs 9 := hbuf₁
    have hcount₁' : s₁.regs 142 = k + (if selected v then 1 else 0) := hcount₁
    have hlen₁ : (s₁.arrs 9).length = (s.arrs 9).length := by
      rw [hbuf]; split <;> simp only [List.length_set]
    have hindex₁ : s₁.regs 207 = i := (hreg₁ _ (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide)).trans hv
    have hleft₁ : s₁.regs 209 = L.length + 1 :=
      (hreg₁ _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hleft
    let s₂ := s₁.setReg 207 (i + 1)
    let s₃ := s₂.setReg 209 L.length
    have hex₂ : Exec w (.assign 207 (.op .add (.reg 207) (.const 1))) s₁ s₂ 4 :=
      .assign (by simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hindex₁, hiw, hi1w, hw])
    have hex₃ : Exec w (.assign 209 (.op .sub (.reg 209) (.const 1))) s₂ s₃ 4 :=
      .assign (by simp [s₂, Expr.eval, BinOp.eval, BinOp.raw, checkWord, hleft₁, hL1w, hLw, hw])
    have hreg₃ : ∀ q : ℕ, q ≠ 207 → q ≠ 209 → s₃.regs q = s₁.regs q := by
      intro q hq₁ hq₂; simp [s₃, s₂, State.setReg, hq₁, hq₂]
    have hk' : k + (if selected v then 1 else 0) + L.length < 2 ^ w := by
      simp only [List.length_cons] at hk
      split <;> omega
    have hcap' : k + (if selected v then 1 else 0) + L.length ≤ (s₃.arrs 9).length := by
      change _ ≤ (s₁.arrs 9).length
      rw [hlen₁]
      simp only [List.length_cons] at hcap
      split <;> omega
    obtain ⟨s₄, t₄, hex₄, ht₄, hbuf₄, hcount₄, hindex₄, hleft₄, harr₄, hreg₄⟩ :=
      ih (i := i + 1) (k := k + (if selected v then 1 else 0)) (s := s₃) hk' htail
        ((harr₁ _ (by decide)).trans hmarks) ((harr₁ _ (by decide)).trans hmat)
        ((hreg₃ _ (by decide) (by decide)).trans
          ((hreg₁ _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hc))
        ((harr₁ mask hmask9).trans hmask) ((harr₁ ranks hranks9).trans hranks)
        (by simp [s₃, s₂])
        ((hreg₃ _ (by decide) (by decide)).trans
          ((hreg₁ _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hshift))
        ((hreg₃ _ (by decide) (by decide)).trans hcount₁') (by simp [s₃]) hcap'
    have htest : (Expr.reg 209).eval w s = some (L.length + 1) := by
      simp [Expr.eval, checkWord, hleft, hL1w]
    refine ⟨s₄, 1 + (t₁ + (4 + 4)) + t₄,
      Exec.while_true htest (by omega) (Exec.seq hex₁ (Exec.seq hex₂ hex₃)) hex₄,
      ?_, ?_, ?_, ?_, hleft₄, ?_, ?_⟩
    · simp only [List.length_cons, Nat.mul_add, Nat.mul_one] at ⊢
      omega
    · simpa only [gm06BoundaryWrites, ← hbuf, s₃, s₂, State.setReg] using hbuf₄
    · cases hs : selected v <;> simp only [selected] at hs <;>
        simpa [gm06BoundaryWords, List.filter_cons, selected, hs, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hcount₄
    · simpa only [List.length_cons, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hindex₄
    · intro j hj; exact (harr₄ j hj).trans (harr₁ j hj)
    · intro q hq₁ hq₂ hq₃ hq₄ hq₅ hq₆ hq₇ hq₈
      exact (hreg₄ q hq₁ hq₂ hq₃ hq₄ hq₅ hq₆ hq₇ hq₈).trans
        ((hreg₃ q hq₇ hq₈).trans (hreg₁ q hq₁ hq₂ hq₃ hq₄ hq₅ hq₆))

end GraphMinor.Compute
