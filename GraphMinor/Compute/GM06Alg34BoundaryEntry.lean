module

public import GraphMinor.Compute.GM06Alg34BoundaryEmit

/-!
# Querying and emitting one boundary label

Add the fixed cell-kind offset to the current old label, query the
component closure, and emit the new rank when the label also survives.
The offset is zero for vertices and the original vertex count for
edges. This common step uses the supplied mask and rank tables.
-/

@[expose] public section
namespace GraphMinor.Compute

/-- Query the packed boundary label `208 + 207` and emit its rank. -/
def gm06BoundaryEntryProg (mask ranks : ℕ) : Cmd :=
  .seq (.assign 205 (.op .add (.reg 208) (.reg 207)))
    (.seq gm06BoundaryHitQueryProg (gm06BoundaryEmitProg mask ranks))

/-- The combined query and emission step writes exactly the surviving
closure-hit label in at most `18 * N + 29` steps. -/
theorem gm06BoundaryEntryProg_exec {w n k shift : ℕ} (x : GM06DrawingData)
    (vs : List (Fin x.n)) (a : Fin x.cellCount) (mask ranks : ℕ)
    (active : Fin n → Bool) (labels : Fin n → ℕ) (v : Fin n)
    (hw : 1 < 2 ^ w) (hN : x.cellCount < 2 ^ w)
    (hsquare : x.cellCount * x.cellCount < 2 ^ w) (hfit : shift + n ≤ x.cellCount)
    (hk : k + 1 < 2 ^ w) (hlabel : active v = true → labels v < 2 ^ w)
    (ha : x.activeCell vs (x.cellNumbering.symm a) = false) {s : State}
    (hmarks : s.arrs 33 = gm06ComplementReachData x vs a)
    (hmat : s.arrs 12 = gm06ClosureMatrixData x) (hc : s.regs 170 = x.cellCount)
    (hmask : s.arrs mask = List.ofFn (fun u : Fin n => if active u then 1 else 0))
    (hranks : s.arrs ranks = List.ofFn labels) (hv : s.regs 207 = v.val)
    (hshift : s.regs 208 = shift) (hcount : s.regs 142 = k) (hcap : k < (s.arrs 9).length) :
    let b : Fin x.cellCount := ⟨shift + v.val, (Nat.add_lt_add_left v.isLt shift).trans_le hfit⟩
    let selected := active v && x.regionClosureHit vs a (x.cellNumbering.symm b)
    ∃ s' t, Exec w (gm06BoundaryEntryProg mask ranks) s s' t ∧ t ≤ 18 * x.cellCount + 29 ∧
      s'.arrs 9 = (if selected then (s.arrs 9).set k (labels v) else s.arrs 9) ∧
      s'.regs 142 = k + (if selected then 1 else 0) ∧
      (∀ j : ℕ, j ≠ 9 → s'.arrs j = s.arrs j) ∧
      (∀ q : ℕ, q ≠ 0 → q ≠ 105 → q ≠ 142 → q ≠ 204 → q ≠ 205 → q ≠ 206 →
        s'.regs q = s.regs q) := by
  dsimp only
  let b : Fin x.cellCount := ⟨shift + v.val, (Nat.add_lt_add_left v.isLt shift).trans_le hfit⟩
  have hn : n < 2 ^ w := (by omega : n ≤ x.cellCount).trans_lt hN
  have haddrw := b.isLt.trans hN
  have hshiftw : shift < 2 ^ w := (Nat.le_add_right _ _).trans_lt haddrw
  let s₁ := s.setReg 205 b.val
  have hex₁ : Exec w (.assign 205 (.op .add (.reg 208) (.reg 207))) s s₁ 4 :=
    .assign (by simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hshift, hv,
      hshiftw, v.isLt.trans hn, haddrw, b])
  obtain ⟨s₂, t₂, hex₂, ht₂, hhit, harr₂, hreg₂⟩ :=
    gm06BoundaryHitQueryProg_exec x vs a b hw hN hsquare ha (s := s₁) hmarks hmat
      (by simpa [s₁] using hc) (by simp [s₁])
  have hv₂ : s₂.regs 207 = v.val := (hreg₂ _ (by decide) (by decide)
    (by decide) (by decide)).trans (by simpa [s₁] using hv)
  have hk₂ : s₂.regs 142 = k := (hreg₂ _ (by decide) (by decide)
    (by decide) (by decide)).trans (by simpa [s₁] using hcount)
  obtain ⟨s₃, t₃, hex₃, ht₃, hbuf, htotal, harr₃, hreg₃⟩ :=
    gm06BoundaryEmitProg_exec mask ranks active labels v
      (x.regionClosureHit vs a (x.cellNumbering.symm b)) hw hn hk hlabel (s := s₂)
      ((harr₂ mask).trans hmask) ((harr₂ ranks).trans hranks) hv₂ hhit hk₂
      (by rw [harr₂]; exact hcap)
  refine ⟨s₃, 4 + (t₂ + t₃), Exec.seq hex₁ (Exec.seq hex₂ hex₃), by omega, ?_, htotal, ?_, ?_⟩
  · simpa only [harr₂, s₁, State.setReg, b] using hbuf
  · intro j hj
    exact (harr₃ j hj).trans (harr₂ j)
  · intro q hq₁ hq₂ hq₃ hq₄ hq₅ hq₆
    exact (hreg₃ q hq₃).trans ((hreg₂ q hq₁ hq₂ hq₄ hq₆).trans
      (by simp [s₁, hq₅]))

end GraphMinor.Compute
