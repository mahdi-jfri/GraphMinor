module

public import GraphMinor.Compute.GM06Alg34BoundaryFilterLoop
import GraphMinor.Compute.GM06Alg34RowEnumeration

/-!
# Allocating and computing one relabelled boundary list

Allocate a buffer for every old label of the chosen cell kind, start
the label and output counters at zero, and run the boundary scan. The
live prefix is exactly the selected new-label list. The old cell-kind
count is read from a register and the packed offset from register 208.
-/

@[expose] public section
namespace GraphMinor.Compute

/-- Build a boundary-list buffer, reading its old label count from `count`. -/
def gm06BoundaryFilterProg (mask ranks count : ℕ) : Cmd :=
  .seq (.assign 209 (.reg count))
    (.seq (.alloc 9 (.reg 209))
      (.seq (.assign 207 (.const 0))
        (.seq (.assign 142 (.const 0)) (gm06BoundaryFilterLoopProg mask ranks))))

/-- The complete boundary-list filter returns exactly its selected new
labels as the live prefix of array 9, with a quadratic time bound. -/
theorem gm06BoundaryFilterProg_exec {w n shift : ℕ} (x : GM06DrawingData)
    (vs : List (Fin x.n)) (a : Fin x.cellCount) (mask ranks count : ℕ)
    (active : Fin n → Bool) (labels : Fin n → ℕ)
    (hmask9 : mask ≠ 9) (hranks9 : ranks ≠ 9)
    (hw : 1 < 2 ^ w) (hN : x.cellCount < 2 ^ w)
    (hsquare : x.cellCount * x.cellCount < 2 ^ w) (hfit : shift + n ≤ x.cellCount)
    (hlabel : ∀ v, active v = true → labels v < 2 ^ w)
    (ha : x.activeCell vs (x.cellNumbering.symm a) = false) {s : State}
    (hmarks : s.arrs 33 = gm06ComplementReachData x vs a)
    (hmat : s.arrs 12 = gm06ClosureMatrixData x) (hc : s.regs 170 = x.cellCount)
    (hmask : s.arrs mask = List.ofFn (fun u : Fin n => if active u then 1 else 0))
    (hranks : s.arrs ranks = List.ofFn labels) (hcount : s.regs count = n)
    (hshift : s.regs 208 = shift) :
    let words := gm06BoundaryWords (gm06BoundarySelection x vs a shift hfit active)
      labels (List.finRange n)
    ∃ s' t, Exec w (gm06BoundaryFilterProg mask ranks count) s s' t ∧
      t ≤ (18 * x.cellCount + 39) * n + 8 ∧
      (s'.arrs 9).take (s'.regs 142) = words ∧ s'.regs 142 = words.length ∧
      (s'.arrs 9).length = n ∧
      (∀ j : ℕ, j ≠ 9 → s'.arrs j = s.arrs j) ∧
      (∀ q : ℕ, q ≠ 0 → q ≠ 105 → q ≠ 142 → q ≠ 204 → q ≠ 205 → q ≠ 206 →
        q ≠ 207 → q ≠ 209 → s'.regs q = s.regs q) := by
  dsimp only
  have hn : n < 2 ^ w := (by omega : n ≤ x.cellCount).trans_lt hN
  let s₁ := s.setReg 209 n
  let s₂ := s₁.setArr 9 (List.replicate n 0)
  let s₃ := s₂.setReg 207 0
  let s₄ := s₃.setReg 142 0
  have hex₁ : Exec w (.assign 209 (.reg count)) s s₁ 2 :=
    .assign (by simp [Expr.eval, checkWord, hcount, hn])
  have hex₂ : Exec w (.alloc 9 (.reg 209)) s₁ s₂ (1 + n) :=
    .alloc (by simp [s₁, Expr.eval, checkWord, hn])
  have hex₃ : Exec w (.assign 207 (.const 0)) s₂ s₃ 2 :=
    .assign (by simp [Expr.eval, checkWord, Nat.zero_lt_of_lt hw])
  have hex₄ : Exec w (.assign 142 (.const 0)) s₃ s₄ 2 :=
    .assign (by simp [Expr.eval, checkWord, Nat.zero_lt_of_lt hw])
  obtain ⟨s₅, t, hex₅, ht, hbuf, htotal, _, _, harr, hreg⟩ :=
    gm06BoundaryFilterLoopProg_exec x vs a mask ranks active labels (List.finRange n)
      hmask9 hranks9 hw hN hsquare hfit (k := 0) (i := 0) (by simpa using hn) hlabel ha
      (by simpa only [List.length_finRange] using (gm06Range_eq_finRange n).symm)
      (s := s₄) (by simpa [s₄, s₃, s₂, s₁] using hmarks)
      (by simpa [s₄, s₃, s₂, s₁] using hmat) (by simpa [s₄, s₃, s₂, s₁] using hc)
      (by simpa [s₄, s₃, s₂, s₁, hmask9] using hmask)
      (by simpa [s₄, s₃, s₂, s₁, hranks9] using hranks) (by simp [s₄, s₃])
      (by simpa [s₄, s₃, s₂, s₁] using hshift) (by simp [s₄])
      (by simp [s₄, s₃, s₂, s₁]) (by simp [s₄, s₃, s₂])
  simp only [Nat.zero_add] at htotal
  refine ⟨s₅, 2 + ((1 + n) + (2 + (2 + t))),
    Exec.seq hex₁ (Exec.seq hex₂ (Exec.seq hex₃ (Exec.seq hex₄ hex₅))), ?_, ?_, htotal, ?_, ?_, ?_⟩
  · have hcost : (18 * x.cellCount + 39) * n = (18 * x.cellCount + 38) * n + n := by
      rw [show 18 * x.cellCount + 39 = (18 * x.cellCount + 38) + 1 by omega,
        Nat.add_mul, Nat.one_mul]
    rw [hcost]
    simpa only [List.length_finRange] using (by omega : 2 + (1 + n + (2 + (2 + t))) ≤
      (18 * x.cellCount + 38) * (List.finRange n).length + n + 8)
  · rw [htotal, hbuf]
    exact gm06BoundaryWrites_take _ labels (List.finRange n) (s₄.arrs 9) (by simp [s₄, s₃, s₂])
  · rw [hbuf, gm06BoundaryWrites_length]
    simp [s₄, s₃, s₂]
  · intro j hj; exact (harr j hj).trans (by simp [s₄, s₃, s₂, s₁, hj])
  · intro q hq₁ hq₂ hq₃ hq₄ hq₅ hq₆ hq₇ hq₈
    exact (hreg q hq₁ hq₂ hq₃ hq₄ hq₅ hq₆ hq₇ hq₈).trans
      (by simp [s₄, s₃, s₂, s₁, hq₃, hq₇, hq₈])

end GraphMinor.Compute
