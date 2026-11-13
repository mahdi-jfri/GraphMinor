module

public import GraphMinor.Compute.GM06Alg34BoundaryHitQuery

/-!
# Emitting selected relabelled boundary entries

Intersect a supplied survival mask entry with the computed boundary-hit
bit. When both are one, copy the corresponding new label from its rank
table into the reserved boundary buffer and advance its count. The
same command handles vertex and edge lists by choosing their mask and
rank array numbers.
-/

@[expose] public section
namespace GraphMinor.Compute

/-- Emit old label 207 when its survival mask and boundary-hit bit 206
are one, using buffer 9 and count 142. -/
def gm06BoundaryEmitProg (mask ranks : ℕ) : Cmd :=
  .ite (.op .mul (.read mask (.reg 207)) (.reg 206))
    (.seq (.write 9 (.reg 142) (.read ranks (.reg 207)))
      (.assign 142 (.op .add (.reg 142) (.const 1)))) .skip

/-- Boundary emission copies exactly the selected rank in at most
twelve steps, changing only the output buffer and its count. -/
theorem gm06BoundaryEmitProg_exec {w n k : ℕ} (mask ranks : ℕ)
    (active : Fin n → Bool) (labels : Fin n → ℕ) (v : Fin n) (hit : Bool)
    (hw : 1 < 2 ^ w) (hn : n < 2 ^ w) (hk : k + 1 < 2 ^ w)
    (hlabel : active v = true → labels v < 2 ^ w) {s : State}
    (hmask : s.arrs mask = List.ofFn (fun u : Fin n => if active u then 1 else 0))
    (hranks : s.arrs ranks = List.ofFn labels) (hv : s.regs 207 = v.val)
    (hhit : s.regs 206 = if hit then 1 else 0) (hcount : s.regs 142 = k)
    (hcap : k < (s.arrs 9).length) :
    ∃ s' t, Exec w (gm06BoundaryEmitProg mask ranks) s s' t ∧ t ≤ 12 ∧
      s'.arrs 9 = (if active v && hit then (s.arrs 9).set k (labels v) else s.arrs 9) ∧
      s'.regs 142 = k + (if active v && hit then 1 else 0) ∧
      (∀ a : ℕ, a ≠ 9 → s'.arrs a = s.arrs a) ∧
      (∀ q : ℕ, q ≠ 142 → s'.regs q = s.regs q) := by
  have hvw := v.isLt.trans hn
  have hkw : k < 2 ^ w := by omega
  have hmlen : v.val < (s.arrs mask).length := by rw [hmask, List.length_ofFn]; exact v.isLt
  have hmget : (s.arrs mask)[v.val]'hmlen = if active v then 1 else 0 := by
    simp only [hmask, List.getElem_ofFn]
  have htest : (Expr.op .mul (.read mask (.reg 207)) (.reg 206)).eval w s =
      some (if active v && hit then 1 else 0) := by
    cases ha : active v <;> cases hh : hit <;>
      simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hv, hvw, hhit, hmlen,
        hmget, ha, hh, hw, Nat.zero_lt_of_lt hw]
  by_cases hsel : (active v && hit) = true
  · have ha : active v = true := by
      cases hv' : active v <;> simp_all only [Bool.false_and, Bool.false_eq_true, Bool.true_and]
    have hrlen : v.val < (s.arrs ranks).length := by rw [hranks, List.length_ofFn]; exact v.isLt
    have hrget : (s.arrs ranks)[v.val]'hrlen = labels v := by simp only [hranks, List.getElem_ofFn]
    have hread : (Expr.read ranks (.reg 207)).eval w s = some (labels v) := by
      simp [Expr.eval, checkWord, hv, hvw, hrlen, hrget, hlabel ha]
    let s₁ := s.writeArr 9 k (labels v)
    let s₂ := s₁.setReg 142 (k + 1)
    have hwrite : Exec w (.write 9 (.reg 142) (.read ranks (.reg 207))) s s₁ 4 :=
      .write (by simp [Expr.eval, checkWord, hcount, hkw]) hread hcap
    have hinc : Exec w (.assign 142 (.op .add (.reg 142) (.const 1))) s₁ s₂ 4 :=
      .assign (by simp [s₁, Expr.eval, BinOp.eval, BinOp.raw, checkWord, hcount, hkw, hk, hw])
    have htest' : (Expr.op .mul (.read mask (.reg 207)) (.reg 206)).eval w s = some 1 := by
      simpa [hsel] using htest
    refine ⟨s₂, 12, Exec.ite_true htest' (by decide) (Exec.seq hwrite hinc), le_rfl,
      by simp only [hsel, ↓reduceIte]; rfl, by simp [s₂, hsel], ?_, ?_⟩
    · intro a ha; exact State.writeArr_arrs_ne _ _ _ ha
    · intro q hq; simp [s₂, s₁, State.setReg, hq]
  · have htest' : (Expr.op .mul (.read mask (.reg 207)) (.reg 206)).eval w s = some 0 := by
      simpa [hsel] using htest
    exact ⟨s, 5, Exec.ite_false htest' (Exec.skip s), by decide,
      by simp [hsel], by simp [hsel, hcount], fun _ _ => rfl, fun _ _ => rfl⟩

end GraphMinor.Compute
