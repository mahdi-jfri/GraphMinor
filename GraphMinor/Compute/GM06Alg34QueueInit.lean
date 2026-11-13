module

public import GraphMinor.Compute.GM06Alg34DriverHeader
public import GraphMinor.Compute.Algorithm101Stream
import GraphMinor.Compute.CrossingOpsBasic
import Mathlib.Tactic.Ring

/-!
# Exact polynomial queue reservation

Compute the supplied vertex count plus the drawing and gap word lengths,
add two, and square four times. Allocate exactly the resulting power
and clear both queue cursors. Every intermediate power is below the
final capacity, so one capacity word bound suffices for the whole phase.
-/

public section
namespace GraphMinor.Compute

private theorem square_exec {w a : ℕ} {s : State} (hr : s.regs 9004 = a)
    (ha : a < 2 ^ w) (ha2 : a ^ 2 < 2 ^ w) :
    Exec w (.assign 9004 (.op .mul (.reg 9004) (.reg 9004)))
      s (s.setReg 9004 (a ^ 2)) 4 := by
  have hv := Crossing.eval_mul (Crossing.eval_reg hr ha) (Crossing.eval_reg hr ha)
    (show a * a < 2 ^ w by simpa only [Nat.pow_two] using ha2)
  have he : Exec w (.assign 9004 (.op .mul (.reg 9004) (.reg 9004)))
      s (s.setReg 9004 (a * a)) 4 := .assign hv
  simpa only [Nat.pow_two] using he

/-- Queue initialization reserves the exact sixteenth power, retains the
supplied arrays and all registers except its capacity and two queue cursors. -/
theorem gm06DriverQueueInit_exec (x : GM06DrawingData) {w : ℕ} {s : State}
    (hinput : s.arrs 0 = x.words)
    (hcap : (x.size + (s.arrs 47).length + 2) ^ 16 < 2 ^ w) :
    ∃ s' t, Exec w gm06DriverQueueInit s s' t ∧
      t ≤ (x.size + (s.arrs 47).length + 2) ^ 16 + 40 ∧
      IsPrefixBuffer 42 [] ((x.size + (s.arrs 47).length + 2) ^ 16) s' ∧
      s'.regs 7000 = 0 ∧ s'.regs 7001 = 0 ∧
      s'.regs 9004 = (x.size + (s.arrs 47).length + 2) ^ 16 ∧
      (∀ A : ℕ, A ≠ 42 → s'.arrs A = s.arrs A) ∧
      (∀ q : ℕ, q ≠ 9004 → q ≠ 7000 → q ≠ 7001 → s'.regs q = s.regs q) := by
  let B := x.size + (s.arrs 47).length + 2
  have hB2 : 2 ≤ B := by dsimp only [B]; omega
  have hB : B < 2 ^ w := (Nat.le_self_pow (by decide : 16 ≠ 0) B).trans_lt hcap
  have hp (k : ℕ) (hk : k ≤ 16) : B ^ k < 2 ^ w :=
    (Nat.pow_le_pow_right (by omega : 1 ≤ B) hk).trans_lt hcap
  have hsize : x.n + x.words.length = x.size := rfl
  have hn : x.n < 2 ^ w := by omega
  have hl0 : x.words.length < 2 ^ w := by omega
  have hl47 : (s.arrs 47).length < 2 ^ w := by dsimp only [B] at hB; omega
  have htwo : 2 < 2 ^ w := by omega
  have heval : (Expr.op .add (.read 0 (.const 0))
      (.op .add (.len 0) (.op .add (.len 47) (.const 2)))).eval w s = some B := by
    have he := Crossing.eval_add (gm06Driver_vertex_eval x hinput hn)
      (Crossing.eval_add (Crossing.eval_len hinput hl0)
        (Crossing.eval_add (Crossing.eval_len (a := 47) rfl hl47) (Crossing.eval_const htwo)
          (by dsimp only [B] at hB; omega))
        (by dsimp only [B] at hB; omega))
      (by dsimp only [B] at hB; omega)
    exact he.trans (congrArg some (by dsimp only [B]; omega))
  let s₁ := s.setReg 9004 B
  let s₂ := s₁.setReg 9004 (B ^ 2)
  let s₃ := s₂.setReg 9004 (B ^ 4)
  let s₄ := s₃.setReg 9004 (B ^ 8)
  let s₅ := s₄.setReg 9004 (B ^ 16)
  let s₆ := s₅.setArr 42 (List.replicate (B ^ 16) 0)
  let s₇ := s₆.setReg 7000 0
  let s₈ := s₇.setReg 7001 0
  have he₁ : Exec w (.assign 9004 (.op .add (.read 0 (.const 0))
      (.op .add (.len 0) (.op .add (.len 47) (.const 2))))) s s₁ 9 := .assign heval
  have he₂ : Exec w (.assign 9004 (.op .mul (.reg 9004) (.reg 9004))) s₁ s₂ 4 :=
    square_exec (a := B) rfl hB (hp 2 (by decide))
  have he₃ : Exec w (.assign 9004 (.op .mul (.reg 9004) (.reg 9004))) s₂ s₃ 4 := by
    have heq : (B ^ 2) ^ 2 = B ^ 4 := by ring
    simpa only [heq] using square_exec (a := B ^ 2) (s := s₂) rfl (hp 2 (by decide))
      (show (B ^ 2) ^ 2 < 2 ^ w by rw [heq]; exact hp 4 (by decide))
  have he₄ : Exec w (.assign 9004 (.op .mul (.reg 9004) (.reg 9004))) s₃ s₄ 4 := by
    have heq : (B ^ 4) ^ 2 = B ^ 8 := by ring
    simpa only [heq] using square_exec (a := B ^ 4) (s := s₃) rfl (hp 4 (by decide))
      (show (B ^ 4) ^ 2 < 2 ^ w by rw [heq]; exact hp 8 (by decide))
  have he₅ : Exec w (.assign 9004 (.op .mul (.reg 9004) (.reg 9004))) s₄ s₅ 4 := by
    have heq : (B ^ 8) ^ 2 = B ^ 16 := by ring
    simpa only [heq] using square_exec (a := B ^ 8) (s := s₄) rfl (hp 8 (by decide))
      (show (B ^ 8) ^ 2 < 2 ^ w by rw [heq]; exact hp 16 (by decide))
  have he₆ : Exec w (.alloc 42 (.reg 9004)) s₅ s₆ (1 + B ^ 16) :=
    .alloc (Crossing.eval_reg rfl hcap)
  have he₇ : Exec w (.assign 7000 (.const 0)) s₆ s₇ 2 := .assign (Crossing.eval_const (Nat.two_pow_pos w))
  have he₈ : Exec w (.assign 7001 (.const 0)) s₇ s₈ 2 := .assign (Crossing.eval_const (Nat.two_pow_pos w))
  refine ⟨s₈, _, .seq he₁ (.seq he₂ (.seq he₃ (.seq he₄ (.seq he₅ (.seq he₆ (.seq he₇ he₈)))))),
    by dsimp only [B]; omega, ?_, ?_, rfl, ?_, ?_, ?_⟩
  · simp [IsPrefixBuffer, s₈, s₇, s₆, B]
  · simp [s₈, s₇]
  · simp [s₈, s₇, s₆, s₅, B]
  · intro A hA
    simp [s₈, s₇, s₆, s₅, s₄, s₃, s₂, s₁, State.setArr, hA]
  · intro q hq hq0 hq1
    simp [s₈, s₇, s₆, s₅, s₄, s₃, s₂, s₁, State.setReg, hq, hq0, hq1]

end GraphMinor.Compute
