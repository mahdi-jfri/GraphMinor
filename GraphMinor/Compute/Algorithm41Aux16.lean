module

public import GraphMinor.Compute.Algorithm41Aux15

/-!
# Working Array Allocation for GM XIII (4.1)

The tree computation needs two set-union arenas, three working table buffers,
and one stored table per tree node. This file allocates those arrays while
preserving the input arrays produced by preprocessing.
-/

@[expose] public section

namespace GraphMinor.Compute

/-- Length of working array `a`, for tree size `t` and arena capacity `cap`. -/
def work41Length (δ ξ ω t cap a : ℕ) : ℕ :=
  if a < 26 then cap
  else if a < 41 then
    if (a - 26) % 5 < 2 then Q_max ξ ω else S_tab δ ξ ω
  else if a < 43 then t
  else if a < 45 then t * Q_max ξ ω
  else t * S_tab δ ξ ω

/-- Working array length expression. Register `18` holds the arena capacity. -/
def work41LengthExpr (δ ξ ω a : ℕ) : Expr :=
  if a < 26 then .reg 18
  else if a < 41 then
    if (a - 26) % 5 < 2 then .const (Q_max ξ ω) else .const (S_tab δ ξ ω)
  else if a < 43 then .reg 2
  else if a < 45 then .op .mul (.reg 2) (.const (Q_max ξ ω))
  else .op .mul (.reg 2) (.const (S_tab δ ξ ω))

/-- Allocate the arenas, working tables, and subtree table storage. -/
def alloc41WorkProg (δ ξ ω : ℕ) : Cmd :=
  seqRange 28 (fun k => .alloc (20 + k) (work41LengthExpr δ ξ ω (20 + k)))

private theorem work41LengthExpr_eval {w δ ξ ω t cap : ℕ} (a : ℕ)
    (ht : t < 2 ^ w) (hc : cap < 2 ^ w)
    (hQ : Q_max ξ ω < 2 ^ w) (hS : S_tab δ ξ ω < 2 ^ w)
    (htQ : t * Q_max ξ ω < 2 ^ w) (htS : t * S_tab δ ξ ω < 2 ^ w)
    {s : State} (hr2 : s.regs 2 = t) (hr18 : s.regs 18 = cap) :
    (work41LengthExpr δ ξ ω a).eval w s = some (work41Length δ ξ ω t cap a) := by
  unfold work41LengthExpr work41Length
  split_ifs <;> simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hr2, hr18, ht, hc, hQ, hS, htQ, htS]

private theorem work41LengthExpr_cost (δ ξ ω a : ℕ) :
    (work41LengthExpr δ ξ ω a).cost ≤ 3 := by
  unfold work41LengthExpr
  split_ifs <;> simp only [Expr.cost] <;> decide

private theorem work41Length_le {δ ξ ω t cap : ℕ}
    (hQ : Q_max ξ ω ≤ cap) (hS : S_tab δ ξ ω ≤ cap)
    (ht : t ≤ cap) (htQ : t * Q_max ξ ω ≤ cap) (htS : t * S_tab δ ξ ω ≤ cap) (a : ℕ) :
    work41Length δ ξ ω t cap a ≤ cap := by
  unfold work41Length
  split_ifs <;> first | exact Nat.le_refl _ | assumption

/-- Allocate all 28 arrays with their required lengths. The bound counts the zero filling,
and the frame conditions preserve every register and every preprocessing array. -/
theorem alloc41WorkProg_exec {w δ ξ ω t cap : ℕ} {s₀ : State}
    (hc : cap < 2 ^ w)
    (hQ : Q_max ξ ω ≤ cap) (hS : S_tab δ ξ ω ≤ cap)
    (ht : t ≤ cap) (htQ : t * Q_max ξ ω ≤ cap) (htS : t * S_tab δ ξ ω ≤ cap)
    (hr2 : s₀.regs 2 = t) (hr18 : s₀.regs 18 = cap) :
    ∃ s' time, Exec w (alloc41WorkProg δ ξ ω) s₀ s' time ∧
      time ≤ 1 + (3 + cap) * 28 ∧
      (∀ r : ℕ, s'.regs r = s₀.regs r) ∧
      (∀ a : ℕ, 20 ≤ a → a < 48 →
        s'.arrs a = List.replicate (work41Length δ ξ ω t cap a) 0) ∧
      (∀ a : ℕ, a < 20 ∨ 48 ≤ a → s'.arrs a = s₀.arrs a) := by
  let P : ℕ → State → Prop := fun k s =>
    (∀ r : ℕ, s.regs r = s₀.regs r) ∧
    (∀ a : ℕ, 20 ≤ a → a < 20 + k →
      s.arrs a = List.replicate (work41Length δ ξ ω t cap a) 0) ∧
    (∀ a : ℕ, a < 20 ∨ 20 + k ≤ a → s.arrs a = s₀.arrs a)
  have h0 : P 0 s₀ := ⟨fun _ => rfl, fun a ha hb => by omega, fun _ _ => rfl⟩
  have hstep : ∀ k < 28, ∀ s, P k s → ∃ s' time,
      Exec w (.alloc (20 + k) (work41LengthExpr δ ξ ω (20 + k))) s s' time ∧
      time ≤ 3 + cap ∧ P (k + 1) s' := by
    intro k hk s hs
    obtain ⟨hreg, harr, hframe⟩ := hs
    let len := work41Length δ ξ ω t cap (20 + k)
    have heval := work41LengthExpr_eval (20 + k) (Nat.lt_of_le_of_lt ht hc) hc
      (Nat.lt_of_le_of_lt hQ hc) (Nat.lt_of_le_of_lt hS hc)
      (Nat.lt_of_le_of_lt htQ hc) (Nat.lt_of_le_of_lt htS hc)
      ((hreg 2).trans hr2) ((hreg 18).trans hr18)
    refine ⟨s.setArr (20 + k) (List.replicate len 0),
      (work41LengthExpr δ ξ ω (20 + k)).cost + len, .alloc heval, ?_, ?_⟩
    · exact Nat.add_le_add (work41LengthExpr_cost δ ξ ω (20 + k)) (work41Length_le hQ hS ht htQ htS _)
    · refine ⟨hreg, ?_, ?_⟩
      · intro a ha hb
        by_cases heq : a = 20 + k
        · subst a
          exact State.setArr_arrs_self ..
        · rw [State.setArr_arrs_ne _ _ heq]
          exact harr a ha (by omega)
      · intro a ha
        have hne : a ≠ 20 + k := by omega
        rw [State.setArr_arrs_ne _ _ hne]
        exact hframe a (by omega)
  rcases Exec.seqRange P h0 hstep with ⟨s', time, hex, htime, hP⟩
  exact ⟨s', time, hex, htime, hP.1, hP.2.1, hP.2.2⟩

end GraphMinor.Compute
