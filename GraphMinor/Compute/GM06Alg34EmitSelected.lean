module

public import GraphMinor.Compute.CrossingOpsBasic

/-!
# Emitting a computed label selected by a finite test

The dual serializer filters supplied incidence rows and gap classes.
A successful test emits the value of a read-only label expression. A
failed test emits nothing. The exact buffer suffix and memory frame
allow these scans to be composed with the surrounding serializer.
-/

@[expose] public section
namespace GraphMinor.Compute

open GraphMinor.Compute.Crossing

/-- Append the computed label exactly when the test succeeds. -/
def gm06EmitSelectedProg (buf cursor : ℕ) (test value : Expr) : Cmd :=
  .ite test (emitProg buf cursor value) .skip

/-- One selected-label step appends exactly its finite output and changes
only the destination buffer and its cursor. -/
theorem gm06EmitSelectedProg_exec {w buf cursor : ℕ} (test value : Expr)
    (keep : Bool) (label : ℕ) {pre : List ℕ} {cap : ℕ} {s : State}
    (htest : test.eval w s = some (if keep then 1 else 0))
    (hvalue : keep = true → value.eval w s = some label)
    (hbuf : IsBuf buf cursor pre cap s)
    (hcap : (if keep then 1 else 0) ≤ cap) (hfit : pre.length + 1 < 2 ^ w) :
    ∃ s' t, Exec w (gm06EmitSelectedProg buf cursor test value) s s' t ∧
      t ≤ test.cost + value.cost + 6 ∧
      IsBuf buf cursor (pre ++ if keep then [label] else [])
        (cap - if keep then 1 else 0) s' ∧
      (∀ A, A ≠ buf → s'.arrs A = s.arrs A) ∧
      (∀ r, r ≠ cursor → s'.regs r = s.regs r) := by
  cases keep with
  | false =>
    refine ⟨s, test.cost + 1, .ite_false htest (.skip s), by omega, ?_,
      fun _ _ => rfl, fun _ _ => rfl⟩
    simpa only [Bool.false_eq_true, ↓reduceIte, List.append_nil, Nat.sub_zero] using hbuf
  | true =>
    have hcap' : cap = cap - 1 + 1 := by change 1 ≤ cap at hcap; omega
    obtain ⟨he, hb⟩ := emitProg_exec buf cursor value (k := cap - 1)
      (hcap' ▸ hbuf) (hvalue rfl) hfit
    refine ⟨_, test.cost + (value.cost + 6), .ite_true htest (by decide) he,
      by omega, ?_, ?_, ?_⟩
    · simpa only [↓reduceIte] using hb
    · intro A hA
      simp only [State.setReg_arrs, State.writeArr, State.setArr_arrs_ne _ _ hA]
    · intro r hr
      simp only [State.setReg_regs_ne _ _ hr, State.writeArr_regs]

end GraphMinor.Compute
