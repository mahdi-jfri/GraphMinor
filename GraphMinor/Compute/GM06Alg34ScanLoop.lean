module

public import GraphMinor.Compute.Logic

/-!
# Counted loops that accumulate a crossing flag

A scan body clears register 0 when its current test succeeds. The loop
therefore keeps the original answer precisely when no visited test has
succeeded. The invariant records this prefix condition and any data
preserved by the body. This rule will compose the four cuff scans.
-/

@[expose] public section
namespace GraphMinor.Compute

/-- Whether one of the first `n` tests succeeds. -/
def gm06AnyPrefix (f : ℕ → Bool) : ℕ → Bool
  | 0 => false
  | n + 1 => gm06AnyPrefix f n || f n

/-- Initialize a scan counter and iterate up to the cuff length in register 105. -/
def gm06ScanLoop (r : ℕ) (body : Cmd) : Cmd :=
  .seq (.assign r (.const 0)) (forUp r (.reg 105) body)

/-- A counted clearing scan preserves its data invariant and computes
the disjunction of all visited tests. This is a loop rule, to be applied
to the concrete crossing comparison and its enclosing scans. -/
theorem gm06ScanLoop_exec {w N B r : ℕ} (body : Cmd) (f : ℕ → Bool)
    (P : State → Prop) (hr : r ≠ 0) (hw : 1 < 2 ^ w) (hN : N < 2 ^ w)
    (hset : ∀ s v, P s → P (s.setReg r v))
    (hbound : ∀ s, P s → s.regs 105 = N)
    (hbody : ∀ i < N, ∀ s, P s → s.regs r = i →
      ∃ s' t, Exec w body s s' t ∧ t ≤ B ∧ P s' ∧ s'.regs r = i ∧
        s'.regs 0 = (if f i then 0 else s.regs 0))
    {s : State} (hs : P s) :
    ∃ s' t, Exec w (gm06ScanLoop r body) s s' t ∧
      t ≤ 5 + N * (7 + B) ∧ P s' ∧ s'.regs r = N ∧
      s'.regs 0 = (if gm06AnyPrefix f N then 0 else s.regs 0) := by
  let I := fun i s' => P s' ∧ s'.regs r = i ∧
    s'.regs 0 = (if gm06AnyPrefix f i then 0 else s.regs 0)
  have hhi : ∀ i ≤ N, ∀ s', I i s' →
      s'.regs r = i ∧ (Expr.reg 105).eval w s' = some N := by
    intro i _ s' hs'
    exact ⟨hs'.2.1, by simp [Expr.eval, checkWord, hbound s' hs'.1, hN]⟩
  have hb : ∀ i < N, Triple w (I i) body
      (fun s' => I (i + 1) (s'.setReg r (i + 1)) ∧ s'.regs r = i) (fun _ => B) := by
    intro i hi s' hs'
    obtain ⟨s'', t, hex, ht, hp, hcounter, hans⟩ := hbody i hi s' hs'.1 hs'.2.1
    refine ⟨s'', t, hex, ht, ⟨hset s'' (i + 1) hp, by simp, ?_⟩, hcounter⟩
    change (s''.setReg r (i + 1)).regs 0 = _
    rw [State.setReg_regs_ne _ _ (Ne.symm hr), hans, hs'.2.2]
    dsimp only [gm06AnyPrefix]
    have hbool (a b : Bool) (v : ℕ) :
        (if b then 0 else if a then 0 else v) = (if a || b then 0 else v) := by
      cases a <;> cases b <;> rfl
    exact hbool _ _ _
  have hloop := Triple.forUp_const I N B hw hN hhi hb
  have hinit : I 0 (s.setReg r 0) := by
    exact ⟨hset s 0 hs, State.setReg_regs_self _ _ _, by
      simp [gm06AnyPrefix, State.setReg_regs_ne _ _ (Ne.symm hr)]⟩
  obtain ⟨s', t, hex, ht, hp, hcounter, hans⟩ := hloop _ hinit
  have hex0 : Exec w (.assign r (.const 0)) s (s.setReg r 0) 2 :=
    .assign (by simp [Expr.eval, checkWord, Nat.zero_lt_of_lt hw])
  exact ⟨s', 2 + t, .seq hex0 hex, by change t ≤ 3 + N * (7 + B) at ht; omega,
    hp, hcounter, hans⟩

/-- A prefix has no successful test exactly when each visited test is false. -/
theorem gm06AnyPrefix_eq_false (f : ℕ → Bool) (n : ℕ) :
    gm06AnyPrefix f n = false ↔ ∀ i < n, f i = false := by
  induction n with
  | zero => simp [gm06AnyPrefix]
  | succ n ih =>
    simp only [gm06AnyPrefix, Bool.or_eq_false_iff, ih]
    constructor
    · rintro ⟨h, hn⟩ i hi
      rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi | rfl
      · exact h i hi
      · exact hn
    · intro h
      exact ⟨fun i hi => h i (Nat.lt_succ_of_lt hi), h n (Nat.lt_succ_self n)⟩

end GraphMinor.Compute
