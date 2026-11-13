module

public import GraphMinor.Compute.CrossingOpsBasic
public import GraphMinor.Compute.GM06Alg34DualEnds

/-!
# Choosing dual endpoints from an incident-region buffer

Read the first selected region. If there are at least two selected
regions, read the second. Otherwise use the first on both sides,
representing a loop. A zero selected count uses the zero padding as a
bounded default. The finite endpoint operation has exactly this form.
-/

@[expose] public section
namespace GraphMinor.Compute

open GraphMinor.Compute.Crossing

/-- The first two selected regions, repeating the first for a loop. -/
def gm06DualEndChoice (L : List ℕ) : ℕ × ℕ :=
  (L.getD 0 0, if 2 ≤ L.length then L.getD 1 0 else L.getD 0 0)

/-- Read endpoints from array 54 and its live count 7604 into 7610 and 7611. -/
def gm06DualEndChoiceProg : Cmd :=
  .seq (.assign 7610 (.read 54 (.const 0)))
    (.ite (.op .le (.const 2) (.reg 7604))
      (.assign 7611 (.read 54 (.const 1))) (.assign 7611 (.reg 7610)))

private theorem choice_first {L : List ℕ} {n : ℕ} (hn : 0 < n) (hL : L.length ≤ n) :
    (L ++ List.replicate (n - L.length) 0)[0]'(by simp only [List.length_append, List.length_replicate]; omega) =
      L.getD 0 0 := by
  cases L with
  | nil => simp only [List.nil_append, List.length_nil, Nat.sub_zero, List.getElem_replicate, List.getD_nil]
  | cons a L => simp only [List.cons_append, List.getElem_cons_zero, List.getD_cons_zero]

private theorem choice_second {L : List ℕ} {n : ℕ} (h2 : 2 ≤ L.length) (hL : L.length ≤ n) :
    (L ++ List.replicate (n - L.length) 0)[1]'(by simp only [List.length_append, List.length_replicate]; omega) =
      L.getD 1 0 := by
  cases L with
  | nil => simp only [List.length_nil] at h2; omega
  | cons a L =>
    cases L with
    | nil => simp only [List.length_cons, List.length_nil] at h2; omega
    | cons b L => simp only [List.cons_append, List.getElem_cons_succ, List.getElem_cons_zero,
        List.getD_cons_succ, List.getD_cons_zero]

/-- Endpoint selection computes the exact first-two operation in constant
RAM time, preserving every array and all other registers. -/
theorem gm06DualEndChoiceProg_exec {w n : ℕ} (L : List ℕ) {s : State}
    (hw : 2 < 2 ^ w) (hn : 0 < n) (hnw : n < 2 ^ w) (hL : L.length ≤ n)
    (hwords : ∀ y ∈ L, y < 2 ^ w)
    (hbuf : s.arrs 54 = L ++ List.replicate (n - L.length) 0) (hcount : s.regs 7604 = L.length) :
    ∃ s' t, Exec w gm06DualEndChoiceProg s s' t ∧ t ≤ 10 ∧
      s'.regs 7610 = (gm06DualEndChoice L).1 ∧ s'.regs 7611 = (gm06DualEndChoice L).2 ∧
      (∀ A : ℕ, s'.arrs A = s.arrs A) ∧
      (∀ r : ℕ, r ≠ 7610 → r ≠ 7611 → s'.regs r = s.regs r) := by
  have hw1 : 1 < 2 ^ w := by omega
  have hlen : (s.arrs 54).length = n := by
    simp only [hbuf, List.length_append, List.length_replicate]
    omega
  have h0 : 0 < (s.arrs 54).length := hlen.symm ▸ hn
  have hfirst : (s.arrs 54)[0] = L.getD 0 0 := by simpa only [hbuf] using choice_first hn hL
  have hfirstw : L.getD 0 0 < 2 ^ w := by
    cases L with
    | nil => simpa only [List.getD_nil] using (Nat.zero_lt_of_lt hw)
    | cons a L => simpa only [List.getD_cons_zero] using hwords a List.mem_cons_self
  let s₁ := s.setReg 7610 (L.getD 0 0)
  have he₁ : Exec w (.assign 7610 (.read 54 (.const 0))) s s₁ 3 :=
    .assign ((eval_read (eval_const (Nat.zero_lt_of_lt hw)) h0 (hfirst ▸ hfirstw)).trans
      (congrArg some hfirst))
  have hcond : (Expr.op .le (.const 2) (.reg 7604)).eval w s₁ =
      some (if 2 ≤ L.length then 1 else 0) := by
    have hbit : (if 2 ≤ L.length then 1 else 0) < 2 ^ w := by split_ifs <;> omega
    simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, s₁, hcount, hbit,
      show L.length < 2 ^ w from hL.trans_lt hnw, hw, hw1, Nat.zero_lt_of_lt hw]
  by_cases h2 : 2 ≤ L.length
  · have h1 : 1 < (s₁.arrs 54).length := by change 1 < (s.arrs 54).length; omega
    have hsecond : (s₁.arrs 54)[1] = L.getD 1 0 := by
      change (s.arrs 54)[1] = L.getD 1 0
      simpa only [hbuf] using choice_second h2 hL
    have hsecondw : L.getD 1 0 < 2 ^ w := by
      cases L with
      | nil => simp only [List.length_nil] at h2; omega
      | cons a L =>
        cases L with
        | nil => simp only [List.length_cons, List.length_nil] at h2; omega
        | cons b L =>
          simpa only [List.getD_cons_succ, List.getD_cons_zero] using
            (hwords b (List.mem_cons_of_mem a List.mem_cons_self))
    let s₂ := s₁.setReg 7611 (L.getD 1 0)
    have he₂ : Exec w (.assign 7611 (.read 54 (.const 1))) s₁ s₂ 3 :=
      .assign ((eval_read (eval_const hw1) h1 (hsecond ▸ hsecondw)).trans (congrArg some hsecond))
    refine ⟨s₂, 9, .seq he₁ (.ite_true (by simpa only [h2, ↓reduceIte] using hcond) (by decide) he₂),
      by decide, ?_, ?_, fun _ => rfl, ?_⟩
    · simp [s₂, s₁, gm06DualEndChoice]
    · simp [s₂, gm06DualEndChoice, h2]
    · intro r h10 h11; simp [s₂, s₁, State.setReg, h10, h11]
  · let s₂ := s₁.setReg 7611 (L.getD 0 0)
    have he₂ : Exec w (.assign 7611 (.reg 7610)) s₁ s₂ 2 :=
      .assign (eval_reg (by simp [s₁]) hfirstw)
    refine ⟨s₂, 8, .seq he₁ (.ite_false (by simpa only [h2, ↓reduceIte] using hcond) he₂),
      by decide, ?_, ?_, fun _ => rfl, ?_⟩
    · simp [s₂, s₁, gm06DualEndChoice]
    · simp [s₂, gm06DualEndChoice, h2]
    · intro r h10 h11; simp [s₂, s₁, State.setReg, h10, h11]

/-- The first-two natural operation is exactly the typed finite dual
endpoint choice, including the bounded zero default. -/
theorem gm06DualEndChoice_eq (x : GM06DrawingData) (hR : 0 < x.regions.length)
    (e : Fin x.ends.length) :
    gm06DualEndChoice ((x.incidentRegions e).map Fin.val) =
      let p := (x.dualEdgeEnds e).getD (⟨0, hR⟩, ⟨0, hR⟩)
      (p.1.val, p.2.val) := by
  unfold GM06DrawingData.dualEdgeEnds
  cases hh : x.incidentRegions e with
  | nil => simp [gm06DualEndChoice]
  | cons a L =>
    cases L with
    | nil => simp [gm06DualEndChoice]
    | cons b L => simp [gm06DualEndChoice]

end GraphMinor.Compute
