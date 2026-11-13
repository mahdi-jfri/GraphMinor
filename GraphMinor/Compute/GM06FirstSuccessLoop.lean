module

public import GraphMinor.Compute.GM06CandidateAttempt

/-!
# Returning the first successful candidate search

Section 13 of our proof of VI (5.7) (outlined in `GraphMinor/GM06/Alg57Algorithm.lean`) skips a
failed candidate and immediately returns a successful one. This loop reads
contact positions from array 617 and stops when BFS succeeds. The
loop proof is stated for a search command with an exact execution
specification, so the candidate construction and BFS can be composed
without assuming a combinatorial search result.
-/

@[expose] public section
namespace GraphMinor.Compute
open TwoPaths

/-- Decode the successful contact and its BFS vertex row. -/
def gm06Find4Result (s : State) : Option (ℕ × List ℕ) :=
  (gm06BfsPathResult s).map (fun path => (s.regs 678, path))

/-- Continue while contacts remain and no BFS has succeeded. -/
def gm06FirstSuccessCond : Expr := exprAnd (.reg 677) (exprNot (.reg 646))

/-- Read and try the current contact, record its index, then advance. -/
def gm06FirstSuccessBody (attempt : Cmd) : Cmd :=
  .seq (.assign 673 (.read 617 (.reg 676)))
    (.seq attempt
      (.seq (.assign 678 (.reg 673))
        (.seq (.assign 676 (.op .add (.reg 676) (.const 1)))
          (.assign 677 (.op .sub (.reg 677) (.const 1))))))

/-- The first-success loop is independent of the search's internal scratch. -/
def gm06FirstSuccessLoop (attempt : Cmd) : Cmd :=
  .while gm06FirstSuccessCond (gm06FirstSuccessBody attempt)

private theorem cond_no_success {w count : ℕ} (s : State) (hw : 1 < 2 ^ w)
    (hcount : count < 2 ^ w) (hr : s.regs 677 = count) (hf : s.regs 646 = 0) :
    gm06FirstSuccessCond.eval w s = some count := by
  have he := GraphMinor.Compute.Crossing.eval_mul (GraphMinor.Compute.Crossing.eval_reg hr hcount)
    (eval_exprEq hw (GraphMinor.Compute.Crossing.eval_reg hf (Nat.two_pow_pos w))
      (GraphMinor.Compute.Crossing.eval_const (Nat.two_pow_pos w)))
    (by simpa using hcount)
  simpa only [gm06FirstSuccessCond, exprAnd, exprNot, exprEq, ↓reduceIte, Nat.mul_one] using he

private theorem cond_success {w count : ℕ} (s : State) (hw : 1 < 2 ^ w)
    (hcount : count < 2 ^ w) (hr : s.regs 677 = count) (hf : s.regs 646 = 1) :
    gm06FirstSuccessCond.eval w s = some 0 := by
  have he := GraphMinor.Compute.Crossing.eval_mul (GraphMinor.Compute.Crossing.eval_reg hr hcount)
    (eval_exprEq hw (GraphMinor.Compute.Crossing.eval_reg hf hw)
      (GraphMinor.Compute.Crossing.eval_const (Nat.two_pow_pos w)))
    (by simp)
  simpa only [gm06FirstSuccessCond, exprAnd, exprNot, exprEq, one_ne_zero, ↓reduceIte, Nat.mul_zero] using he

/-- A failed decoder is exactly the zero success flag, independent of
uninitialized path-array contents. -/
theorem gm06BfsPathResult_none_iff (s : State) :
    gm06BfsPathResult s = none ↔ s.regs 646 = 0 := by
  unfold gm06BfsPathResult
  split_ifs <;> simp_all

/-- Composing exact candidate searches in contact order gives the pure
first-success function. The callback premise is an execution contract
for the parameter command, not an assumed graph-theoretic claim. -/
theorem gm06FirstSuccessLoop_exec {w B : ℕ} (attempt : Cmd)
    (search : ℕ → Option (List ℕ)) (R A : List ℕ)
    (h673 : 673 ∉ R) (h676 : 676 ∉ R) (h677 : 677 ∉ R)
    (h617 : 617 ∉ A) (pre todo : List ℕ) (s : State)
    (hw : 1 < 2 ^ w) (hfit : pre.length + todo.length + 1 < 2 ^ w)
    (hwords : ∀ j ∈ todo, j < 2 ^ w) (hsource : s.arrs 617 = pre ++ todo)
    (hindex : s.regs 676 = pre.length) (hremaining : s.regs 677 = todo.length)
    (hflag : s.regs 646 = 0)
    (htry : ∀ j ∈ todo, ∀ st, Keeps ([673, 676, 677, 678] ++ R) A s st →
      st.regs 673 = j → ∃ sf t, Exec w attempt st sf t ∧ t ≤ B ∧ Keeps R A st sf ∧
        gm06BfsPathResult sf = search j ∧ (sf.regs 646 = 0 ∨ sf.regs 646 = 1)) :
    ∃ sf t, Exec w (gm06FirstSuccessLoop attempt) s sf t ∧
      t ≤ 5 + todo.length * (B + 18) ∧
      Keeps ([673, 676, 677, 678] ++ R) A s sf ∧
      gm06Find4Result sf = gm06FirstSuccessful search todo ∧
      (sf.regs 646 = 0 ∨ sf.regs 646 = 1) := by
  induction todo generalizing pre s with
  | nil =>
    refine ⟨s, 5, .while_false (cond_no_success s hw (Nat.two_pow_pos w) hremaining hflag),
      by simp, Keeps.refl _ _ _, ?_, Or.inl hflag⟩
    simp only [gm06Find4Result, gm06BfsPathResult, hflag, ↓reduceIte, Option.map_none,
      gm06FirstSuccessful]
  | cons j todo ih =>
    have hjword := hwords j List.mem_cons_self
    have hcount : todo.length + 1 < 2 ^ w := by simp only [List.length_cons] at hfit; omega
    have hpre : pre.length < 2 ^ w := by simp only [List.length_cons] at hfit; omega
    let s₀ := s.setReg 673 j
    have he₀ : Exec w (.assign 673 (.read 617 (.reg 676))) s s₀ 3 := by
      apply Exec.assign
      have ha : s.arrs 617 = pre ++ j :: todo := hsource
      have hget : (s.arrs 617)[pre.length]'(by simp only [ha, List.length_append, List.length_cons]; omega) = j := by
        simp only [ha, List.getElem_append_right (by omega : pre.length ≤ pre.length), Nat.sub_self,
          List.getElem_cons_zero]
      have he := GraphMinor.Compute.Crossing.eval_read (a := 617)
        (GraphMinor.Compute.Crossing.eval_reg hindex hpre)
        (by simp only [ha, List.length_append, List.length_cons]; omega) (by rw [hget]; exact hjword)
      simpa only [hget] using he
    have hk₀ : Keeps ([673, 676, 677, 678] ++ R) A s s₀ :=
      (Keeps.refl _ _ s).setReg (by simp) _
    obtain ⟨s₁, t₁, he₁, ht₁, hk₁, hd₁, hf₁⟩ := htry j List.mem_cons_self s₀ hk₀ (by simp [s₀])
    have h673₁ : s₁.regs 673 = j := (hk₁.1 673 h673).trans (by simp [s₀])
    have h676₁ : s₁.regs 676 = pre.length := (hk₁.1 676 h676).trans (by simpa [s₀] using hindex)
    have h677₁ : s₁.regs 677 = todo.length + 1 := (hk₁.1 677 h677).trans (by simpa [s₀] using hremaining)
    let s₂ := s₁.setReg 678 j
    let s₃ := s₂.setReg 676 (pre.length + 1)
    let s₄ := s₃.setReg 677 todo.length
    have he₂ : Exec w (.assign 678 (.reg 673)) s₁ s₂ 2 :=
      .assign (GraphMinor.Compute.Crossing.eval_reg h673₁ hjword)
    have he₃ : Exec w (.assign 676 (.op .add (.reg 676) (.const 1))) s₂ s₃ 4 :=
      .assign (GraphMinor.Compute.Crossing.eval_add
        (GraphMinor.Compute.Crossing.eval_reg (by simpa [s₂] using h676₁) hpre)
        (GraphMinor.Compute.Crossing.eval_const hw) (by simp only [List.length_cons] at hfit; omega))
    have he₄ : Exec w (.assign 677 (.op .sub (.reg 677) (.const 1))) s₃ s₄ 4 := by
      apply Exec.assign
      have he := GraphMinor.Compute.Crossing.eval_sub
        (GraphMinor.Compute.Crossing.eval_reg (r := 677) (s := s₃) (by simpa [s₃, s₂] using h677₁) hcount)
        (GraphMinor.Compute.Crossing.eval_const (c := 1) hw)
      simpa using he
    have hk₀₁ : Keeps ([673, 676, 677, 678] ++ R) A s s₁ :=
      hk₀.trans hk₁ (by intro r hr; exact List.mem_append_right _ hr) (fun _ h => h)
    have hk₄ : Keeps ([673, 676, 677, 678] ++ R) A s s₄ :=
      ((hk₀₁.setReg (by simp) _).setReg (by simp) _).setReg (by simp) _
    have hbody : Exec w (gm06FirstSuccessBody attempt) s s₄ (3 + (t₁ + (2 + (4 + 4)))) :=
      .seq he₀ (.seq he₁ (.seq he₂ (.seq he₃ he₄)))
    have hcond : gm06FirstSuccessCond.eval w s = some (todo.length + 1) :=
      cond_no_success s hw hcount hremaining hflag
    have hd₄ : gm06BfsPathResult s₄ = search j := by
      simpa [gm06BfsPathResult, s₄, s₃, s₂] using hd₁
    cases hs : search j with
    | none =>
      have hf₄ : s₄.regs 646 = 0 := (gm06BfsPathResult_none_iff s₄).mp (hd₄.trans hs)
      have hsource₄ : s₄.arrs 617 = (pre ++ [j]) ++ todo := by
        rw [hk₄.2 617 h617, hsource]
        simp only [List.append_assoc, List.singleton_append]
      obtain ⟨sf, tf, hef, htf, hkf, hdf, hflags⟩ := ih (pre ++ [j]) s₄
        (by simp only [List.length_append, List.length_cons, List.length_nil] at hfit ⊢; omega)
        (fun q hq => hwords q (List.mem_cons_of_mem _ hq)) hsource₄
        (by simp [s₄, s₃]) (by simp [s₄]) hf₄
        (fun q hq st hk hr => htry q (List.mem_cons_of_mem _ hq) st
          (hk₄.trans hk (fun _ h => h) (fun _ h => h)) hr)
      refine ⟨sf, 5 + (3 + (t₁ + (2 + (4 + 4)))) + tf,
        .while_true hcond (Nat.succ_ne_zero _) hbody hef, ?_,
        hk₄.trans hkf (fun _ h => h) (fun _ h => h), ?_, hflags⟩
      · simp only [List.length_cons, Nat.add_mul, Nat.one_mul]
        omega
      · simpa only [gm06FirstSuccessful, hs] using hdf
    | some path =>
      have hf₁' : s₁.regs 646 = 1 := by
        rcases hf₁ with hf | hf
        · have hnone := (gm06BfsPathResult_none_iff s₁).mpr hf
          rw [hd₁, hs] at hnone
          contradiction
        · exact hf
      have hf₄ : s₄.regs 646 = 1 := by simpa [s₄, s₃, s₂] using hf₁'
      have heStop : Exec w (gm06FirstSuccessLoop attempt) s₄ s₄ 5 :=
        .while_false (cond_success (count := todo.length) s₄ hw (by omega) (by simp [s₄]) hf₄)
      refine ⟨s₄, 5 + (3 + (t₁ + (2 + (4 + 4)))) + 5,
        .while_true hcond (Nat.succ_ne_zero _) hbody heStop, ?_, hk₄, ?_, Or.inr hf₄⟩
      · simp only [List.length_cons, Nat.add_mul, Nat.one_mul]
        omega
      · simp only [gm06Find4Result, hd₄, hs, Option.map_some, gm06FirstSuccessful,
          s₄, s₃, s₂, State.setReg_regs_ne _ _ (by decide : 678 ≠ 677),
          State.setReg_regs_ne _ _ (by decide : 678 ≠ 676), State.setReg_regs_self]

end GraphMinor.Compute
