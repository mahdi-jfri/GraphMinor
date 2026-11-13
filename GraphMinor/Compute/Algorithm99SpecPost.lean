module

public import GraphMinor.Compute.Algorithm99State
public import GraphMinor.Compute.BitSet
import GraphMinor.Compute.Join13BDSlice72

/-!
# Splitting the output of (9.9) into the arrays of `Alg99Spec`

`Alg99Spec` (the form in which (10.5) calls Algorithm (9.9) of Graph Minors XIII) asks for the
model of case (ii) in one array, and for the set `X` and the block of case (iii) in two arrays,
without the tag. The program `alg99SpecPostProg Q` reads the tag of `outArr` into register
`Q + 12`; on tag `1` it copies the rest of `outArr` to array `2`; on tag `2` it copies the next
`m` words (`m` in register `Q + 6`) to array `2` and the remaining words to array `3`; on tag `0`
it does nothing. The result is `alg99SpecPostProg_exec`, for any properties `P0`, `P2`, `P3` of
the parts.
-/

@[expose] public section

namespace GraphMinor.Compute

/-- `omega` after unfolding `Reg` and `Arr`. -/
local macro "romega" : tactic => `(tactic| ((try dsimp only [Reg, Arr, inArr, outArr] at *); omega))

/-- Split `outArr` by its tag: tag `1`, the rest to array `2`; tag `2`, the next `m` words
(register `Q + 6`) to array `2` and the others to array `3`. The tag is left in `Q + 12`. -/
def alg99SpecPostProg (Q : ℕ) : Cmd :=
  .seq (.assign (Q + 12) (.read outArr (.const 0)))
    (.ite (.op .eq (.reg (Q + 12)) (.const 1))
      (copyTailProg outArr 2 (Q + 13) (Q + 14))
      (.ite (.op .eq (.reg (Q + 12)) (.const 2))
        (.seq (readSliceProg outArr (.const 1) 2 (.reg (Q + 6)) (Q + 13))
          (.seq (.assign (Q + 13) (.op .sub (.op .sub (.len outArr) (.const 1)) (.reg (Q + 6))))
            (readSliceProg outArr (.op .add (.const 1) (.reg (Q + 6))) 3 (.reg (Q + 13)) (Q + 14))))
        .skip))

/-- **The split of the output of (9.9)**, on the Word RAM. If `outArr` is `0 :: code`,
`1 :: a2` or `2 :: (a2 ++ a3)` with `|a2| = m`, the program leaves the tag in register `Q + 12`
and the parts in arrays `2` and `3`, in time linear in the length of the output. It changes
only arrays `2`, `3` and registers from `Q + 12`. -/
theorem alg99SpecPostProg_exec {w m : ℕ} (Q : ℕ) (P0 : List ℕ → Prop) (P2 : List ℕ → Prop)
    (P3 : List ℕ → List ℕ → Prop) {s : State} {out : List ℕ}
    (hout : s.arrs outArr = out) (hm : s.regs (Q + 6) = m)
    (hcase : (∃ code, out = 0 :: code ∧ P0 code) ∨ (∃ a2, out = 1 :: a2 ∧ P2 a2) ∨
      (∃ a2 a3, out = 2 :: (a2 ++ a3) ∧ a2.length = m ∧ P3 a2 a3))
    (hw3 : 3 < 2 ^ w) (hlen_w : out.length < 2 ^ w) (hval_w : ∀ x ∈ out, x < 2 ^ w) :
    ∃ s' t, Exec w (alg99SpecPostProg Q) s s' t ∧ t ≤ 40 * out.length + 60 ∧
      (∀ a, a ≠ 2 → a ≠ 3 → s'.arrs a = s.arrs a) ∧
      (∀ r < Q + 12, s'.regs r = s.regs r) ∧
      ((s'.regs (Q + 12) = 0 ∧ ∃ code, out = 0 :: code ∧ P0 code) ∨
        (s'.regs (Q + 12) = 1 ∧ P2 (s'.arrs 2)) ∨
        (s'.regs (Q + 12) = 2 ∧ P3 (s'.arrs 2) (s'.arrs 3))) := by
  have c0 := checkWord_of_lt (w := w) (v := 0) (by omega)
  have c1 := checkWord_of_lt (w := w) (v := 1) (by omega)
  have c2 := checkWord_of_lt (w := w) (v := 2) (by omega)
  -- The tag.
  obtain ⟨x, l, hxl⟩ : ∃ x l, out = x :: l := by
    rcases hcase with ⟨c, rfl, -⟩ | ⟨a, rfl, -⟩ | ⟨a, b, rfl, -⟩ <;> exact ⟨_, _, rfl⟩
  subst hxl
  have hx_w : x < 2 ^ w := hval_w x (by simp)
  let s₁ := s.setReg (Q + 12) x
  have hex₁ : Exec w (.assign (Q + 12) (.read outArr (.const 0))) s s₁ 3 :=
    .assign (by simp [Expr.eval, c0, hout, checkWord_of_lt hx_w])
  have hout₁ : s₁.arrs outArr = x :: l := by simp [s₁, hout]
  have hm₁ : s₁.regs (Q + 6) = m := by simp [s₁, hm]
  have hl_w : ∀ y ∈ l, y < 2 ^ w := fun y hy => hval_w y (by simp [hy])
  simp only [List.length_cons] at hlen_w ⊢
  rcases hcase with ⟨code, hc, hP⟩ | ⟨a2, hc, hP⟩ | ⟨a2, a3, hc, hlen2, hP⟩ <;>
    obtain ⟨rfl, rfl⟩ := List.cons.inj hc
  · -- Tag `0`.
    have hne1 : (Expr.op .eq (.reg (Q + 12)) (.const 1)).eval w s₁ = some 0 := by
      simp [Expr.eval, BinOp.eval, BinOp.raw, s₁, c0, c1]
    have hne2 : (Expr.op .eq (.reg (Q + 12)) (.const 2)).eval w s₁ = some 0 := by
      simp [Expr.eval, BinOp.eval, BinOp.raw, s₁, c0, c2]
    refine ⟨s₁, 3 + (_ + (_ + 1)), .seq hex₁ (.ite_false hne1 (.ite_false hne2 (.skip _))),
      ?_, fun a _ _ => rfl, fun r hr => ?_, Or.inl ⟨by simp [s₁], _, rfl, hP⟩⟩
    · simp only [Expr.cost]; omega
    · simp [s₁, State.setReg_regs_ne _ _ (show r ≠ Q + 12 by omega)]
  · -- Tag `1`: the model.
    have he1 : (Expr.op .eq (.reg (Q + 12)) (.const 1)).eval w s₁ = some 1 := by
      simp [Expr.eval, BinOp.eval, BinOp.raw, s₁, c1]
    obtain ⟨s₂, t₂, hex₂, ht₂, h2₂, harr₂, hreg₂⟩ :=
      copyTailProg_exec outArr 2 (Q + 13) (Q + 14) (by romega) (by omega) (by omega) hout₁
        (by omega) hl_w
    refine ⟨s₂, 3 + (_ + t₂), .seq hex₁ (.ite_true he1 one_ne_zero hex₂), ?_,
      fun a h2 _ => by rw [harr₂ a h2]; rfl, fun r hr => ?_,
      Or.inr (Or.inl ⟨?_, by rw [h2₂]; exact hP⟩)⟩
    · simp only [Expr.cost]; omega
    · rw [hreg₂ r (by omega) (by omega)]
      simp [s₁, State.setReg_regs_ne _ _ (show r ≠ Q + 12 by omega)]
    · rw [hreg₂ _ (by omega) (by omega)]; simp [s₁]
  · -- Tag `2`: the set and the block.
    have he1 : (Expr.op .eq (.reg (Q + 12)) (.const 1)).eval w s₁ = some 0 := by
      simp [Expr.eval, BinOp.eval, BinOp.raw, s₁, c0, c1, c2]
    have he2 : (Expr.op .eq (.reg (Q + 12)) (.const 2)).eval w s₁ = some 1 := by
      simp [Expr.eval, BinOp.eval, BinOp.raw, s₁, c1, c2]
    have hL : (2 :: (a2 ++ a3)).length = 1 + m + a3.length := by simp [hlen2]; omega
    have hL' : (a2 ++ a3).length = m + a3.length := by simp [hlen2]
    obtain ⟨s₂, t₂, hex₂, ht₂, h2₂, harr₂, hreg₂⟩ :=
      readArraySlice72_exec outArr 2 (Q + 6) (Q + 13) 1 m (.const 1) (2 :: (a2 ++ a3))
        (by romega) (by omega) (by omega) (by rw [hL]; omega) (by omega)
        (fun y hy => hval_w y (List.mem_of_mem_drop (List.mem_of_mem_take hy))) s₁
        (by simp [Expr.eval, c1]) (by rw [hout₁]) hm₁
    have hout₂ : s₂.arrs outArr = 2 :: (a2 ++ a3) := by rw [harr₂ _ (by romega), hout₁]
    have hlen_a3 : (s₂.arrs outArr).length - 1 - m = a3.length := by rw [hout₂, hL]; omega
    have hm₂ : s₂.regs (Q + 6) = m := by rw [hreg₂ _ (by omega), hm₁]
    have hex₃ : Exec w (.assign (Q + 13) (.op .sub (.op .sub (.len outArr) (.const 1))
        (.reg (Q + 6)))) s₂ (s₂.setReg (Q + 13) a3.length) 6 := by
      refine .assign ?_
      have hw1 : (s₂.arrs outArr).length < 2 ^ w := by rw [hout₂, hL]; omega
      simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord_of_lt hw1, c1, hm₂,
        checkWord_of_lt (show (s₂.arrs outArr).length - 1 < 2 ^ w by omega),
        checkWord_of_lt (show m < 2 ^ w by omega), hlen_a3,
        checkWord_of_lt (show a3.length < 2 ^ w by omega)]
    obtain ⟨s₄, t₄, hex₄, ht₄, h3₄, harr₄, hreg₄⟩ :=
      readArraySlice72_exec outArr 3 (Q + 13) (Q + 14) (1 + m) a3.length
        (.op .add (.const 1) (.reg (Q + 6))) (2 :: (a2 ++ a3))
        (by romega) (by omega) (by omega) (by rw [hL]) (by omega)
        (fun y hy => hval_w y (List.mem_of_mem_drop (List.mem_of_mem_take hy)))
        (s₂.setReg (Q + 13) a3.length)
        (by simp [Expr.eval, BinOp.eval, BinOp.raw, c1, State.setReg_regs_ne _ _
          (show Q + 6 ≠ Q + 13 by omega), hm₂, checkWord_of_lt (show m < 2 ^ w by omega),
          checkWord_of_lt (show 1 + m < 2 ^ w by omega)])
        (by simpa using hout₂) (by simp)
    have hdrop2 : (List.drop 1 (2 :: (a2 ++ a3))).take m = a2 := by simp [← hlen2]
    have hdrop3 : (List.drop (1 + m) (2 :: (a2 ++ a3))).take a3.length = a3 := by
      rw [Nat.add_comm, ← List.drop_drop]; simp [← hlen2]
    refine ⟨s₄, 3 + (_ + (_ + (t₂ + (6 + t₄)))),
      .seq hex₁ (.ite_false he1 (.ite_true he2 one_ne_zero (.seq hex₂ (.seq hex₃ hex₄)))), ?_,
      fun a h2 h3 => ?_, fun r hr => ?_, Or.inr (Or.inr ⟨?_, ?_⟩)⟩
    · simp only [Expr.cost] at ht₂ ht₄ ⊢; rw [hL']; omega
    · rw [harr₄ a h3]; simp only [State.setReg_arrs]; rw [harr₂ a h2]; rfl
    · rw [hreg₄ r (by omega), State.setReg_regs_ne _ _ (show r ≠ Q + 13 by omega),
        hreg₂ r (by omega)]
      simp [s₁, State.setReg_regs_ne _ _ (show r ≠ Q + 12 by omega)]
    · rw [hreg₄ _ (by omega), State.setReg_regs_ne _ _ (show Q + 12 ≠ Q + 13 by omega),
        hreg₂ _ (by omega)]
      simp [s₁]
    · rw [h3₄, hdrop3, harr₄ 2 (by decide)]
      simp only [State.setReg_arrs]
      rw [h2₂, hdrop2]
      exact hP

end GraphMinor.Compute
