module

public import GraphMinor.Compute.GM06Alg34SingletonBlockOption
public import GraphMinor.Compute.GM06Alg34KeepSingleton
import GraphMinor.Compute.GM06Alg34TagInit

/-!
# RAM search over all supplied division blocks

Read each counted block, run the verified singleton test, and retain
the first successful candidate. The induction follows the block stream
and proves that the final registers hold exactly the finite singleton
search combined with any earlier candidate. The time is linear in the
encoded division section and all arrays are preserved.
-/

@[expose] public section
namespace GraphMinor.Compute

/-- Search the blocks counted in register 107, retaining the first singleton. -/
def gm06SingletonLoopProg : Cmd :=
  .while (.reg 107)
    (.seq (readStreamWordProg 0 103 108)
      (.seq gm06SingletonBlockProg
        (.seq gm06KeepSingletonProg (.assign 107 (.op .sub (.reg 107) (.const 1))))))

/-- The whole-division RAM scan computes exactly the finite first-singleton
search, in linear time in its length-prefixed block section. -/
theorem gm06SingletonLoopProg_exec {w off : ℕ} (D : List (List ℕ))
    (tail : List ℕ) (found : Option ℕ)
    (hw : 1 < 2 ^ w) (hvalid : ∀ B ∈ D, ∀ v ∈ B, v < 2 ^ w)
    (hend : off + (D.flatMap GM06DrawingData.listWords).length < 2 ^ w)
    {s : State} (hstream : AtStream 0 off (D.flatMap GM06DrawingData.listWords ++ tail) s)
    (hpos : s.regs 103 = off) (hcount : s.regs 107 = D.length)
    (hfound : gm06SingletonRegs found s) :
    ∃ s' t, Exec w gm06SingletonLoopProg s s' t ∧
      t ≤ 50 * (D.flatMap GM06DrawingData.listWords).length + 1 ∧
      gm06SingletonRegs (found.or (gm06FindSingleton D)) s' ∧
      s'.regs 103 = off + (D.flatMap GM06DrawingData.listWords).length ∧
      s'.regs 107 = 0 ∧ AtStream 0 (off + (D.flatMap GM06DrawingData.listWords).length) tail s' ∧
      (∀ a : ℕ, s'.arrs a = s.arrs a) ∧
      (∀ q : ℕ, q ≠ 103 → q ≠ 107 → q ≠ 108 → q ≠ 109 →
        q ≠ 111 → q ≠ 112 → q ≠ 113 → q ≠ 114 → s'.regs q = s.regs q) := by
  induction D generalizing off s found with
  | nil =>
    have h0 : 0 < 2 ^ w := by omega
    have hc : (Expr.reg 107).eval w s = some 0 := by simp [Expr.eval, checkWord, hcount, h0]
    refine ⟨s, 1, .while_false hc, by simp, ?_, ?_, hcount, ?_, fun _ => rfl,
      fun _ _ _ _ _ _ _ _ _ => rfl⟩
    · cases found <;> exact hfound
    · simpa using hpos
    · simpa using hstream
  | cons B D ih =>
    let bytes := D.flatMap GM06DrawingData.listWords
    have hlen : ((B :: D).flatMap GM06DrawingData.listWords).length = 1 + B.length + bytes.length := by
      simp [GM06DrawingData.listWords, bytes]; omega
    have hcounts := gm06BlockSection_count_le_length D
    have hcountw : D.length + 1 < 2 ^ w := by dsimp only [bytes] at hlen; omega
    have hrestw : D.length < 2 ^ w := by omega
    have hBw : B.length < 2 ^ w := by omega
    have hstream' : AtStream 0 off (B.length :: (B ++ (bytes ++ tail))) s := by
      simpa only [List.flatMap_cons, GM06DrawingData.listWords, List.cons_append, List.append_assoc]
        using hstream
    obtain ⟨s₁, t₁, hex₁, ht₁, hB₁, hpos₁, hstream₁, harr₁, hreg₁⟩ :=
      readStreamWordProg_exec 103 108 (by decide) hw (by omega) hBw hstream' hpos
    have hfound₁ : gm06SingletonRegs found s₁ :=
      ⟨(hreg₁ 113 (by decide) (by decide)).trans hfound.1,
        fun v hv => (hreg₁ 114 (by decide) (by decide)).trans (hfound.2 v hv)⟩
    obtain ⟨s₂, t₂, hex₂, ht₂, hflag₂, hlabel₂, hpos₂, _, hstream₂, harr₂, hreg₂⟩ :=
      gm06SingletonBlockProg_exec_option B (bytes ++ tail) hw
        (hvalid B List.mem_cons_self) (by omega) hstream₁ hpos₁ hB₁
    have hfound₂ : gm06SingletonRegs found s₂ :=
      ⟨(hreg₂ 113 (by decide) (by decide) (by decide) (by decide) (by decide)).trans hfound₁.1,
        fun v hv => (hreg₂ 114 (by decide) (by decide) (by decide) (by decide) (by decide)).trans
          (hfound₁.2 v hv)⟩
    obtain ⟨s₃, t₃, hex₃, ht₃, hfound₃, harr₃, hreg₃⟩ :=
      gm06KeepSingletonProg_exec found (gm06SingletonLabel B) hw
        (fun v hv => hvalid B List.mem_cons_self v (gm06SingletonLabel_mem B v hv))
        hfound₂ hflag₂ hlabel₂
    have hcount₃ : s₃.regs 107 = D.length + 1 := by
      rw [hreg₃ 107 (by decide) (by decide),
        hreg₂ 107 (by decide) (by decide) (by decide) (by decide) (by decide),
        hreg₁ 107 (by decide) (by decide), hcount, List.length_cons]
    have hedec : (Expr.op .sub (.reg 107) (.const 1)).eval w s₃ = some D.length := by
      simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hcount₃, hcountw, hrestw, hw]
    let s₄ := s₃.setReg 107 D.length
    have hex₄ : Exec w (.assign 107 (.op .sub (.reg 107) (.const 1))) s₃ s₄ 4 := .assign hedec
    have hpos₄ : s₄.regs 103 = off + 1 + B.length := by
      rw [State.setReg_regs_ne _ _ (by decide : 103 ≠ 107), hreg₃ 103 (by decide) (by decide), hpos₂]
    have hfound₄ : gm06SingletonRegs (found.or (gm06SingletonLabel B)) s₄ := by
      simpa only [gm06SingletonRegs, s₄,
        State.setReg_regs_ne _ _ (by decide : 113 ≠ 107),
        State.setReg_regs_ne _ _ (by decide : 114 ≠ 107)] using hfound₃
    have hstream₄ : AtStream 0 (off + 1 + B.length) (bytes ++ tail) s₄ :=
      hstream₂.of_arr_eq (harr₃ 0)
    obtain ⟨s₅, t₅, hex₅, ht₅, hfound₅, hpos₅, hzero₅, hstream₅, harr₅, hreg₅⟩ :=
      ih (s := s₄) (off := off + 1 + B.length) (found.or (gm06SingletonLabel B))
        (fun A hA => hvalid A (List.mem_cons_of_mem B hA))
        (by change off + 1 + B.length + bytes.length < 2 ^ w; omega)
        hstream₄ hpos₄ (State.setReg_regs_self _ _ _) hfound₄
    have hopt : (found.or (gm06SingletonLabel B)).or (gm06FindSingleton D) =
        found.or (gm06FindSingleton (B :: D)) := by cases found <;> rfl
    have hcond : (Expr.reg 107).eval w s = some (D.length + 1) := by
      simp [Expr.eval, checkWord, hcount, hcountw]
    have hex : Exec w gm06SingletonLoopProg s s₅ (1 + (t₁ + (t₂ + (t₃ + 4))) + t₅) :=
      .while_true hcond (Nat.succ_ne_zero _) (.seq hex₁ (.seq hex₂ (.seq hex₃ hex₄))) hex₅
    have hoff : off + ((B :: D).flatMap GM06DrawingData.listWords).length =
        off + 1 + B.length + bytes.length := by rw [hlen]; omega
    refine ⟨s₅, _, hex, by rw [hlen]; dsimp only [bytes] at *; omega,
      hopt ▸ hfound₅, hpos₅.trans hoff.symm, hzero₅, hoff.symm ▸ hstream₅, ?_, ?_⟩
    · intro a
      exact (harr₅ a).trans ((harr₃ a).trans ((harr₂ a).trans (harr₁ a)))
    · intro q hq103 hq107 hq108 hq109 hq111 hq112 hq113 hq114
      rw [hreg₅ q hq103 hq107 hq108 hq109 hq111 hq112 hq113 hq114]
      change (s₃.setReg 107 D.length).regs q = s.regs q
      rw [State.setReg_regs_ne _ _ hq107, hreg₃ q hq113 hq114,
        hreg₂ q hq103 hq108 hq109 hq111 hq112, hreg₁ q hq103 hq108]

end GraphMinor.Compute
