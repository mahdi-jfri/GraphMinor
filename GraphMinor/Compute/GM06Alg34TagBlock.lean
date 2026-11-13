module

public import GraphMinor.Compute.GM06Alg34Stream

/-!
# Writing one supplied division block into the label table

For each vertex label in a block, read that label from the input and
write the current block tag into array 3. The counted loop handles
repeated labels as well. Its execution is the explicit finite sequence
of list updates, with linear time in the block length.
-/

@[expose] public section
namespace GraphMinor.Compute

/-- Apply a block's tag to exactly its listed vertex positions. -/
def gm06TagBlock (tag : ℕ) : List ℕ → List ℕ → List ℕ
  | [], ids => ids
  | v :: vs, ids => gm06TagBlock tag vs (ids.set v tag)

theorem gm06TagBlock_length (tag : ℕ) (vs ids : List ℕ) :
    (gm06TagBlock tag vs ids).length = ids.length := by
  induction vs generalizing ids with
  | nil => rfl
  | cons v vs ih => simpa only [gm06TagBlock, List.length_set] using ih (ids.set v tag)

/-- Read the counted labels from cursor 103 and write tag 107 into table
array 3. Register 108 counts remaining labels, and 109 holds one label. -/
def gm06TagBlockProg : Cmd :=
  .while (.reg 108)
    (.seq (readStreamWordProg 0 103 109)
      (.seq (.write 3 (.reg 109) (.reg 107))
        (.assign 108 (.op .sub (.reg 108) (.const 1)))))

/-- Tagging a supplied block costs at most `20 * length + 1` steps and
updates exactly the listed positions of the existing table. -/
theorem gm06TagBlockProg_exec {w off : ℕ} (tag : ℕ) (vs ids tail : List ℕ)
    (hw : 1 < 2 ^ w) (hidsw : ids.length < 2 ^ w) (htagw : tag < 2 ^ w)
    (hvalid : ∀ v ∈ vs, v < ids.length) (hend : off + vs.length < 2 ^ w)
    {s : State} (hstream : AtStream 0 off (vs ++ tail) s) (hids : s.arrs 3 = ids)
    (hpos : s.regs 103 = off) (hcount : s.regs 108 = vs.length) (htag : s.regs 107 = tag) :
    ∃ s' t, Exec w gm06TagBlockProg s s' t ∧ t ≤ 20 * vs.length + 1 ∧
      s'.arrs 3 = gm06TagBlock tag vs ids ∧ s'.regs 103 = off + vs.length ∧
      s'.regs 108 = 0 ∧ AtStream 0 (off + vs.length) tail s' ∧
      (∀ a : ℕ, a ≠ 3 → s'.arrs a = s.arrs a) ∧
      (∀ q : ℕ, q ≠ 103 → q ≠ 108 → q ≠ 109 → s'.regs q = s.regs q) := by
  induction vs generalizing off ids s with
  | nil =>
    have h0 : 0 < 2 ^ w := by omega
    have hc : (Expr.reg 108).eval w s = some 0 := by
      simp only [Expr.eval, hcount, List.length_nil, checkWord, h0, ↓reduceIte]
    refine ⟨s, 1, .while_false hc, by simp, hids, ?_, hcount, ?_, fun _ _ => rfl,
      fun _ _ _ _ => rfl⟩
    · simpa only [List.length_nil, Nat.add_zero] using hpos
    · simpa only [List.nil_append, List.length_nil, Nat.add_zero] using hstream
  | cons v vs ih =>
    have hv : v < ids.length := hvalid v List.mem_cons_self
    have hvw : v < 2 ^ w := hv.trans hidsw
    have hcountw : vs.length + 1 < 2 ^ w := by simp only [List.length_cons] at hend; omega
    have hrestw : vs.length < 2 ^ w := lt_trans (Nat.lt_succ_self _) hcountw
    obtain ⟨s₁, t₁, hex₁, ht₁, hv₁, hpos₁, hstream₁, harr₁, hreg₁⟩ :=
      readStreamWordProg_exec 103 109 (by decide) hw (by simp only [List.length_cons] at hend; omega)
        hvw hstream hpos
    have htag₁ : s₁.regs 107 = tag := by rw [hreg₁ 107 (by decide) (by decide), htag]
    have hidx : v < (s₁.arrs 3).length := by rw [harr₁ 3, hids]; exact hv
    let s₂ := s₁.writeArr 3 v tag
    have hex₂ : Exec w (.write 3 (.reg 109) (.reg 107)) s₁ s₂ 3 :=
      .write (by simp [Expr.eval, checkWord, hv₁, hvw])
        (by simp [Expr.eval, checkWord, htag₁, htagw]) hidx
    have hids₂ : s₂.arrs 3 = ids.set v tag := by
      simp only [s₂, State.writeArr_arrs_self, harr₁ 3, hids]
    have hcount₂ : s₂.regs 108 = vs.length + 1 := by
      simp only [s₂, State.writeArr_regs, hreg₁ 108 (by decide) (by decide), hcount, List.length_cons]
    have heval : (Expr.op .sub (.reg 108) (.const 1)).eval w s₂ = some vs.length := by
      simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hcount₂, hcountw, hrestw, hw]
    let s₃ := s₂.setReg 108 vs.length
    have hex₃ : Exec w (.assign 108 (.op .sub (.reg 108) (.const 1))) s₂ s₃ 4 := .assign heval
    have hstream₃ : AtStream 0 (off + 1) (vs ++ tail) s₃ :=
      hstream₁.of_arr_eq (by
        simp only [s₃, State.setReg_arrs, s₂, State.writeArr_arrs_ne _ _ _ (by decide : 0 ≠ 3)])
    have hids₃ : s₃.arrs 3 = ids.set v tag := hids₂
    have hpos₃ : s₃.regs 103 = off + 1 := by
      simpa only [s₃, State.setReg_regs_ne _ _ (by decide : 103 ≠ 108),
        s₂, State.writeArr_regs] using hpos₁
    have htag₃ : s₃.regs 107 = tag := by
      simpa only [s₃, State.setReg_regs_ne _ _ (by decide : 107 ≠ 108),
        s₂, State.writeArr_regs] using htag₁
    have hvalid₃ : ∀ z ∈ vs, z < (ids.set v tag).length := by
      intro z hz
      simpa only [List.length_set] using hvalid z (List.mem_cons_of_mem v hz)
    have hend₃ : off + 1 + vs.length < 2 ^ w := by
      simp only [List.length_cons] at hend
      omega
    obtain ⟨s₄, t₄, hex₄, ht₄, hids₄, hpos₄, hzero₄, hstream₄, harr₄, hreg₄⟩ :=
      ih (ids.set v tag) (by simpa only [List.length_set] using hidsw) hvalid₃ hend₃
        hstream₃ hids₃ hpos₃ (State.setReg_regs_self _ _ _) htag₃
    have hcond : (Expr.reg 108).eval w s = some (vs.length + 1) := by
      simp only [Expr.eval, hcount, List.length_cons, checkWord, hcountw, ↓reduceIte]
    have hoff : off + (v :: vs).length = off + 1 + vs.length := by simp; omega
    refine ⟨s₄, 1 + (t₁ + (3 + 4)) + t₄,
      .while_true hcond (Nat.succ_ne_zero _) (.seq hex₁ (.seq hex₂ hex₃)) hex₄,
      ?_, hids₄, hpos₄.trans hoff.symm, hzero₄, hoff.symm ▸ hstream₄, ?_, ?_⟩
    · simp only [List.length_cons]
      omega
    · intro a ha
      rw [harr₄ a ha]
      change (s₁.writeArr 3 v tag).arrs a = s.arrs a
      rw [State.writeArr_arrs_ne _ _ _ ha, harr₁ a]
    · intro q hq103 hq108 hq109
      rw [hreg₄ q hq103 hq108 hq109]
      change (s₂.setReg 108 vs.length).regs q = s.regs q
      rw [State.setReg_regs_ne _ _ hq108]
      exact hreg₁ q hq103 hq109

end GraphMinor.Compute
