module

public import GraphMinor.Compute.GM06Alg34TagBlock

/-!
# Writing all supplied division blocks into the table

The outer counter is also the current tag. It decreases after each block,
so later occurrences of a block overwrite earlier tags consistently. The
execution proof follows the length-prefixed input blocks and gives linear
time in the size of their encoded section.
-/

@[expose] public section
namespace GraphMinor.Compute

/-- The finite table obtained by scanning the supplied blocks in order.
Each block receives the number of blocks still to be processed. -/
def gm06DivisionIds : List (List ℕ) → List ℕ → List ℕ
  | [], ids => ids
  | B :: D, ids => gm06DivisionIds D (gm06TagBlock (B :: D).length B ids)

theorem gm06DivisionIds_length (D : List (List ℕ)) (ids : List ℕ) :
    (gm06DivisionIds D ids).length = ids.length := by
  induction D generalizing ids with
  | nil => rfl
  | cons B D ih => simp only [gm06DivisionIds, ih, gm06TagBlock_length]

/-- Read each block length, tag its listed vertices, and decrease the
remaining-block count in register 107. -/
def gm06TagDivisionLoopProg : Cmd :=
  .while (.reg 107)
    (.seq (readStreamWordProg 0 103 108)
      (.seq gm06TagBlockProg (.assign 107 (.op .sub (.reg 107) (.const 1)))))

/-- The division loop performs exactly the finite table updates encoded
by the supplied blocks. Its cost is linear in the encoded block section. -/
theorem gm06TagDivisionLoopProg_exec {w off : ℕ} (D : List (List ℕ)) (ids tail : List ℕ)
    (hw : 1 < 2 ^ w) (hidsw : ids.length < 2 ^ w) (hcountw : D.length < 2 ^ w)
    (hvalid : ∀ B ∈ D, ∀ v ∈ B, v < ids.length)
    (hend : off + (D.flatMap GM06DrawingData.listWords).length < 2 ^ w)
    {s : State} (hstream : AtStream 0 off (D.flatMap GM06DrawingData.listWords ++ tail) s)
    (hids : s.arrs 3 = ids) (hpos : s.regs 103 = off) (hcount : s.regs 107 = D.length) :
    ∃ s' t, Exec w gm06TagDivisionLoopProg s s' t ∧
      t ≤ 40 * (D.flatMap GM06DrawingData.listWords).length + 1 ∧
      s'.arrs 3 = gm06DivisionIds D ids ∧
      s'.regs 103 = off + (D.flatMap GM06DrawingData.listWords).length ∧
      s'.regs 107 = 0 ∧ AtStream 0 (off + (D.flatMap GM06DrawingData.listWords).length) tail s' ∧
      (∀ a : ℕ, a ≠ 3 → s'.arrs a = s.arrs a) ∧
      (∀ q : ℕ, q ≠ 103 → q ≠ 107 → q ≠ 108 → q ≠ 109 → s'.regs q = s.regs q) := by
  induction D generalizing off ids s with
  | nil =>
    have h0 : 0 < 2 ^ w := by omega
    have hc : (Expr.reg 107).eval w s = some 0 := by
      simp only [Expr.eval, hcount, List.length_nil, checkWord, h0, ↓reduceIte]
    refine ⟨s, 1, .while_false hc, by simp, hids, ?_, hcount, ?_, fun _ _ => rfl,
      fun _ _ _ _ _ => rfl⟩
    · simpa only [List.flatMap_nil, List.length_nil, Nat.add_zero] using hpos
    · simpa only [List.flatMap_nil, List.nil_append, List.length_nil, Nat.add_zero] using hstream
  | cons B D ih =>
    have hbytes : ((B :: D).flatMap GM06DrawingData.listWords).length =
        1 + B.length + (D.flatMap GM06DrawingData.listWords).length := by
      simp only [List.flatMap_cons, List.length_append, GM06DrawingData.listWords, List.length_cons]
      omega
    have htotal : off + 1 + B.length + (D.flatMap GM06DrawingData.listWords).length < 2 ^ w := by
      rw [hbytes] at hend
      omega
    have hstream₀ : AtStream 0 off
        (B.length :: (B ++ (D.flatMap GM06DrawingData.listWords ++ tail))) s := by
      simpa only [List.flatMap_cons, GM06DrawingData.listWords, List.cons_append,
        List.append_assoc] using hstream
    obtain ⟨s₁, t₁, hex₁, ht₁, hlen₁, hpos₁, hstream₁, harr₁, hreg₁⟩ :=
      readStreamWordProg_exec 103 108 (by decide) hw (by omega) (by omega) hstream₀ hpos
    have htag₁ : s₁.regs 107 = (B :: D).length := by
      rw [hreg₁ 107 (by decide) (by decide), hcount]
    have hids₁ : s₁.arrs 3 = ids := (harr₁ 3).trans hids
    obtain ⟨s₂, t₂, hex₂, ht₂, hids₂, hpos₂, _, hstream₂, harr₂, hreg₂⟩ :=
      gm06TagBlockProg_exec (B :: D).length B ids (D.flatMap GM06DrawingData.listWords ++ tail)
        hw hidsw hcountw (hvalid B List.mem_cons_self) (by omega)
        hstream₁ hids₁ hpos₁ hlen₁ htag₁
    have hcount₂ : s₂.regs 107 = D.length + 1 := by
      rw [hreg₂ 107 (by decide) (by decide) (by decide), htag₁, List.length_cons]
    have hsuccw : D.length + 1 < 2 ^ w := hcountw
    have hrestw : D.length < 2 ^ w := lt_trans (Nat.lt_succ_self _) hsuccw
    have heval : (Expr.op .sub (.reg 107) (.const 1)).eval w s₂ = some D.length := by
      simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hcount₂, hsuccw, hrestw, hw]
    let s₃ := s₂.setReg 107 D.length
    have hex₃ : Exec w (.assign 107 (.op .sub (.reg 107) (.const 1))) s₂ s₃ 4 := .assign heval
    have hids₃ : s₃.arrs 3 = gm06TagBlock (B :: D).length B ids := hids₂
    have hpos₃ : s₃.regs 103 = off + 1 + B.length := by
      simpa only [s₃, State.setReg_regs_ne _ _ (by decide : 103 ≠ 107)] using hpos₂
    have hstream₃ : AtStream 0 (off + 1 + B.length)
        (D.flatMap GM06DrawingData.listWords ++ tail) s₃ := hstream₂.of_arr_eq rfl
    have hidsw₃ : (gm06TagBlock (B :: D).length B ids).length < 2 ^ w := by
      rw [gm06TagBlock_length]
      exact hidsw
    have hvalid₃ : ∀ A ∈ D, ∀ v ∈ A, v < (gm06TagBlock (B :: D).length B ids).length := by
      intro A hA v hv
      rw [gm06TagBlock_length]
      exact hvalid A (List.mem_cons_of_mem B hA) v hv
    obtain ⟨s₄, t₄, hex₄, ht₄, hids₄, hpos₄, hzero₄, hstream₄, harr₄, hreg₄⟩ :=
      ih (gm06TagBlock (B :: D).length B ids) hidsw₃ hrestw hvalid₃ htotal hstream₃ hids₃
        hpos₃ (State.setReg_regs_self _ _ _)
    have hcond : (Expr.reg 107).eval w s = some (D.length + 1) := by
      simp only [Expr.eval, hcount, List.length_cons, checkWord, hsuccw, ↓reduceIte]
    have hoff : off + ((B :: D).flatMap GM06DrawingData.listWords).length =
        off + 1 + B.length + (D.flatMap GM06DrawingData.listWords).length := by
      rw [hbytes]
      omega
    refine ⟨s₄, 1 + (t₁ + (t₂ + 4)) + t₄,
      .while_true hcond (Nat.succ_ne_zero _) (.seq hex₁ (.seq hex₂ hex₃)) hex₄,
      ?_, hids₄, hpos₄.trans hoff.symm, hzero₄, hoff.symm ▸ hstream₄, ?_, ?_⟩
    · rw [hbytes]
      omega
    · intro a ha
      rw [harr₄ a ha]
      exact (harr₂ a ha).trans (harr₁ a)
    · intro q hq103 hq107 hq108 hq109
      rw [hreg₄ q hq103 hq107 hq108 hq109]
      change (s₂.setReg 107 D.length).regs q = s.regs q
      rw [State.setReg_regs_ne _ _ hq107, hreg₂ q hq103 hq108 hq109]
      exact hreg₁ q hq103 hq108

end GraphMinor.Compute
