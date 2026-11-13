module

public import GraphMinor.Compute.GM06Alg34Stream

/-!
# Locating the cuff data after the regions

The input gives two incidence lists per region. A counted RAM loop skips
both lists and decreases its region counter. The execution proof follows
the supplied list of regions and gives a linear bound in their number.
The lists' entries and every array remain unchanged.
-/

@[expose] public section
namespace GraphMinor.Compute

/-- The region section of the input, with both incidence lists per region. -/
def gm06RegionWords : List (List ℕ × List ℕ) → List ℕ
  | [] => []
  | r :: rs => GM06DrawingData.listWords r.1 ++ GM06DrawingData.listWords r.2 ++ gm06RegionWords rs

/-- Skip the two boundary lists of each counted region. -/
def gm06SkipRegionsProg (a : Arr) (r_pos r_len r_count : Reg) : Cmd :=
  .while (.reg r_count)
    (.seq (gm06SkipListProg a r_pos r_len)
      (.seq (gm06SkipListProg a r_pos r_len)
        (.assign r_count (.op .sub (.reg r_count) (.const 1)))))

/-- Region parsing costs at most `32 * regionCount + 1` RAM steps. It
stops exactly at the cuff section and changes only its three registers. -/
theorem gm06SkipRegionsProg_exec {w a off : ℕ} (r_pos r_len r_count : ℕ)
    (hpl : r_pos ≠ r_len) (hcp : r_count ≠ r_pos) (hcl : r_count ≠ r_len)
    (rs : List (List ℕ × List ℕ)) (tail : List ℕ) (hw : 1 < 2 ^ w)
    (hcountw : rs.length < 2 ^ w) (hend : off + (gm06RegionWords rs).length < 2 ^ w)
    {s : State} (hstream : AtStream a off (gm06RegionWords rs ++ tail) s)
    (hpos : s.regs r_pos = off) (hcount : s.regs r_count = rs.length) :
    ∃ s' t, Exec w (gm06SkipRegionsProg a r_pos r_len r_count) s s' t ∧
      t ≤ 32 * rs.length + 1 ∧
      s'.regs r_pos = off + (gm06RegionWords rs).length ∧ s'.regs r_count = 0 ∧
      AtStream a (off + (gm06RegionWords rs).length) tail s' ∧
      (∀ b, s'.arrs b = s.arrs b) ∧
      (∀ r, r ≠ r_pos → r ≠ r_len → r ≠ r_count → s'.regs r = s.regs r) := by
  induction rs generalizing off s with
  | nil =>
    have h0 : 0 < 2 ^ w := lt_trans Nat.zero_lt_one hw
    have hc : (Expr.reg r_count).eval w s = some 0 := by
      simp only [Expr.eval, hcount, List.length_nil, checkWord, h0, ↓reduceIte]
    refine ⟨s, 1, .while_false hc, by simp, ?_, ?_, ?_, fun _ => rfl, fun _ _ _ _ => rfl⟩
    · simpa only [gm06RegionWords, List.length_nil, Nat.add_zero] using hpos
    · exact hcount
    · simpa only [gm06RegionWords, List.nil_append, List.length_nil, Nat.add_zero] using hstream
  | cons r rs ih =>
    have htotal : off + 1 + r.1.length + 1 + r.2.length + (gm06RegionWords rs).length < 2 ^ w := by
      simpa only [gm06RegionWords, List.length_append, GM06DrawingData.listWords,
        List.length_cons, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hend
    have hstream₀ : AtStream a off (GM06DrawingData.listWords r.1 ++
        (GM06DrawingData.listWords r.2 ++ (gm06RegionWords rs ++ tail))) s := by
      simpa only [gm06RegionWords, List.append_assoc] using hstream
    obtain ⟨s₁, t₁, hex₁, ht₁, hpos₁, _, hstream₁, harr₁, hreg₁⟩ :=
      gm06SkipListProg_exec r_pos r_len hpl hw (by omega) hstream₀ hpos
    obtain ⟨s₂, t₂, hex₂, ht₂, hpos₂, _, hstream₂, harr₂, hreg₂⟩ :=
      gm06SkipListProg_exec r_pos r_len hpl hw (by omega) hstream₁ hpos₁
    have hcount₂ : s₂.regs r_count = rs.length + 1 := by
      rw [hreg₂ r_count hcp hcl, hreg₁ r_count hcp hcl, hcount, List.length_cons]
    have hsuccw : rs.length + 1 < 2 ^ w := hcountw
    have hrestw : rs.length < 2 ^ w := lt_trans (Nat.lt_succ_self rs.length) hsuccw
    have heval : (Expr.op .sub (.reg r_count) (.const 1)).eval w s₂ = some rs.length := by
      simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hcount₂, hsuccw, hrestw, hw]
    let s₃ := s₂.setReg r_count rs.length
    have hex₃ : Exec w (.assign r_count (.op .sub (.reg r_count) (.const 1))) s₂ s₃ 4 :=
      .assign heval
    have hpos₃ : s₃.regs r_pos = off + 1 + r.1.length + 1 + r.2.length := by
      simpa only [s₃, State.setReg_regs_ne _ _ hcp.symm] using hpos₂
    have hcount₃ : s₃.regs r_count = rs.length := State.setReg_regs_self _ _ _
    have hstream₃ : AtStream a (off + 1 + r.1.length + 1 + r.2.length)
        (gm06RegionWords rs ++ tail) s₃ := hstream₂.of_arr_eq rfl
    obtain ⟨s₄, t₄, hex₄, ht₄, hpos₄, hcount₄, hstream₄, harr₄, hreg₄⟩ :=
      ih hrestw htotal hstream₃ hpos₃ hcount₃
    have hcond : (Expr.reg r_count).eval w s = some (rs.length + 1) := by
      simp only [Expr.eval, hcount, List.length_cons, checkWord, hsuccw, ↓reduceIte]
    have hoff : off + (gm06RegionWords (r :: rs)).length =
        off + 1 + r.1.length + 1 + r.2.length + (gm06RegionWords rs).length := by
      simp only [gm06RegionWords, List.length_append, GM06DrawingData.listWords,
        List.length_cons]
      omega
    refine ⟨s₄, 1 + (t₁ + (t₂ + 4)) + t₄,
      .while_true hcond (Nat.succ_ne_zero _) (.seq hex₁ (.seq hex₂ hex₃)) hex₄,
      ?_, ?_, hcount₄, ?_, ?_, ?_⟩
    · simp only [List.length_cons]
      omega
    · exact hpos₄.trans hoff.symm
    · exact hoff.symm ▸ hstream₄
    · intro b
      rw [harr₄ b]
      exact (harr₂ b).trans (harr₁ b)
    · intro q hqp hql hqc
      rw [hreg₄ q hqp hql hqc]
      change (s₂.setReg r_count rs.length).regs q = s.regs q
      rw [State.setReg_regs_ne _ _ hqc, hreg₂ q hqp hql, hreg₁ q hqp hql]

end GraphMinor.Compute
