module

public import GraphMinor.Compute.GM06Alg34EndsStep
public import GraphMinor.Compute.GM06Alg34EdgeMaskLoop

/-!
# Scanning old edges to emit the new endpoint section

Scan consecutive supplied edge labels and apply the conditional emitter
to each pair in the endpoint stream. The output is the finite left fold
of those exact updates. All masks and rank tables are preserved, and
the total cost is linear in the scanned edge count.
-/

@[expose] public section
namespace GraphMinor.Compute

/-- Emit the endpoint pairs counted in register 134, with old index in 135. -/
def gm06EndsLoopProg : Cmd :=
  .while (.reg 134) (.seq gm06EndsStepProg
    (.seq (.assign 135 (.op .add (.reg 135) (.const 1)))
      (.assign 134 (.op .sub (.reg 134) (.const 1)))))

/-- The endpoint scan performs exactly the finite successive pair updates.
The label-order hypothesis states which supplied stream is being scanned. -/
theorem gm06EndsLoopProg_exec {w off k : ℕ} (x : GM06DrawingData)
    (vs : List (Fin x.n)) (L : List (Fin x.ends.length)) (tail : List ℕ)
    (hw : 1 < 2 ^ w) (hn : x.n < 2 ^ w) (hm : x.ends.length < 2 ^ w)
    (hoff : off + 2 * L.length < 2 ^ w) (hk : k + L.length < 2 ^ w)
    (hout : 2 * (x.activeEdges vs).length < 2 ^ w)
    (hlabels : L.map Fin.val = List.range' k L.length) {s : State}
    (hstream : AtStream 0 off (gm06EdgeStream x L ++ tail) s)
    (hpos : s.regs 103 = off) (hindex : s.regs 135 = k) (hcount : s.regs 134 = L.length)
    (hV : s.arrs 5 = gm06VertexRanks vs) (hE : s.arrs 7 = gm06EdgeRanks x vs)
    (hmask : s.arrs 6 = gm06EdgeMask x vs)
    (hcap : (s.arrs 8).length = 2 * (x.activeEdges vs).length) :
    ∃ s' t, Exec w gm06EndsLoopProg s s' t ∧ t ≤ 45 * L.length + 1 ∧
      s'.arrs 8 = L.foldl (fun dst e => gm06RelabelEndsWrite x vs e dst) (s.arrs 8) ∧
      s'.regs 103 = off + 2 * L.length ∧ s'.regs 135 = k + L.length ∧
      s'.regs 134 = 0 ∧ AtStream 0 (off + 2 * L.length) tail s' ∧
      (∀ a : ℕ, a ≠ 8 → s'.arrs a = s.arrs a) ∧
      (∀ q : ℕ, q ≠ 103 → q ≠ 132 → q ≠ 133 → q ≠ 134 → q ≠ 135 →
        s'.regs q = s.regs q) := by
  induction L generalizing off k s with
  | nil =>
    have hcond : (Expr.reg 134).eval w s = some 0 := by
      simp [Expr.eval, checkWord, hcount, Nat.zero_lt_of_lt hw]
    exact ⟨s, 1, .while_false hcond, by simp, rfl, by simpa using hpos,
      by simpa using hindex, hcount, by simpa [gm06EdgeStream] using hstream,
      fun _ _ => rfl, fun _ _ _ _ _ _ => rfl⟩
  | cons e L ih =>
    have hlabel : e.val = k ∧ L.map Fin.val = List.range' (k + 1) L.length := by
      apply List.cons.inj
      simpa only [List.map_cons, List.length_cons, List.range'_succ] using hlabels
    have hLw : L.length < 2 ^ w := by simp only [List.length_cons] at hk; omega
    have hL1w : L.length + 1 < 2 ^ w := by simp only [List.length_cons] at hk; omega
    have hkw : k < 2 ^ w := by omega
    have hk1w : k + 1 < 2 ^ w := by simp only [List.length_cons] at hk; omega
    have hstream₀ : AtStream 0 off
        (x.ends[e].1.val :: x.ends[e].2.val :: (gm06EdgeStream x L ++ tail)) s := by
      simpa only [gm06EdgeStream, List.flatMap_cons, List.cons_append, List.nil_append,
        List.append_assoc] using hstream
    obtain ⟨s₁, t₁, he₁, ht₁, hout₁, hp₁, hs₁, ha₁, hr₁⟩ :=
      gm06EndsStepProg_exec x vs e (gm06EdgeStream x L ++ tail) hw hn hm
        (by simp only [List.length_cons] at hoff; omega) hout hstream₀ hpos
        (hindex.trans hlabel.1.symm) hV hE hmask hcap
    have hi₁ : s₁.regs 135 = k :=
      (hr₁ 135 (by decide) (by decide) (by decide)).trans hindex
    have hc₁ : s₁.regs 134 = L.length + 1 := by
      simpa only [List.length_cons] using
        (hr₁ 134 (by decide) (by decide) (by decide)).trans hcount
    let s₂ := s₁.setReg 135 (k + 1)
    have he₂ : Exec w (.assign 135 (.op .add (.reg 135) (.const 1))) s₁ s₂ 4 :=
      .assign (by simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hi₁, hkw, hw, hk1w])
    let s₃ := s₂.setReg 134 L.length
    have he₃ : Exec w (.assign 134 (.op .sub (.reg 134) (.const 1))) s₂ s₃ 4 :=
      .assign (by simp [s₂, Expr.eval, BinOp.eval, BinOp.raw, checkWord, hc₁, hL1w, hw, hLw])
    have hp₃ : s₃.regs 103 = off + 2 := by simp [s₃, s₂, hp₁]
    have hi₃ : s₃.regs 135 = k + 1 := by simp [s₃, s₂]
    have hs₃ : AtStream 0 (off + 2) (gm06EdgeStream x L ++ tail) s₃ := hs₁.of_arr_eq rfl
    have hcap₃ : (s₃.arrs 8).length = 2 * (x.activeEdges vs).length := by
      change (s₁.arrs 8).length = _
      rw [hout₁, gm06RelabelEndsWrite_length, hcap]
    obtain ⟨s₄, t₄, he₄, ht₄, hout₄, hp₄, hi₄, hc₄, hs₄, ha₄, hr₄⟩ :=
      ih (off := off + 2) (k := k + 1) (s := s₃)
        (by simp only [List.length_cons] at hoff; omega)
        (by simp only [List.length_cons] at hk; omega) hlabel.2
        hs₃ hp₃ hi₃ (by simp [s₃])
        ((ha₁ 5 (by decide)).trans hV) ((ha₁ 7 (by decide)).trans hE)
        ((ha₁ 6 (by decide)).trans hmask) hcap₃
    have hcond : (Expr.reg 134).eval w s = some (L.length + 1) := by
      simp [Expr.eval, checkWord, hcount, hL1w]
    have he : Exec w gm06EndsLoopProg s s₄ ((1 + (t₁ + (4 + 4))) + t₄) :=
      .while_true hcond (by omega) (.seq he₁ (.seq he₂ he₃)) he₄
    refine ⟨s₄, _, he, by simp only [List.length_cons]; omega, ?_, ?_, ?_, hc₄, ?_, ?_, ?_⟩
    · rw [hout₄]
      change L.foldl _ (s₁.arrs 8) = _
      rw [hout₁]
      rfl
    · simp only [List.length_cons]
      omega
    · simp only [List.length_cons]
      omega
    · convert hs₄ using 1 <;> simp only [List.length_cons] <;> omega
    · intro a ha
      exact (ha₄ a ha).trans (ha₁ a ha)
    · intro q hq hqA hqB hqc hqi
      rw [hr₄ q hq hqA hqB hqc hqi]
      change (s₂.setReg 134 L.length).regs q = _
      rw [State.setReg_regs_ne _ _ hqc, State.setReg_regs_ne _ _ hqi]
      exact hr₁ q hq hqA hqB

end GraphMinor.Compute
