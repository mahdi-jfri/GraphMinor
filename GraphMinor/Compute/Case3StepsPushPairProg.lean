module

public import GraphMinor.Compute.Case3StepsPushEncoding
public import GraphMinor.Compute.Case3StepsParallelCopies
import GraphMinor.Compute.TwoPathsRotate

/-!
# Writing one pair in original ambient labels

The source member record supplies both compact endpoints and the complete
multiplicity. The inverse compass list changes the endpoints. Three writes
place the restored pair record in its canonical position without expanding
or truncating its parallel class.
-/

@[expose] public section

namespace GraphMinor.Compute

/-- Restore pair 103 from member array 39 to ambient member array 54. -/
def case3PushPairProg : Cmd :=
  .seq (.assign 116 (.op .add (.const 2) (.op .mul (.const 3) (.reg 103))))
    (.seq (.write 54 (.reg 116) (.read 32 (.read 39 (.reg 116))))
      (.seq (.write 54 (.op .add (.reg 116) (.const 1))
        (.read 32 (.read 39 (.op .add (.reg 116) (.const 1)))))
        (.write 54 (.op .add (.reg 116) (.const 2))
          (.read 39 (.op .add (.reg 116) (.const 2))))))

/-- One restored pair takes twenty-eight steps and retains its full
multiplicity, all surrounding records, and every other array. -/
theorem case3PushPairProg_exec {w N : ℕ} (S : Finset (Fin N)) (D : MultiDigraph S.card)
    (j : Fin D.numActivePairs) (pre suf : List ℕ) (hpre : pre.length = 2 + 3 * j.1)
    (hw : 3 < 2 ^ w) (hcard : S.card < 2 ^ w) (hN : N < 2 ^ w)
    (hA : 2 + 3 * D.numActivePairs < 2 ^ w) (he : D.numEdges < 2 ^ w)
    {s : State} (hD : s.arrs 39 = D.enc) (hlistlen : S.card ≤ (s.arrs 32).length)
    (hlist : ∀ i : Fin S.card, (s.arrs 32).getD i.1 0 = (S.orderEmbOfFin rfl i).1)
    (hdst : s.arrs 54 = pre ++ [0, 0, 0] ++ suf) (hrj : s.regs 103 = j.1) :
    ∃ s', Exec w case3PushPairProg s s' 28 ∧
      s'.arrs 54 = pre ++ [(S.orderEmbOfFin rfl (D.activePairsList[j.1]).1).1,
        (S.orderEmbOfFin rfl (D.activePairsList[j.1]).2).1,
        D.edgeMult (D.activePairsList[j.1]).1 (D.activePairsList[j.1]).2] ++ suf ∧
      (∀ a, a ≠ 54 → s'.arrs a = s.arrs a) ∧
      (∀ r, r ≠ 116 → s'.regs r = s.regs r) := by
  let p := D.activePairsList[j.1]
  have h1 : 1 < 2 ^ w := by omega
  have h2 : 2 < 2 ^ w := by omega
  have hjw : j.1 < 2 ^ w := by have hj := j.2; omega
  have hmul : 3 * j.1 < 2 ^ w := by have hj := j.2; omega
  have hpw : pre.length < 2 ^ w := by have hj := j.2; omega
  have hp1w : pre.length + 1 < 2 ^ w := by have hj := j.2; omega
  have hp2w : pre.length + 2 < 2 ^ w := by have hj := j.2; omega
  obtain ⟨hpu, hvalu⟩ := enc_getElem_triple_fst D [] (by simpa only [List.append_nil] using hD) j.2
  obtain ⟨hpv, hvalv⟩ := enc_getElem_triple_snd D [] (by simpa only [List.append_nil] using hD) j.2
  obtain ⟨hpm, hvalm⟩ := enc_getElem_triple_mult D [] (by simpa only [List.append_nil] using hD) j.2
  have hpu' : pre.length < (s.arrs 39).length := by simpa only [hpre] using hpu
  have hpv' : pre.length + 1 < (s.arrs 39).length := by simpa only [hpre] using hpv
  have hpm' : pre.length + 2 < (s.arrs 39).length := by simpa only [hpre] using hpm
  have hvaluD : (s.arrs 39).getD (2 + 3 * j.1) 0 = p.1.1 := by
    rw [List.getD_eq_getElem _ _ hpu]
    exact hvalu
  have hvalvD : (s.arrs 39).getD (2 + 3 * j.1 + 1) 0 = p.2.1 := by
    rw [List.getD_eq_getElem _ _ hpv]
    exact hvalv
  have hvalmD : (s.arrs 39).getD (2 + 3 * j.1 + 2) 0 = D.edgeMult p.1 p.2 := by
    rw [List.getD_eq_getElem _ _ hpm]
    exact hvalm
  have hvalu' : (s.arrs 39)[pre.length]'hpu' = p.1.1 := by
    rw [← List.getD_eq_getElem _ 0 hpu', hpre]
    exact hvaluD
  have hvalv' : (s.arrs 39)[pre.length + 1]'hpv' = p.2.1 := by
    rw [← List.getD_eq_getElem _ 0 hpv', hpre]
    exact hvalvD
  have hvalm' : (s.arrs 39)[pre.length + 2]'hpm' = D.edgeMult p.1 p.2 := by
    rw [← List.getD_eq_getElem _ 0 hpm', hpre]
    exact hvalmD
  have hlookup (u : Fin S.card) :
      (s.arrs 32)[u.1]'(lt_of_lt_of_le u.2 hlistlen) = (S.orderEmbOfFin rfl u).1 := by
    rw [← List.getD_eq_getElem _ 0 (lt_of_lt_of_le u.2 hlistlen)]
    exact hlist u
  have huw : p.1.1 < 2 ^ w := p.1.2.trans hcard
  have hvw : p.2.1 < 2 ^ w := p.2.2.trans hcard
  have hou : (S.orderEmbOfFin rfl p.1).1 < 2 ^ w := (S.orderEmbOfFin rfl p.1).2.trans hN
  have hov : (S.orderEmbOfFin rfl p.2).1 < 2 ^ w := (S.orderEmbOfFin rfl p.2).2.trans hN
  have hmw : D.edgeMult p.1 p.2 < 2 ^ w := (D.edgeMult_le_numEdges _ _).trans_lt he
  let s₀ := s.setReg 116 pre.length
  let s₁ := s₀.writeArr 54 pre.length (S.orderEmbOfFin rfl p.1).1
  let s₂ := s₁.writeArr 54 (pre.length + 1) (S.orderEmbOfFin rfl p.2).1
  let s₃ := s₂.writeArr 54 (pre.length + 2) (D.edgeMult p.1 p.2)
  have hex₀ : Exec w (.assign 116 (.op .add (.const 2) (.op .mul (.const 3) (.reg 103)))) s s₀ 6 :=
    .assign (by simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hrj, h2, hw, hjw, hmul, ← hpre, hpw])
  have hread_u : (Expr.read 32 (.read 39 (.reg 116))).eval w s₀ = some (S.orderEmbOfFin rfl p.1).1 := by
    simp [Expr.eval, checkWord, s₀, hpw, hpu', hvalu', huw,
      lt_of_lt_of_le p.1.2 hlistlen, hlookup p.1, hou]
  have hex₁ : Exec w (.write 54 (.reg 116) (.read 32 (.read 39 (.reg 116)))) s₀ s₁ 5 :=
    .write (by simp only [Expr.eval, checkWord, s₀, State.setReg_regs_self, hpw, ↓reduceIte]) hread_u
      (by simp only [s₀, State.setReg_arrs, hdst, List.length_append, List.length_cons, List.length_nil]; omega)
  have hread_v : (Expr.read 32 (.read 39 (.op .add (.reg 116) (.const 1)))).eval w s₁ =
      some (S.orderEmbOfFin rfl p.2).1 := by
    simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, s₁, s₀, hpw, h1, hp1w,
      hpv', hvalv', hvw, lt_of_lt_of_le p.2.2 hlistlen, hlookup p.2, hov]
  have hex₂ : Exec w (.write 54 (.op .add (.reg 116) (.const 1))
      (.read 32 (.read 39 (.op .add (.reg 116) (.const 1))))) s₁ s₂ 9 :=
    .write (by simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, s₁, s₀, hpw, h1, hp1w]) hread_v
      (by simp only [s₁, s₀, State.writeArr_arrs_self, State.setReg_arrs, List.length_set,
        hdst, List.length_append, List.length_cons, List.length_nil]; omega)
  have hread_m : (Expr.read 39 (.op .add (.reg 116) (.const 2))).eval w s₂ = some (D.edgeMult p.1 p.2) := by
    simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, s₂, s₁, s₀, hpw, h2, hp2w, hpm', hvalm', hmw]
  have hex₃ : Exec w (.write 54 (.op .add (.reg 116) (.const 2))
      (.read 39 (.op .add (.reg 116) (.const 2)))) s₂ s₃ 8 :=
    .write (by simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, s₂, s₁, s₀, hpw, h2, hp2w]) hread_m
      (by simp only [s₂, s₁, s₀, State.writeArr_arrs_self, State.setReg_arrs, List.length_set,
        hdst, List.length_append, List.length_cons, List.length_nil]; omega)
  have hex : Exec w case3PushPairProg s s₃ 28 := .seq hex₀ (.seq hex₁ (.seq hex₂ hex₃))
  refine ⟨s₃, hex, ?_, ?_, ?_⟩
  · simp only [s₃, s₂, s₁, s₀, State.writeArr_arrs_self, State.setReg_arrs, hdst]
    exact case3TripleBuffer_set pre suf _ _ _
  · intro a ha
    exact hex.arrs_eq_of_not_mem_writtenArrs (by simp [case3PushPairProg, Cmd.writtenArrs, ha])
  · intro r hr
    exact hex.regs_eq_of_not_mem_writtenRegs (by simp [case3PushPairProg, Cmd.writtenRegs, hr])

end GraphMinor.Compute
