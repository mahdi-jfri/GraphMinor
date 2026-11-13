module

public import GraphMinor.Compute.Case3StepsOriginalMemberVerticesProg
public import GraphMinor.Compute.MultiDigraph

/-!
# Reading a member pair in original labels

A saved compact member encoding supplies its two endpoints and full
multiplicity. Its ordered inverse vertex list maps the endpoints to the
original labels. These three values feed the parallel-copy expansion scan.
-/

@[expose] public section

namespace GraphMinor.Compute

/-- Read compact pair 103 from array 38 and map its endpoints through 47. -/
def case3ReadMappedPairProg : Cmd :=
  .seq (readTripleEndpoints 38 103 104 106 107)
    (.seq (.assign 108 (.read 38 (.op .add (.reg 104) (.const 2))))
      (.seq (.assign 106 (.read 47 (.reg 106))) (.assign 107 (.read 47 (.reg 107)))))

/-- The mapped endpoints and unchanged multiplicity are read in constant
time. No array changes, and the outer pair and edge counters are retained. -/
theorem case3ReadMappedPairProg_exec {w n N : ℕ} (G : MultiDigraph n) (orig : Fin n → Fin N)
    (j : Fin G.numActivePairs) (hw : 3 < 2 ^ w) (hn : n < 2 ^ w) (hN : N < 2 ^ w)
    (he : G.numEdges < 2 ^ w) (hA : 2 + 3 * G.numActivePairs < 2 ^ w)
    {s : State} (hG : s.arrs 38 = G.enc)
    (hlabels : s.arrs 47 = List.ofFn (fun u : Fin n => (orig u).1)) (hrj : s.regs 103 = j.1) :
    ∃ s' t, Exec w case3ReadMappedPairProg s s' t ∧ t ≤ 25 ∧
      s'.regs 106 = (orig (G.activePairsList[j.1]).1).1 ∧
      s'.regs 107 = (orig (G.activePairsList[j.1]).2).1 ∧
      s'.regs 108 = G.edgeMult (G.activePairsList[j.1]).1 (G.activePairsList[j.1]).2 ∧
      (∀ a, s'.arrs a = s.arrs a) ∧
      (∀ r, r ≠ 104 → r ≠ 106 → r ≠ 107 → r ≠ 108 → s'.regs r = s.regs r) := by
  obtain ⟨s₁, t₁, hex₁, ht₁, hidx, hru, hrv, harr₁, hreg₁⟩ :=
    readTripleEndpoints_exec G [] 38 103 104 106 107 j.1 s (by decide) (by decide) (by decide)
      hw hn hA j.2 (by simpa only [List.append_nil] using hG) hrj
  let p := G.activePairsList[j.1]
  have h2 : 2 < 2 ^ w := by omega
  have hidxw : 2 + 3 * j.1 < 2 ^ w := by have hj := j.2; omega
  have hidx2w : 2 + 3 * j.1 + 2 < 2 ^ w := by have hj := j.2; omega
  obtain ⟨hpos, hval⟩ := enc_getElem_triple_mult G []
    (by simpa only [List.append_nil] using (harr₁ 38).trans hG) j.2
  have hmultw : G.edgeMult p.1 p.2 < 2 ^ w := (G.edgeMult_le_numEdges _ _).trans_lt he
  dsimp only [p] at hmultw
  let s₂ := s₁.setReg 108 (G.edgeMult p.1 p.2)
  let s₃ := s₂.setReg 106 (orig p.1).1
  let s₄ := s₃.setReg 107 (orig p.2).1
  have hex₂ : Exec w (.assign 108 (.read 38 (.op .add (.reg 104) (.const 2)))) s₁ s₂ 5 :=
    .assign (by
      simp only [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hidx, hidxw, hidx2w, h2, hpos, hval, ↓reduceIte, ↓reduceDIte]
      simp only [p] at *
      exact ite_eq_left hmultw)
  have hread (st : State) (u : Fin n) (r : ℕ)
      (hl : st.arrs 47 = List.ofFn (fun v : Fin n => (orig v).1)) (hr : st.regs r = u.1) :
      (Expr.read 47 (.reg r)).eval w st = some (orig u).1 := by
    have hi : u.1 < (st.arrs 47).length := by rw [hl, List.length_ofFn]; exact u.2
    have hv : (st.arrs 47)[u.1]'hi = (orig u).1 := by simp only [hl, List.getElem_ofFn]
    exact (TwoPaths.read_eval (by simp only [Expr.eval, checkWord, hr, u.2.trans hn, ↓reduceIte]) hi
      (hv ▸ (orig u).2.trans hN)).trans (congrArg some hv)
  have hex₃ : Exec w (.assign 106 (.read 47 (.reg 106))) s₂ s₃ 3 :=
    .assign (hread s₂ p.1 106 ((harr₁ 47).trans hlabels)
      (by rw [State.setReg_regs_ne _ _ (by decide)]; exact hru))
  have hex₄ : Exec w (.assign 107 (.read 47 (.reg 107))) s₃ s₄ 3 :=
    .assign (hread s₃ p.2 107 ((harr₁ 47).trans hlabels)
      (by rw [State.setReg_regs_ne _ _ (by decide), State.setReg_regs_ne _ _ (by decide)]; exact hrv))
  have hex : Exec w case3ReadMappedPairProg s s₄ (t₁ + (5 + (3 + 3))) :=
    .seq hex₁ (.seq hex₂ (.seq hex₃ hex₄))
  refine ⟨s₄, t₁ + (5 + (3 + 3)), hex, by omega, ?_, State.setReg_regs_self .., ?_, ?_, ?_⟩
  · rw [State.setReg_regs_ne _ _ (by decide), State.setReg_regs_self]
  · rw [State.setReg_regs_ne _ _ (by decide), State.setReg_regs_ne _ _ (by decide), State.setReg_regs_self]
  · intro a
    exact harr₁ a
  · intro r h104 h106 h107 h108
    rw [State.setReg_regs_ne _ _ h107, State.setReg_regs_ne _ _ h106, State.setReg_regs_ne _ _ h108]
    exact hreg₁ r h104 h106 h107

end GraphMinor.Compute
