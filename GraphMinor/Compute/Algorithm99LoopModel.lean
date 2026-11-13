module

public import GraphMinor.Compute.Algorithm99Step3Model
public import GraphMinor.Compute.Algorithm99State
import GraphMinor.Compute.Algorithm94Init

/-!
# Step (3) of Algorithm (9.9): writing the model of `K_p`

Step (3) of the proof of (9.8) in Graph Minors XIII (page 104) says: "If we obtain a model of
$K_p$ in $G_i$ and hence in $G$ we stop." When (9.7) returns `0 :: encBitSetsUpTo K p` in
`outArr`, the program `alg99ModelOutProg` copies it to the scratch array `B + 6`, writes the
mapped model `1 :: encBitSetsUpTo (fun j => (K j).map orig) p` back into `outArr`
(`alg99MapModelProg`), and clears the loop flag in register `Q + 5`. The result is
`alg99ModelOutProg_exec`.
-/

@[expose] public section

namespace GraphMinor.Compute

/-- `omega` after unfolding `Reg` and `Arr`. -/
local macro "romega" : tactic => `(tactic| ((try dsimp only [Reg, Arr, inArr, outArr] at *); omega))

/-- The model branch of step (3): copy the output of (9.7) to `B + 6`, put `v = |V(G_i)|` in
register `Q + 8`, write the mapped model to `outArr`, and clear the loop flag `Q + 5`. Register
`Q + 6` holds `n`; registers `Q + 8`, `Q + 9` are scratch. -/
def alg99ModelOutProg (pp B Q : ℕ) : Cmd :=
  .seq (copyArrLoopProg outArr (B + 6) (Q + 8) (Q + 9))
    (.seq (.assign (Q + 8) (.len (B + 2)))
      (.seq (alg99MapModelProg pp (B + 6) (B + 2) outArr (Q + 8) (Q + 6) (Q + 9))
        (.assign (Q + 5) (.const 0))))

/-- **Step (3) of Algorithm (9.9)** (page 104), the model branch, on the Word RAM: from the
output `0 :: encBitSetsUpTo K p` of (9.7) and a stored state, the program writes the model
mapped by `orig` into `outArr` and clears the loop flag. -/
theorem alg99ModelOutProg_exec {w h' n s₀ pp : ℕ} {G : MultiDigraph n} {st : Alg99Iter h' G}
    (hst : st.IsValid s₀) (K : Fin pp → Finset (Fin st.v)) (B Q : ℕ) (hB : 2 ≤ B)
    (hw2 : 2 < 2 ^ w) (hp_w : pp < 2 ^ w) (hv_w : st.v < 2 ^ w) (hn_w : n < 2 ^ w)
    (hpn_w : 1 + pp * n < 2 ^ w) (hpv_w : 1 + pp * st.v < 2 ^ w)
    {s : State} (hS : st.StoredIn B s) (hout : s.arrs outArr = 0 :: encBitSetsUpTo K pp)
    (hn : s.regs (Q + 6) = n) :
    ∃ s' t, Exec w (alg99ModelOutProg pp B Q) s s' t ∧
      t ≤ 45 * (pp * st.v) + pp * n + 50 ∧
      s'.arrs outArr = 1 :: encBitSetsUpTo (fun j => (K j).map ⟨st.orig, hst.orig_injective⟩) pp ∧
      s'.regs (Q + 5) = 0 ∧
      (∀ r, r ≠ Q + 5 → r ≠ Q + 8 → r ≠ Q + 9 → s'.regs r = s.regs r) := by
  have hw1 : 1 < 2 ^ w := by omega
  have hlenK : (encBitSetsUpTo K pp).length = pp * st.v :=
    length_encBitSetsUpTo K pp le_rfl
  obtain ⟨s₁, t₁, hex₁, ht₁, h6₁, harr₁, hreg₁⟩ :=
    copyArrLoopProg_exec outArr (B + 6) (Q + 8) (Q + 9) (by romega) (by romega) hw1 s
      (by rw [hout, List.length_cons, hlenK]; exact hpv_w.trans_le' (by omega))
      (by
        rw [hout]
        intro x hx
        rcases List.mem_cons.mp hx with rfl | hx
        · omega
        · exact all_lt_encBitSetsUpTo K hw1 pp le_rfl x hx)
  rw [hout, List.length_cons, hlenK] at ht₁
  have hB2₁ : s₁.arrs (B + 2) = List.ofFn (fun u => (st.orig u).1) := by
    rw [harr₁ (B + 2) (by romega)]; exact hS.2.1
  have hlen2 : (s₁.arrs (B + 2)).length = st.v := by rw [hB2₁]; simp
  let s₂ := s₁.setReg (Q + 8) st.v
  have hex₂ : Exec w (.assign (Q + 8) (.len (B + 2))) s₁ s₂ 2 :=
    .assign (by simp only [Expr.eval, hlen2, checkWord_of_lt hv_w])
  obtain ⟨s₃, t₃, hex₃, ht₃, hout₃, -, hreg₃⟩ :=
    alg99MapModelProg_exec K st.orig hst.orig_injective (B + 6) (B + 2) outArr (Q + 8) (Q + 6)
      (Q + 9) (by romega) (by romega) (by romega) (by romega) hw2 hp_w hv_w hn_w hpn_w hpv_w
      (s := s₂) (by simp only [s₂, State.setReg_arrs]; rw [h6₁, hout])
      (by simp only [s₂, State.setReg_arrs]; exact hB2₁)
      (by simp [s₂])
      (by
        simp only [s₂, State.setReg_regs_ne _ _ (show Q + 6 ≠ Q + 8 by omega)]
        rw [hreg₁ (Q + 6) (by romega) (by romega), hn])
  have hex₄ : Exec w (.assign (Q + 5) (.const 0)) s₃ (s₃.setReg (Q + 5) 0) 2 :=
    .assign (by simp [Expr.eval, checkWord, show (0 : ℕ) < 2 ^ w by omega])
  refine ⟨s₃.setReg (Q + 5) 0, t₁ + (2 + (t₃ + 2)), .seq hex₁ (.seq hex₂ (.seq hex₃ hex₄)), ?_,
    by simpa using hout₃, by simp, fun r h5 h8 h9 => ?_⟩
  · omega
  · rw [State.setReg_regs_ne _ _ h5, hreg₃ r h9]
    simp only [s₂, State.setReg_regs_ne _ _ h8]
    exact hreg₁ r h8 h9

end GraphMinor.Compute
