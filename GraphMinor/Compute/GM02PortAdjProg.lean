module

public import GraphMinor.Compute.GM02OldPortAdjProg
public import GraphMinor.Compute.GM02EdgePortAdjProg
import GraphMinor.Compute.GM02FullPortNonadjacency
import GraphMinor.Compute.CrossingOpsBasic

/-!
# The complete increasing-pair split adjacency command

Classify each increasing numeric vertex pair by its old, edge, or
terminal ranges. Only old-to-edge and edge-to-terminal pairs can be
adjacent. Run their checked commands in those cases and return zero in
all other cases. Every branch preserves the arrays and pair counters.
-/

public section
namespace GraphMinor.Compute
open GraphMinor.Compute.Crossing Classical

/-- Compute split adjacency for an increasing pair in registers 60 and 61. -/
@[expose] def gm02PortAdjProg (src : Arr) : Cmd :=
  .ite (.op .lt (.reg 61) (.reg 10)) (.assign 63 (.const 0))
    (.ite (.op .lt (.reg 60) (.reg 10))
      (.ite (.op .lt (.reg 61) (.op .add (.reg 10) (.reg 11)))
        (gm02OldPortAdjProg src) (.assign 63 (.const 0)))
      (.ite (.op .lt (.reg 60) (.op .add (.reg 10) (.reg 11)))
        (.ite (.op .lt (.reg 61) (.op .add (.reg 10) (.reg 11)))
          (.assign 63 (.const 0)) gm02EdgePortAdjProg)
        (.assign 63 (.const 0))))

private theorem exec_ite_bound {w : ℕ} {cond : Expr} {yes no : Cmd} {s : State}
    (P : Prop) [Decidable P] (R : State → Prop) (B : ℕ)
    (hc : cond.eval w s = some (if P then 1 else 0))
    (hy : P → ∃ s' t, Exec w yes s s' t ∧ t ≤ B ∧ R s')
    (hn : ¬P → ∃ s' t, Exec w no s s' t ∧ t ≤ B ∧ R s') :
    ∃ s' t, Exec w (.ite cond yes no) s s' t ∧ t ≤ cond.cost + B ∧ R s' := by
  by_cases hp : P
  · obtain ⟨s', t, he, ht, hr⟩ := hy hp
    exact ⟨s', cond.cost + t, .ite_true (by simpa only [hp, ↓reduceIte] using hc)
      (by decide) he, Nat.add_le_add_left ht _, hr⟩
  · obtain ⟨s', t, he, ht, hr⟩ := hn hp
    exact ⟨s', cond.cost + t, .ite_false (by simpa only [hp, ↓reduceIte] using hc) he,
      Nat.add_le_add_left ht _, hr⟩

/-- The range-classifying adjacency command returns the exact bit in at most 65 steps. -/
theorem gm02PortAdjProg_exec {w K code : ℕ} (x : GM02TopologicalInput) (s : State)
    (src : Arr) (gflags hflags : List ℕ) (u v : Fin (gm02FullPortSize x K)) (huv : u.val < v.val)
    (hsrc : s.arrs src = x.enc) (hG : s.arrs 20 = gflags)
    (hGlen : gflags.length = x.G.edges.length) (hGbits : ∀ b ∈ gflags, b ≤ 1)
    (hH : s.arrs 21 = hflags) (hHlen : hflags.length = x.edges.length)
    (hHbits : ∀ b ∈ hflags, b ≤ 1) (hmask : s.arrs 22 = bitSetList x.vertices)
    (hslots : s.arrs 23 = List.ofFn (fun i : Fin (2 * K) => gm02SeparatorDigit x.G.edges.length code i.val))
    (hu : s.regs 60 = u.val) (hv : s.regs 61 = v.val)
    (hn : s.regs 10 = x.G.n) (hm : s.regs 11 = x.G.edges.length) (hf : s.regs 15 = x.edges.length)
    (hw : 2 < 2 ^ w) (hN : gm02FullPortSize x K < 2 ^ w)
    (hfw : x.edges.length < 2 ^ w) (henc : x.enc.length < 2 ^ w) :
    ∃ s' t, Exec w (gm02PortAdjProg src) s s' t ∧ t ≤ 65 ∧
      s'.regs 63 = (if (gm02FullPortGraph x gflags hflags code K).Adj u v then 1 else 0) ∧
      s'.arrs = s.arrs ∧
      (∀ r, r ≠ 32 → r ≠ 42 → r ≠ 43 → r ≠ 44 → r ≠ 45 → r ≠ 46 →
        r ≠ 62 → r ≠ 63 → s'.regs r = s.regs r) := by
  let F := gm02FullPortGraph x gflags hflags code K
  let R : State → Prop := fun st => st.regs 63 = (if F.Adj u v then 1 else 0) ∧
    st.arrs = s.arrs ∧ (∀ r, r ≠ 32 → r ≠ 42 → r ≠ 43 → r ≠ 44 → r ≠ 45 → r ≠ 46 →
      r ≠ 62 → r ≠ 63 → st.regs r = s.regs r)
  have hnw : x.G.n < 2 ^ w := by unfold gm02FullPortSize at hN; omega
  have hmw : x.G.edges.length < 2 ^ w := by unfold gm02FullPortSize at hN; omega
  have hKw : 2 * K < 2 ^ w := by unfold gm02FullPortSize at hN; omega
  have hsum : x.G.n + x.G.edges.length < 2 ^ w := by unfold gm02FullPortSize at hN; omega
  have huw : u.val < 2 ^ w := u.isLt.trans hN
  have hvw : v.val < 2 ^ w := v.isLt.trans hN
  have hU := u.isLt
  have hV := v.isLt
  have hw1 : 1 < 2 ^ w := by omega
  have hVn := eval_lt (eval_reg hv hvw) (eval_reg hn hnw) hw1
  have hUn := eval_lt (eval_reg hu huw) (eval_reg hn hnw) hw1
  have hVs := eval_lt (eval_reg hv hvw) (eval_add (eval_reg hn hnw) (eval_reg hm hmw) hsum) hw1
  have hUs := eval_lt (eval_reg hu huw) (eval_add (eval_reg hn hnw) (eval_reg hm hmw) hsum) hw1
  have hzero (B : ℕ) (hB : 2 ≤ B) (hnot : ¬ F.Adj u v) :
      ∃ st t, Exec w (.assign 63 (.const 0)) s st t ∧ t ≤ B ∧ R st := by
    refine ⟨s.setReg 63 0, 2, .assign (eval_const (by omega)), hB, ?_⟩
    refine ⟨?_, rfl, ?_⟩
    · simp only [State.setReg_regs_self, hnot, ite_false]
    · intro r _ _ _ _ _ _ _ hr63
      exact State.setReg_regs_ne s 0 hr63
  change ∃ st t, Exec w (gm02PortAdjProg src) s st t ∧ t ≤ 65 ∧ R st
  apply exec_ite_bound (v.val < x.G.n) R 62 hVn
  · intro hvn
    apply hzero 62 (by decide)
    have hun : u.val < x.G.n := huv.trans hvn
    exact gm02FullPortGraph_not_adj_old_old x gflags hflags code K ⟨u.val, hun⟩ ⟨v.val, hvn⟩
  · intro hvn
    apply exec_ite_bound (u.val < x.G.n) R 59 hUn
    · intro hun
      apply exec_ite_bound (v.val < x.G.n + x.G.edges.length) R 54 hVs
      · intro hvs
        let a : Fin x.G.n := ⟨u.val, hun⟩
        let e : Fin x.G.edges.length := ⟨v.val - x.G.n, by omega⟩
        have heq : gm02FullPortEdge x K e = v := by apply Fin.ext; change x.G.n + (v.val - x.G.n) = v.val; omega
        obtain ⟨st, t, he, ht, hout, harr, hr⟩ := gm02OldPortAdjProg_exec x s src gflags hflags code K a e
          hsrc hG hGlen hGbits hmask hu (by rw [hv]; change v.val = x.G.n + (v.val - x.G.n); omega)
          hn hm hw hnw hmw (by change x.G.n + (v.val - x.G.n) < 2 ^ w; omega) henc
        refine ⟨st, t, he, by omega, ?_, harr, ?_⟩
        · have huq : gm02FullPortOld x K a = u := Fin.ext rfl
          simpa only [huq, heq] using hout
        · intro r hr32 hr42 _ hr44 hr45 hr46 _ hr63
          exact hr r hr32 hr42 hr44 hr45 hr46 hr63
      · intro hvs
        apply hzero 54 (by decide)
        let p : Fin (2 * K) := ⟨v.val - (x.G.n + x.G.edges.length), by unfold gm02FullPortSize at hV; omega⟩
        have heq : gm02FullPortTerminal x K p = v := by
          apply Fin.ext
          change x.G.n + x.G.edges.length + (v.val - (x.G.n + x.G.edges.length)) = v.val
          omega
        have huq : gm02FullPortOld x K ⟨u.val, hun⟩ = u := Fin.ext rfl
        simpa only [huq, heq] using gm02FullPortGraph_not_adj_old_terminal x gflags hflags code K ⟨u.val, hun⟩ p
    · intro hun
      apply exec_ite_bound (u.val < x.G.n + x.G.edges.length) R 54 hUs
      · intro hus
        apply exec_ite_bound (v.val < x.G.n + x.G.edges.length) R 49 hVs
        · intro hvs
          apply hzero 49 (by decide)
          let e : Fin x.G.edges.length := ⟨u.val - x.G.n, by omega⟩
          let f : Fin x.G.edges.length := ⟨v.val - x.G.n, by omega⟩
          have heq : gm02FullPortEdge x K e = u := by apply Fin.ext; change x.G.n + (u.val - x.G.n) = u.val; omega
          have hfq : gm02FullPortEdge x K f = v := by apply Fin.ext; change x.G.n + (v.val - x.G.n) = v.val; omega
          simpa only [heq, hfq] using gm02FullPortGraph_not_adj_edge_edge x gflags hflags code K e f
        · intro hvs
          let e : Fin x.G.edges.length := ⟨u.val - x.G.n, by omega⟩
          let p : Fin (2 * K) := ⟨v.val - (x.G.n + x.G.edges.length), by unfold gm02FullPortSize at hV; omega⟩
          have heq : gm02FullPortEdge x K e = u := by apply Fin.ext; change x.G.n + (u.val - x.G.n) = u.val; omega
          have hpq : gm02FullPortTerminal x K p = v := by
            apply Fin.ext
            change x.G.n + x.G.edges.length + (v.val - (x.G.n + x.G.edges.length)) = v.val
            omega
          obtain ⟨st, t, he, ht, hout, harr, hr⟩ := gm02EdgePortAdjProg_exec x s gflags hflags e p
            hG hGlen hGbits hH hHlen hHbits hslots
            (by rw [hu]; change u.val = x.G.n + (u.val - x.G.n); omega)
            (by rw [hv]; change v.val = x.G.n + x.G.edges.length + (v.val - (x.G.n + x.G.edges.length)); omega)
            hn hm hf hw hnw hmw hfw hKw
            (by change x.G.n + (u.val - x.G.n) < 2 ^ w; omega)
            (by change x.G.n + x.G.edges.length + (v.val - (x.G.n + x.G.edges.length)) < 2 ^ w; omega)
          refine ⟨st, t, he, by omega, ?_, harr, ?_⟩
          · simpa only [heq, hpq] using hout
          · intro r hr32 _ hr43 _ _ _ hr62 hr63
            exact hr r hr32 hr43 hr62 hr63
      · intro hus
        apply hzero 54 (by decide)
        let p : Fin (2 * K) := ⟨u.val - (x.G.n + x.G.edges.length), by unfold gm02FullPortSize at hU; omega⟩
        let q : Fin (2 * K) := ⟨v.val - (x.G.n + x.G.edges.length), by unfold gm02FullPortSize at hV; omega⟩
        have hpq : gm02FullPortTerminal x K p = u := by
          apply Fin.ext
          change x.G.n + x.G.edges.length + (u.val - (x.G.n + x.G.edges.length)) = u.val
          omega
        have hqq : gm02FullPortTerminal x K q = v := by
          apply Fin.ext
          change x.G.n + x.G.edges.length + (v.val - (x.G.n + x.G.edges.length)) = v.val
          omega
        simpa only [hpq, hqq] using gm02FullPortGraph_not_adj_terminal_terminal x gflags hflags code K p q

end GraphMinor.Compute
