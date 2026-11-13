module

public import GraphMinor.Compute.GM02InjectionScanBody
public import GraphMinor.Compute.GM02InjectionCodeEquivalence
import GraphMinor.Compute.CrossingOpsBasic

/-!
# The complete injection counting loop of II (4.7)

Retain an early successful containment or width answer. A zero
accumulator instead records exclusion of every earlier code. At the
end, the code-coverage theorem turns these exclusions into absence of
any isomorphic topologically contained copy of the fixed pattern.
-/

public section
namespace GraphMinor.Compute
open Graph GraphMinor.GM02 GraphMinor.Compute.Crossing

/-- Scan the full injection-code range stored in register 191. -/
@[expose] noncomputable def gm02InjectionScanProg (H : GM02EdgeListInput) (q : ℕ) : Cmd :=
  forUp 190 (.reg 191) (gm02InjectionScanBody H q)

/-- The actual candidate enumeration decides isomorphic topological containment or reports large host width. -/
theorem gm02InjectionScanProg_exec {W : ℕ} (q : ℕ) (G H : GM02EdgeListInput)
    (w : ℤ) (s : State) (hq : max w.toNat 2 + 2 * H.edges.length < q)
    (hw : 3 < 2 ^ W) (hn : G.n + 1 < 2 ^ W) (hmG : G.edges.length < 2 ^ W)
    (hcap : 1 + 2 * H.edges.length < 2 ^ W) (hlen : gm02InjectedInputLength G H < 2 ^ W)
    (hpow : (G.n + 1) ^ H.n < 2 ^ W)
    (hword : wordSize (gm02TopologicalWordCoefficient q H.edges.length) (G.size + H.size) ≤ W)
    (hG : s.arrs inArr = G.enc) (hrn : s.regs 40 = G.n)
    (hzero : s.regs 190 = 0) (hlimit : s.regs 191 = (G.n + 1) ^ H.n) (hacc : s.regs 192 = 0) :
    ∃ s' t, Exec W (gm02InjectionScanProg H q) s s' t ∧
      t ≤ 3 + (G.n + 1) ^ H.n * (gm02InjectionCodeBudget q G H + 15) ∧
      ((s'.regs 192 = 1 ∧ ∃ L : Graph ℕ ℕ, TopologicallyContains G.graph L ∧ Nonempty (Iso H.graph L)) ∨
        (s'.regs 192 = 0 ∧ ¬∃ L : Graph ℕ ℕ, TopologicallyContains G.graph L ∧ Nonempty (Iso H.graph L)) ∨
        (s'.regs 192 = 2 ∧ w < (treeWidth G.graph G.finite_vertices G.finite_edges : ℕ))) := by
  let limit := (G.n + 1) ^ H.n
  let T := ∃ L : Graph ℕ ℕ, TopologicallyContains G.graph L ∧ Nonempty (Iso H.graph L)
  let P : ℕ → Prop := fun code => ∃ hv : gm02InjectionCodeValid G.n H.n code,
    TopologicallyContains G.graph (gm02InjectedPattern G H (gm02InjectionOfCode G.n H.n code hv)).H
  let M : State → Prop := fun st => st.regs 191 = limit ∧ st.arrs inArr = G.enc ∧ st.regs 40 = G.n
  let C : ℕ → State → Prop := fun j st =>
    (st.regs 192 = 0 ∧ ∀ code < j, ¬P code) ∨
      (st.regs 192 = 1 ∧ T) ∨
      (st.regs 192 = 2 ∧ w < (treeWidth G.graph G.finite_vertices G.finite_edges : ℕ))
  let I : ℕ → State → Prop := fun j st => st.regs 190 = j ∧ M st ∧ C j st
  have hMset (st : State) (j : ℕ) (hM : M st) : M (st.setReg 190 j) := by
    rcases hM with ⟨hl, hs, hn'⟩
    exact ⟨(State.setReg_regs_ne st j (by decide : (191 : Reg) ≠ 190)).trans hl, hs,
      (State.setReg_regs_ne st j (by decide : (40 : Reg) ≠ 190)).trans hn'⟩
  have hI : I 0 s := ⟨hzero, ⟨hlimit, hG, hrn⟩,
    Or.inl ⟨hacc, fun code hc => False.elim (Nat.not_lt_zero code hc)⟩⟩
  have hTopo := gm02_exists_injectionCode_iff G H
  obtain ⟨s', t, he, ht, hi⟩ := forUp_exec' I limit (gm02InjectionCodeBudget q G H + 8)
    (r_i := 190) (hi := .reg 191) (body := gm02InjectionScanBody H q) (by omega) hpow
    (fun j hj st hst => ⟨hst.1, eval_reg hst.2.1.1 hpow⟩)
    (fun j hj st hst => by
      rcases hst with ⟨hindex, hM, hC⟩
      rcases hM with ⟨hl, hs, hn'⟩
      have hMold : M st := ⟨hl, hs, hn'⟩
      rcases hC with ⟨hacc0, hprev⟩ | hpositive
      · obtain ⟨st', tb, heb, htb, hc, hab, hrb⟩ := gm02InjectionScanBody_empty_exec q G H w st
          hq hw hn hmG hcap hlen hpow hj hword hs hn' hindex hacc0
        have hMnew : M st' :=
          ⟨(hrb 191 (by decide) (Or.inr (by decide)) (by decide)).trans hl,
            (hab inArr (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hs,
            (hrb 40 (by decide) (Or.inl (by decide)) (by decide)).trans hn'⟩
        have hCnew : C (j + 1) (st'.setReg 190 (j + 1)) := by
          have hset : (st'.setReg 190 (j + 1)).regs 192 = st'.regs 192 := State.setReg_regs_ne st' (j + 1) (by decide)
          rcases hc with ⟨hf, hp⟩ | ⟨hf, hp⟩ | ⟨hf, hp⟩
          · exact Or.inr (Or.inl ⟨hset.trans hf, hTopo.2 ⟨j, hj, hp⟩⟩)
          · refine Or.inl ⟨hset.trans hf, ?_⟩
            intro code hc hP
            rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hc) with hc | hc
            · exact hprev code hc hP
            · subst code
              obtain ⟨hv, hcontains⟩ := hP
              exact hp hv hcontains
          · exact Or.inr (Or.inr ⟨hset.trans hf, hp⟩)
        exact ⟨st', tb, heb, htb, ⟨State.setReg_regs_self .., hMset st' (j + 1) hMnew, hCnew⟩,
          (hrb 190 (by decide) (Or.inr (by decide)) (by decide)).trans hindex⟩
      · have haccne : st.regs 192 ≠ 0 := by
          rcases hpositive with ⟨hf, _⟩ | ⟨hf, _⟩ <;> rw [hf] <;> decide
        have haccw : st.regs 192 < 2 ^ W := by
          rcases hpositive with ⟨hf, _⟩ | ⟨hf, _⟩ <;> rw [hf] <;> omega
        have hguard : (Expr.op .eq (.reg 192) (.const 0)).eval W st = some 0 := by
          have hv := eval_eq (eval_reg (show st.regs 192 = st.regs 192 from rfl) haccw)
            (eval_const (by omega : 0 < 2 ^ W)) (by omega)
          simpa only [haccne, ite_false] using hv
        have hCnew : C (j + 1) (st.setReg 190 (j + 1)) := by
          have hset : (st.setReg 190 (j + 1)).regs 192 = st.regs 192 := State.setReg_regs_ne st (j + 1) (by decide)
          rcases hpositive with ⟨hf, hp⟩ | ⟨hf, hp⟩
          · exact Or.inr (Or.inl ⟨hset.trans hf, hp⟩)
          · exact Or.inr (Or.inr ⟨hset.trans hf, hp⟩)
        exact ⟨st, 4, .ite_false hguard (.skip st), by omega,
          ⟨State.setReg_regs_self .., hMset st (j + 1) hMold, hCnew⟩, hindex⟩) s hI
  refine ⟨s', t, he, ?_, ?_⟩
  · change t ≤ 3 + limit * (1 + 6 + (gm02InjectionCodeBudget q G H + 8)) at ht
    have hadd : 1 + 6 + (gm02InjectionCodeBudget q G H + 8) = gm02InjectionCodeBudget q G H + 15 := by omega
    rw [hadd] at ht
    exact ht
  · rcases hi.2.2 with ⟨hf, hnone⟩ | hpositive
    · refine Or.inr (Or.inl ⟨hf, ?_⟩)
      intro hcontains
      obtain ⟨code, hcode, hv, hcontains⟩ := hTopo.1 hcontains
      exact hnone code hcode ⟨hv, hcontains⟩
    · exact hpositive.elim Or.inl (fun h => Or.inr (Or.inr h))

end GraphMinor.Compute
