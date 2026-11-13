module

public import GraphMinor.Compute.GM02PortCodeScanBody
public import GraphMinor.Compute.GM02NumericCodeEquivalence
import GraphMinor.Compute.CrossingOpsBasic

/-!
# Enumerating all raw split-choice codes

Scan the fixed polynomial range of candidate codes. While the answer
accumulator is zero, test the next code and retain a positive answer.
The zero invariant says every earlier code is infeasible. A retained
feasibility answer proves containment by the numeric-code equivalence,
and a retained width report already refers to the original host. At the
end, zero means no feasible code exists and hence no containment exists.
-/

public section
namespace GraphMinor.Compute
open Graph Set GraphMinor.GM02 GraphMinor.Compute.Crossing Classical

/-- Scan the complete candidate range stored in register 191. -/
@[expose] noncomputable def gm02PortCodeScanProg (K q : ℕ) : Cmd :=
  forUp 190 (.reg 191) (gm02PortCodeScanBody K q)

/-- The actual code enumeration decides containment or returns a justified host-width report. -/
theorem gm02PortCodeScanProg_exec {W K : ℕ} (x : GM02TopologicalInput) (s : State)
    (gflags hflags : List ℕ) (hK : x.edges.length ≤ K) {k : ℕ}
    (edge : Fin k ≃ E(gm02ActiveGraph x.H hflags)) (w : ℤ) (q : ℕ)
    (hq : max w.toNat 2 + 2 * K < q)
    (hNoLoop : ∀ e v, v ∈ V(x.H) → ¬(gm02ActiveGraph x.G.graph gflags).IsLoopAt e v)
    (hsrc : s.arrs inArr = x.enc) (hG : s.arrs 20 = gflags)
    (hGlen : gflags.length = x.G.edges.length) (hGbits : ∀ b ∈ gflags, b ≤ 1)
    (hH : s.arrs 21 = hflags) (hHlen : hflags.length = x.edges.length)
    (hHbits : ∀ b ∈ hflags, b ≤ 1) (hmask : s.arrs 22 = bitSetList x.vertices)
    (hn : s.regs 10 = x.G.n) (hm : s.regs 11 = x.G.edges.length) (hf : s.regs 15 = x.edges.length)
    (hoff : s.regs 16 = 4 + 2 * x.G.edges.length + x.vertices.card)
    (hzero : s.regs 190 = 0) (hlimit : s.regs 191 = (x.G.edges.length + 1) ^ (2 * K))
    (hacc : s.regs 192 = 0)
    (hw : 3 < 2 ^ W) (hN : gm02FullPortSize x K < 2 ^ W) (henc : x.enc.length < 2 ^ W)
    (hmw : x.G.edges.length + 1 < 2 ^ W) (hpow : (x.G.edges.length + 1) ^ (2 * K) < 2 ^ W)
    (hjoin : 3 + 2 * (gm02FullPortSize x K * gm02FullPortSize x K) + 2 * x.edges.length < 2 ^ W)
    (hword : wordSize (gm02RecursiveWordConstant q) (gm02FullPortSize x K) ≤ W) :
    ∃ s' t, Exec W (gm02PortCodeScanProg K q) s s' t ∧
      t ≤ 3 + (x.G.edges.length + 1) ^ (2 * K) * (gm02PortCodeBudget q x K + 15) ∧
      ((s'.regs 192 = 1 ∧ TopologicallyContains (gm02ActiveGraph x.G.graph gflags) (gm02ActiveGraph x.H hflags)) ∨
       (s'.regs 192 = 0 ∧ ¬TopologicallyContains (gm02ActiveGraph x.G.graph gflags) (gm02ActiveGraph x.H hflags)) ∨
       (s'.regs 192 = 2 ∧ w < treeWidth x.G.graph x.G.finite_vertices x.G.finite_edges)) := by
  let limit := (x.G.edges.length + 1) ^ (2 * K)
  let P : ℕ → Prop := fun code => ∃ hv : gm02PortAssignmentValid x gflags hflags (gm02PortAssignmentOfCode x code),
    (gm02NumericTerminatedInput x gflags hflags code K hK edge hv).A.Feasible
      (Graph.ofSimpleGraph (gm02NumericTerminatedInput x gflags hflags code K hK edge hv).G)
  let M : State → Prop := fun st => st.regs 191 = limit ∧ st.arrs inArr = x.enc ∧
    st.arrs 20 = gflags ∧ st.arrs 21 = hflags ∧ st.arrs 22 = bitSetList x.vertices ∧
    st.regs 10 = x.G.n ∧ st.regs 11 = x.G.edges.length ∧ st.regs 15 = x.edges.length ∧
    st.regs 16 = 4 + 2 * x.G.edges.length + x.vertices.card
  let C : ℕ → State → Prop := fun j st =>
    (st.regs 192 = 0 ∧ ∀ code < j, ¬P code) ∨
    (st.regs 192 = 1 ∧ TopologicallyContains (gm02ActiveGraph x.G.graph gflags) (gm02ActiveGraph x.H hflags)) ∨
    (st.regs 192 = 2 ∧ w < treeWidth x.G.graph x.G.finite_vertices x.G.finite_edges)
  let I : ℕ → State → Prop := fun j st => st.regs 190 = j ∧ M st ∧ C j st
  have hMset (st : State) (j : ℕ) (hM : M st) : M (st.setReg 190 j) := by
    rcases hM with ⟨hl, hs, hg, hh, hb, hn, hm, hf, ho⟩
    exact ⟨(State.setReg_regs_ne st j (by decide : (191 : Reg) ≠ 190)).trans hl, hs, hg, hh, hb,
      (State.setReg_regs_ne st j (by decide : (10 : Reg) ≠ 190)).trans hn,
      (State.setReg_regs_ne st j (by decide : (11 : Reg) ≠ 190)).trans hm,
      (State.setReg_regs_ne st j (by decide : (15 : Reg) ≠ 190)).trans hf,
      (State.setReg_regs_ne st j (by decide : (16 : Reg) ≠ 190)).trans ho⟩
  have hI : I 0 s := ⟨hzero, ⟨hlimit, hsrc, hG, hH, hmask, hn, hm, hf, hoff⟩,
    Or.inl ⟨hacc, fun code hc => False.elim (Nat.not_lt_zero code hc)⟩⟩
  have hTopo := gm02TopologicallyContains_iff_numericCodeFeasible x gflags hflags K hK edge hNoLoop
  obtain ⟨s', t, he, ht, hI'⟩ := forUp_exec' I limit (gm02PortCodeBudget q x K + 8)
    (r_i := 190) (hi := .reg 191) (body := gm02PortCodeScanBody K q) (by omega) hpow
    (fun j hj st hst => ⟨hst.1, eval_reg hst.2.1.1 hpow⟩)
    (fun j hj st hst => by
      rcases hst with ⟨hindex, hM, hC⟩
      rcases hM with ⟨hl, hs, hg, hh, hb, hn', hm', hf', ho⟩
      have hMold : M st := ⟨hl, hs, hg, hh, hb, hn', hm', hf', ho⟩
      rcases hC with ⟨hacc0, hprev⟩ | hpositive
      · obtain ⟨st', tb, heb, htb, hcorrect, hab, hrb⟩ := gm02PortCodeScanBody_empty_exec x st gflags hflags hK edge w q hq
          hs hg hGlen hGbits hh hHlen hHbits hb hn' hm' hf' ho hindex hw hN henc hmw (hj.trans hpow)
          hpow hjoin hword hacc0
        have hMnew : M st' := by
          refine ⟨(hrb 191 (Or.inr (by decide)) (by decide) (by decide)).trans hl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
          · exact (hab inArr (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hs
          · exact (hab 20 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hg
          · exact (hab 21 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hh
          · exact (hab 22 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hb
          · exact (hrb 10 (Or.inl (by decide)) (by decide) (by decide)).trans hn'
          · exact (hrb 11 (Or.inl (by decide)) (by decide) (by decide)).trans hm'
          · exact (hrb 15 (Or.inl (by decide)) (by decide) (by decide)).trans hf'
          · exact (hrb 16 (Or.inl (by decide)) (by decide) (by decide)).trans ho
        have hCnew : C (j + 1) (st'.setReg 190 (j + 1)) := by
          have haccset : (st'.setReg 190 (j + 1)).regs 192 = st'.regs 192 :=
            State.setReg_regs_ne st' (j + 1) (by decide)
          rcases hcorrect with ⟨hflag, hp⟩ | ⟨hflag, hp⟩ | ⟨hflag, hp⟩
          · exact Or.inr (Or.inl ⟨haccset.trans hflag, hTopo.2 ⟨j, hj, hp⟩⟩)
          · refine Or.inl ⟨haccset.trans hflag, ?_⟩
            intro code hc hP
            rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hc) with hc | hc
            · exact hprev code hc hP
            · subst code
              obtain ⟨hv, hfeas⟩ := hP
              exact hp hv hfeas
          · exact Or.inr (Or.inr ⟨haccset.trans hflag, hp⟩)
        exact ⟨st', tb, heb, htb, ⟨State.setReg_regs_self .., hMset st' (j + 1) hMnew, hCnew⟩,
          (hrb 190 (Or.inr (by decide)) (by decide) (by decide)).trans hindex⟩
      · have haccne : st.regs 192 ≠ 0 := by
          rcases hpositive with ⟨hflag, _⟩ | ⟨hflag, _⟩ <;> rw [hflag] <;> decide
        have haccw : st.regs 192 < 2 ^ W := by
          rcases hpositive with ⟨hflag, _⟩ | ⟨hflag, _⟩ <;> rw [hflag] <;> omega
        have hguard : (Expr.op .eq (.reg 192) (.const 0)).eval W st = some 0 := by
          have hv := eval_eq (eval_reg (show st.regs 192 = st.regs 192 from rfl) haccw)
            (eval_const (by omega : 0 < 2 ^ W)) (by omega)
          simpa only [haccne, ite_false] using hv
        have hCnew : C (j + 1) (st.setReg 190 (j + 1)) := by
          have haccset : (st.setReg 190 (j + 1)).regs 192 = st.regs 192 := State.setReg_regs_ne st (j + 1) (by decide)
          rcases hpositive with ⟨hflag, hp⟩ | ⟨hflag, hp⟩
          · exact Or.inr (Or.inl ⟨haccset.trans hflag, hp⟩)
          · exact Or.inr (Or.inr ⟨haccset.trans hflag, hp⟩)
        exact ⟨st, 4, .ite_false hguard (.skip st), by omega,
          ⟨State.setReg_regs_self .., hMset st (j + 1) hMold, hCnew⟩, hindex⟩) s hI
  refine ⟨s', t, he, ?_, ?_⟩
  · change t ≤ 3 + limit * (1 + 6 + (gm02PortCodeBudget q x K + 8)) at ht
    have hi : 1 + 6 + (gm02PortCodeBudget q x K + 8) = gm02PortCodeBudget q x K + 15 := by omega
    rw [hi] at ht
    exact ht
  · rcases hI'.2.2 with ⟨hflag, hnone⟩ | hpositive
    · refine Or.inr (Or.inl ⟨hflag, ?_⟩)
      intro hcontains
      obtain ⟨code, hcode, hv, hfeas⟩ := hTopo.1 hcontains
      exact hnone code hcode ⟨hv, hfeas⟩
    · exact hpositive.elim Or.inl (fun h => Or.inr (Or.inr h))

end GraphMinor.Compute
