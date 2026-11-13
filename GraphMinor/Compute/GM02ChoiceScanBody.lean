module

public import GraphMinor.Compute.GM02CheckPatternChoice
public import GraphMinor.Compute.GM02ChoiceValidityPrefix
import GraphMinor.Compute.CrossingOpsBasic

/-!
# One step of the active pattern choice scan

Read the next pattern flag. An inactive position contributes no
condition. At an active position run the per-edge validator and multiply
its result into the accumulated bit. The prefix recurrence proves that
the new bit describes exactly the next prefix.
-/

public section
namespace GraphMinor.Compute
open GraphMinor.Compute.Crossing Classical

/-- Add pattern position 43 to the accumulated choice-validity bit in register 51. -/
@[expose] def gm02ChoiceScanBody (src : Arr) : Cmd :=
  .ite (.op .eq (.read 21 (.reg 43)) (.const 1))
    (.seq (gm02CheckPatternChoiceProg src)
      (.assign 51 (.op .mul (.reg 51) (.reg 50)))) .skip

/-- One scan step advances the exact validity prefix while preserving its counter and arrays. -/
theorem gm02ChoiceScanBody_exec {w K code : ℕ} (x : GM02TopologicalInput)
    (s : State) (src : Arr) (gflags hflags : List ℕ) (f : Fin x.edges.length)
    (hK : x.edges.length ≤ K) (hsrc : s.arrs src = x.enc)
    (harr : s.arrs 23 = List.ofFn (fun i : Fin (2 * K) => gm02SeparatorDigit x.G.edges.length code i.val))
    (hG : s.arrs 20 = gflags) (hGlen : gflags.length = x.G.edges.length)
    (hGbits : ∀ b ∈ gflags, b ≤ 1) (hH : s.arrs 21 = hflags)
    (hHlen : hflags.length = x.edges.length) (hHbits : ∀ b ∈ hflags, b ≤ 1)
    (hf : s.regs 43 = f.val)
    (hprefix : s.regs 51 = if gm02PortAssignmentPrefixValid x gflags hflags
      (gm02PortAssignmentOfCode x code) f.val then 1 else 0)
    (hoff : s.regs 16 = 4 + 2 * x.G.edges.length + x.vertices.card)
    (hm : s.regs 11 = x.G.edges.length)
    (hw : 2 < 2 ^ w) (hn : x.G.n < 2 ^ w) (hKw : 2 * K < 2 ^ w)
    (hmw : x.G.edges.length + 1 < 2 ^ w) (henc : x.enc.length < 2 ^ w) :
    ∃ s' t, Exec w (gm02ChoiceScanBody src) s s' t ∧ t ≤ 132 ∧
      s'.regs 51 = (if gm02PortAssignmentPrefixValid x gflags hflags
        (gm02PortAssignmentOfCode x code) (f.val + 1) then 1 else 0) ∧
      s'.regs 43 = s.regs 43 ∧ s'.arrs = s.arrs ∧
      (∀ r, r ≠ 32 → (r < 42 ∨ 51 < r) → s'.regs r = s.regs r) := by
  let assignment := gm02PortAssignmentOfCode x code
  let P := gm02PortAssignmentPrefixValid x gflags hflags assignment f.val
  let Q := gm02PortAssignmentEdgeValid x gflags assignment f
  have hfw : f.val < 2 ^ w := by have := f.isLt; omega
  have hfi : f.val < hflags.length := hHlen.symm ▸ f.isLt
  let flag := hflags[f.val]'hfi
  have hflag : flag ≤ 1 := hHbits _ (List.getElem_mem hfi)
  have hget : (s.arrs 21)[f.val]? = some flag := by
    rw [hH]
    exact List.getElem?_eq_some_iff.2 ⟨hfi, rfl⟩
  obtain ⟨hi, hvalue⟩ := List.getElem?_eq_some_iff.1 hget
  have hread := (eval_read (eval_reg hf hfw) hi (hvalue ▸ hflag.trans_lt (by omega))).trans
    (congrArg some hvalue)
  have hguard := eval_eq hread (eval_const (by omega : 1 < 2 ^ w)) (by omega)
  have hactive_iff : hflags[f.val]? = some 1 ↔ flag = 1 := by
    rw [List.getElem?_eq_getElem hfi]
    exact ⟨Option.some.inj, congrArg some⟩
  have hrec := gm02PortAssignmentPrefixValid_succ x gflags hflags assignment f
  by_cases hactive : hflags[f.val]? = some 1
  · have hg : (Expr.op .eq (.read 21 (.reg 43)) (.const 1)).eval w s = some 1 := by
      simpa only [hactive_iff.1 hactive, ↓reduceIte] using hguard
    obtain ⟨s₁, t₁, he₁, ht₁, hout, ha, hr43, hr⟩ :=
      gm02CheckPatternChoiceProg_exec x s src gflags f hK hsrc harr hG hGlen hGbits hf hoff hm
        hw hn hKw hmw henc
    have hlocal : s₁.regs 50 = if Q then 1 else 0 := by
      simpa only [Q, gm02PortAssignmentEdgeValid, assignment] using hout
    have hp : s₁.regs 51 = if P then 1 else 0 :=
      (hr 51 (by decide) (Or.inr (by decide))).trans hprefix
    have hpw : (if P then 1 else 0) < 2 ^ w := by split <;> omega
    have hqw : (if Q then 1 else 0) < 2 ^ w := by split <;> omega
    have hprod : (if P then 1 else 0) * (if Q then 1 else 0) < 2 ^ w := by
      split_ifs <;> simp only [Nat.one_mul, Nat.zero_mul, Nat.mul_zero] <;> omega
    let bit := (if P then 1 else 0) * (if Q then 1 else 0)
    let s₂ := s₁.setReg 51 bit
    have he₂ : Exec w (.assign 51 (.op .mul (.reg 51) (.reg 50))) s₁ s₂ 4 :=
      .assign (eval_mul (eval_reg hp hpw) (eval_reg hlocal hqw) hprod)
    refine ⟨s₂, 4 + (t₁ + 4), .ite_true hg (by decide) (.seq he₁ he₂), by omega, ?_, ?_, ha, ?_⟩
    · rw [show s₂.regs 51 = bit from State.setReg_regs_self ..]
      have hiff : gm02PortAssignmentPrefixValid x gflags hflags assignment (f.val + 1) ↔ P ∧ Q := by
        simpa only [hactive, true_implies] using hrec
      rw [hiff]
      by_cases hp' : P <;> by_cases hq' : Q <;> simp [bit, hp', hq']
    · exact (State.setReg_regs_ne s₁ bit (by decide : (43 : Reg) ≠ 51)).trans hr43
    · intro r hr32 hrange
      have hr51 : r ≠ 51 := by dsimp only [Reg] at *; omega
      exact (State.setReg_regs_ne s₁ bit hr51).trans
        (hr r hr32 (by dsimp only [Reg] at *; omega))
  · have hg : (Expr.op .eq (.read 21 (.reg 43)) (.const 1)).eval w s = some 0 := by
      simpa only [show flag ≠ 1 from fun h => hactive (hactive_iff.2 h), ↓reduceIte] using hguard
    refine ⟨s, 5, .ite_false hg (.skip s), by decide, ?_, rfl, rfl, fun _ _ _ => rfl⟩
    have hiff : gm02PortAssignmentPrefixValid x gflags hflags assignment (f.val + 1) ↔ P := by
      simpa only [hactive, false_implies, and_true] using hrec
    rw [hiff]
    exact hprefix

end GraphMinor.Compute
