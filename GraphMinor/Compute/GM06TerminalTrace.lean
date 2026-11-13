module

public import GraphMinor.Compute.GM06FirstContact
public import GraphMinor.Compute.GM13SocietyTabulate
import GraphMinor.Compute.CrossingOpsBasic

/-!
# A RAM first-contact trace

The terminal trace in Section 15 of our proof of VI (5.7) (outlined in
`GraphMinor/GM06/Alg57Algorithm.lean`) scans a dart row and reads the target bit of each dart's
head. Once a contact has been found, later scan steps do nothing. The resulting prefix is copied to
a fresh array. A prefix invariant proves exact agreement with the pure trace, including empty inputs
and inputs with no contact.
-/

@[expose] public section
namespace GraphMinor.Compute
open TwoPaths GraphMinor.Compute.Crossing

/-- The body of the first-contact scan. Registers 601 and 602 hold
the trace length and the contact bit, respectively. -/
def gm06TerminalTraceStep : Cmd :=
  .ite (.op .eq (.reg 602) (.const 0))
    (.seq (.assign 602 (.op .eq
      (.op .eq (.read 602 (.read 601 (.read 600 (.reg 600)))) (.const 0)) (.const 0)))
      (.assign 601 (.op .add (.reg 601) (.const 1)))) .skip

/-- Read darts from 600, heads from 601 and target bits from 602.
Return the traced dart prefix in 603, its length in register 601,
and its contact bit in register 602. -/
def gm06TerminalTraceProg : Cmd :=
  .seq (.assign 600 (.const 0))
    (.seq (.assign 601 (.const 0))
      (.seq (.assign 602 (.const 0))
        (.seq (forUp 600 (.len 600) gm06TerminalTraceStep)
          (gm13TabulateProg 605 (.reg 601) (.read 600 (.reg 605)) 603))))

private theorem prefix_eq_take_length {α : Type*} {xs ys : List α}
    (h : xs <+: ys) : ys.take xs.length = xs := by
  obtain ⟨tail, rfl⟩ := h
  simp

/-- The RAM trace computes precisely the pure first-contact prefix,
in linear time, preserving every input and all unrelated memory. -/
theorem gm06TerminalTraceProg_exec {w : ℕ} (heads targets ds : List ℕ) (s : State)
    (hw : 1 < 2 ^ w) (hn : ds.length < 2 ^ w)
    (hh : heads.length < 2 ^ w) (ht : targets.length < 2 ^ w)
    (hd : ∀ d ∈ ds, d < heads.length)
    (hv : ∀ v ∈ heads, v < targets.length)
    (hb : ∀ b ∈ targets, b < 2 ^ w)
    (h600 : s.arrs 600 = ds) (h601 : s.arrs 601 = heads) (h602 : s.arrs 602 = targets) :
    ∃ s' t, Exec w gm06TerminalTraceProg s s' t ∧
      t ≤ 15 + 38 * ds.length ∧
      Keeps [600, 601, 602, 605] [603] s s' ∧
      s'.arrs 603 = (gm06TerminalTrace heads targets ds).1 ∧
      s'.regs 601 = (gm06TerminalTrace heads targets ds).1.length ∧
      s'.regs 602 = (gm06TerminalTrace heads targets ds).2.toNat := by
  let stop := gm06TerminalContact heads targets
  let tr := fun i => gm06FirstContact stop (ds.take i)
  let Inv := fun i st => st.regs 600 = i ∧ Keeps [600, 601, 602] [] s st ∧
    st.regs 601 = (tr i).1.length ∧ st.regs 602 = (tr i).2.toNat
  let s₀ := ((s.setReg 600 0).setReg 601 0).setReg 602 0
  have he₀ : Exec w (.seq (.assign 600 (.const 0))
      (.seq (.assign 601 (.const 0)) (.assign 602 (.const 0)))) s s₀ 6 :=
    .seq (.assign (GraphMinor.Compute.Crossing.eval_const (Nat.two_pow_pos w)))
      (.seq (.assign (GraphMinor.Compute.Crossing.eval_const (Nat.two_pow_pos w))) (.assign (GraphMinor.Compute.Crossing.eval_const (Nat.two_pow_pos w))))
  have hI₀ : Inv 0 s₀ := by
    refine ⟨by simp [s₀], ?_, ?_, ?_⟩
    · exact (((Keeps.refl [600, 601, 602] [] s).setReg (by simp) _).setReg
        (by simp) _).setReg (by simp) _
    · simp [s₀, tr, gm06FirstContact]
    · simp [s₀, tr, gm06FirstContact]
  obtain ⟨s₁, t₁, he₁, ht₁, hI₁⟩ := forUp_exec' (r_i := 600) (hi := .len 600)
    (body := gm06TerminalTraceStep) Inv ds.length 16 hw hn
    (fun i _ st h => ⟨h.1, GraphMinor.Compute.Crossing.eval_len ((h.2.1.2 600 (by simp)).trans h600) hn⟩)
    (fun i hi st h => by
      obtain ⟨hidx, hk, hlen, hflag⟩ := h
      have hnext : tr (i + 1) = if (tr i).2 then tr i else ((tr i).1 ++ [ds[i]], stop ds[i]) := by
        dsimp only [tr]
        rw [List.take_add_one, List.getElem?_eq_getElem hi, Option.toList_some]
        exact gm06FirstContact_append_one stop (ds.take i) ds[i]
      cases hdone : (tr i).2 with
      | true =>
        have hf : st.regs 602 = 1 := by simpa [hdone] using hflag
        have he : Exec w gm06TerminalTraceStep st st 4 :=
          .ite_false (by simpa using (GraphMinor.Compute.Crossing.eval_eq (GraphMinor.Compute.Crossing.eval_reg hf hw)
            (GraphMinor.Compute.Crossing.eval_const (Nat.two_pow_pos w)) hw)) (.skip st)
        refine ⟨st, 4, he, by decide, ⟨by simp, hk.setReg (by simp) _, ?_, ?_⟩, hidx⟩
        · simpa only [hnext, hdone, ↓reduceIte, State.setReg_regs_ne _ _ (by decide : 601 ≠ 600)] using hlen
        · simpa only [hnext, hdone, ↓reduceIte, State.setReg_regs_ne _ _ (by decide : 602 ≠ 600)] using hflag
      | false =>
        have hf : st.regs 602 = 0 := by simpa [hdone] using hflag
        have htlen : (tr i).1.length = i := by
          have heq := gm06FirstContact_eq_self_of_false stop (ds.take i) hdone
          rw [heq, List.length_take_of_le hi.le]
        have hlen' : st.regs 601 = i := hlen.trans htlen
        have hd' : ds[i] < heads.length := hd _ (List.getElem_mem hi)
        have hv' : heads[ds[i]] < targets.length := hv _ (List.getElem_mem hd')
        have hb' := hb _ (List.getElem_mem hv')
        have hds : st.arrs 600 = ds := (hk.2 600 (by simp)).trans h600
        have hhs : st.arrs 601 = heads := (hk.2 601 (by simp)).trans h601
        have hts : st.arrs 602 = targets := (hk.2 602 (by simp)).trans h602
        have erd : (Expr.read 600 (.reg 600)).eval w st = some ds[i] := by
          have he := GraphMinor.Compute.Crossing.eval_read (a := 600) (GraphMinor.Compute.Crossing.eval_reg hidx (hi.trans hn))
            (by simpa only [hds] using hi) (by simpa only [hds] using hd'.trans hh)
          simpa only [hds] using he
        have erh : (Expr.read 601 (.read 600 (.reg 600))).eval w st = some heads[ds[i]] := by
          have he := GraphMinor.Compute.Crossing.eval_read (a := 601) erd
            (by simpa only [hhs] using hd') (by simpa only [hhs] using hv'.trans ht)
          simpa only [hhs] using he
        have ert : (Expr.read 602 (.read 601 (.read 600 (.reg 600)))).eval w st =
            some targets[heads[ds[i]]] := by
          have he := GraphMinor.Compute.Crossing.eval_read (a := 602) erh
            (by simpa only [hts] using hv') (by simpa only [hts] using hb')
          simpa only [hts] using he
        let bit := (stop ds[i]).toNat
        have ebit : (Expr.op .eq
            (.op .eq (.read 602 (.read 601 (.read 600 (.reg 600)))) (.const 0))
            (.const 0)).eval w st = some bit := by
          have he := GraphMinor.Compute.Crossing.eval_eq (GraphMinor.Compute.Crossing.eval_eq ert (GraphMinor.Compute.Crossing.eval_const (Nat.two_pow_pos w)) hw)
            (GraphMinor.Compute.Crossing.eval_const (Nat.two_pow_pos w)) hw
          have hstop : stop ds[i] = (targets[heads[ds[i]]] != 0) := by
            simp only [stop, gm06TerminalContact, List.getElem?_eq_getElem hd',
              Option.getD_some, List.getElem?_eq_getElem hv']
          change _ = some (stop ds[i]).toNat
          rw [hstop]
          by_cases hz : targets[heads[ds[i]]] = 0
          · simpa [hz] using he
          · have hbne : (targets[heads[ds[i]]] != 0) = true := by simpa using hz
            simpa only [hz, ↓reduceIte, hbne, Bool.toNat_true] using he
        let st₁ := st.setReg 602 bit
        let st₂ := st₁.setReg 601 (i + 1)
        have he : Exec w gm06TerminalTraceStep st st₂ 16 :=
          show Exec w (.ite (.op .eq (.reg 602) (.const 0))
            (.seq (.assign 602 (.op .eq (.op .eq (.read 602 (.read 601 (.read 600 (.reg 600)))) (.const 0)) (.const 0)))
              (.assign 601 (.op .add (.reg 601) (.const 1)))) .skip) st st₂ 16 from
          .ite_true (by simpa using (GraphMinor.Compute.Crossing.eval_eq (GraphMinor.Compute.Crossing.eval_reg hf (Nat.two_pow_pos w))
            (GraphMinor.Compute.Crossing.eval_const (Nat.two_pow_pos w)) hw)) (by decide)
            (.seq (.assign ebit) (.assign (GraphMinor.Compute.Crossing.eval_add
              (GraphMinor.Compute.Crossing.eval_reg (by simpa [st₁] using hlen') (hi.trans hn)) (GraphMinor.Compute.Crossing.eval_const hw) (by omega))))
        refine ⟨st₂, 16, he, by decide, ⟨by simp, ?_, ?_, ?_⟩, ?_⟩
        · exact ((hk.setReg (by simp) _).setReg (by simp) _).setReg (by simp) _
        · simp [st₂, hnext, hdone, htlen]
        · simp [st₂, st₁, hnext, hdone, bit]
        · simpa [st₂, st₁] using hidx) s₀ hI₀
  have hk₁ : Keeps [600, 601, 602] [] s s₁ := hI₁.2.1
  let out := (gm06TerminalTrace heads targets ds).1
  have hout : out <+: ds := gm06FirstContact_prefix stop ds
  have hol : out.length ≤ ds.length := hout.length_le
  have hlen₁ : s₁.regs 601 = out.length := by simpa [tr, out, gm06TerminalTrace, stop] using hI₁.2.2.1
  obtain ⟨s₂, t₂, he₂, ht₂, hk₂, hd₂⟩ := gm13TabulateProg_exec 605 (.reg 601)
    (.read 600 (.reg 605)) 603 out s₁ hw (hol.trans_lt hn)
    (fun st hk => GraphMinor.Compute.Crossing.eval_reg ((hk.1 601 (by decide)).trans hlen₁) (hol.trans_lt hn))
    (fun st j hj hk hidx => by
      have hds : st.arrs 600 = ds := (hk.2 600 (by decide)).trans ((hk₁.2 600 (by simp)).trans h600)
      have hjd := hj.trans_le hol
      have hget : ds[j] = out[j] := by
        have heq := prefix_eq_take_length hout
        have hh := congrArg (fun xs => xs[j]?) heq
        simpa only [List.getElem?_take, hj, ↓reduceIte, List.getElem?_eq_getElem hjd,
          List.getElem?_eq_getElem hj, Option.some.injEq] using hh
      have hread : (Expr.read 600 (.reg 605)).eval w st = some ds[j] := by
        have he := GraphMinor.Compute.Crossing.eval_read (a := 600) (GraphMinor.Compute.Crossing.eval_reg hidx (hjd.trans hn))
          (by simpa only [hds] using hjd) (by simpa only [hds] using (hd _ (List.getElem_mem hjd)).trans hh)
        simpa only [hds] using he
      simpa only [hget] using hread)
  have hkall : Keeps [600, 601, 602, 605] [603] s s₂ :=
    (hk₁.mono (by simp) (by simp)).trans hk₂ (by simp) (by simp)
  refine ⟨s₂, 2 + (2 + (2 + (t₁ + t₂))), ?_, ?_, hkall, hd₂, ?_, ?_⟩
  · exact .seq (.assign (GraphMinor.Compute.Crossing.eval_const (Nat.two_pow_pos w)))
      (.seq (.assign (GraphMinor.Compute.Crossing.eval_const (Nat.two_pow_pos w)))
        (.seq (.assign (GraphMinor.Compute.Crossing.eval_const (Nat.two_pow_pos w))) (.seq he₁ he₂)))
  · simp only [Expr.cost] at ht₁ ht₂
    omega
  · exact (hk₂.1 601 (by decide)).trans hlen₁
  · rw [hk₂.1 602 (by decide)]
    simpa [tr, gm06TerminalTrace, stop] using hI₁.2.2.2

end GraphMinor.Compute
