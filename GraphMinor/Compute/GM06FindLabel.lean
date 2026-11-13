module

public import GraphMinor.Compute.CrossingOpsBasic
public import GraphMinor.Compute.TwoPathsCyc

/-!
# Finding a directed label in a rotation row

Scan a row for the label held in a register. The result is a position
of that label, or the row length when there is no occurrence. A rotation
row has no repeated directed labels, so a found position identifies the
label uniquely. The program preserves its input arrays and other registers.
-/

@[expose] public section
namespace GraphMinor.Compute
open GraphMinor.Compute.Crossing TwoPaths

/-- Search for a register-held label, returning the last matching position. -/
def gm06FindLabelProg (a : Arr) (needle idx res : Reg) : Cmd :=
  .seq (.assign res (.len a)) (.seq (.assign idx (.const 0))
    (forUp idx (.len a) (.ite (.op .eq (.read a (.reg idx)) (.reg needle))
      (.assign res (.reg idx)) .skip)))

/-- The label search returns a genuine position or excludes every occurrence. -/
theorem gm06FindLabelProg_exec {w : ℕ} (a needle idx res : ℕ)
    (hir : idx ≠ res) (hni : needle ≠ idx) (hnr : needle ≠ res)
    (xs : List ℕ) (v : ℕ) (s : State) (hw : 1 < 2 ^ w)
    (hn : xs.length < 2 ^ w) (hx : ∀ x ∈ xs, x < 2 ^ w)
    (hv : v < 2 ^ w) (ha : s.arrs a = xs) (hr : s.regs needle = v) :
    ∃ s' t, Exec w (gm06FindLabelProg a needle idx res) s s' t ∧
      t ≤ 7 + 13 * xs.length ∧ Keeps [idx, res] [] s s' ∧
      ((s'.regs res = xs.length ∧ ∀ j (hj : j < xs.length), xs[j] ≠ v) ∨
        ∃ (j : ℕ) (hj : j < xs.length), s'.regs res = j ∧ xs[j] = v) := by
  let I : ℕ → State → Prop := fun i st =>
    st.regs idx = i ∧ Keeps [idx, res] [] s st ∧
      ((st.regs res = xs.length ∧ ∀ j (hj : j < xs.length), j < i → xs[j] ≠ v) ∨
        ∃ (j : ℕ) (hj : j < xs.length), j < i ∧ st.regs res = j ∧ xs[j] = v)
  let s₁ := s.setReg res xs.length
  let s₂ := s₁.setReg idx 0
  have hk₀ : Keeps [idx, res] [] s s₂ :=
    ((Keeps.refl _ _ s).setReg (by simp) _).setReg (by simp) _
  have hI₀ : I 0 s₂ := by
    refine ⟨by simp [s₂], hk₀, Or.inl ⟨?_, ?_⟩⟩
    · simp [s₂, s₁, hir.symm]
    · intro j hj hj0; omega
  obtain ⟨s', t, he, ht, hI'⟩ := forUp_exec' I xs.length 6 hw hn
    (fun i _ st h => ⟨h.1, eval_len ((h.2.1.2 a (by simp)).trans ha) hn⟩)
    (fun i hi st h => by
      have ha' : st.arrs a = xs := (h.2.1.2 a (by simp)).trans ha
      have hr' : st.regs needle = v := (h.2.1.1 needle (by simp [hni, hnr])).trans hr
      have hrRead := eval_read (a := a) (eval_reg h.1 (hi.trans hn))
        (by simpa only [ha'] using hi)
        (by simpa only [ha'] using hx xs[i] (List.getElem_mem hi))
      simp only [ha'] at hrRead
      have hc := eval_eq hrRead (eval_reg hr' hv) hw
      by_cases hv' : xs[i] = v
      · let st' := st.setReg res i
        have hex : Exec w
            (.ite (.op .eq (.read a (.reg idx)) (.reg needle)) (.assign res (.reg idx)) .skip)
            st st' 6 :=
          .ite_true (by simpa only [hv', ite_true] using hc) (by decide)
            (.assign (eval_reg h.1 (hi.trans hn)))
        refine ⟨st', 6, hex, le_rfl, ?_, ?_⟩
        · refine ⟨by simp, ((h.2.1.setReg (by simp) _).setReg (by simp) _),
            Or.inr ⟨i, hi, by omega, ?_, hv'⟩⟩
          simp [st', hir.symm]
        · simpa only [st', State.setReg_regs_ne _ _ hir] using h.1
      · have hex : Exec w
            (.ite (.op .eq (.read a (.reg idx)) (.reg needle)) (.assign res (.reg idx)) .skip)
            st st 5 :=
          .ite_false (by simpa only [hv', ite_false] using hc) (.skip st)
        refine ⟨st, 5, hex, by decide, ⟨by simp, h.2.1.setReg (by simp) _, ?_⟩, h.1⟩
        rcases h.2.2 with hz | ho
        · refine Or.inl ⟨by simpa only [State.setReg_regs_ne _ _ hir.symm] using hz.1, ?_⟩
          intro j hj hji
          by_cases hji' : j = i
          · subst j; exact hv'
          · exact hz.2 j hj (by omega)
        · obtain ⟨j, hj, hji, hp, hm⟩ := ho
          exact Or.inr ⟨j, hj, by omega,
            by simpa only [State.setReg_regs_ne _ _ hir.symm] using hp, hm⟩)
    s₂ hI₀
  have he₁ : Exec w (.assign res (.len a)) s s₁ 2 := .assign (eval_len ha hn)
  have he₂ : Exec w (.assign idx (.const 0)) s₁ s₂ 2 := .assign (eval_const (Nat.two_pow_pos w))
  refine ⟨s', 2 + (2 + t), .seq he₁ (.seq he₂ he), ?_, hI'.2.1, ?_⟩
  · simp only [Expr.cost] at ht
    omega
  · rcases hI'.2.2 with hz | ho
    · exact Or.inl ⟨hz.1, fun j hj => hz.2 j hj hj⟩
    · obtain ⟨j, hj, _, hp, hm⟩ := ho
      exact Or.inr ⟨j, hj, hp, hm⟩

/-- In a rotation row with no repeated labels, a present label is found at its unique index. -/
theorem gm06FindLabelProg_exec_nodup {w : ℕ} (a needle idx res : ℕ)
    (hir : idx ≠ res) (hni : needle ≠ idx) (hnr : needle ≠ res)
    (xs : List ℕ) (v : ℕ) (s : State) (hw : 1 < 2 ^ w)
    (hn : xs.length < 2 ^ w) (hx : ∀ x ∈ xs, x < 2 ^ w)
    (hnd : xs.Nodup) (hm : v ∈ xs)
    (ha : s.arrs a = xs) (hr : s.regs needle = v) :
    ∃ s' t, Exec w (gm06FindLabelProg a needle idx res) s s' t ∧
      t ≤ 7 + 13 * xs.length ∧ Keeps [idx, res] [] s s' ∧
      s'.regs res = xs.idxOf v := by
  obtain ⟨s', t, he, ht, hk, hd⟩ :=
    gm06FindLabelProg_exec a needle idx res hir hni hnr xs v s hw hn hx (hx v hm) ha hr
  refine ⟨s', t, he, ht, hk, ?_⟩
  rcases hd with hnone | hsome
  · obtain ⟨j, hj, heq⟩ := List.mem_iff_getElem.mp hm
    exact False.elim (hnone.2 j hj heq)
  · obtain ⟨j, hj, hrj, hjv⟩ := hsome
    have hi : xs.idxOf v < xs.length := List.idxOf_lt_length_iff.mpr hm
    have heq : xs[j] = xs[xs.idxOf v] := hjv.trans (List.getElem_idxOf hi).symm
    exact hrj.trans (hnd.getElem_inj_iff.mp heq)

end GraphMinor.Compute
