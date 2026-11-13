module

public import GraphMinor.Compute.GM06CuffDegree

/-!
# Searching a cuff for a vertex of valency one

The cylinder reductions and the terminal case of VI (5.7), page 133,
use a valency-one test at the initial cuff. Query each supplied cuff
vertex by scanning the endpoint array. A flag records whether a vertex
of valency one has been found. When the flag is set, a second register
holds a position witnessing it. Every input array is preserved.
-/

@[expose] public section
namespace GraphMinor.Compute
open GraphMinor.Compute.Crossing TwoPaths

/-- Scan cuff vertices, returning a flag in 27 and a witnessing position in 28. -/
def gm06DegreeOneScanProg (ends cuff : Arr) : Cmd :=
  .seq (.assign 27 (.const 0))
    (.seq (.assign 26 (.const 0))
      (forUp 26 (.len cuff)
        (.seq (gm06CuffDegreeProg ends cuff)
          (.ite (.op .eq (.reg 21) (.const 1))
            (.seq (.assign 28 (.reg 26)) (.assign 27 (.const 1))) .skip))))

/-- The cuff scan either excludes valency one everywhere or returns an actual witness. -/
theorem gm06DegreeOneScanProg_exec {w : ℕ} (ends cuff : ℕ)
    (xs cs : List ℕ) (s : State) (hw : 1 < 2 ^ w)
    (hn : xs.length < 2 ^ w) (hc : cs.length < 2 ^ w)
    (hx : ∀ x ∈ xs, x < 2 ^ w) (hcs : ∀ x ∈ cs, x < 2 ^ w)
    (ha : s.arrs ends = xs) (hb : s.arrs cuff = cs) :
    ∃ s' t, Exec w (gm06DegreeOneScanProg ends cuff) s s' t ∧
      t ≤ 7 + cs.length * (24 + 14 * xs.length) ∧
      Keeps [20, 21, 22, 26, 27, 28] [] s s' ∧
      ((s'.regs 27 = 0 ∧ ∀ j (hj : j < cs.length), xs.count cs[j] ≠ 1) ∨
        (s'.regs 27 = 1 ∧ ∃ (j : ℕ) (hj : j < cs.length),
          s'.regs 28 = j ∧ xs.count cs[j] = 1)) := by
  let R := [20, 21, 22, 26, 27, 28]
  let I : ℕ → State → Prop := fun i st =>
    st.regs 26 = i ∧ Keeps R [] s st ∧
      ((st.regs 27 = 0 ∧ ∀ j (hj : j < cs.length), j < i → xs.count cs[j] ≠ 1) ∨
        (st.regs 27 = 1 ∧ ∃ (j : ℕ) (hj : j < cs.length),
          j < i ∧ st.regs 28 = j ∧ xs.count cs[j] = 1))
  let s₁ := s.setReg 27 0
  let s₂ := s₁.setReg 26 0
  have hk₀ : Keeps R [] s s₂ :=
    ((Keeps.refl R [] s).setReg (by simp [R]) _).setReg (by simp [R]) _
  have hI₀ : I 0 s₂ := by
    refine ⟨by simp [s₂], hk₀, Or.inl ⟨by simp [s₂, s₁], ?_⟩⟩
    intro j hj hji
    omega
  obtain ⟨s', t, he, ht, hI'⟩ := forUp_exec' I cs.length (17 + 14 * xs.length) hw hc
    (fun i _ st h => ⟨h.1, GraphMinor.Compute.Crossing.eval_len ((h.2.1.2 cuff (by simp)).trans hb) hc⟩)
    (fun i hi st h => by
      obtain ⟨st₁, t₁, he₁, ht₁, hk₁, hd₁, _⟩ := gm06CuffDegreeProg_exec ends cuff
        xs cs i hi st hw hn hc hx hcs
        ((h.2.1.2 ends (by simp)).trans ha) ((h.2.1.2 cuff (by simp)).trans hb) h.1
      have hk₁' : Keeps R [] st st₁ := hk₁.mono (by
        intro r hr
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl <;> simp [R]) (by simp)
      have hk : Keeps R [] s st₁ := h.2.1.trans hk₁' (by simp) (by simp)
      have hiReg : st₁.regs 26 = i := (hk₁.1 26 (by decide)).trans h.1
      have hfReg : st₁.regs 27 = st.regs 27 := hk₁.1 27 (by decide)
      have hpReg : st₁.regs 28 = st.regs 28 := hk₁.1 28 (by decide)
      have hcount : xs.count cs[i] < 2 ^ w := (List.count_le_length).trans_lt hn
      have hcEval := GraphMinor.Compute.Crossing.eval_eq (GraphMinor.Compute.Crossing.eval_reg hd₁ hcount) (GraphMinor.Compute.Crossing.eval_const hw) hw
      by_cases hv : xs.count cs[i] = 1
      · let st₂ := st₁.setReg 28 i
        let st₃ := st₂.setReg 27 1
        have he₂ : Exec w
            (.ite (.op .eq (.reg 21) (.const 1))
              (.seq (.assign 28 (.reg 26)) (.assign 27 (.const 1))) .skip) st₁ st₃ 7 :=
          .ite_true (by simpa only [hv, ite_true] using hcEval) (by decide)
            (.seq (.assign (GraphMinor.Compute.Crossing.eval_reg hiReg (hi.trans hc))) (.assign (GraphMinor.Compute.Crossing.eval_const hw)))
        refine ⟨st₃, t₁ + 7, .seq he₁ he₂, by omega, ?_, ?_⟩
        · refine ⟨by simp, ((hk.setReg (by simp [R]) _).setReg (by simp [R]) _).setReg
            (by simp [R]) _, Or.inr ⟨by simp [st₃], i, hi, by omega, ?_, hv⟩⟩
          simp [st₃, st₂]
        · simpa [st₃, st₂] using hiReg
      · have he₂ : Exec w
            (.ite (.op .eq (.reg 21) (.const 1))
              (.seq (.assign 28 (.reg 26)) (.assign 27 (.const 1))) .skip) st₁ st₁ 4 :=
          .ite_false (by simpa only [hv, ite_false] using hcEval) (.skip st₁)
        refine ⟨st₁, t₁ + 4, .seq he₁ he₂, by omega, ?_, hiReg⟩
        refine ⟨by simp, hk.setReg (by simp [R]) _, ?_⟩
        rcases h.2.2 with hzero | hone
        · refine Or.inl ⟨by simpa only [State.setReg_regs_ne _ _ (by decide : 27 ≠ 26), hfReg]
            using hzero.1, ?_⟩
          intro j hj hji
          by_cases heq : j = i
          · subst j; exact hv
          · exact hzero.2 j hj (by omega)
        · obtain ⟨hf, j, hj, hji, hp, hd⟩ := hone
          refine Or.inr ⟨?_, j, hj, by omega, ?_, hd⟩
          · simpa only [State.setReg_regs_ne _ _ (by decide : 27 ≠ 26), hfReg] using hf
          · simpa only [State.setReg_regs_ne _ _ (by decide : 28 ≠ 26), hpReg] using hp)
    s₂ hI₀
  have hi₁ : Exec w (.assign 27 (.const 0)) s s₁ 2 :=
    .assign (GraphMinor.Compute.Crossing.eval_const (Nat.two_pow_pos w))
  have hi₂ : Exec w (.assign 26 (.const 0)) s₁ s₂ 2 :=
    .assign (GraphMinor.Compute.Crossing.eval_const (Nat.two_pow_pos w))
  refine ⟨s', 2 + (2 + t), .seq hi₁ (.seq hi₂ he), ?_, hI'.2.1, ?_⟩
  · simp only [Expr.cost] at ht
    have hh : 1 + 6 + (17 + 14 * xs.length) = 24 + 14 * xs.length := by omega
    rw [hh] at ht
    omega
  · rcases hI'.2.2 with hz | ho
    · exact Or.inl ⟨hz.1, fun j hj => hz.2 j hj hj⟩
    · obtain ⟨hf, j, hj, _, hp, hd⟩ := ho
      exact Or.inr ⟨hf, j, hj, hp, hd⟩

end GraphMinor.Compute
