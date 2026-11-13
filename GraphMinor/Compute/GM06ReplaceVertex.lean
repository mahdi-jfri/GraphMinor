module

public import GraphMinor.Compute.CrossingOpsBasic
public import GraphMinor.Compute.TwoPathsCyc

/-!
# Updating endpoint labels after a cylinder contraction

Reduction 3 of VI, page 128, moves the neighbour of an initial vertex
to that vertex. On endpoint labels this replaces every occurrence of
the neighbour by the initial label. This file verifies the in-place
RAM pass doing that replacement. Edge deletion and boundary updates
are separate operations.
-/

@[expose] public section
namespace GraphMinor.Compute
open GraphMinor.Compute.Crossing TwoPaths

/-- Replace the label in register 24 by the label in register 25 throughout an array. -/
def gm06ReplaceVertexProg (a : Arr) : Cmd :=
  .seq (.assign 23 (.const 0))
    (forUp 23 (.len a)
      (.ite (.op .eq (.read a (.reg 23)) (.reg 24))
        (.write a (.reg 23) (.reg 25)) .skip))

/-- The contraction-label pass replaces exactly the old label, in linear time. -/
theorem gm06ReplaceVertexProg_exec {w : ℕ} (a : Arr) (xs : List ℕ)
    (old new : ℕ) (s : State) (hw : 1 < 2 ^ w)
    (hn : xs.length < 2 ^ w) (hx : ∀ x ∈ xs, x < 2 ^ w)
    (ho : old < 2 ^ w) (hnew : new < 2 ^ w)
    (ha : s.arrs a = xs) (hro : s.regs 24 = old) (hrn : s.regs 25 = new) :
    ∃ s' t, Exec w (gm06ReplaceVertexProg a) s s' t ∧
      t ≤ 5 + 14 * xs.length ∧ Keeps [23] [a] s s' ∧
      s'.arrs a = xs.map (fun x => if x = old then new else x) := by
  let f := fun x => if x = old then new else x
  let I : ℕ → State → Prop := fun i st =>
    st.regs 23 = i ∧ Keeps [23] [a] s st ∧ (st.arrs a).length = xs.length ∧
    ∀ j (hj : j < xs.length) (hjs : j < (st.arrs a).length), (st.arrs a)[j] =
      if j < i then f xs[j] else xs[j]
  have hI : I 0 (s.setReg 23 0) := by
    refine ⟨by simp, (Keeps.refl _ _ s).setReg (by simp) _, by simpa using congrArg List.length ha, ?_⟩
    intro j hj hjs
    simp [ha]
  obtain ⟨s', t, he, ht, hI'⟩ := forUp_exec' I xs.length 7 hw hn
    (fun i _ st h => ⟨h.1, by
      have hh := eval_len (a := a) (s := st) rfl (h.2.2.1 ▸ hn)
      simpa only [h.2.2.1] using hh⟩)
    (fun i hi st h => by
      have hai : i < (st.arrs a).length := by omega
      have hread : (st.arrs a)[i] = xs[i] := by simpa using h.2.2.2 i hi hai
      have hrOld : st.regs 24 = old := (h.2.1.1 24 (by decide)).trans hro
      have hrNew : st.regs 25 = new := (h.2.1.1 25 (by decide)).trans hrn
      have hrRead := eval_read (a := a) (eval_reg h.1 (hi.trans hn)) hai
        (by rw [hread]; exact hx _ (List.getElem_mem hi))
      rw [hread] at hrRead
      have hc := eval_eq hrRead (eval_reg hrOld ho) hw
      by_cases hv : xs[i] = old
      · let st' := st.writeArr a i new
        have hb : Exec w (.write a (.reg 23) (.reg 25)) st st' 3 :=
          .write (eval_reg h.1 (hi.trans hn)) (eval_reg hrNew hnew) hai
        have hex : Exec w
            (.ite (.op .eq (.read a (.reg 23)) (.reg 24))
              (.write a (.reg 23) (.reg 25)) .skip) st st' 7 :=
          .ite_true (by simpa only [hv, ite_true] using hc) (by decide) hb
        refine ⟨st', 7, hex, le_rfl, ?_, by simpa [st'] using h.1⟩
        refine ⟨by simp, (h.2.1.writeArr (by simp) _ _).setReg (by simp) _, by simpa only [st', State.setReg_arrs, State.writeArr_arrs_self, List.length_set] using h.2.2.1, ?_⟩
        intro j hj hjs
        by_cases hji : j = i
        · subst j
          simp [st', List.getElem_set_self, f, hv]
        · simp only [State.setReg_arrs] at hjs ⊢
          dsimp only [st'] at hjs ⊢
          simp only [State.writeArr_arrs_self] at hjs ⊢
          rw [List.getElem_set_ne (Ne.symm hji), h.2.2.2 j hj (by omega)]
          have hh : (j < i + 1) = (j < i) := propext (by omega)
          simp only [hh]
      · have hex : Exec w
            (.ite (.op .eq (.read a (.reg 23)) (.reg 24))
              (.write a (.reg 23) (.reg 25)) .skip) st st 5 :=
          .ite_false (by simpa only [hv, ite_false] using hc) (.skip st)
        refine ⟨st, 5, hex, by decide, ?_, h.1⟩
        refine ⟨by simp, h.2.1.setReg (by simp) _, by simpa using h.2.2.1, ?_⟩
        intro j hj hjs
        simp only [State.setReg_arrs]
        rw [h.2.2.2 j hj (by omega)]
        by_cases hji : j = i
        · subst j
          simp [f, hv]
        · have hh : (j < i + 1) = (j < i) := propext (by omega)
          simp only [hh])
    (s.setReg 23 0) hI
  refine ⟨s', 2 + t, .seq (.assign (eval_const (Nat.two_pow_pos w))) he, ?_, hI'.2.1, ?_⟩
  · simp only [Expr.cost] at ht
    omega
  · apply List.ext_getElem
    · simpa only [List.length_map] using hI'.2.2.1
    · intro j hj hj'
      rw [List.getElem_map]
      have hjx : j < xs.length := by omega
      simpa only [if_pos hjx] using hI'.2.2.2 j hjx hj

end GraphMinor.Compute
