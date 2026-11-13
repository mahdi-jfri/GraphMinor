module

public import GraphMinor.Compute.GM06ActiveEdgeSector

/-!
# Finding an active edge in a directed sector

Scan the original edge labels and query each activity bit and pair of
directed ends. Return an edge in the chosen sector when one exists,
or the edge-count sentinel when none exists. This is a finite selection
routine for the cylinder reductions. It does not assume that a selected
sector has already been identified with a geometric side.
-/

@[expose] public section
namespace GraphMinor.Compute
open TwoPaths

/-- Return a qualifying edge in 55, or the activity-array length when there is none. -/
def gm06FindSectorEdgeProg (rot active : Arr) : Cmd :=
  .seq (.assign 55 (.len active)) (.seq (.assign 53 (.const 0))
    (forUp 53 (.len active)
      (.seq (gm06ActiveEdgeSectorProg rot active)
        (.ite (.op .eq (.reg 43) (.const 1)) (.assign 55 (.reg 53)) .skip))))

/-- The edge scan finds an active edge in the supplied directed sector or excludes all of them. -/
theorem gm06FindSectorEdgeProg_exec {w : ℕ} (rot active : ℕ) (xs mask : List ℕ)
    (p q : ℕ) (s : State) (hw : 2 < 2 ^ w)
    (hn : xs.length < 2 ^ w) (hx : ∀ x ∈ xs, x < 2 ^ w) (hnd : xs.Nodup)
    (hp : p ∈ xs) (hq : q ∈ xs) (hm : 2 * mask.length < 2 ^ w)
    (hbits : ∀ b ∈ mask, b ≤ 1) (ha : s.arrs rot = xs) (hb : s.arrs active = mask)
    (h36 : s.regs 36 = p) (h37 : s.regs 37 = q) :
    ∃ s' t, Exec w (gm06FindSectorEdgeProg rot active) s s' t ∧
      t ≤ 7 + mask.length * (120 + 104 * xs.length) ∧
      Keeps [53, 55, 38, 50, 40, 41, 42, 43, 54] [] s s' ∧
      ((s'.regs 55 = mask.length ∧ ∀ e (he : e < mask.length),
        ¬(mask[e] = 1 ∧ (gm06RotationSectorFlag xs p q (2 * e) = 1 ∨
          gm06RotationSectorFlag xs p q (2 * e + 1) = 1))) ∨
        ∃ (e : ℕ) (he : e < mask.length), s'.regs 55 = e ∧ mask[e] = 1 ∧
          (gm06RotationSectorFlag xs p q (2 * e) = 1 ∨
            gm06RotationSectorFlag xs p q (2 * e + 1) = 1)) := by
  let R := [53, 55, 38, 50, 40, 41, 42, 43, 54]
  let P := fun e (he : e < mask.length) => mask[e] = 1 ∧
    (gm06RotationSectorFlag xs p q (2 * e) = 1 ∨
      gm06RotationSectorFlag xs p q (2 * e + 1) = 1)
  let I : ℕ → State → Prop := fun i st => st.regs 53 = i ∧ Keeps R [] s st ∧
    ((st.regs 55 = mask.length ∧ ∀ e (he : e < mask.length), e < i → ¬P e he) ∨
      ∃ (e : ℕ) (he : e < mask.length), e < i ∧ st.regs 55 = e ∧ P e he)
  have hw1 : 1 < 2 ^ w := by omega
  have hmw : mask.length < 2 ^ w := by omega
  let s₁ := s.setReg 55 mask.length
  let s₂ := s₁.setReg 53 0
  have hk₀ : Keeps R [] s s₂ :=
    ((Keeps.refl _ _ s).setReg (by simp [R]) _).setReg (by simp [R]) _
  have hI₀ : I 0 s₂ := by
    refine ⟨by simp [s₂], hk₀, Or.inl ⟨by simp [s₂, s₁], ?_⟩⟩
    intro e he he0; omega
  obtain ⟨s', t, hex, ht, hI'⟩ := GraphMinor.Compute.Crossing.forUp_exec' I mask.length
    (113 + 104 * xs.length) hw1 hmw
    (fun i _ st h => ⟨h.1, GraphMinor.Compute.Crossing.eval_len
      ((h.2.1.2 active (by simp)).trans hb) hmw⟩)
    (fun i hi st h => by
      obtain ⟨st₁, t₁, he₁, ht₁, hk₁, hgood, hbit⟩ := gm06ActiveEdgeSectorProg_exec rot active
        xs mask p q i st hw hn hx hnd hp hq hi hm hbits
        ((h.2.1.2 rot (by simp)).trans ha) ((h.2.1.2 active (by simp)).trans hb)
        ((h.2.1.1 36 (by simp [R])).trans h36) ((h.2.1.1 37 (by simp [R])).trans h37) h.1
      change st₁.regs 43 = 1 ↔ P i hi at hgood
      have hk₁' : Keeps R [] st st₁ := hk₁.mono (by
        intro j hj
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hj
        rcases hj with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp [R]) (by simp)
      have hk : Keeps R [] s st₁ := h.2.1.trans hk₁' (by simp) (by simp)
      have hiReg : st₁.regs 53 = i := (hk₁.1 53 (by decide)).trans h.1
      have hpReg : st₁.regs 55 = st.regs 55 := hk₁.1 55 (by decide)
      have hflagw : st₁.regs 43 < 2 ^ w := by
        rcases hbit with hh | hh
        · rw [hh]; exact Nat.two_pow_pos w
        · rw [hh]; exact hw1
      have hc := GraphMinor.Compute.Crossing.eval_eq
        (GraphMinor.Compute.Crossing.eval_reg rfl hflagw)
        (GraphMinor.Compute.Crossing.eval_const hw1) hw1
      by_cases hflag : st₁.regs 43 = 1
      · let st₂ := st₁.setReg 55 i
        have he₂ : Exec w (.ite (.op .eq (.reg 43) (.const 1))
            (.assign 55 (.reg 53)) .skip) st₁ st₂ 5 :=
          .ite_true (by simpa only [hflag, ite_true] using hc) (by decide)
            (.assign (GraphMinor.Compute.Crossing.eval_reg hiReg (hi.trans hmw)))
        refine ⟨st₂, t₁ + 5, .seq he₁ he₂, by omega, ?_, ?_⟩
        · refine ⟨by simp, (hk.setReg (by simp [R]) _).setReg (by simp [R]) _,
            Or.inr ⟨i, hi, by omega, ?_, hgood.mp hflag⟩⟩
          simp [st₂]
        · simpa only [st₂, State.setReg_regs_ne _ _ (by decide : 53 ≠ 55)] using hiReg
      · have hbad : ¬P i hi := fun hh => hflag (hgood.mpr hh)
        have he₂ : Exec w (.ite (.op .eq (.reg 43) (.const 1))
            (.assign 55 (.reg 53)) .skip) st₁ st₁ 4 :=
          .ite_false (by simpa only [hflag, ite_false] using hc) (.skip st₁)
        refine ⟨st₁, t₁ + 4, .seq he₁ he₂, by omega,
          ⟨by simp, hk.setReg (by simp [R]) _, ?_⟩, hiReg⟩
        rcases h.2.2 with hz | ho
        · refine Or.inl ⟨?_, ?_⟩
          · simpa only [State.setReg_regs_ne _ _ (by decide : 55 ≠ 53), hpReg] using hz.1
          · intro e he hei
            by_cases hei' : e = i
            · subst e; exact hbad
            · exact hz.2 e he (by omega)
        · obtain ⟨e, he, hei, hpos, hP⟩ := ho
          refine Or.inr ⟨e, he, by omega, ?_, hP⟩
          simpa only [State.setReg_regs_ne _ _ (by decide : 55 ≠ 53), hpReg] using hpos)
    s₂ hI₀
  have he₁ : Exec w (.assign 55 (.len active)) s s₁ 2 :=
    .assign (GraphMinor.Compute.Crossing.eval_len hb hmw)
  have he₂ : Exec w (.assign 53 (.const 0)) s₁ s₂ 2 :=
    .assign (GraphMinor.Compute.Crossing.eval_const (Nat.two_pow_pos w))
  refine ⟨s', 2 + (2 + t), .seq he₁ (.seq he₂ hex), ?_, hI'.2.1, ?_⟩
  · simp only [Expr.cost] at ht
    have hh : 1 + 6 + (113 + 104 * xs.length) = 120 + 104 * xs.length := by omega
    rw [hh] at ht
    omega
  · rcases hI'.2.2 with hz | ho
    · exact Or.inl ⟨hz.1, fun e he => hz.2 e he he⟩
    · obtain ⟨e, he, _, hp, hP⟩ := ho
      exact Or.inr ⟨e, he, hp, hP⟩

end GraphMinor.Compute
