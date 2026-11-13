module

public import GraphMinor.Compute.GM06DeleteSectorEdge

/-!
# Exhausting active edges in a fixed sector

Repeat the finite sector-edge deletion until no eligible edge remains.
Each successful pass decreases the active count by one. The final
unsuccessful pass clears the loop flag. This proves termination and a
polynomial running-time bound without a supplied reduction history.
-/

@[expose] public section
namespace GraphMinor.Compute
open TwoPaths

private theorem bits_set_zero (xs : List ℕ) (hbits : ∀ b ∈ xs, b ≤ 1) (i : ℕ) :
    ∀ b ∈ xs.set i 0, b ≤ 1 := by
  induction xs generalizing i with
  | nil => simp
  | cons a xs ih =>
    cases i with
    | zero =>
      intro b hb
      rcases List.mem_cons.mp hb with rfl | hb
      · exact Nat.zero_le 1
      · exact hbits b (List.mem_cons_of_mem a hb)
    | succ i =>
      intro b hb
      rcases List.mem_cons.mp hb with rfl | hb
      · exact hbits b (by simp)
      · exact ih (fun b hb => hbits b (List.mem_cons_of_mem a hb)) i b hb

/-- Repeatedly delete eligible sector edges until the change flag becomes zero. -/
def gm06ExhaustSectorProg (rot active : Arr) : Cmd :=
  .seq (.assign 60 (.const 1)) (.while (.reg 60) (gm06DeleteSectorEdgeProg rot active))

/-- Sector exhaustion preserves well-formed activity bits and excludes every eligible edge. -/
theorem gm06ExhaustSectorProg_exec {w : ℕ} (rot active : ℕ) (hne : rot ≠ active)
    (xs mask : List ℕ) (p q : ℕ) (s : State) (hw : 2 < 2 ^ w)
    (hn : xs.length < 2 ^ w) (hx : ∀ x ∈ xs, x < 2 ^ w) (hnd : xs.Nodup)
    (hp : p ∈ xs) (hq : q ∈ xs) (hm : 2 * mask.length < 2 ^ w)
    (hbits : ∀ b ∈ mask, b ≤ 1) (ha : s.arrs rot = xs) (hb : s.arrs active = mask)
    (h36 : s.regs 36 = p) (h37 : s.regs 37 = q) :
    ∃ s' t, Exec w (gm06ExhaustSectorProg rot active) s s' t ∧
      t ≤ 2 + (mask.count 1 + 2) * (18 + mask.length * (120 + 104 * xs.length)) ∧
      Keeps [53, 55, 38, 50, 40, 41, 42, 43, 54, 60] [active] s s' ∧
      (s'.arrs active).length = mask.length ∧ (∀ b ∈ s'.arrs active, b ≤ 1) ∧
      (s'.arrs active).count 1 ≤ mask.count 1 ∧ s'.regs 60 = 0 ∧
      ∀ e (he : e < (s'.arrs active).length),
        ¬((s'.arrs active)[e] = 1 ∧ (gm06RotationSectorFlag xs p q (2 * e) = 1 ∨
          gm06RotationSectorFlag xs p q (2 * e + 1) = 1)) := by
  let R := [53, 55, 38, 50, 40, 41, 42, 43, 54, 60]
  let I : State → Prop := fun st => Keeps R [active] s st ∧
    (st.arrs active).length = mask.length ∧ (∀ b ∈ st.arrs active, b ≤ 1) ∧
    (st.regs 60 = 0 ∨ st.regs 60 = 1) ∧
    (st.regs 60 = 0 → ∀ e (he : e < (st.arrs active).length),
      ¬((st.arrs active)[e] = 1 ∧ (gm06RotationSectorFlag xs p q (2 * e) = 1 ∨
        gm06RotationSectorFlag xs p q (2 * e + 1) = 1))) ∧
    (st.arrs active).count 1 ≤ mask.count 1
  let μ : State → ℕ := fun st => if st.regs 60 = 0 then 0 else (st.arrs active).count 1 + 1
  let B := 17 + mask.length * (120 + 104 * xs.length)
  have hw1 : 1 < 2 ^ w := by omega
  let s₀ := s.setReg 60 1
  have hI₀ : I s₀ := by
    refine ⟨(Keeps.refl _ _ s).setReg (by simp [R]) _, ?_, ?_, Or.inr (by simp [s₀]), ?_, ?_⟩
    · simpa only [s₀, State.setReg_arrs, hb]
    · simpa only [s₀, State.setReg_arrs, hb] using hbits
    · intro hz
      have hh : (1 : ℕ) = 0 := by simpa [s₀] using hz
      cases hh
    · simp only [s₀, State.setReg_arrs, hb, le_refl]
  obtain ⟨s', t, he, ht, hI', hzero⟩ := GraphMinor.Compute.Crossing.while_exec (w := w) (cond := .reg 60)
    (body := gm06DeleteSectorEdgeProg rot active) I μ (fun _ => 0) B
    (fun st h => by
      obtain ⟨_, _, _, hflag, _, _⟩ := h
      refine ⟨st.regs 60, GraphMinor.Compute.Crossing.eval_reg rfl ?_⟩
      rcases hflag with hh | hh
      · rw [hh]; exact Nat.two_pow_pos w
      · rw [hh]; exact hw1)
    (fun st h hrun => by
      obtain ⟨hk, hlen, hbit, hflag, _, hcount⟩ := h
      have hflagOne : st.regs 60 = 1 := by
        rcases hflag with hh | hh
        · exact False.elim (hrun (GraphMinor.Compute.Crossing.eval_reg hh (Nat.two_pow_pos w)))
        · exact hh
      obtain ⟨st', t', hex, htime, hk', hd⟩ := gm06DeleteSectorEdgeProg_exec rot active xs
        (st.arrs active) p q st hw hn hx hnd hp hq
        (by simpa only [hlen] using hm) hbit
        ((hk.2 rot (by simpa only [List.mem_singleton] using hne)).trans ha) rfl
        ((hk.1 36 (by simp [R])).trans h36) ((hk.1 37 (by simp [R])).trans h37)
      have htime' : t' ≤ B := by simpa only [B, hlen] using htime
      have hframe : Keeps R [active] s st' := hk.trans hk' (by simp [R]) (by simp)
      refine ⟨st', t', hex, by simpa using htime', ?_, ?_⟩
      · rcases hd with ⟨hz, harr, hnone⟩ | ⟨ho, e, he, _, harr, _, _, hdec⟩
        · refine ⟨hframe, ?_, ?_, Or.inl hz, ?_, ?_⟩
          · simpa only [harr] using hlen
          · simpa only [harr] using hbit
          · intro _; simpa only [harr] using hnone
          · simpa only [harr] using hcount
        · refine ⟨hframe, ?_, ?_, Or.inr ho, ?_, ?_⟩
          · simpa only [harr, List.length_set] using hlen
          · simpa only [harr] using bits_set_zero (st.arrs active) hbit e
          · intro hz
            have hh : (1 : ℕ) = 0 := ho.symm.trans hz
            cases hh
          · omega
      · rcases hd with ⟨hz, _, _⟩ | ⟨ho, e, he, _, _, _, _, hdec⟩
        · simp [μ, hz, hflagOne]
        · simp only [μ, ho, hflagOne, Nat.one_ne_zero, ite_false]
          omega)
    s₀ hI₀
  have hflagZero : s'.regs 60 = 0 := by
    have hh : s'.regs 60 < 2 ^ w ∧ s'.regs 60 = 0 := by
      simpa only [Expr.eval, checkWord_eq_some] using hzero
    exact hh.2
  obtain ⟨hk, hlen, hbit, _, hnone, hcount⟩ := hI'
  have hμ : μ s₀ + 1 = mask.count 1 + 2 := by
    simp [μ, s₀, hb]
  have hB : (Expr.reg 60).cost + B = 18 + mask.length * (120 + 104 * xs.length) := by
    simp only [Expr.cost, B]
    omega
  simp only [Nat.add_zero] at ht
  rw [hμ, hB] at ht
  refine ⟨s', 2 + t, .seq (.assign (GraphMinor.Compute.Crossing.eval_const hw1)) he,
    by omega, hk, hlen, hbit, hcount, hflagZero, hnone hflagZero⟩

end GraphMinor.Compute
