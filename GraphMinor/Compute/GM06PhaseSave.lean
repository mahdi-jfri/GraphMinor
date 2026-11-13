module

public import GraphMinor.Compute.GM06Reduction4PhaseProgram

/-!
# Saving the cut records before component searches

The component searches in Sections 12 and 13 of our proof of VI (5.7) (outlined in
`GraphMinor/GM06/Alg57Algorithm.lean`) reuse the cut workspace. This pass saves the physical
rotation-record buffer, the shared origin table and the current linkage. It initializes the
copied-space counts, component cursor and return flag from the current core itself.
-/

@[expose] public section
namespace GraphMinor.Compute
open TwoPaths

/-- Registers written while saving component-search inputs. -/
def gm06Reduction4PhaseSaveRegs : List ℕ := [650, 682, 683, 684, 685, 693, 681, 646]

/-- Persistent scratch copies used by all component searches. -/
def gm06Reduction4PhaseSaveArrs : List ℕ := [640, 641, 642]

/-- Saving the actual cut output and current linkage computes every
phase counter and preserves all core memory, including the loop bit. -/
theorem gm06Reduction4PhaseSaveProg_exec {w n m : ℕ} (inner outer records origins : List ℕ)
    (paths : List (List ℕ)) (s : State) (hw : 2 < 2 ^ w)
    (hn : 2 * n < 2 ^ w) (hm : 2 * (m + inner.length + outer.length) < 2 ^ w)
    (hrecords : records.length < 2 ^ w) (horigins : origins.length < 2 ^ w)
    (hpaths : (gm06EncodeRows paths).length < 2 ^ w)
    (hrecordWords : ∀ a ∈ records, a < 2 ^ w) (horiginWords : ∀ a ∈ origins, a < 2 ^ w)
    (hpathWords : ∀ a ∈ gm06EncodeRows paths, a < 2 ^ w)
    (h601 : s.arrs 601 = records) (h626 : s.arrs 626 = origins) (h8 : s.arrs 8 = gm06EncodeRows paths)
    (h100 : s.regs 100 = n) (h12 : (s.arrs 12).length = m)
    (h6 : s.arrs 6 = inner) (h7 : s.arrs 7 = outer) :
    ∃ sf t, Exec w gm06Reduction4PhaseSaveProg s sf t ∧
      t ≤ 50 + 14 * (records.length + origins.length + (gm06EncodeRows paths).length) ∧
      Keeps gm06Reduction4PhaseSaveRegs gm06Reduction4PhaseSaveArrs s sf ∧
      sf.arrs 640 = records ∧ sf.arrs 641 = origins ∧ sf.arrs 642 = gm06EncodeRows paths ∧
      sf.regs 682 = 2 * n ∧ sf.regs 683 = 2 * (m + inner.length + outer.length) ∧
      sf.regs 684 = m ∧ sf.regs 685 = inner.length ∧ sf.regs 693 = 1 ∧ sf.regs 681 = 0 ∧ sf.regs 646 = 0 := by
  obtain ⟨s₁, t₁, he₁, ht₁, hk₁, hd₁⟩ := gm06PhaseCopyProg_exec 601 640 (by decide) records s
    (by omega) hrecords hrecordWords h601
  obtain ⟨s₂, t₂, he₂, ht₂, hk₂, hd₂⟩ := gm06PhaseCopyProg_exec 626 641 (by decide) origins s₁
    (by omega) horigins horiginWords ((hk₁.2 626 (by decide)).trans h626)
  obtain ⟨s₃, t₃, he₃, ht₃, hk₃, hd₃⟩ := gm06PhaseCopyProg_exec 8 642 (by decide) (gm06EncodeRows paths) s₂
    (by omega) hpaths hpathWords ((hk₂.2 8 (by decide)).trans ((hk₁.2 8 (by decide)).trans h8))
  have hk₀₃ : Keeps [650] gm06Reduction4PhaseSaveArrs s s₃ :=
    ((hk₁.mono (fun _ h => h) (by simp [gm06Reduction4PhaseSaveArrs])).trans hk₂
      (fun _ h => h) (by simp [gm06Reduction4PhaseSaveArrs])).trans hk₃
      (fun _ h => h) (by simp [gm06Reduction4PhaseSaveArrs])
  have h100' := (hk₀₃.1 100 (by decide)).trans h100
  have h12' := (congrArg List.length (hk₀₃.2 12 (by decide))).trans h12
  have h6' := (hk₀₃.2 6 (by decide)).trans h6
  have h7' := (hk₀₃.2 7 (by decide)).trans h7
  let aug := m + inner.length + outer.length
  let s₄ := s₃.setReg 682 (2 * n)
  let s₅ := s₄.setReg 683 (2 * aug)
  let s₆ := s₅.setReg 684 m
  let s₇ := s₆.setReg 685 inner.length
  let s₈ := s₇.setReg 693 1
  let s₉ := s₈.setReg 681 0
  let sf := s₉.setReg 646 0
  have he₄ : Exec w (.assign 682 (.op .mul (.const 2) (.reg 100))) s₃ s₄ 4 :=
    .assign (GraphMinor.Compute.Crossing.eval_mul (GraphMinor.Compute.Crossing.eval_const hw)
      (GraphMinor.Compute.Crossing.eval_reg h100' (by omega)) hn)
  have he₅ : Exec w (.assign 683 (.op .mul (.const 2)
      (.op .add (.len 12) (.op .add (.len 6) (.len 7))))) s₄ s₅ 8 :=
    .assign (by
      have h12'' : (s₄.arrs 12).length = m := h12'
      have he := GraphMinor.Compute.Crossing.eval_mul (GraphMinor.Compute.Crossing.eval_const (w := w) hw)
        (GraphMinor.Compute.Crossing.eval_add
          (by simpa only [h12''] using GraphMinor.Compute.Crossing.eval_len (w := w) (s := s₄) (a := 12) rfl (by omega))
          (GraphMinor.Compute.Crossing.eval_add
            (GraphMinor.Compute.Crossing.eval_len (show s₄.arrs 6 = inner from h6') (by omega))
            (GraphMinor.Compute.Crossing.eval_len (show s₄.arrs 7 = outer from h7') (by omega)) (by omega)) (by omega)) (by simpa only [Nat.add_assoc] using hm)
      simpa only [aug, Nat.add_assoc] using he)
  have he₆ : Exec w (.assign 684 (.len 12)) s₅ s₆ 2 := .assign (by
    have he := GraphMinor.Compute.Crossing.eval_len (w := w) (s := s₅) (a := 12) rfl (by change (s₃.arrs 12).length < 2 ^ w; rw [h12']; omega)
    simpa only [show (s₅.arrs 12).length = m from h12'] using he)
  have he₇ : Exec w (.assign 685 (.len 6)) s₆ s₇ 2 :=
    .assign (GraphMinor.Compute.Crossing.eval_len (show s₆.arrs 6 = inner from h6') (by omega))
  have he₈ : Exec w (.assign 693 (.const 1)) s₇ s₈ 2 := .assign (GraphMinor.Compute.Crossing.eval_const (by omega))
  have he₉ : Exec w (.assign 681 (.const 0)) s₈ s₉ 2 := .assign (GraphMinor.Compute.Crossing.eval_const (Nat.two_pow_pos w))
  have hef : Exec w (.assign 646 (.const 0)) s₉ sf 2 := .assign (GraphMinor.Compute.Crossing.eval_const (Nat.two_pow_pos w))
  have hk : Keeps gm06Reduction4PhaseSaveRegs gm06Reduction4PhaseSaveArrs s sf :=
    (((((((hk₀₃.mono (by simp [gm06Reduction4PhaseSaveRegs]) (fun _ h => h)).setReg
      (by simp [gm06Reduction4PhaseSaveRegs]) _).setReg (by simp [gm06Reduction4PhaseSaveRegs]) _).setReg
      (by simp [gm06Reduction4PhaseSaveRegs]) _).setReg (by simp [gm06Reduction4PhaseSaveRegs]) _).setReg
      (by simp [gm06Reduction4PhaseSaveRegs]) _).setReg (by simp [gm06Reduction4PhaseSaveRegs]) _).setReg
      (by simp [gm06Reduction4PhaseSaveRegs]) _
  refine ⟨sf, t₁ + (t₂ + (t₃ + (4 + (8 + (2 + (2 + (2 + (2 + 2)))))))),
    .seq he₁ (.seq he₂ (.seq he₃ (.seq he₄ (.seq he₅ (.seq he₆ (.seq he₇ (.seq he₈ (.seq he₉ hef)))))))),
    by omega, hk, ?_, ?_, ?_, by simp [sf, s₉, s₈, s₇, s₆, s₅, s₄],
    by simp [sf, s₉, s₈, s₇, s₆, s₅, aug], by simp [sf, s₉, s₈, s₇, s₆],
    by simp [sf, s₉, s₈, s₇], by simp [sf, s₉, s₈], by simp [sf, s₉], by simp [sf]⟩
  · exact (hk₃.2 640 (by decide)).trans ((hk₂.2 640 (by decide)).trans hd₁)
  · exact (hk₃.2 641 (by decide)).trans hd₂
  · exact hd₃

end GraphMinor.Compute
