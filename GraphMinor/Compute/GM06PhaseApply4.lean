module

public import GraphMinor.Compute.GM06PhaseRows
public import GraphMinor.Compute.GM06Apply4Program
import GraphMinor.Compute.GM06RowPositions
import GraphMinor.Compute.WhileRounds

/-!
# Installing a successful Reduction 4 in the current core

Section 13 of our proof of VI (5.7) (outlined in `GraphMinor/GM06/Alg57Algorithm.lean`) changes one
linkage row and clears the loop bit. This program reads the current
linkage in core array 8, applies the projected replacement and tail
splice, writes the complete encoding back, and returns success. The
finite event record stays in scratch. Only contractions have numeric
records in the persistent undo history.
-/

@[expose] public section
namespace GraphMinor.Compute
open TwoPaths

/-- Apply the selected contact to the current core linkage.
Registers 681/678 and array 635 contain the component, contact and
actual copied directed replacement row returned by the search. -/
def gm06PhaseApply4Prog : Cmd :=
  .seq (gm06PhaseCopyProg 8 600)
    (.seq (.assign 669 (.reg 681))
      (.seq gm06Apply4Prog
        (.seq (gm06PhaseCopyProg 600 8)
          (.seq (.assign 329 (.const 0)) (.assign 646 (.const 1))))))

/-- Register frame, including the explicit core bit and return bit. -/
def gm06PhaseApply4Regs : List ℕ := [650, 669, 329, 646] ++ gm06Apply4Regs

/-- Array frame, including the complete updated core linkage. -/
def gm06PhaseApply4Arrs : List ℕ := 8 :: gm06Apply4Arrs

/-- A successful search installs exactly the pure full-linkage
APPLY_4 output. Every other core array, the contraction history,
and all registers outside the explicit frame are unchanged. -/
theorem gm06PhaseApply4Prog_exec {w i j : ℕ} (replacement : List ℕ) (paths : List (List ℕ))
    (hi : i < paths.length) (hj : j ≤ paths[i].length) (s : State)
    (hw : 4 < 2 ^ w) (hfit : (gm06EncodeRows paths).length + replacement.length + 3 < 2 ^ w)
    (hwords : ∀ a ∈ gm06EncodeRows paths, a < 2 ^ w) (hnew : ∀ d ∈ replacement, d < 2 ^ w)
    (h8 : s.arrs 8 = gm06EncodeRows paths) (h635 : s.arrs 635 = replacement)
    (h681 : s.regs 681 = i) (h678 : s.regs 678 = j) :
    ∃ sf t, Exec w gm06PhaseApply4Prog s sf t ∧
      t ≤ 350 + 40 * i + 340 * (gm06EncodeRows paths).length + 170 * replacement.length ∧
      Keeps gm06PhaseApply4Regs gm06PhaseApply4Arrs s sf ∧
      sf.arrs 8 = gm06EncodeRows (gm06Apply4Paths replacement paths i j) ∧
      sf.regs 329 = 0 ∧ sf.regs 646 = 1 := by
  have hiw : i < 2 ^ w := hi.trans (hwords _ (by simp [gm06EncodeRows]))
  obtain ⟨s₁, t₁, he₁, ht₁, hk₁, hd₁⟩ := gm06PhaseCopyProg_exec 8 600 (by decide) (gm06EncodeRows paths) s
    (by omega) (by omega) hwords h8
  let s₂ := s₁.setReg 669 i
  have he₂ : Exec w (.assign 669 (.reg 681)) s₁ s₂ 2 :=
    .assign (GraphMinor.Compute.Crossing.eval_reg ((hk₁.1 681 (by decide)).trans h681) hiw)
  have hk₂ : Keeps [650, 669] [600] s s₂ :=
    (hk₁.mono (by simp) (fun _ h => h)).setReg (by simp) _
  obtain ⟨s₃, t₃, he₃, ht₃, hk₃, hd₃, _, _, _, _⟩ := gm06Apply4Prog_exec replacement paths hi hj s₂ hw hfit hwords hnew
    (by simpa only [s₂, State.setReg_arrs] using hd₁)
    ((hk₂.2 635 (by decide)).trans h635) (by simp [s₂]) ((hk₂.1 678 (by decide)).trans h678)
  have hnewLen : (gm06EncodeRows (gm06Apply4Paths replacement paths i j)).length ≤
      (gm06EncodeRows paths).length + replacement.length := by
    have hlen := gm06EncodeRows_set_length paths i hi
      (gm06Apply4Row gm06ProjectCutDart replacement (paths[i]?.getD []) j)
    simp only [gm06Apply4Row, List.getElem?_eq_getElem hi, Option.getD_some,
      List.length_append, List.length_map, List.length_drop] at hlen
    simp only [gm06Apply4Paths, gm06Apply4Row, List.getElem?_eq_getElem hi, Option.getD_some]
    omega
  have hnewWords : ∀ a ∈ gm06EncodeRows (gm06Apply4Paths replacement paths i j), a < 2 ^ w := by
    have h600words : ∀ a ∈ s₂.arrs 600, a < 2 ^ w := by
      simpa only [s₂, State.setReg_arrs, hd₁] using hwords
    simpa only [hd₃] using he₃.arrs_lt 600 h600words
  obtain ⟨s₄, t₄, he₄, ht₄, hk₄, hd₄⟩ := gm06PhaseCopyProg_exec 600 8 (by decide)
    (gm06EncodeRows (gm06Apply4Paths replacement paths i j)) s₃ (by omega) (by omega) hnewWords hd₃
  let s₅ := s₄.setReg 329 0
  let sf := s₅.setReg 646 1
  have he₅ : Exec w (.assign 329 (.const 0)) s₄ s₅ 2 := .assign (GraphMinor.Compute.Crossing.eval_const (Nat.two_pow_pos w))
  have hef : Exec w (.assign 646 (.const 1)) s₅ sf 2 := .assign (GraphMinor.Compute.Crossing.eval_const (by omega))
  have hk₀₃ : Keeps gm06PhaseApply4Regs gm06PhaseApply4Arrs s s₃ :=
    (hk₂.mono (by simp [gm06PhaseApply4Regs]) (by simp [gm06PhaseApply4Arrs, gm06Apply4Arrs])).trans hk₃
      (fun _ h => List.mem_append_right _ h) (fun _ h => List.mem_cons_of_mem _ h)
  refine ⟨sf, t₁ + (2 + (t₃ + (t₄ + (2 + 2)))), .seq he₁ (.seq he₂ (.seq he₃ (.seq he₄ (.seq he₅ hef)))),
    by omega, ?_, by simpa only [sf, s₅, State.setReg_arrs] using hd₄, by simp [sf, s₅], by simp [sf]⟩
  exact ((hk₀₃.trans hk₄ (by simp [gm06PhaseApply4Regs]) (by simp [gm06PhaseApply4Arrs])).setReg
    (by simp [gm06PhaseApply4Regs]) _).setReg (by simp [gm06PhaseApply4Regs]) _

end GraphMinor.Compute
