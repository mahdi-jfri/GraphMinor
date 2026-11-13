module

public import GraphMinor.Compute.GM06Apply4RowProgram
public import GraphMinor.Compute.GM06Apply4Install
import GraphMinor.Compute.GM06RowPositions

/-!
# Applying Reduction 4 to the complete finite linkage

Section 13 of our proof of VI (5.7) (outlined in `GraphMinor/GM06/Alg57Algorithm.lean`) records the
reduction, replaces one path by the projected candidate followed by
its retained suffix, and clears the continuation and cache flags.
The old path is read from the full linkage encoding. The program
installs the resulting row in that encoding and preserves every
other path and all drawing data. A Reduction 4 undo leaves its
terminal linkage unchanged, so the record needs only its tag and
the selected path/contact indices.
-/

@[expose] public section
namespace GraphMinor.Compute
open TwoPaths

/-- Reduction tag, selected linkage row and positive contact position. -/
def gm06Apply4Record (i j : ℕ) : List ℕ := [4, i, j]

/-- Exact complete linkage after the projected prefix/suffix splice. -/
def gm06Apply4Paths (replacement : List ℕ) (paths : List (List ℕ)) (i j : ℕ) : List (List ℕ) :=
  paths.set i (gm06Apply4Row gm06ProjectCutDart replacement (paths[i]?.getD []) j)

/-- Save the selected Reduction 4 event in record array 638. -/
def gm06Apply4RecordProg : Cmd :=
  .seq (.alloc 638 (.const 3))
    (.seq (.write 638 (.const 0) (.const 4))
      (.seq (.write 638 (.const 1) (.reg 669)) (.write 638 (.const 2) (.reg 678))))

/-- Record construction reads the actual selected indices. -/
theorem gm06Apply4RecordProg_exec {w i j : ℕ} (s : State) (hw : 4 < 2 ^ w)
    (hi : i < 2 ^ w) (hj : j < 2 ^ w) (h669 : s.regs 669 = i) (h678 : s.regs 678 = j) :
    ∃ sf, Exec w gm06Apply4RecordProg s sf 13 ∧ Keeps [] [638] s sf ∧
      sf.arrs 638 = gm06Apply4Record i j := by
  let s₀ := s.setArr 638 (List.replicate 3 0)
  let s₁ := s₀.writeArr 638 0 4
  let s₂ := s₁.writeArr 638 1 i
  let sf := s₂.writeArr 638 2 j
  have he₀ : Exec w (.alloc 638 (.const 3)) s s₀ 4 :=
    .alloc (GraphMinor.Compute.Crossing.eval_const (by omega))
  have he₁ : Exec w (.write 638 (.const 0) (.const 4)) s₀ s₁ 3 :=
    .write (GraphMinor.Compute.Crossing.eval_const (Nat.two_pow_pos w))
      (GraphMinor.Compute.Crossing.eval_const hw) (by simp [s₀])
  have he₂ : Exec w (.write 638 (.const 1) (.reg 669)) s₁ s₂ 3 :=
    .write (GraphMinor.Compute.Crossing.eval_const (by omega))
      (GraphMinor.Compute.Crossing.eval_reg h669 hi) (by simp [s₁, s₀, State.writeArr])
  have he₃ : Exec w (.write 638 (.const 2) (.reg 678)) s₂ sf 3 :=
    .write (GraphMinor.Compute.Crossing.eval_const (by omega))
      (GraphMinor.Compute.Crossing.eval_reg h678 hj) (by simp [s₂, s₁, s₀, State.writeArr])
  exact ⟨sf, .seq he₀ (.seq he₁ (.seq he₂ he₃)),
    ((((Keeps.refl _ _ s).setArr (by simp) _).writeArr (by simp) _ _).writeArr (by simp) _ _).writeArr (by simp) _ _,
    by simp [sf, s₂, s₁, s₀, State.writeArr, gm06Apply4Record]⟩

/-- Set continuation bit b to zero and invalidate cut/linkage-index tables. -/
def gm06Apply4ClearProg : Cmd :=
  .seq (.assign 671 (.const 0)) (.seq (.assign 672 (.const 0)) (.assign 673 (.const 0)))

/-- Record, select, splice and install the linkage row, then clear flags. -/
def gm06Apply4Prog : Cmd :=
  .seq gm06Apply4RecordProg
    (.seq gm06ReadApply4RowProg
      (.seq gm06Apply4RowProg (.seq gm06InstallApply4RowProg gm06Apply4ClearProg)))

/-- Full register frame of the finite APPLY_4 command. -/
def gm06Apply4Regs : List ℕ :=
  [650, 651, 652, 655, 660, 661, 662, 664, 668, 665, 666, 667, 659, 671, 672, 673]

/-- Only the linkage encoding, its scratch rows and event record change. -/
def gm06Apply4Arrs : List ℕ := [638, 610, 613, 611, 637, 601, 600, 602]

/-- APPLY_4 returns the exact complete updated linkage and event record,
sets b to zero and invalidates both caches, in linear encoded-input time.
The replacement is actual cut darts, whose projection is computed here. -/
theorem gm06Apply4Prog_exec {w i j : ℕ} (replacement : List ℕ) (paths : List (List ℕ))
    (hi : i < paths.length) (hj : j ≤ paths[i].length) (s : State)
    (hw : 4 < 2 ^ w) (hfit : (gm06EncodeRows paths).length + replacement.length + 3 < 2 ^ w)
    (hwords : ∀ x ∈ gm06EncodeRows paths, x < 2 ^ w) (hnew : ∀ d ∈ replacement, d < 2 ^ w)
    (h600 : s.arrs 600 = gm06EncodeRows paths) (h635 : s.arrs 635 = replacement)
    (h669 : s.regs 669 = i) (h678 : s.regs 678 = j) :
    ∃ sf t, Exec w gm06Apply4Prog s sf t ∧
      t ≤ 300 + 40 * i + 300 * (gm06EncodeRows paths).length + 150 * replacement.length ∧
      Keeps gm06Apply4Regs gm06Apply4Arrs s sf ∧
      sf.arrs 600 = gm06EncodeRows (gm06Apply4Paths replacement paths i j) ∧
      sf.arrs 638 = gm06Apply4Record i j ∧ sf.regs 671 = 0 ∧ sf.regs 672 = 0 ∧ sf.regs 673 = 0 := by
  have hcode : (gm06EncodeRows paths).length < 2 ^ w := by omega
  have hiw : i < 2 ^ w := hi.trans (hwords _ (by simp [gm06EncodeRows]))
  have hpre := gm06RowsPrefixLength_le paths (i + 1)
  rw [gm06RowsPrefixLength_succ paths hi] at hpre
  have htotal : (gm06EncodeRows paths).length = 1 + (gm06EncodeRowsPayload paths).length := by
    simp only [gm06EncodeRows, List.length_cons]
    omega
  have holdLen : paths[i].length ≤ (gm06EncodeRows paths).length := by omega
  have holdWords : ∀ d ∈ paths[i], d < 2 ^ w := by
    intro d hd
    apply hwords d
    simp only [gm06EncodeRows, gm06EncodeRowsPayload, List.mem_cons, List.mem_flatMap]
    exact Or.inr ⟨paths[i], List.getElem_mem hi, by simp [gm06EncodeNatList, hd]⟩
  let row := gm06Apply4Row gm06ProjectCutDart replacement paths[i] j
  have hrowLen : row.length = replacement.length + (paths[i].length - j) := by
    simp only [row, gm06Apply4Row, List.length_append, List.length_map, List.length_drop]
  have hrowWords : ∀ d ∈ row, d < 2 ^ w := by
    intro d hd
    rcases List.mem_append.mp hd with hd | hd
    · obtain ⟨dart, hmem, rfl⟩ := List.mem_map.mp hd
      exact (gm06ProjectCutDart_le dart).trans_lt (hnew dart hmem)
    · exact holdWords d (List.mem_of_mem_drop hd)
  have hnewLen : (gm06EncodeRows (paths.set i row)).length < 2 ^ w := by
    have he := gm06EncodeRows_set_length paths i hi row
    rw [hrowLen] at he
    omega
  obtain ⟨s₁, he₁, hk₁, hd₁⟩ := gm06Apply4RecordProg_exec s hw hiw (by omega) h669 h678
  obtain ⟨s₂, t₂, he₂, ht₂, hk₂, hd₂⟩ := gm06ReadApply4RowProg_exec paths i hi s₁ (by omega) hcode hwords
    ((hk₁.2 600 (by decide)).trans h600) ((hk₁.1 669 (by simp)).trans h669)
  have hk₁₂ : Keeps gm06Apply4Regs gm06Apply4Arrs s s₂ :=
    (hk₁.mono (by simp [gm06Apply4Regs]) (by simp [gm06Apply4Arrs])).trans hk₂
      (by simp [gm06Apply4Regs]) (by simp [gm06Apply4Arrs])
  obtain ⟨s₃, t₃, he₃, ht₃, hk₃, hd₃⟩ := gm06Apply4RowProg_exec replacement paths[i] s₂ hw
    (by omega) hj hnew holdWords ((hk₁₂.2 635 (by decide)).trans h635) hd₂
    ((hk₁₂.1 678 (by decide)).trans h678)
  have hk₁₃ : Keeps gm06Apply4Regs gm06Apply4Arrs s s₃ :=
    hk₁₂.trans hk₃ (by simp [gm06Apply4Regs]) (by simp [gm06Apply4Arrs])
  obtain ⟨s₄, t₄, he₄, ht₄, hk₄, hd₄, _⟩ := gm06InstallApply4RowProg_exec paths i hi row s₃ (by omega)
    hcode hnewLen hwords hrowWords ((hk₃.2 600 (by decide)).trans ((hk₂.2 600 (by decide)).trans
      ((hk₁.2 600 (by decide)).trans h600))) hd₃ ((hk₁₃.1 669 (by decide)).trans h669)
  have hk₁₄ : Keeps gm06Apply4Regs gm06Apply4Arrs s s₄ :=
    hk₁₃.trans hk₄ (by simp [gm06Apply4Regs]) (by simp [gm06Apply4Arrs])
  let sf := ((s₄.setReg 671 0).setReg 672 0).setReg 673 0
  have hef : Exec w gm06Apply4ClearProg s₄ sf 6 :=
    .seq (.assign (GraphMinor.Compute.Crossing.eval_const (Nat.two_pow_pos w)))
      (.seq (.assign (GraphMinor.Compute.Crossing.eval_const (Nat.two_pow_pos w)))
        (.assign (GraphMinor.Compute.Crossing.eval_const (Nat.two_pow_pos w))))
  refine ⟨sf, 13 + (t₂ + (t₃ + (t₄ + 6))), .seq he₁ (.seq he₂ (.seq he₃ (.seq he₄ hef))), ?_,
    ((hk₁₄.setReg (by simp [gm06Apply4Regs]) _).setReg (by simp [gm06Apply4Regs]) _).setReg (by simp [gm06Apply4Regs]) _,
    ?_, ?_, by simp [sf], by simp [sf], by simp [sf]⟩
  · rw [hrowLen] at ht₄
    omega
  · simpa only [sf, State.setReg_arrs, gm06Apply4Paths, List.getElem?_eq_getElem hi, Option.getD_some] using hd₄
  · exact (hk₄.2 638 (by decide)).trans ((hk₃.2 638 (by decide)).trans ((hk₂.2 638 (by decide)).trans hd₁))

end GraphMinor.Compute
