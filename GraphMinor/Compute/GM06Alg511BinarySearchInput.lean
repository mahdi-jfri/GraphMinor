module

public import GraphMinor.Compute.GM06Alg511BinaryLoad
public import GraphMinor.Compute.GM06Alg511Flow
public import GraphMinor.Compute.GM06Alg511BinaryIntegral
public import GraphMinor.Compute.GM06Alg511FlowFlag
import Mathlib.Tactic

/-!
# Binary drawing data and the ordinary maximum-flow layout

Keep two rows: the complete binary drawing input and its ordinary
labelled graph/cuff encoding for the verified maximum-flow program.
The second row repeats only adjacency, cuff membership and the path
count, all determined by the supplied graph labels. It contains no
paths, separator or answer. No geometric or integer magnitude choice
enters either row.

Load the binary input first and retain the flow row for the second
initial check of VI (5.11), page 134. Its large integers remain sign
and digit lists. The loader has linear cost in the complete input.
-/

@[expose] public section
namespace GraphMinor.Compute
open TwoPaths

/-- The ordinary graph/cuff input for maximum flow, alongside the
binary drawing fields. Both rows describe only the supplied instance. -/
def gm06Alg511BinarySearchRows (x : GM06Alg511BinaryInput) : List (List ℕ) :=
  [x.words, encDisjointPathsIn x.toWindingInput.drawing.flowInput]

/-- The complete binary search input, counting every supplied bit. -/
def gm06Alg511BinarySearchWords (x : GM06Alg511BinaryInput) : List ℕ :=
  gm06EncodeRows (gm06Alg511BinarySearchRows x)

/-- The complete code retains every original binary drawing field. -/
theorem gm06Alg511BinarySearchWords_injective : Function.Injective gm06Alg511BinarySearchWords := by
  intro x y h
  have hh := gm06EncodeRows_injective h
  exact GM06Alg511BinaryInput.words_injective (List.cons.inj hh).1

/-- The two stored row lengths and their three headers account
for the whole code. Thus integer bits count towards its length. -/
theorem gm06Alg511BinarySearchWords_length (x : GM06Alg511BinaryInput) :
    (gm06Alg511BinarySearchWords x).length =
      3 + x.words.length + (encDisjointPathsIn x.toWindingInput.drawing.flowInput).length := by
  simp only [gm06Alg511BinarySearchWords, gm06Alg511BinarySearchRows, gm06EncodeRows,
    gm06EncodeRowsPayload, gm06EncodeNatList, List.flatMap_cons, List.flatMap_nil,
    List.length_cons, List.length_nil, List.length_append]
  omega

/-- Select both plain input layouts, copy the binary drawing row
to array zero and load its fields and integrality operands. -/
def gm06Alg511BinaryLoadSearchProg : Cmd :=
  .seq (gm06Alg511SelectFieldProg 0 1000 0)
    (.seq (gm06Alg511SelectFieldProg 0 1001 1)
      (.seq (gm06Alg511CopyRowProg 1000 0) gm06Alg511BinaryLoadProg))

/-- The binary search loader returns exactly the supplied nine
fields, target sign/digit operands and graph path count. It retains
the full binary row and the ordinary Menger row in arrays 1000 and
1001. No interpreted integer magnitude is put in a register. -/
theorem gm06Alg511BinaryLoadSearchProg_exec {w : ℕ} (x : GM06Alg511BinaryInput) (s : State)
    (hw : 3 < 2 ^ w) (hA : s.arrs 0 = gm06Alg511BinarySearchWords x)
    (hfit : (gm06Alg511BinarySearchWords x).length + 2 < 2 ^ w)
    (hk : x.pathCount < 2 ^ w) (hwords : ∀ word ∈ gm06Alg511BinarySearchWords x, word < 2 ^ w) :
    ∃ t u, Exec w gm06Alg511BinaryLoadSearchProg s t u ∧
      u ≤ 3000 + 400 * (gm06Alg511BinarySearchWords x).length ∧
      (∀ i : Fin 9, t.arrs (gm06Alg511BinaryFieldTarget i.val) = x.rows[i.val]'i.isLt) ∧
      t.regs 52 = x.pathCount ∧ t.regs 2704 = x.numerator.negative.toNat ∧ t.regs 2705 = x.denominator.negative.toNat ∧
      t.arrs 2700 = x.numerator.digits.map Bool.toNat ∧ t.arrs 2701 = x.denominator.digits.map Bool.toNat ∧
      t.arrs 1000 = x.words ∧ t.arrs 1001 = encDisjointPathsIn x.toWindingInput.drawing.flowInput := by
  have hlen := gm06Alg511BinarySearchWords_length x
  have hwholeFit : (gm06EncodeRows (gm06Alg511BinarySearchRows x)).length < 2 ^ w := by
    change (gm06Alg511BinarySearchWords x).length < 2 ^ w
    omega
  have hbinaryFit : x.words.length + 2 < 2 ^ w := by omega
  have hflowFit : (encDisjointPathsIn x.toWindingInput.drawing.flowInput).length < 2 ^ w := by omega
  have hbinaryWords : ∀ v ∈ x.words, v < 2 ^ w :=
    fun v hv => hwords v (gm06Alg511_mem_encoded_row (by simp [gm06Alg511BinarySearchRows]) hv)
  obtain ⟨s₁, u₁, he₁, ht₁, hb₁, hk₁⟩ := gm06Alg511SelectFieldProg_exec (w := w) 0 1000 (by decide)
    (gm06Alg511BinarySearchRows x) 0 (by change 0 < 2; decide) s (by omega) hA hwholeFit hwords
  obtain ⟨s₂, u₂, he₂, ht₂, hf₂, hk₂⟩ := gm06Alg511SelectFieldProg_exec (w := w) 0 1001 (by decide)
    (gm06Alg511BinarySearchRows x) 1 (by change 1 < 2; decide) s₁ (by omega) ((hk₁ 0 (by decide)).trans hA) hwholeFit hwords
  have hb₂ : s₂.arrs 1000 = x.words := (hk₂ 1000 (by decide)).trans hb₁
  obtain ⟨s₃, u₃, he₃, ht₃, hk₃, hin₃⟩ := gm06Alg511CopyRowProg_exec (w := w) 1000 0 (by decide) x.words s₂
    (by omega) (by omega) hbinaryWords hb₂
  obtain ⟨t, u₄, he₄, ht₄, hfields, hcount, hnSign, hdSign, hnDigits, hdDigits, _, hk₄⟩ :=
    gm06Alg511BinaryLoadProg_exec x s₃ hw hin₃ hbinaryFit hk hbinaryWords
  refine ⟨t, u₁ + (u₂ + (u₃ + u₄)), .seq he₁ (.seq he₂ (.seq he₃ he₄)), ?_, hfields, hcount,
    hnSign, hdSign, hnDigits, hdDigits, ?_, ?_⟩
  · change u₁ ≤ 18 + 17 * 0 + 22 * x.words.length at ht₁
    change u₂ ≤ 18 + 17 * 1 + 22 * (encDisjointPathsIn x.toWindingInput.drawing.flowInput).length at ht₂
    omega
  · exact (hk₄ 1000 (by decide)).trans ((hk₃.2 1000 (by decide)).trans hb₂)
  · exact (hk₄ 1001 (by decide)).trans ((hk₃.2 1001 (by decide)).trans hf₂)

/-- Copy the retained ordinary graph row to the verified Menger
program's input. This is used only after integrality succeeds. -/
def gm06Alg511BinaryPrepareFlowProg : Cmd := gm06Alg511CopyRowProg 1001 0

/-- Retained supplied tables after the two initial checks. They
contain only graph fields and input words, with no answer attached. -/
def gm06Alg511BinaryLoadedTables (x : GM06Alg511BinaryInput) (s : State) : Prop :=
  (∀ i : Fin 9, s.arrs (gm06Alg511BinaryFieldTarget i.val) = x.rows[i.val]'i.isLt) ∧
    s.arrs 1000 = x.words ∧ s.arrs 1001 = encDisjointPathsIn x.toWindingInput.drawing.flowInput

/-- A transition preserving the nine field arrays and two saved
input rows retains the supplied table interpretation. -/
theorem gm06Alg511BinaryLoadedTables.frame {x : GM06Alg511BinaryInput} {s t : State}
    (h : gm06Alg511BinaryLoadedTables x s)
    (hf : ∀ i : Fin 9, t.arrs (gm06Alg511BinaryFieldTarget i.val) = s.arrs (gm06Alg511BinaryFieldTarget i.val))
    (hb : t.arrs 1000 = s.arrs 1000) (hflow : t.arrs 1001 = s.arrs 1001) :
    gm06Alg511BinaryLoadedTables x t :=
  ⟨fun i => (hf i).trans (h.1 i), hb.trans h.2.1, hflow.trans h.2.2⟩

private theorem integral_field_not_written (i : Fin 9) :
    gm06Alg511BinaryFieldTarget i.val ∉ gm06Alg511BinaryIntegralProg.writtenArrs := by
  fin_cases i <;> decide

private theorem flow_field_not_written (i : Fin 9) :
    gm06Alg511BinaryFieldTarget i.val ∉ gm06Alg511FlowFlagProg.writtenArrs := by
  fin_cases i <;> decide

private theorem integral_saved_not_written (a : ℕ) (ha : a = 1000 ∨ a = 1001) :
    a ∉ gm06Alg511BinaryIntegralProg.writtenArrs := by
  rcases ha with rfl | rfl <;> decide

private theorem flow_saved_not_written (a : ℕ) (ha : a = 1000 ∨ a = 1001) :
    a ∉ gm06Alg511FlowFlagProg.writtenArrs := by
  rcases ha with rfl | rfl <;> decide

/-- Run maximum flow on its retained ordinary input, then restore
the graph path count from its supplied one-word row. -/
def gm06Alg511BinaryFlowProg : Cmd :=
  .seq gm06Alg511BinaryPrepareFlowProg
    (.seq gm06Alg511FlowFlagProg (.assign 52 (.read 1501 (.const 0))))

/-- Check integrality first, and run maximum flow only if it
succeeds, exactly in the order of VI (5.11), page 134. -/
def gm06Alg511BinaryInitialChecksProg : Cmd :=
  .seq gm06Alg511BinaryLoadSearchProg
    (.seq gm06Alg511BinaryIntegralProg (.ite (.reg 0) gm06Alg511BinaryFlowProg .skip))

/-- Both initial checks are executed from the complete binary input.
The bit is exactly integrality and existence of a full finite flow
family. Success also provides the verified raw predecessor/successor
path system needed to compute the initial linkage and its winding. -/
theorem gm06Alg511BinaryInitialChecksProg_exec :
    ∃ C c : ℕ, 1 ≤ C ∧ 1 ≤ c ∧ ∀ (x : GM06Alg511BinaryInput) (s : State) (w : ℕ),
      x.denominator.value ≠ 0 → 3 < 2 ^ w →
      (gm06Alg511BinarySearchWords x).length + 2 < 2 ^ w →
      x.pathCount + x.numerator.digits.length + x.denominator.digits.length + 4 < 2 ^ w →
      wordSize c (disjointPathsSize x.toWindingInput.drawing.flowInput) ≤ w →
      s.arrs 0 = gm06Alg511BinarySearchWords x →
      (∀ word ∈ gm06Alg511BinarySearchWords x, word < 2 ^ w) →
      ∃ t u, Exec w gm06Alg511BinaryInitialChecksProg s t u ∧
        u ≤ 4000 + 500 * (gm06Alg511BinarySearchWords x).length +
          2700 * (x.pathCount + x.numerator.digits.length + x.denominator.digits.length + 2) ^ 2 +
          C * (x.pathCount + x.vertexCount + 1) ^ 3 ∧
        gm06Alg511BinaryLoadedTables x t ∧ t.regs 52 = x.pathCount ∧ t.regs 0 < 2 ∧
        (t.regs 0 = 1 ↔
          (∃ m : ℤ, (x.pathCount : ℝ) * ((x.numerator.value : ℝ) / x.denominator.value) = m) ∧
          ∃ P : Fin x.pathCount → ABWalk x.toWindingInput.drawing.flowGraph
            x.toWindingInput.drawing.flowInput.A x.toWindingInput.drawing.flowInput.B,
              PairwiseVertexDisjoint P ∧ ∀ i, (P i).walk.IsPath) ∧
        (t.regs 0 = 1 →
          IsValidPathSystem x.toWindingInput.drawing.flowGraph
            x.toWindingInput.drawing.flowInput.A x.toWindingInput.drawing.flowInput.B
            (decUsed x.vertexCount (t.arrs outArr)) (decPred x.vertexCount (t.arrs outArr)) (decSucc x.vertexCount (t.arrs outArr)) ∧
          (pathStarts (decUsed x.vertexCount (t.arrs outArr)) (decPred x.vertexCount (t.arrs outArr))).card = x.pathCount ∧
          (t.arrs outArr).length = 1 + 3 * x.vertexCount) := by
  obtain ⟨C, c, hC, hc, hflow⟩ := gm06Alg511FlowFlagProg_exec_with_pathSystem
  refine ⟨C, c, hC, hc, ?_⟩
  intro x s w hden hw hfit hsize hwflow hinput hwords
  have hk : x.pathCount < 2 ^ w := by omega
  have hlen := gm06Alg511BinarySearchWords_length x
  obtain ⟨s₁, u₁, he₁, ht₁, hfields, hk₁, _, _, ha₁, hd₁, hb₁, hf₁⟩ :=
    gm06Alg511BinaryLoadSearchProg_exec x s hw hinput hfit hk hwords
  obtain ⟨s₂, u₂, flag, he₂, ht₂, hflag, hbit, hiff⟩ :=
    gm06Alg511BinaryIntegralProg_exec x.pathCount x.numerator x.denominator s₁ hden hw hsize hk₁ ha₁ hd₁
  have hkeepTables : gm06Alg511BinaryLoadedTables x s₂ :=
    (show gm06Alg511BinaryLoadedTables x s₁ from ⟨hfields, hb₁, hf₁⟩).frame
      (fun i => he₂.arrs_eq_of_not_mem_writtenArrs (integral_field_not_written i))
      (he₂.arrs_eq_of_not_mem_writtenArrs (integral_saved_not_written 1000 (Or.inl rfl)))
      (he₂.arrs_eq_of_not_mem_writtenArrs (integral_saved_not_written 1001 (Or.inr rfl)))
  have hk₂ : s₂.regs 52 = x.pathCount :=
    (he₂.regs_eq_of_not_mem_writtenRegs (by decide)).trans hk₁
  by_cases hone : flag = 1
  · have hgrid := hiff.mp hone
    have hflowWords : ∀ v ∈ encDisjointPathsIn x.toWindingInput.drawing.flowInput, v < 2 ^ w :=
      fun v hv => hwords v (gm06Alg511_mem_encoded_row (by simp [gm06Alg511BinarySearchRows]) hv)
    obtain ⟨s₃, u₃, he₃, ht₃, hk₃, hin₃⟩ := gm06Alg511CopyRowProg_exec (w := w) 1001 0 (by decide)
      (encDisjointPathsIn x.toWindingInput.drawing.flowInput) s₂ (by omega) (by omega) hflowWords hkeepTables.2.2
    obtain ⟨s₄, u₄, he₄, ht₄, hbool₄, hiff₄, _, hpath₄⟩ := hflow x.toWindingInput.drawing.flowInput s₃ w (by omega) hwflow hin₃
    have hkeepTables₃ : gm06Alg511BinaryLoadedTables x s₃ := hkeepTables.frame
      (fun i => hk₃.2 _ (by
        have hnonzero : ∀ i : Fin 9, gm06Alg511BinaryFieldTarget i.val ≠ 0 := by decide
        exact fun he => hnonzero i (List.mem_singleton.mp he)))
      (hk₃.2 1000 (by decide)) (hk₃.2 1001 (by decide))
    have hkeepTables₄ : gm06Alg511BinaryLoadedTables x s₄ := hkeepTables₃.frame
      (fun i => he₄.arrs_eq_of_not_mem_writtenArrs (flow_field_not_written i))
      (he₄.arrs_eq_of_not_mem_writtenArrs (flow_saved_not_written 1000 (Or.inl rfl)))
      (he₄.arrs_eq_of_not_mem_writtenArrs (flow_saved_not_written 1001 (Or.inr rfl)))
    have hkrow₄ : s₄.arrs 1501 = [x.pathCount] := hkeepTables₄.1 ⟨5, by decide⟩
    let t := s₄.setReg 52 x.pathCount
    have he₅ : Exec w (.assign 52 (.read 1501 (.const 0))) s₄ t 3 :=
      .assign ((Crossing.eval_read (a := 1501) (Crossing.eval_const (Nat.two_pow_pos w))
        (by rw [hkrow₄]; simp) (by simpa only [hkrow₄, List.getElem_cons_zero] using hk)).trans (by simp [hkrow₄]))
    have htflow := ht₄.trans (Nat.add_le_add_right (Nat.mul_le_mul_left C (gm06Alg511FlowSize_le x.toWindingInput.drawing)) 3)
    change u₄ ≤ C * (x.pathCount + x.vertexCount + 1) ^ 3 + 3 at htflow
    refine ⟨t, u₁ + (u₂ + (1 + (u₃ + (u₄ + 3)))), .seq he₁ (.seq he₂
      (.ite_true (Crossing.eval_reg hflag (hbit.trans_le (by omega))) (by omega) (.seq he₃ (.seq he₄ he₅)))),
      ?_, hkeepTables₄, by simp [t], ?_, ?_, ?_⟩
    · omega
    · have hbit₄ : s₄.regs 0 < 2 := by rcases hbool₄ with h | h <;> rw [h] <;> decide
      simpa only [t, State.setReg_regs_ne _ _ (by decide : (0 : ℕ) ≠ 52)] using hbit₄
    · simpa only [t, State.setReg_regs_ne _ _ (by decide : (0 : ℕ) ≠ 52), hgrid, true_and, GM06Alg511Input.flowInput, GM06Alg511BinaryInput.toWindingInput] using hiff₄
    · simpa only [t, State.setReg_regs_ne _ _ (by decide : (0 : ℕ) ≠ 52), State.setReg_arrs, GM06Alg511Input.flowInput, GM06Alg511BinaryInput.toWindingInput] using hpath₄
  · have hzero : flag = 0 := by omega
    have hnot : ¬ ∃ m : ℤ, (x.pathCount : ℝ) * ((x.numerator.value : ℝ) / x.denominator.value) = m :=
      fun h => hone (hiff.mpr h)
    refine ⟨s₂, u₁ + (u₂ + 2), .seq he₁ (.seq he₂ (.ite_false (Crossing.eval_reg (hflag.trans hzero) (Nat.two_pow_pos w)) (.skip s₂))),
      ?_, hkeepTables, hk₂, by simpa only [hflag] using hbit, ?_, ?_⟩
    · omega
    · simp only [hflag, hzero, Nat.zero_ne_one, hnot, false_and]
    · intro h
      have hh := hflag.trans hzero
      omega

end GraphMinor.Compute
