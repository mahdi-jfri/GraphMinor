module

public import GraphMinor.GM06.Alg34LoopWhileExec
public import GraphMinor.Compute.GM06Alg34QueueInit
import GraphMinor.Compute.CrossingOpsBasic

/-!
# Starting the loop from the supplied arrays

Queue initialization computes its capacity from the two supplied array
lengths and the vertex header. No task is initially pending. The
quadratic initial work bound establishes the queue budget, so the proved
loop execution starts from the actual input without a proof certificate.
-/

public section
namespace GraphMinor.Compute
open GM06
universe u

/-- Reserve the queue, set the running flag, and execute the proved loop
from an original cross-free represented finite input. -/
theorem gm06Driver_start (X : GM06GapInput)
    (hX : gm06LoopInstance.{u} X) {s : State}
    (hin : s.arrs 0 = X.drawing.words) (hgap : s.arrs 47 = X.discGapWords) :
    let Q := X.drawing.size + X.discGapWords.length
    ∃ b s' t, Exec (wordSize 256 Q)
      (.seq gm06DriverQueueInit (.seq (.assign 9000 (.const 1))
        (.while (.reg 9000) gm06DriverBody))) s s' t ∧
      t ≤ (Q + 2) ^ 16 + 43 + (gm06RoundBound Q + 1) * (3 * (Q + 2) ^ 2) ∧
      s'.regs 9001 = (if b then 1 else 0) ∧
      (IsFeasible X.drawing.graph X.drawing.divisionSet ↔ b = true) := by
  let Q := X.drawing.size + X.discGapWords.length
  let M := X.drawing.n + X.drawing.regions.length
  let E := X.drawing.ends.length
  have hB : gm06LoopBounds M E Q X := gm06LoopBounds_initial X Q (Nat.le_add_right _ _)
  have hc := X.drawing.cellCount_le_size.trans (show X.drawing.size ≤ Q from Nat.le_add_right _ _)
  have hW : X.drawing.workWeight (M + 1) ≤ 3 * (Q + 2) ^ 2 := by
    unfold GM06DrawingData.cellCount at hc
    exact gm06WorkWeight_le_quadratic Q (M + 1) X.drawing (by omega) (by omega)
      (by dsimp only [M]; omega)
  obtain ⟨s₁, t₁, he₁, ht₁, hbuf, hpos, hend, hcap, ha, _⟩ :=
    gm06DriverQueueInit_exec X.drawing hin (w := wordSize 256 Q)
      (by rw [hgap]; exact gm06Loop_capacity_lt Q)
  rw [hgap] at ht₁ hbuf hcap
  change t₁ ≤ (Q + 2) ^ 16 + 40 at ht₁
  let s₂ := s₁.setReg 9000 1
  have hw : 1 < 2 ^ wordSize 256 Q := lt_two_pow_wordSize_of_le (by decide) (by omega)
  have he₂ : Exec (wordSize 256 Q) (.assign 9000 (.const 1)) s₁ s₂ 2 :=
    .assign (Crossing.eval_const hw)
  have hi : gm06DriverInvariant.{u} M E Q
      (IsFeasible X.drawing.graph X.drawing.divisionSet) (.running X [] []) s₂ := by
    refine ⟨hX, hB, ?_, (ha 0 (by decide)).trans hin, (ha 47 (by decide)).trans hgap,
      ?_, ?_, ?_, rfl, ?_, ?_, ?_⟩
    · intro T hT; cases hT
    · simpa only [gm06TaskWords, List.flatMap_nil, List.nil_append, List.length_nil, Nat.sub_zero]
        using hbuf.of_arr_eq (show s₂.arrs 42 = s₁.arrs 42 from rfl)
    · simpa [s₂, State.setReg, List.length_nil] using hpos
    · simpa [s₂, State.setReg, gm06TaskWords, List.flatMap_nil,
        List.nil_append, List.length_nil] using hend
    · simpa [s₂, State.setReg] using hcap
    · simpa only [gm06TaskWords, List.flatMap_nil, List.nil_append, List.length_nil,
        gm06TaskWork, List.map_nil, List.sum_nil, Nat.add_zero, Nat.zero_add] using
        gm06Queue_capacity_bound Q _ hW
    · simp only [GM06DriverConfig.Feasible, List.not_mem_nil, false_implies, implies_true, and_true]
  obtain ⟨b, s', t₂, he₃, ht₂, hans, hf⟩ := gm06Driver_while hi
  have hw' := Nat.mul_le_mul_left (gm06RoundBound Q + 1) hW
  simp only [GM06DriverConfig.work, gm06TaskWork, List.map_nil, List.sum_nil, Nat.add_zero] at ht₂
  refine ⟨b, s', t₁ + (2 + t₂), .seq he₁ (.seq he₂ he₃), ?_, hans, hf⟩
  change t₁ + (2 + t₂) ≤ (Q + 2) ^ 16 + 43 + (gm06RoundBound Q + 1) * (3 * (Q + 2) ^ 2)
  omega

end GraphMinor.Compute
