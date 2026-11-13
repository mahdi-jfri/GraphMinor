module

public import GraphMinor.Compute.GM06Alg511ReadChosenDarts
public import GraphMinor.Compute.GM06Alg511CopyRow
public import GraphMinor.Compute.GM06Alg511TurnBounds
import Mathlib.Tactic

/-!
# Summing turns along the stored initial linkage

For VI (5.11), page 134, read the path's darts from the full linkage
choice array, copy their exact list to the turn accumulator's input,
and sum the supplied signed words. The result uses the stored edge
labels of the full linkage even when parallel edges are present.
-/

@[expose] public section
namespace GraphMinor.Compute
open TwoPaths

/-- Read the stored path darts and sum their signed turns. -/
def gm06Alg511ChosenTurnProg : Cmd :=
  .seq gm06Alg511ReadChosenDartsProg
    (.seq (gm06Alg511CopyRowProg 13 12) gm06Alg511TurnSumProg)

/-- The signed turn sum of the stored path is computed in linear
time, preserving every array except the two path scratch arrays. -/
theorem gm06Alg511ChosenTurnProg_exec {w : ℕ} (x : GM06Alg511Input)
    (turns : List ℤ) (choices : List ℕ) (vs : List (Fin x.vertexCount)) (s : State)
    (hw : 2 < 2 ^ w) (hn : x.vertexCount < 2 ^ w)
    (hturnlen : 2 * turns.length < 2 ^ w)
    (hchoiceLen : choices.length = x.vertexCount)
    (hchoiceWords : ∀ d ∈ choices, d < 2 ^ w)
    (hdarts : ∀ d ∈ gm06Alg511ChosenDarts x choices vs, d < 2 * turns.length)
    (hproduct : x.vertexCount * (gm06Alg511TurnWords turns).sum < 2 ^ w)
    (hchoices : s.arrs 1300 = choices) (hwords : s.arrs 11 = gm06Alg511TurnWords turns)
    (hbuf : IsBufPrefix s 12 42 x.vertexCount (vs.map Fin.val)) :
    ∃ s' t, Exec w gm06Alg511ChosenTurnProg s s' t ∧
      t ≤ 25 + 56 * (vs.length - 1) ∧
      (∀ arr, arr ≠ 12 → arr ≠ 13 → s'.arrs arr = s.arrs arr) ∧
      s'.arrs 12 = gm06Alg511ChosenDarts x choices vs ∧
      (s'.regs 21 : ℤ) - (s'.regs 22 : ℤ) =
        ((gm06Alg511ChosenDarts x choices vs).map
          (gm06Alg511DartTurn (gm06Alg511TurnWords turns))).sum := by
  let darts := gm06Alg511ChosenDarts x choices vs
  have hlen : darts.length = vs.length - 1 := by
    simp only [darts, gm06Alg511ChosenDarts, List.length_map, List.length_take,
      min_eq_left (Nat.sub_le _ _)]
  have hdlen : darts.length ≤ x.vertexCount := by
    rw [hlen]
    exact (Nat.sub_le _ _).trans (by simpa only [List.length_map] using hbuf.2.2.1)
  obtain ⟨s₁, t₁, he₁, ht₁, hk₁, harr₁⟩ := gm06Alg511ReadChosenDartsProg_exec
    x choices vs s (by omega) hn hchoiceLen hchoiceWords hchoices hbuf
  obtain ⟨s₂, t₂, he₂, ht₂, hk₂, harr₂⟩ := gm06Alg511CopyRowProg_exec
    13 12 (by decide) darts s₁ (by omega) (hdlen.trans_lt hn)
    (fun d hd => (hdarts d hd).trans hturnlen) harr₁
  obtain ⟨hpos, hneg⟩ := gm06Alg511TurnSum_word_bounds turns darts hdlen hdarts hproduct
  obtain ⟨s₃, t₃, he₃, ht₃, harr₃, hsum⟩ := gm06Alg511TurnSum_exec_signed
    turns darts s₂ hw hturnlen (hdlen.trans_lt hn)
    ((hk₂.2 11 (by decide)).trans ((hk₁.2 11 (by decide)).trans hwords))
    harr₂ hdarts hpos hneg
  refine ⟨s₃, t₁ + (t₂ + t₃), .seq he₁ (.seq he₂ he₃), ?_, ?_, ?_, hsum⟩
  · rw [hlen] at ht₂ ht₃
    omega
  · intro arr hne₁ hne₂
    rw [harr₃, hk₂.2 arr (by simpa using hne₁), hk₁.2 arr (by simpa using hne₂)]
  · rw [harr₃]
    exact harr₂

end GraphMinor.Compute
