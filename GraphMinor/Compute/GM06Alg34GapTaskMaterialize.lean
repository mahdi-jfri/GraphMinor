module

public import GraphMinor.Compute.GM06Alg34GapTaskRead
public import GraphMinor.Compute.GM06Alg34GapTaskMaterializeBody
import Mathlib.Tactic.Ring

/-!
# Reading and materializing a pending component task

Decode one queued parent/root record, then construct its exact augmented
component input. The read cursor advances by one record, while the
pending queue words and end counter stay available. This is the
component-task execution used by the algorithm's work queue.
-/

@[expose] public section
namespace GraphMinor.Compute

/-- Read one pending record and install its exact augmented component input. -/
def gm06GapTaskMaterializeProg : Cmd :=
  .seq gm06GapTaskReadProg gm06GapTaskMaterializeBodyProg

private theorem materialize_budget (n : ℕ) :
    50 * (n + 1) + 1600 * (n + 2) ^ 3 ≤ 1700 * (n + 2) ^ 3 := by
  ring_nf
  omega

/-- Decoding and materialization compute the queued task's exact target
arrays in cubic time, preserving the remaining queue and its end counter. -/
theorem gm06GapTaskMaterializeProg_exec {w off : ℕ} (T : GM06GapComponentTask) (tail : List ℕ)
    (L : List (Fin T.drawing.n)) (hL : T.drawing.cuffs = [L]) (hlen : T.gaps.length = L.length)
    (hw : wordSize 3 T.drawing.size ≤ w) (hsize : T.size < 2 ^ w)
    (hend : off + T.words.length < 2 ^ w) {s : State}
    (hstream : AtStream 42 off (T.words ++ tail) s) (hpos : s.regs 7000 = off) :
    ∃ s' t, Exec w gm06GapTaskMaterializeProg s s' t ∧ t ≤ 1700 * (T.size + 2) ^ 3 ∧
      s'.arrs 0 = T.target.drawing.words ∧ s'.arrs 47 = T.target.discGapWords ∧
      s'.regs 7000 = off + T.words.length ∧ AtStream 42 (off + T.words.length) tail s' ∧
      s'.regs 7001 = s.regs 7001 ∧
      (∀ A : ℕ, 38 ≤ A → A ≠ 47 → A ≠ 48 → s'.arrs A = s.arrs A) := by
  have hw1 : 1 < 2 ^ w :=
    (lt_two_pow_wordSize_of_le (c := 3) (n := T.drawing.size) (k := 1) (by decide) (by omega)).trans_le
      (Nat.pow_le_pow_right (by decide) hw)
  obtain ⟨s₁, t₁, he₁, ht₁, hin₁, hgap₁, hroot₁, hpos₁, hstream₁, harr₁, hreg₁⟩ :=
    gm06GapTaskReadProg_exec T tail hw1 hsize hend hstream hpos
  obtain ⟨s₂, t₂, he₂, ht₂, hin₂, hgap₂, harr₂, hreg₂⟩ :=
    gm06GapTaskMaterializeBodyProg_exec T L hL hlen (c := 3) (by decide) hin₁ hgap₁ hroot₁
  have hbodyTime : t₂ ≤ 1600 * (T.size + 2) ^ 3 :=
    ht₂.trans (Nat.mul_le_mul_left 1600
      (Nat.pow_le_pow_left (Nat.add_le_add_right T.drawing_size_le 2) 3))
  refine ⟨s₂, t₁ + t₂, .seq he₁ (he₂.mono_wordSize hw),
    (Nat.add_le_add ht₁ hbodyTime).trans (materialize_budget T.size), hin₂, hgap₂,
    (hreg₂ 7000 (by decide)).trans hpos₁,
    hstream₁.of_arr_eq (harr₂ 42 (by decide) (by decide) (by decide)),
    (hreg₂ 7001 (by decide)).trans (hreg₁ 7001 (by decide) (by decide) (by decide) (by decide)), ?_⟩
  intro A hA h47 h48
  exact (harr₂ A hA h47 h48).trans (harr₁ A (by omega) h47)

end GraphMinor.Compute
