module

public import GraphMinor.Compute.GM06Alg34GapTaskData
public import GraphMinor.Compute.GM06Alg34GapComponentBuild
public import GraphMinor.Compute.GM06Alg34ComponentPrepare
import Mathlib.Tactic.Ring

/-!
# Materializing a decoded component work record

Prepare the parent graph's component search tables, install the decoded
source label, and build the exact augmented component input. The fixed
scratch write sets preserve the pending queue, saved parent records,
and all high driver counters throughout this cubic-time operation.
-/

@[expose] public section
namespace GraphMinor.Compute

/-- Materialize the parent component whose decoded source is in 7300. -/
def gm06GapTaskMaterializeBodyProg : Cmd :=
  .seq gm06ComponentPrepareProg
    (.seq (.assign 114 (.reg 7300)) gm06GapComponentBuildProg)

private theorem body_arrays : gm06GapTaskMaterializeBodyProg.writtenArrs ⊆
    Finset.range 38 ∪ {47, 48} := by decide

set_option maxRecDepth 4096 in
private theorem body_registers : gm06GapTaskMaterializeBodyProg.writtenRegs ⊆
    Finset.range 300 ∪ {6400, 6401, 6402, 6403, 6404, 6500, 6501, 6502} := by decide

/-- Component materialization preserves pending records and all other external arrays. -/
theorem gm06GapTaskMaterializeBody_array_frame {w t : ℕ} {s s' : State}
    (he : Exec w gm06GapTaskMaterializeBodyProg s s' t) {A : ℕ}
    (hA : 38 ≤ A) (h47 : A ≠ 47) (h48 : A ≠ 48) : s'.arrs A = s.arrs A := by
  apply he.arrs_eq_of_not_mem_writtenArrs
  intro hm
  rcases Finset.mem_union.mp (body_arrays hm) with hh | hh
  · have hlt := Finset.mem_range.mp hh
    omega
  · simp only [Finset.mem_insert, Finset.mem_singleton] at hh
    exact hh.elim h47 h48

/-- Component materialization preserves every high queue/driver counter. -/
theorem gm06GapTaskMaterializeBody_register_frame {w t : ℕ} {s s' : State}
    (he : Exec w gm06GapTaskMaterializeBodyProg s s' t) {q : ℕ} (hq : 6503 ≤ q) :
    s'.regs q = s.regs q := by
  apply he.regs_eq_of_not_mem_writtenRegs
  intro hm
  rcases Finset.mem_union.mp (body_registers hm) with hh | hh
  · have hlt := Finset.mem_range.mp hh
    omega
  · simp only [Finset.mem_insert, Finset.mem_singleton] at hh
    rcases hh with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> omega

private theorem body_budget (n : ℕ) :
    250 * (n + 1) ^ 2 + 2 + 1300 * (n + 2) ^ 3 ≤ 1600 * (n + 2) ^ 3 := by
  ring_nf
  omega

/-- A decoded parent record materializes its exact finite target arrays
in cubic time with logarithmic words, preserving the pending queue. -/
theorem gm06GapTaskMaterializeBodyProg_exec (T : GM06GapComponentTask)
    (L : List (Fin T.drawing.n)) (hL : T.drawing.cuffs = [L]) (hlen : T.gaps.length = L.length)
    {c : ℕ} (hc : 3 ≤ c) {s : State} (hinput : s.arrs 0 = T.drawing.words)
    (hgap : s.arrs 47 = T.gaps.map Fin.val) (hroot : s.regs 7300 = T.root.val) :
    ∃ s' t, Exec (wordSize c T.drawing.size) gm06GapTaskMaterializeBodyProg s s' t ∧
      t ≤ 1600 * (T.drawing.size + 2) ^ 3 ∧ s'.arrs 0 = T.target.drawing.words ∧
      s'.arrs 47 = T.target.discGapWords ∧
      (∀ A : ℕ, 38 ≤ A → A ≠ 47 → A ≠ 48 → s'.arrs A = s.arrs A) ∧
      (∀ q : ℕ, 6503 ≤ q → s'.regs q = s.regs q) := by
  obtain ⟨s₁, t₁, he₁, ht₁, hin₁, hadj₁, hlen₁, hn₁, _, _, _⟩ :=
    gm06ComponentPrepareProg_exec T.drawing hL (c := c) (by omega) hinput
  have hgap₁ : s₁.arrs 47 = T.gaps.map Fin.val :=
    (he₁.arrs_eq_of_not_mem_writtenArrs (by decide : 47 ∉ gm06ComponentPrepareProg.writtenArrs)).trans hgap
  have hroot₁ : s₁.regs 7300 = T.root.val :=
    (he₁.regs_eq_of_not_mem_writtenRegs (by decide : 7300 ∉ gm06ComponentPrepareProg.writtenRegs)).trans hroot
  have hword : T.root.val < 2 ^ wordSize c T.drawing.size :=
    T.root.isLt.trans (T.drawing.counts_le_size.1.trans_lt
      (lt_two_pow_wordSize_of_le (by omega) (Nat.le_succ _)))
  let s₂ := s₁.setReg 114 T.root.val
  have he₂ : Exec (wordSize c T.drawing.size) (.assign 114 (.reg 7300)) s₁ s₂ 2 :=
    .assign (by simp [Expr.eval, checkWord, hroot₁, hword])
  have hadj₂ : IsAdjList T.drawing.vertexGraph 30 31 32 (adjListOf T.drawing.vertexGraph) s₂ := hadj₁
  obtain ⟨s₃, t₃, he₃, ht₃, hbase, hnewgap, _⟩ :=
    gm06GapComponentBuildProg_exec T.drawing L T.gaps T.root hL hlen hc (s := s₂) hin₁ hgap₁
      (by simp [s₂]) (by simpa [s₂] using hn₁) hadj₂ hlen₁
  have he : Exec (wordSize c T.drawing.size) gm06GapTaskMaterializeBodyProg s s₃ (t₁ + (2 + t₃)) :=
    .seq he₁ (.seq he₂ he₃)
  refine ⟨s₃, _, he, (show t₁ + (2 + t₃) ≤
      250 * (T.drawing.size + 1) ^ 2 + 2 + 1300 * (T.drawing.size + 2) ^ 3 by omega).trans
        (body_budget T.drawing.size), hbase, ?_, ?_, ?_⟩
  · exact hnewgap.trans (T.input.inducedGapInput_discGapWords
      (T.drawing.componentVertices T.root) L T.gaps hL rfl).symm
  · exact fun _ hA h47 h48 => gm06GapTaskMaterializeBody_array_frame he hA h47 h48
  · exact fun _ hq => gm06GapTaskMaterializeBody_register_frame he hq

end GraphMinor.Compute
