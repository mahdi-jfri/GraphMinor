module

public import GraphMinor.Compute.GM06UnpackSuccessor
public import GraphMinor.Compute.GM06InitEdgeActivity
public import GraphMinor.Compute.GM06SuccessorGraphRep
import GraphMinor.Compute.GM06SuccessorDegreeScan
import GraphMinor.Compute.CrossingOpsBasic

/-!
# Loading the instance and creating cylinder workspace

Copy the six supplied fields to their work arrays and compute one
activity bit per original edge from the endpoint array length. The
representation bijection identifies this count with the graph's actual
edge count. All supplied fields remain available after initialization.
-/

@[expose] public section
namespace GraphMinor.Compute
open TwoPaths
universe u v

/-- Load the finite cylinder instance and compute its initial activity array. -/
def gm06InitSuccessorWorkspaceProg : Cmd :=
  .seq gm06UnpackSuccessorProg (gm06InitEdgeActivityProg 3 12)

/-- Workspace initialization preserves the supplied fields and activates every actual edge. -/
theorem gm06InitSuccessorWorkspaceProg_exec {w : ℕ} (x : GM06SuccessorInput)
    {α : Type u} {β : Type v} (G : Graph α β) (rep : GM06SuccessorGraphRep x G)
    (s : State) (hw : 2 < 2 ^ w) (ha : s.arrs 0 = gm06EncodeSuccessorInput x)
    (hn : (gm06EncodeSuccessorInput x).length < 2 ^ w)
    (hwords : ∀ a ∈ gm06EncodeSuccessorInput x, a < 2 ^ w) :
    ∃ s' t, Exec w gm06InitSuccessorWorkspaceProg s s' t ∧
      t ≤ 11 + 22 * (gm06EncodeSuccessorInput x).length + 13 * G.edgeSet.ncard ∧
      (∀ j : Fin 6, s'.arrs (gm06SuccessorFieldArray j.val) =
        (gm06SuccessorRows x)[j.val]'(by simp [gm06SuccessorRows])) ∧
      s'.arrs 12 = List.replicate G.edgeSet.ncard 1 ∧ s'.arrs 0 = s.arrs 0 := by
  obtain ⟨s₁, t₁, he₁, ht₁, hf, _, hs⟩ :=
    gm06UnpackSuccessorProg_exec x s (by omega) ha hn hwords
  have hends : s₁.arrs 3 = x.endpoints := by
    simpa only [gm06SuccessorRows, List.getElem_cons_succ, List.getElem_cons_zero,
      Nat.reduceAdd, gm06SuccessorFieldArray, Nat.reduceLT, ite_true, ite_false] using hf ⟨1, by decide⟩
  have hbound := gm06Row_word_bounds (show x.endpoints ∈ gm06SuccessorRows x by
    simp [gm06SuccessorRows]) hwords
  obtain ⟨s₂, t₂, he₂, ht₂, hk, hm⟩ := gm06InitEdgeActivityProg_exec 3 12 x.endpoints
    s₁ hw rep.endpoints_length hbound.1 hends
  refine ⟨s₂, t₁ + t₂, .seq he₁ he₂, by omega, ?_, hm, ?_⟩
  · intro j
    have hj : gm06SuccessorFieldArray j.val ≠ 12 := by
      have hh := j.isLt; unfold gm06SuccessorFieldArray; split <;> omega
    exact (hk.2 (gm06SuccessorFieldArray j.val) (by simpa only [List.mem_singleton] using hj)).trans (hf j)
  · exact (hk.2 0 (by decide)).trans hs

/-- Read the supplied vertex count and activate all original vertex
labels in the persistent live mask. -/
def gm06InitSuccessorLiveProg : Cmd :=
  .seq (.assign 100 (.read 2 (.const 0)))
    (.seq (.alloc 14 (.reg 100)) (fillArr 14 (.len 14) (.const 1) 57))

/-- The live-mask initialization reads only the ordinary count field.
Its result is independent of the old mask and register contents. -/
theorem gm06InitSuccessorLiveProg_exec {w n : ℕ} (s : State)
    (hw : 1 < 2 ^ w) (hn : n < 2 ^ w) (h2 : s.arrs 2 = [n]) :
    ∃ sf t, Exec w gm06InitSuccessorLiveProg s sf t ∧ t ≤ 9 + 13 * n ∧
      Keeps [100, 57] [14] s sf ∧ sf.regs 100 = n ∧ sf.arrs 14 = List.replicate n 1 := by
  let s₁ := s.setReg 100 n
  let s₂ := s₁.setArr 14 (List.replicate n 0)
  have he₁ : Exec w (.assign 100 (.read 2 (.const 0))) s s₁ 3 := by
    apply Exec.assign
    simp [Expr.eval, checkWord, h2, hn]
  have he₂ : Exec w (.alloc 14 (.reg 100)) s₁ s₂ (1 + n) :=
    .alloc (GraphMinor.Compute.Crossing.eval_reg (by simp [s₁]) hn)
  obtain ⟨sf, tf, hef, htf, h14, _⟩ := Triple.fillArr_const 14 1 57 (List.replicate n 0)
    hw (by simpa only [List.length_replicate] using hn) hw s₂ (by simp [s₂])
  have he : Exec w gm06InitSuccessorLiveProg s sf (3 + ((1 + n) + tf)) :=
    .seq he₁ (.seq he₂ hef)
  refine ⟨sf, _, he, by simp only [List.length_replicate] at htf; omega, ⟨?_, ?_⟩, ?_, ?_⟩
  · intro r hr
    apply he.regs_eq_of_not_mem_writtenRegs
    simpa [gm06InitSuccessorLiveProg, fillArr, forUp, Cmd.writtenRegs] using hr
  · intro a ha
    apply he.arrs_eq_of_not_mem_writtenArrs
    simpa [gm06InitSuccessorLiveProg, fillArr, forUp, Cmd.writtenArrs] using ha
  · have h100 : sf.regs 100 = s₂.regs 100 := hef.regs_eq_of_not_mem_writtenRegs (by
      simp [fillArr, forUp, Cmd.writtenRegs])
    exact h100.trans (by simp [s₂, s₁])
  · simpa only [List.length_replicate] using h14

/-- Allocate the numeric contraction history and initialize the
reduction-following bit. The capacity is two words per possible
size-decreasing step of the original graph. -/
def gm06InitSuccessorHistoryProg : Cmd :=
  .seq (.alloc 9 (.op .mul (.const 2) (.op .add (.reg 100) (.len 12))))
    (.seq (.assign 309 (.const 0)) (.assign 329 (.const 1)))

/-- History allocation uses only the computed edge-mask length and
the original vertex count, with an empty history and bit one. -/
theorem gm06InitSuccessorHistoryProg_exec {w n m : ℕ} (s : State)
    (hw : 2 < 2 ^ w) (hsize : 2 * (n + m) < 2 ^ w)
    (h100 : s.regs 100 = n) (h12 : (s.arrs 12).length = m) :
    ∃ sf, Exec w gm06InitSuccessorHistoryProg s sf (9 + 2 * (n + m)) ∧
      Keeps [309, 329] [9] s sf ∧ sf.arrs 9 = List.replicate (2 * (n + m)) 0 ∧
      sf.regs 309 = 0 ∧ sf.regs 329 = 1 := by
  let s₁ := s.setArr 9 (List.replicate (2 * (n + m)) 0)
  let s₂ := s₁.setReg 309 0
  let s₃ := s₂.setReg 329 1
  have hlen : (Expr.len 12).eval w s = some m := by
    simp [Expr.eval, checkWord, h12, show m < 2 ^ w by omega]
  have hsum : (Expr.op .add (.reg 100) (.len 12)).eval w s = some (n + m) :=
    GraphMinor.Compute.Crossing.eval_add
      (GraphMinor.Compute.Crossing.eval_reg h100 (by omega)) hlen (by omega)
  have he₁ : Exec w (.alloc 9 (.op .mul (.const 2) (.op .add (.reg 100) (.len 12))))
      s s₁ (5 + 2 * (n + m)) :=
    .alloc (GraphMinor.Compute.Crossing.eval_mul
      (GraphMinor.Compute.Crossing.eval_const hw) hsum hsize)
  have he₂ : Exec w (.assign 309 (.const 0)) s₁ s₂ 2 :=
    .assign (GraphMinor.Compute.Crossing.eval_const (Nat.two_pow_pos w))
  have he₃ : Exec w (.assign 329 (.const 1)) s₂ s₃ 2 :=
    .assign (GraphMinor.Compute.Crossing.eval_const (by omega))
  have he : Exec w gm06InitSuccessorHistoryProg s s₃ (9 + 2 * (n + m)) := by
    have hcost : (5 + 2 * (n + m)) + (2 + 2) = 9 + 2 * (n + m) := by omega
    rw [← hcost]
    exact .seq he₁ (.seq he₂ he₃)
  refine ⟨s₃, he, ⟨?_, ?_⟩, by simp [s₃, s₂, s₁], by simp [s₃, s₂], by simp [s₃]⟩
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp [s₃, s₂, s₁, hr.1, hr.2]
  · intro a ha
    simp only [List.mem_singleton] at ha
    simp [s₃, s₂, s₁, ha]

/-- Initialize the current graph, live labels, inverse history and
bit from the six ordinary input fields. -/
def gm06InitializeSuccessorProg : Cmd :=
  .seq gm06InitSuccessorWorkspaceProg
    (.seq gm06InitSuccessorLiveProg gm06InitSuccessorHistoryProg)

/-- Initialization of the reduction loop of VI (5.7), page 133.
All masks and the history are computed from the ordinary input.
The supplied cuff, rotation and given-path fields remain exact. -/
theorem gm06InitializeSuccessorProg_exec {w : ℕ} (x : GM06SuccessorInput)
    {α : Type u} {β : Type v} (G : Graph α β) (rep : GM06SuccessorGraphRep x G)
    (s : State) (hw : 2 < 2 ^ w) (ha : s.arrs 0 = gm06EncodeSuccessorInput x)
    (hn : (gm06EncodeSuccessorInput x).length < 2 ^ w)
    (hwords : ∀ a ∈ gm06EncodeSuccessorInput x, a < 2 ^ w)
    (hsize : 2 * (x.vertexCount + G.edgeSet.ncard) < 2 ^ w) :
    ∃ sf t, Exec w gm06InitializeSuccessorProg s sf t ∧
      t ≤ 30 + 22 * (gm06EncodeSuccessorInput x).length +
        15 * (x.vertexCount + G.edgeSet.ncard) ∧
      (∀ j : Fin 6, sf.arrs (gm06SuccessorFieldArray j.val) =
        (gm06SuccessorRows x)[j.val]'(by simp [gm06SuccessorRows])) ∧
      sf.arrs 12 = List.replicate G.edgeSet.ncard 1 ∧
      sf.arrs 14 = List.replicate x.vertexCount 1 ∧
      sf.arrs 9 = List.replicate (2 * (x.vertexCount + G.edgeSet.ncard)) 0 ∧
      sf.regs 100 = x.vertexCount ∧ sf.regs 309 = 0 ∧ sf.regs 329 = 1 ∧
      sf.arrs 0 = s.arrs 0 := by
  obtain ⟨s₁, t₁, he₁, ht₁, hfields, hactive, hinput⟩ :=
    gm06InitSuccessorWorkspaceProg_exec x G rep s hw ha hn hwords
  have h2 : s₁.arrs 2 = [x.vertexCount] := by
    simpa only [gm06SuccessorFieldArray, Nat.reduceLT, ite_true, Nat.add_zero,
      gm06SuccessorRows, List.getElem_cons_zero] using hfields ⟨0, by decide⟩
  obtain ⟨s₂, t₂, he₂, ht₂, hk₂, h100, hlive⟩ := gm06InitSuccessorLiveProg_exec (w := w) s₁
    (by omega) (by omega) h2
  obtain ⟨sf, he₃, hk₃, hhist, hcount, hbit⟩ := gm06InitSuccessorHistoryProg_exec s₂ hw hsize
    h100 (by rw [hk₂.2 12 (by decide), hactive, List.length_replicate])
  refine ⟨sf, t₁ + (t₂ + (9 + 2 * (x.vertexCount + G.edgeSet.ncard))),
    .seq he₁ (.seq he₂ he₃), by omega, ?_, ?_, (hk₃.2 14 (by decide)).trans hlive,
    hhist, (hk₃.1 100 (by decide)).trans h100, hcount, hbit, ?_⟩
  · intro j
    have haddr14 : gm06SuccessorFieldArray j.val ≠ 14 := by
      have hj := j.isLt
      unfold gm06SuccessorFieldArray
      split <;> omega
    have haddr9 : gm06SuccessorFieldArray j.val ≠ 9 := by
      have hj := j.isLt
      unfold gm06SuccessorFieldArray
      split <;> omega
    exact (hk₃.2 _ (by simpa only [List.mem_singleton] using haddr9)).trans
      ((hk₂.2 _ (by simpa only [List.mem_singleton] using haddr14)).trans (hfields j))
  · exact (hk₃.2 12 (by decide)).trans ((hk₂.2 12 (by decide)).trans hactive)
  · exact (hk₃.2 0 (by decide)).trans ((hk₂.2 0 (by decide)).trans hinput)

end GraphMinor.Compute
