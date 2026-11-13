module

public import GraphMinor.Compute.GM06UnpackRows
public import GraphMinor.Compute.GM06SuccessorInput
import GraphMinor.Compute.CrossingOpsBasic

/-!
# Loading the finite instance of VI (5.7)

The six supplied fields contain no region rows. Read the graph fields
into arrays 2, 3 and 4, then the cuff and linkage fields into arrays
6, 7 and 8. Array 5 remains available for scratch data. This keeps
the current reduction scans at their existing array addresses.
The cursor ends at the end of the input, in linear time.
-/

@[expose] public section
namespace GraphMinor.Compute

/-- The work-array address of a supplied field, skipping scratch array 5. -/
def gm06SuccessorFieldArray (j : ℕ) : ℕ := if j < 3 then 2 + j else 3 + j

/-- Load the graph fields and then the cuff and linkage fields. -/
def gm06UnpackSuccessorProg : Cmd :=
  .seq (.assign 8 (.const 1))
    (.seq (gm06UnpackRowsProg 0 2 3) (gm06UnpackRowsProg 0 6 3))

/-- The six input fields are loaded exactly at the existing scan
addresses, preserving the input and the unused scratch array. -/
theorem gm06UnpackSuccessorProg_exec {w : ℕ} (x : GM06SuccessorInput) (s : State)
    (hw : 1 < 2 ^ w) (ha : s.arrs 0 = gm06EncodeSuccessorInput x)
    (hn : (gm06EncodeSuccessorInput x).length < 2 ^ w)
    (hwords : ∀ v ∈ gm06EncodeSuccessorInput x, v < 2 ^ w) :
    ∃ s' t, Exec w gm06UnpackSuccessorProg s s' t ∧
      t ≤ 3 + 22 * (gm06EncodeSuccessorInput x).length ∧
      (∀ j : Fin 6, s'.arrs (gm06SuccessorFieldArray j.val) =
        (gm06SuccessorRows x)[j.val]'(by simpa [gm06SuccessorRows] using j.isLt)) ∧
      s'.regs 8 = (gm06EncodeSuccessorInput x).length ∧
      s'.arrs 0 = s.arrs 0 := by
  let front := [[x.vertexCount], x.endpoints, gm06EncodeRows x.rotations]
  let back := [x.innerCuff, x.outerCuff, gm06EncodeRows x.linkage]
  have hfLen : front.length = 3 := rfl
  have hbLen : back.length = 3 := rfl
  have hrows : gm06SuccessorRows x = front ++ back := rfl
  have hcode : gm06EncodeSuccessorInput x =
      [6] ++ gm06EncodeRowsPayload front ++ gm06EncodeRowsPayload back := by
    simp only [gm06EncodeSuccessorInput, gm06EncodeRows, hrows, List.length_append,
      hfLen, hbLen, Nat.reduceAdd, gm06EncodeRowsPayload, List.flatMap_append,
      List.cons_append, List.nil_append]
  let s₁ := s.setReg 8 1
  obtain ⟨s₂, t₂, he₂, ht₂, hf, hc₂, _, har₂⟩ := gm06UnpackRowsProg_exec 0 2 (by decide)
    front [6] (gm06EncodeRowsPayload back) s₁ hw
    (by simpa only [s₁, State.setReg_arrs, ha, hcode, List.append_assoc])
    (by simpa only [s₁, State.setReg_arrs, ha] using hn)
    (by simpa only [s₁, State.setReg_arrs, ha] using hwords) (by simp [s₁])
  have hsrc₂ : s₂.arrs 0 = gm06EncodeSuccessorInput x :=
    (har₂ 0 (Or.inl (by decide))).trans (by simpa only [s₁, State.setReg_arrs] using ha)
  obtain ⟨s₃, t₃, he₃, ht₃, hb, hc₃, _, har₃⟩ := gm06UnpackRowsProg_exec 0 6 (by decide)
    back ([6] ++ gm06EncodeRowsPayload front) [] s₂ hw
    (by rw [hsrc₂, hcode]; simp only [List.append_nil])
    (by rw [hsrc₂]; exact hn) (by rw [hsrc₂]; exact hwords)
    (by simpa only [List.length_append, List.length_singleton] using hc₂)
  have hlength : (gm06EncodeSuccessorInput x).length =
      1 + (gm06EncodeRowsPayload front).length + (gm06EncodeRowsPayload back).length := by
    rw [hcode]; simp only [List.length_append, List.length_singleton]
  refine ⟨s₃, 2 + (t₂ + t₃), .seq (.assign (GraphMinor.Compute.Crossing.eval_const hw))
    (.seq (by simpa only [hfLen] using he₂) (by simpa only [hbLen] using he₃)), ?_, ?_, ?_, ?_⟩
  · omega
  · intro j
    by_cases hj : j.val < 3
    · have hh := hf j.val (by simpa only [hfLen] using hj)
      have hframe : s₃.arrs (2 + j.val) = s₂.arrs (2 + j.val) := har₃ _ (Or.inl (by omega))
      simpa only [gm06SuccessorFieldArray, hj, ite_true, hrows, List.getElem_append_left
        (show j.val < front.length by simpa only [hfLen] using hj)] using hframe.trans hh
    · have hjb : j.val - 3 < back.length := by have hh := j.isLt; rw [hbLen]; omega
      have hh := hb (j.val - 3) hjb
      have haddr : 6 + (j.val - 3) = 3 + j.val := by omega
      simpa only [gm06SuccessorFieldArray, hj, ite_false, haddr, hrows,
        List.getElem_append_right (show front.length ≤ j.val by rw [hfLen]; omega), hfLen] using hh
  · simpa only [List.length_append, List.length_singleton, hlength] using hc₃
  · exact (har₃ 0 (Or.inl (by decide))).trans ((har₂ 0 (Or.inl (by decide))).trans rfl)

end GraphMinor.Compute
