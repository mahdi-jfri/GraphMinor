module

public import GraphMinor.Compute.GM06CutSplitRows
import GraphMinor.Compute.GM06FaceBuffers

/-!
# Initialized RAM construction of every copied rotation

Section 9 of our proof of VI (5.7) (outlined in `GraphMinor/GM06/Alg57Algorithm.lean`) returns two
permanent rotation slots per original vertex. This program allocates the output
buffer, writes its row count, initializes both source and output cursors,
and processes every input rotation. The output decoder reads only the
computed prefix. Its theorem identifies that prefix with exactly the
encoded pure copied rotations, including empty slots.
-/

@[expose] public section
namespace GraphMinor.Compute
open TwoPaths

/-- Initialize the copied-row buffer and all original-row loop counters. -/
def gm06CutInitRowsProg : Cmd :=
  .seq (.alloc 625 (.op .add (.const 1) (.op .mul (.const 2) (.len 600))))
    (.seq (.write 625 (.const 0) (.op .mul (.const 2) (.read 600 (.const 0))))
      (.seq (.assign 655 (.const 1))
        (.seq (.assign 661 (.const 1))
          (.seq (.assign 666 (.const 0)) (.assign 665 (.read 600 (.const 0)))))))

/-- Initialization creates a buffer with its computed doubled row count.
It preserves the rotation source and all computed linkage/cuff tables. -/
theorem gm06CutInitRowsProg_exec {w : ℕ} (rows : List (List ℕ)) (s : State)
    (hw : 2 < 2 ^ w) (hfit : 3 + 2 * (gm06EncodeRows rows).length < 2 ^ w)
    (ha : s.arrs 600 = gm06EncodeRows rows) :
    ∃ sf t, Exec w gm06CutInitRowsProg s sf t ∧
      t ≤ 21 + 2 * (gm06EncodeRows rows).length ∧ Keeps [655, 661, 666, 665] [625] s sf ∧
      GraphMinor.Compute.Crossing.IsBuf 625 655 [2 * rows.length] (2 * (gm06EncodeRows rows).length) sf ∧
      sf.regs 661 = 1 ∧ sf.regs 665 = rows.length ∧ sf.regs 666 = 0 := by
  let L := (gm06EncodeRows rows).length
  have hL : L = 1 + rows.length + rows.flatten.length := gm06FaceCode_length rows
  have hw1 : 1 < 2 ^ w := by omega
  have hlen : L < 2 ^ w := by omega
  have hcount : rows.length < 2 ^ w := by omega
  have readCount : ∀ st : State, st.arrs 600 = gm06EncodeRows rows →
      (Expr.read 600 (.const 0)).eval w st = some rows.length := by
    intro st hsrc
    have hi : 0 < (st.arrs 600).length := by simp [hsrc, gm06EncodeRows]
    have hget : (st.arrs 600)[0]'hi = rows.length := by simp [hsrc, gm06EncodeRows]
    have he := GraphMinor.Compute.Crossing.eval_read (a := 600)
      (GraphMinor.Compute.Crossing.eval_const (c := 0) (Nat.two_pow_pos w)) hi
      (by rw [hget]; exact hcount)
    simpa only [hget] using he
  let s₀ := s.setArr 625 (List.replicate (1 + 2 * L) 0)
  let s₁ := s₀.writeArr 625 0 (2 * rows.length)
  let s₂ := s₁.setReg 655 1
  let s₃ := s₂.setReg 661 1
  let s₄ := s₃.setReg 666 0
  let s₅ := s₄.setReg 665 rows.length
  have he₀ : Exec w (.alloc 625 (.op .add (.const 1) (.op .mul (.const 2) (.len 600))))
      s s₀ (5 + (1 + 2 * L)) :=
    .alloc (GraphMinor.Compute.Crossing.eval_add (GraphMinor.Compute.Crossing.eval_const hw1)
      (GraphMinor.Compute.Crossing.eval_mul (GraphMinor.Compute.Crossing.eval_const hw)
        (GraphMinor.Compute.Crossing.eval_len ha hlen) (by omega)) (by omega))
  have he₁ : Exec w (.write 625 (.const 0) (.op .mul (.const 2) (.read 600 (.const 0)))) s₀ s₁ 6 :=
    .write (GraphMinor.Compute.Crossing.eval_const (Nat.two_pow_pos w))
      (GraphMinor.Compute.Crossing.eval_mul (GraphMinor.Compute.Crossing.eval_const hw)
        (readCount s₀ (by simpa [s₀] using ha)) (by omega)) (by simp [s₀])
  have he₂ : Exec w (.assign 655 (.const 1)) s₁ s₂ 2 := .assign (GraphMinor.Compute.Crossing.eval_const hw1)
  have he₃ : Exec w (.assign 661 (.const 1)) s₂ s₃ 2 := .assign (GraphMinor.Compute.Crossing.eval_const hw1)
  have he₄ : Exec w (.assign 666 (.const 0)) s₃ s₄ 2 :=
    .assign (GraphMinor.Compute.Crossing.eval_const (Nat.two_pow_pos w))
  have he₅ : Exec w (.assign 665 (.read 600 (.const 0))) s₄ s₅ 3 :=
    .assign (readCount s₄ (by simp [s₄, s₃, s₂, s₁, s₀, State.writeArr, ha]))
  refine ⟨s₅, (5 + (1 + 2 * L)) + (6 + (2 + (2 + (2 + 3)))),
    .seq he₀ (.seq he₁ (.seq he₂ (.seq he₃ (.seq he₄ he₅)))), by omega, ?_, ⟨?_, by simp [s₅, s₄, s₃, s₂]⟩,
    by simp [s₅, s₄, s₃], by simp [s₅], by simp [s₅, s₄]⟩
  · exact ((((((Keeps.refl _ _ s).setArr (by simp) _).writeArr (by simp) _ _).setReg
      (by simp) _).setReg (by simp) _).setReg (by simp) _).setReg (by simp) _
  · have hrep : List.replicate (1 + 2 * L) 0 = 0 :: List.replicate (2 * L) 0 := by
      rw [Nat.add_comm 1, List.replicate_succ]
    simp [s₅, s₄, s₃, s₂, s₁, s₀, State.writeArr, hrep, L]

/-- Construct all copied rotations from the supplied rows and the
already computed cut-position tables. -/
def gm06CutRowsProg : Cmd := .seq gm06CutInitRowsProg gm06CutSplitRowsLoop

/-- Read exactly the prefix written by the cut-rotation construction. -/
def gm06CutRowsResult (s : State) : List ℕ := s.arrs 625 |>.take (s.regs 655)

/-- The complete initialized cut-row program returns exactly the pure
encoded copied rotations. Its source contains original rotations only. -/
theorem gm06CutRowsProg_exec {w n m : ℕ} (marks : GM06CutTables) (rows : List (List ℕ)) (s : State)
    (hw : 4 < 2 ^ w) (hn : n < 2 ^ w) (hm : 4 * m < 2 ^ w)
    (hrows : rows.length = n) (hnd : ∀ row ∈ rows, row.Nodup) (hkeys : ∀ d ∈ rows.flatten, d < 2 * m)
    (hlens : marks.incoming.length = n ∧ marks.outgoing.length = n ∧
      marks.cuffPositive.length = n ∧ marks.cuffNegative.length = n)
    (hwords : ∀ x ∈ marks.incoming ++ marks.outgoing ++ marks.cuffPositive ++ marks.cuffNegative, x < 2 ^ w)
    (h620 : s.arrs 620 = marks.incoming) (h621 : s.arrs 621 = marks.outgoing)
    (h623 : s.arrs 623 = marks.cuffPositive) (h624 : s.arrs 624 = marks.cuffNegative)
    (h600 : s.arrs 600 = gm06EncodeRows rows) (h647 : s.regs 647 = 2 * m)
    (hfit : 3 + 2 * (gm06EncodeRows rows).length < 2 ^ w)
    (hsrcWords : ∀ x ∈ gm06EncodeRows rows, x < 2 ^ w) :
    ∃ sf t, Exec w gm06CutRowsProg s sf t ∧
      t ≤ 22 + 2 * (gm06EncodeRows rows).length + rows.length * (6000 + 26 * m) + 6000 * rows.flatten.length ∧
      Keeps gm06CutSplitRowsRegs [611, 614, 615, 616, 625] s sf ∧
      gm06CutRowsResult sf = gm06EncodeRows (gm06SplitRotationRows marks rows) := by
  have hw2 : 2 < 2 ^ w := by omega
  have hL := gm06FaceCode_length rows
  obtain ⟨s₁, t₁, he₁, ht₁, hk₁, hb₁, hp₁, hc₁, hv₁⟩ := gm06CutInitRowsProg_exec rows s hw2 hfit h600
  obtain ⟨sf, tf, hef, htf, hkf, hbf, _, _, _⟩ := gm06CutSplitRowsLoop_exec
    (base := 0) marks rows [rows.length] [] [2 * rows.length] s₁ hw hn hm
    (by omega) (by omega) hnd hkeys hlens hwords
    ((hk₁.2 620 (by decide)).trans h620) ((hk₁.2 621 (by decide)).trans h621)
    ((hk₁.2 623 (by decide)).trans h623) ((hk₁.2 624 (by decide)).trans h624)
    (by simpa only [gm06EncodeRows, List.singleton_append, List.append_nil] using
      (hk₁.2 600 (by decide)).trans h600)
    (by rw [hk₁.2 600 (by decide), h600]; omega)
    (by rw [hk₁.2 600 (by decide), h600]; exact hsrcWords)
    ((hk₁.1 647 (by decide)).trans h647) hv₁ hp₁ hc₁ hb₁ (by omega)
    (by simp only [List.length_singleton]; omega)
  refine ⟨sf, t₁ + tf, .seq he₁ hef, by omega,
    (hk₁.mono (by simp [gm06CutSplitRowsRegs, gm06CutSplitVertexRegs]) (by simp)).trans hkf
      (fun _ h => h) (fun _ h => h), ?_⟩
  rw [gm06CutRowsResult, hbf.2, hbf.1, List.take_left]
  rw [gm06SplitRotationRowsFrom_zero]
  simp only [gm06EncodeRows, gm06SplitRotationRows_length, List.singleton_append]

end GraphMinor.Compute
