module

public import GraphMinor.Compute.GM06CutRowIndices
public import GraphMinor.Compute.GM06WordRows
public import Mathlib.Data.List.Rotate
public import GraphMinor.Compute.GM06LoopErasure

/-!
# Rotating the selected face to finish with its inner cuff dart

Section 15 of our proof of VI (5.7) (outlined in `GraphMinor/GM06/Alg57Algorithm.lean`) rotates the
selected face row so its final dart is the reverse inner cuff dart,
then traces only the preceding darts. The pure function copies the
suffix after that dart followed by the prefix before it. The RAM
program finds the cuff's actual position and performs those copies.
-/

@[expose] public section
namespace GraphMinor.Compute
open TwoPaths

/-- The rotated selected face with its final reverse cuff dart omitted. -/
def gm06TerminalFaceWalk (face : List ℕ) (cuff : ℕ) : List ℕ :=
  face.drop (face.idxOf cuff + 1) ++ face.take (face.idxOf cuff)

/-- Restoring the omitted dart gives exactly a rotation of the face. -/
theorem gm06TerminalFaceWalk_rotate (face : List ℕ) (cuff : ℕ) (hc : cuff ∈ face) :
    gm06TerminalFaceWalk face cuff ++ [cuff] = face.rotate (face.idxOf cuff + 1) := by
  have hi := List.idxOf_lt_length_of_mem hc
  rw [List.rotate_eq_drop_append_take (by omega)]
  rw [List.take_succ_eq_append_getElem hi, List.getElem_idxOf hi]
  exact List.append_assoc _ _ _

/-- Exactly the reverse cuff dart is omitted from the rotated row. -/
theorem gm06TerminalFaceWalk_length (face : List ℕ) (cuff : ℕ) (hc : cuff ∈ face) :
    (gm06TerminalFaceWalk face cuff).length + 1 = face.length := by
  have h := congrArg List.length (gm06TerminalFaceWalk_rotate face cuff hc)
  simpa only [List.length_append, List.length_singleton, List.length_rotate] using h

/-- A dart-simple face remains dart-simple after rotation and omission. -/
theorem gm06TerminalFaceWalk_nodup (face : List ℕ) (cuff : ℕ) (hc : cuff ∈ face) (hnd : face.Nodup) :
    (gm06TerminalFaceWalk face cuff).Nodup := by
  have hr : (gm06TerminalFaceWalk face cuff ++ [cuff]).Nodup := by
    rw [gm06TerminalFaceWalk_rotate face cuff hc, List.nodup_rotate]
    exact hnd
  exact (List.nodup_append.mp hr).1

/-- Every traversed dart is from the original selected face. -/
theorem gm06TerminalFaceWalk_mem {face : List ℕ} {cuff d : ℕ} (hc : cuff ∈ face)
    (hd : d ∈ gm06TerminalFaceWalk face cuff) : d ∈ face := by
  apply (List.mem_rotate (n := face.idxOf cuff + 1)).mp
  rw [← gm06TerminalFaceWalk_rotate face cuff hc]
  exact List.mem_append_left _ hd

/-- The suffix of a directed walk starts at its corresponding visited
vertex. This is the suffix counterpart of `GM06DartWalk.take`. -/
theorem GM06DartWalk.drop {D V : Type*} {tail head : D → V} {s t : V}
    {ds : List D} (h : GM06DartWalk tail head s ds t) (j : ℕ) (hj : j ≤ ds.length) :
    GM06DartWalk tail head
      ((gm06WalkVertices head s ds)[j]'(by simpa only [gm06WalkVertices,
        List.length_cons, List.length_map] using Nat.lt_succ_of_le hj)) (ds.drop j) t := by
  induction h generalizing j with
  | nil =>
    have hz : j = 0 := by simp only [List.length_nil] at hj; omega
    subst j
    exact .nil _
  | @cons s t d ds ht hw ih =>
    cases j with
    | zero => exact .cons ht hw
    | succ j => exact ih j (by simp only [List.length_cons] at hj; omega)

/-- Rotating a closed directed face walk after its reverse cuff dart
and omitting that dart gives the stated walk between its two ends. -/
theorem gm06TerminalFaceWalk_walk {tail head : ℕ → ℕ} {v cuff : ℕ} {face : List ℕ}
    (hwalk : GM06DartWalk tail head v face v) (hc : cuff ∈ face) :
    GM06DartWalk tail head (head cuff) (gm06TerminalFaceWalk face cuff) (tail cuff) := by
  have hi := List.idxOf_lt_length_of_mem hc
  have hpre := hwalk.take (face.idxOf cuff) hi.le
  have hpost := hwalk.drop (face.idxOf cuff) hi.le
  have hsplit : face.drop (face.idxOf cuff) = cuff :: face.drop (face.idxOf cuff + 1) := by
    rw [List.drop_eq_getElem_cons hi, List.getElem_idxOf hi]
  rw [hsplit] at hpost
  cases hpost with
  | cons ht hw =>
    simpa only [gm06TerminalFaceWalk, ht] using hw.append hpre

/-- Find the cuff in face 600, copy its suffix/prefix and return walk 614. -/
def gm06TerminalFaceProg : Cmd :=
  .seq (gm06FindLabelProg 600 667 650 674)
    (.seq (gm13TabulateProg 650 (.op .sub (.len 600) (.op .add (.reg 674) (.const 1)))
      (.read 600 (.op .add (.reg 650) (.op .add (.reg 674) (.const 1)))) 604)
      (.seq (gm13TabulateProg 650 (.reg 674) (.read 600 (.reg 650)) 605)
        (gm06ConcatWordsProg 604 605 614)))

/-- Actual rotation and cuff omission compute the exact list function,
with linear cost and no supplied cuff-position table. -/
theorem gm06TerminalFaceProg_exec {w : ℕ} (face : List ℕ) (cuff : ℕ) (s : State)
    (hw : 1 < 2 ^ w) (hfit : face.length + 2 < 2 ^ w) (hnd : face.Nodup) (hc : cuff ∈ face)
    (hwords : ∀ d ∈ face, d < 2 ^ w) (h600 : s.arrs 600 = face) (h667 : s.regs 667 = cuff) :
    ∃ sf t, Exec w gm06TerminalFaceProg s sf t ∧ t ≤ 60 + 60 * face.length ∧
      Keeps [650, 651, 652, 655, 674] [604, 605, 614] s sf ∧
      sf.arrs 614 = gm06TerminalFaceWalk face cuff := by
  let p := face.idxOf cuff
  have hp : p < face.length := List.idxOf_lt_length_of_mem hc
  obtain ⟨s₁, t₁, he₁, ht₁, hk₁, hd₁⟩ := gm06FindLabelProg_exec_idxOf 600 667 650 674
    (by decide) (by decide) (by decide) face cuff s hw (by omega) hwords (hwords cuff hc) hnd h600 h667
  have hdropLen : (face.drop (p + 1)).length = face.length - (p + 1) := List.length_drop
  obtain ⟨s₂, t₂, he₂, ht₂, hk₂, hd₂⟩ := gm13TabulateProg_exec (w := w) 650
    (.op .sub (.len 600) (.op .add (.reg 674) (.const 1)))
    (.read 600 (.op .add (.reg 650) (.op .add (.reg 674) (.const 1)))) 604 (face.drop (p + 1)) s₁ hw
    (by rw [hdropLen]; omega)
    (fun st hk => by
      rw [hdropLen]
      exact GraphMinor.Compute.Crossing.eval_sub
        (GraphMinor.Compute.Crossing.eval_len ((hk.2 600 (by decide)).trans ((hk₁.2 600 (by simp)).trans h600)) (by omega))
        (GraphMinor.Compute.Crossing.eval_add
          (GraphMinor.Compute.Crossing.eval_reg (w := w) ((hk.1 674 (by decide)).trans hd₁) (by omega))
          (GraphMinor.Compute.Crossing.eval_const hw) (by omega)))
    (fun st i hi hk hr => by
      have hi' : i < face.length - (p + 1) := hdropLen ▸ hi
      have hindex : i + (p + 1) < face.length := by omega
      have ha := (hk.2 600 (by decide)).trans ((hk₁.2 600 (by simp)).trans h600)
      have he := GraphMinor.Compute.Crossing.eval_read (a := 600)
        (GraphMinor.Compute.Crossing.eval_add
          (GraphMinor.Compute.Crossing.eval_reg (w := w) hr (by omega))
          (GraphMinor.Compute.Crossing.eval_add
            (GraphMinor.Compute.Crossing.eval_reg (w := w) ((hk.1 674 (by decide)).trans hd₁) (by omega))
            (GraphMinor.Compute.Crossing.eval_const hw) (by omega)) (by omega))
        (by simpa only [ha] using hindex) (by simpa only [ha] using hwords _ (List.getElem_mem hindex))
      simpa only [ha, List.getElem_drop, Nat.add_comm] using he)
  have hk₁₂ : Keeps [650, 674] [604] s s₂ :=
    (hk₁.mono (fun _ h => h) (by simp)).trans hk₂ (by simp) (by simp)
  have htakeLen : (face.take p).length = p := List.length_take_of_le hp.le
  obtain ⟨s₃, t₃, he₃, ht₃, hk₃, hd₃⟩ := gm13TabulateProg_exec (w := w) 650 (.reg 674) (.read 600 (.reg 650))
    605 (face.take p) s₂ hw (by rw [htakeLen]; omega)
    (fun st hk => by
      rw [htakeLen]
      exact GraphMinor.Compute.Crossing.eval_reg (w := w) ((hk.1 674 (by decide)).trans ((hk₂.1 674 (by decide)).trans hd₁)) (by omega))
    (fun st i hi hk hr => by
      have hip : i < p := htakeLen ▸ hi
      have hi' : i < face.length := by omega
      have ha := (hk.2 600 (by decide)).trans ((hk₁₂.2 600 (by decide)).trans h600)
      have he := GraphMinor.Compute.Crossing.eval_read (a := 600)
        (GraphMinor.Compute.Crossing.eval_reg (w := w) hr (by omega))
        (by simpa only [ha] using hi') (by simpa only [ha] using hwords _ (List.getElem_mem hi'))
      simpa only [ha, List.getElem_take] using he)
  have hk₁₃ : Keeps [650, 674] [604, 605] s s₃ :=
    (hk₁₂.mono (fun _ h => h) (by simp)).trans hk₃ (by simp) (by simp)
  obtain ⟨sf, tf, hef, htf, hkf, hdf, _⟩ := gm06ConcatWordsProg_exec (by decide : 604 ≠ 614) (by decide : 605 ≠ 614)
    (face.drop (p + 1)) (face.take p) s₃ hw (by rw [hdropLen, htakeLen]; omega)
    (fun d hd => hwords d (List.mem_of_mem_drop hd)) (fun d hd => hwords d (List.mem_of_mem_take hd))
    ((hk₃.2 604 (by decide)).trans hd₂) hd₃
  refine ⟨sf, t₁ + (t₂ + (t₃ + tf)), .seq he₁ (.seq he₂ (.seq he₃ hef)), ?_,
    (hk₁₃.mono (by simp) (by simp)).trans hkf (by simp) (by simp), hdf⟩
  simp only [Expr.cost, hdropLen, htakeLen] at ht₂ ht₃ htf
  omega

end GraphMinor.Compute
