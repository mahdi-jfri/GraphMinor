module

public import GraphMinor.Compute.GM06Alg511BinaryReflectPaths
public import GraphMinor.Compute.GM06Alg511ReflectTable
import GraphMinor.Compute.CrossingOpsReplLists
import Mathlib.Tactic

/-!
# Reflecting the retained drawing fields read by the successor

Reverse and relabel the cuff-augmented rotation rows, reverse both
ordered cuffs and permute the retained ordinary linkage rows. The
original edge ends and vertex count stay unchanged. Each cuff uses
a separate temporary copy, and the path permutation protects its
original code. No region row or edge-turn magnitude is read.

The proved program is the finite drawing-data part of the orientation
reversal in VI (5.11), page 134. Its explicit time is polynomial in
rotation-code size, cuff sizes and path-table capacity. All binary
comparison values and the reflection/success bits are preserved.
-/

@[expose] public section
namespace GraphMinor.Compute
open TwoPaths

/-- Reflect one cuff in place using an ordinary temporary copy. -/
def gm06Alg511BinaryReflectCuffInPlaceProg (src tmp : ℕ) : Cmd :=
  .seq (gm06Alg511CopyRowProg src tmp) (gm06Alg511ReflectCuffProg tmp src)

/-- In-place cuff reflection retains exactly the reflected order,
with a linear word-count cost and no change to other arrays. -/
theorem gm06Alg511BinaryReflectCuffInPlaceProg_exec {w : ℕ} (src tmp : ℕ) (hne : src ≠ tmp)
    (xs : List ℕ) (s : State) (hw : 1 < 2 ^ w) (hsize : xs.length < 2 ^ w)
    (hwords : ∀ v ∈ xs, v < 2 ^ w) (ha : s.arrs src = xs) :
    ∃ t u, Exec w (gm06Alg511BinaryReflectCuffInPlaceProg src tmp) s t u ∧
      u ≤ 12 + 28 * xs.length ∧ Keeps [20] [src, tmp] s t ∧
      t.arrs src = gm06Alg511ReflectCuffWords xs := by
  obtain ⟨st, u₁, he₁, ht₁, hk₁, htmp⟩ := gm06Alg511CopyRowProg_exec (w := w) src tmp hne xs s hw hsize hwords ha
  obtain ⟨t, u₂, he₂, ht₂, hk₂, hout⟩ := gm06Alg511ReflectCuffProg_exec (w := w) tmp src hne.symm xs st hw hsize hwords htmp
  exact ⟨t, u₁ + u₂, .seq he₁ he₂, by omega,
    (hk₁.mono (by simp) (by simp)).trans hk₂ (by simp) (by simp), hout⟩

/-- Reflect only the retained cuff-augmented rotation table. -/
def gm06Alg511BinaryReflectRotationsProg : Cmd :=
  .seq (gm06Alg511CopyRowProg 1231 4)
    (.seq (.assign 60 (.op .div (.len 1230) (.const 2)))
      (.seq (gm06Alg511ReflectTableProg false) (gm06Alg511CopyRowProg 4 1231)))

/-- The rotation reflection computes its original-edge count from
the ordinary endpoint table, then applies the verified row program.
Both cuff families are present in its directed-label range. -/
theorem gm06Alg511BinaryReflectRotationsProg_exec {w : ℕ} (m k : ℕ)
    (ends : List ℕ) (rotations : List (List ℕ)) (s : State)
    (hw : 2 < 2 ^ w) (hendCount : ends.length = 2 * m)
    (haug : 2 * (m + k + k) < 2 ^ w) (hcode : (gm06EncodeRows rotations).length < 2 ^ w)
    (hwords : ∀ v ∈ gm06EncodeRows rotations, v < 2 ^ w)
    (hdarts : ∀ row ∈ rotations, ∀ d ∈ row, d < 2 * (m + k + k))
    (hE : s.arrs 1230 = ends) (hR : s.arrs 1231 = gm06EncodeRows rotations) (hK : s.regs 52 = k) :
    ∃ t u, Exec w gm06Alg511BinaryReflectRotationsProg s t u ∧
      u ≤ 32 + 24 * (gm06EncodeRows rotations).length + rotations.length * (607 + 600 * (gm06EncodeRows rotations).length) ∧
      Keeps [20, 60, 1400, 1401, 31, 7, 8, 9, 11, 23, 24, 323, 324, 313, 98]
        [4, 25, 26, 27, 28, 1231] s t ∧
      t.arrs 1231 = gm06EncodeRows (rotations.map (gm06Alg511ReflectedTableRow false m k)) := by
  have hendsFit : ends.length < 2 ^ w := by omega
  have hmFit : m < 2 ^ w := by omega
  obtain ⟨s₁, u₁, he₁, ht₁, hk₁, hrot₁⟩ := gm06Alg511CopyRowProg_exec (w := w) 1231 4 (by decide)
    (gm06EncodeRows rotations) s (by omega) hcode hwords hR
  let s₂ := s₁.setReg 60 m
  have he₂ : Exec w (.assign 60 (.op .div (.len 1230) (.const 2))) s₁ s₂ 4 := by
    have hdiv := Crossing.eval_div (Crossing.eval_len ((hk₁.2 1230 (by decide)).trans hE) hendsFit)
      (Crossing.eval_const hw) (by decide : (2 : ℕ) ≠ 0) (by omega : ends.length / 2 < 2 ^ w)
    have heq : ends.length / 2 = m := by omega
    exact .assign (by simpa only [heq] using hdiv)
  obtain ⟨s₃, u₃, he₃, ht₃, hk₃, hrot₃⟩ := gm06Alg511ReflectTableProg_exec (w := w) false m k rotations s₂ hw haug hcode
    hwords hdarts hrot₁ (by simp [s₂]) ((State.setReg_regs_ne _ _ (by decide)).trans ((hk₁.1 52 (by decide)).trans hK))
  have hnewLen := gm06Alg511ReflectedTable_code_length false m k rotations
  have hnewWords := gm06Alg511ReflectedTable_code_words false m k rotations haug hwords hdarts
  obtain ⟨t, u₄, he₄, ht₄, hk₄, hout⟩ := gm06Alg511CopyRowProg_exec (w := w) 4 1231 (by decide)
    (gm06EncodeRows (rotations.map (gm06Alg511ReflectedTableRow false m k))) s₃ (by omega) (by simpa only [hnewLen] using hcode) hnewWords hrot₃
  let R := [20, 60, 1400, 1401, 31, 7, 8, 9, 11, 23, 24, 323, 324, 313, 98]
  let A := [4, 25, 26, 27, 28, 1231]
  have hk₂ : Keeps R A s s₂ := (hk₁.mono (by simp [R]) (by simp [A])).setReg (by simp [R]) m
  have hkeep : Keeps R A s t := (hk₂.trans hk₃ (by simp [R]) (by simp [A])).trans hk₄ (by simp [R]) (by simp [A])
  refine ⟨t, u₁ + (4 + (u₃ + u₄)), .seq he₁ (.seq he₂ (.seq he₃ he₄)), ?_, hkeep, hout⟩
  rw [hnewLen] at ht₄
  omega

/-- Reverse both cuffs without reading any turn or region data. -/
def gm06Alg511BinaryReflectCuffsProg : Cmd :=
  .seq (gm06Alg511BinaryReflectCuffInPlaceProg 1210 1702) (gm06Alg511BinaryReflectCuffInPlaceProg 1211 1703)

/-- Both reflected cuff rows are computed in linear total cuff
length. All other drawing and binary arrays are preserved. -/
theorem gm06Alg511BinaryReflectCuffsProg_exec {w : ℕ} (inner outer : List ℕ) (s : State)
    (hw : 1 < 2 ^ w) (hi : inner.length < 2 ^ w) (ho : outer.length < 2 ^ w)
    (hwi : ∀ v ∈ inner, v < 2 ^ w) (hwo : ∀ v ∈ outer, v < 2 ^ w)
    (hI : s.arrs 1210 = inner) (hO : s.arrs 1211 = outer) :
    ∃ t u, Exec w gm06Alg511BinaryReflectCuffsProg s t u ∧ u ≤ 24 + 28 * inner.length + 28 * outer.length ∧
      Keeps [20] [1210, 1702, 1211, 1703] s t ∧
      t.arrs 1210 = gm06Alg511ReflectCuffWords inner ∧ t.arrs 1211 = gm06Alg511ReflectCuffWords outer := by
  obtain ⟨st, u₁, he₁, ht₁, hk₁, hinner⟩ := gm06Alg511BinaryReflectCuffInPlaceProg_exec (w := w) 1210 1702 (by decide)
    inner s hw hi hwi hI
  obtain ⟨t, u₂, he₂, ht₂, hk₂, houter⟩ := gm06Alg511BinaryReflectCuffInPlaceProg_exec (w := w) 1211 1703 (by decide)
    outer st hw ho hwo ((hk₁.2 1211 (by decide)).trans hO)
  exact ⟨t, u₁ + u₂, .seq he₁ he₂, by omega, (hk₁.mono (by simp) (by simp)).trans hk₂ (by simp) (by simp),
    (hk₂.2 1210 (by decide)).trans hinner, houter⟩

/-- Reflect all retained drawing fields read by the successor.
The original vertex count and ordinary endpoint array stay fixed. -/
def gm06Alg511BinaryReflectDrawingProg : Cmd :=
  .seq gm06Alg511BinaryReflectRotationsProg (.seq gm06Alg511BinaryReflectCuffsProg gm06Alg511BinaryReflectPathsProg)

/-- The whole finite reflection computes exactly the reversed
rotation/cuff/path data, preserving every binary integer row and
the original edge ends. Its displayed capacity-based time bound is
polynomial in the supplied drawing and actual simple-path sizes. -/
theorem gm06Alg511BinaryReflectDrawingProg_exec {w : ℕ} (m k n : ℕ)
    (ends inner outer : List ℕ) (rotations paths : List (List ℕ)) (s : State)
    (hw : 2 < 2 ^ w) (hn : n < 2 ^ w) (hendCount : ends.length = 2 * m)
    (haug : 2 * (m + k + k) < 2 ^ w) (hcode : (gm06EncodeRows rotations).length < 2 ^ w)
    (hwords : ∀ v ∈ gm06EncodeRows rotations, v < 2 ^ w)
    (hdarts : ∀ row ∈ rotations, ∀ d ∈ row, d < 2 * (m + k + k))
    (hi : inner.length < 2 ^ w) (ho : outer.length < 2 ^ w)
    (hwi : ∀ v ∈ inner, v < 2 ^ w) (hwo : ∀ v ∈ outer, v < 2 ^ w)
    (hpathCount : paths.length = k) (hcap : 1 + k + k * n < 2 ^ w)
    (hpaths : ∀ row ∈ paths, row.length ≤ n ∧ ∀ d ∈ row, d < 2 ^ w)
    (hE : s.arrs 1230 = ends) (hR : s.arrs 1231 = gm06EncodeRows rotations)
    (hI : s.arrs 1210 = inner) (hO : s.arrs 1211 = outer) (hP : s.arrs 8 = gm06EncodeRows paths) (hK : s.regs 52 = k) :
    ∃ t u, Exec w gm06Alg511BinaryReflectDrawingProg s t u ∧
      u ≤ 80 + 24 * (gm06EncodeRows rotations).length + rotations.length * (607 + 600 * (gm06EncodeRows rotations).length) +
        28 * inner.length + 28 * outer.length + 12 * (1 + k + k * n) +
        k * (307 + 40 * k + 150 * n + 100 * (1 + k + k * n)) ∧
      Keeps [20, 60, 4, 1400, 1401, 31, 7, 8, 9, 11, 23, 24, 323, 324, 313, 98, 1701]
        [4, 25, 26, 27, 28, 1231, 1210, 1702, 1211, 1703, 1700, 13, 8] s t ∧
      t.arrs 1231 = gm06EncodeRows (rotations.map (gm06Alg511ReflectedTableRow false m k)) ∧
      t.arrs 1210 = gm06Alg511ReflectCuffWords inner ∧ t.arrs 1211 = gm06Alg511ReflectCuffWords outer ∧
      t.arrs 8 = gm06EncodeRows (gm06Alg511ReflectedPathRows paths) := by
  obtain ⟨s₁, u₁, he₁, ht₁, hk₁, hrot⟩ := gm06Alg511BinaryReflectRotationsProg_exec (w := w) m k ends rotations s hw
    hendCount haug hcode hwords hdarts hE hR hK
  obtain ⟨s₂, u₂, he₂, ht₂, hk₂, hinner, houter⟩ := gm06Alg511BinaryReflectCuffsProg_exec (w := w) inner outer s₁ (by omega)
    hi ho hwi hwo ((hk₁.2 1210 (by decide)).trans hI) ((hk₁.2 1211 (by decide)).trans hO)
  obtain ⟨t, u₃, he₃, ht₃, hk₃, hpath⟩ := gm06Alg511BinaryReflectPathsProg_exec (w := w) paths n s₂ (by omega) hn
    (by simpa only [hpathCount] using hcap) hpaths
      ((hk₂.2 8 (by decide)).trans ((hk₁.2 8 (by decide)).trans hP))
      ((hk₂.1 52 (by decide)).trans ((hk₁.1 52 (by decide)).trans (hK.trans hpathCount.symm)))
  let R := [20, 60, 4, 1400, 1401, 31, 7, 8, 9, 11, 23, 24, 323, 324, 313, 98, 1701]
  let A := [4, 25, 26, 27, 28, 1231, 1210, 1702, 1211, 1703, 1700, 13, 8]
  have hkeep₁ : Keeps R A s s₁ := hk₁.mono (by simp [R]) (by simp [A])
  have hkeep₂ : Keeps R A s s₂ := hkeep₁.trans hk₂ (by simp [R]) (by simp [A])
  have hkeep : Keeps R A s t := hkeep₂.trans hk₃ (by simp [R]) (by simp [A])
  refine ⟨t, u₁ + (u₂ + u₃), .seq he₁ (.seq he₂ he₃), ?_, hkeep,
    (hk₃.2 1231 (by decide)).trans ((hk₂.2 1231 (by decide)).trans hrot),
    (hk₃.2 1210 (by decide)).trans hinner, (hk₃.2 1211 (by decide)).trans houter, hpath⟩
  rw [hpathCount] at ht₃
  omega

end GraphMinor.Compute
