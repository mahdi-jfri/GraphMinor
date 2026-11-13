module

public import GraphMinor.Compute.GM06CutMarkProgram
public import GraphMinor.Compute.GM06CutMarkFacts
public import GraphMinor.Compute.GM06CutRowsProgram

/-!
# Computing the complete cut rotation system from the input

Section 9 of our proof of VI (5.7) (outlined in `GraphMinor/GM06/Alg57Algorithm.lean`) first
computes path positions and signed ends at both cuffs, then splits each
original rotation by the interval table. This program performs all
of those passes. Neither cut positions nor side assignments are
supplied. Its exact output is the encoded pure cut-rotation list.
The bound counts all mark scans and the complete original-row loop.
-/

@[expose] public section
namespace GraphMinor.Compute
open TwoPaths

/-- All registers used by input-to-cut-rotation construction. -/
def gm06CutRotationRegs : List ℕ := gm06CutMarkRegs ++ gm06CutSplitRowsRegs ++ [647]

/-- Build all cut marks, compute the full augmented dart-label-space
size, and construct both induced rows of every original vertex. -/
def gm06CutRotationProg : Cmd :=
  .seq gm06CutMarkProg
    (.seq (.assign 647 (.op .mul (.const 2)
      (.op .add (.op .add (.reg 649) (.len 609)) (.len 610)))) gm06CutRowsProg)

/-- The complete finite rotation construction for cutting along the
linkage. Input rotations include both cuff rows, and the outer gap
labels follow the inner gap labels. The output decoder reads exactly
the written prefix of 625, whose length is in register 655. -/
theorem gm06CutRotationProg_exec {w n m : ℕ}
    (origins : List ℕ) (paths : List (List ℕ)) (inner outer : List ℕ)
    (rows : List (List ℕ)) (s : State)
    (hw : 4 < 2 ^ w) (hn : n < 2 ^ w)
    (hsize : 4 * (m + inner.length + outer.length) < 2 ^ w)
    (horig : origins.length = 2 * m) (hv : ∀ v ∈ origins, v < n)
    (hd : ∀ d ∈ paths.flatten, d < 2 * m)
    (hci : ∀ v ∈ inner, v < n) (hco : ∀ v ∈ outer, v < n)
    (hrows : rows.length = n) (hnd : ∀ row ∈ rows, row.Nodup)
    (hkeys : ∀ d ∈ rows.flatten, d < 2 * (m + inner.length + outer.length))
    (hpathCode : (gm06EncodeRows paths).length < 2 ^ w)
    (hpathWords : ∀ x ∈ gm06EncodeRows paths, x < 2 ^ w)
    (hrotFit : 3 + 2 * (gm06EncodeRows rows).length < 2 ^ w)
    (hrotWords : ∀ x ∈ gm06EncodeRows rows, x < 2 ^ w)
    (h600 : s.arrs 600 = gm06EncodeRows rows) (h601 : s.arrs 601 = origins)
    (h608 : s.arrs 608 = gm06EncodeRows paths) (h609 : s.arrs 609 = inner) (h610 : s.arrs 610 = outer)
    (h648 : s.regs 648 = n) (h649 : s.regs 649 = m) :
    ∃ sf t, Exec w gm06CutRotationProg s sf t ∧
      t ≤ 56 + 4 * n + 23 * paths.length + 56 * paths.flatten.length +
        31 * (inner.length + outer.length) + 2 * (gm06EncodeRows rows).length +
        n * (6000 + 26 * (m + inner.length + outer.length)) + 6000 * rows.flatten.length ∧
      Keeps gm06CutRotationRegs [611, 614, 615, 616, 620, 621, 623, 624, 625] s sf ∧
      gm06CutRowsResult sf = gm06EncodeRows (gm06CutAlongLinkageRotations n m origins paths inner outer rows) := by
  have hw2 : 2 < 2 ^ w := by omega
  have hmarkSize : 2 * (m + inner.length + outer.length) + 1 < 2 ^ w := by omega
  let marks := gm06BuildCutTables n m origins paths inner outer
  obtain ⟨s₁, t₁, he₁, ht₁, hk₁, hi₁, ho₁, hp₁, hn₁⟩ := gm06CutMarkProg_exec
    origins paths inner outer s hw2 hn hmarkSize horig hv hd hci hco hpathCode hpathWords
    h601 h608 h609 h610 h648 h649
  let s₂ := s₁.setReg 647 (2 * (m + inner.length + outer.length))
  have he₂ : Exec w (.assign 647 (.op .mul (.const 2)
      (.op .add (.op .add (.reg 649) (.len 609)) (.len 610)))) s₁ s₂ 8 :=
    .assign (GraphMinor.Compute.Crossing.eval_mul (GraphMinor.Compute.Crossing.eval_const hw2)
      (GraphMinor.Compute.Crossing.eval_add
        (GraphMinor.Compute.Crossing.eval_add
          (GraphMinor.Compute.Crossing.eval_reg ((hk₁.1 649 (by simp [gm06CutMarkRegs, gm06CutLinkageRegs])).trans h649)
            (by omega))
          (GraphMinor.Compute.Crossing.eval_len ((hk₁.2 609 (by decide)).trans h609) (by omega)) (by omega))
        (GraphMinor.Compute.Crossing.eval_len ((hk₁.2 610 (by decide)).trans h610) (by omega)) (by omega)) (by omega))
  have hk₁₂ : Keeps gm06CutRotationRegs [611, 614, 615, 616, 620, 621, 623, 624, 625] s s₂ :=
    (hk₁.mono (by simp [gm06CutRotationRegs, gm06CutMarkRegs, gm06CutLinkageRegs]) (by simp)).setReg
      (by simp [gm06CutRotationRegs]) _
  obtain ⟨sf, tf, hef, htf, hkf, hdf⟩ := gm06CutRowsProg_exec marks rows s₂ hw hn hsize
    hrows hnd hkeys (gm06BuildCutTables_lengths n m origins paths inner outer)
    (gm06BuildCutTables_words origins paths inner outer hmarkSize hd)
    hi₁ ho₁ hp₁ hn₁ ((hk₁₂.2 600 (by decide)).trans h600) (by simp [s₂]) hrotFit hrotWords
  refine ⟨sf, t₁ + (8 + tf), .seq he₁ (.seq he₂ hef), ?_,
    hk₁₂.trans hkf (by simp [gm06CutRotationRegs, gm06CutSplitRowsRegs, gm06CutSplitVertexRegs]) (by simp), hdf⟩
  rw [hrows] at htf
  omega

/-- The explicit construction bound is at most a fixed quadratic in
its finite input sizes and permanent label-space sizes. -/
theorem gm06CutRotation_cost_le_polynomial (n m k p c r d : ℕ) :
    56 + 4 * n + 23 * k + 56 * p + 31 * c + 2 * r + n * (6000 + 26 * (m + c)) + 6000 * d ≤
      100000 * (n + m + c + k + p + r + d + 1) ^ 2 := by
  let N := n + m + c + k + p + r + d + 1
  have hn : n ≤ N := by dsimp only [N]; omega
  have hmc : m + c ≤ N := by dsimp only [N]; omega
  have hN : 1 ≤ N := by dsimp only [N]; omega
  have hcross : n * (m + c) ≤ N * N := Nat.mul_le_mul hn hmc
  have hlinear : 56 + 4 * n + 23 * k + 56 * p + 31 * c + 2 * r + 6000 * n + 6000 * d ≤ 10000 * N := by
    dsimp only [N]
    omega
  have hNN : N ≤ N * N := by simpa only [Nat.mul_one] using Nat.mul_le_mul_left N hN
  have he : 56 + 4 * n + 23 * k + 56 * p + 31 * c + 2 * r + n * (6000 + 26 * (m + c)) + 6000 * d =
      (56 + 4 * n + 23 * k + 56 * p + 31 * c + 2 * r + 6000 * n + 6000 * d) + 26 * (n * (m + c)) := by ring
  rw [he]
  change _ ≤ 100000 * N ^ 2
  rw [pow_two]
  omega

end GraphMinor.Compute
