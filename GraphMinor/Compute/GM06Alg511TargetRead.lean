module

public import GraphMinor.Compute.GM06Alg511WindingInput
public import GraphMinor.Compute.GM06Alg511InitialTest
public import GraphMinor.Compute.GM06Alg511SelectField
import Mathlib.Tactic

/-!
# Reading the rational target while preserving the flow input

The full drawing is retained in array 1000 after loading the plain
input. Select its base drawing row, then the path count and the two
target integers. Apply the verified remainder test of (5.10)(i), as
required before the maximum-flow check on page 134. Array zero keeps
the ordinary graph input throughout this phase.
-/

@[expose] public section
namespace GraphMinor.Compute

/-- Read the signed target from the retained drawing and test
integrality, preserving the prepared Menger input in array zero. -/
def gm06Alg511ReadTargetProg : Cmd :=
  .seq (gm06Alg511SelectFieldProg 1000 1002 0)
    (.seq (gm06Alg511SelectFieldProg 1002 8 6)
      (.seq (gm06Alg511SelectFieldProg 1002 9 7)
        (.seq (gm06Alg511SelectFieldProg 1002 10 8) gm06Alg511LoadedTest)))

/-- The target-reading phase returns exactly (5.10)(i), with a linear
bound and with both the full drawing and graph input preserved. -/
theorem gm06Alg511ReadTargetProg_exec {w : ℕ} (x : GM06Alg511WindingInput) (s : State)
    (hb : x.drawing.denominator ≠ 0) (hw : 1 < 2 ^ w)
    (ha : s.arrs 1000 = gm06Alg511WindingWords x)
    (hn : (gm06Alg511WindingWords x).length < 2 ^ w)
    (hwords : ∀ v ∈ gm06Alg511WindingWords x, v < 2 ^ w)
    (hkfit : x.drawing.pathCount < 2 ^ w) (hafit : x.drawing.numerator.natAbs < 2 ^ w)
    (hdfit : x.drawing.denominator.natAbs < 2 ^ w)
    (hprod : x.drawing.pathCount * x.drawing.numerator.natAbs < 2 ^ w) :
    ∃ s' t, Exec w gm06Alg511ReadTargetProg s s' t ∧
      t ≤ 556 + 22 * (gm06Alg511Words x.drawing).length ∧
      s'.arrs 0 = s.arrs 0 ∧ s'.arrs 1000 = s.arrs 1000 ∧
      (s'.regs 0 = 0 ∨ s'.regs 0 = 1) ∧
      (s'.regs 0 = 1 ↔ ∃ m : ℤ, (x.drawing.pathCount : ℝ) * x.drawing.target = m) := by
  let rows := [gm06Alg511Words x.drawing,
    gm06EncodeRows (x.edgeTurns.map gm06Alg511IntegerWords)]
  have hrow : gm06Alg511Words x.drawing ∈ rows := by simp [rows]
  have hbasefit : (gm06Alg511Words x.drawing).length < 2 ^ w :=
    (gm06Alg511_encoded_row_length_le hrow).trans_lt hn
  have hbasewords : ∀ v ∈ gm06Alg511Words x.drawing, v < 2 ^ w := by
    intro v hv
    exact hwords v (gm06Alg511_mem_encoded_row hrow hv)
  obtain ⟨s₁, t₁, he₁, ht₁, hbase, harr₁⟩ := gm06Alg511SelectFieldProg_exec
    1000 1002 (by decide) rows 0 (by simp [rows]) s hw ha hn hwords
  have hcode : s₁.arrs 1002 = gm06EncodeRows (gm06Alg511Rows x.drawing) := hbase
  obtain ⟨s₂, t₂, he₂, ht₂, hcount, harr₂⟩ := gm06Alg511SelectFieldProg_exec
    1002 8 (by decide) (gm06Alg511Rows x.drawing) 6 (by simp [gm06Alg511Rows])
    s₁ hw hcode hbasefit hbasewords
  have hcode₂ : s₂.arrs 1002 = gm06EncodeRows (gm06Alg511Rows x.drawing) := by
    rw [harr₂ 1002 (by decide), hcode]
  obtain ⟨s₃, t₃, he₃, ht₃, hnum, harr₃⟩ := gm06Alg511SelectFieldProg_exec
    1002 9 (by decide) (gm06Alg511Rows x.drawing) 7 (by simp [gm06Alg511Rows])
    s₂ hw hcode₂ hbasefit hbasewords
  have hcode₃ : s₃.arrs 1002 = gm06EncodeRows (gm06Alg511Rows x.drawing) := by
    rw [harr₃ 1002 (by decide), hcode₂]
  obtain ⟨s₄, t₄, he₄, ht₄, hden, harr₄⟩ := gm06Alg511SelectFieldProg_exec
    1002 10 (by decide) (gm06Alg511Rows x.drawing) 8 (by simp [gm06Alg511Rows])
    s₃ hw hcode₃ hbasefit hbasewords
  have hK : s₄.arrs 8 = [x.drawing.pathCount] := by
    rw [harr₄ 8 (by decide), harr₃ 8 (by decide)]
    exact hcount
  have hA : s₄.arrs 9 = gm06Alg511IntegerWords x.drawing.numerator := by
    rw [harr₄ 9 (by decide)]
    exact hnum
  have hD : s₄.arrs 10 = gm06Alg511IntegerWords x.drawing.denominator := hden
  obtain ⟨s₅, he₅, harr₅, hbit, hbool⟩ := gm06Alg511LoadedTest_exec
    x.drawing s₄ w hb hw hK hA hD hkfit hafit hdfit hprod
  refine ⟨s₅, t₁ + (t₂ + (t₃ + (t₄ + 17))),
    .seq he₁ (.seq he₂ (.seq he₃ (.seq he₄ he₅))), ?_, ?_, ?_, hbool, hbit⟩
  · change t₁ ≤ 18 + 17 * 0 + 22 * (gm06Alg511Words x.drawing).length at ht₁
    change t₂ ≤ 18 + 17 * 6 + 22 * 1 at ht₂
    change t₃ ≤ 18 + 17 * 7 + 22 * 2 at ht₃
    change t₄ ≤ 18 + 17 * 8 + 22 * 2 at ht₄
    omega
  · rw [harr₅, harr₄ 0 (by decide), harr₃ 0 (by decide), harr₂ 0 (by decide), harr₁ 0 (by decide)]
  · rw [harr₅, harr₄ 1000 (by decide), harr₃ 1000 (by decide),
      harr₂ 1000 (by decide), harr₁ 1000 (by decide)]

end GraphMinor.Compute
