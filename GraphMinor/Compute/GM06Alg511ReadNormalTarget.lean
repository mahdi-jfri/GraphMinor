module

public import GraphMinor.Compute.GM06Alg511NormalizeTarget
public import GraphMinor.Compute.GM06Alg511WindingInput
public import GraphMinor.Compute.GM06Alg511SelectField
import Mathlib.Tactic

/-!
# Reading a positive-denominator target from retained input

For VI (5.11), page 134, read the two signed target fields from the
original drawing words and normalize the denominator's sign. The
current winding numerator and path count remain available for the
orientation comparison. No target words must be preloaded in scratch.
-/

@[expose] public section
namespace GraphMinor.Compute

/-- Select the signed target rows and normalize them in registers
62/63, 64 and 66 while preserving the computed winding. -/
def gm06Alg511ReadNormalTargetProg : Cmd :=
  .seq (gm06Alg511SelectFieldProg 1000 1002 0)
    (.seq (gm06Alg511SelectFieldProg 1002 1009 7)
      (.seq (gm06Alg511SelectFieldProg 1002 1010 8) gm06Alg511NormalizeTargetProg))

private theorem natAbs_mem_integerWords (z : ℤ) : z.natAbs ∈ gm06Alg511IntegerWords z := by
  cases z <;> simp [gm06Alg511IntegerWords]

/-- Loading and sign-normalizing the target takes linear time in
the supplied drawing words and preserves the computed winding pair. -/
theorem gm06Alg511ReadNormalTargetProg_exec {w : ℕ} (x : GM06Alg511WindingInput) (s : State)
    (hb : x.drawing.denominator ≠ 0) (hw : 1 < 2 ^ w)
    (ha : s.arrs 1000 = gm06Alg511WindingWords x)
    (hn : (gm06Alg511WindingWords x).length < 2 ^ w)
    (hwords : ∀ v ∈ gm06Alg511WindingWords x, v < 2 ^ w) :
    ∃ s' t, Exec w gm06Alg511ReadNormalTargetProg s s' t ∧
      t ≤ 413 + 22 * (gm06Alg511Words x.drawing).length ∧
      s'.regs 62 = (gm06Alg511NormalTargetNumerator x.drawing.numerator x.drawing.denominator).toNat ∧
      s'.regs 63 = (-(gm06Alg511NormalTargetNumerator x.drawing.numerator x.drawing.denominator)).toNat ∧
      s'.regs 64 = x.drawing.denominator.natAbs ∧ s'.regs 66 = x.drawing.denominator.natAbs ∧
      0 < s'.regs 64 ∧
      ((s'.regs 62 : ℝ) - (s'.regs 63 : ℝ)) / s'.regs 64 = x.drawing.target ∧
      s'.regs 54 = s.regs 54 ∧ s'.regs 55 = s.regs 55 ∧ s'.regs 52 = s.regs 52 ∧
      ∀ a, a ∉ [1002, 1009, 1010] → s'.arrs a = s.arrs a := by
  let rows := [gm06Alg511Words x.drawing,
    gm06EncodeRows (x.edgeTurns.map gm06Alg511IntegerWords)]
  have hrow : gm06Alg511Words x.drawing ∈ rows := by simp [rows]
  have hbfit := (gm06Alg511_encoded_row_length_le hrow).trans_lt hn
  have hbwords : ∀ v ∈ gm06Alg511Words x.drawing, v < 2 ^ w :=
    fun v hv => hwords v (gm06Alg511_mem_encoded_row hrow hv)
  obtain ⟨s₁, t₁, he₁, ht₁, hbase, harr₁⟩ := gm06Alg511SelectFieldProg_exec
    1000 1002 (by decide) rows 0 (by simp [rows]) s hw ha hn hwords
  change s₁.arrs 1002 = gm06EncodeRows (gm06Alg511Rows x.drawing) at hbase
  obtain ⟨s₂, t₂, he₂, ht₂, hnum, harr₂⟩ := gm06Alg511SelectFieldProg_exec
    1002 1009 (by decide) (gm06Alg511Rows x.drawing) 7 (by simp [gm06Alg511Rows])
    s₁ hw hbase hbfit hbwords
  have hbase₂ : s₂.arrs 1002 = gm06EncodeRows (gm06Alg511Rows x.drawing) :=
    (harr₂ 1002 (by decide)).trans hbase
  obtain ⟨s₃, t₃, he₃, ht₃, hden, harr₃⟩ := gm06Alg511SelectFieldProg_exec
    1002 1010 (by decide) (gm06Alg511Rows x.drawing) 8 (by simp [gm06Alg511Rows])
    s₂ hw hbase₂ hbfit hbwords
  have hnum₃ : s₃.arrs 1009 = gm06Alg511IntegerWords x.drawing.numerator :=
    (harr₃ 1009 (by decide)).trans hnum
  have hafit : x.drawing.numerator.natAbs < 2 ^ w := hbwords _
    (gm06Alg511_mem_encoded_row (rows := gm06Alg511Rows x.drawing)
      (row := gm06Alg511IntegerWords x.drawing.numerator) (by simp [gm06Alg511Rows])
      (natAbs_mem_integerWords _))
  have hdfit : x.drawing.denominator.natAbs < 2 ^ w := hbwords _
    (gm06Alg511_mem_encoded_row (rows := gm06Alg511Rows x.drawing)
      (row := gm06Alg511IntegerWords x.drawing.denominator) (by simp [gm06Alg511Rows])
      (natAbs_mem_integerWords _))
  obtain ⟨s₄, he₄, hp, hq, hd, hd', hpos, hvalue, hkeep⟩ :=
    gm06Alg511NormalizeTargetProg_exec x.drawing.numerator x.drawing.denominator s₃
      hb hw hafit hdfit hnum₃ hden
  have he : Exec w gm06Alg511ReadNormalTargetProg s s₄ (t₁ + (t₂ + (t₃ + 16))) :=
    .seq he₁ (.seq he₂ (.seq he₃ he₄))
  refine ⟨s₄, _, he, ?_, hp, hq, hd, hd', hpos, hvalue,
    he.regs_eq_of_not_mem_writtenRegs (by decide), he.regs_eq_of_not_mem_writtenRegs (by decide),
    he.regs_eq_of_not_mem_writtenRegs (by decide), ?_⟩
  · change t₁ ≤ 18 + 17 * 0 + 22 * (gm06Alg511Words x.drawing).length at ht₁
    change t₂ ≤ 18 + 17 * 7 + 22 * 2 at ht₂
    change t₃ ≤ 18 + 17 * 8 + 22 * 2 at ht₃
    omega
  · intro a ha'
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at ha'
    obtain ⟨ha2, ha9, ha10⟩ := ha'
    rw [hkeep.2 a (by simp), harr₃ a ha10, harr₂ a ha9, harr₁ a ha2]

end GraphMinor.Compute
