module

public import GraphMinor.Compute.GM06Alg511WindingInput
public import GraphMinor.Compute.GM06Alg511SelectField
public import GraphMinor.Compute.TwoPathsCyc
import GraphMinor.Compute.CrossingOpsBasic
import Mathlib.Tactic

/-!
# Reading the ordinary fields needed by the initial winding phase

For VI (5.11), page 134, retain the flow result and read the original
drawing from array 1000. Load its endpoint list, ordered cuffs and
counts into scratch arrays. Start at the first prescribed inner cuff
label. Every loaded value is an ordinary supplied instance field.
-/

@[expose] public section
namespace GraphMinor.Compute
open TwoPaths

/-- Read the graph fields needed for winding computation, then set
the vertex count, first source, path count and source index registers. -/
def gm06Alg511WindingFieldsProg : Cmd :=
  .seq (gm06Alg511SelectFieldProg 1000 1002 0)
    (.seq (gm06Alg511SelectFieldProg 1002 1007 0)
      (.seq (gm06Alg511SelectFieldProg 1002 1004 4)
        (.seq (gm06Alg511SelectFieldProg 1002 1006 5)
          (.seq (gm06Alg511SelectFieldProg 1002 1008 6)
            (.seq (gm06Alg511SelectFieldProg 1002 3 1)
              (.seq (.assign 41 (.read 1007 (.const 0)))
                (.seq (.assign 40 (.read 1004 (.const 0)))
                  (.seq (.assign 52 (.read 1008 (.const 0)))
                    (.assign 53 (.const 0))))))))))

/-- The field-loading program reads exactly the supplied graph data
and preserves the maximum-flow output and retained drawing. -/
theorem gm06Alg511WindingFieldsProg_exec {w : ℕ} (x : GM06Alg511WindingInput) (s : State)
    (hw : 1 < 2 ^ w) (hinner : x.drawing.innerCuff ≠ [])
    (ha : s.arrs 1000 = gm06Alg511WindingWords x)
    (hn : (gm06Alg511WindingWords x).length < 2 ^ w)
    (hwords : ∀ v ∈ gm06Alg511WindingWords x, v < 2 ^ w) :
    ∃ s' t, Exec w gm06Alg511WindingFieldsProg s s' t ∧
      t ≤ 535 + 88 * (gm06Alg511Words x.drawing).length ∧
      s'.arrs 3 = x.drawing.endpoints ∧ s'.arrs 1006 = x.drawing.outerCuff ∧
      s'.arrs 1004 = x.drawing.innerCuff ∧
      s'.regs 41 = x.drawing.vertexCount ∧ s'.regs 40 = x.drawing.innerCuff.getD 0 0 ∧
      s'.regs 52 = x.drawing.pathCount ∧ s'.regs 53 = 0 ∧
      ∀ a, a ∉ [1002, 1007, 1004, 1006, 1008, 3] → s'.arrs a = s.arrs a := by
  let rows := [gm06Alg511Words x.drawing,
    gm06EncodeRows (x.edgeTurns.map gm06Alg511IntegerWords)]
  have hrow : gm06Alg511Words x.drawing ∈ rows := by simp [rows]
  have hbfit := (gm06Alg511_encoded_row_length_le hrow).trans_lt hn
  have hbwords : ∀ v ∈ gm06Alg511Words x.drawing, v < 2 ^ w :=
    fun v hv => hwords v (gm06Alg511_mem_encoded_row hrow hv)
  obtain ⟨s₁, t₁, he₁, ht₁, hbase, harr₁⟩ := gm06Alg511SelectFieldProg_exec
    1000 1002 (by decide) rows 0 (by simp [rows]) s hw ha hn hwords
  change s₁.arrs 1002 = gm06EncodeRows (gm06Alg511Rows x.drawing) at hbase
  obtain ⟨s₂, t₂, he₂, ht₂, hcount, harr₂⟩ := gm06Alg511SelectFieldProg_exec
    1002 1007 (by decide) (gm06Alg511Rows x.drawing) 0 (by simp [gm06Alg511Rows])
    s₁ hw hbase hbfit hbwords
  have hbase₂ : s₂.arrs 1002 = gm06EncodeRows (gm06Alg511Rows x.drawing) :=
    (harr₂ 1002 (by decide)).trans hbase
  obtain ⟨s₃, t₃, he₃, ht₃, hinnerrow, harr₃⟩ := gm06Alg511SelectFieldProg_exec
    1002 1004 (by decide) (gm06Alg511Rows x.drawing) 4 (by simp [gm06Alg511Rows])
    s₂ hw hbase₂ hbfit hbwords
  have hbase₃ : s₃.arrs 1002 = gm06EncodeRows (gm06Alg511Rows x.drawing) :=
    (harr₃ 1002 (by decide)).trans hbase₂
  obtain ⟨s₄, t₄, he₄, ht₄, houter, harr₄⟩ := gm06Alg511SelectFieldProg_exec
    1002 1006 (by decide) (gm06Alg511Rows x.drawing) 5 (by simp [gm06Alg511Rows])
    s₃ hw hbase₃ hbfit hbwords
  have hbase₄ : s₄.arrs 1002 = gm06EncodeRows (gm06Alg511Rows x.drawing) :=
    (harr₄ 1002 (by decide)).trans hbase₃
  obtain ⟨s₅, t₅, he₅, ht₅, hkrow, harr₅⟩ := gm06Alg511SelectFieldProg_exec
    1002 1008 (by decide) (gm06Alg511Rows x.drawing) 6 (by simp [gm06Alg511Rows])
    s₄ hw hbase₄ hbfit hbwords
  have hbase₅ : s₅.arrs 1002 = gm06EncodeRows (gm06Alg511Rows x.drawing) :=
    (harr₅ 1002 (by decide)).trans hbase₄
  obtain ⟨s₆, t₆, he₆, ht₆, hends, harr₆⟩ := gm06Alg511SelectFieldProg_exec
    1002 3 (by decide) (gm06Alg511Rows x.drawing) 1 (by simp [gm06Alg511Rows])
    s₅ hw hbase₅ hbfit hbwords
  change s₄.arrs 1006 = x.drawing.outerCuff at houter
  change s₆.arrs 3 = x.drawing.endpoints at hends
  have hNrow : s₆.arrs 1007 = [x.drawing.vertexCount] := by
    rw [harr₆ 1007 (by decide), harr₅ 1007 (by decide), harr₄ 1007 (by decide),
      harr₃ 1007 (by decide)]
    exact hcount
  have hIrow : s₆.arrs 1004 = x.drawing.innerCuff := by
    rw [harr₆ 1004 (by decide), harr₅ 1004 (by decide), harr₄ 1004 (by decide)]
    exact hinnerrow
  have hKrow : s₆.arrs 1008 = [x.drawing.pathCount] :=
    (harr₆ 1008 (by decide)).trans hkrow
  have hnfit : x.drawing.vertexCount < 2 ^ w := hbwords _
    (gm06Alg511_mem_encoded_row (rows := gm06Alg511Rows x.drawing)
      (row := [x.drawing.vertexCount]) (by simp [gm06Alg511Rows]) (by simp))
  have hkfit : x.drawing.pathCount < 2 ^ w := hbwords _
    (gm06Alg511_mem_encoded_row (rows := gm06Alg511Rows x.drawing)
      (row := [x.drawing.pathCount]) (by simp [gm06Alg511Rows]) (by simp))
  have hheadmem : x.drawing.innerCuff.getD 0 0 ∈ x.drawing.innerCuff := by
    cases h : x.drawing.innerCuff with
    | nil => exact False.elim (hinner h)
    | cons a as => simp
  have hheadfit : x.drawing.innerCuff.getD 0 0 < 2 ^ w := hbwords _
    (gm06Alg511_mem_encoded_row (rows := gm06Alg511Rows x.drawing)
      (row := x.drawing.innerCuff) (by simp [gm06Alg511Rows]) hheadmem)
  have hipos : 0 < x.drawing.innerCuff.length := by
    cases h : x.drawing.innerCuff with
    | nil => exact False.elim (hinner h)
    | cons a as => simp
  let s₇ := s₆.setReg 41 x.drawing.vertexCount
  let s₈ := s₇.setReg 40 (x.drawing.innerCuff.getD 0 0)
  let s₉ := s₈.setReg 52 x.drawing.pathCount
  let s₁₀ := s₉.setReg 53 0
  have he₇ : Exec w (.assign 41 (.read 1007 (.const 0))) s₆ s₇ 3 :=
    .assign (by simp [Expr.eval, hNrow, checkWord, hnfit])
  have he₈ : Exec w (.assign 40 (.read 1004 (.const 0))) s₇ s₈ 3 := by
    apply Exec.assign
    have hi₇ : 0 < (s₇.arrs 1004).length := by simpa [s₇, hIrow] using hipos
    have hh := Crossing.eval_read (a := 1004) (Crossing.eval_const (Nat.two_pow_pos w)) hi₇
      (show (s₇.arrs 1004)[0] < 2 ^ w by simpa [s₇, hIrow, hipos] using hheadfit)
    simpa [s₇, hIrow, hipos] using hh
  have he₉ : Exec w (.assign 52 (.read 1008 (.const 0))) s₈ s₉ 3 :=
    .assign (by simp [Expr.eval, s₈, s₇, hKrow, checkWord, hkfit])
  have he₁₀ : Exec w (.assign 53 (.const 0)) s₉ s₁₀ 2 :=
    .assign (Crossing.eval_const (Nat.two_pow_pos w))
  refine ⟨s₁₀, t₁ + (t₂ + (t₃ + (t₄ + (t₅ + (t₆ + 11))))),
    .seq he₁ (.seq he₂ (.seq he₃ (.seq he₄ (.seq he₅ (.seq he₆
      (.seq he₇ (.seq he₈ (.seq he₉ he₁₀)))))))), ?_, hends, ?_, hIrow,
    by simp [s₁₀, s₉, s₈, s₇], by simp [s₁₀, s₉, s₈],
    by simp [s₁₀, s₉], by simp [s₁₀], ?_⟩
  · change t₁ ≤ 18 + 17 * 0 + 22 * (gm06Alg511Words x.drawing).length at ht₁
    change t₂ ≤ 18 + 17 * 0 + 22 * 1 at ht₂
    change t₃ ≤ 18 + 17 * 4 + 22 * x.drawing.innerCuff.length at ht₃
    change t₄ ≤ 18 + 17 * 5 + 22 * x.drawing.outerCuff.length at ht₄
    change t₅ ≤ 18 + 17 * 6 + 22 * 1 at ht₅
    change t₆ ≤ 18 + 17 * 1 + 22 * x.drawing.endpoints.length at ht₆
    have hi := gm06Alg511_encoded_row_length_le
      (rows := gm06Alg511Rows x.drawing) (row := x.drawing.innerCuff) (by simp [gm06Alg511Rows])
    have ho := gm06Alg511_encoded_row_length_le
      (rows := gm06Alg511Rows x.drawing) (row := x.drawing.outerCuff) (by simp [gm06Alg511Rows])
    have he := gm06Alg511_encoded_row_length_le
      (rows := gm06Alg511Rows x.drawing) (row := x.drawing.endpoints) (by simp [gm06Alg511Rows])
    change x.drawing.innerCuff.length ≤ (gm06Alg511Words x.drawing).length at hi
    change x.drawing.outerCuff.length ≤ (gm06Alg511Words x.drawing).length at ho
    change x.drawing.endpoints.length ≤ (gm06Alg511Words x.drawing).length at he
    omega
  · simpa only [s₁₀, s₉, s₈, s₇, State.setReg_arrs] using
      (harr₆ 1006 (by decide)).trans ((harr₅ 1006 (by decide)).trans houter)
  · intro a ha'
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at ha'
    obtain ⟨ha2, ha7, ha4, ha6, ha8, ha3⟩ := ha'
    simp only [s₁₀, s₉, s₈, s₇, State.setReg_arrs]
    rw [harr₆ a ha3, harr₅ a ha8, harr₄ a ha6, harr₃ a ha4, harr₂ a ha7, harr₁ a ha2]

end GraphMinor.Compute
