module

public import GraphMinor.Compute.GM06Alg511ReflectedInput
public import GraphMinor.Compute.GM06Alg511TailPosition
import GraphMinor.Compute.CrossingOpsBasic
import Mathlib.Tactic

/-!
# Computing one vertex's reflected reference correction

For VI (5.11), page 134, scan the two ordered cuff rows for a vertex
label. A positive matching position contributes a whole-turn
correction, while the first position and the missing-label sentinel
do not. Write the resulting bit into the vertex correction array.
-/

@[expose] public section
namespace GraphMinor.Compute
open TwoPaths

/-- Test whether a found cuff position is positive and below the
missing-label sentinel. -/
def gm06Alg511TailExpr (res : Reg) (row : Arr) : Expr :=
  .op .mul (.op .lt (.const 0) (.reg res)) (.op .lt (.reg res) (.len row))

private theorem tailExpr_eval {w : ℕ} (res row q len : ℕ) (s : State)
    (hw : 1 < 2 ^ w) (hn : len < 2 ^ w) (hq : q ≤ len)
    (hr : s.regs res = q) (ha : (s.arrs row).length = len) :
    (gm06Alg511TailExpr res row).eval w s = some (if 0 < q ∧ q < len then 1 else 0) := by
  have hqfit := hq.trans_lt hn
  have hfirst := Crossing.eval_lt (Crossing.eval_const (Nat.two_pow_pos w))
    (Crossing.eval_reg hr hqfit) hw
  have hlen : (Expr.len row).eval w s = some len := by simp [Expr.eval, ha, checkWord, hn]
  have hsecond := Crossing.eval_lt (Crossing.eval_reg hr hqfit) hlen hw
  have hbound : (if 0 < q then 1 else 0) * (if q < len then 1 else 0) < 2 ^ w := by
    split_ifs <;> omega
  have he := Crossing.eval_mul hfirst hsecond hbound
  have hbit : (if 0 < q then 1 else 0) * (if q < len then 1 else 0) =
      if 0 < q ∧ q < len then 1 else 0 := by split_ifs <;> omega
  simpa only [gm06Alg511TailExpr, hbit] using he

private theorem bit_sum_le_two (P Q : Prop) [Decidable P] [Decidable Q] :
    (if P then 1 else 0) + (if Q then 1 else 0) ≤ 2 := by
  split_ifs <;> omega

private theorem positive_bit_sum (P Q : Prop) [Decidable P] [Decidable Q] :
    (if 0 < (if P then 1 else 0) + (if Q then 1 else 0) then 1 else 0) =
      if P ∨ Q then 1 else 0 := by
  by_cases hP : P <;> by_cases hQ : Q <;> simp [hP, hQ]

/-- For vertex counter 77, search inner row 1004 and outer row 1006,
then write its reference correction into array 1200. -/
def gm06Alg511OffsetBody : Cmd :=
  .seq (gm06FindLabelProg 1004 77 20 64)
    (.seq (gm06FindLabelProg 1006 77 20 65)
      (.write 1200 (.reg 77) (.op .lt (.const 0)
        (.op .add (gm06Alg511TailExpr 64 1004) (gm06Alg511TailExpr 65 1006)))))

/-- The two scans compute the exact supplied-cuff correction bit
for one vertex, preserving the cuff rows and all other arrays. -/
theorem gm06Alg511OffsetBody_exec {w : ℕ} (x : GM06Alg511Input) (v : ℕ) (s : State)
    (hw : 2 < 2 ^ w) (hn : x.vertexCount < 2 ^ w) (hv : v < x.vertexCount)
    (hi : x.innerCuff.length < 2 ^ w) (ho : x.outerCuff.length < 2 ^ w)
    (hiwords : ∀ a ∈ x.innerCuff, a < 2 ^ w) (howords : ∀ a ∈ x.outerCuff, a < 2 ^ w)
    (hind : x.innerCuff.Nodup) (hond : x.outerCuff.Nodup)
    (hinner : s.arrs 1004 = x.innerCuff) (houter : s.arrs 1006 = x.outerCuff)
    (hcap : (s.arrs 1200).length = x.vertexCount) (hcur : s.regs 77 = v) :
    ∃ s' t, Exec w gm06Alg511OffsetBody s s' t ∧
      t ≤ 33 + 13 * x.innerCuff.length + 13 * x.outerCuff.length ∧
      Keeps [20, 64, 65] [1200] s s' ∧
      s'.arrs 1200 = (s.arrs 1200).set v (gm06Alg511CuffOffset x v) := by
  have hw₁ : 1 < 2 ^ w := by omega
  obtain ⟨s₁, t₁, he₁, ht₁, hk₁, hres₁⟩ := gm06FindLabelProg_exec
    1004 77 20 64 (by decide) (by decide) (by decide) x.innerCuff v s hw₁ hi hiwords
    (hv.trans hn) hinner hcur
  have hinneq := gm06Alg511Tail_mem_iff_of_scan x.innerCuff hind v (s₁.regs 64) hres₁
  have hpos₁ : s₁.regs 64 ≤ x.innerCuff.length := by
    rcases hres₁ with h | ⟨j, hj, hr, _⟩ <;> omega
  obtain ⟨s₂, t₂, he₂, ht₂, hk₂, hres₂⟩ := gm06FindLabelProg_exec
    1006 77 20 65 (by decide) (by decide) (by decide) x.outerCuff v s₁ hw₁ ho howords
    (hv.trans hn) ((hk₁.2 1006 (by simp)).trans houter) ((hk₁.1 77 (by decide)).trans hcur)
  have houteq := gm06Alg511Tail_mem_iff_of_scan x.outerCuff hond v (s₂.regs 65) hres₂
  have hpos₂ : s₂.regs 65 ≤ x.outerCuff.length := by
    rcases hres₂ with h | ⟨j, hj, hr, _⟩ <;> omega
  have hinner₂ : s₂.arrs 1004 = x.innerCuff :=
    (hk₂.2 1004 (by simp)).trans ((hk₁.2 1004 (by simp)).trans hinner)
  have houter₂ : s₂.arrs 1006 = x.outerCuff :=
    (hk₂.2 1006 (by simp)).trans ((hk₁.2 1006 (by simp)).trans houter)
  have heI : (gm06Alg511TailExpr 64 1004).eval w s₂ =
      some (if v ∈ x.innerCuff.tail then 1 else 0) := by
    simpa only [← hinneq] using tailExpr_eval 64 1004 (s₁.regs 64) x.innerCuff.length s₂
      hw₁ hi hpos₁ (hk₂.1 64 (by decide)) (congrArg List.length hinner₂)
  have heO : (gm06Alg511TailExpr 65 1006).eval w s₂ =
      some (if v ∈ x.outerCuff.tail then 1 else 0) := by
    simpa only [← houteq] using tailExpr_eval 65 1006 (s₂.regs 65) x.outerCuff.length s₂
      hw₁ ho hpos₂ rfl (congrArg List.length houter₂)
  have hsumfit : (if v ∈ x.innerCuff.tail then 1 else 0) +
      (if v ∈ x.outerCuff.tail then 1 else 0) < 2 ^ w :=
    (bit_sum_le_two _ _).trans_lt hw
  have heOffset := Crossing.eval_lt (Crossing.eval_const (Nat.two_pow_pos w))
    (Crossing.eval_add heI heO hsumfit) hw₁
  have hbit : (if 0 < (if v ∈ x.innerCuff.tail then 1 else 0) +
      (if v ∈ x.outerCuff.tail then 1 else 0) then 1 else 0) = gm06Alg511CuffOffset x v := by
    exact positive_bit_sum _ _
  rw [hbit] at heOffset
  have hcur₂ : s₂.regs 77 = v := (hk₂.1 77 (by decide)).trans ((hk₁.1 77 (by decide)).trans hcur)
  have hcap₂ : (s₂.arrs 1200).length = x.vertexCount := by
    rw [hk₂.2 1200 (by simp), hk₁.2 1200 (by simp), hcap]
  let s₃ := s₂.writeArr 1200 v (gm06Alg511CuffOffset x v)
  have he₃ : Exec w
      (.write 1200 (.reg 77) (.op .lt (.const 0)
        (.op .add (gm06Alg511TailExpr 64 1004) (gm06Alg511TailExpr 65 1006)))) s₂ s₃ 19 :=
    .write (Crossing.eval_reg hcur₂ (hv.trans hn)) heOffset (by rw [hcap₂]; exact hv)
  have hkeep : Keeps [20, 64, 65] [1200] s s₂ :=
    (hk₁.mono (by simp) (by simp)).trans hk₂ (by simp) (by simp)
  refine ⟨s₃, t₁ + (t₂ + 19), .seq he₁ (.seq he₂ he₃), by omega,
    hkeep.writeArr (by simp) _ _, ?_⟩
  simp only [s₃, State.writeArr, State.setArr_arrs, ite_true]
  rw [hk₂.2 1200 (by simp), hk₁.2 1200 (by simp)]

end GraphMinor.Compute
