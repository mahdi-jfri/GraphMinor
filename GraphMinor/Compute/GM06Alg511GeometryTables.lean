module

public import GraphMinor.Compute.GM06Alg511ReflectTable
public import GraphMinor.Compute.GM06Alg511SelectField
public import GraphMinor.Compute.GM06Alg511CopyRow
public import GraphMinor.Compute.GM06Alg511ReflectedInput
import GraphMinor.Compute.CrossingOpsReplLists
import Mathlib.Tactic

/-!
# Loading and computing both reflected drawing tables

For the orientation step of VI (5.11), page 134, read the rotation
and region fields from the supplied drawing words. Compute the
original edge count from the endpoint row. Transform each complete
encoded table and retain the two results in arrays 1220 and 1221.
The results are exactly the corresponding fields of the finite
reflected input. The bound is quadratic in the supplied drawing
word length, and all other instance arrays are preserved.
-/

@[expose] public section
namespace GraphMinor.Compute
open TwoPaths GraphMinor.Compute.Crossing

/-- Compute the original edge count, read and reflect the rotation
table, then read and reflect the region table. Array 1002 retains
the supplied drawing words and array 3 its original endpoint row. -/
def gm06Alg511ReflectGeometryTablesProg : Cmd :=
  .seq (.assign 60 (.op .div (.len 3) (.const 2)))
    (.seq (gm06Alg511SelectFieldProg 1002 4 2)
      (.seq (gm06Alg511ReflectTableProg false)
        (.seq (gm06Alg511CopyRowProg 4 1220)
          (.seq (gm06Alg511SelectFieldProg 1002 4 3)
            (.seq (gm06Alg511ReflectTableProg true) (gm06Alg511CopyRowProg 4 1221))))))

private theorem geometry_time_le (B R F a b c d e f : ℕ)
    (hR : R ≤ B) (hF : F ≤ B)
    (ha : a ≤ 52 + 22 * R) (hb : b ≤ 1000 * (R + 1) ^ 2)
    (hc : c ≤ 6 + 12 * R) (hd : d ≤ 69 + 22 * F)
    (he : e ≤ 1000 * (F + 1) ^ 2) (hf : f ≤ 6 + 12 * F) :
    4 + (a + (b + (c + (d + (e + f))))) ≤ 3000 * (B + 1) ^ 2 := by
  have hpR : (R + 1) ^ 2 ≤ (B + 1) ^ 2 := Nat.pow_le_pow_left (by omega) 2
  have hpF : (F + 1) ^ 2 ≤ (B + 1) ^ 2 := Nat.pow_le_pow_left (by omega) 2
  have hb' := hb.trans (Nat.mul_le_mul_left 1000 hpR)
  have he' := he.trans (Nat.mul_le_mul_left 1000 hpF)
  nlinarith

/-- Both reflected drawing tables are computed from their ordinary
supplied input fields, with a fixed quadratic running-time bound.
The source, flow and retained linkage arrays are preserved. -/
theorem gm06Alg511ReflectGeometryTablesProg_exec {w : ℕ}
    (x : GM06Alg511Input) (s : State) (hw : 2 < 2 ^ w)
    (hn : (gm06Alg511Words x).length < 2 ^ w)
    (hwords : ∀ v ∈ gm06Alg511Words x, v < 2 ^ w)
    (haug : 2 * (x.endpoints.length / 2 + x.pathCount + x.pathCount) < 2 ^ w)
    (hrot : ∀ row ∈ x.rotations, ∀ d ∈ row,
      d < 2 * (x.endpoints.length / 2 + x.pathCount + x.pathCount))
    (hregion : ∀ row ∈ x.regionBoundaries, ∀ d ∈ row.tail,
      d < 2 * (x.endpoints.length / 2 + x.pathCount + x.pathCount))
    (h1002 : s.arrs 1002 = gm06Alg511Words x) (h3 : s.arrs 3 = x.endpoints)
    (h52 : s.regs 52 = x.pathCount) :
    ∃ s' t, Exec w gm06Alg511ReflectGeometryTablesProg s s' t ∧
      t ≤ 3000 * ((gm06Alg511Words x).length + 1) ^ 2 ∧
      Keeps [60, 31, 7, 8, 9, 11, 20, 23, 24, 323, 324, 313, 98, 1400, 1401]
        [4, 25, 26, 27, 28, 1220, 1221] s s' ∧
      s'.regs 60 = x.endpoints.length / 2 ∧
      s'.arrs 1220 = gm06EncodeRows x.reflected.rotations ∧
      s'.arrs 1221 = gm06EncodeRows x.reflected.regionBoundaries := by
  let m := x.endpoints.length / 2
  let k := x.pathCount
  let B := (gm06Alg511Words x).length
  let R := (gm06EncodeRows x.rotations).length
  let F := (gm06EncodeRows x.regionBoundaries).length
  have hE : x.endpoints.length ≤ B :=
    gm06Alg511_encoded_row_length_le (by simp [gm06Alg511Rows])
  have hR : R ≤ B := gm06Alg511_encoded_row_length_le (by simp [gm06Alg511Rows])
  have hF : F ≤ B := gm06Alg511_encoded_row_length_le (by simp [gm06Alg511Rows])
  have hRw : R < 2 ^ w := hR.trans_lt hn
  have hFw : F < 2 ^ w := hF.trans_lt hn
  have hRotWords : ∀ d ∈ gm06EncodeRows x.rotations, d < 2 ^ w :=
    fun d hd => hwords d (gm06Alg511_mem_encoded_row (by simp [gm06Alg511Rows]) hd)
  have hRegWords : ∀ d ∈ gm06EncodeRows x.regionBoundaries, d < 2 ^ w :=
    fun d hd => hwords d (gm06Alg511_mem_encoded_row (by simp [gm06Alg511Rows]) hd)
  have hRefR : x.reflected.rotations = x.rotations.map (gm06Alg511ReflectedTableRow false m k) := rfl
  have hRefF : x.reflected.regionBoundaries =
      x.regionBoundaries.map (gm06Alg511ReflectedTableRow true m k) := rfl
  have hRefRlen : (gm06EncodeRows x.reflected.rotations).length = R := by
    rw [hRefR, gm06Alg511ReflectedTable_code_length]
  have hRefFlen : (gm06EncodeRows x.reflected.regionBoundaries).length = F := by
    rw [hRefF, gm06Alg511ReflectedTable_code_length]
  have hRefRwords : ∀ d ∈ gm06EncodeRows x.reflected.rotations, d < 2 ^ w := by
    rw [hRefR]
    exact gm06Alg511ReflectedTable_code_words false m k x.rotations haug hRotWords hrot
  have hRefFwords : ∀ d ∈ gm06EncodeRows x.reflected.regionBoundaries, d < 2 ^ w := by
    rw [hRefF]
    exact gm06Alg511ReflectedTable_code_words true m k x.regionBoundaries haug hRegWords hregion
  have hEm : x.endpoints.length < 2 ^ w := hE.trans_lt hn
  have hm : m < 2 ^ w := (Nat.div_le_self _ _).trans_lt hEm
  let s₀ := s.setReg 60 m
  have he₀ : Exec w (.assign 60 (.op .div (.len 3) (.const 2))) s s₀ 4 :=
    .assign (GraphMinor.Compute.Crossing.eval_div (GraphMinor.Compute.Crossing.eval_len h3 hEm)
      (GraphMinor.Compute.Crossing.eval_const hw) (by decide) hm)
  obtain ⟨s₁, t₁, he₁, ht₁, h4₁, ha₁⟩ := gm06Alg511SelectFieldProg_exec 1002 4 (by decide)
    (gm06Alg511Rows x) 2 (by simp [gm06Alg511Rows]) s₀ (by omega)
    (by simpa [s₀, gm06Alg511Words] using h1002) hn hwords
  change s₁.arrs 4 = gm06EncodeRows x.rotations at h4₁
  have h60₁ : s₁.regs 60 = m :=
    (he₁.regs_eq_of_not_mem_writtenRegs (r := 60) (by decide)).trans (by simp [s₀])
  have h52₁ : s₁.regs 52 = k :=
    (he₁.regs_eq_of_not_mem_writtenRegs (r := 52) (by decide)).trans (by simpa [s₀] using h52)
  obtain ⟨s₂, t₂, he₂, ht₂, hk₂, h4₂⟩ := gm06Alg511ReflectTableProg_exec false m k x.rotations s₁
    hw haug hRw hRotWords hrot h4₁ h60₁ h52₁
  have ht₂' := ht₂.trans (gm06Alg511ReflectTable_time_le x.rotations)
  change s₂.arrs 4 = gm06EncodeRows x.reflected.rotations at h4₂
  obtain ⟨s₃, t₃, he₃, ht₃, hk₃, h1220⟩ := gm06Alg511CopyRowProg_exec 4 1220 (by decide)
    (gm06EncodeRows x.reflected.rotations) s₂ (by omega) (by rw [hRefRlen]; exact hRw) hRefRwords h4₂
  have hBase₃ : s₃.arrs 1002 = gm06Alg511Words x := (hk₃.2 1002 (by decide)).trans
    ((hk₂.2 1002 (by decide)).trans ((ha₁ 1002 (by decide)).trans (by simpa [s₀] using h1002)))
  have h60₃ : s₃.regs 60 = m := (hk₃.1 60 (by decide)).trans ((hk₂.1 60 (by decide)).trans h60₁)
  have h52₃ : s₃.regs 52 = k := (hk₃.1 52 (by decide)).trans ((hk₂.1 52 (by decide)).trans h52₁)
  obtain ⟨s₄, t₄, he₄, ht₄, h4₄, ha₄⟩ := gm06Alg511SelectFieldProg_exec 1002 4 (by decide)
    (gm06Alg511Rows x) 3 (by simp [gm06Alg511Rows]) s₃ (by omega) hBase₃ hn hwords
  change s₄.arrs 4 = gm06EncodeRows x.regionBoundaries at h4₄
  have h60₄ : s₄.regs 60 = m := (he₄.regs_eq_of_not_mem_writtenRegs (r := 60) (by decide)).trans h60₃
  have h52₄ : s₄.regs 52 = k := (he₄.regs_eq_of_not_mem_writtenRegs (r := 52) (by decide)).trans h52₃
  obtain ⟨s₅, t₅, he₅, ht₅, hk₅, h4₅⟩ := gm06Alg511ReflectTableProg_exec true m k x.regionBoundaries s₄
    hw haug hFw hRegWords hregion h4₄ h60₄ h52₄
  have ht₅' := ht₅.trans (gm06Alg511ReflectTable_time_le x.regionBoundaries)
  change s₅.arrs 4 = gm06EncodeRows x.reflected.regionBoundaries at h4₅
  obtain ⟨s₆, t₆, he₆, ht₆, hk₆, h1221⟩ := gm06Alg511CopyRowProg_exec 4 1221 (by decide)
    (gm06EncodeRows x.reflected.regionBoundaries) s₅ (by omega) (by rw [hRefFlen]; exact hFw) hRefFwords h4₅
  let total := 4 + (t₁ + (t₂ + (t₃ + (t₄ + (t₅ + t₆)))))
  have he : Exec w gm06Alg511ReflectGeometryTablesProg s s₆ total :=
    .seq he₀ (.seq he₁ (.seq he₂ (.seq he₃ (.seq he₄ (.seq he₅ he₆)))))
  refine ⟨s₆, total, he, ?_, ?_, ?_, ?_, h1221⟩
  · apply geometry_time_le B R F t₁ t₂ t₃ t₄ t₅ t₆ hR hF
    · simpa [gm06Alg511Rows, R] using ht₁
    · exact ht₂'
    · simpa only [hRefRlen] using ht₃
    · simpa [gm06Alg511Rows, F] using ht₄
    · exact ht₅'
    · simpa only [hRefFlen] using ht₆
  · constructor
    · intro r hr
      apply he.regs_eq_of_not_mem_writtenRegs
      have hs : gm06Alg511ReflectGeometryTablesProg.writtenRegs ⊆
          ([60, 31, 7, 8, 9, 11, 20, 23, 24, 323, 324, 313, 98, 1400, 1401] : List Reg).toFinset := by decide
      exact fun h => hr (List.mem_toFinset.mp (hs h))
    · intro a ha
      apply he.arrs_eq_of_not_mem_writtenArrs
      have hs : gm06Alg511ReflectGeometryTablesProg.writtenArrs ⊆
          ([4, 25, 26, 27, 28, 1220, 1221] : List Arr).toFinset := by decide
      exact fun h => ha (List.mem_toFinset.mp (hs h))
  · exact (hk₆.1 60 (by decide)).trans ((hk₅.1 60 (by decide)).trans h60₄)
  · rw [hk₆.2 1220 (by decide), hk₅.2 1220 (by decide), ha₄ 1220 (by decide)]
    exact h1220

end GraphMinor.Compute
