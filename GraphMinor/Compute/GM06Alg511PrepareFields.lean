module

public import GraphMinor.Compute.GM06Alg511ReflectTable
public import GraphMinor.Compute.GM06Alg511SelectField
public import GraphMinor.Compute.GM06Alg511CopyRow
public import GraphMinor.Compute.GM06Alg511ReflectedInput
public import GraphMinor.Compute.GM06Alg511PackSuccessor
import GraphMinor.Compute.CrossingOpsReplLists
import Mathlib.Tactic

/-!
# Preparing only the drawing fields read by the successor procedure

The input to VI (5.7) uses the ordinary edge ends and rotations
with both cuffs. It reads no region rows. After the orientation
choice in (5.11), page 134, load the vertex count, ordinary ends
and rotation table from the retained original drawing words.
Reverse and relabel the rotation rows exactly when flag 57 is set.
Store the three fields apart from the callee's working drawing.
The existing oriented cuff arrays and computed path rows survive.
-/

@[expose] public section
namespace GraphMinor.Compute
open TwoPaths

/-- Load only the vertex, edge and rotation fields. The oriented
cuffs and current paths already occupy arrays 1210, 1211 and 8. -/
def gm06Alg511PrepareSuccessorFieldsProg : Cmd :=
  .seq (gm06Alg511SelectFieldProg 1002 1500 0)
    (.seq (gm06Alg511SelectFieldProg 1002 1230 1)
      (.seq (gm06Alg511SelectFieldProg 1002 4 2)
        (.seq (.assign 60 (.op .div (.len 1230) (.const 2)))
          (.seq (.ite (.reg 57) (gm06Alg511ReflectTableProg false) .skip)
            (gm06Alg511CopyRowProg 4 1231)))))

private theorem prepare_frame {w : ℕ} {s t : State} {u : ℕ}
    (he : Exec w gm06Alg511PrepareSuccessorFieldsProg s t u) :
    Keeps [31, 7, 8, 9, 11, 323, 324, 313, 98, 60, 1400, 1401, 20, 23, 24]
      [1500, 1230, 4, 25, 26, 27, 28, 1231] s t := by
  have hr : gm06Alg511PrepareSuccessorFieldsProg.writtenRegs ⊆
      ([31, 7, 8, 9, 11, 323, 324, 313, 98, 60, 1400, 1401, 20, 23, 24] : List ℕ).toFinset := by decide
  have ha : gm06Alg511PrepareSuccessorFieldsProg.writtenArrs ⊆
      ([1500, 1230, 4, 25, 26, 27, 28, 1231] : List ℕ).toFinset := by decide
  constructor
  · intro r hn
    exact he.regs_eq_of_not_mem_writtenRegs (fun hm => hn (List.mem_toFinset.mp (hr hm)))
  · intro a hn
    exact he.arrs_eq_of_not_mem_writtenArrs (fun hm => hn (List.mem_toFinset.mp (ha hm)))

private theorem selected_rotations_exec {w m k : ℕ} (rows : List (List ℕ))
    (flip : Bool) (s : State) (hw : 2 < 2 ^ w)
    (haug : 2 * (m + k + k) < 2 ^ w)
    (hcode : (gm06EncodeRows rows).length < 2 ^ w)
    (hwords : ∀ d ∈ gm06EncodeRows rows, d < 2 ^ w)
    (hdarts : ∀ row ∈ rows, ∀ d ∈ row, d < 2 * (m + k + k))
    (h4 : s.arrs 4 = gm06EncodeRows rows) (h60 : s.regs 60 = m) (h52 : s.regs 52 = k)
    (h57 : s.regs 57 = if flip then 1 else 0) :
    ∃ t u, Exec w (.ite (.reg 57) (gm06Alg511ReflectTableProg false) .skip) s t u ∧
      u ≤ 1 + 1000 * ((gm06EncodeRows rows).length + 1) ^ 2 ∧
      Keeps [1400, 1401, 31, 7, 8, 9, 11, 20, 23, 24, 323, 324, 313, 98]
        [4, 25, 26, 27, 28] s t ∧
      t.arrs 4 = gm06EncodeRows (if flip then rows.map (gm06Alg511ReflectedTableRow false m k) else rows) := by
  cases flip with
  | false =>
    refine ⟨s, 2, .ite_false (Crossing.eval_reg h57 (Nat.two_pow_pos _)) (.skip s),
      ?_, Keeps.refl _ _ s, h4⟩
    have hh : 1 ≤ ((gm06EncodeRows rows).length + 1) ^ 2 := by
      exact Nat.one_le_pow _ _ (by omega)
    omega
  | true =>
    obtain ⟨t, u, he, ht, hk, hrows⟩ := gm06Alg511ReflectTableProg_exec false m k rows s hw
      haug hcode hwords hdarts h4 h60 h52
    refine ⟨t, 1 + u, .ite_true (Crossing.eval_reg (by simpa only [ite_true] using h57) (show 1 < 2 ^ w by omega)) (by decide) he,
      ?_, hk, hrows⟩
    exact Nat.add_le_add_left (ht.trans (gm06Alg511ReflectTable_time_le rows)) 1

private theorem preparation_time_le (B R E a b c d e : ℕ)
    (hR : R ≤ B) (hE : E ≤ B)
    (ha : a ≤ 40) (hb : b ≤ 35 + 22 * E) (hc : c ≤ 52 + 22 * R)
    (hd : d ≤ 1 + 1000 * (R + 1) ^ 2) (he : e ≤ 6 + 12 * R) :
    a + (b + (c + (4 + (d + e)))) ≤ 2000 * (B + 1) ^ 2 := by
  have hp : (R + 1) ^ 2 ≤ (B + 1) ^ 2 := Nat.pow_le_pow_left (by omega) 2
  have hd' := hd.trans (Nat.add_le_add_left (Nat.mul_le_mul_left 1000 hp) 1)
  have hB : B + 1 ≤ (B + 1) ^ 2 := Nat.le_self_pow (by decide) (B + 1)
  nlinarith only [ha, hb, hc, hd', he, hR, hE, hB]

/-- The selected orientation's successor fields are computed from
the original supplied drawing words. No region field is loaded.
The bound is quadratic, and all current paths, oriented cuffs and
winding/target registers remain unchanged. -/
theorem gm06Alg511PrepareSuccessorFieldsProg_exec {w : ℕ}
    (x : GM06Alg511Input) (flip : Bool) (s : State) (hw : 2 < 2 ^ w)
    (hn : (gm06Alg511Words x).length < 2 ^ w)
    (hwords : ∀ d ∈ gm06Alg511Words x, d < 2 ^ w)
    (haug : 2 * (x.endpoints.length / 2 + x.pathCount + x.pathCount) < 2 ^ w)
    (hdarts : ∀ row ∈ x.rotations, ∀ d ∈ row,
      d < 2 * (x.endpoints.length / 2 + x.pathCount + x.pathCount))
    (hbase : s.arrs 1002 = gm06Alg511Words x) (hK : s.regs 52 = x.pathCount)
    (hflip : s.regs 57 = if flip then 1 else 0) :
    ∃ t u, Exec w gm06Alg511PrepareSuccessorFieldsProg s t u ∧
      u ≤ 2000 * ((gm06Alg511Words x).length + 1) ^ 2 ∧
      Keeps [31, 7, 8, 9, 11, 323, 324, 313, 98, 60, 1400, 1401, 20, 23, 24]
        [1500, 1230, 4, 25, 26, 27, 28, 1231] s t ∧
      t.arrs 1500 = [(if flip then x.reflected else x).vertexCount] ∧
      t.arrs 1230 = (if flip then x.reflected else x).endpoints ∧
      t.arrs 1231 = gm06EncodeRows (if flip then x.reflected else x).rotations := by
  let B := (gm06Alg511Words x).length
  let R := (gm06EncodeRows x.rotations).length
  let m := x.endpoints.length / 2
  let k := x.pathCount
  have hE : x.endpoints.length ≤ B := gm06Alg511_encoded_row_length_le (by simp [gm06Alg511Rows])
  have hR : R ≤ B := gm06Alg511_encoded_row_length_le (by simp [gm06Alg511Rows])
  have hRw : R < 2 ^ w := hR.trans_lt hn
  have hRotWords : ∀ d ∈ gm06EncodeRows x.rotations, d < 2 ^ w :=
    fun d hd => hwords d (gm06Alg511_mem_encoded_row (by simp [gm06Alg511Rows]) hd)
  have hRefR : x.reflected.rotations = x.rotations.map (gm06Alg511ReflectedTableRow false m k) := rfl
  have hRefLen : (gm06EncodeRows x.reflected.rotations).length = R := by
    rw [hRefR, gm06Alg511ReflectedTable_code_length]
  have hRefWords : ∀ d ∈ gm06EncodeRows x.reflected.rotations, d < 2 ^ w := by
    rw [hRefR]
    exact gm06Alg511ReflectedTable_code_words false m k x.rotations haug hRotWords hdarts
  obtain ⟨s₁, u₁, he₁, ht₁, hV₁, ha₁⟩ := gm06Alg511SelectFieldProg_exec 1002 1500 (by decide)
    (gm06Alg511Rows x) 0 (by simp [gm06Alg511Rows]) s (by omega) hbase hn hwords
  obtain ⟨s₂, u₂, he₂, ht₂, hE₂, ha₂⟩ := gm06Alg511SelectFieldProg_exec 1002 1230 (by decide)
    (gm06Alg511Rows x) 1 (by simp [gm06Alg511Rows]) s₁ (by omega)
    ((ha₁ 1002 (by decide)).trans hbase) hn hwords
  obtain ⟨s₃, u₃, he₃, ht₃, hR₃, ha₃⟩ := gm06Alg511SelectFieldProg_exec 1002 4 (by decide)
    (gm06Alg511Rows x) 2 (by simp [gm06Alg511Rows]) s₂ (by omega)
    ((ha₂ 1002 (by decide)).trans ((ha₁ 1002 (by decide)).trans hbase)) hn hwords
  change s₁.arrs 1500 = [x.vertexCount] at hV₁
  change s₂.arrs 1230 = x.endpoints at hE₂
  change s₃.arrs 4 = gm06EncodeRows x.rotations at hR₃
  have hE₃ : s₃.arrs 1230 = x.endpoints := (ha₃ 1230 (by decide)).trans hE₂
  have hK₃ : s₃.regs 52 = k :=
    (he₃.regs_eq_of_not_mem_writtenRegs (by decide)).trans
      ((he₂.regs_eq_of_not_mem_writtenRegs (by decide)).trans
        ((he₁.regs_eq_of_not_mem_writtenRegs (by decide)).trans hK))
  have hflip₃ : s₃.regs 57 = if flip then 1 else 0 :=
    (he₃.regs_eq_of_not_mem_writtenRegs (by decide)).trans
      ((he₂.regs_eq_of_not_mem_writtenRegs (by decide)).trans
        ((he₁.regs_eq_of_not_mem_writtenRegs (by decide)).trans hflip))
  let s₄ := s₃.setReg 60 m
  have hm : m < 2 ^ w := ((Nat.div_le_self _ _).trans hE).trans_lt hn
  have he₄ : Exec w (.assign 60 (.op .div (.len 1230) (.const 2))) s₃ s₄ 4 :=
    .assign (Crossing.eval_div (Crossing.eval_len hE₃ (hE.trans_lt hn))
      (Crossing.eval_const hw) (by decide) hm)
  obtain ⟨s₅, u₅, he₅, ht₅, hk₅, h4₅⟩ := selected_rotations_exec x.rotations flip s₄ hw haug
    hRw hRotWords hdarts hR₃ (by simp [s₄, m]) (by simpa [s₄] using hK₃)
      (by simpa [s₄] using hflip₃)
  have hsel : s₅.arrs 4 = gm06EncodeRows (if flip then x.reflected else x).rotations := by
    cases flip <;> simpa only [Bool.false_eq_true, ite_false, ite_true, hRefR] using h4₅
  have hselectedLen : (gm06EncodeRows (if flip then x.reflected else x).rotations).length < 2 ^ w := by
    cases flip <;> simpa only [Bool.false_eq_true, ite_false, ite_true, hRefLen] using hRw
  have hselectedWords : ∀ d ∈ gm06EncodeRows (if flip then x.reflected else x).rotations, d < 2 ^ w := by
    cases flip
    · exact hRotWords
    · exact hRefWords
  obtain ⟨s₆, u₆, he₆, ht₆, hk₆, hR₆⟩ := gm06Alg511CopyRowProg_exec 4 1231 (by decide)
    (gm06EncodeRows (if flip then x.reflected else x).rotations) s₅ (by omega)
      hselectedLen hselectedWords hsel
  have he : Exec w gm06Alg511PrepareSuccessorFieldsProg s s₆
      (u₁ + (u₂ + (u₃ + (4 + (u₅ + u₆))))) := .seq he₁ (.seq he₂ (.seq he₃ (.seq he₄ (.seq he₅ he₆))))
  refine ⟨s₆, _, he, ?_, prepare_frame he, ?_, ?_, hR₆⟩
  · apply preparation_time_le B R x.endpoints.length u₁ u₂ u₃ u₅ u₆ hR hE
    · simpa only [gm06Alg511Rows, List.getElem_cons_zero, List.length_singleton] using ht₁
    · simpa only [gm06Alg511Rows, List.getElem_cons_succ, List.getElem_cons_zero] using ht₂
    · simpa only [gm06Alg511Rows, List.getElem_cons_succ, List.getElem_cons_zero] using ht₃
    · exact ht₅
    · cases flip <;> simpa only [Bool.false_eq_true, ite_false, ite_true, hRefLen] using ht₆
  · have hh : s₆.arrs 1500 = [x.vertexCount] := (hk₆.2 1500 (by decide)).trans
      ((hk₅.2 1500 (by decide)).trans ((ha₃ 1500 (by decide)).trans
        ((ha₂ 1500 (by decide)).trans hV₁)))
    cases flip <;> exact hh
  · have hh : s₆.arrs 1230 = x.endpoints := (hk₆.2 1230 (by decide)).trans
      ((hk₅.2 1230 (by decide)).trans hE₃)
    cases flip <;> exact hh

/-- The six actual field arrays used at each successor call. The
last field is the computed current path table in array 8. -/
def gm06Alg511SuccessorFieldSources (i : Fin 6) : ℕ :=
  ([1500, 1230, 1231, 1210, 1211, 8] : List ℕ)[i.val]'(by simp)

/-- Prepare the selected orientation's three graph fields and
pack them with its already computed cuffs and path rows. -/
def gm06Alg511PrepareSuccessorInputProg : Cmd :=
  .seq gm06Alg511PrepareSuccessorFieldsProg
    (gm06Alg511PackSuccessorProg (List.ofFn gm06Alg511SuccessorFieldSources))

private theorem field_source_ne (i : Fin 6) :
    gm06Alg511SuccessorFieldSources i ≠ 0 ∧ gm06Alg511SuccessorFieldSources i ≠ 1600 := by
  fin_cases i <;> decide

private theorem loop_register_frame {w : ℕ} {s t : State} {u : ℕ}
    (he : Exec w gm06Alg511PrepareSuccessorInputProg s t u) :
    ∀ j ∈ [54, 55, 62, 63, 52, 66, 6000], t.regs j = s.regs j := by
  intro j hj
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hj
  rcases hj with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    exact he.regs_eq_of_not_mem_writtenRegs (by decide)

/-- The complete successor input is assembled from the retained
original drawing, the computed orientation and the computed path
rows. It has the exact region-free six-field format, retains every
source field, and preserves all seven loop registers. -/
theorem gm06Alg511PrepareSuccessorInputProg_exec {w : ℕ}
    (x : GM06Alg511Input) (flip : Bool) (rows : List (List ℕ)) (s : State)
    (hw : 2 < 2 ^ w)
    (hn : (gm06Alg511Words x).length < 2 ^ w)
    (hwords : ∀ d ∈ gm06Alg511Words x, d < 2 ^ w)
    (haug : 2 * (x.endpoints.length / 2 + x.pathCount + x.pathCount) < 2 ^ w)
    (hdarts : ∀ row ∈ x.rotations, ∀ d ∈ row,
      d < 2 * (x.endpoints.length / 2 + x.pathCount + x.pathCount))
    (hcode : (gm06EncodeSuccessorInput ((if flip then x.reflected else x).withLinkage rows)).length < 2 ^ w)
    (hcodewords : ∀ d ∈ gm06EncodeSuccessorInput ((if flip then x.reflected else x).withLinkage rows), d < 2 ^ w)
    (hbase : s.arrs 1002 = gm06Alg511Words x) (hK : s.regs 52 = x.pathCount)
    (hflip : s.regs 57 = if flip then 1 else 0)
    (hinner : s.arrs 1210 = (if flip then x.reflected else x).innerCuff)
    (houter : s.arrs 1211 = (if flip then x.reflected else x).outerCuff)
    (hpaths : s.arrs 8 = gm06EncodeRows rows) :
    ∃ t u, Exec w gm06Alg511PrepareSuccessorInputProg s t u ∧
      u ≤ 2000 * ((gm06Alg511Words x).length + 1) ^ 2 + 45 +
        44 * (gm06EncodeSuccessorInput ((if flip then x.reflected else x).withLinkage rows)).length ∧
      t.arrs 0 = gm06EncodeSuccessorInput ((if flip then x.reflected else x).withLinkage rows) ∧
      t.arrs 1002 = gm06Alg511Words x ∧
      (∀ i : Fin 6, t.arrs (gm06Alg511SuccessorFieldSources i) =
        (gm06SuccessorRows ((if flip then x.reflected else x).withLinkage rows))[i.val]'(by simp [gm06SuccessorRows])) ∧
      ∀ j ∈ [54, 55, 62, 63, 52, 66, 6000], t.regs j = s.regs j := by
  obtain ⟨s₁, u₁, he₁, ht₁, hk₁, hV, hE, hR⟩ :=
    gm06Alg511PrepareSuccessorFieldsProg_exec x flip s hw hn hwords haug hdarts hbase hK hflip
  have hfields (i : Fin 6) : s₁.arrs (gm06Alg511SuccessorFieldSources i) =
      (gm06SuccessorRows ((if flip then x.reflected else x).withLinkage rows))[i.val]'(by simp [gm06SuccessorRows]) := by
    fin_cases i
    · exact hV
    · exact hE
    · exact hR
    · exact (hk₁.2 1210 (by decide)).trans hinner
    · exact (hk₁.2 1211 (by decide)).trans houter
    · exact (hk₁.2 8 (by decide)).trans hpaths
  obtain ⟨s₂, u₂, he₂, ht₂, h0, ha₂, _⟩ := gm06Alg511PackSuccessorInput_exec
    ((if flip then x.reflected else x).withLinkage rows) gm06Alg511SuccessorFieldSources
    field_source_ne s₁ (by omega) hcode hcodewords hfields
  have he : Exec w gm06Alg511PrepareSuccessorInputProg s s₂ (u₁ + u₂) := .seq he₁ he₂
  refine ⟨s₂, _, he, by omega, h0,
    (ha₂ 1002 (by decide) (by decide)).trans ((hk₁.2 1002 (by decide)).trans hbase), ?_, loop_register_frame he⟩
  intro i
  exact (ha₂ _ (field_source_ne i).1 (field_source_ne i).2).trans (hfields i)

end GraphMinor.Compute
