module

public import GraphMinor.Compute.GM06SpliceRotations
public import GraphMinor.Compute.GM06Alg34FilterMapArray
public import GraphMinor.Compute.TwoPathsNorm
import GraphMinor.Compute.CrossingOpsReplLists

/-!
# Pruning inactive directed ends from one rotation row

After the deletion masks of VI (5.7), page 133, extend the ordinary
edge mask by ones for the two auxiliary cuffs. An ordinary directed
word is kept precisely when its edge's activity word is one. The
auxiliary words are consequently always kept.

The RAM filter emits the retained words in their old order and
copies just the occupied prefix to the replacement-row array. It
computes the exact list filter in linear time and preserves the
source row, activity array and all ordinary instance fields.
-/

public section
namespace GraphMinor.Compute
open TwoPaths GraphMinor.Compute.Crossing

/-- Add the two fixed cuff families to the current ordinary mask. -/
@[expose] def gm06AugmentedActivity (mask : List ℕ) (k : ℕ) : List ℕ :=
  mask ++ List.replicate (2 * k) 1

/-- The ordinary mask prefix is followed by always-active cuff edges. -/
@[expose] def gm06AugmentedActivityProg : Cmd :=
  .seq (.alloc 30 (.op .add (.len 12) (.op .mul (.const 2) (.len 6))))
    (.seq (gm06RotationSliceProg 12 30 (.len 12) (.const 0) (.const 0))
      (fillModelPart72Prog 313 (.op .mul (.const 2) (.len 6)) (.len 12) (.const 1) 30))

/-- Building the augmented activity array keeps the original mask
and cuff row, and assigns one to every auxiliary edge. -/
theorem gm06AugmentedActivityProg_exec {w : ℕ} (mask cuff : List ℕ) (s : State)
    (hw : 2 < 2 ^ w) (hlen : mask.length + 2 * cuff.length < 2 ^ w)
    (hbits : ∀ x ∈ mask, x ≤ 1) (h12 : s.arrs 12 = mask) (h6 : s.arrs 6 = cuff) :
    ∃ s' t, Exec w gm06AugmentedActivityProg s s' t ∧
      t ≤ 17 + 16 * mask.length + 30 * cuff.length ∧
      Keeps [313] [30] s s' ∧ s'.arrs 30 = gm06AugmentedActivity mask cuff.length := by
  let cap := mask.length + 2 * cuff.length
  have hm : mask.length < 2 ^ w := by omega
  have hk : cuff.length < 2 ^ w := by omega
  have hkw : 2 * cuff.length < 2 ^ w := by omega
  have hw1 : 1 < 2 ^ w := by omega
  have hwords : ∀ x ∈ mask, x < 2 ^ w := fun x hx => (hbits x hx).trans_lt hw1
  let s₀ := s.setArr 30 (List.replicate cap 0)
  have he₀ : Exec w (.alloc 30 (.op .add (.len 12) (.op .mul (.const 2) (.len 6))))
      s s₀ (5 + cap) := by
    exact .alloc (eval_add (eval_len h12 hm)
      (eval_mul (eval_const hw) (eval_len h6 hk) hkw) hlen)
  have hk₀ : Keeps [313] [30] s s₀ := (Keeps.refl _ _ s).setArr (by simp) _
  obtain ⟨s₁, t₁, he₁, ht₁, hk₁, hout₁⟩ := gm06RotationSliceProg_exec
    12 30 (by decide) (.len 12) (.const 0) (.const 0) mask [] 0 mask.length cap s₀
    hw1 hm (by omega) hwords (by dsimp only [cap]; omega) (by simpa only [List.length_nil, Nat.zero_add] using hlen)
    (by simpa [s₀] using h12) (by simp [s₀])
    (fun st h => eval_len ((h.2 12 (by decide)).trans (by simpa [s₀] using h12)) hm)
    (fun _ _ => eval_const (Nat.two_pow_pos w))
    (fun _ _ => eval_const (Nat.two_pow_pos w))
  have hbuf : s₁.arrs 30 = mask ++ List.replicate (2 * cuff.length) 0 := by
    simpa only [List.nil_append, List.drop_zero, List.take_length, cap, Nat.add_sub_cancel_left] using hout₁
  have hframe₁ : Keeps [313] [30] s s₁ := hk₀.trans hk₁ (by simp) (by simp)
  obtain ⟨s₂, t₂, he₂, ht₂, hk₂, hout₂, _⟩ := fillModelPart72Prog_exec 313
    (.op .mul (.const 2) (.len 6)) (.len 12) (.const 1) 30
    (List.replicate (2 * cuff.length) 1) mask (2 * cuff.length) s₁ hw1 (by simp) hlen
    (fun st h => by
      simpa only [List.length_replicate] using eval_mul (eval_const hw)
        (eval_len ((h.2 6 (by decide)).trans ((hframe₁.2 6 (by decide)).trans h6)) hk) hkw)
    (fun st h => eval_len ((h.2 12 (by decide)).trans ((hframe₁.2 12 (by decide)).trans h12)) hm)
    (fun st i hi _ _ => by simpa only [List.getElem_replicate] using eval_const (s := st) hw1)
    hbuf
  refine ⟨s₂, (5 + cap) + (t₁ + t₂), .seq he₀ (.seq he₁ he₂), ?_,
    hframe₁.trans hk₂ (by simp) (by simp), ?_⟩
  · simp only [Expr.cost, List.length_replicate, Nat.reduceAdd] at ht₁ ht₂
    dsimp only [cap]
    omega
  · simpa only [List.length_replicate, Nat.sub_self, List.replicate_zero, List.append_nil,
      gm06AugmentedActivity] using hout₂

/-- Both directed words of an edge use that edge's activity bit. -/
@[expose] def gm06KeepActiveDart (activity : List ℕ) (d : ℕ) : Bool :=
  activity[d / 2]?.getD 0 == 1

/-- The two cuff blocks do not change the original ordinary index space. -/
theorem gm06AugmentedActivity_length (mask : List ℕ) (k : ℕ) :
    (gm06AugmentedActivity mask k).length = mask.length + 2 * k := by
  simp only [gm06AugmentedActivity, List.length_append, List.length_replicate]

/-- The extended mask remains a bit list. -/
theorem gm06AugmentedActivity_bits (mask : List ℕ) (k : ℕ)
    (hbits : ∀ x ∈ mask, x ≤ 1) : ∀ x ∈ gm06AugmentedActivity mask k, x ≤ 1 := by
  intro x hx
  rcases List.mem_append.mp hx with hx | hx
  · exact hbits x hx
  · exact le_of_eq (List.eq_of_mem_replicate hx)

/-- Dividing either directed code by two gives the same edge index. -/
theorem gm06KeepActiveDart_code (activity : List ℕ) (j : ℕ) (b : Bool) :
    gm06KeepActiveDart activity (2 * j + b.toNat) = (activity[j]?.getD 0 == 1) := by
  have he : (2 * j + b.toNat) / 2 = j := by
    have hb : b.toNat < 2 := by cases b <;> decide
    omega
  simp only [gm06KeepActiveDart, he]

/-- Ordinary words are kept precisely by their supplied ordinary bit. -/
theorem gm06KeepActiveDart_ordinary (mask : List ℕ) (k : ℕ) (j : Fin mask.length) (b : Bool) :
    gm06KeepActiveDart (gm06AugmentedActivity mask k) (2 * j.val + b.toNat) = true ↔ mask[j] = 1 := by
  rw [gm06KeepActiveDart_code]
  simp only [gm06AugmentedActivity, List.getElem?_append_left j.isLt,
    List.getElem?_eq_getElem j.isLt, Option.getD_some, beq_iff_eq, Fin.getElem_fin]

/-- Every directed end of either fixed cuff family remains present. -/
theorem gm06KeepActiveDart_cuff (mask : List ℕ) (k j : ℕ) (b : Bool)
    (hj : j < 2 * k) :
    gm06KeepActiveDart (gm06AugmentedActivity mask k) (2 * (mask.length + j) + b.toNat) = true := by
  rw [gm06KeepActiveDart_code]
  simp only [gm06AugmentedActivity, List.getElem?_append_right (by omega : mask.length ≤ mask.length + j),
    Nat.add_sub_cancel_left, List.getElem?_replicate, ite_eq_left hj, Option.getD_some, beq_self_eq_true]

/-- Filter row 25 into replacement row 27, using augmented activity
array 30. Arrays 27 and 29 are local work buffers. -/
@[expose] def gm06PruneRotationRowProg : Cmd :=
  .seq (.alloc 27 (.len 25))
    (.seq (.assign 334 (.const 0))
      (.seq (gm06FilterMapArrayProg 25 27 331 332 333 334
        (.read 30 (.op .div (.reg 333) (.const 2))) (.reg 333))
        (.seq (readSliceProg 27 (.const 0) 29 (.reg 334) 335) (copyProg 27 29))))

private theorem filter_flatMap (p : ℕ → Bool) (xs : List ℕ) :
    xs.flatMap (fun x => if p x then [x] else []) = xs.filter p := by
  induction xs with
  | nil => rfl
  | cons x xs ih => cases h : p x <;> simp [h, ih]

/-- The concrete row filter produces exactly the retained list in
its old order, with a linear bound and an explicit scratch frame. -/
theorem gm06PruneRotationRowProg_exec {w : ℕ} (activity row : List ℕ) (s : State)
    (hw : 2 < 2 ^ w) (hlen : row.length + 2 < 2 ^ w)
    (haLen : activity.length < 2 ^ w) (hbits : ∀ x ∈ activity, x ≤ 1)
    (hd : ∀ d ∈ row, d < 2 * activity.length)
    (hwords : ∀ d ∈ row, d < 2 ^ w) (h25 : s.arrs 25 = row) (h30 : s.arrs 30 = activity) :
    ∃ s' t, Exec w gm06PruneRotationRowProg s s' t ∧
      t ≤ 50 + 60 * row.length ∧
      Keeps [331, 332, 333, 334, 335, 336, 337, 98] [27, 29] s s' ∧
      s'.arrs 27 = row.filter (gm06KeepActiveDart activity) := by
  let keep := gm06KeepActiveDart activity
  let out := row.filter keep
  have hw1 : 1 < 2 ^ w := by omega
  have hrowLen : row.length < 2 ^ w := by omega
  have houtLen : out.length ≤ row.length := List.length_filter_le _ _
  have houtWords : ∀ x ∈ out, x < 2 ^ w := fun x hx => hwords x (List.mem_filter.mp hx).1
  let s₀ := s.setArr 27 (List.replicate row.length 0)
  let s₁ := s₀.setReg 334 0
  have he₀ : Exec w (.alloc 27 (.len 25)) s s₀ (1 + row.length) := .alloc (eval_len h25 hrowLen)
  have he₁ : Exec w (.assign 334 (.const 0)) s₀ s₁ 2 := .assign (eval_const (Nat.two_pow_pos w))
  have hbuf : IsBuf 27 334 [] row.length s₁ := ⟨by simp [s₁, s₀], by simp [s₁]⟩
  have hmask₁ : s₁.arrs 30 = activity := by simpa [s₁, s₀] using h30
  have hsrc₁ : s₁.arrs 25 = row := by simpa [s₁, s₀] using h25
  obtain ⟨s₂, t₂, he₂, ht₂, hbuf₂, harr₂, hregs₂⟩ := gm06FilterMapArrayProg_exec
    25 27 331 332 333 334 (.read 30 (.op .div (.reg 333) (.const 2))) (.reg 333)
    keep id (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    hw1 hsrc₁ hrowLen hwords hbuf
    (by simp only [id_eq, filter_flatMap]; exact houtLen) (by simpa only [List.length_nil, Nat.zero_add] using hlen)
    (fun st y hy ha _ hry => by
      have hj : y / 2 < activity.length := by have hh := hd y hy; omega
      have hmask : st.arrs 30 = activity := (ha 30 (by decide)).trans hmask₁
      have hv : activity[y / 2] ≤ 1 := hbits _ (List.getElem_mem hj)
      have hvw : activity[y / 2] < 2 ^ w := hv.trans_lt hw1
      have hread := eval_read (a := 30)
        (eval_div (eval_reg hry (hwords y hy)) (eval_const hw) (by decide : (2 : ℕ) ≠ 0)
          (hj.trans haLen)) (by simpa only [hmask] using hj) (by simpa only [hmask] using hvw)
      have heq : activity[y / 2] = if keep y then 1 else 0 := by
        by_cases hv1 : activity[y / 2] = 1
        · simp [keep, gm06KeepActiveDart, List.getElem?_eq_getElem hj, hv1]
        · have hv0 : activity[y / 2] = 0 := by omega
          simp [keep, gm06KeepActiveDart, List.getElem?_eq_getElem hj, hv0]
      exact hread.trans (congrArg some (by simpa only [hmask] using heq)))
    (fun st y hy _ _ _ hry => eval_reg hry (hwords y hy))
  have hbuf₂' : IsBuf 27 334 out (row.length - out.length) s₂ := by
    simpa only [id_eq, filter_flatMap, List.nil_append] using hbuf₂
  obtain ⟨s₃, t₃, he₃, ht₃, hout₃, harr₃, _⟩ := readSliceProg_exec 27 29 (.const 0) 334 335
    (by decide) (by decide) [] out (List.replicate (row.length - out.length) 0) rfl rfl houtWords
    hw1 (by simpa only [List.length_nil, Nat.zero_add] using houtLen.trans_lt hrowLen)
    (eval_const (Nat.two_pow_pos w))
    (by simpa only [IsBuf, List.nil_append] using hbuf₂'.1) hbuf₂'.2
  have hk₃ : Keeps [335, 336, 337] [29] s₂ s₃ := by
    refine ⟨fun r hr => Exec.regs_eq_of_not_mem_writtenRegs he₃ ?_, fun a ha => harr₃ a (by simpa using ha)⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    simp [readSliceProg, readSliceBody, forUp, Cmd.writtenRegs]
    exact ⟨hr.2.2, hr.1, hr.2.1⟩
  obtain ⟨s₄, t₄, he₄, ht₄, hk₄, hout₄⟩ := copyProg_exec (dst := 27) (src := 29)
    (by decide) out s₃ hw1 (by omega) houtWords hout₃
  let R := [331, 332, 333, 334, 335, 336, 337, 98]
  let A := [27, 29]
  have hk₀ : Keeps R A s s₁ :=
    ((Keeps.refl _ _ s).setArr (by simp [A]) _).setReg (by simp [R]) _
  have hk₂ : Keeps [331, 332, 333, 334] [27] s₁ s₂ := by
    refine ⟨fun r hr => ?_, fun a ha => harr₂ a (by simpa using ha)⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
    exact hregs₂ r hr.1 hr.2.1 hr.2.2.1 hr.2.2.2
  refine ⟨s₄, (1 + row.length) + (2 + (t₂ + (t₃ + t₄))),
    .seq he₀ (.seq he₁ (.seq he₂ (.seq he₃ he₄))), ?_,
    ((hk₀.trans hk₂ (by simp [R]) (by simp [A])).trans hk₃
      (by simp [R]) (by simp [A])).trans hk₄ (by simp [R, rI3]) (by simp [A]), hout₄⟩
  simp only [Expr.cost, Nat.reduceAdd] at ht₂ ht₃
  change t₄ ≤ 6 + 12 * out.length at ht₄
  omega

end GraphMinor.Compute
