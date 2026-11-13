module

public import GraphMinor.Compute.BitSet
public import GraphMinor.Compute.Logic
import Mathlib.Data.List.GetD

/-!
# Reading perimeter bits through the compass inverse list

The original perimeter bitset uses original vertex labels. The inverse list
maps compact labels to those labels. A scan gathers the corresponding bits
into array 20, so the interior-member test compares sets on the same vertex
type. This implements the perimeter test in XIII (9.9), step 6, p. 105.
-/

@[expose] public section

namespace GraphMinor.Compute

/-- Pull a set back to compact labels through an explicitly given map. -/
def case3PullbackBits {m n : ℕ} (e : Fin m → Fin n) (P : Finset (Fin n)) : Finset (Fin m) :=
  Finset.univ.filter (fun i => e i ∈ P)

/-- Gather original perimeter bits through the inverse vertex list. -/
def case3GatherBitsProg : Cmd :=
  .seq (.alloc 20 (.reg 14))
    (.seq (.assign 96 (.const 0))
      (forUp 96 (.reg 14) (.write 20 (.reg 96) (.read 45 (.read 32 (.reg 96))))))

private theorem gatherLoop_exec {w m n : ℕ} (e : Fin m → Fin n) (P : Finset (Fin n))
    (hw : 1 < 2 ^ w) (hm : m + 1 < 2 ^ w) (hn : n < 2 ^ w)
    (rem k : ℕ) (hrem : k + rem = m) {s : State}
    (hP : IsBitSet P 45 s) (hlistlen : m ≤ (s.arrs 32).length)
    (hlist : ∀ i : Fin m, (s.arrs 32).getD i.1 0 = (e i).1)
    (hrn : s.regs 14 = m) (hri : s.regs 96 = k)
    (hlen : (s.arrs 20).length = m)
    (hbits : ∀ i : Fin m, (s.arrs 20).getD i.1 0 =
      if i.1 < k then (if e i ∈ P then 1 else 0) else 0) :
    ∃ s' t, Exec w (forUp 96 (.reg 14)
        (.write 20 (.reg 96) (.read 45 (.read 32 (.reg 96))))) s s' t ∧
      t ≤ 3 + 12 * rem ∧ s'.arrs 20 = bitSetList (case3PullbackBits e P) := by
  have h0 : 0 < 2 ^ w := by omega
  have hmw : m < 2 ^ w := by omega
  induction rem generalizing k s with
  | zero =>
    have hk : k = m := by omega
    have hc : (Expr.op .lt (.reg 96) (.reg 14)).eval w s = some 0 := by
      simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hri, hrn, hk, hmw, h0]
    refine ⟨s, 3, .while_false hc, by omega, ?_⟩
    apply List.ext_getElem (by rw [hlen, length_bitSetList])
    intro j hj hj'
    have hjm : j < m := by rw [← hlen]; exact hj
    have hb := hbits ⟨j, hjm⟩
    rw [List.getD_eq_getElem _ 0 hj] at hb
    rw [getElem_bitSetList _ j hjm]
    simpa only [hk, hjm, ↓reduceIte, case3PullbackBits, Finset.mem_filter,
      Finset.mem_univ, true_and] using hb
  | succ rem ih =>
    have hk : k < m := by omega
    have hkw : k < 2 ^ w := by omega
    have hkpw : k + 1 < 2 ^ w := by omega
    let i : Fin m := ⟨k, hk⟩
    have hil : k < (s.arrs 32).length := lt_of_lt_of_le hk hlistlen
    have hew : (e i).1 < 2 ^ w := (e i).2.trans hn
    have hiel : (e i).1 < (s.arrs 45).length := by rw [hP.1]; exact (e i).2
    have hlabel : (s.arrs 32)[k] = (e i).1 := by
      have hh := hlist i
      change (s.arrs 32).getD k 0 = (e i).1 at hh
      rwa [List.getD_eq_getElem _ 0 hil] at hh
    have hbit := hP.getElem_eq_ite (e i)
    have hread : (Expr.read 45 (.read 32 (.reg 96))).eval w s =
        some (if e i ∈ P then 1 else 0) := by
      by_cases hp : e i ∈ P <;>
        simp [Expr.eval, checkWord, hri, hkw, hil, hlabel, hew, hiel, hbit, hp, hw, h0]
    have hc : (Expr.op .lt (.reg 96) (.reg 14)).eval w s = some 1 := by
      simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hri, hrn, hk, hkw, hmw, hw]
    let sB := s.writeArr 20 k (if e i ∈ P then 1 else 0)
    let sC := sB.setReg 96 (k + 1)
    have hexB : Exec w (.write 20 (.reg 96) (.read 45 (.read 32 (.reg 96)))) s sB 5 :=
      .write (by simp only [Expr.eval, checkWord, hri, hkw, ↓reduceIte]) hread (by rw [hlen]; exact hk)
    have hexC : Exec w (.assign 96 (.op .add (.reg 96) (.const 1))) sB sC 4 :=
      .assign (by simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, sB, hri, hkw, hw, hkpw])
    have harrC : ∀ a, a ≠ 20 → sC.arrs a = s.arrs a := by
      intro a ha
      simp only [sC, sB, State.setReg_arrs, State.writeArr_arrs_ne _ _ _ ha]
    have hlenC : (sC.arrs 20).length = m := by
      simp only [sC, sB, State.setReg_arrs, State.writeArr_arrs_self, List.length_set, hlen]
    have hbitsC : ∀ j : Fin m, (sC.arrs 20).getD j.1 0 =
        if j.1 < k + 1 then (if e j ∈ P then 1 else 0) else 0 := by
      intro j
      have hj : j.1 < (s.arrs 20).length := by rw [hlen]; exact j.2
      simp only [sC, sB, State.setReg_arrs, State.writeArr_arrs_self]
      rw [List.getD_eq_getElem _ 0 (by rw [List.length_set]; exact hj), List.getElem_set]
      by_cases hkj : k = j.1
      · have hij : i = j := Fin.ext hkj
        simp only [hkj, hij, ↓reduceIte, Nat.lt_add_one]
      · simp only [hkj, ↓reduceIte]
        have hb := hbits j
        rw [List.getD_eq_getElem _ 0 hj] at hb
        rw [hb]
        have htest : j.1 < k + 1 ↔ j.1 < k := by omega
        simp only [htest]
    obtain ⟨s', t, hex, ht, hdst⟩ := ih (k + 1) (by omega) (s := sC)
      (hP.of_arr_eq (harrC 45 (by decide)))
      (by rw [harrC 32 (by decide)]; exact hlistlen)
      (by intro j; rw [harrC 32 (by decide)]; exact hlist j)
      (by simp only [sC, sB, State.setReg_regs_ne _ _ (show (14 : ℕ) ≠ 96 by decide), State.writeArr_regs, hrn])
      (State.setReg_regs_self ..) hlenC hbitsC
    exact ⟨s', 3 + (5 + 4) + t, .while_true hc (by decide) (.seq hexB hexC) hex, by omega, hdst⟩

/-- Gathering a perimeter bitset costs at most `13 m + 6` steps and changes
only array 20 and register 96. The source labels and bitset are retained. -/
theorem case3GatherBitsProg_exec {w m n : ℕ} (e : Fin m → Fin n) (P : Finset (Fin n))
    (hw : 1 < 2 ^ w) (hm : m + 1 < 2 ^ w) (hn : n < 2 ^ w)
    {s : State} (hP : IsBitSet P 45 s) (hlistlen : m ≤ (s.arrs 32).length)
    (hlist : ∀ i : Fin m, (s.arrs 32).getD i.1 0 = (e i).1) (hrn : s.regs 14 = m) :
    ∃ s' t, Exec w case3GatherBitsProg s s' t ∧ t ≤ 13 * m + 6 ∧
      IsBitSet (case3PullbackBits e P) 20 s' ∧
      (∀ a, a ≠ 20 → s'.arrs a = s.arrs a) ∧
      (∀ r, r ≠ 96 → s'.regs r = s.regs r) := by
  have hmw : m < 2 ^ w := by omega
  have h0 : 0 < 2 ^ w := by omega
  let s₁ := s.setArr 20 (List.replicate m 0)
  let s₂ := s₁.setReg 96 0
  have hex₁ : Exec w (.alloc 20 (.reg 14)) s s₁ (1 + m) :=
    .alloc (by simp only [Expr.eval, checkWord, hrn, hmw, ↓reduceIte])
  have hex₂ : Exec w (.assign 96 (.const 0)) s₁ s₂ 2 :=
    .assign (by simp only [Expr.eval, checkWord, h0, ↓reduceIte])
  have harr₂ : ∀ a, a ≠ 20 → s₂.arrs a = s.arrs a := by
    intro a ha
    simp only [s₂, s₁, State.setReg_arrs, State.setArr_arrs_ne _ _ ha]
  obtain ⟨s₃, t₃, hex₃, ht₃, hdst₃⟩ := gatherLoop_exec e P hw hm hn m 0 (by omega) (s := s₂)
    (hP.of_arr_eq (harr₂ 45 (by decide)))
    (by rw [harr₂ 32 (by decide)]; exact hlistlen)
    (by intro i; rw [harr₂ 32 (by decide)]; exact hlist i)
    (by simp only [s₂, s₁, State.setReg_regs_ne _ _ (show (14 : ℕ) ≠ 96 by decide), State.setArr_regs, hrn])
    (State.setReg_regs_self ..)
    (by simp only [s₂, s₁, State.setReg_arrs, State.setArr_arrs_self, List.length_replicate])
    (fun i => by simp only [s₂, s₁, State.setReg_arrs, State.setArr_arrs_self,
      Nat.not_lt_zero, ↓reduceIte, List.getD_replicate 0 i.2])
  have hex : Exec w case3GatherBitsProg s s₃ (1 + m + (2 + t₃)) := .seq hex₁ (.seq hex₂ hex₃)
  refine ⟨s₃, 1 + m + (2 + t₃), hex, by omega, IsBitSet.of_bitSetList _ _ _ hdst₃, ?_, ?_⟩
  · intro a ha
    exact hex.arrs_eq_of_not_mem_writtenArrs (by simp [case3GatherBitsProg, forUp, Cmd.writtenArrs, ha])
  · intro r hr
    exact hex.regs_eq_of_not_mem_writtenRegs (by simp [case3GatherBitsProg, forUp, Cmd.writtenRegs, hr])

end GraphMinor.Compute
