module

public import GraphMinor.Compute.GM06ListEncoding
public import GraphMinor.Compute.Algorithm77Prog
import GraphMinor.Compute.CrossingOpsBasic

/-!
# Reading a structural input row on the RAM

The cylinder input uses length-prefixed rows. Read the next length,
copy that many words to a work array, and advance the input cursor.
The proof uses the verified array-slice copy and gives a linear time
bound. The source input is preserved.
-/

@[expose] public section
namespace GraphMinor.Compute
open GraphMinor.Compute.Crossing

/-- Read the row at cursor register 8 into a distinct work array. -/
def gm06ReadRowProg (src dst : Arr) : Cmd :=
  .seq (.assign 9 (.read src (.reg 8)))
    (.seq (.assign 8 (.op .add (.reg 8) (.const 1)))
      (copySliceToArrCmd src dst))

/-- The RAM row reader returns exactly the encoded row and advances past it. -/
theorem gm06ReadRowProg_exec {w : ℕ} (src dst : Arr) (hne : src ≠ dst)
    (pre row tail : List ℕ) (s : State) (hw : 1 < 2 ^ w)
    (ha : s.arrs src = pre ++ gm06EncodeNatList row ++ tail)
    (hn : (s.arrs src).length < 2 ^ w)
    (hwords : ∀ x ∈ s.arrs src, x < 2 ^ w) (hr : s.regs 8 = pre.length) :
    ∃ s' t, Exec w (gm06ReadRowProg src dst) s s' t ∧
      t ≤ 13 + 22 * row.length ∧ s'.arrs dst = row ∧
      s'.regs 8 = pre.length + 1 + row.length ∧
      (∀ r, r ≠ 7 → r ≠ 8 → r ≠ 9 → r ≠ 11 → s'.regs r = s.regs r) ∧
      (∀ a, a ≠ dst → s'.arrs a = s.arrs a) := by
  have hlen : (s.arrs src).length = pre.length + 1 + row.length + tail.length := by
    simp [ha, gm06EncodeNatList]
    omega
  have hp : pre.length < (s.arrs src).length := by omega
  have hget : (s.arrs src)[pre.length] = row.length := by
    have hh : (s.arrs src)[pre.length]? = some row.length := by
      rw [ha]
      simp only [gm06EncodeNatList, List.append_assoc, List.cons_append]
      rw [List.getElem?_append_right (le_refl _)]
      simp
    simpa only [List.getElem?_eq_getElem hp, Option.some.injEq] using hh
  have hrow : row.length < 2 ^ w := by omega
  have hoff : pre.length + 1 < 2 ^ w := by omega
  let s₁ := s.setReg 9 row.length
  let s₂ := s₁.setReg 8 (pre.length + 1)
  have he₁ : Exec w (.assign 9 (.read src (.reg 8))) s s₁ 3 :=
    .assign (by
      have hh := GraphMinor.Compute.Crossing.eval_read (a := src) (GraphMinor.Compute.Crossing.eval_reg hr (hp.trans hn)) hp
        (by rw [hget]; exact hrow)
      simpa only [hget] using hh)
  have he₂ : Exec w (.assign 8 (.op .add (.reg 8) (.const 1))) s₁ s₂ 4 :=
    .assign (GraphMinor.Compute.Crossing.eval_add (GraphMinor.Compute.Crossing.eval_reg (by simpa [s₁] using hr) (hp.trans hn))
      (GraphMinor.Compute.Crossing.eval_const hw) hoff)
  obtain ⟨s', t, he, ht, hd, hc, hregs, harrs⟩ := copySliceToArrCmd_exec src dst hne row
    (pre.length + 1) (s := s₂) hw
    (by simpa [s₂, s₁] using hn)
    (by simpa only [s₂, s₁, State.setReg_arrs] using (show
      pre.length + 1 + row.length ≤ (s.arrs src).length by omega))
    (by
      intro j hj
      simp only [s₂, s₁, State.setReg_arrs, ha, gm06EncodeNatList, List.append_assoc, List.cons_append]
      rw [List.getElem?_append_right (by omega)]
      have hsub : pre.length + 1 + j - pre.length = j + 1 := by omega
      rw [hsub]
      simp only [List.getElem?_cons_succ]
      rw [List.getElem?_append_left hj, List.getElem?_eq_getElem hj])
    (by
      intro x hx
      apply hwords x
      rw [ha]
      exact List.mem_append.mpr (Or.inl (List.mem_append.mpr (Or.inr
        (by simpa [gm06EncodeNatList] using Or.inr hx)))))
    (by simp [s₂]) (by simp [s₂, s₁])
  refine ⟨s', 3 + (4 + t), .seq he₁ (.seq he₂ he), by omega, hd, hc, ?_, ?_⟩
  · intro r h7 h8 h9 h11
    rw [hregs r h7 h8 h9 h11]
    simp [s₂, s₁, State.setReg_regs_ne, h8, h9]
  · intro a hne'
    simpa only [s₂, s₁, State.setReg_arrs] using harrs a hne'

end GraphMinor.Compute
