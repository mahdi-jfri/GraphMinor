module

public import GraphMinor.Compute.BitSet
import Mathlib.Data.List.GetD

/-!
# Recording a loop owner once

During a member scan, a present vertex receives the current member label only
if its owner word is still the missing sentinel. Later members preserve that
word. This makes the first containing member the owner of all loops there.
-/

@[expose] public section

namespace GraphMinor.Compute

/-- Record the current group for an unassigned vertex present in its bitset. -/
def case3RecordOwnerBody (a_set a_owner r_i r_group r_missing : ℕ) : Cmd :=
  .ite (.op .mul (.read a_set (.reg r_i))
      (.op .eq (.read a_owner (.reg r_i)) (.reg r_missing)))
    (.write a_owner (.reg r_i) (.reg r_group))
    (.write a_owner (.reg r_i) (.read a_owner (.reg r_i)))

/-- One owner entry is replaced by the group label exactly on its first visit.
Both branches write an entry, so the resulting state has one uniform form. -/
theorem case3RecordOwnerBody_exec {w n : ℕ} (S : Finset (Fin n))
    (a_set a_owner r_i r_group r_missing k old label missing : ℕ)
    (hk : k < n) (hw : 1 < 2 ^ w) (hn : n < 2 ^ w)
    (hold : old < 2 ^ w) (hlabel : label < 2 ^ w) (hmissing : missing < 2 ^ w)
    {s : State} (hset : IsBitSet S a_set s) (hlen : (s.arrs a_owner).length = n)
    (hget : (s.arrs a_owner).getD k 0 = old)
    (hri : s.regs r_i = k) (hrg : s.regs r_group = label)
    (hrm : s.regs r_missing = missing) :
    ∃ t, Exec w (case3RecordOwnerBody a_set a_owner r_i r_group r_missing) s
      (s.writeArr a_owner k
        (if (⟨k, hk⟩ : Fin n) ∈ S ∧ old = missing then label else old)) t ∧ t ≤ 12 := by
  have h0 : 0 < 2 ^ w := by omega
  have hkw : k < 2 ^ w := hk.trans hn
  have hidx : k < (s.arrs a_set).length := by rw [hset.1]; exact hk
  have hidxo : k < (s.arrs a_owner).length := by omega
  have hbit : (s.arrs a_set)[k]'hidx = if (⟨k, hk⟩ : Fin n) ∈ S then 1 else 0 := by
    simpa only [hset.arr_eq_bitSetList] using getElem_bitSetList S k hk
  have ho : (s.arrs a_owner)[k]'hidxo = old := by
    simpa only [List.getD_eq_getElem _ 0 hidxo] using hget
  have hi : (Expr.reg r_i).eval w s = some k := by
    simp only [Expr.eval, checkWord, hri, hkw, ↓reduceIte]
  have hv : (Expr.reg r_group).eval w s = some label := by
    simp only [Expr.eval, checkWord, hrg, hlabel, ↓reduceIte]
  have hread : (Expr.read a_owner (.reg r_i)).eval w s = some old := by
    simp [Expr.eval, checkWord, hri, hkw, hidxo, ho, hold]
  by_cases h : (⟨k, hk⟩ : Fin n) ∈ S ∧ old = missing
  · have hc : (Expr.op .mul (.read a_set (.reg r_i))
        (.op .eq (.read a_owner (.reg r_i)) (.reg r_missing))).eval w s = some 1 := by
      simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hri, hrm, hkw,
        hidx, hidxo, hbit, ho, hold, hmissing, h.1, h.2, hw]
    simp only [ite_eq_left h]
    exact ⟨10, .ite_true hc (by decide) (.write hi hv hidxo), by decide⟩
  · have hc : (Expr.op .mul (.read a_set (.reg r_i))
        (.op .eq (.read a_owner (.reg r_i)) (.reg r_missing))).eval w s = some 0 := by
      by_cases hs : (⟨k, hk⟩ : Fin n) ∈ S
      · have he : old ≠ missing := fun he => h ⟨hs, he⟩
        simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hri, hrm, hkw,
          hidx, hidxo, hbit, ho, hold, hmissing, hs, he, hw, h0]
      · by_cases he : old = missing <;> simp [he, Expr.eval, BinOp.eval, BinOp.raw, checkWord, hri, hrm, hkw,
          hidx, hidxo, hbit, ho, hold, hmissing, hs, hw, h0]
    simp only [h, ↓reduceIte]
    exact ⟨11, .ite_false hc (.write hi hread hidxo), by decide⟩

end GraphMinor.Compute
