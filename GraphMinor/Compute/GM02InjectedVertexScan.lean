module

public import GraphMinor.Compute.GM02InjectedVertexScanBody
import GraphMinor.Compute.CrossingOpsBasic
import Mathlib.Tactic.Ring

/-!
# Scanning all host vertices for one injected pattern

Run the verified emission step through all host positions. Its exact
buffer prefix invariant yields the sorted pattern vertices at the end.
The scan is linear in the host vertex count for a fixed pattern.
-/

public section
namespace GraphMinor.Compute
open GraphMinor.Compute.Crossing

/-- Scan host positions using register 194 and retain their selected images. -/
@[expose] def gm02InjectedVertexScanProg (p : ℕ) : Cmd :=
  forUp 194 (.reg 40) (gm02InjectedVertexScanBody p)

/-- The complete host scan emits the exact sorted vertex buffer and uses linear time. -/
theorem gm02InjectedVertexScanProg_exec {W : ℕ} (G H : GM02EdgeListInput)
    (f : Fin H.n ↪ Fin G.n) (s : State)
    (hw : 1 < 2 ^ W) (hn : G.n + 1 < 2 ^ W) (hrn : s.regs 40 = G.n)
    (hzero : s.regs 194 = 0) (hpos : s.regs 195 = 1)
    (hslots : ∀ i : Fin H.n, s.regs (200 + i.val) = (f i).val)
    (hbuf : s.arrs 29 = gm02InjectedVertexBuffer G H f 0) :
    ∃ s' t, Exec W (gm02InjectedVertexScanProg H.n) s s' t ∧
      t ≤ 3 + G.n * ((gm02InjectionMembershipExpr H.n).cost + 14) ∧
      s'.arrs 29 = gm02InjectedVertexBuffer G H f G.n ∧
      s'.regs 195 = H.n + 1 ∧
      (∀ a, a ≠ 29 → s'.arrs a = s.arrs a) ∧
      (∀ r, r ≠ 194 → r ≠ 195 → s'.regs r = s.regs r) := by
  let I : ℕ → State → Prop := fun j st => st.regs 194 = j ∧
    st.arrs 29 = gm02InjectedVertexBuffer G H f j ∧
    st.regs 195 = (gm02InjectedVertexWords G H f j).length ∧
    (∀ a, a ≠ 29 → st.arrs a = s.arrs a) ∧
    (∀ r, r ≠ 194 → r ≠ 195 → st.regs r = s.regs r)
  have hI : I 0 s := by
    refine ⟨hzero, hbuf, ?_, fun _ _ => rfl, fun _ _ _ => rfl⟩
    simpa only [gm02InjectedVertexWords, gm02InjectedVertexPrefix, List.take_zero,
      List.filter_nil, List.map_nil, List.append_nil, List.length_singleton] using hpos
  have hn' : G.n < 2 ^ W := by omega
  obtain ⟨s', t, he, ht, hi⟩ := forUp_exec' I G.n ((gm02InjectionMembershipExpr H.n).cost + 7)
    (r_i := 194) (hi := .reg 40) (body := gm02InjectedVertexScanBody H.n) hw hn'
    (fun j hj st hst => ⟨hst.1, eval_reg ((hst.2.2.2.2 40 (by decide) (by decide)).trans hrn) hn'⟩)
    (fun j hj st hst => by
      rcases hst with ⟨hindex, hbuffer, hposition, harr, hreg⟩
      have hslots' (i : Fin H.n) : st.regs (200 + i.val) = (f i).val := by
        have h194 : 200 + i.val ≠ 194 := Nat.ne_of_gt
          ((by decide : 194 < 200).trans_le (Nat.le_add_right 200 i.val))
        have h195 : 200 + i.val ≠ 195 := Nat.ne_of_gt
          ((by decide : 195 < 200).trans_le (Nat.le_add_right 200 i.val))
        exact (hreg _ h194 h195).trans (hslots i)
      obtain ⟨st', t, he, ht, hb, hp, ha, hr⟩ := gm02InjectedVertexScanBody_exec G H f ⟨j, hj⟩ st
        hw hn hslots' hindex hbuffer hposition
      refine ⟨st', t, he, ht, ?_, (hr 194 (by decide)).trans hindex⟩
      refine ⟨State.setReg_regs_self .., hb, ?_, ?_, ?_⟩
      · exact (State.setReg_regs_ne st' (j + 1) (by decide : (195 : Reg) ≠ 194)).trans hp
      · intro a ha29
        exact (ha a ha29).trans (harr a ha29)
      · intro r hr194 hr195
        exact (State.setReg_regs_ne st' (j + 1) hr194).trans ((hr r hr195).trans (hreg r hr194 hr195))) s hI
  refine ⟨s', t, he, ?_, hi.2.1, ?_, hi.2.2.2.1, hi.2.2.2.2⟩
  · dsimp only [Expr.cost] at ht
    convert ht using 1 <;> ring
  · have hfull := gm02InjectedVertexPrefix_full G H f
    have hlength : (gm02InjectedVertexPrefix G H f G.n).length = H.n := by
      rw [hfull]
      change (((Finset.univ.image f).sort).map Fin.val).length = H.n
      rw [List.length_map, Finset.length_sort, Finset.card_image_of_injective _ f.injective,
        Finset.card_univ, Fintype.card_fin]
    simpa only [gm02InjectedVertexWords, List.length_append, List.length_singleton, hlength,
      Nat.add_comm] using hi.2.2.1

end GraphMinor.Compute
