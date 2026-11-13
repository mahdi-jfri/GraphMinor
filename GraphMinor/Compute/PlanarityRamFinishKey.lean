module

public import GraphMinor.Compute.PlanarityRamAdd
public import GraphMinor.Compute.PlanarityRamRead
public import GraphMinor.Compute.PlanarityRamUpdate

/-!
# Computing an edge's sorting key

Part I, Section 1 sets the key to twice the first lowpoint plus the bit
saying that the second lowpoint is below the source depth. The program
reads the source and both lowpoints, decodes the source depth, and writes
one key word. It leaves the source and child lowpoints ready for the
parent-pair update.
-/

@[expose] public section
namespace GraphMinor.Compute.PlanarityRam

open LRPlanarity

/-- The sorting key assigned when an edge is finished. -/
def finishedKey (search : Search) (i : ℕ) : ℕ :=
  2 * search.edges[i]!.pair.low +
    (decide (search.edges[i]!.pair.second <
      (search.depth[search.edges[i]!.source]?.join).getD 0)).toNat

/-- Compute the key with the edge index in register 45. -/
def finishKeyProg : Cmd :=
  .seq (.assign 41 (.read Field.tail.array (.reg 45)))
    (.seq (.assign 43 (.read Field.low.array (.reg 45)))
      (.seq (.assign 44 (.read Field.low2.array (.reg 45)))
        (.seq (.assign 46 (depthExpr 41))
          (.write Field.key.array (.reg 45)
            (.op .add (.op .mul (.const 2) (.reg 43))
              (.op .lt (.reg 44) (.reg 46)))))))

/-- Finishing the key takes twenty-three steps. Its source must index the
depth array, and each read and the resulting key must fit in a word. -/
theorem finishKeyProg_refines {N M w : ℕ} {s : State} {search : Search}
    (h : SearchAt N M s search) (i : ℕ) (hi : i < search.edges.size)
    (hr : s.regs 45 = i) (hv : search.edges[i].source < search.depth.size)
    (hw : 2 < 2 ^ w) (hiw : i < 2 ^ w)
    (hvw : search.edges[i].source < 2 ^ w)
    (hlo : search.edges[i].pair.low < 2 ^ w) (hhi : search.edges[i].pair.second < 2 ^ w)
    (hdw : optionWord search.depth[search.edges[i].source] < 2 ^ w)
    (hkey : finishedKey search i < 2 ^ w) :
    ∃ s', Exec w finishKeyProg s s' 23 ∧
      SearchAt N M s' (setEdgeKey search i (finishedKey search i)) ∧
      s'.regs 41 = search.edges[i].source ∧ s'.regs 43 = search.edges[i].pair.low ∧
      s'.regs 44 = search.edges[i].pair.second ∧ s'.regs 45 = i := by
  let e := search.edges[i]
  change e.source < search.depth.size at hv
  change e.source < 2 ^ w at hvw
  change e.pair.low < 2 ^ w at hlo
  change e.pair.second < 2 ^ w at hhi
  change optionWord search.depth[e.source] < 2 ^ w at hdw
  let d := (search.depth[e.source]?.join).getD 0
  let s1 := s.setReg 41 e.source
  let s2 := s1.setReg 43 e.pair.low
  let s3 := s2.setReg 44 e.pair.second
  let s4 := s3.setReg 46 d
  let s5 := s4.writeArr Field.key.array i (finishedKey search i)
  have h1 := h.setReg 41 e.source (by decide) (by decide)
  have h2 := h1.setReg 43 e.pair.low (by decide) (by decide)
  have h3 := h2.setReg 44 e.pair.second (by decide) (by decide)
  have h4 := h3.setReg 46 d (by decide) (by decide)
  have hx1 : Exec w (.assign 41 (.read Field.tail.array (.reg 45))) s s1 3 :=
    Exec.assign (h.read_tail hi hr hiw hvw)
  have hx2 : Exec w (.assign 43 (.read Field.low.array (.reg 45))) s1 s2 3 :=
    Exec.assign (h1.read_low hi (by simpa [s1] using hr) hiw hlo)
  have hx3 : Exec w (.assign 44 (.read Field.low2.array (.reg 45))) s2 s3 3 :=
    Exec.assign (h2.read_low2 hi (by simpa [s2, s1] using hr) hiw hhi)
  have hx4 : Exec w (.assign 46 (depthExpr 41)) s3 s4 5 := by
    apply Exec.assign
    exact depthExpr_eval h3.2.2.2.2.2.1 hv (by simp [s3, s2, s1]) hvw hdw (by omega)
  have hd : d < 2 ^ w := by
    have hh := Nat.lt_of_le_of_lt
      (Nat.sub_le (optionWord search.depth[e.source]) 1) hdw
    simpa [d, optionWord_sub_one, Array.getElem?_eq_getElem hv] using hh
  have he : search.edges[i]! = e := getElem!_pos search.edges i hi
  have hmul : 2 * e.pair.low < 2 ^ w := by
    have hb : 2 * e.pair.low ≤ finishedKey search i := by
      simp only [finishedKey, he]
      exact Nat.le_add_right _ _
    exact Nat.lt_of_le_of_lt hb hkey
  have hbit : (decide (e.pair.second < d)).toNat < 2 ^ w := by
    cases hb : decide (e.pair.second < d)
    · exact Nat.lt_trans (by decide : 0 < 2) hw
    · exact Nat.lt_trans (by decide : 1 < 2) hw
  have emul : (Expr.op .mul (.const 2) (.reg 43)).eval w s4 = some (2 * e.pair.low) := by
    simp [Expr.eval, s4, s3, s2, checkWord_of_lt hlo, checkWord_of_lt hw,
      BinOp.eval, BinOp.raw, checkWord_of_lt hmul]
  have ebit : (Expr.op .lt (.reg 44) (.reg 46)).eval w s4 =
      some (decide (e.pair.second < d)).toNat := by
    simp only [Expr.eval, s4, s3, State.setReg_regs_self, State.setReg_regs_ne _ _
      (show (44 : ℕ) ≠ 46 by decide), checkWord_of_lt hhi, checkWord_of_lt hd, BinOp.eval, BinOp.raw]
    convert checkWord_of_lt hbit using 1
    by_cases hb : e.pair.second < d <;> simp [hb]
  have ekey : (Expr.op .add (.op .mul (.const 2) (.reg 43))
      (.op .lt (.reg 44) (.reg 46))).eval w s4 = some (finishedKey search i) := by
    rw [Expr.eval, emul, ebit]
    simpa only [BinOp.eval, BinOp.raw, finishedKey, he] using checkWord_of_lt hkey
  have hslot : i < (s4.arrs Field.key.array).length :=
    h4.2.2.2.2.2.2.2.2.2.2.2.2.2.1.index_lt (by simpa using hi)
  have hx5 : Exec w (.write Field.key.array (.reg 45)
      (.op .add (.op .mul (.const 2) (.reg 43)) (.op .lt (.reg 44) (.reg 46)))) s4 s5 9 :=
    Exec.write (by simpa [Expr.eval, s4, s3, s2, s1, hr] using checkWord_of_lt hiw) ekey hslot
  refine ⟨s5, Exec.seq hx1 (Exec.seq hx2 (Exec.seq hx3 (Exec.seq hx4 hx5))),
    h4.write_key i (finishedKey search i) hi, ?_, ?_, ?_, ?_⟩
  · simp [s5, s4, s3, s2, s1, e]
  · simp [s5, s4, s3, s2, e]
  · simp [s5, s4, s3, e]
  · simpa [s5, s4, s3, s2, s1] using hr

end GraphMinor.Compute.PlanarityRam
