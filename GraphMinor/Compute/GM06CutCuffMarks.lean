module

public import GraphMinor.Compute.GM06CutTables
public import GraphMinor.Compute.GM06PredecessorProgram
import GraphMinor.Compute.CrossingOpsBasic

/-!
# Marking the two ends of both cuffs

The encoding correction to Section 9 of our proof of VI (5.7) (outlined in
`GraphMinor/GM06/Alg57Algorithm.lean`) includes both cuff orders. This scan takes one such order and
its edge-label base. At vertex i it writes the forward end of gap i and the reverse end of the
preceding gap. Each write is computed from the index, including the wrap at index zero. The
same program is used for the inner and outer cuffs.
-/

@[expose] public section
namespace GraphMinor.Compute
open TwoPaths

/-- The signed cuff pairs have one entry for each supplied cuff vertex. -/
theorem gm06CutCuffPairs_length (base : ℕ) (cuff : List ℕ) (positive : Bool) :
    (gm06CutCuffPairs base cuff positive).length = cuff.length := by
  simp [gm06CutCuffPairs]

/-- The pair at index i gives the two ends prescribed by the cuff order. -/
theorem gm06CutCuffPairs_getElem (base : ℕ) (cuff : List ℕ) (positive : Bool)
    (i : ℕ) (hi : i < cuff.length) :
    (gm06CutCuffPairs base cuff positive)[i]'(by simpa [gm06CutCuffPairs] using hi) =
      (cuff[i], if positive then 2 * (base + i)
        else 2 * (base + gm06PreviousCuffIndex cuff.length i) + 1) := by
  simp [gm06CutCuffPairs]

/-- Append the next computed cuff write to a prefix of its scatter pass. -/
theorem gm06CutCuffPairs_take_succ (base : ℕ) (cuff : List ℕ) (positive : Bool)
    (i : ℕ) (hi : i < cuff.length) (table : List ℕ) :
    gm06Scatter ((gm06CutCuffPairs base cuff positive).take (i + 1)) table =
      (gm06Scatter ((gm06CutCuffPairs base cuff positive).take i) table).set cuff[i]
        (if positive then 2 * (base + i)
          else 2 * (base + gm06PreviousCuffIndex cuff.length i) + 1) := by
  rw [List.take_succ_eq_append_getElem (by simpa [gm06CutCuffPairs] using hi),
    gm06Scatter_append, gm06CutCuffPairs_getElem]
  rfl

/-- Compute the preceding gap index, including cyclic wrap. -/
def gm06CutCuffPreviousProg (src : ℕ) : Cmd :=
  .ite (.reg 650)
    (.assign 652 (.op .sub (.reg 650) (.const 1)))
    (.assign 652 (.op .sub (.len src) (.const 1)))

/-- The wrap computation is valid even for a one-vertex cuff. -/
theorem gm06CutCuffPreviousProg_exec {w k i src : ℕ} (s : State)
    (hw : 1 < 2 ^ w) (hk : k < 2 ^ w) (hi : i < k)
    (hsrc : (s.arrs src).length = k) (h650 : s.regs 650 = i) :
    Exec w (gm06CutCuffPreviousProg src) s
      (s.setReg 652 (gm06PreviousCuffIndex k i)) 5 := by
  by_cases hz : i = 0
  · have he : Exec w (.assign 652 (.op .sub (.len src) (.const 1))) s
        (s.setReg 652 (k - 1)) 4 :=
      .assign (GraphMinor.Compute.Crossing.eval_sub
        (by simp [Expr.eval, checkWord, hsrc, hk]) (GraphMinor.Compute.Crossing.eval_const hw))
    simpa only [gm06CutCuffPreviousProg, gm06PreviousCuffIndex, hz, ite_true,
      Expr.cost, Nat.reduceAdd] using
      (Exec.ite_false (cond := .reg 650)
        (by simpa only [hz] using GraphMinor.Compute.Crossing.eval_reg h650 (hi.trans hk)) he)
  · have he : Exec w (.assign 652 (.op .sub (.reg 650) (.const 1))) s
        (s.setReg 652 (i - 1)) 4 :=
      .assign (GraphMinor.Compute.Crossing.eval_sub
        (GraphMinor.Compute.Crossing.eval_reg h650 (hi.trans hk))
        (GraphMinor.Compute.Crossing.eval_const hw))
    simpa only [gm06CutCuffPreviousProg, gm06PreviousCuffIndex, hz, ite_false,
      Expr.cost, Nat.reduceAdd] using
      (Exec.ite_true (cond := .reg 650) (GraphMinor.Compute.Crossing.eval_reg h650 (hi.trans hk)) hz he)

/-- Write the positive and negative cuff ends at the current vertex.
The first edge label of this cuff is in register 653. -/
def gm06CutCuffMarkBody (src : ℕ) : Cmd :=
  .seq (.assign 651 (.read src (.reg 650)))
    (.seq (gm06CutCuffPreviousProg src)
      (.seq (.write 623 (.reg 651) (.op .mul (.const 2) (.op .add (.reg 653) (.reg 650))))
        (.write 624 (.reg 651) (.op .add
          (.op .mul (.const 2) (.op .add (.reg 653) (.reg 652))) (.const 1)))))

/-- Process one of the two supplied cuff orders. -/
def gm06CutCuffMarkProg (src : ℕ) : Cmd :=
  .seq (.assign 650 (.const 0)) (forUp 650 (.len src) (gm06CutCuffMarkBody src))

/-- The cuff scan computes exactly the two signed scatters, with a
linear time bound. Its input contains only the cuff's vertex order. -/
theorem gm06CutCuffMarkProg_exec {w n base src : ℕ}
    (hsrcPos : src ≠ 623) (hsrcNeg : src ≠ 624)
    (cuff positive negative : List ℕ) (s : State)
    (hw : 2 < 2 ^ w) (hn : n < 2 ^ w)
    (hsize : 2 * (base + cuff.length) + 1 < 2 ^ w)
    (hv : ∀ v ∈ cuff, v < n) (hpos : positive.length = n) (hneg : negative.length = n)
    (ha : s.arrs src = cuff) (hb : s.regs 653 = base)
    (h623 : s.arrs 623 = positive) (h624 : s.arrs 624 = negative) :
    ∃ sf t, Exec w (gm06CutCuffMarkProg src) s sf t ∧
      t ≤ 5 + 31 * cuff.length ∧ Keeps [650, 651, 652] [623, 624] s sf ∧
      sf.arrs 623 = gm06Scatter (gm06CutCuffPairs base cuff true) positive ∧
      sf.arrs 624 = gm06Scatter (gm06CutCuffPairs base cuff false) negative := by
  have hw1 : 1 < 2 ^ w := by omega
  have hkw : cuff.length < 2 ^ w := by omega
  have hbw : base < 2 ^ w := by omega
  let pscan := fun i => gm06Scatter ((gm06CutCuffPairs base cuff true).take i) positive
  let nscan := fun i => gm06Scatter ((gm06CutCuffPairs base cuff false).take i) negative
  let Inv := fun i st => st.regs 650 = i ∧ Keeps [650, 651, 652] [623, 624] s st ∧
    st.arrs 623 = pscan i ∧ st.arrs 624 = nscan i
  let s₀ := s.setReg 650 0
  have hI₀ : Inv 0 s₀ := ⟨by simp [s₀], (Keeps.refl _ _ s).setReg (by simp) _, h623, h624⟩
  obtain ⟨sf, tf, hef, htf, hIf⟩ := GraphMinor.Compute.Crossing.forUp_exec'
    (r_i := 650) (hi := .len src) (body := gm06CutCuffMarkBody src) Inv cuff.length 24 hw1 hkw
    (fun i _ st h => ⟨h.1, GraphMinor.Compute.Crossing.eval_len
      (by rw [h.2.1.2 src (by simp [hsrcPos, hsrcNeg]), ha]) hkw⟩)
    (fun i hi st h => by
      obtain ⟨hidx, hk, hpt, hnt⟩ := h
      have hcuff : st.arrs src = cuff := (hk.2 src (by simp [hsrcPos, hsrcNeg])).trans ha
      have hbase : st.regs 653 = base := (hk.1 653 (by decide)).trans hb
      have hv' : cuff[i] < n := hv _ (List.getElem_mem hi)
      have hprev := gm06PreviousCuffIndex_lt hi
      let st₁ := st.setReg 651 cuff[i]
      let st₂ := st₁.setReg 652 (gm06PreviousCuffIndex cuff.length i)
      let st₃ := st₂.writeArr 623 cuff[i] (2 * (base + i))
      let st₄ := st₃.writeArr 624 cuff[i] (2 * (base + gm06PreviousCuffIndex cuff.length i) + 1)
      have hread : (Expr.read src (.reg 650)).eval w st = some cuff[i] := by
        have he := GraphMinor.Compute.Crossing.eval_read (a := src) (s := st)
          (GraphMinor.Compute.Crossing.eval_reg hidx (hi.trans hkw))
          (by simpa [hcuff] using hi) (by simpa [hcuff] using hv'.trans hn)
        simpa only [hcuff] using he
      have he₁ : Exec w (.assign 651 (.read src (.reg 650))) st st₁ 3 := .assign hread
      have he₂ : Exec w (gm06CutCuffPreviousProg src) st₁ st₂ 5 :=
        gm06CutCuffPreviousProg_exec st₁ hw1 hkw hi (by simp [st₁, hcuff]) (by simp [st₁, hidx])
      have hindex₂ : (Expr.reg 651).eval w st₂ = some cuff[i] :=
        GraphMinor.Compute.Crossing.eval_reg (by simp [st₂, st₁]) (hv'.trans hn)
      have hbase₂ : (Expr.reg 653).eval w st₂ = some base :=
        GraphMinor.Compute.Crossing.eval_reg (by simp [st₂, st₁, hbase]) hbw
      have hposExpr : (Expr.op .mul (.const 2) (.op .add (.reg 653) (.reg 650))).eval w st₂ =
          some (2 * (base + i)) :=
        GraphMinor.Compute.Crossing.eval_mul (GraphMinor.Compute.Crossing.eval_const hw)
          (GraphMinor.Compute.Crossing.eval_add hbase₂
            (GraphMinor.Compute.Crossing.eval_reg (by simp [st₂, st₁, hidx]) (hi.trans hkw))
            (by omega)) (by omega)
      have hnegExpr : (Expr.op .add (.op .mul (.const 2) (.op .add (.reg 653) (.reg 652)))
          (.const 1)).eval w st₃ = some (2 * (base + gm06PreviousCuffIndex cuff.length i) + 1) :=
        GraphMinor.Compute.Crossing.eval_add
          (GraphMinor.Compute.Crossing.eval_mul (GraphMinor.Compute.Crossing.eval_const hw)
            (GraphMinor.Compute.Crossing.eval_add
              (GraphMinor.Compute.Crossing.eval_reg (by simp [st₃, st₂, st₁, hbase]) hbw)
              (GraphMinor.Compute.Crossing.eval_reg (by simp [st₃, st₂]) (hprev.trans hkw))
              (by omega)) (by omega)) (GraphMinor.Compute.Crossing.eval_const hw1) (by omega)
      have hplen : (st₂.arrs 623).length = n := by simp [st₂, st₁, hpt, pscan, gm06Scatter_length, hpos]
      have hnlen : (st₃.arrs 624).length = n := by
        simp [st₃, st₂, st₁, State.writeArr, hnt, nscan, gm06Scatter_length, hneg]
      have he₃ : Exec w (.write 623 (.reg 651) (.op .mul (.const 2) (.op .add (.reg 653) (.reg 650))))
          st₂ st₃ 7 := .write hindex₂ hposExpr (by rw [hplen]; exact hv')
      have he₄ : Exec w (.write 624 (.reg 651) (.op .add
          (.op .mul (.const 2) (.op .add (.reg 653) (.reg 652))) (.const 1))) st₃ st₄ 9 :=
        .write (GraphMinor.Compute.Crossing.eval_reg (by simp [st₃, st₂, st₁]) (hv'.trans hn))
          hnegExpr (by rw [hnlen]; exact hv')
      refine ⟨st₄, 24, .seq he₁ (.seq he₂ (.seq he₃ he₄)), le_rfl, ⟨by simp, ?_, ?_, ?_⟩, ?_⟩
      · exact ((((hk.setReg (by simp) _).setReg (by simp) _).writeArr
          (by simp) _ _).writeArr (by simp) _ _).setReg (by simp) _
      · change (st.arrs 623).set cuff[i] (2 * (base + i)) = pscan (i + 1)
        rw [hpt]
        exact (gm06CutCuffPairs_take_succ base cuff true i hi positive).symm
      · change (st.arrs 624).set cuff[i] (2 * (base + gm06PreviousCuffIndex cuff.length i) + 1) = nscan (i + 1)
        rw [hnt]
        exact (gm06CutCuffPairs_take_succ base cuff false i hi negative).symm
      · simpa [st₄, st₃, st₂, st₁, State.writeArr] using hidx) s₀ hI₀
  refine ⟨sf, 2 + tf, .seq (.assign (GraphMinor.Compute.Crossing.eval_const (Nat.two_pow_pos w))) hef,
    ?_, hIf.2.1, ?_, ?_⟩
  · simp only [Expr.cost] at htf
    omega
  · simpa only [pscan, ← gm06CutCuffPairs_length base cuff true, List.take_length] using hIf.2.2.1
  · simpa only [nscan, ← gm06CutCuffPairs_length base cuff false, List.take_length] using hIf.2.2.2

end GraphMinor.Compute
