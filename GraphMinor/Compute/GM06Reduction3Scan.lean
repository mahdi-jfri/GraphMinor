module

public import GraphMinor.Compute.GM06Reduction3Candidate
import GraphMinor.Compute.CrossingOpsBasic

/-!
# Scanning all initial vertices for an initial-edge contraction

The Reduction 3 test in VI (5.7), page 133, reads the initial
vertex, counts its active ends and reads its given path's first
neighbour. Scan every initial cuff index until this test succeeds.
Save the chosen path index and retain its computed edge and
neighbour registers for the contraction update. Failure excludes
the finite condition at every initial vertex. All instance arrays
are preserved by this search.
-/

public section
namespace GraphMinor.Compute
open TwoPaths GraphMinor.Compute.Crossing

/-- Scan the initial cuff for a valency-one start whose neighbour
is off the outer cuff. Registers 327/328 hold success and its index. -/
@[expose] def gm06Reduction3ScanProg : Cmd :=
  .seq (.assign 327 (.const 0)) (.seq (.assign 295 (.const 0))
    (forUp 295 (.len 6) (.ite (.reg 327) .skip
      (.seq (.assign 22 (.read 6 (.reg 295)))
        (.seq gm06Reduction3CandidateProg
          (.ite (.reg 306) (.seq (.assign 327 (.const 1)) (.assign 328 (.reg 295))) .skip))))))

/-- The complete finite scan returns one computed contraction
candidate, retaining its endpoints and first directed edge, or
excludes the test at every start. Its bound includes all row reads. -/
theorem gm06Reduction3ScanProg_exec {w B : ℕ}
    (xs mask cs outer : List ℕ) (paths : List (List ℕ))
    (hip : cs.length ≤ paths.length)
    (hne : ∀ j : Fin cs.length, 0 < (paths[j.val]'(j.isLt.trans_le hip)).length)
    (hfirst : ∀ j : Fin cs.length, (paths[j.val][0]'(hne j)) < 2 * mask.length)
    (s : State) (hw : 2 < 2 ^ w) (hm : 2 * mask.length < 2 ^ w)
    (hlen : xs.length = 2 * mask.length) (hx : ∀ x ∈ xs, x < 2 ^ w)
    (hbits : ∀ x ∈ mask, x ≤ 1) (hcs : cs.length < 2 ^ w)
    (hcsWords : ∀ x ∈ cs, x < 2 ^ w) (ho : outer.length < 2 ^ w)
    (hoWords : ∀ x ∈ outer, x < 2 ^ w)
    (hpLen : (gm06EncodeRows paths).length < 2 ^ w)
    (hpWords : ∀ x ∈ gm06EncodeRows paths, x < 2 ^ w)
    (hpathsB : ∀ row ∈ paths, row.length ≤ B)
    (h3 : s.arrs 3 = xs) (h12 : s.arrs 12 = mask) (h6 : s.arrs 6 = cs)
    (h7 : s.arrs 7 = outer) (h8 : s.arrs 8 = gm06EncodeRows paths) :
    let neighbour := fun j : Fin cs.length =>
      xs[gm06DartMate (paths[j.val][0]'(hne j))]'(hlen ▸ gm06DartMate_lt (hfirst j))
    let P := fun j : Fin cs.length => (gm06ActiveEndpointBits xs mask cs[j.val]).sum = 1 ∧ neighbour j ∉ outer
    ∃ s' t, Exec w gm06Reduction3ScanProg s s' t ∧
      t ≤ 7 + cs.length * (73 + 42 * mask.length + 17 * cs.length + 22 * B + 13 * outer.length) ∧
      Keeps [327, 328, 295, 22, 20, 21, 7, 8, 9, 11, 31, 23, 24, 301, 303, 304, 305, 306] [24] s s' ∧
      ((s'.regs 327 = 0 ∧ ∀ j, ¬ P j) ∨
       ∃ j : Fin cs.length, s'.regs 327 = 1 ∧ s'.regs 328 = j.val ∧
         s'.regs 22 = cs[j.val] ∧ s'.regs 23 = paths[j.val][0]'(hne j) ∧
         s'.regs 24 = gm06DartMate (paths[j.val][0]'(hne j)) ∧
         s'.regs 301 = neighbour j ∧ s'.regs 306 = 1 ∧ P j) := by
  dsimp only
  let neighbour := fun j : Fin cs.length =>
    xs[gm06DartMate (paths[j.val][0]'(hne j))]'(hlen ▸ gm06DartMate_lt (hfirst j))
  let P := fun j : Fin cs.length => (gm06ActiveEndpointBits xs mask cs[j.val]).sum = 1 ∧ neighbour j ∉ outer
  let R := [327, 328, 295, 22, 20, 21, 7, 8, 9, 11, 31, 23, 24, 301, 303, 304, 305, 306]
  let budget := 66 + 42 * mask.length + 17 * cs.length + 22 * B + 13 * outer.length
  let Outcome := fun st : State => ∃ j : Fin cs.length,
    st.regs 327 = 1 ∧ st.regs 328 = j.val ∧ st.regs 22 = cs[j.val] ∧
      st.regs 23 = paths[j.val][0]'(hne j) ∧ st.regs 24 = gm06DartMate (paths[j.val][0]'(hne j)) ∧
      st.regs 301 = neighbour j ∧ st.regs 306 = 1 ∧ P j
  let Inv := fun i st => st.regs 295 = i ∧ Keeps R [24] s st ∧
    ((st.regs 327 = 0 ∧ ∀ j : Fin cs.length, j.val < i → ¬ P j) ∨ Outcome st)
  have hw1 : 1 < 2 ^ w := by omega
  let s₁ := s.setReg 327 0
  let s₂ := s₁.setReg 295 0
  have he₁ : Exec w (.assign 327 (.const 0)) s s₁ 2 := .assign (GraphMinor.Compute.Crossing.eval_const (Nat.two_pow_pos w))
  have he₂ : Exec w (.assign 295 (.const 0)) s₁ s₂ 2 := .assign (GraphMinor.Compute.Crossing.eval_const (Nat.two_pow_pos w))
  have hInv : Inv 0 s₂ := by
    refine ⟨by simp [s₂], ((Keeps.refl _ _ s).setReg (by simp [R]) _).setReg (by simp [R]) _,
      Or.inl ⟨by simp [s₂, s₁], ?_⟩⟩
    intro j hj; omega
  obtain ⟨s', t, hex, ht, hout⟩ := forUp_exec' (r_i := 295) (hi := .len 6)
    (body := .ite (.reg 327) .skip
      (.seq (.assign 22 (.read 6 (.reg 295))) (.seq gm06Reduction3CandidateProg
        (.ite (.reg 306) (.seq (.assign 327 (.const 1)) (.assign 328 (.reg 295))) .skip))))
    Inv cs.length budget hw1 hcs
    (fun i _ st h => ⟨h.1, GraphMinor.Compute.Crossing.eval_len ((h.2.1.2 6 (by decide)).trans h6) hcs⟩)
    (fun i hi st h => by
      obtain ⟨hidx, hframe, hcase⟩ := h
      rcases hcase with ⟨hzero, hfailed⟩ | hsuccess
      · let v : Fin cs.length := ⟨i, hi⟩
        have hip' : i < paths.length := hi.trans_le hip
        have hcs' : st.arrs 6 = cs := (hframe.2 6 (by decide)).trans h6
        let st₀ := st.setReg 22 cs[i]
        have he₀ : Exec w (.assign 22 (.read 6 (.reg 295))) st st₀ 3 := by
          have hh := GraphMinor.Compute.Crossing.eval_read (a := 6)
            (GraphMinor.Compute.Crossing.eval_reg hidx (hi.trans hcs))
            (by simpa only [hcs'] using hi) (by simpa only [hcs'] using hcsWords _ (List.getElem_mem hi))
          simpa only [hcs', Expr.cost, Nat.reduceAdd] using Exec.assign (r := 22) hh
        have hk₀ : Keeps R [24] s st₀ := hframe.setReg (by simp [R]) _
        obtain ⟨st₁, t₁, heCand, ht₁, hk₁, hcount, h23, h24, h301, hflag, hbit⟩ :=
          gm06Reduction3CandidateProg_exec xs mask outer paths i cs[i] hip' (hne v) (hfirst v) st₀
            hw hm hlen hx hbits (hcsWords _ (List.getElem_mem hi)) ho hoWords hpLen hpWords
            (by simpa [st₀] using (hframe.2 3 (by decide)).trans h3)
            (by simpa [st₀] using (hframe.2 12 (by decide)).trans h12)
            (by simpa [st₀] using (hframe.2 7 (by decide)).trans h7)
            (by simpa [st₀] using (hframe.2 8 (by decide)).trans h8)
            (by simp [st₀]) (by simpa [st₀] using hidx)
        have hk : Keeps R [24] s st₁ := hk₀.trans hk₁ (by simp [R]) (by simp)
        have hidx₁ : st₁.regs 295 = i := (hk₁.1 295 (by decide)).trans (by simpa [st₀] using hidx)
        have hzero₁ : st₁.regs 327 = 0 := (hk₁.1 327 (by decide)).trans (by simpa [st₀] using hzero)
        have h22 : st₁.regs 22 = cs[i] := (hk₁.1 22 (by decide)).trans (by simp [st₀])
        have hflag' : st₁.regs 306 = 1 ↔ P v := hflag
        have hcost : t₁ + 9 ≤ budget := by
          have hb := hpathsB paths[i] (List.getElem_mem hip')
          dsimp only [budget]; omega
        rcases hbit with hz | hone
        · have hnone : ¬ P v := fun hp => Nat.zero_ne_one (hz.symm.trans (hflag'.mpr hp))
          have hsave : Exec w (.ite (.reg 306) (.seq (.assign 327 (.const 1)) (.assign 328 (.reg 295))) .skip)
              st₁ st₁ 2 := .ite_false (GraphMinor.Compute.Crossing.eval_reg hz (Nat.two_pow_pos w)) (.skip st₁)
          refine ⟨st₁, 1 + (3 + (t₁ + 2)), .ite_false
            (GraphMinor.Compute.Crossing.eval_reg hzero (Nat.two_pow_pos w)) (.seq he₀ (.seq heCand hsave)),
            by omega, ⟨by simp, hk.setReg (by simp [R]) _, Or.inl ⟨?_, ?_⟩⟩, hidx₁⟩
          · simpa using hzero₁
          · intro j hj
            by_cases hji : j.val = i
            · exact (Fin.ext hji : j = v) ▸ hnone
            · exact hfailed j (by omega)
        · let st₂ := st₁.setReg 327 1
          let st₃ := st₂.setReg 328 i
          have hsave : Exec w (.ite (.reg 306) (.seq (.assign 327 (.const 1)) (.assign 328 (.reg 295))) .skip)
              st₁ st₃ 5 := .ite_true (GraphMinor.Compute.Crossing.eval_reg hone hw1) (by decide)
                (.seq (.assign (GraphMinor.Compute.Crossing.eval_const hw1))
                  (.assign (GraphMinor.Compute.Crossing.eval_reg (by simpa [st₂] using hidx₁) (hi.trans hcs))))
          have ho' : Outcome st₃ := by
            refine ⟨v, by simp [st₃, st₂], by simp [st₃, v], ?_, ?_, ?_, ?_, ?_, hflag'.mp hone⟩
            · simpa [st₃, st₂] using h22
            · simpa [st₃, st₂] using h23
            · simpa [st₃, st₂] using h24
            · simpa [st₃, st₂] using h301
            · simpa [st₃, st₂] using hone
          refine ⟨st₃, 1 + (3 + (t₁ + 5)), .ite_false
            (GraphMinor.Compute.Crossing.eval_reg hzero (Nat.two_pow_pos w)) (.seq he₀ (.seq heCand hsave)),
            by omega, ⟨by simp, ((hk.setReg (by simp [R]) _).setReg (by simp [R]) _).setReg (by simp [R]) _,
              Or.inr ?_⟩, ?_⟩
          · simpa only [Outcome, State.setReg_regs_ne _ _ (by decide : 327 ≠ 295),
              State.setReg_regs_ne _ _ (by decide : 328 ≠ 295), State.setReg_regs_ne _ _ (by decide : 22 ≠ 295),
              State.setReg_regs_ne _ _ (by decide : 23 ≠ 295), State.setReg_regs_ne _ _ (by decide : 24 ≠ 295),
              State.setReg_regs_ne _ _ (by decide : 301 ≠ 295), State.setReg_regs_ne _ _ (by decide : 306 ≠ 295)] using ho'
          · simpa [st₃, st₂] using hidx₁
      · obtain ⟨j, hone, hindex, h22, h23, h24, h301, h306, hp⟩ := hsuccess
        have ho' : Outcome st := ⟨j, hone, hindex, h22, h23, h24, h301, h306, hp⟩
        refine ⟨st, 2, .ite_true (GraphMinor.Compute.Crossing.eval_reg hone hw1) (by decide) (.skip st),
          by dsimp only [budget]; omega, ⟨by simp, hframe.setReg (by simp [R]) _, Or.inr ?_⟩, hidx⟩
        simpa only [Outcome, State.setReg_regs_ne _ _ (by decide : 327 ≠ 295),
          State.setReg_regs_ne _ _ (by decide : 328 ≠ 295), State.setReg_regs_ne _ _ (by decide : 22 ≠ 295),
          State.setReg_regs_ne _ _ (by decide : 23 ≠ 295), State.setReg_regs_ne _ _ (by decide : 24 ≠ 295),
          State.setReg_regs_ne _ _ (by decide : 301 ≠ 295), State.setReg_regs_ne _ _ (by decide : 306 ≠ 295)] using ho') s₂ hInv
  simp only [Expr.cost] at ht
  refine ⟨s', 2 + (2 + t), .seq he₁ (.seq he₂ hex), ?_, hout.2.1, ?_⟩
  · have hb : 1 + 6 + budget = 73 + 42 * mask.length + 17 * cs.length + 22 * B + 13 * outer.length := by
      dsimp only [budget]; omega
    rw [hb] at ht
    omega
  · rcases hout.2.2 with ⟨hz, hfailed⟩ | ho'
    · exact Or.inl ⟨hz, fun j => hfailed j j.isLt⟩
    · exact Or.inr ho'

end GraphMinor.Compute
