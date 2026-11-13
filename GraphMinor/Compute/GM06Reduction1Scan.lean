module

public import GraphMinor.Compute.GM06Reduction1AtVertex
import GraphMinor.Compute.CrossingOpsBasic

/-!
# Scanning all supplied initial vertices for Reduction 1

Each cuff position loads its given path and input rotation, then
tries the calibrated edge deletion. Save the first successful cuff
index and skip all later queries. Thus success describes one edge
update, while failure excludes the finite clockwise test at every
initial vertex. This is the complete Reduction 1 finite scan for
VI (5.7), page 133.
-/

@[expose] public section
namespace GraphMinor.Compute
open TwoPaths GraphMinor.Compute.Crossing

/-- Scan cuff positions and perform the first clockwise deletion.
Register 297 records the successful cuff index and 55 its edge. -/
def gm06Reduction1ScanProg : Cmd :=
  .seq (.assign 60 (.const 0)) (.seq (.assign 295 (.const 0))
    (forUp 295 (.len 6) (.ite (.reg 60) .skip
      (.seq gm06Reduction1AtVertexProg
        (.ite (.reg 60) (.assign 297 (.reg 295)) .skip)))))

/-- The scan performs one verified finite edge update or excludes
all its candidates. Its polynomial bound includes ordinary row loading. -/
theorem gm06Reduction1ScanProg_exec {w B : ℕ}
    (cs mask : List ℕ) (paths rots : List (List ℕ))
    (hip : cs.length ≤ paths.length)
    (hvertex : ∀ i : Fin cs.length, cs[i.val] < rots.length)
    (hne : ∀ i : Fin cs.length, 0 < paths[i.val].length)
    (hw : 2 < 2 ^ w) (hsize : 2 * (mask.length + cs.length) + 1 < 2 ^ w)
    (hpLen : (gm06EncodeRows paths).length < 2 ^ w)
    (hrLen : (gm06EncodeRows rots).length < 2 ^ w)
    (hpWords : ∀ v ∈ gm06EncodeRows paths, v < 2 ^ w)
    (hrWords : ∀ v ∈ gm06EncodeRows rots, v < 2 ^ w)
    (hcsB : cs.length ≤ B) (hrotB : rots.length ≤ B)
    (hpathsB : ∀ row ∈ paths, row.length ≤ B) (hrotsB : ∀ row ∈ rots, row.length ≤ B)
    (hbits : ∀ b ∈ mask, b ≤ 1)
    (hnd : ∀ i : Fin cs.length, (rots[cs[i.val]]'(hvertex i)).Nodup)
    (hp : ∀ i : Fin cs.length,
      2 * (mask.length + gm06PreviousCuffIndex cs.length i.val) + 1 ∈ (rots[cs[i.val]]'(hvertex i)))
    (hq : ∀ i : Fin cs.length, (paths[i.val][0]'(hne i)) ∈ (rots[cs[i.val]]'(hvertex i)))
    (hc : ∀ i : Fin cs.length, 2 * (mask.length + i.val) ∈ (rots[cs[i.val]]'(hvertex i)))
    {s : State} (h6 : s.arrs 6 = cs) (h8 : s.arrs 8 = gm06EncodeRows paths)
    (h4 : s.arrs 4 = gm06EncodeRows rots) (h12 : s.arrs 12 = mask) :
    let P := fun (i : Fin cs.length) (e : Fin mask.length) => mask[e.val] = 1 ∧
      (gm06CalibratedSectorFlag (rots[cs[i.val]]'(hvertex i))
        (2 * (mask.length + gm06PreviousCuffIndex cs.length i.val) + 1)
        (paths[i.val][0]'(hne i)) (2 * (mask.length + i.val)) (2 * e.val) = 1 ∨
       gm06CalibratedSectorFlag (rots[cs[i.val]]'(hvertex i))
        (2 * (mask.length + gm06PreviousCuffIndex cs.length i.val) + 1)
        (paths[i.val][0]'(hne i)) (2 * (mask.length + i.val)) (2 * e.val + 1) = 1)
    ∃ s' t, Exec w gm06Reduction1ScanProg s s' t ∧
      t ≤ 7 + cs.length * (131 + 117 * B + mask.length * (120 + 104 * B)) ∧
      Keeps [295, 297, 7, 8, 9, 11, 31, 37, 296, 36, 39, 38, 50, 40, 41, 42, 43, 59, 53, 55, 54, 60]
        [12, 24, 25] s s' ∧
      ((s'.regs 60 = 0 ∧ s'.arrs 12 = mask ∧ ∀ i e, ¬ P i e) ∨
       ∃ (i : Fin cs.length) (e : Fin mask.length),
        s'.regs 60 = 1 ∧ s'.regs 297 = i.val ∧ s'.regs 55 = e.val ∧
        s'.arrs 12 = mask.set e.val 0 ∧ P i e ∧
        (s'.arrs 12).count 1 + 1 = mask.count 1) := by
  dsimp only
  let P := fun (i : Fin cs.length) (e : Fin mask.length) => mask[e.val] = 1 ∧
    (gm06CalibratedSectorFlag (rots[cs[i.val]]'(hvertex i))
      (2 * (mask.length + gm06PreviousCuffIndex cs.length i.val) + 1)
      (paths[i.val][0]'(hne i)) (2 * (mask.length + i.val)) (2 * e.val) = 1 ∨
     gm06CalibratedSectorFlag (rots[cs[i.val]]'(hvertex i))
      (2 * (mask.length + gm06PreviousCuffIndex cs.length i.val) + 1)
      (paths[i.val][0]'(hne i)) (2 * (mask.length + i.val)) (2 * e.val + 1) = 1)
  let R := [295, 297, 7, 8, 9, 11, 31, 37, 296, 36, 39, 38, 50, 40, 41, 42, 43, 59, 53, 55, 54, 60]
  let A := [12, 24, 25]
  let budget := 120 + 117 * B + mask.length * (120 + 104 * B)
  let Outcome := fun st : State => ∃ (i : Fin cs.length) (e : Fin mask.length),
    st.regs 60 = 1 ∧ st.regs 297 = i.val ∧ st.regs 55 = e.val ∧
      st.arrs 12 = mask.set e.val 0 ∧ P i e ∧ (st.arrs 12).count 1 + 1 = mask.count 1
  let Inv := fun i st => st.regs 295 = i ∧ Keeps R A s st ∧
    ((st.regs 60 = 0 ∧ st.arrs 12 = mask ∧
      ∀ j : Fin cs.length, j.val < i → ∀ e, ¬ P j e) ∨ Outcome st)
  have hw1 : 1 < 2 ^ w := by omega
  have hkw : cs.length < 2 ^ w := by omega
  let s₁ := s.setReg 60 0
  let s₂ := s₁.setReg 295 0
  have he₁ : Exec w (.assign 60 (.const 0)) s s₁ 2 :=
    .assign (GraphMinor.Compute.Crossing.eval_const (Nat.two_pow_pos w))
  have he₂ : Exec w (.assign 295 (.const 0)) s₁ s₂ 2 :=
    .assign (GraphMinor.Compute.Crossing.eval_const (Nat.two_pow_pos w))
  have hInv₀ : Inv 0 s₂ := by
    refine ⟨by simp [s₂],
      ((Keeps.refl R A s).setReg (by simp [R]) 0).setReg (by simp [R]) 0,
      Or.inl ⟨by simp [s₂, s₁], by simpa [s₂, s₁] using h12, ?_⟩⟩
    intro j hj
    omega
  obtain ⟨s', t, hex, ht, hInv⟩ := forUp_exec' (r_i := 295) (hi := .len 6)
    (body := .ite (.reg 60) .skip (.seq gm06Reduction1AtVertexProg
      (.ite (.reg 60) (.assign 297 (.reg 295)) .skip))) Inv cs.length (budget + 4) hw1 hkw
    (fun i _ st h => ⟨h.1, GraphMinor.Compute.Crossing.eval_len
      ((h.2.1.2 6 (by simp [A])).trans h6) hkw⟩)
    (fun i hi st h => by
      obtain ⟨hidx, hframe, hcase⟩ := h
      rcases hcase with ⟨hflag, hmask, hfailed⟩ | hsuccess
      · let v : Fin cs.length := ⟨i, hi⟩
        have hv : cs[i] < rots.length := hvertex v
        obtain ⟨st₁, t₁, he₁, ht₁, hk₁, hi₁, hout⟩ := gm06Reduction1AtVertexProg_exec
          cs mask paths rots i hi (hi.trans_le hip) (hvertex v) (hne v) st hw hsize
          hpLen hrLen hpWords hrWords hbits (hnd v) (hp v) (hq v) (hc v)
          ((hframe.2 6 (by simp [A])).trans h6)
          ((hframe.2 8 (by simp [A])).trans h8)
          ((hframe.2 4 (by simp [A])).trans h4) hmask hidx
        have hk : Keeps R A s st₁ := hframe.trans hk₁ (by simp [R]) (by simp [A])
        have hcost : t₁ ≤ budget := by
          have hpB := hpathsB paths[i] (List.getElem_mem (hi.trans_le hip))
          have hrB := hrotsB rots[cs[i]] (List.getElem_mem (hvertex v))
          have hproduct := Nat.mul_le_mul_left mask.length
            (show 120 + 104 * rots[cs[i]].length ≤ 120 + 104 * B by omega)
          dsimp only [budget]
          omega
        rcases hout with ⟨hz, hm, hnone⟩ | ⟨hone, e, he, hpos, hm, hactive, hsector, hprogress⟩
        · have hsave : Exec w (.ite (.reg 60) (.assign 297 (.reg 295)) .skip) st₁ st₁ 2 :=
            .ite_false (GraphMinor.Compute.Crossing.eval_reg hz (Nat.two_pow_pos w)) (.skip st₁)
          refine ⟨st₁, 1 + (t₁ + 2), .ite_false
            (GraphMinor.Compute.Crossing.eval_reg hflag (Nat.two_pow_pos w)) (.seq he₁ hsave),
            by omega, ⟨by simp, hk.setReg (by simp [R]) _, Or.inl ⟨?_, ?_, ?_⟩⟩, hi₁⟩
          · simpa using hz
          · simpa using hm
          · intro j hji e
            by_cases hj : j.val = i
            · have hjv : j = v := Fin.ext hj
              subst j
              exact hnone e.val e.isLt
            · exact hfailed j (by omega) e
        · let st₂ := st₁.setReg 297 i
          have hsave : Exec w (.ite (.reg 60) (.assign 297 (.reg 295)) .skip) st₁ st₂ 3 :=
            .ite_true (GraphMinor.Compute.Crossing.eval_reg hone hw1) (by decide)
              (.assign (GraphMinor.Compute.Crossing.eval_reg hi₁ (hi.trans hkw)))
          have ho : Outcome st₂ := by
            refine ⟨v, ⟨e, he⟩, ?_, by simp [st₂, v], ?_, ?_, ⟨hactive, hsector⟩, ?_⟩
            · simpa [st₂] using hone
            · simpa [st₂] using hpos
            · simpa [st₂] using hm
            · simpa [st₂] using hprogress
          refine ⟨st₂, 1 + (t₁ + 3), .ite_false
            (GraphMinor.Compute.Crossing.eval_reg hflag (Nat.two_pow_pos w)) (.seq he₁ hsave),
            by omega, ⟨by simp, (hk.setReg (by simp [R]) _).setReg (by simp [R]) _,
              Or.inr ?_⟩, ?_⟩
          · simpa only [Outcome, State.setReg_regs_ne _ _ (by decide : 60 ≠ 295),
              State.setReg_regs_ne _ _ (by decide : 297 ≠ 295),
              State.setReg_regs_ne _ _ (by decide : 55 ≠ 295), State.setReg_arrs] using ho
          · simpa [st₂] using hi₁
      · obtain ⟨j, e, hone, hj, he, hm, hp, hprogress⟩ := hsuccess
        have hsuccess' : Outcome st := ⟨j, e, hone, hj, he, hm, hp, hprogress⟩
        refine ⟨st, 2, .ite_true (GraphMinor.Compute.Crossing.eval_reg hone hw1) (by decide) (.skip st),
          by dsimp [budget]; omega,
          ⟨by simp, hframe.setReg (by simp [R]) _, Or.inr ?_⟩, hidx⟩
        simpa only [Outcome, State.setReg_regs_ne _ _ (by decide : 60 ≠ 295),
          State.setReg_regs_ne _ _ (by decide : 297 ≠ 295),
          State.setReg_regs_ne _ _ (by decide : 55 ≠ 295), State.setReg_arrs] using hsuccess') s₂ hInv₀
  have hbudget : 1 + 6 + (budget + 4) = 131 + 117 * B + mask.length * (120 + 104 * B) := by
    dsimp only [budget]
    omega
  simp only [Expr.cost] at ht
  rw [hbudget] at ht
  refine ⟨s', 2 + (2 + t), .seq he₁ (.seq he₂ hex), by omega, hInv.2.1, ?_⟩
  rcases hInv.2.2 with ⟨hz, hm, hfailed⟩ | ho
  · exact Or.inl ⟨hz, hm, fun i => hfailed i i.isLt⟩
  · exact Or.inr ho

end GraphMinor.Compute
