module

public import GraphMinor.Compute.CrossingLiftChoose
public import GraphMinor.Compute.CrossingLiftPatch
public import GraphMinor.Compute.CrossingLiftSplice
import Mathlib.Data.List.GetD

/-!
# The interior-vertex contraction lift on the RAM

When both contracted ends are off the cycle, a used merged vertex is internal to one path.
Section 11 chooses an old endpoint supporting each incident path edge, then replaces the
merged vertex by those choices, suppressing a repeated choice. The program below reads the
two neighbouring path vertices, makes those choices from the recorded neighbour list, writes
the short segment, and splices it into the path.
-/

@[expose] public section

namespace GraphMinor.Compute.Crossing

/-- Lift an internal occurrence whose position is in register `R`. The endpoints are supplied
in `r_u`, `r_v`. Arrays `patch` and `tmp` and registers starting at `R` are scratch space. -/
def liftOffOffUsedProg (src neighbours patch tmp r_u r_v R : ℕ) : Cmd :=
  .seq (.assign (R + 2) (.read src (.op .sub (.reg R) (.const 1))))
    (.seq (.assign (R + 3) (.read src (.op .add (.reg R) (.const 1))))
      (.seq (liftChooseProg neighbours r_u r_v (R + 2) (R + 6) (R + 11))
        (.seq (liftChooseProg neighbours r_u r_v (R + 3) (R + 7) (R + 11))
          (.seq (liftPatchProg patch (R + 6) (R + 7))
            (.seq (.assign (R + 9) (.op .add (.reg R) (.const 1)))
              (.seq (liftSpliceProg src patch tmp R (R + 9) (R + 11))
                (liftCopyPathProg tmp src (R + 11))))))))

/-- The used-vertex case of Section 11 when both ends are off the cycle.
The hypotheses say only how the path, neighbour list, endpoints and internal position are
stored. The result is the prescribed prefix, short segment and suffix, with linear cost. -/
theorem liftOffOffUsedProg_exec {w : ℕ} (src neighbours patch tmp r_u r_v R : ℕ)
    (harr : [src, neighbours, patch, tmp].Nodup) (huR : r_u < R) (hvR : r_v < R)
    (L Nv : List ℕ) (u v i : ℕ) (s : State)
    (hsrc : s.arrs src = L) (hNv : s.arrs neighbours = Nv) (hnd : Nv.Nodup)
    (hu : s.regs r_u = u) (hv : s.regs r_v = v) (hpos : s.regs R = i)
    (hipos : 0 < i) (hinext : i + 1 < L.length)
    (hLw : ∀ x ∈ L, x < 2 ^ w) (hNw : ∀ x ∈ Nv, x < 2 ^ w)
    (huw : u < 2 ^ w) (hvw : v < 2 ^ w)
    (hw : 8 * (L.length + Nv.length + 2) < 2 ^ w) :
    let a := L[i - 1]'(by omega)
    let b := L[i + 1]
    let ua := if a ∈ Nv then v else u
    let ub := if b ∈ Nv then v else u
    let Y := if ua = ub then [ua] else [ua, ub]
    ∃ s' t, Exec w (liftOffOffUsedProg src neighbours patch tmp r_u r_v R) s s' t ∧
      t ≤ 50 * (L.length + Nv.length + 1) + 150 ∧
      s'.arrs src = L.take i ++ Y ++ L.drop (i + 1) ∧
      (∀ c, c ∉ [src, patch, tmp] → s'.arrs c = s.arrs c) ∧
      (∀ r < R, s'.regs r = s.regs r) := by
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil,
    not_or, not_false_eq_true, List.nodup_nil, and_true] at harr
  obtain ⟨⟨hsn, hsp, hst⟩, ⟨hnp, hnt⟩, hpt⟩ := harr
  dsimp only
  let a := L[i - 1]'(by omega)
  let b := L[i + 1]
  let ua := if a ∈ Nv then v else u
  let ub := if b ∈ Nv then v else u
  let Y := if ua = ub then [ua] else [ua, ub]
  have hi : i < L.length := by omega
  have hw1 : 1 < 2 ^ w := by omega
  have haw : a < 2 ^ w := hLw _ (List.getElem_mem (by omega))
  have hbw : b < 2 ^ w := hLw _ (List.getElem_mem hinext)
  have huaw : ua < 2 ^ w := by dsimp [ua]; split_ifs <;> assumption
  have hubw : ub < 2 ^ w := by dsimp [ub]; split_ifs <;> assumption
  have hYlen : Y.length ≤ 2 := by dsimp [Y]; split_ifs <;> simp
  have hYw : ∀ x ∈ Y, x < 2 ^ w := by
    intro x hx
    dsimp [Y] at hx
    split_ifs at hx <;> simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    · subst x; exact huaw
    · rcases hx with rfl | rfl; exact huaw; exact hubw
  let s1 := s.setReg (R + 2) a
  let s2 := s1.setReg (R + 3) b
  have hreadA : (Expr.read src (.op .sub (.reg R) (.const 1))).eval w s = some a := by
    have hbound : i - 1 < (s.arrs src).length := by rw [hsrc]; omega
    have he := eval_read (eval_sub (eval_reg hpos (by omega)) (eval_const hw1))
      hbound (by simpa only [hsrc] using haw)
    simpa only [hsrc] using he
  have hreadB : (Expr.read src (.op .add (.reg R) (.const 1))).eval w s1 = some b := by
    have hbound : i + 1 < (s1.arrs src).length := by simpa [s1, hsrc] using hinext
    have he := eval_read (w := w) (s := s1)
      (eval_add (eval_reg (r := R) (v := i) (by simp [s1, hpos]) (by omega)) (eval_const hw1) (by omega))
      hbound (by simpa only [s1, State.setReg_arrs, hsrc] using hbw)
    simpa only [s1, State.setReg_arrs, hsrc] using he
  have hu2 : s2.regs r_u = u := by
    simp [s2, s1, show r_u ≠ R + 3 by omega, show r_u ≠ R + 2 by omega, hu]
  have hv2 : s2.regs r_v = v := by
    simp [s2, s1, show r_v ≠ R + 3 by omega, show r_v ≠ R + 2 by omega, hv]
  obtain ⟨s3, t3, he3, ht3, ho3, ha3, hr3⟩ := liftChooseProg_exec
    neighbours r_u r_v (R + 2) (R + 6) (R + 11) (by omega) (by omega) (by omega)
    Nv u v a s2 hNv hnd hu2 hv2 (by simp [s2, s1]) hNw huw hvw haw (by omega)
  have hu3 : s3.regs r_u = u := (hr3 r_u (by omega) (by omega)).trans hu2
  have hv3 : s3.regs r_v = v := (hr3 r_v (by omega) (by omega)).trans hv2
  have hy3 : s3.regs (R + 3) = b := by
    rw [hr3 (R + 3) (by omega) (by omega)]; simp [s2]
  obtain ⟨s4, t4, he4, ht4, ho4, ha4, hr4⟩ := liftChooseProg_exec
    neighbours r_u r_v (R + 3) (R + 7) (R + 11) (by omega) (by omega) (by omega)
    Nv u v b s3 ((ha3 neighbours).trans hNv) hnd hu3 hv3 hy3 hNw huw hvw hbw (by omega)
  have hua4 : s4.regs (R + 6) = ua :=
    (hr4 (R + 6) (by omega) (by omega)).trans ho3
  have hub4 : s4.regs (R + 7) = ub := ho4
  obtain ⟨s5, t5, he5, ht5, hpatch5, ha5, hr5⟩ := liftPatchProg_exec
    patch (R + 6) (R + 7) ua ub s4 hua4 hub4 huaw hubw (by omega)
  have hsrc5 : s5.arrs src = L := by
    rw [ha5 src hsp, ha4 src, ha3 src]; exact hsrc
  have hpos5 : s5.regs R = i := by
    rw [hr5 R, hr4 R (by omega) (by omega), hr3 R (by omega) (by omega)]
    simp [s2, s1, hpos]
  let s6 := s5.setReg (R + 9) (i + 1)
  have he6 : Exec w (.assign (R + 9) (.op .add (.reg R) (.const 1))) s5 s6 4 :=
    .assign (eval_add (eval_reg hpos5 (by omega)) (eval_const hw1) (by omega))
  have hsplit : L = L.take i ++ [L[i]] ++ L.drop (i + 1) := by
    rw [List.append_assoc, List.singleton_append, ← List.drop_eq_getElem_cons hi]
    exact (List.take_append_drop i L).symm
  have htake : (L.take i).length = i := List.length_take_of_le (by omega)
  have hdrop : (L.drop (i + 1)).length = L.length - (i + 1) := List.length_drop
  have houtw : ∀ x ∈ L.take i ++ Y ++ L.drop (i + 1), x < 2 ^ w := by
    intro x hx
    rcases List.mem_append.mp hx with hx | hx
    · rcases List.mem_append.mp hx with hx | hx
      · exact hLw x (List.mem_of_mem_take hx)
      · exact hYw x hx
    · exact hLw x (List.mem_of_mem_drop hx)
  obtain ⟨s7, t7, he7, ht7, hout7, ha7, hr7⟩ := liftSpliceProg_exec
    src patch tmp R (R + 9) (R + 11) hst hpt (by omega) (by omega)
    (L.take i) [L[i]] Y (L.drop (i + 1)) s6
    (hsrc5.trans hsplit) hpatch5
    (by simp [s6, hpos5, htake]) (by simp [s6, htake]) houtw
    (by simp only [htake, List.length_singleton, hdrop]; omega)
  have h7len : (L.take i ++ Y ++ L.drop (i + 1)).length + 1 < 2 ^ w := by
    simp only [List.length_append, htake, hdrop]; omega
  obtain ⟨s8, t8, he8, ht8, hout8, ha8, hr8⟩ := liftCopyPathProg_exec
    tmp src (R + 11) (Ne.symm hst) (L.take i ++ Y ++ L.drop (i + 1)) s7 hout7 houtw h7len
  refine ⟨s8, 5 + (5 + (t3 + (t4 + (t5 + (4 + (t7 + t8)))))),
    .seq (.assign hreadA) (.seq (.assign hreadB) (.seq he3 (.seq he4
      (.seq he5 (.seq he6 (.seq he7 he8)))))), ?_, hout8, ?_, ?_⟩
  · simp only [List.length_append, htake, hdrop] at ht8
    omega
  · intro c hc
    simp only [List.mem_cons, List.not_mem_nil, not_or, not_false_eq_true, and_true] at hc
    rw [ha8 c hc.1, ha7 c hc.2.2]
    change s5.arrs c = s.arrs c
    rw [ha5 c hc.2.1, ha4 c, ha3 c]
    rfl
  · intro r hr
    rw [hr8 r (by omega), hr7 r (by omega)]
    simp only [s6, State.setReg_regs_ne _ _ (show r ≠ R + 9 by omega)]
    rw [hr5 r, hr4 r (by omega) (by omega), hr3 r (by omega) (by omega)]
    simp [s2, s1, show r ≠ R + 3 by omega, show r ≠ R + 2 by omega]

/-- The numerical list computation of the both-off-cycle case of Section 11. -/
def liftOffOffWords (u v : ℕ) (Nv L : List ℕ) : List ℕ :=
  if v ∈ L then
    let i := L.idxOf v
    let a := L.getD (i - 1) v
    let b := L.getD (i + 1) v
    let ua := if a ∈ Nv then v else u
    let ub := if b ∈ Nv then v else u
    L.take i ++ (if ua = ub then [ua] else [ua, ub]) ++ L.drop (i + 1)
  else L

/-- Scan for the merged vertex and perform the interior lift only when it occurs. -/
def liftOffOffProg (src neighbours patch tmp r_u r_v R : ℕ) : Cmd :=
  .seq (liftFindVertexProg src r_v R (R + 1))
    (.ite (.op .lt (.reg R) (.len src))
      (liftOffOffUsedProg src neighbours patch tmp r_u r_v R) .skip)

/-- The full both-off-cycle program, including the unused-vertex case. A used vertex must
be internal, as it is on a cycle path when the retained vertex is off the cycle. -/
theorem liftOffOffProg_exec {w : ℕ} (src neighbours patch tmp r_u r_v R : ℕ)
    (harr : [src, neighbours, patch, tmp].Nodup) (huR : r_u < R) (hvR : r_v < R)
    (L Nv : List ℕ) (u v : ℕ) (s : State)
    (hsrc : s.arrs src = L) (hNv : s.arrs neighbours = Nv) (hnd : Nv.Nodup)
    (hLnd : L.Nodup) (hu : s.regs r_u = u) (hv : s.regs r_v = v)
    (hinner : v ∈ L → 0 < L.idxOf v ∧ L.idxOf v + 1 < L.length)
    (hLw : ∀ x ∈ L, x < 2 ^ w) (hNw : ∀ x ∈ Nv, x < 2 ^ w)
    (huw : u < 2 ^ w) (hvw : v < 2 ^ w)
    (hw : 8 * (L.length + Nv.length + 2) < 2 ^ w) :
    ∃ s' t, Exec w (liftOffOffProg src neighbours patch tmp r_u r_v R) s s' t ∧
      t ≤ 70 * (L.length + Nv.length + 1) + 160 ∧
      s'.arrs src = liftOffOffWords u v Nv L ∧
      (∀ c, c ∉ [src, patch, tmp] → s'.arrs c = s.arrs c) ∧
      (∀ r < R, s'.regs r = s.regs r) := by
  have hw1 : 1 < 2 ^ w := by omega
  obtain ⟨s1, t1, he1, ht1, hp1, ha1, hr1⟩ := liftFindVertexProg_exec
    src r_v R (R + 1) (by omega) (by omega) (by omega) L v s hsrc hv hLnd hLw hvw (by omega)
  have hc := eval_lt (eval_reg hp1 (Nat.lt_of_le_of_lt List.idxOf_le_length (by omega)))
    (eval_len ((ha1 src).trans hsrc) (by omega)) hw1
  have hu1 : s1.regs r_u = u := (hr1 r_u (by omega) (by omega)).trans hu
  have hv1 : s1.regs r_v = v := (hr1 r_v (by omega) (by omega)).trans hv
  by_cases hmem : v ∈ L
  · obtain ⟨hpos, hnext⟩ := hinner hmem
    have hlt : L.idxOf v < L.length := List.idxOf_lt_length_iff.mpr hmem
    have hc1 : (Expr.op .lt (.reg R) (.len src)).eval w s1 = some 1 := by
      simpa only [hlt, ↓reduceIte] using hc
    obtain ⟨s2, t2, he2, ht2, ho2, ha2, hr2⟩ := liftOffOffUsedProg_exec
      src neighbours patch tmp r_u r_v R harr huR hvR L Nv u v (L.idxOf v) s1
      ((ha1 src).trans hsrc) ((ha1 neighbours).trans hNv) hnd hu1 hv1 hp1 hpos hnext
      hLw hNw huw hvw hw
    refine ⟨s2, t1 + (3 + t2), .seq he1 (.ite_true hc1 (by omega) he2), by omega, ?_, ?_, ?_⟩
    · simpa only [liftOffOffWords, hmem, ↓reduceIte,
        List.getD_eq_getElem L v (show L.idxOf v - 1 < L.length by omega),
        List.getD_eq_getElem L v hnext] using ho2
    · intro c hc; exact (ha2 c hc).trans (ha1 c)
    · intro r hr; exact (hr2 r hr).trans (hr1 r (by omega) (by omega))
  · have hlt : ¬ L.idxOf v < L.length := by rw [List.idxOf_eq_length hmem]; omega
    have hc0 : (Expr.op .lt (.reg R) (.len src)).eval w s1 = some 0 := by
      simpa only [hlt, ↓reduceIte] using hc
    refine ⟨s1, t1 + 4, .seq he1 (.ite_false hc0 (.skip s1)), by omega, ?_,
      fun c _ => ha1 c, ?_⟩
    · simpa only [liftOffOffWords, hmem, ↓reduceIte] using (ha1 src).trans hsrc
    · intro r hr; exact hr1 r (by omega) (by omega)

end GraphMinor.Compute.Crossing
