module

public import GraphMinor.Compute.Algorithm92LiftModel

/-!
# Graph Minors XIII, (9.2): lifting an `(l, m)`-star (`Algorithm92LiftStar.lean`)

When the stored answer of the compressed copy of `H ∪ F` is an `(l, m)`-star, written as
`0 :: c :: encHPaths rays`, the output for `G` is `0 :: node c :: encHPaths (liftRay ∘ rays)`
(`BlobMap.isStarRay_liftRay`, `Algorithm92Lift.lean`). Each vertex `v` of a ray after the first
is replaced by its piece: the node itself, or the run of `fE v` in the layout, read forwards or
backwards according to the vertex before it on the ray (`BlobMap.piece`).

This file holds the reverse copy (`copyRevProg`), the facts on appending to a written prefix, and
the program for one piece (`pieceCmd`).
-/

@[expose] public section

namespace GraphMinor.Compute

namespace Alg92

section Copy

variable {w : ℕ} {s : State}

/-- Copy `cnt` entries of `src`, read backwards from position `cur`, to `dst` from position
`pos` on. -/
def copyRevProg (src dst : Arr) (r_cur r_pos r_cnt r_t : Reg) : Cmd :=
  .seq (.assign r_t (.const 0))
    (forUp r_t (.reg r_cnt)
      (.write dst (.op .add (.reg r_pos) (.reg r_t)) (.read src (.op .sub (.reg r_cur) (.reg r_t)))))

theorem copyRevProg_exec (src dst r_cur r_pos r_cnt r_t : ℕ) (hsd : src ≠ dst)
    (hcp : r_t ≠ r_cur) (hpp : r_t ≠ r_pos) (hnp : r_t ≠ r_cnt)
    {m : ℕ} {f : ℕ → ℕ} {cur pos cnt : ℕ} {L : List ℕ}
    (hw : 1 < 2 ^ w) (hS : s.arrs src = L) (hD : s.arrs dst = tab m f)
    (hcur : s.regs r_cur = cur) (hpos : s.regs r_pos = pos) (hcnt : s.regs r_cnt = cnt)
    (hfit : pos + cnt ≤ m) (hsrc : cur < L.length) (hcc : cnt ≤ cur + 1) (hm : m + L.length < 2 ^ w)
    (hvals : ∀ v ∈ L, v < 2 ^ w) :
    ∃ s' t, Exec w (copyRevProg src dst r_cur r_pos r_cnt r_t) s s' t ∧ t ≤ 5 + 15 * cnt ∧
      s'.arrs dst = tab m (fun j => if pos ≤ j ∧ j < pos + cnt then L.getD (cur - (j - pos)) 0
        else f j) ∧
      (∀ a, a ≠ dst → s'.arrs a = s.arrs a) ∧ (∀ r, r ≠ r_t → s'.regs r = s.regs r) := by
  let I (i : ℕ) (s' : State) : Prop :=
    s'.regs r_t = i ∧
    s'.arrs dst = tab m (fun j => if pos ≤ j ∧ j < pos + i then L.getD (cur - (j - pos)) 0
      else f j) ∧
    (∀ a, a ≠ dst → s'.arrs a = s.arrs a) ∧ (∀ r, r ≠ r_t → s'.regs r = s.regs r)
  have hcnt_w : cnt < 2 ^ w := by omega
  have hloop : ⦃I 0⦄[w] forUp r_t (.reg r_cnt)
      (.write dst (.op .add (.reg r_pos) (.reg r_t)) (.read src (.op .sub (.reg r_cur) (.reg r_t))))
      ⦃I cnt⦄ ≤ fun _ => (Expr.reg r_cnt).cost + 2 + cnt * ((Expr.reg r_cnt).cost + 6 + 8) := by
    refine Triple.forUp_const I cnt 8 hw hcnt_w ?_ ?_
    · rintro i _ s' ⟨hi, -, -, hr⟩
      exact ⟨hi, ev_reg (by rw [hr r_cnt (Ne.symm hnp), hcnt]) hcnt_w⟩
    · intro i hi
      apply Triple.write
      rintro s' ⟨hit, hdst, harr, hreg⟩
      have hcur' : s'.regs r_cur = cur := by rw [hreg r_cur (Ne.symm hcp), hcur]
      have hpos' : s'.regs r_pos = pos := by rw [hreg r_pos (Ne.symm hpp), hpos]
      have hsrc' : s'.arrs src = L := by rw [harr src hsd, hS]
      have hidx : (Expr.op .add (.reg r_pos) (.reg r_t)).eval w s' = some (pos + i) :=
        ev_add (ev_reg hpos' (by omega)) (ev_reg hit (by omega)) (by omega)
      have hcidx : (Expr.op .sub (.reg r_cur) (.reg r_t)).eval w s' = some (cur - i) :=
        ev_sub (ev_reg hcur' (by omega)) (ev_reg hit (by omega))
      have hval : (Expr.read src (.op .sub (.reg r_cur) (.reg r_t))).eval w s' =
          some (L.getD (cur - i) 0) := by
        refine ev_read hcidx (by rw [hsrc']; omega) (by rw [hsrc']) ?_
        rw [List.getD_eq_getElem _ _ (by omega)]
        exact hvals _ (List.getElem_mem _)
      refine ⟨pos + i, L.getD (cur - i) 0, hidx, hval, by rw [hdst]; simp; omega, ?_,
        by simp [Expr.cost]⟩
      refine ⟨⟨by simp, ?_, fun a ha => ?_, fun r hr => ?_⟩, by simp [hit]⟩
      · simp only [State.setReg_arrs]
        rw [writeArr_tab hdst (by omega)]
        refine tab_congr fun j _ => ?_
        simp only [Function.update_apply]
        by_cases hj : j = pos + i
        · subst hj; simp
        · rw [if_neg hj]
          by_cases hj' : pos ≤ j ∧ j < pos + i
          · rw [if_pos hj', if_pos ⟨hj'.1, by omega⟩]
          · rw [if_neg hj', if_neg (by omega)]
      · simp only [State.setReg_arrs, State.writeArr, State.setArr]
        rw [Function.update_of_ne ha]
        exact harr a ha
      · simp only [State.setReg, State.writeArr, State.setArr, Function.update_of_ne hr]
        exact hreg r hr
  have hinit : ⦃fun s' => s' = s⦄[w] .assign r_t (.const 0) ⦃I 0⦄ ≤ fun _ => 2 := by
    apply Triple.assign
    rintro _ rfl
    refine ⟨0, ev_const (by omega), ⟨by simp, ?_, (fun a _ => by simp), (fun r hr => by
      simp [State.setReg, Function.update_of_ne hr])⟩, by simp [Expr.cost]⟩
    simp only [State.setReg_arrs, hD]
    exact tab_congr fun j _ => by rw [if_neg (by omega)]
  obtain ⟨s', t, hex, ht, hI⟩ := (hinit.seq_const₂ hloop) s rfl
  exact ⟨s', t, hex, by simp [Expr.cost] at ht; omega, hI.2.1, hI.2.2.1, hI.2.2.2⟩


end Copy

/-! ### Appending to a written prefix -/

theorem preTab_append_copy {P L : List ℕ} {M cur cnt : ℕ} (hcur : cur + cnt ≤ L.length)
    (hM : P.length + cnt ≤ M) :
    tab M (fun j => if P.length ≤ j ∧ j < P.length + cnt then L.getD (cur + (j - P.length)) 0
      else preTab P P.length j) =
    tab M (preTab (P ++ (L.drop cur).take cnt) (P ++ (L.drop cur).take cnt).length) := by
  refine tab_congr fun j _ => ?_
  simp only [preTab, List.length_append, List.length_take, List.length_drop]
  by_cases h1 : P.length ≤ j ∧ j < P.length + cnt
  · have hlt : j - P.length < ((L.drop cur).take cnt).length := by simp; omega
    rw [if_pos h1, if_pos (by omega), List.getD_append_right _ _ _ _ h1.1,
      List.getD_eq_getElem _ _ hlt, List.getElem_take, List.getElem_drop,
      List.getD_eq_getElem _ _ (by omega)]
  · rw [if_neg h1]
    by_cases h2 : j < P.length
    · rw [if_pos h2, if_pos (by omega), List.getD_append _ _ _ _ h2]
    · rw [if_neg h2, if_neg (by omega)]

theorem preTab_append_copyRev {P L : List ℕ} {M cur cnt : ℕ} (hcur : cur < L.length)
    (hcc : cnt ≤ cur + 1) (hM : P.length + cnt ≤ M) :
    tab M (fun j => if P.length ≤ j ∧ j < P.length + cnt then L.getD (cur - (j - P.length)) 0
      else preTab P P.length j) =
    tab M (preTab (P ++ ((L.drop (cur + 1 - cnt)).take cnt).reverse)
      (P ++ ((L.drop (cur + 1 - cnt)).take cnt).reverse).length) := by
  refine tab_congr fun j _ => ?_
  simp only [preTab, List.length_append, List.length_reverse, List.length_take, List.length_drop]
  by_cases h1 : P.length ≤ j ∧ j < P.length + cnt
  · have hlt : j - P.length < ((L.drop (cur + 1 - cnt)).take cnt).reverse.length := by
      simp; omega
    rw [if_pos h1, if_pos (by omega), List.getD_append_right _ _ _ _ h1.1,
      List.getD_eq_getElem _ _ hlt, List.getElem_reverse, List.getElem_take,
      List.getElem_drop, List.getD_eq_getElem _ _ (by omega)]
    congr 1
    simp only [List.length_take, List.length_drop]
    omega
  · rw [if_neg h1]
    by_cases h2 : j < P.length
    · rw [if_pos h2, if_pos (by omega), List.getD_append _ _ _ _ h2]
    · rw [if_neg h2, if_neg (by omega)]

/-! ### One piece -/

/-- The work array of the output. -/
abbrev aBuf : ℕ := 18
abbrev ry : ℕ := 13
abbrev rS : ℕ := 14
abbrev rE : ℕ := 15
abbrev rC : ℕ := 16
abbrev rv : ℕ := 17
abbrev rprev : ℕ := 18
abbrev rq : ℕ := 19

/-- The piece of the vertex `v` of a ray after the vertex `prev`, on plain functions. -/
def pieceN (E L : List ℕ) (nd : ℕ → Bool) (rsA enA rankA : ℕ → ℕ) (prev v : ℕ) : List ℕ :=
  if nd (E.getD v 0) then [E.getD v 0]
  else if rankA (L.getD (rsA (E.getD v 0) - 1) 0) = prev then
    (L.drop (rsA (E.getD v 0))).take (enA (rsA (E.getD v 0)) + 1 - rsA (E.getD v 0))
  else ((L.drop (rsA (E.getD v 0))).take (enA (rsA (E.getD v 0)) + 1 - rsA (E.getD v 0))).reverse

theorem length_pieceN_le {E L : List ℕ} {nd : ℕ → Bool} {rsA enA rankA : ℕ → ℕ} (prev v : ℕ) :
    (pieceN E L nd rsA enA rankA prev v).length ≤ L.length + 1 := by
  unfold pieceN
  split_ifs <;> simp <;> omega

/-- Write the piece of `rv` after `rprev` at position `rpos` of `aBuf`. -/
def pieceCmd : Cmd :=
  .seq (.assign ry (.read aE (.reg rv))) <|
  .ite (.read aN (.reg ry))
    (.seq (.write aBuf (.reg rpos) (.reg ry)) (.assign rpos (.op .add (.reg rpos) (.const 1)))) <|
  .seq (.assign rS (.read aRS (.reg ry))) <|
  .seq (.assign rE (.read aEn (.reg rS))) <|
  .seq (.assign rC (.op .sub (.op .add (.reg rE) (.const 1)) (.reg rS))) <|
  .seq (.ite (.op .eq (.read aRank (.read aL (.op .sub (.reg rS) (.const 1)))) (.reg rprev))
    (copyProg aL aBuf rS rpos rC rt) (copyRevProg aL aBuf rE rpos rC rt))
    (.assign rpos (.op .add (.reg rpos) (.reg rC)))

theorem pieceCmd_exec {w : ℕ} {s : State} {E L P : List ℕ} {nd : ℕ → Bool}
    {rsA enA rankA : ℕ → ℕ} {n Mb prev v : ℕ}
    (hE : s.arrs aE = tab n (fun c => E.getD c 0))
    (hN : s.arrs aN = tab (n + 1) (fun u => if nd u then 1 else 0))
    (hRS : s.arrs aRS = tab (n + 1) rsA) (hEn : s.arrs aEn = tab L.length enA)
    (hL : s.arrs aL = L) (hRank : s.arrs aRank = tab n rankA)
    (hBuf : s.arrs aBuf = tab Mb (preTab P P.length))
    (hrv : s.regs rv = v) (hrp : s.regs rprev = prev) (hpos : s.regs rpos = P.length)
    (hv : v < n) (hEv : E.getD v 0 < n)
    (hrun : nd (E.getD v 0) = false → 1 ≤ rsA (E.getD v 0) ∧
      rsA (E.getD v 0) ≤ enA (rsA (E.getD v 0)) ∧ enA (rsA (E.getD v 0)) < L.length ∧
      L.getD (rsA (E.getD v 0) - 1) 0 < n)
    (hfit : P.length + (L.length + 1) ≤ Mb) (hLw : ∀ u ∈ L, u < 2 ^ w)
    (hrk : ∀ u < n, rankA u < 2 ^ w) (hprev : prev < 2 ^ w)
    (hB : Mb + L.length + n + 4 < 2 ^ w) :
    ∃ s' t, Exec w pieceCmd s s' t ∧ t ≤ 45 + 15 * L.length ∧
      s'.arrs aBuf = tab Mb (preTab (P ++ pieceN E L nd rsA enA rankA prev v)
        (P ++ pieceN E L nd rsA enA rankA prev v).length) ∧
      s'.regs rpos = (P ++ pieceN E L nd rsA enA rankA prev v).length ∧
      (∀ a, a ≠ aBuf → s'.arrs a = s.arrs a) ∧
      (∀ q, q ≠ ry → q ≠ rS → q ≠ rE → q ≠ rC → q ≠ rt → q ≠ rpos → s'.regs q = s.regs q) := by
  generalize hy : E.getD v 0 = y at hEv hrun
  have ex1 : Exec w (.assign ry (.read aE (.reg rv))) s (s.setReg ry y) _ :=
    .assign (ev_read (ev_reg hrv (by omega)) (by rw [hE, length_tab]; omega)
      (by rw [hE, getD_tab _ hv, hy]) (by omega))
  generalize hs1 : s.setReg ry y = s1 at ex1
  have hr1 : ∀ q, q ≠ ry → s1.regs q = s.regs q := fun q h => by rw [← hs1, State.setReg_regs_ne _ _ h]
  have hy1 : s1.regs ry = y := by rw [← hs1]; simp
  have ha1 : ∀ a, s1.arrs a = s.arrs a := fun a => by rw [← hs1]; rfl
  have hc : (Expr.read aN (.reg ry)).eval w s1 = some (if nd y then 1 else 0) :=
    ev_read (ev_reg hy1 (by omega)) (by rw [ha1, hN, length_tab]; omega)
      (by rw [ha1, hN, getD_tab _ (by omega)]) (by split_ifs <;> omega)
  have hpos1 : s1.regs rpos = P.length := by rw [hr1 rpos (by decide), hpos]
  have hBuf1 : s1.arrs aBuf = tab Mb (preTab P P.length) := by rw [ha1, hBuf]
  by_cases hnd : nd y = true
  · rw [if_pos hnd] at hc
    have hpc : pieceN E L nd rsA enA rankA prev v = [y] := by simp only [pieceN, hy, hnd, if_true]
    rw [hpc]
    have exa : Exec w (.write aBuf (.reg rpos) (.reg ry)) s1 (s1.writeArr aBuf P.length y) _ :=
      .write (ev_reg hpos1 (by omega)) (ev_reg hy1 (by omega)) (by rw [hBuf1, length_tab]; omega)
    have exb : Exec w (.assign rpos (.op .add (.reg rpos) (.const 1))) (s1.writeArr aBuf P.length y)
        ((s1.writeArr aBuf P.length y).setReg rpos (P.length + 1)) _ :=
      .assign (ev_add (ev_reg (by rw [State.writeArr_regs, hpos1]) (by omega)) (ev_const (by omega))
        (by omega))
    refine ⟨_, _, .seq ex1 (.ite_true hc one_ne_zero (.seq exa exb)), by simp [Expr.cost]; omega, ?_,
      by simp, fun a h => ?_, fun q h1 h2 h3 h4 h5 h6 => ?_⟩
    · rw [State.setReg_arrs, writeArr_tab hBuf1 (by omega), preTab_snoc (by omega)]
    · rw [State.setReg_arrs, State.writeArr_arrs_ne _ _ _ h, ha1]
    · rw [State.setReg_regs_ne _ _ h6, State.writeArr_regs, hr1 q h1]
  · have hnd' : nd y = false := by simpa using hnd
    rw [if_neg hnd] at hc
    obtain ⟨h1, h2, h3, h4⟩ := hrun hnd'
    generalize hrs : rsA y = rs at h1 h2 h3 h4
    generalize hen : enA rs = en at h2 h3
    have ex2 : Exec w (.assign rS (.read aRS (.reg ry))) s1 (s1.setReg rS rs) _ :=
      .assign (ev_read (ev_reg hy1 (by omega)) (by rw [ha1, hRS, length_tab]; omega)
        (by rw [ha1, hRS, getD_tab _ (by omega), hrs]) (by omega))
    have ex3 : Exec w (.assign rE (.read aEn (.reg rS))) (s1.setReg rS rs)
        ((s1.setReg rS rs).setReg rE en) _ :=
      .assign (ev_read (ev_reg (v := rs) (by simp) (by omega))
        (by simp only [State.setReg_arrs]; rw [ha1, hEn, length_tab]; omega)
        (by simp only [State.setReg_arrs]; rw [ha1, hEn, getD_tab _ (by omega), hen]) (by omega))
    have ex4 : Exec w (.assign rC (.op .sub (.op .add (.reg rE) (.const 1)) (.reg rS)))
        ((s1.setReg rS rs).setReg rE en)
        (((s1.setReg rS rs).setReg rE en).setReg rC (en + 1 - rs)) _ :=
      .assign (ev_sub (ev_add (ev_reg (v := en) (by simp) (by omega)) (ev_const (by omega))
        (by omega)) (ev_reg (v := rs) (by simp [State.setReg_regs_ne]) (by omega)))
    generalize hs4 : ((s1.setReg rS rs).setReg rE en).setReg rC (en + 1 - rs) = s4 at ex4
    have ha4 : ∀ a, s4.arrs a = s.arrs a := fun a => by rw [← hs4]; simp [ha1]
    have hr4 : ∀ q, q ≠ ry → q ≠ rS → q ≠ rE → q ≠ rC → s4.regs q = s.regs q := fun q a b c d => by
      rw [← hs4, State.setReg_regs_ne _ _ d, State.setReg_regs_ne _ _ c,
        State.setReg_regs_ne _ _ b, hr1 q a]
    have hS4 : s4.regs rS = rs := by rw [← hs4]; simp [State.setReg_regs_ne]
    have hE4 : s4.regs rE = en := by rw [← hs4]; simp [State.setReg_regs_ne]
    have hC4 : s4.regs rC = en + 1 - rs := by rw [← hs4]; simp
    have hpos4 : s4.regs rpos = P.length := by
      rw [hr4 rpos (by decide) (by decide) (by decide) (by decide), hpos]
    have hL4 : s4.arrs aL = L := by rw [ha4, hL]
    have hBuf4 : s4.arrs aBuf = tab Mb (preTab P P.length) := by rw [ha4, hBuf]
    have hLr : L.getD (rs - 1) 0 < 2 ^ w := by omega
    have eL : (Expr.read aL (.op .sub (.reg rS) (.const 1))).eval w s4 = some (L.getD (rs - 1) 0) :=
      ev_read (ev_sub (ev_reg hS4 (by omega)) (ev_const (by omega))) (by rw [hL4]; omega)
        (by rw [hL4]) hLr
    have eK : (Expr.read aRank (.read aL (.op .sub (.reg rS) (.const 1)))).eval w s4 =
        some (rankA (L.getD (rs - 1) 0)) :=
      ev_read eL (by rw [ha4, hRank, length_tab]; omega) (by rw [ha4, hRank, getD_tab _ h4])
        (hrk _ h4)
    have ec := ev_eq eK (ev_reg (by rw [hr4 rprev (by decide) (by decide) (by decide)
      (by decide), hrp]) hprev) (by omega) (s := s4) (w := w)
    have hseg : (L.drop rs).take (en + 1 - rs) = (L.drop (en + 1 - (en + 1 - rs))).take (en + 1 - rs) := by
      congr 2; omega
    -- the copy, forwards or backwards
    have hcopy : ∃ s5 t5, Exec w (.ite (.op .eq (.read aRank (.read aL (.op .sub (.reg rS) (.const 1))))
        (.reg rprev)) (copyProg aL aBuf rS rpos rC rt) (copyRevProg aL aBuf rE rpos rC rt)) s4 s5 t5 ∧
        t5 ≤ 13 + 15 * L.length ∧
        s5.arrs aBuf = tab Mb (preTab (P ++ pieceN E L nd rsA enA rankA prev v)
          (P ++ pieceN E L nd rsA enA rankA prev v).length) ∧
        (∀ a, a ≠ aBuf → s5.arrs a = s4.arrs a) ∧ (∀ q, q ≠ rt → s5.regs q = s4.regs q) := by
      by_cases ho : rankA (L.getD (rs - 1) 0) = prev
      · rw [if_pos ho] at ec
        have hpc : pieceN E L nd rsA enA rankA prev v = (L.drop rs).take (en + 1 - rs) := by
          simp only [pieceN, hy, hnd', Bool.false_eq_true, if_false, hrs, hen, ho, if_true]
        obtain ⟨s5, t5, ex5, ht5, hB5, ha5, hr5⟩ := copyProg_exec (w := w) aL aBuf rS rpos rC rt
          (by decide) (by decide) (by decide) (by decide) (s := s4) (cur := rs) (pos := P.length)
          (cnt := en + 1 - rs) (by omega) hL4 hBuf4 hS4 hpos4 hC4 (by omega) (by omega) (by omega)
          hLw
        refine ⟨s5, _, .ite_true ec one_ne_zero ex5, by simp [Expr.cost]; omega, ?_, ha5, hr5⟩
        rw [hB5, preTab_append_copy (by omega) (by omega), hpc]
      · rw [if_neg ho] at ec
        have hpc : pieceN E L nd rsA enA rankA prev v =
            ((L.drop (en + 1 - (en + 1 - rs))).take (en + 1 - rs)).reverse := by
          simp only [pieceN, hy, hnd', Bool.false_eq_true, if_false, hrs, hen, ho]
          rw [hseg]
        obtain ⟨s5, t5, ex5, ht5, hB5, ha5, hr5⟩ := copyRevProg_exec (w := w) aL aBuf rE rpos rC rt
          (by decide) (by decide) (by decide) (by decide) (s := s4) (cur := en) (pos := P.length)
          (cnt := en + 1 - rs) (by omega) hL4 hBuf4 hE4 hpos4 hC4 (by omega) (by omega) (by omega)
          (by omega) hLw
        refine ⟨s5, _, .ite_false ec ex5, by simp [Expr.cost]; omega, ?_, ha5, hr5⟩
        rw [hB5, preTab_append_copyRev (by omega) (by omega) (by omega), hpc]
    obtain ⟨s5, t5, ex5, ht5, hB5, ha5, hr5⟩ := hcopy
    have hplen : (pieceN E L nd rsA enA rankA prev v).length = en + 1 - rs := by
      simp only [pieceN, hy, hnd', Bool.false_eq_true, if_false, hrs, hen]
      split_ifs <;> simp <;> omega
    have ex6 : Exec w (.assign rpos (.op .add (.reg rpos) (.reg rC))) s5
        (s5.setReg rpos (P.length + (en + 1 - rs))) _ :=
      .assign (ev_add (ev_reg (by rw [hr5 rpos (by decide), hpos4]) (by omega))
        (ev_reg (by rw [hr5 rC (by decide), hC4]) (by omega)) (by omega))
    refine ⟨_, _, .seq ex1 (.ite_false hc (.seq ex2 (.seq ex3 (.seq ex4 (.seq ex5 ex6))))),
      by simp only [Expr.cost] at ht5 ⊢; omega, by rw [State.setReg_arrs, hB5],
      by rw [State.setReg_regs_self, List.length_append, hplen], fun a h => ?_,
      fun q b1 b2 b3 b4 b5 b6 => ?_⟩
    · rw [State.setReg_arrs, ha5 a h, ha4]
    · rw [State.setReg_regs_ne _ _ b6, hr5 q b5, hr4 q b1 b2 b3 b4]

/-! ### One ray -/

variable (E L : List ℕ) (nd : ℕ → Bool) (rsA enA rankA : ℕ → ℕ) in
/-- The part of the lifted ray for the entry `t` of the ray `ray`. -/
def stepPiece (ray : List ℕ) (t : ℕ) : List ℕ :=
  if t = 0 then [E.getD (ray.getD 0 0) 0]
  else pieceN E L nd rsA enA rankA (ray.getD (t - 1) 0) (ray.getD t 0)

variable (E L : List ℕ) (nd : ℕ → Bool) (rsA enA rankA : ℕ → ℕ) in
/-- The lifted ray, on plain lists. -/
def liftN (ray : List ℕ) (t : ℕ) : List ℕ :=
  (List.range t).flatMap (stepPiece E L nd rsA enA rankA ray)

theorem liftN_succ {E L : List ℕ} {nd : ℕ → Bool} {rsA enA rankA : ℕ → ℕ} (ray : List ℕ) (t : ℕ) :
    liftN E L nd rsA enA rankA ray (t + 1) =
      liftN E L nd rsA enA rankA ray t ++ stepPiece E L nd rsA enA rankA ray t := by
  simp [liftN, List.range_succ, List.flatMap_append]

theorem length_stepPiece_le {E L : List ℕ} {nd : ℕ → Bool} {rsA enA rankA : ℕ → ℕ}
    (ray : List ℕ) (t : ℕ) : (stepPiece E L nd rsA enA rankA ray t).length ≤ L.length + 1 := by
  unfold stepPiece
  split_ifs
  · simp
  · exact length_pieceN_le _ _

/-- One step of a ray: the entry `ri` of the ray whose length is at position `rcur` of `aAns`. -/
def stepBody : Cmd :=
  .seq (.assign rv (.read aAns (.op .add (.op .add (.reg rcur) (.const 1)) (.reg ri)))) <|
  .ite (.op .eq (.reg ri) (.const 0))
    (.seq (.write aBuf (.reg rpos) (.read aE (.reg rv))) (.assign rpos (.op .add (.reg rpos) (.const 1))))
    (.seq (.assign rprev (.read aAns (.op .add (.reg rcur) (.reg ri)))) pieceCmd)

theorem tab_preTab_set {Q : List ℕ} {M i v : ℕ} (hi : i < Q.length) (hQ : Q.length ≤ M) :
    tab M (Function.update (preTab Q Q.length) i v) = tab M (preTab (Q.set i v) (Q.set i v).length) := by
  refine tab_congr fun j _ => ?_
  simp only [Function.update_apply, preTab, List.length_set]
  by_cases hj : j = i
  · subst hj; rw [if_pos rfl, if_pos hi, List.getD_eq_getElem _ _ (by simpa using hi)]; simp
  · rw [if_neg hj]
    split_ifs with h
    · rw [List.getD_eq_getElem _ _ h, List.getD_eq_getElem _ _ (by simpa using h),
        List.getElem_set_ne (Ne.symm hj)]
    · rfl

/-- The facts that the pieces need on an entry `v` of a ray. -/
def GoodV (E L : List ℕ) (nd : ℕ → Bool) (rsA enA : ℕ → ℕ) (n v : ℕ) : Prop :=
  v < n ∧ E.getD v 0 < n ∧ (nd (E.getD v 0) = false → 1 ≤ rsA (E.getD v 0) ∧
    rsA (E.getD v 0) ≤ enA (rsA (E.getD v 0)) ∧ enA (rsA (E.getD v 0)) < L.length ∧
    L.getD (rsA (E.getD v 0) - 1) 0 < n)

theorem stepBody_exec {w : ℕ} {s : State} {E L Q A ray : List ℕ} {nd : ℕ → Bool}
    {rsA enA rankA : ℕ → ℕ} {n Mb cur t : ℕ}
    (hE : s.arrs aE = tab n (fun c => E.getD c 0))
    (hN : s.arrs aN = tab (n + 1) (fun u => if nd u then 1 else 0))
    (hRS : s.arrs aRS = tab (n + 1) rsA) (hEn : s.arrs aEn = tab L.length enA)
    (hL : s.arrs aL = L) (hRank : s.arrs aRank = tab n rankA) (hA : s.arrs aAns = A)
    (hBuf : s.arrs aBuf = tab Mb (preTab Q Q.length))
    (hri : s.regs ri = t) (hcur : s.regs rcur = cur) (hpos : s.regs rpos = Q.length)
    (ht : t < ray.length) (hAlen : cur + 1 + ray.length ≤ A.length)
    (hray : ∀ t' < ray.length, A.getD (cur + 1 + t') 0 = ray.getD t' 0)
    (hgood : ∀ v ∈ ray, GoodV E L nd rsA enA n v)
    (hfit : Q.length + (L.length + 1) ≤ Mb) (hLw : ∀ u ∈ L, u < 2 ^ w)
    (hAw : ∀ u ∈ A, u < 2 ^ w) (hrk : ∀ u < n, rankA u < 2 ^ w)
    (hB : Mb + L.length + A.length + n + 4 < 2 ^ w) :
    ∃ s' t'', Exec w stepBody s s' t'' ∧ t'' ≤ 60 + 15 * L.length ∧
      s'.arrs aBuf = tab Mb (preTab (Q ++ stepPiece E L nd rsA enA rankA ray t)
        (Q ++ stepPiece E L nd rsA enA rankA ray t).length) ∧
      s'.regs rpos = (Q ++ stepPiece E L nd rsA enA rankA ray t).length ∧
      (∀ a, a ≠ aBuf → s'.arrs a = s.arrs a) ∧
      (∀ q, q ≠ ry → q ≠ rS → q ≠ rE → q ≠ rC → q ≠ rt → q ≠ rpos → q ≠ rv → q ≠ rprev →
        s'.regs q = s.regs q) := by
  have hgt := hgood _ (List.getElem_mem ht)
  rw [← List.getD_eq_getElem _ 0 ht] at hgt
  obtain ⟨hv1, hv2, hv3⟩ := hgt
  have hAv : A.getD (cur + 1 + t) 0 < 2 ^ w := by
    rw [List.getD_eq_getElem _ _ (by omega)]; exact hAw _ (List.getElem_mem _)
  have ex1 : Exec w (.assign rv (.read aAns (.op .add (.op .add (.reg rcur) (.const 1)) (.reg ri))))
      s (s.setReg rv (ray.getD t 0)) _ :=
    .assign (ev_read (ev_add (ev_add (ev_reg hcur (by omega)) (ev_const (by omega)) (by omega))
      (ev_reg hri (by omega)) (by omega)) (by rw [hA]; omega) (by rw [hA, hray t ht])
      (by rw [← hray t ht]; exact hAv))
  generalize hs1 : s.setReg rv (ray.getD t 0) = s1 at ex1
  have hr1 : ∀ q, q ≠ rv → s1.regs q = s.regs q := fun q h => by rw [← hs1, State.setReg_regs_ne _ _ h]
  have hv1' : s1.regs rv = ray.getD t 0 := by rw [← hs1]; simp
  have ha1 : ∀ a, s1.arrs a = s.arrs a := fun a => by rw [← hs1]; rfl
  have hc := ev_eq (ev_reg (by rw [hr1 ri (by decide), hri]) (by omega))
    (ev_const (v := 0) (by omega)) (by omega) (s := s1) (w := w)
  by_cases ht0 : t = 0
  · subst ht0
    rw [if_pos rfl] at hc
    have hsp : stepPiece E L nd rsA enA rankA ray 0 = [E.getD (ray.getD 0 0) 0] := by
      simp [stepPiece]
    rw [hsp]
    have exa : Exec w (.write aBuf (.reg rpos) (.read aE (.reg rv))) s1
        (s1.writeArr aBuf Q.length (E.getD (ray.getD 0 0) 0)) _ :=
      .write (ev_reg (by rw [hr1 rpos (by decide), hpos]) (by omega))
        (ev_read (ev_reg hv1' (by omega)) (by rw [ha1, hE, length_tab]; omega)
          (by rw [ha1, hE, getD_tab _ hv1]) (by omega))
        (by rw [ha1, hBuf, length_tab]; omega)
    have exb : Exec w (.assign rpos (.op .add (.reg rpos) (.const 1)))
        (s1.writeArr aBuf Q.length (E.getD (ray.getD 0 0) 0))
        ((s1.writeArr aBuf Q.length (E.getD (ray.getD 0 0) 0)).setReg rpos (Q.length + 1)) _ :=
      .assign (ev_add (ev_reg (by rw [State.writeArr_regs, hr1 rpos (by decide), hpos]) (by omega))
        (ev_const (by omega)) (by omega))
    refine ⟨_, _, .seq ex1 (.ite_true hc one_ne_zero (.seq exa exb)), by simp [Expr.cost]; omega,
      ?_, by simp, fun a h => ?_, fun q h1 h2 h3 h4 h5 h6 h7 h8 => ?_⟩
    · rw [State.setReg_arrs, writeArr_tab (by rw [ha1, hBuf]) (by omega), preTab_snoc (by omega)]
    · rw [State.setReg_arrs, State.writeArr_arrs_ne _ _ _ h, ha1]
    · rw [State.setReg_regs_ne _ _ h6, State.writeArr_regs, hr1 q h7]
  · rw [if_neg ht0] at hc
    have hsp : stepPiece E L nd rsA enA rankA ray t =
        pieceN E L nd rsA enA rankA (ray.getD (t - 1) 0) (ray.getD t 0) := by
      simp [stepPiece, ht0]
    rw [hsp]
    have hprev := hray (t - 1) (by omega)
    rw [show cur + 1 + (t - 1) = cur + t by omega] at hprev
    have hAp : A.getD (cur + t) 0 < 2 ^ w := by
      rw [List.getD_eq_getElem _ _ (by omega)]; exact hAw _ (List.getElem_mem _)
    have exa : Exec w (.assign rprev (.read aAns (.op .add (.reg rcur) (.reg ri)))) s1
        (s1.setReg rprev (ray.getD (t - 1) 0)) _ :=
      .assign (ev_read (ev_add (ev_reg (by rw [hr1 rcur (by decide), hcur]) (by omega))
        (ev_reg (by rw [hr1 ri (by decide), hri]) (by omega)) (by omega))
        (by rw [ha1, hA]; omega) (by rw [ha1, hA, hprev]) (by rw [← hprev]; exact hAp))
    generalize hs2 : s1.setReg rprev (ray.getD (t - 1) 0) = s2 at exa
    have ha2 : ∀ a, s2.arrs a = s.arrs a := fun a => by rw [← hs2]; simp [ha1]
    obtain ⟨s3, t3, ex3, ht3, hB3, hpos3, ha3, hr3⟩ := pieceCmd_exec (w := w) (s := s2) (E := E)
      (L := L) (P := Q) (nd := nd) (rsA := rsA) (enA := enA) (rankA := rankA) (n := n) (Mb := Mb)
      (prev := ray.getD (t - 1) 0) (v := ray.getD t 0)
      (by rw [ha2, hE]) (by rw [ha2, hN]) (by rw [ha2, hRS]) (by rw [ha2, hEn]) (by rw [ha2, hL])
      (by rw [ha2, hRank]) (by rw [ha2, hBuf])
      (by rw [← hs2, State.setReg_regs_ne _ _ (by decide), hv1'])
      (by rw [← hs2]; simp)
      (by rw [← hs2, State.setReg_regs_ne _ _ (by decide), hr1 rpos (by decide), hpos])
      hv1 hv2 hv3 hfit hLw hrk (by rw [← hprev]; exact hAp) (by omega)
    refine ⟨s3, _, .seq ex1 (.ite_false hc (.seq exa ex3)), by simp only [Expr.cost] at ht3 ⊢; omega,
      hB3, hpos3, fun a h => by rw [ha3 a h, ha2], fun q h1 h2 h3 h4 h5 h6 h7 h8 => ?_⟩
    rw [hr3 q h1 h2 h3 h4 h5 h6, ← hs2, State.setReg_regs_ne _ _ h8, hr1 q h7]

theorem length_liftN_le {E L : List ℕ} {nd : ℕ → Bool} {rsA enA rankA : ℕ → ℕ} (ray : List ℕ) :
    ∀ t, (liftN E L nd rsA enA rankA ray t).length ≤ t * (L.length + 1)
  | 0 => by simp [liftN]
  | t + 1 => by
    rw [liftN_succ, List.length_append, Nat.add_mul, Nat.one_mul]
    have := length_liftN_le (E := E) (L := L) (nd := nd) (rsA := rsA) (enA := enA)
      (rankA := rankA) ray t
    have := length_stepPiece_le (E := E) (L := L) (nd := nd) (rsA := rsA) (enA := enA)
      (rankA := rankA) ray t
    omega

/-- Write one lifted ray, with its length in front. -/
def rayBody : Cmd :=
  .seq (.assign rcnt (.read aAns (.reg rcur))) <|
  .seq (.assign rq (.reg rpos)) <|
  .seq (.write aBuf (.reg rpos) (.const 0)) <|
  .seq (.assign rpos (.op .add (.reg rpos) (.const 1))) <|
  .seq (.assign ri (.const 0)) <|
  .seq (forUp ri (.reg rcnt) stepBody) <|
  .seq (.write aBuf (.reg rq) (.op .sub (.op .sub (.reg rpos) (.reg rq)) (.const 1)))
    (.assign rcur (.op .add (.op .add (.reg rcur) (.const 1)) (.reg rcnt)))

theorem rayBody_exec {w : ℕ} {s : State} {E L P A ray : List ℕ} {nd : ℕ → Bool}
    {rsA enA rankA : ℕ → ℕ} {n Mb cur : ℕ}
    (hE : s.arrs aE = tab n (fun c => E.getD c 0))
    (hN : s.arrs aN = tab (n + 1) (fun u => if nd u then 1 else 0))
    (hRS : s.arrs aRS = tab (n + 1) rsA) (hEn : s.arrs aEn = tab L.length enA)
    (hL : s.arrs aL = L) (hRank : s.arrs aRank = tab n rankA) (hA : s.arrs aAns = A)
    (hBuf : s.arrs aBuf = tab Mb (preTab P P.length))
    (hcur : s.regs rcur = cur) (hpos : s.regs rpos = P.length)
    (hAlen : cur + 1 + ray.length ≤ A.length) (hcnt : A.getD cur 0 = ray.length)
    (hray : ∀ t' < ray.length, A.getD (cur + 1 + t') 0 = ray.getD t' 0)
    (hgood : ∀ v ∈ ray, GoodV E L nd rsA enA n v)
    (hfit : P.length + 1 + ray.length * (L.length + 1) ≤ Mb) (hLw : ∀ u ∈ L, u < 2 ^ w)
    (hAw : ∀ u ∈ A, u < 2 ^ w) (hrk : ∀ u < n, rankA u < 2 ^ w)
    (hB : Mb + L.length + A.length + n + 4 < 2 ^ w) :
    ∃ s' t'', Exec w rayBody s s' t'' ∧ t'' ≤ 30 + ray.length * (67 + 15 * L.length) ∧
      s'.arrs aBuf = tab Mb (preTab (P ++ (liftN E L nd rsA enA rankA ray ray.length).length ::
          liftN E L nd rsA enA rankA ray ray.length)
        (P ++ (liftN E L nd rsA enA rankA ray ray.length).length ::
          liftN E L nd rsA enA rankA ray ray.length).length) ∧
      s'.regs rpos = (P ++ (liftN E L nd rsA enA rankA ray ray.length).length ::
          liftN E L nd rsA enA rankA ray ray.length).length ∧
      s'.regs rcur = cur + 1 + ray.length ∧
      (∀ a, a ≠ aBuf → s'.arrs a = s.arrs a) ∧
      (∀ q, q ≠ ry → q ≠ rS → q ≠ rE → q ≠ rC → q ≠ rt → q ≠ rpos → q ≠ rv → q ≠ rprev →
        q ≠ rcnt → q ≠ rq → q ≠ ri → q ≠ rcur → s'.regs q = s.regs q) := by
  have hAc : A.getD cur 0 < 2 ^ w := by
    rw [List.getD_eq_getElem _ _ (by omega)]; exact hAw _ (List.getElem_mem _)
  have ex1 : Exec w (.assign rcnt (.read aAns (.reg rcur))) s (s.setReg rcnt ray.length) _ :=
    .assign (ev_read (ev_reg hcur (by omega)) (by rw [hA]; omega) (by rw [hA, hcnt])
      (by rw [← hcnt]; exact hAc))
  have ex2 : Exec w (.assign rq (.reg rpos)) (s.setReg rcnt ray.length)
      ((s.setReg rcnt ray.length).setReg rq P.length) _ :=
    .assign (ev_reg (by rw [State.setReg_regs_ne _ _ (by decide), hpos]) (by omega))
  generalize hs2 : (s.setReg rcnt ray.length).setReg rq P.length = s2 at ex2
  have ex3 : Exec w (.write aBuf (.reg rpos) (.const 0)) s2 (s2.writeArr aBuf P.length 0) _ :=
    .write (ev_reg (by rw [← hs2]; simp [State.setReg_regs_ne, hpos]) (by omega))
      (ev_const (by omega)) (by rw [← hs2]; simp [hBuf]; omega)
  have ex4 : Exec w (.assign rpos (.op .add (.reg rpos) (.const 1))) (s2.writeArr aBuf P.length 0)
      ((s2.writeArr aBuf P.length 0).setReg rpos (P.length + 1)) _ :=
    .assign (ev_add (ev_reg (by rw [← hs2]; simp [State.setReg_regs_ne, hpos]) (by omega))
      (ev_const (by omega)) (by omega))
  have ex5 : Exec w (.assign ri (.const 0)) ((s2.writeArr aBuf P.length 0).setReg rpos (P.length + 1))
      (((s2.writeArr aBuf P.length 0).setReg rpos (P.length + 1)).setReg ri 0) _ :=
    .assign (ev_const (by omega))
  generalize hs5 : ((s2.writeArr aBuf P.length 0).setReg rpos (P.length + 1)).setReg ri 0 = s5 at ex5
  have ha5 : ∀ a, a ≠ aBuf → s5.arrs a = s.arrs a := fun a h => by
    rw [← hs5, ← hs2]; simp [State.writeArr_arrs_ne _ _ _ h]
  have hr5 : ∀ q, q ≠ rcnt → q ≠ rq → q ≠ rpos → q ≠ ri → s5.regs q = s.regs q := fun q a b c d => by
    rw [← hs5, ← hs2]; simp [State.setReg_regs_ne _ _ a, State.setReg_regs_ne _ _ b,
      State.setReg_regs_ne _ _ c, State.setReg_regs_ne _ _ d]
  have hBuf5 : s5.arrs aBuf = tab Mb (preTab (P ++ [0] ++ liftN E L nd rsA enA rankA ray 0)
      (P ++ [0] ++ liftN E L nd rsA enA rankA ray 0).length) := by
    rw [← hs5, ← hs2]
    simp only [State.setReg_arrs, liftN, List.range_zero, List.flatMap_nil, List.append_nil]
    rw [writeArr_tab (f := preTab P P.length) (m := Mb) (by simp [hBuf])
      (show P.length < Mb by omega), preTab_snoc (by omega)]
  let J (t : ℕ) (u : State) : Prop :=
    u.regs ri = t ∧ u.regs rcur = cur ∧ u.regs rq = P.length ∧ u.regs rcnt = ray.length ∧
      u.regs rpos = (P ++ [0] ++ liftN E L nd rsA enA rankA ray t).length ∧
      u.arrs aBuf = tab Mb (preTab (P ++ [0] ++ liftN E L nd rsA enA rankA ray t)
        (P ++ [0] ++ liftN E L nd rsA enA rankA ray t).length) ∧
      (∀ a, a ≠ aBuf → u.arrs a = s.arrs a) ∧
      (∀ q, q ≠ ry → q ≠ rS → q ≠ rE → q ≠ rC → q ≠ rt → q ≠ rpos → q ≠ rv → q ≠ rprev →
        q ≠ ri → u.regs q = s5.regs q)
  have hJ0 : J 0 s5 := ⟨by rw [← hs5]; simp,
    by rw [hr5 rcur (by decide) (by decide) (by decide) (by decide), hcur],
    by rw [← hs5, ← hs2]; simp [State.setReg_regs_ne], by rw [← hs5, ← hs2]; simp [State.setReg_regs_ne],
    by rw [← hs5]; simp [liftN], hBuf5, ha5, fun _ _ _ _ _ _ _ _ _ _ => rfl⟩
  obtain ⟨s6, t6, ex6, ht6, hri6, hcur6, hq6, hcnt6, hpos6, hBuf6, ha6, hr6⟩ :=
    Triple.forUp_const (w := w) J ray.length (60 + 15 * L.length) (r_i := ri) (hi := .reg rcnt)
      (body := stepBody) (by omega) (by omega)
      (fun t _ u hu => ⟨hu.1, ev_reg hu.2.2.2.1 (by omega)⟩) (fun t ht => by
        rintro u ⟨hu1, hu2, hu3, hu4, hu5, hu6, hu7, hu8⟩
        have hlen := length_liftN_le (E := E) (L := L) (nd := nd) (rsA := rsA) (enA := enA)
          (rankA := rankA) ray t
        have hmul : t * (L.length + 1) + (L.length + 1) ≤ ray.length * (L.length + 1) := by
          rw [← Nat.succ_mul]; exact Nat.mul_le_mul_right _ ht
        obtain ⟨u', t', ex', ht', hB', hpos', ha', hr'⟩ := stepBody_exec (w := w) (s := u)
          (Q := P ++ [0] ++ liftN E L nd rsA enA rankA ray t) (A := A) (ray := ray) (t := t)
          (by rw [hu7 aE (by decide), hE]) (by rw [hu7 aN (by decide), hN])
          (by rw [hu7 aRS (by decide), hRS]) (by rw [hu7 aEn (by decide), hEn])
          (by rw [hu7 aL (by decide), hL]) (by rw [hu7 aRank (by decide), hRank])
          (by rw [hu7 aAns (by decide), hA]) hu6 hu1 hu2 hu5 ht hAlen hray hgood
          (by simp only [List.length_append, List.length_singleton]; omega) hLw hAw hrk hB
        refine ⟨u', t', ex', ht', ⟨by simp, ?_, ?_, ?_, ?_, ?_, fun a h => ?_, ?_⟩, ?_⟩
        · rw [State.setReg_regs_ne _ _ (by decide), hr' rcur (by decide) (by decide) (by decide)
            (by decide) (by decide) (by decide) (by decide) (by decide), hu2]
        · rw [State.setReg_regs_ne _ _ (by decide), hr' rq (by decide) (by decide) (by decide)
            (by decide) (by decide) (by decide) (by decide) (by decide), hu3]
        · rw [State.setReg_regs_ne _ _ (by decide), hr' rcnt (by decide) (by decide) (by decide)
            (by decide) (by decide) (by decide) (by decide) (by decide), hu4]
        · rw [State.setReg_regs_ne _ _ (by decide), hpos', liftN_succ, List.append_assoc]
        · rw [State.setReg_arrs, hB', liftN_succ, List.append_assoc]
        · rw [State.setReg_arrs, ha' a h, hu7 a h]
        · intro q b1 b2 b3 b4 b5 b6 b7 b8 b9
          rw [State.setReg_regs_ne _ _ b9, hr' q b1 b2 b3 b4 b5 b6 b7 b8, hu8 q b1 b2 b3 b4 b5 b6 b7
            b8 b9]
        · rw [hr' ri (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
            (by decide) (by decide), hu1]) s5 hJ0
  generalize hX : liftN E L nd rsA enA rankA ray ray.length = X at hpos6 hBuf6
  have hXlen : X.length ≤ ray.length * (L.length + 1) := by
    rw [← hX]; exact length_liftN_le ray ray.length
  have ex7 : Exec w (.write aBuf (.reg rq) (.op .sub (.op .sub (.reg rpos) (.reg rq)) (.const 1))) s6
      (s6.writeArr aBuf P.length X.length) ((Expr.reg rq).cost +
        (Expr.op .sub (.op .sub (.reg rpos) (.reg rq)) (.const 1)).cost + 1) := by
    have e := ev_sub (ev_sub (ev_reg hpos6 (by simp; omega)) (ev_reg hq6 (by omega)))
      (ev_const (v := 1) (by omega)) (w := w) (s := s6)
    have hlenX : (P ++ [0] ++ X).length - P.length - 1 = X.length := by simp
    rw [hlenX] at e
    exact .write (ev_reg hq6 (by omega)) e (by rw [hBuf6, length_tab]; omega)
  have ex8 : Exec w (.assign rcur (.op .add (.op .add (.reg rcur) (.const 1)) (.reg rcnt)))
      (s6.writeArr aBuf P.length X.length)
      ((s6.writeArr aBuf P.length X.length).setReg rcur (cur + 1 + ray.length)) _ :=
    .assign (ev_add (ev_add (ev_reg (by simp [hcur6]) (by omega)) (ev_const (by omega)) (by omega))
      (ev_reg (by simp [hcnt6]) (by omega)) (by omega))
  refine ⟨_, _, .seq ex1 (.seq ex2 (.seq ex3 (.seq ex4 (.seq ex5 (.seq ex6 (.seq ex7 ex8)))))),
    ?_, ?_, ?_, by simp, fun a h => ?_, fun q h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 => ?_⟩
  · simp only [Expr.cost] at ht6 ⊢
    nlinarith
  · have hset : (P ++ [0] ++ X).set P.length X.length = P ++ X.length :: X := by
      rw [List.append_assoc, List.set_append_right _ _ (by omega), Nat.sub_self]; simp
    rw [State.setReg_arrs, writeArr_tab hBuf6 (by omega),
      tab_preTab_set (by simp) (by simp; omega), hset]
  · rw [State.setReg_regs_ne _ _ (by decide), State.writeArr_regs, hpos6]
    simp
  · rw [State.setReg_arrs, State.writeArr_arrs_ne _ _ _ h, ha6 a h]
  · rw [State.setReg_regs_ne _ _ h12, State.writeArr_regs, hr6 q h1 h2 h3 h4 h5 h6 h7 h8 h11,
      hr5 q h9 h10 h6 h11]

end Alg92

end GraphMinor.Compute
