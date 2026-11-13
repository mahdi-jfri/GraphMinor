module

public import GraphMinor.Compute.Algorithm92Sweep

/-!
# Graph Minors XIII, (9.2): the numbers of the compressed vertices (`Algorithm92Rank.lean`)

The third program after `F` (page 101 of Graph Minors XIII) goes over the vertices `y < n` in
order. For each one it finds the vertex `rep y` that stands for the blob of `y`: `y` itself if `y`
is a node or lies on no path, and otherwise the last entry of the run of `y`, which the pass of
`Algorithm92Sweep.lean` located. The vertex `y` is a vertex of the compressed graph when it is a
node, or when it lies on a path and stands for itself. The program numbers these vertices in
increasing order (array `aRank`) and lists them (array `aE`).

The program is stated on plain functions (`rankProg_exec`).
-/

@[expose] public section

namespace GraphMinor.Compute

namespace Alg92

/-- The array of the vertices that stand for the blobs. -/
abbrev aRep : ℕ := 10
/-- The array of the numbers of the compressed vertices. -/
abbrev aRank : ℕ := 11
/-- The array of the compressed vertices, in increasing order. -/
abbrev aE : ℕ := 12
/-- The register that counts the compressed vertices. -/
abbrev rN : ℕ := 11

/-- Put `rep y` into `rtmp`, for `y` in `ri`. -/
def repCmd : Cmd :=
  .ite (.read aN (.reg ri)) (.assign rtmp (.reg ri))
    (.ite (.read aP (.reg ri)) (.assign rtmp (.read aL (.read aEn (.read aRS (.reg ri)))))
      (.assign rtmp (.reg ri)))

/-- One step of the numbering, at the vertex `ri`. -/
def rankBody : Cmd :=
  .seq repCmd <|
  .seq (.write aRep (.reg ri) (.reg rtmp)) <|
  .ite (.op .add (.read aN (.reg ri)) (.op .mul (.read aP (.reg ri)) (.op .eq (.reg rtmp) (.reg ri))))
    (.seq (.write aRank (.reg ri) (.reg rN)) <|
      .seq (.write aE (.reg rN) (.reg ri)) (.assign rN (.op .add (.reg rN) (.const 1))))
    .skip

/-- The numbering, with the allocation of its three arrays. -/
def rankProg : Cmd :=
  .seq (.alloc aRep (.reg rn)) <|
  .seq (.alloc aRank (.reg rn)) <|
  .seq (.alloc aE (.reg rn)) <|
  .seq (.assign rN (.const 0)) <|
  .seq (.assign ri (.const 0)) (forUp ri (.reg rn) rankBody)

variable (nd onp : ℕ → Bool) (rep : ℕ → ℕ)

/-- The vertex that stands for the blob of `y`. -/
def repv (y : ℕ) : ℕ := if nd y then y else if onp y then rep y else y

/-- The test for a vertex of the compressed graph. -/
def isV (y : ℕ) : Bool := nd y || (onp y && decide (repv nd onp rep y = y))

/-- The compressed vertices below `y`, in increasing order. -/
def vlist (y : ℕ) : List ℕ := (List.range y).filter (isV nd onp rep)

theorem vlist_succ (y : ℕ) : vlist nd onp rep (y + 1) =
    vlist nd onp rep y ++ (if isV nd onp rep y then [y] else []) := by
  unfold vlist
  rw [List.range_succ, List.filter_append]
  congr 1
  simp only [List.filter_cons, List.filter_nil]

variable {nd onp rep}

theorem repCmd_exec {w n M : ℕ} {s : State} {L : List ℕ} {rsA enA : ℕ → ℕ} {y : ℕ}
    (hri : s.regs ri = y) (hy : y < n)
    (hN : s.arrs aN = tab (n + 1) (fun v => if nd v then 1 else 0))
    (hP : s.arrs aP = tab (n + 1) (fun v => if onp v then 1 else 0))
    (hRS : s.arrs aRS = tab (n + 1) rsA) (hEn : s.arrs aEn = tab M enA) (hL : s.arrs aL = L)
    (hrep : nd y = false → onp y = true →
      rsA y < M ∧ enA (rsA y) < L.length ∧ L.getD (enA (rsA y)) 0 = rep y)
    (hB : M + L.length + n + 2 < 2 ^ w) (hLw : ∀ v ∈ L, v < 2 ^ w) :
    ∃ t, Exec w repCmd s (s.setReg rtmp (repv nd onp rep y)) t ∧ t ≤ 12 := by
  have hcN : (Expr.read aN (.reg ri)).eval w s = some (if nd y then 1 else 0) :=
    ev_read (ev_reg hri (by omega)) (by rw [hN, length_tab]; omega) (by rw [hN, getD_tab _ (by omega)])
      (by split_ifs <;> omega)
  have hcP : (Expr.read aP (.reg ri)).eval w s = some (if onp y then 1 else 0) :=
    ev_read (ev_reg hri (by omega)) (by rw [hP, length_tab]; omega) (by rw [hP, getD_tab _ (by omega)])
      (by split_ifs <;> omega)
  by_cases hnd : nd y = true
  · rw [if_pos hnd] at hcN
    rw [show repv nd onp rep y = y by simp [repv, hnd]]
    exact ⟨_, .ite_true hcN one_ne_zero (.assign (ev_reg hri (by omega))), by simp [Expr.cost]⟩
  · have hnd' : nd y = false := by simpa using hnd
    rw [if_neg hnd] at hcN
    by_cases hop : onp y = true
    · rw [if_pos hop] at hcP
      obtain ⟨h1, h2, h3⟩ := hrep hnd' hop
      have e1 : (Expr.read aRS (.reg ri)).eval w s = some (rsA y) :=
        ev_read (ev_reg hri (by omega)) (by rw [hRS]; simp; omega)
          (by rw [hRS, getD_tab _ (by omega)]) (by omega)
      have e2 : (Expr.read aEn (.read aRS (.reg ri))).eval w s = some (enA (rsA y)) :=
        ev_read e1 (by rw [hEn]; simp; omega) (by rw [hEn, getD_tab _ h1]) (by omega)
      have e3 : (Expr.read aL (.read aEn (.read aRS (.reg ri)))).eval w s = some (rep y) := by
        refine ev_read e2 (by rw [hL]; omega) (by rw [hL, h3]) ?_
        rw [← h3, List.getD_eq_getElem _ _ h2]; exact hLw _ (List.getElem_mem _)
      rw [show repv nd onp rep y = rep y by simp [repv, hnd', hop]]
      exact ⟨_, .ite_false hcN (.ite_true hcP one_ne_zero (.assign e3)), by simp [Expr.cost]⟩
    · rw [if_neg hop] at hcP
      have hop' : onp y = false := by simpa using hop
      rw [show repv nd onp rep y = y by simp [repv, hnd', hop']]
      exact ⟨_, .ite_false hcN (.ite_false hcP (.assign (ev_reg hri (by omega)))),
        by simp [Expr.cost]⟩

variable (nd onp rep) in
/-- The invariant of the numbering after `y` steps, from the start state `s0`. -/
def rankInv (n : ℕ) (s0 : State) (y : ℕ) (s : State) : Prop :=
  s.regs ri = y ∧ s.regs rN = (vlist nd onp rep y).length ∧
    s.arrs aRep = tab n (fun z => if z < y then repv nd onp rep z else 0) ∧
    s.arrs aRank = tab n (fun z => if z < y ∧ isV nd onp rep z then (vlist nd onp rep z).length
      else 0) ∧
    s.arrs aE = tab n (fun c => (vlist nd onp rep y).getD c 0) ∧
    (∀ a, a ≠ aRep → a ≠ aRank → a ≠ aE → s.arrs a = s0.arrs a) ∧
    (∀ q, q ≠ ri → q ≠ rN → q ≠ rtmp → s.regs q = s0.regs q)

theorem length_vlist_le (y : ℕ) : (vlist nd onp rep y).length ≤ y := by
  unfold vlist
  exact (List.length_filter_le _ _).trans (by simp)

theorem rankStep {w n M : ℕ} {s0 : State} {L : List ℕ} {rsA enA : ℕ → ℕ}
    (hN : s0.arrs aN = tab (n + 1) (fun v => if nd v then 1 else 0))
    (hP : s0.arrs aP = tab (n + 1) (fun v => if onp v then 1 else 0))
    (hRS : s0.arrs aRS = tab (n + 1) rsA) (hEn : s0.arrs aEn = tab M enA) (hL : s0.arrs aL = L)
    (hrep : ∀ y < n, nd y = false → onp y = true →
      rsA y < M ∧ enA (rsA y) < L.length ∧ L.getD (enA (rsA y)) 0 = rep y)
    (hrepn : ∀ y < n, rep y < 2 ^ w)
    (hB : M + L.length + n + 2 < 2 ^ w) (hLw : ∀ v ∈ L, v < 2 ^ w) {y : ℕ} (hy : y < n) :
    ⦃rankInv nd onp rep n s0 y⦄[w] rankBody
      ⦃fun s' => rankInv nd onp rep n s0 (y + 1) (s'.setReg ri (y + 1)) ∧ s'.regs ri = y⦄ ≤
        fun _ => 40 := by
  rintro s ⟨hri, hcnt, hRep, hRank, hE, ha, hr⟩
  have g : ∀ a, a ≠ aRep → a ≠ aRank → a ≠ aE → s.arrs a = s0.arrs a := ha
  obtain ⟨t1, ex1, ht1⟩ := repCmd_exec (rep := rep) hri hy (by rw [g aN (by decide) (by decide)
    (by decide), hN]) (by rw [g aP (by decide) (by decide) (by decide), hP])
    (by rw [g aRS (by decide) (by decide) (by decide), hRS])
    (by rw [g aEn (by decide) (by decide) (by decide), hEn])
    (by rw [g aL (by decide) (by decide) (by decide), hL]) (hrep y hy) hB hLw
  generalize hrv : repv nd onp rep y = rv at ex1
  have hrvw : rv < 2 ^ w := by
    rw [← hrv]; unfold repv; split_ifs
    · omega
    · exact hrepn y hy
    · omega
  generalize hs1 : s.setReg rtmp rv = s1 at ex1
  have hr1 : ∀ q, q ≠ rtmp → s1.regs q = s.regs q := fun q hq => by
    rw [← hs1, State.setReg_regs_ne _ _ hq]
  have ht1' : s1.regs rtmp = rv := by rw [← hs1]; simp
  have ha1 : ∀ a, s1.arrs a = s.arrs a := fun a => by rw [← hs1]; rfl
  have ex2 : Exec w (.write aRep (.reg ri) (.reg rtmp)) s1 (s1.writeArr aRep y rv) _ :=
    .write (ev_reg (by rw [hr1 ri (by decide), hri]) (by omega)) (ev_reg ht1' hrvw)
      (by rw [ha1, hRep, length_tab]; omega)
  have hRep2 := writeArr_tab (by rw [ha1, hRep]) hy rv (s := s1)
  generalize hs2 : s1.writeArr aRep y rv = s2 at ex2 hRep2
  have hr2 : s2.regs = s1.regs := by rw [← hs2]; rfl
  have ha2 : ∀ a, a ≠ aRep → s2.arrs a = s.arrs a := fun a h => by
    rw [← hs2, State.writeArr_arrs_ne _ _ _ h, ha1]
  have hri2 : s2.regs ri = y := by rw [hr2, hr1 ri (by decide), hri]
  have hRepF : Function.update (fun z => if z < y then repv nd onp rep z else 0) y rv =
      fun z => if z < y + 1 then repv nd onp rep z else 0 := by
    funext z; simp only [Function.update_apply]
    by_cases hz : z = y
    · subst hz; simp [hrv]
    · rw [if_neg hz]; congr 1; apply propext; omega
  rw [hRepF] at hRep2
  -- the test
  have hN2 : s2.arrs aN = tab (n + 1) (fun v => if nd v then 1 else 0) := by
    rw [ha2 aN (by decide), g aN (by decide) (by decide) (by decide), hN]
  have hP2 : s2.arrs aP = tab (n + 1) (fun v => if onp v then 1 else 0) := by
    rw [ha2 aP (by decide), g aP (by decide) (by decide) (by decide), hP]
  have eN : (Expr.read aN (.reg ri)).eval w s2 = some (if nd y then 1 else 0) :=
    ev_read (ev_reg hri2 (by omega)) (by rw [hN2, length_tab]; omega)
      (by rw [hN2, getD_tab _ (by omega)]) (by split_ifs <;> omega)
  have eP : (Expr.read aP (.reg ri)).eval w s2 = some (if onp y then 1 else 0) :=
    ev_read (ev_reg hri2 (by omega)) (by rw [hP2, length_tab]; omega)
      (by rw [hP2, getD_tab _ (by omega)]) (by split_ifs <;> omega)
  have eQ := ev_eq (ev_reg (by rw [hr2, ht1']) hrvw) (ev_reg hri2 (by omega)) (by omega)
    (s := s2) (w := w)
  have eC := ev_add eN (ev_mul eP eQ (by split_ifs <;> omega)) (by split_ifs <;> omega)
  have hC : (if nd y then 1 else 0) + (if onp y then 1 else 0) * (if rv = y then 1 else 0) = 0 ↔
      isV nd onp rep y = false := by
    unfold isV; rw [hrv]; cases nd y <;> cases onp y <;> by_cases h : rv = y <;> simp [h]
  have hfr : ∀ s3 : State, s3.regs ri = y → s3.arrs aRep = s2.arrs aRep →
      (∀ a, a ≠ aRank → a ≠ aE → s3.arrs a = s2.arrs a) →
      (∀ q, q ≠ rN → s3.regs q = s2.regs q) → (s3.regs rN = (vlist nd onp rep (y + 1)).length) →
      s3.arrs aRank = tab n (fun z => if z < y + 1 ∧ isV nd onp rep z then
        (vlist nd onp rep z).length else 0) →
      s3.arrs aE = tab n (fun c => (vlist nd onp rep (y + 1)).getD c 0) →
      rankInv nd onp rep n s0 (y + 1) (s3.setReg ri (y + 1)) ∧ s3.regs ri = y := by
    intro s3 e1 e2 e3 e4 e5 e6 e7
    refine ⟨⟨by simp, by rw [State.setReg_regs_ne _ _ (by decide), e5],
      by rw [State.setReg_arrs, e2, hRep2], by rw [State.setReg_arrs, e6],
      by rw [State.setReg_arrs, e7], fun a b1 b2 b3 => ?_, fun q c1 c2 c3 => ?_⟩, e1⟩
    · rw [State.setReg_arrs, e3 a b2 b3, ha2 a b1, ha a b1 b2 b3]
    · rw [State.setReg_regs_ne _ _ c1, e4 q c2, hr2, hr1 q c3, hr q c1 c2 c3]
  have hcnt2 : s2.regs rN = (vlist nd onp rep y).length := by
    rw [hr2, hr1 rN (by decide), hcnt]
  have hvl := length_vlist_le (nd := nd) (onp := onp) (rep := rep) y
  by_cases hV : isV nd onp rep y = true
  · have hc0 : (if nd y then 1 else 0) + (if onp y then 1 else 0) * (if rv = y then 1 else 0) ≠ 0 :=
      fun h0 => by rw [hC.mp h0] at hV; exact absurd hV (by simp)
    have ex3 : Exec w (.write aRank (.reg ri) (.reg rN)) s2
        (s2.writeArr aRank y (vlist nd onp rep y).length) _ :=
      .write (ev_reg hri2 (by omega)) (ev_reg hcnt2 (by omega))
        (by rw [ha2 aRank (by decide), hRank, length_tab]; omega)
    have hRank3 := writeArr_tab (by rw [ha2 aRank (by decide), hRank]) hy
      (vlist nd onp rep y).length (s := s2)
    generalize hs3 : s2.writeArr aRank y (vlist nd onp rep y).length = s3 at ex3 hRank3
    have hr3 : s3.regs = s2.regs := by rw [← hs3]; rfl
    have ex4 : Exec w (.write aE (.reg rN) (.reg ri)) s3
        (s3.writeArr aE (vlist nd onp rep y).length y) _ :=
      .write (ev_reg (by rw [hr3, hcnt2]) (by omega)) (ev_reg (by rw [hr3, hri2]) (by omega))
        (by rw [← hs3, State.writeArr_arrs_ne _ _ _ (by decide), ha2 aE (by decide), hE,
          length_tab]; omega)
    have hE3 : s3.arrs aE = tab n (fun c => (vlist nd onp rep y).getD c 0) := by
      rw [← hs3, State.writeArr_arrs_ne _ _ _ (by decide), ha2 aE (by decide), hE]
    have hE4 := writeArr_tab hE3 (show (vlist nd onp rep y).length < n by omega) y
    generalize hs4 : s3.writeArr aE (vlist nd onp rep y).length y = s4 at ex4 hE4
    have ex5 : Exec w (.assign rN (.op .add (.reg rN) (.const 1))) s4
        (s4.setReg rN ((vlist nd onp rep y).length + 1)) _ :=
      .assign (ev_add (ev_reg (by rw [← hs4, State.writeArr_regs, hr3, hcnt2]) (by omega))
        (ev_const (by omega)) (by omega))
    refine ⟨_, _, .seq ex1 (.seq ex2 (.ite_true eC hc0 (.seq ex3 (.seq ex4 ex5)))),
      by simp [Expr.cost] at ht1 ⊢; omega, hfr _ ?_ ?_ ?_ ?_ ?_ ?_ ?_⟩
    · rw [State.setReg_regs_ne _ _ (by decide), ← hs4, State.writeArr_regs, hr3, hri2]
    · rw [State.setReg_arrs, ← hs4, State.writeArr_arrs_ne _ _ _ (by decide), ← hs3,
        State.writeArr_arrs_ne _ _ _ (by decide)]
    · intro a b1 b2
      rw [State.setReg_arrs, ← hs4, State.writeArr_arrs_ne _ _ _ b2, ← hs3,
        State.writeArr_arrs_ne _ _ _ b1]
    · intro q hq
      rw [State.setReg_regs_ne _ _ hq, ← hs4, State.writeArr_regs, hr3]
    · rw [State.setReg_regs_self, vlist_succ, if_pos hV, List.length_append]; rfl
    · rw [State.setReg_arrs, ← hs4, State.writeArr_arrs_ne _ _ _ (by decide), hRank3]
      refine tab_congr fun z _ => ?_
      simp only [Function.update_apply]
      by_cases hz : z = y
      · subst hz; simp [hV]
      · rw [if_neg hz]; congr 1; apply propext
        constructor <;> rintro ⟨h1, h2⟩ <;> exact ⟨by omega, h2⟩
    · rw [State.setReg_arrs, hE4, vlist_succ, if_pos hV]
      refine tab_congr fun c _ => ?_
      simp only [Function.update_apply]
      by_cases hc : c = (vlist nd onp rep y).length
      · subst hc; simp
      · rw [if_neg hc]
        rcases Nat.lt_or_ge c (vlist nd onp rep y).length with h | h
        · rw [List.getD_append _ _ _ _ h]
        · rw [List.getD_eq_default _ _ h, List.getD_eq_default _ _ (by simp; omega)]
  · have hV' : isV nd onp rep y = false := by simpa using hV
    have hc0 := hC.mpr hV'
    rw [hc0] at eC
    refine ⟨_, _, .seq ex1 (.seq ex2 (.ite_false eC (.skip _))),
      by simp [Expr.cost] at ht1 ⊢; omega, hfr _ hri2 rfl (fun _ _ _ => rfl) (fun _ _ => rfl) ?_ ?_ ?_⟩
    · rw [hcnt2, vlist_succ, if_neg hV, List.append_nil]
    · rw [ha2 aRank (by decide), hRank]
      refine tab_congr fun z _ => ?_
      by_cases hz : z = y
      · subst hz; simp [hV']
      · congr 1; apply propext; constructor <;> rintro ⟨h1, h2⟩ <;> exact ⟨by omega, h2⟩
    · rw [ha2 aE (by decide), hE, vlist_succ, if_neg hV, List.append_nil]

theorem rankProg_exec {w n M : ℕ} {s : State} {L : List ℕ} {rsA enA : ℕ → ℕ}
    (hrn : s.regs rn = n)
    (hN : s.arrs aN = tab (n + 1) (fun v => if nd v then 1 else 0))
    (hP : s.arrs aP = tab (n + 1) (fun v => if onp v then 1 else 0))
    (hRS : s.arrs aRS = tab (n + 1) rsA) (hEn : s.arrs aEn = tab M enA) (hL : s.arrs aL = L)
    (hrep : ∀ y < n, nd y = false → onp y = true →
      rsA y < M ∧ enA (rsA y) < L.length ∧ L.getD (enA (rsA y)) 0 = rep y)
    (hrepn : ∀ y < n, rep y < 2 ^ w)
    (hB : M + L.length + n + 2 < 2 ^ w) (hLw : ∀ v ∈ L, v < 2 ^ w) :
    ∃ s' t, Exec w rankProg s s' t ∧ t ≤ 10 + 3 * n + 47 * n ∧
      s'.regs rN = (vlist nd onp rep n).length ∧
      s'.arrs aRep = tab n (repv nd onp rep) ∧
      s'.arrs aRank = tab n (fun z => if isV nd onp rep z then (vlist nd onp rep z).length else 0) ∧
      s'.arrs aE = tab n (fun c => (vlist nd onp rep n).getD c 0) ∧
      (∀ a, a ≠ aRep → a ≠ aRank → a ≠ aE → s'.arrs a = s.arrs a) ∧
      (∀ q, q ≠ ri → q ≠ rN → q ≠ rtmp → s'.regs q = s.regs q) := by
  have ex1 : Exec w (.alloc aRep (.reg rn)) s (s.setArr aRep (List.replicate n 0)) _ :=
    .alloc (ev_reg hrn (by omega))
  generalize hs1 : s.setArr aRep (List.replicate n 0) = s1 at ex1
  have ex2 : Exec w (.alloc aRank (.reg rn)) s1 (s1.setArr aRank (List.replicate n 0)) _ :=
    .alloc (ev_reg (by rw [← hs1]; simp [hrn]) (by omega))
  generalize hs2 : s1.setArr aRank (List.replicate n 0) = s2 at ex2
  have ex3 : Exec w (.alloc aE (.reg rn)) s2 (s2.setArr aE (List.replicate n 0)) _ :=
    .alloc (ev_reg (by rw [← hs2, ← hs1]; simp [hrn]) (by omega))
  generalize hs3 : s2.setArr aE (List.replicate n 0) = s3 at ex3
  have ex4 : Exec w (.assign rN (.const 0)) s3 (s3.setReg rN 0) _ := .assign (ev_const (by omega))
  have ex5 : Exec w (.assign ri (.const 0)) (s3.setReg rN 0) ((s3.setReg rN 0).setReg ri 0) _ :=
    .assign (ev_const (by omega))
  generalize hs5 : (s3.setReg rN 0).setReg ri 0 = s5 at ex5
  have ha5 : ∀ a, a ≠ aRep → a ≠ aRank → a ≠ aE → s5.arrs a = s.arrs a := fun a h1 h2 h3 => by
    rw [← hs5, ← hs3, ← hs2, ← hs1]
    simp [State.setArr_arrs_ne _ _ h1, State.setArr_arrs_ne _ _ h2, State.setArr_arrs_ne _ _ h3]
  have hr5 : ∀ q, q ≠ ri → q ≠ rN → s5.regs q = s.regs q := fun q h1 h2 => by
    rw [← hs5, ← hs3, ← hs2, ← hs1]
    simp [State.setReg_regs_ne _ _ h1, State.setReg_regs_ne _ _ h2]
  have hI0 : rankInv nd onp rep n s5 0 s5 := by
    refine ⟨by rw [← hs5]; simp, by rw [← hs5]; simp [vlist], ?_, ?_, ?_, fun _ _ _ _ => rfl,
      fun _ _ _ _ => rfl⟩
    · rw [← hs5, ← hs3, ← hs2, ← hs1]
      simp only [State.setReg_arrs, State.setArr_arrs_ne _ _ (show aRep ≠ aE by decide),
        State.setArr_arrs_ne _ _ (show aRep ≠ aRank by decide), State.setArr_arrs_self,
        replicate_eq_tab]
      exact tab_congr fun j _ => by simp
    · rw [← hs5, ← hs3, ← hs2]
      simp only [State.setReg_arrs, State.setArr_arrs_ne _ _ (show aRank ≠ aE by decide),
        State.setArr_arrs_self, replicate_eq_tab]
      exact tab_congr fun j _ => by simp
    · rw [← hs5, ← hs3]
      simp only [State.setReg_arrs, State.setArr_arrs_self, replicate_eq_tab]
      exact tab_congr fun j _ => by simp [vlist]
  have g : ∀ a, a ≠ aRep → a ≠ aRank → a ≠ aE → s5.arrs a = s.arrs a := ha5
  obtain ⟨s6, t6, ex6, ht6, hri6, hcnt6, hRep6, hRank6, hE6, ha6, hr6⟩ :=
    Triple.forUp_const (w := w) (rankInv nd onp rep n s5) n 40 (r_i := ri) (hi := .reg rn)
      (body := rankBody) (by omega) (by omega)
      (fun i _ s' hs' => ⟨hs'.1, ev_reg (by rw [hs'.2.2.2.2.2.2 rn (by decide) (by decide)
        (by decide), hr5 rn (by decide) (by decide), hrn]) (by omega)⟩)
      (fun i hi => rankStep (by rw [g aN (by decide) (by decide) (by decide), hN])
        (by rw [g aP (by decide) (by decide) (by decide), hP])
        (by rw [g aRS (by decide) (by decide) (by decide), hRS])
        (by rw [g aEn (by decide) (by decide) (by decide), hEn])
        (by rw [g aL (by decide) (by decide) (by decide), hL]) hrep hrepn hB hLw hi) s5 hI0
  refine ⟨s6, _, .seq ex1 (.seq ex2 (.seq ex3 (.seq ex4 (.seq ex5 ex6)))), ?_, hcnt6, ?_, ?_, hE6,
    fun a h1 h2 h3 => by rw [ha6 a h1 h2 h3, ha5 a h1 h2 h3],
    fun q h1 h2 h3 => by rw [hr6 q h1 h2 h3, hr5 q h1 h2]⟩
  · simp only [Expr.cost] at ht6 ⊢
    omega
  · rw [hRep6]; exact tab_congr fun z hz => by simp [hz]
  · rw [hRank6]; exact tab_congr fun z hz => by simp [hz]

end Alg92

end GraphMinor.Compute
