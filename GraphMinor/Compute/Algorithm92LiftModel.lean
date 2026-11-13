module

public import GraphMinor.Compute.Algorithm92Dispatch

/-!
# Graph Minors XIII, (9.2): lifting a model of `K_p` (`Algorithm92LiftModel.lean`)

When the stored answer of the compressed copy of `H ∪ F` is a model of `K_p`, written as
`1 :: encBitSetsUpTo K p`, the output for `G` is `1 :: encBitSetsUpTo (fun i => liftSet (K i)) p`
(`BlobMap.isCliqueModel_liftSets`, `Algorithm92Lift.lean`). A vertex `y` of `G` lies in the lift
of `K i` exactly when it is a node or lies on a path, and the number of `cRep y` is in `K i`. The
program (`modelProg`) writes these bits, reading the number of `cRep y` from the arrays `aRep`
and `aRank`.
-/

@[expose] public section

namespace GraphMinor.Compute

namespace Alg92

/-- The register of the outer loop. -/
abbrev rO : ℕ := 12

theorem getD_encBitSetsUpTo {n p : ℕ} (X : Fin p → Finset (Fin n)) :
    ∀ (j : ℕ) (_hj : j ≤ p) {i y : ℕ} (hi : i < j) (hy : y < n),
      (encBitSetsUpTo X j).getD (i * n + y) 0 = if ⟨y, hy⟩ ∈ X ⟨i, by omega⟩ then 1 else 0
  | 0, _, _, _, hi, _ => absurd hi (Nat.not_lt_zero _)
  | j + 1, hj, i, y, hi, hy => by
    have hjp : j < p := by omega
    simp only [encBitSetsUpTo, hjp, dite_true]
    have hlen := length_encBitSetsUpTo X j (by omega)
    by_cases hij : i = j
    · subst hij
      rw [List.getD_append_right _ _ _ _ (by rw [hlen]; omega), hlen, Nat.add_sub_cancel_left,
        List.getD_eq_getElem _ _ (by simpa using hy)]
      simp [bitSetList]
    · have hlt : i * n + y < (encBitSetsUpTo X j).length := by
        rw [hlen]
        have : (i + 1) * n ≤ j * n := Nat.mul_le_mul_right _ (by omega)
        rw [Nat.add_mul, Nat.one_mul] at this; omega
      rw [List.getD_append _ _ _ _ hlt]
      exact getD_encBitSetsUpTo X j (by omega) (by omega) hy

/-- One bit of the output: the bit of the vertex `ri` for the branch set `rO`. -/
def modelBody : Cmd :=
  .ite (.op .add (.read aN (.reg ri)) (.read aP (.reg ri)))
    (.write outArr (.op .add (.op .add (.const 1) (.op .mul (.reg rO) (.reg rn))) (.reg ri))
      (.read aAns (.op .add (.op .add (.const 1) (.op .mul (.reg rO) (.reg rN)))
        (.read aRank (.read aRep (.reg ri))))))
    .skip

/-- The program that writes the lifted model. -/
def modelProg (p : ℕ) : Cmd :=
  .seq (.alloc outArr (.op .add (.const 1) (.op .mul (.const p) (.reg rn)))) <|
  .seq (.write outArr (.const 0) (.const 1)) <|
  .seq (.assign rO (.const 0))
    (forUp rO (.const p) (.seq (.assign ri (.const 0)) (forUp ri (.reg rn) modelBody)))

variable {n N p : ℕ} {nd onp : ℕ → Bool} {repA rankA : ℕ → ℕ} {A : List ℕ}

variable (n N nd onp repA rankA A) in
/-- The bit of the vertex `y` for the branch set `i`. -/
def mbit (i y : ℕ) : ℕ := if nd y || onp y then A.getD (1 + i * N + rankA (repA y)) 0 else 0

variable (n N nd onp repA rankA A) in
/-- The output after the bits before position `q` are written. -/
def mOut (q : ℕ) (j : ℕ) : ℕ :=
  if j = 0 then 1 else if j - 1 < q then mbit N nd onp repA rankA A ((j - 1) / n) ((j - 1) % n)
    else 0

theorem divmod_aux {n i y : ℕ} (hy : y < n) : (i * n + y) / n = i ∧ (i * n + y) % n = y := by
  have hn : 0 < n := by omega
  constructor
  · rw [Nat.add_comm, Nat.add_mul_div_right _ _ hn, Nat.div_eq_of_lt hy, Nat.zero_add]
  · rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hy]

theorem mOut_succ (q : ℕ) :
    Function.update (mOut n N nd onp repA rankA A q) (q + 1)
      (mbit N nd onp repA rankA A (q / n) (q % n)) = mOut n N nd onp repA rankA A (q + 1) := by
  funext j
  simp only [Function.update_apply, mOut]
  by_cases hj : j = q + 1
  · subst hj; simp
  · rw [if_neg hj]
    split_ifs <;> first | rfl | omega

theorem modelStep {w : ℕ} {s0 : State} {i y : ℕ} {M : ℕ}
    (hN0 : s0.arrs aN = tab (n + 1) (fun v => if nd v then 1 else 0))
    (hP0 : s0.arrs aP = tab (n + 1) (fun v => if onp v then 1 else 0))
    (hRep0 : s0.arrs aRep = tab n repA) (hRank0 : s0.arrs aRank = tab n rankA)
    (hA0 : s0.arrs aAns = A) (hAw : ∀ v ∈ A, v < 2 ^ w)
    (hrep : ∀ y < n, (nd y || onp y) = true → repA y < n ∧ 1 + i * N + rankA (repA y) < A.length)
    (hrk : ∀ v < n, rankA v < 2 ^ w)
    (hip : i < p) (hy : y < n) (hM : M = 1 + p * n)
    (hB : M + n + p + N + A.length + 4 < 2 ^ w)
    {s : State} (hri : s.regs ri = y) (hrO : s.regs rO = i) (hrn : s.regs rn = n)
    (hrN : s.regs rN = N) (hout : s.arrs outArr = tab M (mOut n N nd onp repA rankA A (i * n + y)))
    (ha : ∀ a, a ≠ outArr → s.arrs a = s0.arrs a) :
    ∃ s' t, Exec w modelBody s s' t ∧ t ≤ 25 ∧ s'.regs = s.regs ∧
      s'.arrs outArr = tab M (mOut n N nd onp repA rankA A (i * n + y + 1)) ∧
      (∀ a, a ≠ outArr → s'.arrs a = s0.arrs a) := by
  have hin : i * n + y < p * n := by
    have : (i + 1) * n ≤ p * n := Nat.mul_le_mul_right _ (by omega)
    rw [Nat.add_mul, Nat.one_mul] at this; omega
  obtain ⟨hdiv, hmod⟩ := divmod_aux (i := i) hy
  have hsucc := mOut_succ (n := n) (N := N) (nd := nd) (onp := onp) (repA := repA)
    (rankA := rankA) (A := A) (i * n + y)
  rw [hdiv, hmod] at hsucc
  have hNs : s.arrs aN = tab (n + 1) (fun v => if nd v then 1 else 0) := by
    rw [ha aN (by decide), hN0]
  have hPs : s.arrs aP = tab (n + 1) (fun v => if onp v then 1 else 0) := by
    rw [ha aP (by decide), hP0]
  have e1 : (Expr.read aN (.reg ri)).eval w s = some (if nd y then 1 else 0) :=
    ev_read (ev_reg hri (by omega)) (by rw [hNs, length_tab]; omega)
      (by rw [hNs, getD_tab _ (by omega)]) (by split_ifs <;> omega)
  have e2 : (Expr.read aP (.reg ri)).eval w s = some (if onp y then 1 else 0) :=
    ev_read (ev_reg hri (by omega)) (by rw [hPs, length_tab]; omega)
      (by rw [hPs, getD_tab _ (by omega)]) (by split_ifs <;> omega)
  have ec := ev_add e1 e2 (by split_ifs <;> omega)
  by_cases hno : (nd y || onp y) = true
  · have hc0 : (if nd y then 1 else 0) + (if onp y then 1 else 0) ≠ 0 := by
      cases h1 : nd y <;> cases h2 : onp y <;> simp_all
    obtain ⟨hr1, hr2⟩ := hrep y hy hno
    have hRs : s.arrs aRep = tab n repA := by rw [ha aRep (by decide), hRep0]
    have hKs : s.arrs aRank = tab n rankA := by rw [ha aRank (by decide), hRank0]
    have hAs : s.arrs aAns = A := by rw [ha aAns (by decide), hA0]
    have f1 : (Expr.read aRep (.reg ri)).eval w s = some (repA y) :=
      ev_read (ev_reg hri (by omega)) (by rw [hRs, length_tab]; omega)
        (by rw [hRs, getD_tab _ hy]) (by omega)
    have f2 : (Expr.read aRank (.read aRep (.reg ri))).eval w s = some (rankA (repA y)) :=
      ev_read f1 (by rw [hKs, length_tab]; omega) (by rw [hKs, getD_tab _ hr1]) (hrk _ hr1)
    have f3 := ev_add (ev_add (ev_const (v := 1) (by omega))
      (ev_mul (ev_reg hrO (by omega)) (ev_reg hrN (by omega)) (by omega)) (by omega)) f2
      (by omega) (w := w) (s := s)
    have f4 : (Expr.read aAns (.op .add (.op .add (.const 1) (.op .mul (.reg rO) (.reg rN)))
        (.read aRank (.read aRep (.reg ri))))).eval w s =
        some (A.getD (1 + i * N + rankA (repA y)) 0) :=
      ev_read f3 (by rw [hAs]; omega) (by rw [hAs])
        (by rw [List.getD_eq_getElem _ _ hr2]; exact hAw _ (List.getElem_mem _))
    have g1 := ev_add (ev_add (ev_const (v := 1) (by omega))
      (ev_mul (ev_reg hrO (by omega)) (ev_reg hrn (by omega)) (by omega)) (by omega))
      (ev_reg hri (by omega)) (by omega) (w := w) (s := s)
    have ex : Exec w modelBody s (s.writeArr outArr (1 + i * n + y) (A.getD (1 + i * N + rankA (repA y)) 0)) _ :=
      .ite_true ec hc0 (.write g1 f4 (by rw [hout, length_tab]; omega))
    refine ⟨_, _, ex, by simp [Expr.cost], rfl, ?_, fun a h => by
      rw [State.writeArr_arrs_ne _ _ _ h, ha a h]⟩
    rw [writeArr_tab hout (by omega), show 1 + i * n + y = i * n + y + 1 by omega, ← hsucc]
    simp [mbit, hno]
  · have hno' : (nd y || onp y) = false := by simpa using hno
    have hc0 : (if nd y then 1 else 0) + (if onp y then 1 else 0) = 0 := by
      cases h1 : nd y <;> cases h2 : onp y <;> simp_all
    rw [hc0] at ec
    refine ⟨s, _, .ite_false ec (.skip _), by simp [Expr.cost], rfl, ?_, ha⟩
    rw [hout, ← hsucc]
    have h0 : mbit N nd onp repA rankA A i y = 0 := by simp [mbit, hno']
    rw [h0]
    refine tab_congr fun j _ => ?_
    simp only [Function.update_apply]
    split_ifs with hj
    · subst hj; simp [mOut]
    · rfl

theorem modelProg_exec {w : ℕ} {s : State}
    (hN0 : s.arrs aN = tab (n + 1) (fun v => if nd v then 1 else 0))
    (hP0 : s.arrs aP = tab (n + 1) (fun v => if onp v then 1 else 0))
    (hRep0 : s.arrs aRep = tab n repA) (hRank0 : s.arrs aRank = tab n rankA)
    (hA0 : s.arrs aAns = A) (hAw : ∀ v ∈ A, v < 2 ^ w) (hrn : s.regs rn = n) (hrN : s.regs rN = N)
    (hrep : ∀ i < p, ∀ y < n, (nd y || onp y) = true →
      repA y < n ∧ 1 + i * N + rankA (repA y) < A.length)
    (hrk : ∀ v < n, rankA v < 2 ^ w) (hB : 1 + p * n + n + p + N + A.length + 4 < 2 ^ w) :
    ∃ s' t, Exec w (modelProg p) s s' t ∧ t ≤ 20 + 13 * p + 33 * (p * n) ∧
      s'.arrs outArr = tab (1 + p * n) (mOut n N nd onp repA rankA A (p * n)) ∧
      (∀ a, a ≠ outArr → s'.arrs a = s.arrs a) := by
  have ex1 : Exec w (.alloc outArr (.op .add (.const 1) (.op .mul (.const p) (.reg rn)))) s
      (s.setArr outArr (List.replicate (1 + p * n) 0)) _ :=
    .alloc (ev_add (ev_const (by omega)) (ev_mul (ev_const (by omega)) (ev_reg hrn (by omega))
      (by omega)) (by omega))
  have ex2 : Exec w (.write outArr (.const 0) (.const 1)) (s.setArr outArr (List.replicate (1 + p * n) 0))
      ((s.setArr outArr (List.replicate (1 + p * n) 0)).writeArr outArr 0 1) _ :=
    .write (ev_const (by omega)) (ev_const (by omega)) (by simp)
  have ex3 : Exec w (.assign rO (.const 0)) ((s.setArr outArr (List.replicate (1 + p * n) 0)).writeArr outArr 0 1)
      (((s.setArr outArr (List.replicate (1 + p * n) 0)).writeArr outArr 0 1).setReg rO 0) _ :=
    .assign (ev_const (by omega))
  generalize hs3 : ((s.setArr outArr (List.replicate (1 + p * n) 0)).writeArr outArr 0 1).setReg rO 0
    = s3 at ex3
  have ha3 : ∀ a, a ≠ outArr → s3.arrs a = s.arrs a := fun a h => by
    rw [← hs3, State.setReg_arrs, State.writeArr_arrs_ne _ _ _ h, State.setArr_arrs_ne _ _ h]
  have hout3 : s3.arrs outArr = tab (1 + p * n) (mOut n N nd onp repA rankA A (0 * n)) := by
    rw [← hs3, State.setReg_arrs, State.writeArr_arrs_self, State.setArr_arrs_self,
      replicate_eq_tab, tab_set _ (by omega)]
    refine tab_congr fun j _ => ?_
    simp only [Function.update_apply, mOut]
    split_ifs <;> first | rfl | omega
  let I (i : ℕ) (s' : State) : Prop :=
    s'.regs rO = i ∧ s'.arrs outArr = tab (1 + p * n) (mOut n N nd onp repA rankA A (i * n)) ∧
      (∀ a, a ≠ outArr → s'.arrs a = s.arrs a) ∧ (∀ q, q ≠ ri → q ≠ rO → s'.regs q = s.regs q)
  have hI0 : I 0 s3 := ⟨by rw [← hs3]; simp, hout3, ha3, fun q h1 h2 => by
    rw [← hs3, State.setReg_regs_ne _ _ h2]; rfl⟩
  obtain ⟨s4, t4, ex4, ht4, -, hout4, ha4, -⟩ :=
    Triple.forUp_const (w := w) I p (5 + 32 * n) (r_i := rO) (hi := .const p)
      (body := .seq (.assign ri (.const 0)) (forUp ri (.reg rn) modelBody)) (by omega) (by omega)
      (fun i _ s' hs' => ⟨hs'.1, ev_const (by omega)⟩) (fun i hi => by
        rintro s' ⟨hrO', hout', ha', hr'⟩
        have exa : Exec w (.assign ri (.const 0)) s' (s'.setReg ri 0) _ := .assign (ev_const (by omega))
        let J (y : ℕ) (u : State) : Prop :=
          u.regs ri = y ∧ u.arrs outArr = tab (1 + p * n) (mOut n N nd onp repA rankA A (i * n + y)) ∧
            (∀ a, a ≠ outArr → u.arrs a = s.arrs a) ∧ (∀ q, q ≠ ri → u.regs q = s'.regs q)
        have hJ0 : J 0 (s'.setReg ri 0) := ⟨by simp, by simpa using hout', ha',
          fun q h => by rw [State.setReg_regs_ne _ _ h]⟩
        obtain ⟨s5, t5, ex5, ht5, hri5, hout5, ha5, hr5⟩ :=
          Triple.forUp_const (w := w) J n 25 (r_i := ri) (hi := .reg rn) (body := modelBody)
            (by omega) (by omega)
            (fun y _ u hu => ⟨hu.1, ev_reg (by rw [hu.2.2.2 rn (by decide), hr' rn (by decide)
              (by decide), hrn]) (by omega)⟩)
            (fun y hy => by
              rintro u ⟨hu1, hu2, hu3, hu4⟩
              obtain ⟨u', t', ex', ht', hreg', hout'', ha''⟩ := modelStep (s0 := s) (M := 1 + p * n)
                hN0 hP0 hRep0 hRank0 hA0 hAw (hrep i hi) hrk hi hy rfl hB hu1
                (by rw [hu4 rO (by decide), hrO']) (by rw [hu4 rn (by decide), hr' rn (by decide)
                  (by decide), hrn]) (by rw [hu4 rN (by decide), hr' rN (by decide) (by decide), hrN])
                hu2 hu3
              refine ⟨u', t', ex', ht', ⟨by simp, by rw [State.setReg_arrs, hout'', Nat.add_assoc],
                fun a h => by rw [State.setReg_arrs, ha'' a h], fun q h => by
                  rw [State.setReg_regs_ne _ _ h, hreg', hu4 q h]⟩, by rw [hreg', hu1]⟩)
            (s'.setReg ri 0) hJ0
        refine ⟨s5, _, .seq exa ex5, by simp only [Expr.cost] at ht5 ⊢; nlinarith, ⟨by
          simp, by rw [State.setReg_arrs, hout5, Nat.add_mul, Nat.one_mul], fun a h => by
          rw [State.setReg_arrs, ha5 a h], fun q h1 h2 => by
          rw [State.setReg_regs_ne _ _ h2, hr5 q h1, hr' q h1 h2]⟩, by
          rw [hr5 rO (by decide), hrO']⟩) s3 hI0
  refine ⟨s4, _, .seq ex1 (.seq ex2 (.seq ex3 ex4)), ?_, hout4, ha4⟩
  simp only [Expr.cost] at ht4 ⊢
  nlinarith

/-! ### The lifted model -/

section Lift

variable {l m h k r : ℕ} {x : Alg92Input l m p h k r} {segs : List (List (Fin x.n))}
  {paths : Fin k → List (Fin x.n)} (hF : IsFSystem x segs paths)
include hF

theorem ndB_or_onpB {y : ℕ} (hy : y < x.n) :
    (ndB x segs y || onpB x segs y) = true ↔
      ((⟨y, hy⟩ : Fin x.n) ∈ fNodes x segs ∨ OnPath (fPaths x segs) ⟨y, hy⟩) := by
  have e1 := ndB_val (x := x) (segs := segs) ⟨y, hy⟩
  simp only at e1
  rw [Bool.or_eq_true, e1, decide_eq_true_eq]
  simp only [onpB, decide_eq_true_eq]
  exact or_congr Iff.rfl (mem_layout_iff (y := ⟨y, hy⟩))

theorem mem_liftSet_iff {K : Finset (Fin (fVerts x segs).card)} {y : Fin x.n} :
    y ∈ (cBlobMap (fNodes x segs) (fPaths x segs) (fE x segs) (fι x segs)).liftSet K ↔
      (y ∈ fNodes x segs ∨ OnPath (fPaths x segs) y) ∧
        fι x segs (cRep (fNodes x segs) (fPaths x segs) y) ∈ K := by
  have hP := hF.isPathSystem
  have hinj : Function.Injective (fE x segs) := fun a b hab =>
    (Finset.orderEmbOfFin (fVerts x segs) rfl).injective hab
  have hmemE : ∀ v, fE x segs v ∈ fVerts x segs := fun v => Finset.orderEmbOfFin_mem _ _ v
  rw [BlobMap.mem_liftSet]
  constructor
  · rintro ⟨v, hv, hy⟩
    have hmem := (hP.mem_cBlob_iff (hmemE v)).mp (show y ∈ cBlob _ _ (fE x segs v) from hy)
    refine ⟨hmem.1, ?_⟩
    have : fι x segs (fE x segs v) = v := hinj (fE_fι (hmemE v))
    rw [hmem.2, this]; exact hv
  · rintro ⟨hy, hK⟩
    refine ⟨_, hK, show y ∈ cBlob _ _ (fE x segs _) from
      (hP.mem_cBlob_iff (hmemE _)).mpr ⟨hy, ?_⟩⟩
    exact (fE_fι (hP.cRep_mem_cVerts hy)).symm

/-- **The output of `modelProg` is the lifted model.** -/
theorem mOut_eq_lift (K : Fin p → Finset (Fin (fVerts x segs).card)) :
    tab (1 + p * x.n) (mOut x.n (fVerts x segs).card (ndB x segs) (onpB x segs) (repvF x segs)
      (rankF x segs) (1 :: encBitSetsUpTo K p) (p * x.n)) =
    1 :: encBitSetsUpTo (fun i => (cBlobMap (fNodes x segs) (fPaths x segs) (fE x segs)
      (fι x segs)).liftSet (K i)) p := by
  have hP := hF.isPathSystem
  rw [tab_eq_iff]
  refine ⟨by rw [List.length_cons, length_encBitSetsUpTo _ _ le_rfl]; ring, fun j hj => ?_⟩
  cases j with
  | zero => simp [mOut]
  | succ q =>
    have hq : q < p * x.n := by omega
    have hn : 0 < x.n := by
      rcases Nat.eq_zero_or_pos x.n with h0 | h0
      · rw [h0, Nat.mul_zero] at hq; omega
      · exact h0
    have hi : q / x.n < p := by
      rw [Nat.div_lt_iff_lt_mul hn]; exact hq
    have hy : q % x.n < x.n := Nat.mod_lt _ hn
    have hqd : q = q / x.n * x.n + q % x.n := by
      have := Nat.div_add_mod q x.n; rw [Nat.mul_comm] at this; omega
    rw [List.getD_cons_succ, hqd, getD_encBitSetsUpTo _ p le_rfl hi hy, ← hqd]
    simp only [mOut, Nat.add_one_ne_zero, if_false, Nat.add_sub_cancel, if_pos hq, mbit]
    by_cases hno : (ndB x segs (q % x.n) || onpB x segs (q % x.n)) = true
    · rw [if_pos hno]
      have hS := (ndB_or_onpB hF hy).mp hno
      have hc := hP.cRep_mem_cVerts hS
      rw [repvF, repv_eq hF hy, rankF_eq hF hc, Nat.add_assoc, Nat.add_comm 1, List.getD_cons_succ,
        getD_encBitSetsUpTo _ p le_rfl hi (fι x segs _).2]
      simp only [Fin.eta]
      by_cases hK : fι x segs (cRep (fNodes x segs) (fPaths x segs) ⟨q % x.n, hy⟩) ∈ K ⟨q / x.n, hi⟩
      · rw [if_pos hK, if_pos ((mem_liftSet_iff hF).mpr ⟨hS, hK⟩)]
      · rw [if_neg hK, if_neg (fun h => hK ((mem_liftSet_iff hF).mp h).2)]
    · rw [if_neg hno, if_neg (fun h => hno ((ndB_or_onpB hF hy).mpr ((mem_liftSet_iff hF).mp h).1))]

end Lift

end Alg92

end GraphMinor.Compute
