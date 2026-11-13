module

public import GraphMinor.Compute.Algorithm92BuildRun

/-!
# Graph Minors XIII, (9.2): the pass over the layout (`Algorithm92Sweep.lean`)

The second program after `F` (page 101 of Graph Minors XIII) makes one pass over the layout of
`H ∪ F`. It keeps in a register the start of the current run (the position after the last node).
At a node it records, at the start of the run that ends there, the position of the last entry of
the run (array `aEn`). At a vertex that is not a node it records the start of its run (array
`aRS`). It also marks every vertex that it sees (array `aP`).

The pass is stated on plain lists (`sweepProg_exec`). The functions `rsF`, `enF` describe the two
arrays after the pass, and `rsF_spec`, `enF_spec` give the two facts that `sweep_spec`
(`Algorithm92Layout.lean`) needs.
-/

@[expose] public section

namespace GraphMinor.Compute

namespace Alg92

/-- The array of run starts, indexed by vertex. -/
abbrev aRS : ℕ := 8
/-- The array of run ends, indexed by run start. -/
abbrev aEn : ℕ := 9

variable (nd : ℕ → Bool) (L : List ℕ)

/-- The run ends after `i` steps of the pass. -/
def enF : ℕ → ℕ → ℕ
  | 0 => fun _ => 0
  | i + 1 => if nd (L.getD i 0) then Function.update (enF i) (rsIdx nd L i) (i - 1) else enF i

/-- The run starts after `i` steps of the pass. -/
def rsF : ℕ → ℕ → ℕ
  | 0 => fun _ => 0
  | i + 1 => if nd (L.getD i 0) then rsF i else Function.update (rsF i) (L.getD i 0) (rsIdx nd L i)

/-- The marks of the vertices seen in the first `i` steps of the pass. -/
noncomputable def pF (i : ℕ) : ℕ → ℕ := ind (fun v => ∃ j < i, L.getD j 0 = v)

variable {nd L}

theorem rsF_spec : ∀ (i v : ℕ), nd v = false → (∃ j < i, L.getD j 0 = v) →
    ∃ j < i, L.getD j 0 = v ∧ rsF nd L i v = rsIdx nd L j
  | 0, _, _, ⟨j, hj, _⟩ => absurd hj (Nat.not_lt_zero _)
  | i + 1, v, hv, ⟨j, hj, hjv⟩ => by
    by_cases hiv : L.getD i 0 = v
    · refine ⟨i, by omega, hiv, ?_⟩
      simp only [rsF]
      rw [hiv, hv, if_neg (by simp), Function.update_self]
    · have hji : j < i := by
        rcases Nat.lt_succ_iff_lt_or_eq.mp hj with h | h
        · exact h
        · exact absurd (h ▸ hjv) hiv
      obtain ⟨j', hj', h1, h2⟩ := rsF_spec i v hv ⟨j, hji, hjv⟩
      refine ⟨j', by omega, h1, ?_⟩
      simp only [rsF]
      split_ifs
      · exact h2
      · rw [Function.update_of_ne (Ne.symm hiv), h2]

theorem enF_spec : ∀ (i j : ℕ), j < i → nd (L.getD j 0) = true → enF nd L i (rsIdx nd L j) = j - 1
  | 0, _, hj, _ => absurd hj (Nat.not_lt_zero _)
  | i + 1, j, hj, hnd => by
    simp only [enF]
    by_cases hji : j = i
    · subst hji
      rw [if_pos hnd, Function.update_self]
    · have hji' : j < i := by omega
      have hlt : rsIdx nd L j < rsIdx nd L i := by
        have h1 := rsIdx_le nd L j
        have h2 := rsIdx_mono nd L (show j + 1 ≤ i by omega)
        rw [rsIdx_succ_of_nd hnd] at h2
        omega
      split_ifs
      · rw [Function.update_of_ne (Nat.ne_of_lt hlt), enF_spec i j hji' hnd]
      · exact enF_spec i j hji' hnd

theorem rsIdx_succ_of_not_nd {j : ℕ} (h : nd (L.getD j 0) = false) :
    rsIdx nd L (j + 1) = rsIdx nd L j := by
  rw [rsIdx, h]; simp

/-! ### The program -/

/-- One step of the pass, at position `ri` of the layout. -/
def sweepBody : Cmd :=
  .seq (.assign rtmp (.read aL (.reg ri))) <|
  .seq (.write aP (.reg rtmp) (.const 1)) <|
  .ite (.read aN (.reg rtmp))
    (.seq (.write aEn (.reg rs) (.op .sub (.reg ri) (.const 1)))
      (.assign rs (.op .add (.reg ri) (.const 1))))
    (.write aRS (.reg rtmp) (.reg rs))

/-- The pass over the layout, with the allocation of its three arrays. -/
def sweepProg : Cmd :=
  .seq (.alloc aRS (.op .add (.reg rn) (.const 1))) <|
  .seq (.alloc aEn (.len aL)) <|
  .seq (.alloc aP (.op .add (.reg rn) (.const 1))) <|
  .seq (.assign rs (.const 0)) <|
  .seq (.assign ri (.const 0)) (forUp ri (.len aL) sweepBody)

variable (nd L) in
/-- The invariant of the pass after `i` steps, from the start state `s0`. -/
def sweepInv (n : ℕ) (s0 : State) (i : ℕ) (s : State) : Prop :=
  s.regs ri = i ∧ s.regs rs = rsIdx nd L i ∧
    s.arrs aRS = tab (n + 1) (rsF nd L i) ∧ s.arrs aEn = tab L.length (enF nd L i) ∧
    s.arrs aP = tab (n + 1) (pF L i) ∧
    (∀ a, a ≠ aRS → a ≠ aEn → a ≠ aP → s.arrs a = s0.arrs a) ∧
    (∀ q, q ≠ ri → q ≠ rs → q ≠ rtmp → s.regs q = s0.regs q)

theorem sweepStep {w n : ℕ} {s0 : State} (hL0 : s0.arrs aL = L)
    (hN0 : s0.arrs aN = tab (n + 1) (fun v => if nd v then 1 else 0))
    (hLn : ∀ v ∈ L, v ≤ n) (hB : L.length + n + 2 < 2 ^ w) {i : ℕ} (hi : i < L.length) :
    ⦃sweepInv nd L n s0 i⦄[w] sweepBody
      ⦃fun s' => sweepInv nd L n s0 (i + 1) (s'.setReg ri (i + 1)) ∧ s'.regs ri = i⦄ ≤
        fun _ => 17 := by
  rintro s ⟨hri, hrs, hRS, hEn, hP, ha, hr⟩
  have hLs : s.arrs aL = L := by rw [ha aL (by decide) (by decide) (by decide), hL0]
  have hNs : s.arrs aN = tab (n + 1) (fun v => if nd v then 1 else 0) := by
    rw [ha aN (by decide) (by decide) (by decide), hN0]
  have hvn : L.getD i 0 ≤ n := by
    rw [List.getD_eq_getElem _ _ hi]; exact hLn _ (List.getElem_mem _)
  generalize hv : L.getD i 0 = v at hvn
  have hrsi := rsIdx_le nd L i
  -- step 1: read the entry
  have ex1 : Exec w (.assign rtmp (.read aL (.reg ri))) s (s.setReg rtmp v) _ :=
    .assign (ev_read (ev_reg hri (by omega)) (by rw [hLs]; omega) (by rw [hLs, hv]) (by omega))
  generalize hs1 : s.setReg rtmp v = s1 at ex1
  have hr1 : ∀ q, q ≠ rtmp → s1.regs q = s.regs q := fun q hq => by
    rw [← hs1, State.setReg_regs_ne _ _ hq]
  have ht1 : s1.regs rtmp = v := by rw [← hs1]; simp
  have ha1 : ∀ a, s1.arrs a = s.arrs a := fun a => by rw [← hs1]; rfl
  -- step 2: mark it as seen
  have ex2 : Exec w (.write aP (.reg rtmp) (.const 1)) s1 (s1.writeArr aP v 1) _ :=
    .write (ev_reg ht1 (by omega)) (ev_const (by omega)) (by rw [ha1, hP, length_tab]; omega)
  have hP2 := writeArr_tab (by rw [ha1, hP]) (show v < n + 1 by omega) 1 (s := s1)
  have hpF : Function.update (pF L i) v 1 = pF L (i + 1) := by
    unfold pF
    rw [update_ind]
    congr 1; funext u; apply propext
    constructor
    · rintro (⟨j, hj, hju⟩ | rfl)
      · exact ⟨j, by omega, hju⟩
      · exact ⟨i, by omega, hv⟩
    · rintro ⟨j, hj, hju⟩
      by_cases hji : j = i
      · subst hji; right; rw [← hju, hv]
      · exact Or.inl ⟨j, by omega, hju⟩
  rw [hpF] at hP2
  generalize hs2 : s1.writeArr aP v 1 = s2 at ex2 hP2
  have hr2 : s2.regs = s1.regs := by rw [← hs2]; rfl
  have ha2 : ∀ a, a ≠ aP → s2.arrs a = s.arrs a := fun a h => by
    rw [← hs2, State.writeArr_arrs_ne _ _ _ h, ha1]
  have hcond : (Expr.read aN (.reg rtmp)).eval w s2 = some (if nd v then 1 else 0) :=
    ev_read (ev_reg (by rw [hr2, ht1]) (by omega)) (by rw [ha2 aN (by decide), hNs]; simp; omega)
      (by rw [ha2 aN (by decide), hNs, getD_tab _ (by omega)]) (by split_ifs <;> omega)
  have hpost : ∀ s3 : State, s3.regs ri = i → s3.regs rs = rsIdx nd L (i + 1) →
      s3.arrs aRS = tab (n + 1) (rsF nd L (i + 1)) →
      s3.arrs aEn = tab L.length (enF nd L (i + 1)) →
      (∀ a, a ≠ aRS → a ≠ aEn → s3.arrs a = s2.arrs a) →
      (∀ q, q ≠ rs → s3.regs q = s2.regs q) →
      sweepInv nd L n s0 (i + 1) (s3.setReg ri (i + 1)) ∧ s3.regs ri = i := by
    intro s3 h1 h2 h3 h4 h5 h6
    refine ⟨⟨by simp, by rw [State.setReg_regs_ne _ _ (by decide), h2], by rw [State.setReg_arrs, h3],
      by rw [State.setReg_arrs, h4], by rw [State.setReg_arrs, h5 aP (by decide) (by decide), hP2],
      fun a b1 b2 b3 => ?_, fun q c1 c2 c3 => ?_⟩, h1⟩
    · rw [State.setReg_arrs, h5 a b1 b2, ha2 a b3, ha a b1 b2 b3]
    · rw [State.setReg_regs_ne _ _ c1, h6 q c2, hr2, hr1 q c3, hr q c1 c2 c3]
  by_cases hndv : nd v = true
  · rw [if_pos hndv] at hcond
    have ex3 : Exec w (.write aEn (.reg rs) (.op .sub (.reg ri) (.const 1))) s2
        (s2.writeArr aEn (rsIdx nd L i) (i - 1)) _ :=
      .write (ev_reg (by rw [hr2, hr1 rs (by decide), hrs]) (by omega))
        (ev_sub (ev_reg (by rw [hr2, hr1 ri (by decide), hri]) (by omega)) (ev_const (by omega)))
        (by rw [ha2 aEn (by decide), hEn, length_tab]; omega)
    have ex4 : Exec w (.assign rs (.op .add (.reg ri) (.const 1)))
        (s2.writeArr aEn (rsIdx nd L i) (i - 1))
        ((s2.writeArr aEn (rsIdx nd L i) (i - 1)).setReg rs (i + 1)) _ :=
      .assign (ev_add (ev_reg (by rw [State.writeArr_regs, hr2, hr1 ri (by decide), hri])
        (by omega)) (ev_const (by omega)) (by omega))
    refine ⟨_, _, .seq ex1 (.seq ex2 (.ite_true hcond one_ne_zero (.seq ex3 ex4))),
      by simp [Expr.cost], hpost _ ?_ ?_ ?_ ?_ ?_ ?_⟩
    · rw [State.setReg_regs_ne _ _ (by decide), State.writeArr_regs, hr2, hr1 ri (by decide), hri]
    · rw [State.setReg_regs_self, rsIdx_succ_of_nd (by rw [hv]; exact hndv)]
    · rw [State.setReg_arrs, State.writeArr_arrs_ne _ _ _ (by decide), ha2 aRS (by decide), hRS]
      simp only [rsF, hv, hndv, if_true]
    · rw [State.setReg_arrs, writeArr_tab (by rw [ha2 aEn (by decide), hEn]) (by omega)]
      simp only [enF, hv, hndv, if_true]
    · intro a h1 h2; rw [State.setReg_arrs, State.writeArr_arrs_ne _ _ _ h2]
    · intro q hq; rw [State.setReg_regs_ne _ _ hq, State.writeArr_regs]
  · have hndv' : nd v = false := by simpa using hndv
    rw [if_neg hndv] at hcond
    have ex3 : Exec w (.write aRS (.reg rtmp) (.reg rs)) s2 (s2.writeArr aRS v (rsIdx nd L i)) _ :=
      .write (ev_reg (by rw [hr2, ht1]) (by omega))
        (ev_reg (by rw [hr2, hr1 rs (by decide), hrs]) (by omega))
        (by rw [ha2 aRS (by decide), hRS, length_tab]; omega)
    refine ⟨_, _, .seq ex1 (.seq ex2 (.ite_false hcond ex3)),
      by simp [Expr.cost], hpost _ ?_ ?_ ?_ ?_ ?_ ?_⟩
    · rw [State.writeArr_regs, hr2, hr1 ri (by decide), hri]
    · rw [State.writeArr_regs, hr2, hr1 rs (by decide), hrs,
        rsIdx_succ_of_not_nd (by rw [hv]; exact hndv')]
    · rw [writeArr_tab (by rw [ha2 aRS (by decide), hRS]) (by omega)]
      simp only [rsF, hv, hndv', Bool.false_eq_true, if_false]
    · rw [State.writeArr_arrs_ne _ _ _ (by decide), ha2 aEn (by decide), hEn]
      simp only [enF, hv, hndv', Bool.false_eq_true, if_false]
    · intro a h1 h2; rw [State.writeArr_arrs_ne _ _ _ h1]
    · intro q hq; rw [State.writeArr_regs]

/-- **The pass over the layout.** -/
theorem sweepProg_exec {w n : ℕ} {s : State} (hL0 : s.arrs aL = L)
    (hN0 : s.arrs aN = tab (n + 1) (fun v => if nd v then 1 else 0)) (hrn : s.regs rn = n)
    (hLn : ∀ v ∈ L, v ≤ n) (hB : L.length + n + 2 < 2 ^ w) :
    ∃ s' t, Exec w sweepProg s s' t ∧ t ≤ 20 + 2 * n + 25 * L.length ∧
      s'.arrs aRS = tab (n + 1) (rsF nd L L.length) ∧
      s'.arrs aEn = tab L.length (enF nd L L.length) ∧
      s'.arrs aP = tab (n + 1) (pF L L.length) ∧
      (∀ a, a ≠ aRS → a ≠ aEn → a ≠ aP → s'.arrs a = s.arrs a) ∧
      (∀ q, q ≠ ri → q ≠ rs → q ≠ rtmp → s'.regs q = s.regs q) := by
  have ex1 : Exec w (.alloc aRS (.op .add (.reg rn) (.const 1))) s
      (s.setArr aRS (List.replicate (n + 1) 0)) _ :=
    .alloc (ev_add (ev_reg hrn (by omega)) (ev_const (by omega)) (by omega))
  generalize hs1 : s.setArr aRS (List.replicate (n + 1) 0) = s1 at ex1
  have ex2 : Exec w (.alloc aEn (.len aL)) s1 (s1.setArr aEn (List.replicate L.length 0)) _ :=
    .alloc (ev_len (by rw [← hs1, State.setArr_arrs_ne _ _ (by decide), hL0]) (by omega))
  generalize hs2 : s1.setArr aEn (List.replicate L.length 0) = s2 at ex2
  have ex3 : Exec w (.alloc aP (.op .add (.reg rn) (.const 1))) s2
      (s2.setArr aP (List.replicate (n + 1) 0)) _ :=
    .alloc (ev_add (ev_reg (by rw [← hs2, ← hs1]; simp [hrn]) (by omega)) (ev_const (by omega))
      (by omega))
  generalize hs3 : s2.setArr aP (List.replicate (n + 1) 0) = s3 at ex3
  have ex4 : Exec w (.assign rs (.const 0)) s3 (s3.setReg rs 0) _ := .assign (ev_const (by omega))
  have ex5 : Exec w (.assign ri (.const 0)) (s3.setReg rs 0) ((s3.setReg rs 0).setReg ri 0) _ :=
    .assign (ev_const (by omega))
  generalize hs5 : (s3.setReg rs 0).setReg ri 0 = s5 at ex5
  have ha5 : ∀ a, a ≠ aRS → a ≠ aEn → a ≠ aP → s5.arrs a = s.arrs a := fun a h1 h2 h3 => by
    rw [← hs5, ← hs3, ← hs2, ← hs1]
    simp [State.setArr_arrs_ne _ _ h1, State.setArr_arrs_ne _ _ h2, State.setArr_arrs_ne _ _ h3]
  have hr5 : ∀ q, q ≠ ri → q ≠ rs → s5.regs q = s.regs q := fun q h1 h2 => by
    rw [← hs5, ← hs3, ← hs2, ← hs1]
    simp [State.setReg_regs_ne _ _ h1, State.setReg_regs_ne _ _ h2]
  have hI0 : sweepInv nd L n s5 0 s5 := by
    refine ⟨by rw [← hs5]; simp, by rw [← hs5]; simp [rsIdx], ?_, ?_, ?_, fun _ _ _ _ => rfl,
      fun _ _ _ _ => rfl⟩
    · rw [← hs5, ← hs3, ← hs2, ← hs1]
      simp only [State.setReg_arrs, State.setArr_arrs_ne _ _ (show aRS ≠ aP by decide),
        State.setArr_arrs_ne _ _ (show aRS ≠ aEn by decide), State.setArr_arrs_self,
        replicate_eq_tab]
      rfl
    · rw [← hs5, ← hs3, ← hs2]
      simp only [State.setReg_arrs, State.setArr_arrs_ne _ _ (show aEn ≠ aP by decide),
        State.setArr_arrs_self, replicate_eq_tab]
      rfl
    · rw [← hs5, ← hs3]
      simp only [State.setReg_arrs, State.setArr_arrs_self, replicate_eq_tab]
      exact tab_congr fun j _ => by simp [pF, ind]
  have hL5 : s5.arrs aL = L := by rw [ha5 aL (by decide) (by decide) (by decide), hL0]
  have hN5 : s5.arrs aN = tab (n + 1) (fun v => if nd v then 1 else 0) := by
    rw [ha5 aN (by decide) (by decide) (by decide), hN0]
  obtain ⟨s6, t6, ex6, ht6, hri6, -, hRS6, hEn6, hP6, ha6, hr6⟩ :=
    Triple.forUp_const (w := w) (sweepInv nd L n s5) L.length 17 (r_i := ri) (hi := .len aL)
      (body := sweepBody) (by omega) (by omega)
      (fun i _ s' hs' => ⟨hs'.1, ev_len (by rw [hs'.2.2.2.2.2.1 aL (by decide) (by decide)
        (by decide), hL5]) (by omega)⟩)
      (fun i hi => sweepStep hL5 hN5 hLn hB hi) s5 hI0
  refine ⟨s6, _, .seq ex1 (.seq ex2 (.seq ex3 (.seq ex4 (.seq ex5 ex6)))), ?_, hRS6, hEn6, hP6,
    fun a h1 h2 h3 => by rw [ha6 a h1 h2 h3, ha5 a h1 h2 h3],
    fun q h1 h2 h3 => by rw [hr6 q h1 h2 h3, hr5 q h1 h2]⟩
  simp only [Expr.cost] at ht6 ⊢
  omega

end Alg92

end GraphMinor.Compute
