module

public import GraphMinor.Compute.Algorithm92RankSpec

/-!
# Graph Minors XIII, (9.2): the program that writes the key (`Algorithm92KeyProg.lean`)

The fourth program after `F` (page 101 of Graph Minors XIII) writes the key of the compressed copy
of `H ∪ F` (`compKey`, `Algorithm92Key.lean`) into the array `aKey`: the number `N` of compressed
vertices, the numbers of the branch vertices, and then one pass over the layout that writes `N`
at each separator and the number of each vertex that stands for its blob.

The program is stated on plain functions (`keyProg_exec`).
-/

@[expose] public section

namespace GraphMinor.Compute

namespace Alg92

/-- The work array of the key. -/
abbrev aK : ℕ := 13
/-- The array of the key. -/
abbrev aKey : ℕ := 14

/-- The entries of the key for one entry `v` of the layout. -/
def keyOne (n N : ℕ) (repA rankA : ℕ → ℕ) (v : ℕ) : List ℕ :=
  if v = n then [N] else if repA v = v then [rankA v] else []

theorem preTab_snoc {K : List ℕ} {M : ℕ} (hK : K.length < M) (v : ℕ) :
    tab M (Function.update (preTab K K.length) K.length v) =
      tab M (preTab (K ++ [v]) (K ++ [v]).length) := by
  refine tab_congr fun j _ => ?_
  simp only [Function.update_apply, preTab, List.length_append, List.length_singleton]
  by_cases hj : j = K.length
  · subst hj; simp
  · rw [if_neg hj]
    by_cases hj' : j < K.length
    · rw [if_pos hj', if_pos (by omega), List.getD_append _ _ _ _ hj']
    · rw [if_neg hj', if_neg (by omega)]

/-! ### The branch vertices -/

/-- Write the number of the `ri`-th branch vertex at position `1 + ri`. -/
def keyBvBody : Cmd :=
  .write aK (.op .add (.const 1) (.reg ri)) (.read aRank (.read aW (.op .add (.const 3) (.reg ri))))

/-- One step of the pass: the entries of the key for the entry `ri` of the layout. -/
def keyBody : Cmd :=
  .seq (.assign rtmp (.read aL (.reg ri))) <|
  .ite (.op .eq (.reg rtmp) (.reg rn))
    (.seq (.write aK (.reg rpos) (.reg rN)) (.assign rpos (.op .add (.reg rpos) (.const 1))))
    (.ite (.op .eq (.read aRep (.reg rtmp)) (.reg rtmp))
      (.seq (.write aK (.reg rpos) (.read aRank (.reg rtmp)))
        (.assign rpos (.op .add (.reg rpos) (.const 1))))
      .skip)

/-- The program that writes the key into `aKey`. -/
def keyProg (V : ℕ) : Cmd :=
  .seq (.alloc aK (.op .add (.len aL) (.const (V + 1)))) <|
  .seq (.write aK (.const 0) (.reg rN)) <|
  .seq (.assign ri (.const 0)) <|
  .seq (forUp ri (.const V) keyBvBody) <|
  .seq (.assign rpos (.const (1 + V))) <|
  .seq (.assign ri (.const 0)) <|
  .seq (forUp ri (.len aL) keyBody) <|
  .seq (.alloc aKey (.reg rpos)) <|
  .seq (.assign rA (.const 0)) <|
  .seq (.assign rB (.const 0)) (copyProg aK aKey rA rB rpos rt)

variable {n N V : ℕ} {repA rankA : ℕ → ℕ} {L Wa : List ℕ}

/-- The invariant of the loop over the branch vertices. -/
def keyBvInv (M : ℕ) (pre : List ℕ) (s0 : State) (u : ℕ) (s : State) : Prop :=
  s.regs ri = u ∧ s.arrs aK = tab M (preTab (pre.take (1 + u)) (pre.take (1 + u)).length) ∧
    (∀ a, a ≠ aK → s.arrs a = s0.arrs a) ∧ (∀ q, q ≠ ri → s.regs q = s0.regs q)

/-- The invariant of the pass. -/
def keyInv (M : ℕ) (pre : List ℕ) (s0 : State) (i : ℕ) (s : State) : Prop :=
  s.regs ri = i ∧ s.regs rpos = (pre ++ (L.take i).flatMap (keyOne n N repA rankA)).length ∧
    s.arrs aK = tab M (preTab (pre ++ (L.take i).flatMap (keyOne n N repA rankA))
      (pre ++ (L.take i).flatMap (keyOne n N repA rankA)).length) ∧
    (∀ a, a ≠ aK → s.arrs a = s0.arrs a) ∧ (∀ q, q ≠ ri → q ≠ rpos → q ≠ rtmp → s.regs q = s0.regs q)

theorem length_flatMap_keyOne_le (L : List ℕ) :
    (L.flatMap (keyOne n N repA rankA)).length ≤ L.length := by
  induction L with
  | nil => simp
  | cons v L ih =>
    simp only [List.flatMap_cons, List.length_append, List.length_cons]
    have : (keyOne n N repA rankA v).length ≤ 1 := by unfold keyOne; split_ifs <;> simp
    omega

theorem keyStep {w M : ℕ} {s0 : State} {pre : List ℕ} (hL0 : s0.arrs aL = L)
    (hRep0 : s0.arrs aRep = tab n repA) (hRank0 : s0.arrs aRank = tab n rankA)
    (hrn : s0.regs rn = n) (hrN : s0.regs rN = N) (hLn : ∀ v ∈ L, v ≤ n)
    (hM : pre.length + L.length ≤ M) (hB : M + n + N + 2 < 2 ^ w)
    (hrk : ∀ v < n, rankA v < 2 ^ w) (hrp : ∀ v < n, repA v < 2 ^ w) {i : ℕ}
    (hi : i < L.length) :
    ⦃keyInv (n := n) (N := N) (repA := repA) (rankA := rankA) (L := L) M pre s0 i⦄[w] keyBody
      ⦃fun s' => keyInv (n := n) (N := N) (repA := repA) (rankA := rankA) (L := L) M pre s0 (i + 1)
        (s'.setReg ri (i + 1)) ∧ s'.regs ri = i⦄ ≤ fun _ => 20 := by
  rintro s ⟨hri, hpos, hK, ha, hr⟩
  have hLs : s.arrs aL = L := by rw [ha aL (by decide), hL0]
  have hvn : L.getD i 0 ≤ n := by
    rw [List.getD_eq_getElem _ _ hi]; exact hLn _ (List.getElem_mem _)
  have htake : (L.take (i + 1)).flatMap (keyOne n N repA rankA) =
      (L.take i).flatMap (keyOne n N repA rankA) ++ keyOne n N repA rankA (L.getD i 0) := by
    rw [List.take_add_one, List.getElem?_eq_getElem hi, Option.toList_some, List.flatMap_append,
      List.flatMap_singleton, List.getD_eq_getElem _ _ hi]
  have hlen := length_flatMap_keyOne_le (n := n) (N := N) (repA := repA) (rankA := rankA)
    (L.take i)
  have hti : (L.take i).length = i := by simp; omega
  generalize hK0 : pre ++ (L.take i).flatMap (keyOne n N repA rankA) = K at hpos hK
  have hKlen : K.length < M := by
    rw [← hK0, List.length_append]; omega
  generalize hv : L.getD i 0 = v at hvn htake
  have hnew : pre ++ (L.take (i + 1)).flatMap (keyOne n N repA rankA) =
      K ++ keyOne n N repA rankA v := by rw [htake, ← hK0, List.append_assoc]
  -- step 1: read the entry
  have ex1 : Exec w (.assign rtmp (.read aL (.reg ri))) s (s.setReg rtmp v) _ :=
    .assign (ev_read (ev_reg hri (by omega)) (by rw [hLs]; omega) (by rw [hLs, hv]) (by omega))
  generalize hs1 : s.setReg rtmp v = s1 at ex1
  have hr1 : ∀ q, q ≠ rtmp → s1.regs q = s.regs q := fun q hq => by
    rw [← hs1, State.setReg_regs_ne _ _ hq]
  have ht1 : s1.regs rtmp = v := by rw [← hs1]; simp
  have ha1 : ∀ a, s1.arrs a = s.arrs a := fun a => by rw [← hs1]; rfl
  have hrn1 : s1.regs rn = n := by rw [hr1 rn (by decide), hr rn (by decide) (by decide)
    (by decide), hrn]
  have hpos1 : s1.regs rpos = K.length := by rw [hr1 rpos (by decide), hpos]
  have hK1 : s1.arrs aK = tab M (preTab K K.length) := by rw [ha1, hK]
  -- the frame after a step that appends the list `e`
  have hpost : ∀ (e : List ℕ) (s3 : State), keyOne n N repA rankA v = e →
      s3.regs ri = i → s3.regs rpos = (K ++ e).length →
      s3.arrs aK = tab M (preTab (K ++ e) (K ++ e).length) →
      (∀ a, a ≠ aK → s3.arrs a = s1.arrs a) → (∀ q, q ≠ rpos → s3.regs q = s1.regs q) →
      keyInv (n := n) (N := N) (repA := repA) (rankA := rankA) (L := L) M pre s0 (i + 1)
        (s3.setReg ri (i + 1)) ∧ s3.regs ri = i := by
    intro e s3 he e1 e2 e3 e4 e5
    rw [← he] at e2 e3
    refine ⟨⟨by simp, by rw [State.setReg_regs_ne _ _ (by decide), e2, hnew],
      by rw [State.setReg_arrs, e3, hnew], fun a b => ?_, fun q c1 c2 c3 => ?_⟩, e1⟩
    · rw [State.setReg_arrs, e4 a b, ha1, ha a b]
    · rw [State.setReg_regs_ne _ _ c1, e5 q c2, hr1 q c3, hr q c1 c2 c3]
  -- appending one entry
  have happ : ∀ (val : Expr) (u : ℕ), val.eval w s1 = some u → keyOne n N repA rankA v = [u] →
      ∃ s3 t, Exec w (.seq (.write aK (.reg rpos) val)
        (.assign rpos (.op .add (.reg rpos) (.const 1)))) s1 s3 t ∧ t ≤ val.cost + 6 ∧
        keyInv (n := n) (N := N) (repA := repA) (rankA := rankA) (L := L) M pre s0 (i + 1)
          (s3.setReg ri (i + 1)) ∧ s3.regs ri = i := by
    intro val u hval he
    have exa : Exec w (.write aK (.reg rpos) val) s1 (s1.writeArr aK K.length u) _ :=
      .write (ev_reg hpos1 (by omega)) hval (by rw [hK1, length_tab]; exact hKlen)
    have exb : Exec w (.assign rpos (.op .add (.reg rpos) (.const 1))) (s1.writeArr aK K.length u)
        ((s1.writeArr aK K.length u).setReg rpos (K.length + 1)) _ :=
      .assign (ev_add (ev_reg (by rw [State.writeArr_regs, hpos1]) (by omega)) (ev_const (by omega))
        (by omega))
    refine ⟨_, _, .seq exa exb, by simp [Expr.cost]; omega, hpost [u] _ he ?_ ?_ ?_ ?_ ?_⟩
    · rw [State.setReg_regs_ne _ _ (by decide), State.writeArr_regs, hr1 ri (by decide), hri]
    · simp
    · rw [State.setReg_arrs, writeArr_tab hK1 hKlen, preTab_snoc hKlen]
    · intro a h; rw [State.setReg_arrs, State.writeArr_arrs_ne _ _ _ h]
    · intro q h; rw [State.setReg_regs_ne _ _ h, State.writeArr_regs]
  have hc1 := ev_eq (ev_reg ht1 (by omega)) (ev_reg hrn1 (by omega)) (by omega) (s := s1) (w := w)
  by_cases hvn' : v = n
  · rw [if_pos hvn'] at hc1
    obtain ⟨s3, t3, ex3, ht3, hI⟩ := happ (.reg rN) N
      (ev_reg (by rw [hr1 rN (by decide), hr rN (by decide) (by decide) (by decide), hrN])
        (by omega)) (by simp [keyOne, hvn'])
    exact ⟨s3, _, .seq ex1 (.ite_true hc1 one_ne_zero ex3), by simp [Expr.cost] at ht3 ⊢; omega,
      hI⟩
  · rw [if_neg hvn'] at hc1
    have hvlt : v < n := by omega
    have hRep1 : s1.arrs aRep = tab n repA := by rw [ha1, ha aRep (by decide), hRep0]
    have hRank1 : s1.arrs aRank = tab n rankA := by rw [ha1, ha aRank (by decide), hRank0]
    have eR : (Expr.read aRep (.reg rtmp)).eval w s1 = some (repA v) :=
      ev_read (ev_reg ht1 (by omega)) (by rw [hRep1, length_tab]; omega)
        (by rw [hRep1, getD_tab _ hvlt]) (hrp v hvlt)
    have hc2 := ev_eq eR (ev_reg ht1 (by omega)) (by omega)
    by_cases hrv : repA v = v
    · rw [if_pos hrv] at hc2
      have eK : (Expr.read aRank (.reg rtmp)).eval w s1 = some (rankA v) :=
        ev_read (ev_reg ht1 (by omega)) (by rw [hRank1, length_tab]; omega)
          (by rw [hRank1, getD_tab _ hvlt]) (hrk v hvlt)
      obtain ⟨s3, t3, ex3, ht3, hI⟩ := happ _ _ eK (by simp [keyOne, hvn', hrv])
      exact ⟨s3, _, .seq ex1 (.ite_false hc1 (.ite_true hc2 one_ne_zero ex3)),
        by simp [Expr.cost] at ht3 ⊢; omega, hI⟩
    · rw [if_neg hrv] at hc2
      refine ⟨s1, _, .seq ex1 (.ite_false hc1 (.ite_false hc2 (.skip _))), by simp [Expr.cost],
        hpost [] s1 (by simp [keyOne, hvn', hrv]) (by rw [hr1 ri (by decide), hri])
          (by simpa using hpos1) (by simpa using hK1) (fun _ _ => rfl) (fun _ _ => rfl)⟩

/-- The numbers of the branch vertices, read through `Wa`. -/
def bvRanks (V : ℕ) (rankA : ℕ → ℕ) (Wa : List ℕ) : List ℕ :=
  (List.range V).map (fun u => rankA (Wa.getD (3 + u) 0))

theorem take_succ_bvRanks {u : ℕ} (hu : u < V) :
    (N :: bvRanks V rankA Wa).take (1 + (u + 1)) =
      (N :: bvRanks V rankA Wa).take (1 + u) ++ [rankA (Wa.getD (3 + u) 0)] := by
  rw [show 1 + (u + 1) = (1 + u) + 1 by omega, List.take_add_one,
    List.getElem?_eq_getElem (by simp [bvRanks]; omega)]
  simp [bvRanks, Nat.add_comm 1 u]

theorem keyBvStep {w M : ℕ} {s0 : State} (hW0 : s0.arrs aW = Wa)
    (hRank0 : s0.arrs aRank = tab n rankA) (hWV : 3 + V ≤ Wa.length)
    (hWn : ∀ u < V, Wa.getD (3 + u) 0 < n) (hWw : ∀ v ∈ Wa, v < 2 ^ w)
    (hM : 1 + V ≤ M) (hB : M + Wa.length + n + 4 < 2 ^ w) (hrk : ∀ v < n, rankA v < 2 ^ w)
    {u : ℕ} (hu : u < V) :
    ⦃keyBvInv M (N :: bvRanks V rankA Wa) s0 u⦄[w] keyBvBody
      ⦃fun s' => keyBvInv M (N :: bvRanks V rankA Wa) s0 (u + 1) (s'.setReg ri (u + 1)) ∧
        s'.regs ri = u⦄ ≤ fun _ => 9 := by
  rintro s ⟨hri, hK, ha, hr⟩
  have hWs : s.arrs aW = Wa := by rw [ha aW (by decide), hW0]
  have hRs : s.arrs aRank = tab n rankA := by rw [ha aRank (by decide), hRank0]
  have hwv := hWn u hu
  have hlen : ((N :: bvRanks V rankA Wa).take (1 + u)).length = 1 + u := by
    simp [bvRanks]; omega
  have e1 : (Expr.read aW (.op .add (.const 3) (.reg ri))).eval w s = some (Wa.getD (3 + u) 0) :=
    ev_read (ev_add (ev_const (by omega)) (ev_reg hri (by omega)) (by omega)) (by rw [hWs]; omega)
      (by rw [hWs]) (by omega)
  have e2 : (Expr.read aRank (.read aW (.op .add (.const 3) (.reg ri)))).eval w s =
      some (rankA (Wa.getD (3 + u) 0)) :=
    ev_read e1 (by rw [hRs, length_tab]; omega) (by rw [hRs, getD_tab _ hwv]) (hrk _ hwv)
  have ex : Exec w keyBvBody s (s.writeArr aK (1 + u) (rankA (Wa.getD (3 + u) 0))) _ :=
    .write (ev_add (ev_const (by omega)) (ev_reg hri (by omega)) (by omega)) e2
      (by rw [hK, length_tab]; omega)
  refine ⟨_, _, ex, by simp [Expr.cost], ⟨by simp, ?_, ?_, ?_⟩, by simp [hri]⟩
  · rw [State.setReg_arrs, take_succ_bvRanks hu]
    generalize hT : (N :: bvRanks V rankA Wa).take (1 + u) = T at hK hlen
    rw [show 1 + u = T.length from hlen.symm, writeArr_tab hK (by omega), preTab_snoc (by omega)]
  · intro a h; rw [State.setReg_arrs, State.writeArr_arrs_ne _ _ _ h, ha a h]
  · intro q h; rw [State.setReg_regs_ne _ _ h, State.writeArr_regs, hr q h]

/-- **The program that writes the key.** -/
theorem keyProg_exec {w : ℕ} {s : State} (hL0 : s.arrs aL = L) (hW0 : s.arrs aW = Wa)
    (hRep0 : s.arrs aRep = tab n repA) (hRank0 : s.arrs aRank = tab n rankA)
    (hrn : s.regs rn = n) (hrN : s.regs rN = N) (hLn : ∀ v ∈ L, v ≤ n)
    (hWV : 3 + V ≤ Wa.length) (hWn : ∀ u < V, Wa.getD (3 + u) 0 < n) (hWw : ∀ v ∈ Wa, v < 2 ^ w)
    (hB : 2 * (L.length + V + 1) + Wa.length + n + N + 4 < 2 ^ w)
    (hrk : ∀ v < n, rankA v < 2 ^ w) (hrp : ∀ v < n, repA v < 2 ^ w) :
    ∃ s' t, Exec w (keyProg V) s s' t ∧ t ≤ 50 + 40 * V + 50 * L.length ∧
      s'.arrs aKey = N :: bvRanks V rankA Wa ++ L.flatMap (keyOne n N repA rankA) ∧
      (∀ a, a ≠ aK → a ≠ aKey → s'.arrs a = s.arrs a) ∧
      (∀ q, q ≠ ri → q ≠ rpos → q ≠ rtmp → q ≠ rA → q ≠ rB → q ≠ rt → s'.regs q = s.regs q) := by
  have hNw : N < 2 ^ w := by omega
  -- the work array, with `N` at position `0`
  have ex1 : Exec w (.alloc aK (.op .add (.len aL) (.const (V + 1)))) s
      (s.setArr aK (List.replicate (L.length + (V + 1)) 0)) _ :=
    .alloc (ev_add (ev_len (by rw [hL0]) (by omega)) (ev_const (by omega)) (by omega))
  generalize hM : L.length + (V + 1) = M at ex1
  have ex2 : Exec w (.write aK (.const 0) (.reg rN)) (s.setArr aK (List.replicate M 0))
      ((s.setArr aK (List.replicate M 0)).writeArr aK 0 N) _ :=
    .write (ev_const (by omega)) (ev_reg (by simp [hrN]) hNw) (by simp; omega)
  have ex3 : Exec w (.assign ri (.const 0)) ((s.setArr aK (List.replicate M 0)).writeArr aK 0 N)
      (((s.setArr aK (List.replicate M 0)).writeArr aK 0 N).setReg ri 0) _ :=
    .assign (ev_const (by omega))
  generalize hs3 : ((s.setArr aK (List.replicate M 0)).writeArr aK 0 N).setReg ri 0 = s3 at ex3
  have ha3 : ∀ a, a ≠ aK → s3.arrs a = s.arrs a := fun a h => by
    rw [← hs3, State.setReg_arrs, State.writeArr_arrs_ne _ _ _ h, State.setArr_arrs_ne _ _ h]
  have hr3 : ∀ q, q ≠ ri → s3.regs q = s.regs q := fun q h => by
    rw [← hs3, State.setReg_regs_ne _ _ h]; rfl
  have hK3 : s3.arrs aK = tab M (preTab ((N :: bvRanks V rankA Wa).take (1 + 0))
      ((N :: bvRanks V rankA Wa).take (1 + 0)).length) := by
    rw [← hs3, State.setReg_arrs, State.writeArr_arrs_self, State.setArr_arrs_self,
      replicate_eq_tab, tab_set _ (by omega)]
    refine tab_congr fun j _ => ?_
    simp only [Function.update_apply, preTab]
    by_cases hj : j = 0
    · subst hj; simp
    · rw [if_neg hj, if_neg (by simp; omega)]
  -- the branch vertices
  obtain ⟨s4, t4, ex4, ht4, hri4, hK4, ha4, hr4⟩ :=
    Triple.forUp_const (w := w) (keyBvInv M (N :: bvRanks V rankA Wa) s3) V 9 (r_i := ri)
      (hi := .const V) (body := keyBvBody) (by omega) (by omega)
      (fun i _ s' hs' => ⟨hs'.1, ev_const (by omega)⟩)
      (fun u hu => keyBvStep (by rw [ha3 aW (by decide), hW0])
        (by rw [ha3 aRank (by decide), hRank0]) hWV hWn hWw (by omega) (by omega) hrk hu) s3
      ⟨by rw [← hs3]; simp, hK3, fun _ _ => rfl, fun _ _ => rfl⟩
  have hpre : (N :: bvRanks V rankA Wa).take (1 + V) = N :: bvRanks V rankA Wa :=
    List.take_of_length_le (by simp [bvRanks])
  rw [hpre] at hK4
  -- the pass
  have ex5 : Exec w (.assign rpos (.const (1 + V))) s4 (s4.setReg rpos (1 + V)) _ :=
    .assign (ev_const (by omega))
  have ex6 : Exec w (.assign ri (.const 0)) (s4.setReg rpos (1 + V))
      ((s4.setReg rpos (1 + V)).setReg ri 0) _ := .assign (ev_const (by omega))
  generalize hs6 : (s4.setReg rpos (1 + V)).setReg ri 0 = s6 at ex6
  have ha6 : ∀ a, a ≠ aK → s6.arrs a = s.arrs a := fun a h => by
    rw [← hs6, State.setReg_arrs, State.setReg_arrs, ha4 a h, ha3 a h]
  have hr6 : ∀ q, q ≠ ri → q ≠ rpos → s6.regs q = s.regs q := fun q h1 h2 => by
    rw [← hs6, State.setReg_regs_ne _ _ h1, State.setReg_regs_ne _ _ h2, hr4 q h1, hr3 q h1]
  obtain ⟨s7, t7, ex7, ht7, hri7, hpos7, hK7, ha7, hr7⟩ :=
    Triple.forUp_const (w := w) (keyInv (n := n) (N := N) (repA := repA) (rankA := rankA)
      (L := L) M (N :: bvRanks V rankA Wa) s6) L.length 20 (r_i := ri) (hi := .len aL)
      (body := keyBody) (by omega) (by omega)
      (fun i _ s' hs' => ⟨hs'.1, ev_len (by rw [hs'.2.2.2.1 aL (by decide),
        ha6 aL (by decide), hL0]) (by omega)⟩)
      (fun i hi => keyStep (by rw [ha6 aL (by decide), hL0])
        (by rw [ha6 aRep (by decide), hRep0]) (by rw [ha6 aRank (by decide), hRank0])
        (by rw [hr6 rn (by decide) (by decide), hrn]) (by rw [hr6 rN (by decide) (by decide), hrN])
        hLn (by simp [bvRanks]; omega) (by omega) hrk hrp hi) s6
      ⟨by rw [← hs6]; simp, by rw [← hs6]; simp [bvRanks]; omega,
        by rw [← hs6]; simpa using hK4, fun _ _ => rfl, fun _ _ _ _ => rfl⟩
  rw [List.take_of_length_le le_rfl] at hpos7 hK7
  generalize hKdef : N :: bvRanks V rankA Wa ++ L.flatMap (keyOne n N repA rankA) = K at hpos7 hK7
  have hKlen : K.length ≤ M := by
    have := length_flatMap_keyOne_le (n := n) (N := N) (repA := repA) (rankA := rankA) L
    rw [← hKdef]
    simp only [List.cons_append, List.length_cons, List.length_append, bvRanks, List.length_map,
      List.length_range]
    omega
  have hKw : ∀ v ∈ K, v < 2 ^ w := by
    intro v hv
    rw [← hKdef] at hv
    simp only [List.cons_append, List.mem_cons, List.mem_append, bvRanks, List.mem_map,
      List.mem_range, List.mem_flatMap] at hv
    rcases hv with rfl | ⟨u, hu, rfl⟩ | ⟨v', hv', hv⟩
    · exact hNw
    · exact hrk _ (hWn u hu)
    · unfold keyOne at hv
      have := hLn v' hv'
      split_ifs at hv with h1 h2
      · simp at hv; omega
      · simp at hv; rw [hv]; exact hrk _ (by omega)
      · simp at hv
  -- copy the key into its own array
  have ex8 : Exec w (.alloc aKey (.reg rpos)) s7 (s7.setArr aKey (List.replicate K.length 0)) _ :=
    .alloc (ev_reg hpos7 (by omega))
  have ex9 : Exec w (.assign rA (.const 0)) (s7.setArr aKey (List.replicate K.length 0))
      ((s7.setArr aKey (List.replicate K.length 0)).setReg rA 0) _ := .assign (ev_const (by omega))
  have ex10 : Exec w (.assign rB (.const 0)) ((s7.setArr aKey (List.replicate K.length 0)).setReg rA 0)
      (((s7.setArr aKey (List.replicate K.length 0)).setReg rA 0).setReg rB 0) _ :=
    .assign (ev_const (by omega))
  generalize hs10 : ((s7.setArr aKey (List.replicate K.length 0)).setReg rA 0).setReg rB 0 = s10
    at ex10
  have hvals : ∀ v ∈ tab M (preTab K K.length), v < 2 ^ w := by
    intro v hv
    obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.mp hv
    have hj' : j < M := by simpa using hj
    rw [← List.getD_eq_getElem _ 0 hj, getD_tab _ hj']
    simp only [preTab]
    split_ifs with h
    · rw [List.getD_eq_getElem _ _ h]; exact hKw _ (List.getElem_mem _)
    · omega
  obtain ⟨s11, t11, ex11, ht11, hKey11, ha11, hr11⟩ := copyProg_exec aK aKey rA rB rpos rt
    (by decide) (by decide) (by decide) (by decide) (s := s10) (m := K.length) (f := fun _ => 0)
    (cur := 0) (pos := 0) (cnt := K.length) (L := tab M (preTab K K.length)) (by omega)
    (by rw [← hs10]; simp [State.setArr_arrs_ne, hK7])
    (by rw [← hs10]; simp [replicate_eq_tab])
    (by rw [← hs10]; simp) (by rw [← hs10]; simp)
    (by rw [← hs10]; simp [State.setReg_regs_ne, hpos7]) (by omega) (by simp; omega)
    (by simp; omega) hvals
  refine ⟨s11, _, .seq ex1 (.seq ex2 (.seq ex3 (.seq ex4 (.seq ex5 (.seq ex6 (.seq ex7 (.seq ex8
    (.seq ex9 (.seq ex10 ex11))))))))), ?_, ?_, ?_, ?_⟩
  · simp only [Expr.cost] at ht4 ht7 ht11 ⊢
    have : L.length * (1 + 6 + 20) ≤ 27 * L.length := by omega
    omega
  · rw [hKey11, ← hKdef]
    conv_rhs => rw [eq_tab (N :: bvRanks V rankA Wa ++ L.flatMap (keyOne n N repA rankA))]
    rw [hKdef]
    refine tab_congr fun j hj => ?_
    rw [if_pos ⟨Nat.zero_le _, by omega⟩, Nat.zero_add, Nat.sub_zero, getD_tab _ (by omega)]
    simp [preTab, hj]
  · intro a h1 h2
    rw [ha11 a h2, ← hs10]
    simp only [State.setReg_arrs, State.setArr_arrs_ne _ _ h2]
    rw [ha7 a h1, ha6 a h1]
  · intro q h1 h2 h3 h4 h5 h6
    rw [hr11 q h6, ← hs10]
    simp only [State.setReg_regs_ne _ _ h5, State.setReg_regs_ne _ _ h4, State.setArr_regs]
    rw [hr7 q h1 h2 h3, hr6 q h1 h2]

end Alg92

end GraphMinor.Compute
