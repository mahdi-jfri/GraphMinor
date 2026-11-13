module

public import GraphMinor.Compute.Algorithm92LiftStar

/-!
# Graph Minors XIII, (9.2): the program that lifts an `(l, m)`-star (`Algorithm92LiftStarRun.lean`)

The stored answer `0 :: c :: encHPaths rays` of the compressed copy of `H ∪ F` is read ray by
ray; each ray is lifted into the work array `aBuf` (`rayBody`), and the result is copied to the
output array (`starProg_exec`, on plain lists).
-/

@[expose] public section

namespace GraphMinor.Compute

namespace Alg92

/-- The program that writes the lifted star. -/
def starProg (l : ℕ) : Cmd :=
  .seq (.alloc aBuf (.op .add (.op .mul (.len aAns) (.op .add (.len aL) (.const 1))) (.const 3))) <|
  .seq (.write aBuf (.const 0) (.const 0)) <|
  .seq (.write aBuf (.const 1) (.read aE (.read aAns (.const 1)))) <|
  .seq (.assign rpos (.const 2)) <|
  .seq (.assign rcur (.const 2)) <|
  .seq (.assign rO (.const 0)) <|
  .seq (forUp rO (.const l) rayBody) <|
  .seq (.alloc outArr (.reg rpos)) <|
  .seq (.assign rA (.const 0)) <|
  .seq (.assign rB (.const 0)) (copyProg aBuf outArr rA rB rpos rt)

variable {E L : List ℕ} {nd : ℕ → Bool} {rsA enA rankA : ℕ → ℕ} {n : ℕ}

variable (E L nd rsA enA rankA) in
/-- The lifted rays, each with its length in front. -/
def liftRays (rays : List (List ℕ)) : List ℕ :=
  (rays.map (fun r => lenPre (liftN E L nd rsA enA rankA r r.length))).flatten

theorem getD_ans {c : ℕ} {rays : List (List ℕ)} {j : ℕ} (hj : j < rays.length) :
    (0 :: c :: (rays.map lenPre).flatten).getD (2 + ((rays.map lenPre).take j).flatten.length) 0 =
      rays[j].length ∧
    ∀ t < rays[j].length, (0 :: c :: (rays.map lenPre).flatten).getD
      (2 + ((rays.map lenPre).take j).flatten.length + 1 + t) 0 = rays[j].getD t 0 := by
  obtain ⟨h1, h2⟩ := getD_lenPre_flatten rays hj
  refine ⟨?_, fun t ht => ?_⟩
  · rw [show 2 + ((rays.map lenPre).take j).flatten.length =
      ((rays.map lenPre).take j).flatten.length + 1 + 1 by omega, List.getD_cons_succ,
      List.getD_cons_succ, h1]
  · rw [show 2 + ((rays.map lenPre).take j).flatten.length + 1 + t =
      (((rays.map lenPre).take j).flatten.length + 1 + t) + 1 + 1 by omega, List.getD_cons_succ,
      List.getD_cons_succ, h2 t ht]

theorem length_ans_le {c : ℕ} {rays : List (List ℕ)} {j : ℕ} (hj : j < rays.length) :
    2 + ((rays.map lenPre).take j).flatten.length + 1 + rays[j].length ≤
      (0 :: c :: (rays.map lenPre).flatten).length := by
  have := length_flatten_take_succ (rays.map lenPre) (j := j) (by simpa using hj)
  have h2 := length_flatten_take_le (rays.map lenPre) (j + 1)
  simp only [List.getElem_map, lenPre, List.length_cons] at this ⊢
  omega

theorem liftRays_take_succ {rays : List (List ℕ)} {j : ℕ} (hj : j < rays.length) :
    liftRays E L nd rsA enA rankA (rays.take (j + 1)) =
      liftRays E L nd rsA enA rankA (rays.take j) ++
        ((liftN E L nd rsA enA rankA rays[j] rays[j].length).length ::
          liftN E L nd rsA enA rankA rays[j] rays[j].length) := by
  unfold liftRays
  rw [List.take_add_one, List.getElem?_eq_getElem hj, Option.toList_some, List.map_append,
    List.flatten_append, List.map_singleton, List.flatten_singleton]
  rfl

theorem lt_of_getD {K : List ℕ} {b : ℕ} (hK : ∀ u ∈ K, u < b) (hb : 0 < b) (i : ℕ) :
    K.getD i 0 < b := by
  rcases Nat.lt_or_ge i K.length with h | h
  · rw [List.getD_eq_getElem _ _ h]; exact hK _ (List.getElem_mem h)
  · rw [List.getD_eq_default _ _ h]; exact hb

theorem lt_of_mem_liftN {b : ℕ} (hE : ∀ u ∈ E, u < b) (hL : ∀ u ∈ L, u < b) (hb : 0 < b)
    (ray : List ℕ) (t : ℕ) : ∀ u ∈ liftN E L nd rsA enA rankA ray t, u < b := by
  intro u hu
  simp only [liftN, List.mem_flatMap, List.mem_range] at hu
  obtain ⟨i, -, hi⟩ := hu
  unfold stepPiece pieceN at hi
  split_ifs at hi <;> (try simp only [List.mem_singleton, List.mem_reverse] at hi) <;>
    first
    | (rw [hi]; exact lt_of_getD hE hb _)
    | exact hL _ (List.mem_of_mem_drop (List.mem_of_mem_take hi))

theorem lt_of_mem_liftRays {b : ℕ} (hE : ∀ u ∈ E, u < b) (hL : ∀ u ∈ L, u < b) (hb : 0 < b)
    {rays : List (List ℕ)} (hr : ∀ r ∈ rays, r.length * (L.length + 1) < b) :
    ∀ u ∈ liftRays E L nd rsA enA rankA rays, u < b := by
  intro u hu
  simp only [liftRays, List.mem_flatten, List.mem_map] at hu
  obtain ⟨_, ⟨r, hr', rfl⟩, hu⟩ := hu
  rcases List.mem_cons.mp hu with rfl | hu
  · exact lt_of_le_of_lt (length_liftN_le r r.length) (hr r hr')
  · exact lt_of_mem_liftN hE hL hb r r.length u hu

theorem length_lt_flatten_lenPre {rays : List (List ℕ)} {r : List ℕ} (h : r ∈ rays) :
    r.length < (rays.map lenPre).flatten.length := by
  induction rays with
  | nil => simp at h
  | cons q rs ih =>
    simp only [List.map_cons, List.flatten_cons, List.length_append, lenPre, List.length_cons]
    rcases List.mem_cons.mp h with rfl | h
    · omega
    · have := ih h; omega

theorem length_le_flatten_lenPre (rays : List (List ℕ)) :
    rays.length ≤ (rays.map lenPre).flatten.length := by
  induction rays with
  | nil => simp
  | cons q rs ih =>
    simp only [List.map_cons, List.flatten_cons, List.length_append, lenPre, List.length_cons]
    omega

theorem tab_preTab_copy {P : List ℕ} {Mb : ℕ} (hP : P.length ≤ Mb) :
    tab P.length (fun j => if 0 ≤ j ∧ j < 0 + P.length then
      (tab Mb (preTab P P.length)).getD (0 + (j - 0)) 0 else 0) = P := by
  rw [tab_eq_iff]
  refine ⟨rfl, fun j hj => ?_⟩
  rw [if_pos ⟨Nat.zero_le _, by omega⟩, Nat.zero_add, Nat.sub_zero, getD_tab _ (by omega)]
  simp [preTab, hj]

/-- **The program that lifts a star**, on plain lists. -/
theorem starProg_exec {w l : ℕ} {s : State} {c : ℕ} {rays : List (List ℕ)}
    (hE : s.arrs aE = tab n (fun c => E.getD c 0))
    (hN : s.arrs aN = tab (n + 1) (fun u => if nd u then 1 else 0))
    (hRS : s.arrs aRS = tab (n + 1) rsA) (hEn : s.arrs aEn = tab L.length enA)
    (hL : s.arrs aL = L) (hRank : s.arrs aRank = tab n rankA)
    (hA : s.arrs aAns = 0 :: c :: (rays.map lenPre).flatten) (hl : rays.length = l)
    (hc : c < n) (hEc : E.getD c 0 < n)
    (hgood : ∀ r ∈ rays, ∀ v ∈ r, GoodV E L nd rsA enA n v)
    (hLw : ∀ u ∈ L, u < 2 ^ w) (hAw : ∀ u ∈ 0 :: c :: (rays.map lenPre).flatten, u < 2 ^ w)
    (hrk : ∀ u < n, rankA u < 2 ^ w) (hEw : ∀ u ∈ E, u < 2 ^ w)
    (hB : 2 * ((0 :: c :: (rays.map lenPre).flatten).length * (L.length + 1) + 3) + L.length +
      (0 :: c :: (rays.map lenPre).flatten).length + n + 4 < 2 ^ w) :
    ∃ s' t, Exec w (starProg l) s s' t ∧
      t ≤ 60 + l * (37 + (0 :: c :: (rays.map lenPre).flatten).length * (67 + 15 * L.length)) +
        17 * ((0 :: c :: (rays.map lenPre).flatten).length * (L.length + 1) + 3) ∧
      s'.arrs outArr = 0 :: E.getD c 0 :: liftRays E L nd rsA enA rankA rays ∧
      (∀ a, a ≠ aBuf → a ≠ outArr → s'.arrs a = s.arrs a) := by
  have hAlenR : rays.length ≤ (0 :: c :: (rays.map lenPre).flatten).length := by
    have := length_le_flatten_lenPre rays; simp only [List.length_cons]; omega
  have hrayA : ∀ r ∈ rays, r.length ≤ (0 :: c :: (rays.map lenPre).flatten).length := by
    intro r hr; have := length_lt_flatten_lenPre hr; simp only [List.length_cons]; omega
  have hlenA : (0 :: c :: (rays.map lenPre).flatten).length =
      2 + ((rays.map lenPre).take l).flatten.length := by
    rw [← hl, ← List.length_map (f := lenPre), List.take_length]; simp; omega
  generalize hAdef : 0 :: c :: (rays.map lenPre).flatten = A at hA hAw hB hAlenR hrayA hlenA ⊢
  have hA1 : A.getD 1 0 = c := by rw [← hAdef]; rfl
  have hAlen2 : 2 ≤ A.length := by rw [← hAdef]; simp
  -- the work array, with `0` and the center
  have ex1 : Exec w (.alloc aBuf (.op .add (.op .mul (.len aAns) (.op .add (.len aL) (.const 1)))
      (.const 3))) s (s.setArr aBuf (List.replicate (A.length * (L.length + 1) + 3) 0)) _ :=
    .alloc (ev_add (ev_mul (ev_len (a := aAns) (by rw [hA]) (by omega))
      (ev_add (ev_len (a := aL) (by rw [hL]) (by omega)) (ev_const (v := 1) (by omega)) (by omega))
      (by nlinarith)) (ev_const (v := 3) (by omega)) (by omega))
  generalize hMb : A.length * (L.length + 1) + 3 = Mb at hB ex1 ⊢
  generalize hs1 : s.setArr aBuf (List.replicate Mb 0) = s1 at ex1
  have ha1 : ∀ a, a ≠ aBuf → s1.arrs a = s.arrs a := fun a h => by
    rw [← hs1, State.setArr_arrs_ne _ _ h]
  have ex2 : Exec w (.write aBuf (.const 0) (.const 0)) s1 (s1.writeArr aBuf 0 0) _ :=
    .write (ev_const (by omega)) (ev_const (by omega)) (by rw [← hs1]; simp; omega)
  have hw2 : ∀ a, a ≠ aBuf → (s1.writeArr aBuf 0 0).arrs a = s.arrs a := fun a h => by
    rw [State.writeArr_arrs_ne _ _ _ h, ha1 a h]
  have ex3 : Exec w (.write aBuf (.const 1) (.read aE (.read aAns (.const 1)))) (s1.writeArr aBuf 0 0)
      ((s1.writeArr aBuf 0 0).writeArr aBuf 1 (E.getD c 0)) _ :=
    .write (ev_const (by omega))
      (ev_read (ev_read (ev_const (by omega)) (by rw [hw2 _ (by decide), hA]; omega)
        (by rw [hw2 _ (by decide), hA, hA1]) (by omega)) (by rw [hw2 _ (by decide), hE]; simpa using hc)
        (by rw [hw2 _ (by decide), hE, getD_tab _ hc]) (by omega))
      (by rw [← hs1]; simp; omega)
  generalize hs3 : (s1.writeArr aBuf 0 0).writeArr aBuf 1 (E.getD c 0) = s3 at ex3
  have hBuf3 : s3.arrs aBuf = tab Mb (preTab [0, E.getD c 0] [0, E.getD c 0].length) := by
    rw [← hs3, ← hs1]
    simp only [State.writeArr_arrs_self, State.setArr_arrs_self, replicate_eq_tab]
    rw [tab_set _ (by omega), tab_set _ (by omega)]
    refine tab_congr fun j _ => ?_
    simp only [Function.update_apply, preTab, List.length_cons, List.length_nil]
    rcases j with _ | _ | j <;> simp
  have ha3 : ∀ a, a ≠ aBuf → s3.arrs a = s.arrs a := fun a h => by
    rw [← hs3, State.writeArr_arrs_ne _ _ _ h, State.writeArr_arrs_ne _ _ _ h, ha1 a h]
  have ex4 : Exec w (.assign rpos (.const 2)) s3 (s3.setReg rpos 2) _ := .assign (ev_const (by omega))
  have ex5 : Exec w (.assign rcur (.const 2)) (s3.setReg rpos 2) ((s3.setReg rpos 2).setReg rcur 2) _ :=
    .assign (ev_const (by omega))
  have ex6 : Exec w (.assign rO (.const 0)) ((s3.setReg rpos 2).setReg rcur 2)
      (((s3.setReg rpos 2).setReg rcur 2).setReg rO 0) _ := .assign (ev_const (by omega))
  generalize hs6 : ((s3.setReg rpos 2).setReg rcur 2).setReg rO 0 = s6 at ex6
  -- the loop over the rays
  let I (j : ℕ) (u : State) : Prop :=
    u.regs rO = j ∧ u.regs rcur = 2 + ((rays.map lenPre).take j).flatten.length ∧
      u.regs rpos = ([0, E.getD c 0] ++ liftRays E L nd rsA enA rankA (rays.take j)).length ∧
      u.arrs aBuf = tab Mb (preTab ([0, E.getD c 0] ++ liftRays E L nd rsA enA rankA (rays.take j))
        ([0, E.getD c 0] ++ liftRays E L nd rsA enA rankA (rays.take j)).length) ∧
      ([0, E.getD c 0] ++ liftRays E L nd rsA enA rankA (rays.take j)).length + 2 * (L.length + 1) ≤
        2 + (2 + ((rays.map lenPre).take j).flatten.length) * (L.length + 1) ∧
      (∀ a, a ≠ aBuf → u.arrs a = s.arrs a)
  have hI0 : I 0 s6 := ⟨by rw [← hs6]; simp, by rw [← hs6]; simp, by rw [← hs6]; simp [liftRays],
    by rw [← hs6]; simpa [liftRays] using hBuf3, by simp [liftRays],
    fun a h => by rw [← hs6]; simp only [State.setReg_arrs]; exact ha3 a h⟩
  have hlw : l < 2 ^ w := by omega
  obtain ⟨u, tl, exl, htl, hu1, hu2, hu3, hu4, hu5, hu6⟩ :=
    Triple.forUp_const (w := w) I l (30 + A.length * (67 + 15 * L.length)) (r_i := rO)
      (hi := .const l) (body := rayBody) (by omega) hlw
      (fun j _ u hu => ⟨hu.1, ev_const hlw⟩) (fun j hj => by
        rintro u ⟨hu1, hu2, hu3, hu4, hu5, hu6⟩
        have hjr : j < rays.length := by omega
        obtain ⟨g1, g2⟩ := getD_ans (c := c) hjr
        have hAl := length_ans_le (c := c) hjr
        rw [hAdef] at g1 g2 hAl
        have hfl := length_flatten_take_succ (rays.map lenPre) (j := j) (by simpa using hjr)
        simp only [List.getElem_map, lenPre, List.length_cons] at hfl
        have hrl : rays[j].length * (L.length + 1) +
            (2 + ((rays.map lenPre).take j).flatten.length) * (L.length + 1) ≤
              A.length * (L.length + 1) := by
          rw [← Nat.add_mul]; exact Nat.mul_le_mul_right _ (by omega)
        have hrj : rays[j].length * (67 + 15 * L.length) ≤ A.length * (67 + 15 * L.length) :=
          Nat.mul_le_mul_right _ (hrayA _ (List.getElem_mem hjr))
        have hX := length_liftN_le (E := E) (L := L) (nd := nd) (rsA := rsA) (enA := enA)
          (rankA := rankA) rays[j] rays[j].length
        obtain ⟨u', t', ex', ht', hB', hpos', hcur', ha', hr'⟩ := rayBody_exec (w := w) (s := u)
          (P := [0, E.getD c 0] ++ liftRays E L nd rsA enA rankA (rays.take j)) (A := A)
          (ray := rays[j]) (Mb := Mb) (cur := 2 + ((rays.map lenPre).take j).flatten.length)
          (by rw [hu6 aE (by decide), hE]) (by rw [hu6 aN (by decide), hN])
          (by rw [hu6 aRS (by decide), hRS]) (by rw [hu6 aEn (by decide), hEn])
          (by rw [hu6 aL (by decide), hL]) (by rw [hu6 aRank (by decide), hRank])
          (by rw [hu6 aAns (by decide), hA]) hu4 hu2 hu3 (by omega) g1 g2
          (hgood _ (List.getElem_mem hjr)) (by omega) hLw hAw hrk (by omega)
        have hexp : (2 + (((rays.map lenPre).take j).flatten.length + (rays[j].length + 1))) *
            (L.length + 1) = (2 + ((rays.map lenPre).take j).flatten.length) * (L.length + 1) +
              rays[j].length * (L.length + 1) + (L.length + 1) := by ring
        refine ⟨u', t', ex', show t' ≤ 30 + A.length * (67 + 15 * L.length) by omega, ⟨by simp, ?_, ?_, ?_, ?_, fun a h => ?_⟩, ?_⟩
        · rw [State.setReg_regs_ne _ _ (by decide), hcur', hfl]; omega
        · rw [State.setReg_regs_ne _ _ (by decide), hpos', liftRays_take_succ hjr,
            List.append_assoc]
        · rw [State.setReg_arrs, hB', liftRays_take_succ hjr, List.append_assoc]
        · rw [liftRays_take_succ hjr, hfl, hexp]
          simp only [List.length_append, List.length_cons, List.length_nil] at hu5 ⊢
          omega
        · rw [State.setReg_arrs, ha' a h, hu6 a h]
        · rw [hr' rO (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
            (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), hu1]) s6 hI0
  have hT : rays.take l = rays := by rw [← hl, List.take_length]
  simp only [hT] at hu3 hu4 hu5
  rw [← hlenA] at hu5
  generalize hP : [0, E.getD c 0] ++ liftRays E L nd rsA enA rankA rays = P at hu3 hu4 hu5
  have hPM : P.length ≤ Mb := by
    have : 2 * (L.length + 1) ≤ 2 + A.length * (L.length + 1) + 1 := by nlinarith
    rw [← hMb]; omega
  have hPw : ∀ v ∈ P, v < 2 ^ w := by
    rw [← hP]
    intro v hv
    simp only [List.cons_append, List.nil_append, List.mem_cons] at hv
    rcases hv with rfl | rfl | hv
    · omega
    · omega
    · refine lt_of_mem_liftRays hEw hLw (by omega) (fun r hr => ?_) v hv
      have := Nat.mul_le_mul_right (L.length + 1) (hrayA r hr)
      omega
  have ex8 : Exec w (.alloc outArr (.reg rpos)) u (u.setArr outArr (List.replicate P.length 0)) _ :=
    .alloc (ev_reg hu3 (by omega))
  have ex9 : Exec w (.assign rA (.const 0)) (u.setArr outArr (List.replicate P.length 0))
      ((u.setArr outArr (List.replicate P.length 0)).setReg rA 0) _ := .assign (ev_const (by omega))
  have ex10 : Exec w (.assign rB (.const 0)) ((u.setArr outArr (List.replicate P.length 0)).setReg rA 0)
      (((u.setArr outArr (List.replicate P.length 0)).setReg rA 0).setReg rB 0) _ :=
    .assign (ev_const (by omega))
  generalize hs10 : ((u.setArr outArr (List.replicate P.length 0)).setReg rA 0).setReg rB 0 = s10
    at ex10
  obtain ⟨s', t11, ex11, ht11, hout, harr, -⟩ := copyProg_exec (w := w) (s := s10) aBuf outArr rA rB
    rpos rt (L := tab Mb (preTab P P.length)) (m := P.length) (f := fun _ => 0) (cur := 0) (pos := 0)
    (cnt := P.length) (by decide) (by decide) (by decide) (by decide) (by omega)
    (by rw [← hs10]; simp only [State.setReg_arrs]; rw [State.setArr_arrs_ne _ _ (by decide), hu4])
    (by rw [← hs10]; simp only [State.setReg_arrs, State.setArr_arrs_self, replicate_eq_tab])
    (by rw [← hs10]; simp [State.setReg_regs_ne])
    (by rw [← hs10]; simp [State.setReg_regs_ne])
    (by rw [← hs10]; simp [State.setReg_regs_ne, hu3])
    (by omega) (by simpa using hPM) (by simp; omega)
    (fun v hv => by
      simp only [tab, List.mem_map, List.mem_range] at hv
      obtain ⟨j, -, rfl⟩ := hv
      unfold preTab
      split_ifs
      · exact lt_of_getD hPw (by omega) _
      · omega)
  refine ⟨s', _, .seq ex1 (.seq ex2 (.seq ex3 (.seq ex4 (.seq ex5 (.seq ex6 (.seq exl (.seq ex8
    (.seq ex9 (.seq ex10 ex11))))))))), ?_, ?_, fun a h1 h2 => ?_⟩
  · simp only [Expr.cost] at htl ⊢
    rw [show 1 + 6 + (30 + A.length * (67 + 15 * L.length)) =
      37 + A.length * (67 + 15 * L.length) by ring] at htl
    omega
  · rw [hout, tab_preTab_copy hPM, ← hP]; rfl
  · rw [harr a h2, ← hs10]
    simp only [State.setReg_arrs]
    rw [State.setArr_arrs_ne _ _ h2, hu6 a h1]

end Alg92

end GraphMinor.Compute
