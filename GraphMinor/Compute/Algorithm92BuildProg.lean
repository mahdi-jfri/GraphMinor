module

public import GraphMinor.Compute.Algorithm92Build
import GraphMinor.Compute.Algorithm92Search

/-!
# Graph Minors XIII, (9.2): the program that writes the layout (`Algorithm92BuildProg.lean`)

The first program after `F` (page 101 of Graph Minors XIII). It reads `x.W.encList` and
`encSegs92 segs` and writes the layout of the paths of `H ∪ F` into the array `aL`. This file holds
the two loop bodies: `wallBody` writes the block of one path of the wall, and `segBody` the block
of one path of `F` (and marks the two ends of that path as nodes).
-/

@[expose] public section

namespace GraphMinor.Compute

namespace Alg92

open WallOfHeight

/-! ### Registers and arrays -/

/-- The arrays written by the program that finds `F`. -/
abbrev aG : ℕ := 2
abbrev aW : ℕ := 3
abbrev aF : ℕ := 4
/-- The layout, the node marks, the path marks, and the table of the edges of the elementary
wall. -/
abbrev aL : ℕ := 5
abbrev aN : ℕ := 6
abbrev aP : ℕ := 7
abbrev aEdge : ℕ := 16

abbrev rn : ℕ := 1
abbrev rpos : ℕ := 2
abbrev rcur : ℕ := 3
abbrev rcnt : ℕ := 4
abbrev ri : ℕ := 5
abbrev rt : ℕ := 6
abbrev rA : ℕ := 7
abbrev rB : ℕ := 8
abbrev rs : ℕ := 9
abbrev rtmp : ℕ := 10

/-- The entry of the array `aW` at index `3 + aEdge[e]`: a branch vertex at an end of a path of
the wall. -/
def bvAt (e : Expr) : Expr := .read aW (.op .add (.const 3) (.read aEdge e))

/-- Write the block of the `ri`-th path of the wall: the separator, the first branch vertex, the
inner vertices (copied from `aW`), and the last branch vertex. -/
def wallBody : Cmd :=
  .seq (.write aL (.reg rpos) (.reg rn)) <|
  .seq (.write aL (.op .add (.reg rpos) (.const 1)) (bvAt (.op .mul (.const 2) (.reg ri)))) <|
  .seq (.assign rcnt (.read aW (.reg rcur))) <|
  .seq (.assign rA (.op .add (.reg rcur) (.const 1))) <|
  .seq (.assign rB (.op .add (.reg rpos) (.const 2))) <|
  .seq (copyProg aW aL rA rB rcnt rt) <|
  .seq (.write aL (.op .add (.reg rB) (.reg rcnt))
    (bvAt (.op .add (.op .mul (.const 2) (.reg ri)) (.const 1)))) <|
  .seq (.assign rpos (.op .add (.op .add (.reg rB) (.reg rcnt)) (.const 1)))
    (.assign rcur (.op .add (.reg rA) (.reg rcnt)))

/-- The table of the ends of the edges of the elementary wall. -/
def edgeTab (h : ℕ) : List ℕ := (elemWallEdges h).flatMap (fun e => [e.1.val, e.2.val])

theorem getD_edgeTab {h k' : ℕ} (hk : k' < (elemWallEdges h).length) :
    (edgeTab h).getD (2 * k') 0 = ((elemWallEdges h)[k']).1.val ∧
    (edgeTab h).getD (2 * k' + 1) 0 = ((elemWallEdges h)[k']).2.val := by
  have key : ∀ (L : List (Fin (elemWallNumVerts h) × Fin (elemWallNumVerts h))) (j : ℕ)
      (hj : j < L.length),
      (L.flatMap (fun e => [e.1.val, e.2.val])).getD (2 * j) 0 = (L[j]).1.val ∧
      (L.flatMap (fun e => [e.1.val, e.2.val])).getD (2 * j + 1) 0 = (L[j]).2.val := by
    intro L
    induction L with
    | nil => intro j hj; simp at hj
    | cons e L ih =>
      intro j hj
      cases j with
      | zero => simp
      | succ j =>
        have := ih j (by simpa using hj)
        simp only [List.flatMap_cons, List.getElem_cons_succ]
        rw [show 2 * (j + 1) = 2 * j + 2 by ring, show 2 * j + 2 + 1 = 2 * j + 1 + 2 by ring]
        simpa using this
  exact key _ _ hk

theorem length_edgeTab (h : ℕ) : (edgeTab h).length = 2 * (elemWallEdges h).length := by
  simp [edgeTab, List.length_flatMap]
  ring

theorem lt_of_mem_edgeTab {h v : ℕ} (hv : v ∈ edgeTab h) : v < elemWallNumVerts h := by
  simp only [edgeTab, List.mem_flatMap, List.mem_cons, List.not_mem_nil, or_false] at hv
  obtain ⟨e, -, rfl | rfl⟩ := hv
  · exact e.1.2
  · exact e.2.2

variable {l m p h k r : ℕ} {x : Alg92Input l m p h k r} {segs : List (List (Fin x.n))}

/-- The layout written up to position `q`. -/
noncomputable def lpre (x : Alg92Input l m p h k r) (segs : List (List (Fin x.n))) (q : ℕ) :
    ℕ → ℕ :=
  fun j => if j < q then (layout x segs).getD j 0 else 0

theorem lt_of_mem_encList {v : ℕ} (hv : v ∈ x.W.encList) :
    v ≤ h + elemWallNumVerts h + (elemWallEdges h).length + x.n := by
  have hlen := length_internalVerts_le_of_isValid x.hW_valid.2.2
  simp only [WallOfHeight.encList, List.mem_append, List.mem_cons, List.mem_map, List.mem_flatMap,
    List.mem_finRange, true_and, List.not_mem_nil, or_false] at hv
  rcases hv with ((rfl | rfl | rfl) | ⟨u, rfl⟩) | ⟨k', rfl | ⟨y, -, rfl⟩⟩
  · omega
  · omega
  · omega
  · have := (x.W.branchVert u).2; omega
  · have := hlen k'; omega
  · have := y.2; omega

/-- The array `Lay` written up to position `q`. -/
def preTab (Lay : List ℕ) (q : ℕ) : ℕ → ℕ := fun j => if j < q then Lay.getD j 0 else 0

/-- **The body of the wall loop**, on plain lists: it copies one block of `Lay` from `Wa` and the
edge table `Et`. -/
theorem wallBody_exec {w : ℕ} {s : State} {Wa Et Lay : List ℕ} {M nv p0 c0 kk cnt u1 u2 : ℕ}
    (hrn : s.regs rn = nv) (hpos : s.regs rpos = p0) (hcur : s.regs rcur = c0)
    (hri : s.regs ri = kk)
    (hL : s.arrs aL = tab M (preTab Lay p0)) (hW : s.arrs aW = Wa) (hE : s.arrs aEdge = Et)
    (hcnt : Wa.getD c0 0 = cnt) (hcopy : ∀ t < cnt, Wa.getD (c0 + 1 + t) 0 = Lay.getD (p0 + 2 + t) 0)
    (hu1 : Et.getD (2 * kk) 0 = u1) (hu2 : Et.getD (2 * kk + 1) 0 = u2)
    (hb1 : Wa.getD (3 + u1) 0 = Lay.getD (p0 + 1) 0)
    (hb2 : Wa.getD (3 + u2) 0 = Lay.getD (p0 + 2 + cnt) 0) (hsep : Lay.getD p0 0 = nv)
    (hfit : p0 + 3 + cnt ≤ M) (hcfit : c0 + 1 + cnt ≤ Wa.length) (hu1W : 3 + u1 < Wa.length)
    (hu2W : 3 + u2 < Wa.length) (hkE : 2 * kk + 1 < Et.length)
    (hvW : ∀ v ∈ Wa, v < 2 ^ w) (hvE : ∀ v ∈ Et, v < 2 ^ w) (hnv : nv < 2 ^ w)
    (hbig : M + Wa.length + Et.length + 4 < 2 ^ w) :
    ∃ s' t, Exec w wallBody s s' t ∧ t ≤ 53 + 15 * cnt ∧
      s'.regs rpos = p0 + 3 + cnt ∧ s'.regs rcur = c0 + 1 + cnt ∧
      s'.arrs aL = tab M (preTab Lay (p0 + 3 + cnt)) ∧
      (∀ a, a ≠ aL → s'.arrs a = s.arrs a) ∧
      (∀ r, r ≠ rpos → r ≠ rcur → r ≠ rcnt → r ≠ rA → r ≠ rB → r ≠ rt → s'.regs r = s.regs r) := by
  have hw1 : 1 < 2 ^ w := by omega
  have gW : ∀ i < Wa.length, Wa.getD i 0 < 2 ^ w := fun i hi => by
    rw [List.getD_eq_getElem _ _ hi]; exact hvW _ (List.getElem_mem _)
  have gE : ∀ i < Et.length, Et.getD i 0 < 2 ^ w := fun i hi => by
    rw [List.getD_eq_getElem _ _ hi]; exact hvE _ (List.getElem_mem _)
  -- step 1: the separator
  have ex1 : Exec w (.write aL (.reg rpos) (.reg rn)) s (s.writeArr aL p0 nv) _ :=
    .write (ev_reg hpos (by omega)) (ev_reg hrn hnv) (by rw [hL]; simp; omega)
  have hL1 := writeArr_tab hL (show p0 < M by omega) nv
  have hE1 : (s.writeArr aL p0 nv).arrs aEdge = Et := by
    rw [State.writeArr_arrs_ne _ _ _ (by decide), hE]
  have hW1 : (s.writeArr aL p0 nv).arrs aW = Wa := by
    rw [State.writeArr_arrs_ne _ _ _ (by decide), hW]
  -- step 2: the first branch vertex
  have hidx2 : (Expr.op .mul (.const 2) (.reg ri)).eval w (s.writeArr aL p0 nv) = some (2 * kk) :=
    ev_mul (ev_const (by omega)) (ev_reg (by simp [State.writeArr_regs, hri]) (by omega)) (by omega)
  have hed2 : (Expr.read aEdge (.op .mul (.const 2) (.reg ri))).eval w (s.writeArr aL p0 nv) =
      some u1 :=
    ev_read hidx2 (by rw [hE1]; omega) (by rw [hE1, hu1]) (hu1 ▸ gE _ (by omega))
  have hval2 : (bvAt (.op .mul (.const 2) (.reg ri))).eval w (s.writeArr aL p0 nv) =
      some (Lay.getD (p0 + 1) 0) :=
    ev_read (ev_add (ev_const (by omega)) hed2 (by omega)) (by rw [hW1]; omega)
      (by rw [hW1, hb1]) (hb1 ▸ gW _ hu1W)
  have ex2 := Exec.write (a := aL) (idx := .op .add (.reg rpos) (.const 1))
    (ev_add (ev_reg (v := p0) (by simp [State.writeArr_regs, hpos]) (by omega))
      (ev_const (v := 1) (by omega)) (by omega)) hval2 (by rw [hL1]; simp; omega)
  have hL2 := writeArr_tab hL1 (show p0 + 1 < M by omega) (Lay.getD (p0 + 1) 0)
  -- steps 3 to 5: registers
  generalize hs2 : (s.writeArr aL p0 nv).writeArr aL (p0 + 1) (Lay.getD (p0 + 1) 0) = s2 at ex2 hL2
  have hr2 : s2.regs = s.regs := by rw [← hs2]; rfl
  have ha2 : ∀ a, a ≠ aL → s2.arrs a = s.arrs a := fun a ha => by
    rw [← hs2, State.writeArr_arrs_ne _ _ _ ha, State.writeArr_arrs_ne _ _ _ ha]
  have hW2 : s2.arrs aW = Wa := by rw [ha2 aW (by decide), hW]
  have hE2 : s2.arrs aEdge = Et := by rw [ha2 aEdge (by decide), hE]
  have ex3 : Exec w (.assign rcnt (.read aW (.reg rcur))) s2 (s2.setReg rcnt cnt) _ :=
    .assign (ev_read (ev_reg (by rw [hr2, hcur]) (by omega)) (by rw [hW2]; omega)
      (by rw [hW2, hcnt]) (hcnt ▸ gW _ (by omega)))
  have ex4 : Exec w (.assign rA (.op .add (.reg rcur) (.const 1))) (s2.setReg rcnt cnt)
      ((s2.setReg rcnt cnt).setReg rA (c0 + 1)) _ :=
    .assign (ev_add (ev_reg (by rw [State.setReg_regs_ne _ _ (by decide), hr2, hcur]) (by omega))
      (ev_const (by omega)) (by omega))
  have ex5 : Exec w (.assign rB (.op .add (.reg rpos) (.const 2)))
      ((s2.setReg rcnt cnt).setReg rA (c0 + 1))
      (((s2.setReg rcnt cnt).setReg rA (c0 + 1)).setReg rB (p0 + 2)) _ :=
    .assign (ev_add (ev_reg (by rw [State.setReg_regs_ne _ _ (by decide),
      State.setReg_regs_ne _ _ (by decide), hr2, hpos]) (by omega)) (ev_const (by omega))
      (by omega))
  generalize hs5 : ((s2.setReg rcnt cnt).setReg rA (c0 + 1)).setReg rB (p0 + 2) = s5 at ex5
  have hr5 : ∀ r, r ≠ rB → r ≠ rA → r ≠ rcnt → s5.regs r = s.regs r := fun r h1 h2 h3 => by
    rw [← hs5, State.setReg_regs_ne _ _ h1, State.setReg_regs_ne _ _ h2,
      State.setReg_regs_ne _ _ h3, hr2]
  have ha5 : ∀ a, s5.arrs a = s2.arrs a := fun a => by rw [← hs5]; rfl
  -- step 6: the inner vertices
  obtain ⟨s6, t6, ex6, ht6, hL6, ha6, hr6⟩ := copyProg_exec aW aL rA rB rcnt rt (by decide)
    (by decide) (by decide) (by decide) (s := s5) (cur := c0 + 1) (pos := p0 + 2) (cnt := cnt)
    hw1 (by rw [ha5, hW2]) (by rw [ha5]; exact hL2) (by simp [← hs5, State.setReg_regs_ne])
    (by simp [← hs5]) (by simp [← hs5, State.setReg_regs_ne]) (by omega) (by omega)
    (by omega) hvW
  have hs6ri : s6.regs ri = kk := by rw [hr6 ri (by decide), hr5 ri (by decide) (by decide) (by decide), hri]
  have hs6B : s6.regs rB = p0 + 2 := by rw [hr6 rB (by decide), ← hs5]; simp
  have hs6A : s6.regs rA = c0 + 1 := by rw [hr6 rA (by decide), ← hs5]; simp [State.setReg_regs_ne]
  have hs6c : s6.regs rcnt = cnt := by rw [hr6 rcnt (by decide), ← hs5]; simp [State.setReg_regs_ne]
  have hW6 : s6.arrs aW = Wa := by rw [ha6 aW (by decide), ha5, hW2]
  have hE6 : s6.arrs aEdge = Et := by rw [ha6 aEdge (by decide), ha5, hE2]
  -- step 7: the last branch vertex
  have hidx7 : (Expr.op .add (.op .mul (.const 2) (.reg ri)) (.const 1)).eval w s6 =
      some (2 * kk + 1) :=
    ev_add (ev_mul (ev_const (by omega)) (ev_reg hs6ri (by omega)) (by omega))
      (ev_const (by omega)) (by omega)
  have hed7 : (Expr.read aEdge (.op .add (.op .mul (.const 2) (.reg ri)) (.const 1))).eval w s6 =
      some u2 :=
    ev_read hidx7 (by rw [hE6]; omega) (by rw [hE6, hu2]) (hu2 ▸ gE _ (by omega))
  have hval7 : (bvAt (.op .add (.op .mul (.const 2) (.reg ri)) (.const 1))).eval w s6 =
      some (Lay.getD (p0 + 2 + cnt) 0) :=
    ev_read (ev_add (ev_const (by omega)) hed7 (by omega)) (by rw [hW6]; omega)
      (by rw [hW6, hb2]) (hb2 ▸ gW _ hu2W)
  have ex7 := Exec.write (a := aL) (idx := .op .add (.reg rB) (.reg rcnt))
    (ev_add (ev_reg hs6B (by omega)) (ev_reg hs6c (by omega)) (by omega)) hval7
    (by rw [hL6]; simp; omega)
  have hL7 := writeArr_tab hL6 (show p0 + 2 + cnt < M by omega) (Lay.getD (p0 + 2 + cnt) 0)
  generalize hs7 : s6.writeArr aL (p0 + 2 + cnt) (Lay.getD (p0 + 2 + cnt) 0) = s7 at ex7 hL7
  have hr7 : s7.regs = s6.regs := by rw [← hs7]; rfl
  have ex8 : Exec w (.assign rpos (.op .add (.op .add (.reg rB) (.reg rcnt)) (.const 1))) s7
      (s7.setReg rpos (p0 + 2 + cnt + 1)) _ :=
    .assign (ev_add (ev_add (ev_reg (by rw [hr7, hs6B]) (by omega))
      (ev_reg (by rw [hr7, hs6c]) (by omega)) (by omega)) (ev_const (by omega)) (by omega))
  have ex9 : Exec w (.assign rcur (.op .add (.reg rA) (.reg rcnt))) (s7.setReg rpos (p0 + 2 + cnt + 1))
      ((s7.setReg rpos (p0 + 2 + cnt + 1)).setReg rcur (c0 + 1 + cnt)) _ :=
    .assign (ev_add (ev_reg (by rw [State.setReg_regs_ne _ _ (by decide), hr7, hs6A]) (by omega))
      (ev_reg (by rw [State.setReg_regs_ne _ _ (by decide), hr7, hs6c]) (by omega)) (by omega))
  refine ⟨_, _, .seq ex1 (.seq ex2 (.seq ex3 (.seq ex4 (.seq ex5 (.seq ex6 (.seq ex7
    (.seq ex8 ex9))))))), ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [Expr.cost, bvAt]; omega
  · rw [State.setReg_regs_ne _ _ (by decide), State.setReg_regs_self]; omega
  · rw [State.setReg_regs_self]
  · rw [State.setReg_arrs, State.setReg_arrs, hL7]
    refine tab_congr fun j _ => ?_
    simp only [Function.update_apply, preTab]
    by_cases hj1 : j = p0 + 2 + cnt
    · subst hj1; rw [if_pos rfl, if_pos (by omega)]
    rw [if_neg hj1]
    by_cases hj2 : p0 + 2 ≤ j ∧ j < p0 + 2 + cnt
    · rw [if_pos hj2, if_pos (by omega)]
      obtain ⟨t, rfl⟩ : ∃ t, j = p0 + 2 + t := ⟨j - (p0 + 2), by omega⟩
      rw [show c0 + 1 + (p0 + 2 + t - (p0 + 2)) = c0 + 1 + t by omega, hcopy t (by omega)]
    rw [if_neg hj2]
    by_cases hj3 : j = p0 + 1
    · subst hj3; rw [if_pos rfl, if_pos (by omega)]
    rw [if_neg hj3]
    by_cases hj4 : j = p0
    · subst hj4; rw [if_pos rfl, if_pos (by omega), hsep]
    rw [if_neg hj4]
    by_cases hj5 : j < p0
    · rw [if_pos hj5, if_pos (by omega)]
    · rw [if_neg hj5, if_neg (by omega)]
  · intro a ha
    rw [State.setReg_arrs, State.setReg_arrs, ← hs7, State.writeArr_arrs_ne _ _ _ ha, ha6 a ha,
      ha5, ha2 a ha]
  · intro r h1 h2 h3 h4 h5 h6
    rw [State.setReg_regs_ne _ _ h2, State.setReg_regs_ne _ _ h1, hr7, hr6 r h6, hr5 r h5 h4 h3]

/-- Write the block of the next path of `F`: the separator and the vertices (copied from `aF`); if
the path is not empty, mark its two ends as nodes. -/
def segBody : Cmd :=
  .seq (.write aL (.reg rpos) (.reg rn)) <|
  .seq (.assign rcnt (.read aF (.reg rcur))) <|
  .seq (.ite (.op .lt (.const 0) (.reg rcnt))
    (.seq (.write aN (.read aF (.op .add (.reg rcur) (.const 1))) (.const 1))
      (.write aN (.read aF (.op .add (.reg rcur) (.reg rcnt))) (.const 1))) .skip) <|
  .seq (.assign rA (.op .add (.reg rcur) (.const 1))) <|
  .seq (.assign rB (.op .add (.reg rpos) (.const 1))) <|
  .seq (copyProg aF aL rA rB rcnt rt) <|
  .seq (.assign rpos (.op .add (.reg rB) (.reg rcnt)))
    (.assign rcur (.op .add (.reg rA) (.reg rcnt)))

/-- The node marks after the ends of a path of `F` are marked. -/
def markEnds (g : ℕ → ℕ) (cnt a b : ℕ) : ℕ → ℕ :=
  if 0 < cnt then Function.update (Function.update g a 1) b 1 else g

/-- **The body of the loop over the paths of `F`**, on plain lists. -/
theorem segBody_exec {w : ℕ} {s : State} {Fa Lay : List ℕ} {g : ℕ → ℕ} {M nv p0 c0 cnt : ℕ}
    (hrn : s.regs rn = nv) (hpos : s.regs rpos = p0) (hcur : s.regs rcur = c0)
    (hL : s.arrs aL = tab M (preTab Lay p0)) (hF : s.arrs aF = Fa)
    (hN : s.arrs aN = tab (nv + 1) g)
    (hcnt : Fa.getD c0 0 = cnt) (hcopy : ∀ t < cnt, Fa.getD (c0 + 1 + t) 0 = Lay.getD (p0 + 1 + t) 0)
    (hvert : ∀ t < cnt, Fa.getD (c0 + 1 + t) 0 < nv) (hsep : Lay.getD p0 0 = nv)
    (hfit : p0 + 1 + cnt ≤ M) (hcfit : c0 + 1 + cnt ≤ Fa.length)
    (hvF : ∀ v ∈ Fa, v < 2 ^ w) (hbig : M + Fa.length + nv + 4 < 2 ^ w) :
    ∃ s' t, Exec w segBody s s' t ∧ t ≤ 50 + 15 * cnt ∧
      s'.regs rpos = p0 + 1 + cnt ∧ s'.regs rcur = c0 + 1 + cnt ∧
      s'.arrs aL = tab M (preTab Lay (p0 + 1 + cnt)) ∧
      s'.arrs aN = tab (nv + 1) (markEnds g cnt (Fa.getD (c0 + 1) 0) (Fa.getD (c0 + cnt) 0)) ∧
      (∀ a, a ≠ aL → a ≠ aN → s'.arrs a = s.arrs a) ∧
      (∀ r, r ≠ rpos → r ≠ rcur → r ≠ rcnt → r ≠ rA → r ≠ rB → r ≠ rt → s'.regs r = s.regs r) := by
  have hw1 : 1 < 2 ^ w := by omega
  have gF : ∀ i < Fa.length, Fa.getD i 0 < 2 ^ w := fun i hi => by
    rw [List.getD_eq_getElem _ _ hi]; exact hvF _ (List.getElem_mem _)
  -- step 1: the separator
  have ex1 : Exec w (.write aL (.reg rpos) (.reg rn)) s (s.writeArr aL p0 nv) _ :=
    .write (ev_reg hpos (by omega)) (ev_reg hrn (by omega)) (by rw [hL]; simp; omega)
  have hL1 := writeArr_tab hL (show p0 < M by omega) nv
  generalize hs1 : s.writeArr aL p0 nv = s1 at ex1 hL1
  have hr1 : s1.regs = s.regs := by rw [← hs1]; rfl
  have ha1 : ∀ a, a ≠ aL → s1.arrs a = s.arrs a := fun a ha => by
    rw [← hs1, State.writeArr_arrs_ne _ _ _ ha]
  have hF1 : s1.arrs aF = Fa := by rw [ha1 aF (by decide), hF]
  -- step 2: the length
  have ex2 : Exec w (.assign rcnt (.read aF (.reg rcur))) s1 (s1.setReg rcnt cnt) _ :=
    .assign (ev_read (ev_reg (by rw [hr1, hcur]) (by omega)) (by rw [hF1]; omega)
      (by rw [hF1, hcnt]) (hcnt ▸ gF _ (by omega)))
  generalize hs2 : s1.setReg rcnt cnt = s2 at ex2
  have hr2 : ∀ r, r ≠ rcnt → s2.regs r = s.regs r := fun r hr => by
    rw [← hs2, State.setReg_regs_ne _ _ hr, hr1]
  have hc2 : s2.regs rcnt = cnt := by rw [← hs2]; simp
  have ha2 : ∀ a, s2.arrs a = s1.arrs a := fun a => by rw [← hs2]; rfl
  have hN2 : s2.arrs aN = tab (nv + 1) g := by rw [ha2, ha1 aN (by decide), hN]
  have hF2 : s2.arrs aF = Fa := by rw [ha2, hF1]
  -- step 3: mark the ends
  have ex3 : ∃ s3 t3, Exec w (.ite (.op .lt (.const 0) (.reg rcnt))
      (.seq (.write aN (.read aF (.op .add (.reg rcur) (.const 1))) (.const 1))
        (.write aN (.read aF (.op .add (.reg rcur) (.reg rcnt))) (.const 1))) .skip) s2 s3 t3 ∧
      t3 ≤ 16 ∧ s3.regs = s2.regs ∧
      s3.arrs aN = tab (nv + 1) (markEnds g cnt (Fa.getD (c0 + 1) 0) (Fa.getD (c0 + cnt) 0)) ∧
      (∀ a, a ≠ aN → s3.arrs a = s2.arrs a) := by
    have hcond : (Expr.op .lt (.const 0) (.reg rcnt)).eval w s2 = some (if 0 < cnt then 1 else 0) :=
      ev_lt (ev_const (by omega)) (ev_reg hc2 (by omega)) hw1
    by_cases hpos0 : 0 < cnt
    · rw [if_pos hpos0] at hcond
      have hv1 := hvert 0 hpos0
      have hv2 := hvert (cnt - 1) (by omega)
      rw [Nat.add_zero] at hv1
      rw [show c0 + 1 + (cnt - 1) = c0 + cnt by omega] at hv2
      have hcur2 : s2.regs rcur = c0 := by rw [hr2 rcur (by decide), hcur]
      have exa := Exec.write (w := w) (a := aN) (val := .const 1)
        (ev_read (ev_add (ev_reg hcur2 (by omega)) (ev_const (v := 1) (by omega)) (by omega))
          (by rw [hF2]; omega) (by rw [hF2]) (by omega)) (ev_const (by omega))
          (by rw [hN2, length_tab]; omega)
      have hNa := writeArr_tab hN2 (show Fa.getD (c0 + 1) 0 < nv + 1 by omega) 1
      generalize hsa : s2.writeArr aN (Fa.getD (c0 + 1) 0) 1 = sa at exa hNa
      have hra : sa.regs = s2.regs := by rw [← hsa]; rfl
      have haa : ∀ a, a ≠ aN → sa.arrs a = s2.arrs a := fun a ha => by
        rw [← hsa, State.writeArr_arrs_ne _ _ _ ha]
      have exb := Exec.write (w := w) (a := aN) (val := .const 1) (s := sa)
        (ev_read (ev_add (ev_reg (by rw [hra, hcur2]) (by omega)) (ev_reg (by rw [hra, hc2])
          (by omega)) (by omega)) (by rw [haa aF (by decide), hF2]; omega)
          (by rw [haa aF (by decide), hF2]) (by omega)) (ev_const (by omega))
          (by rw [hNa, length_tab]; omega)
      refine ⟨_, _, .ite_true hcond one_ne_zero (.seq exa exb), by simp [Expr.cost],
        by rw [State.writeArr_regs, hra], ?_, ?_⟩
      · rw [writeArr_tab hNa (show Fa.getD (c0 + cnt) 0 < nv + 1 by omega), markEnds,
          if_pos hpos0]
      · intro a ha
        rw [State.writeArr_arrs_ne _ _ _ ha, haa a ha]
    · rw [if_neg hpos0] at hcond
      refine ⟨_, _, .ite_false hcond (.skip _), by simp [Expr.cost], rfl, ?_, fun _ _ => rfl⟩
      rw [hN2, markEnds, if_neg hpos0]
  obtain ⟨s3, t3, ex3, ht3, hr3, hN3, ha3⟩ := ex3
  -- steps 4 and 5: registers
  have ex4 : Exec w (.assign rA (.op .add (.reg rcur) (.const 1))) s3 (s3.setReg rA (c0 + 1)) _ :=
    .assign (ev_add (ev_reg (by rw [hr3, hr2 rcur (by decide), hcur]) (by omega))
      (ev_const (by omega)) (by omega))
  have ex5 : Exec w (.assign rB (.op .add (.reg rpos) (.const 1))) (s3.setReg rA (c0 + 1))
      ((s3.setReg rA (c0 + 1)).setReg rB (p0 + 1)) _ :=
    .assign (ev_add (ev_reg (by rw [State.setReg_regs_ne _ _ (by decide), hr3,
      hr2 rpos (by decide), hpos]) (by omega)) (ev_const (by omega)) (by omega))
  generalize hs5 : (s3.setReg rA (c0 + 1)).setReg rB (p0 + 1) = s5 at ex5
  have ha5 : ∀ a, s5.arrs a = s3.arrs a := fun a => by rw [← hs5]; rfl
  have hr5 : ∀ r, r ≠ rB → r ≠ rA → s5.regs r = s3.regs r := fun r h1 h2 => by
    rw [← hs5, State.setReg_regs_ne _ _ h1, State.setReg_regs_ne _ _ h2]
  -- step 6: the vertices
  have hL5 : s5.arrs aL = tab M (Function.update (preTab Lay p0) p0 nv) := by
    rw [ha5, ha3 aL (by decide), ha2, hL1]
  obtain ⟨s6, t6, ex6, ht6, hL6, ha6, hr6⟩ := copyProg_exec aF aL rA rB rcnt rt (by decide)
    (by decide) (by decide) (by decide) (s := s5) (cur := c0 + 1) (pos := p0 + 1) (cnt := cnt)
    hw1 (by rw [ha5, ha3 aF (by decide), hF2]) hL5 (by simp [← hs5, State.setReg_regs_ne])
    (by simp [← hs5]) (by rw [hr5 rcnt (by decide) (by decide), hr3, hc2]) (by omega) (by omega)
    (by omega) hvF
  have hs6B : s6.regs rB = p0 + 1 := by rw [hr6 rB (by decide), ← hs5]; simp
  have hs6A : s6.regs rA = c0 + 1 := by rw [hr6 rA (by decide), ← hs5]; simp [State.setReg_regs_ne]
  have hs6c : s6.regs rcnt = cnt := by
    rw [hr6 rcnt (by decide), hr5 rcnt (by decide) (by decide), hr3, hc2]
  have ex7 : Exec w (.assign rpos (.op .add (.reg rB) (.reg rcnt))) s6
      (s6.setReg rpos (p0 + 1 + cnt)) _ :=
    .assign (ev_add (ev_reg hs6B (by omega)) (ev_reg hs6c (by omega)) (by omega))
  have ex8 : Exec w (.assign rcur (.op .add (.reg rA) (.reg rcnt))) (s6.setReg rpos (p0 + 1 + cnt))
      ((s6.setReg rpos (p0 + 1 + cnt)).setReg rcur (c0 + 1 + cnt)) _ :=
    .assign (ev_add (ev_reg (by rw [State.setReg_regs_ne _ _ (by decide), hs6A]) (by omega))
      (ev_reg (by rw [State.setReg_regs_ne _ _ (by decide), hs6c]) (by omega)) (by omega))
  refine ⟨_, _, .seq ex1 (.seq ex2 (.seq ex3 (.seq ex4 (.seq ex5 (.seq ex6 (.seq ex7 ex8)))))),
    ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [Expr.cost]; omega
  · rw [State.setReg_regs_ne _ _ (by decide), State.setReg_regs_self]
  · rw [State.setReg_regs_self]
  · rw [State.setReg_arrs, State.setReg_arrs, hL6]
    refine tab_congr fun j _ => ?_
    simp only [Function.update_apply, preTab]
    by_cases hj2 : p0 + 1 ≤ j ∧ j < p0 + 1 + cnt
    · rw [if_pos hj2, if_pos (by omega)]
      obtain ⟨t, rfl⟩ : ∃ t, j = p0 + 1 + t := ⟨j - (p0 + 1), by omega⟩
      rw [show c0 + 1 + (p0 + 1 + t - (p0 + 1)) = c0 + 1 + t by omega, hcopy t (by omega)]
    rw [if_neg hj2]
    by_cases hj4 : j = p0
    · subst hj4; rw [if_pos rfl, if_pos (by omega), hsep]
    rw [if_neg hj4]
    by_cases hj5 : j < p0
    · rw [if_pos hj5, if_pos (by omega)]
    · rw [if_neg hj5, if_neg (by omega)]
  · rw [State.setReg_arrs, State.setReg_arrs, ha6 aN (by decide), ha5, hN3]
  · intro a ha hb
    rw [State.setReg_arrs, State.setReg_arrs, ha6 a ha, ha5, ha3 a hb, ha2, ha1 a ha]
  · intro r h1 h2 h3 h4 h5 h6
    rw [State.setReg_regs_ne _ _ h2, State.setReg_regs_ne _ _ h1, hr6 r h6, hr5 r h5 h4, hr3,
      hr2 r h3]

end Alg92

end GraphMinor.Compute
