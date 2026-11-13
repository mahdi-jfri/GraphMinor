module

public import GraphMinor.Compute.Algorithm92BuildLoop

/-!
# Graph Minors XIII, (9.2): the program that writes the layout (`Algorithm92BuildRun.lean`)

The first program after `F` (page 101 of Graph Minors XIII) reads `x.G.enc`, `x.W.encList` and
`encSegs92 segs`. It writes the layout of the paths of `H ∪ F` into the array `aL` and marks the
nodes of `H ∪ F` in the array `aN`. The main result is `buildProg_exec`.
-/

@[expose] public section

namespace GraphMinor.Compute

namespace Alg92

open WallOfHeight

variable {l m p h k r : ℕ} {x : Alg92Input l m p h k r} {segs : List (List (Fin x.n))}

/-! ### Marking the branch vertices -/

/-- Mark the `ri`-th branch vertex as a node. -/
def bvBody : Cmd := .write aN (.read aW (.op .add (.const 3) (.reg ri))) (.const 1)

/-- The loop that marks the branch vertices as nodes. -/
def bvLoop (h : ℕ) : Cmd := forUp ri (.const (elemWallNumVerts h)) bvBody

variable (x) in
/-- The numbers marked as nodes after the first `i` branch vertices are marked. -/
def bvP (i v : ℕ) : Prop :=
  v = x.n ∨ ∃ u : Fin (elemWallNumVerts h), u.val < i ∧ (x.W.branchVert u).val = v

theorem bvP_succ {i : ℕ} (hi : i < elemWallNumVerts h) :
    Function.update (ind (bvP x i)) (x.W.branchVert ⟨i, hi⟩).val 1 = ind (bvP x (i + 1)) := by
  rw [update_ind]
  congr 1
  funext v
  apply propext
  simp only [bvP]
  constructor
  · rintro ((h1 | ⟨u, hu, hv⟩) | h2)
    · exact Or.inl h1
    · exact Or.inr ⟨u, by omega, hv⟩
    · exact Or.inr ⟨⟨i, hi⟩, by simp, h2.symm⟩
  · rintro (h1 | ⟨u, hu, hv⟩)
    · exact Or.inl (Or.inl h1)
    · by_cases hui : u.val = i
      · right; rw [← hv]; congr 2; exact Fin.ext hui
      · exact Or.inl (Or.inr ⟨u, by omega, hv⟩)

theorem bvP_all : bvP x (elemWallNumVerts h) = ndJ x segs 0 := by
  funext v
  apply propext
  simp only [bvP, ndJ]
  constructor
  · rintro (h1 | ⟨u, -, hv⟩)
    · exact Or.inl h1
    · exact Or.inr (Or.inl ⟨u, hv⟩)
  · rintro (h1 | ⟨u, hv⟩ | ⟨j', hj', -⟩)
    · exact Or.inl h1
    · exact Or.inr ⟨u, u.2, hv⟩
    · omega

variable (x) in
/-- The invariant of the loop that marks the branch vertices. -/
def bvInv (s0 : State) (i : ℕ) (s : State) : Prop :=
  s.regs ri = i ∧ s.arrs aN = tab (x.n + 1) (ind (bvP x i)) ∧
    (∀ a, a ≠ aN → s.arrs a = s0.arrs a) ∧ (∀ q, q ≠ ri → s.regs q = s0.regs q)

theorem bvLoop_exec {w : ℕ} {s0 : State} (hW0 : s0.arrs aW = x.W.encList)
    (hB : bigB x segs < 2 ^ w) (hI : bvInv x s0 0 s0) :
    ∃ s' t, Exec w (bvLoop h) s0 s' t ∧ t ≤ 3 + elemWallNumVerts h * 13 ∧
      bvInv x s0 (elemWallNumVerts h) s' := by
  have hV := le_length_encList (x := x)
  have hB' := hB; unfold bigB at hB'
  have := Triple.forUp_const (w := w) (bvInv x s0) (elemWallNumVerts h) 6 (r_i := ri)
    (hi := .const (elemWallNumVerts h)) (body := bvBody) (by omega) (by omega)
    (fun i _ s hs => ⟨hs.1, ev_const (by omega)⟩) (fun i hi => by
      rintro s ⟨hri, hN, ha, hr⟩
      have hWs : s.arrs aW = x.W.encList := by rw [ha aW (by decide), hW0]
      have hbv := getD_encList_bv (x := x) i hi
      have hlt := (x.W.branchVert ⟨i, hi⟩).2
      have ex := Exec.write (w := w) (a := aN) (s := s)
        (idx := .read aW (.op .add (.const 3) (.reg ri))) (val := .const 1)
        (ev_read (ev_add (ev_const (by omega)) (ev_reg hri (by omega)) (by omega))
          (by rw [hWs]; omega) (by rw [hWs, hbv]) (by omega))
        (ev_const (by omega)) (by rw [hN, length_tab]; omega)
      refine ⟨_, _, ex, by simp [Expr.cost], ⟨by simp, ?_, ?_, ?_⟩, by simp [hri]⟩
      · rw [State.setReg_arrs, writeArr_tab hN (by omega), bvP_succ hi]
      · intro a ha'
        rw [State.setReg_arrs, State.writeArr_arrs_ne _ _ _ ha', ha a ha']
      · intro q hq
        rw [State.setReg_regs_ne _ _ hq, State.writeArr_regs, hr q hq]) s0 hI
  obtain ⟨s', t, ex, ht, hs'⟩ := this
  exact ⟨s', t, ex, by simp only [Expr.cost] at ht; omega, hs'⟩

/-! ### The whole program -/

/-- The length of the layout, computed from the lengths of `aW` and `aF` (`length_layout`). -/
def layLenExpr (h : ℕ) : Expr :=
  .op .sub (.op .add (.op .add (.len aW) (.len aF)) (.const (2 * (elemWallEdges h).length)))
    (.const (4 + elemWallNumVerts h))

/-- **The program that writes the layout of `H ∪ F`** into `aL` and marks the nodes in `aN`. -/
def buildProg (h : ℕ) : Cmd :=
  .seq (.assign rn (.read aG (.const 0))) <|
  .seq (constProg aEdge (edgeTab h)) <|
  .seq (.alloc aN (.op .add (.reg rn) (.const 1))) <|
  .seq (.write aN (.reg rn) (.const 1)) <|
  .seq (.assign ri (.const 0)) <|
  .seq (bvLoop h) <|
  .seq (.alloc aL (layLenExpr h)) <|
  .seq (.assign rpos (.const 0)) <|
  .seq (.assign rcur (.const (3 + elemWallNumVerts h))) <|
  .seq (.assign ri (.const 0)) <|
  .seq (wallLoop h) <|
  .seq (.assign rcur (.const 1)) <|
  .seq (.assign ri (.const 0)) segLoop

variable (x segs) in
/-- The time bound of `buildProg`. -/
def buildTime : ℕ :=
  60 + 8 * (elemWallEdges h).length + 13 * elemWallNumVerts h + x.n + (layout x segs).length +
    (elemWallEdges h).length * (60 + 15 * x.n) + segs.length * (61 + 15 * x.n)

theorem lpos_all : lpos x segs ((elemWallEdges h).length + segs.length) = (layout x segs).length := by
  unfold lpos
  rw [List.take_of_length_le (by simp), layout_eq]

theorem tab_preTab_length (L : List ℕ) : tab L.length (preTab L L.length) = L := by
  rw [tab_eq_iff]
  exact ⟨rfl, fun j hj => by simp [preTab, hj]⟩

theorem buildProg_exec {w : ℕ} {s : State} (hG : s.arrs aG = x.G.enc)
    (hW : s.arrs aW = x.W.encList) (hF : s.arrs aF = encSegs92 segs)
    (hnd : ∀ P ∈ segs, P.length ≤ x.n) (hB : bigB x segs < 2 ^ w) :
    ∃ s' t, Exec w (buildProg h) s s' t ∧ t ≤ buildTime x segs ∧
      s'.regs rn = x.n ∧ s'.arrs aL = layout x segs ∧
      s'.arrs aN = tab (x.n + 1) (fun v => if ndB x segs v then 1 else 0) ∧
      s'.arrs aEdge = edgeTab h ∧
      (∀ a, a ≠ aL → a ≠ aN → a ≠ aEdge → s'.arrs a = s.arrs a) := by
  have hB' := hB; unfold bigB at hB'
  have hV := le_length_encList (x := x)
  have hlay := length_layout (x := x) (segs := segs)
  -- step 1: the number of vertices
  have ex1 : Exec w (.assign rn (.read aG (.const 0))) s (s.setReg rn x.n) _ :=
    .assign (ev_read (ev_const (by omega)) (by rw [hG]; simp) (by rw [hG]; rfl) (by omega))
  generalize hs1 : s.setReg rn x.n = s1 at ex1
  have hr1 : s1.regs rn = x.n := by rw [← hs1]; simp
  have ha1 : ∀ a, s1.arrs a = s.arrs a := fun a => by rw [← hs1]; rfl
  -- step 2: the edge table
  obtain ⟨s2, t2, ex2, ht2, hE2, ha2, hr2⟩ := constProg_exec (w := w) aEdge (edgeTab h) s1
    (by rw [length_edgeTab]; omega) (fun v hv => by have := lt_of_mem_edgeTab hv; omega)
  rw [length_edgeTab] at ht2
  -- steps 3 and 4: the node array, with the separator marked
  have ex3 : Exec w (.alloc aN (.op .add (.reg rn) (.const 1))) s2
      (s2.setArr aN (List.replicate (x.n + 1) 0)) _ :=
    .alloc (ev_add (ev_reg (by rw [hr2, hr1]) (by omega)) (ev_const (by omega)) (by omega))
  have hN3 : (s2.setArr aN (List.replicate (x.n + 1) 0)).arrs aN = tab (x.n + 1) (ind (fun _ => False)) := by
    rw [State.setArr_arrs_self, replicate_eq_tab]
    exact tab_congr fun j _ => by simp [ind]
  have ex4 : Exec w (.write aN (.reg rn) (.const 1)) (s2.setArr aN (List.replicate (x.n + 1) 0))
      ((s2.setArr aN (List.replicate (x.n + 1) 0)).writeArr aN x.n 1) _ :=
    .write (ev_reg (by rw [State.setArr_regs, hr2, hr1]) (by omega)) (ev_const (by omega))
      (by simp)
  have hN4 := writeArr_tab hN3 (show x.n < x.n + 1 by omega) 1
  rw [update_ind] at hN4
  generalize hs4 : (s2.setArr aN (List.replicate (x.n + 1) 0)).writeArr aN x.n 1 = s4 at ex4 hN4
  have hr4 : s4.regs = s2.regs := by rw [← hs4]; rfl
  have ha4 : ∀ a, a ≠ aN → s4.arrs a = s2.arrs a := fun a ha => by
    rw [← hs4, State.writeArr_arrs_ne _ _ _ ha, State.setArr_arrs_ne _ _ ha]
  -- step 5: the loop over the branch vertices
  have ex5 : Exec w (.assign ri (.const 0)) s4 (s4.setReg ri 0) _ := .assign (ev_const (by omega))
  have hW5 : (s4.setReg ri 0).arrs aW = x.W.encList := by
    rw [State.setReg_arrs, ha4 aW (by decide), ha2 aW (by decide), ha1, hW]
  obtain ⟨s6, t6, ex6, ht6, hri6, hN6, ha6, hr6⟩ := bvLoop_exec (segs := segs) (h := h)
    (s0 := s4.setReg ri 0) hW5 hB ⟨by simp, by
      rw [State.setReg_arrs, hN4]
      congr 2; funext v; apply propext; simp [bvP], fun _ _ => rfl, fun _ _ => rfl⟩
  rw [bvP_all (segs := segs)] at hN6
  have hr6' : s6.regs rn = x.n := by
    rw [hr6 rn (by decide), State.setReg_regs_ne _ _ (by decide), hr4, hr2, hr1]
  have ha6' : ∀ a, a ≠ aN → a ≠ aEdge → s6.arrs a = s.arrs a := fun a h1 h2 => by
    rw [ha6 a h1, State.setReg_arrs, ha4 a h1, ha2 a h2, ha1]
  have hE6 : s6.arrs aEdge = edgeTab h := by
    rw [ha6 aEdge (by decide), State.setReg_arrs, ha4 aEdge (by decide), hE2]
  -- step 6: the layout array
  have hM : (layLenExpr h).eval w s6 = some (layout x segs).length := by
    have e := ev_sub (ev_add (ev_add (ev_len (a := aW) (s := s6) (w := w)
      (by rw [ha6' aW (by decide) (by decide), hW]) (by omega))
      (ev_len (a := aF) (by rw [ha6' aF (by decide) (by decide), hF]) (by omega)) (by omega))
      (ev_const (v := 2 * (elemWallEdges h).length) (by omega)) (by omega))
      (ev_const (v := 4 + elemWallNumVerts h) (by omega))
    rw [layLenExpr, e, show x.W.encList.length + (encSegs92 segs).length +
      2 * (elemWallEdges h).length - (4 + elemWallNumVerts h) = (layout x segs).length by omega]
  have ex7 : Exec w (.alloc aL (layLenExpr h)) s6
      (s6.setArr aL (List.replicate (layout x segs).length 0)) _ := .alloc hM
  generalize hs7 : s6.setArr aL (List.replicate (layout x segs).length 0) = s7 at ex7
  have hL7 : s7.arrs aL = tab (layout x segs).length (preTab (layout x segs) 0) := by
    rw [← hs7, State.setArr_arrs_self, replicate_eq_tab]
    exact tab_congr fun j _ => by simp [preTab]
  have ha7 : ∀ a, a ≠ aL → s7.arrs a = s6.arrs a := fun a ha => by
    rw [← hs7, State.setArr_arrs_ne _ _ ha]
  have hr7 : s7.regs = s6.regs := by rw [← hs7]; rfl
  -- step 7: the loop over the paths of the wall
  have ex8 : Exec w (.assign rpos (.const 0)) s7 (s7.setReg rpos 0) _ := .assign (ev_const (by omega))
  have ex9 : Exec w (.assign rcur (.const (3 + elemWallNumVerts h))) (s7.setReg rpos 0)
      ((s7.setReg rpos 0).setReg rcur (3 + elemWallNumVerts h)) _ := .assign (ev_const (by omega))
  have ex10 : Exec w (.assign ri (.const 0)) ((s7.setReg rpos 0).setReg rcur (3 + elemWallNumVerts h))
      (((s7.setReg rpos 0).setReg rcur (3 + elemWallNumVerts h)).setReg ri 0) _ :=
    .assign (ev_const (by omega))
  generalize hs10 : ((s7.setReg rpos 0).setReg rcur (3 + elemWallNumVerts h)).setReg ri 0 = s10
    at ex10
  have ha10 : ∀ a, s10.arrs a = s7.arrs a := fun a => by rw [← hs10]; rfl
  obtain ⟨s11, t11, ex11, ht11, hrn11, hpos11, hcur11, hri11, hL11, ha11, hr11⟩ :=
    wallLoop_exec (x := x) (segs := segs) (w := w) (s0 := s10)
      (by rw [ha10, ha7 aW (by decide), ha6' aW (by decide) (by decide), hW])
      (by rw [ha10, ha7 aEdge (by decide), hE6]) hB
      ⟨by rw [← hs10]; simp [hr7, hr6'], by rw [← hs10]; simp [lpos],
        by rw [← hs10]; simp [wcur], by rw [← hs10]; simp,
        by rw [ha10, hL7]; simp [lpos], fun _ _ => rfl, fun _ _ _ _ _ _ _ _ => rfl⟩
  -- step 8: the loop over the paths of `F`
  have ex12 : Exec w (.assign rcur (.const 1)) s11 (s11.setReg rcur 1) _ := .assign (ev_const (by omega))
  have ex13 : Exec w (.assign ri (.const 0)) (s11.setReg rcur 1) ((s11.setReg rcur 1).setReg ri 0) _ :=
    .assign (ev_const (by omega))
  generalize hs13 : (s11.setReg rcur 1).setReg ri 0 = s13 at ex13
  have ha13 : ∀ a, s13.arrs a = s11.arrs a := fun a => by rw [← hs13]; rfl
  have hN11 : s11.arrs aN = tab (x.n + 1) (ind (ndJ x segs 0)) := by
    rw [ha11 aN (by decide), ha10, ha7 aN (by decide), hN6]
  obtain ⟨s14, t14, ex14, ht14, hrn14, -, -, -, hL14, hN14, ha14, -⟩ :=
    segLoop_exec (x := x) (segs := segs) (w := w) (s0 := s13)
      (by rw [ha13, ha11 aF (by decide), ha10, ha7 aF (by decide),
        ha6' aF (by decide) (by decide), hF]) hnd hB
      ⟨by rw [← hs13]; simp [hrn11], by rw [← hs13]; simp [hpos11],
        by rw [← hs13]; simp [scur], by rw [← hs13]; simp,
        by rw [ha13, hL11]; simp, by rw [ha13, hN11], fun _ _ _ => rfl,
        fun _ _ _ _ _ _ _ _ => rfl⟩
  refine ⟨s14, _, .seq ex1 (.seq ex2 (.seq ex3 (.seq ex4 (.seq ex5 (.seq ex6 (.seq ex7 (.seq ex8
    (.seq ex9 (.seq ex10 (.seq ex11 (.seq ex12 (.seq ex13 ex14)))))))))))), ?_, hrn14, ?_, ?_, ?_,
    ?_⟩
  · simp only [Expr.cost, layLenExpr, buildTime] at ht2 ht6 ht11 ht14 ⊢
    omega
  · rw [hL14, lpos_all, tab_preTab_length]
  · rw [hN14]
    exact tab_congr fun v hv => ind_ndJ_length hv
  · rw [ha14 aEdge (by decide) (by decide), ha13, ha11 aEdge (by decide), ha10,
      ha7 aEdge (by decide), hE6]
  · intro a h1 h2 h3
    rw [ha14 a h1 h2, ha13, ha11 a h1, ha10, ha7 a h1, ha6' a h2 h3]

end Alg92

end GraphMinor.Compute
