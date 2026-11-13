module

public import GraphMinor.Compute.Algorithm99MoveRun
public import GraphMinor.Compute.Algorithm99MoveA

/-!
# Renaming a Case (iii) block in place

Output (a) of steps (5) to (7) of Algorithm (9.9) (Graph Minors XIII, page 104) is a block
`encCase3Block W K_vList K_eList corners members` in the labels of the renumbered graph `G'`.
The program of this file walks through the block in the order in which `parseCase3Block`
reads it, and replaces each vertex word `x` by `o[x]`, where array `o` stores `orig`. Lengths,
copy numbers of edges and the trees of the member records are kept.

* `mvPrefRun`: a length `k` followed by `k` vertex words (`mvPrefRun_exec`);
* `mvPrefRunLoop`: `m` such runs in a row (`mvPrefRunLoop_exec`);
* `mvWall`: the code `W.encList` of a wall (`mvWall_exec`);
* `mvRecord`, `mvRecordLoop`: the member records (`mvRecord_exec`, `mvRecordLoop_exec`);
* `mvBlock`: the whole block (`mvBlock_exec`).

Each program keeps the position of the next unread word in register `r` and works for any
words before and after the part it renames.
-/

@[expose] public section

namespace GraphMinor.Compute

/-- `omega` after unfolding `Reg` and `Arr`, which `omega` does not see as `ℕ`. -/
local macro "romega" : tactic => `(tactic| ((try dsimp only [Reg, Arr, inArr, outArr] at *); omega))

/-! ### Two assignments -/

/-- Reading the word at the position held in register `q`. -/
theorem mv_exec_assign_read {w : ℕ} {s : State} {a : Arr} {r q : Reg} {pos v : ℕ}
    (hq : s.regs q = pos) (hpos_w : pos < 2 ^ w) (hlt : pos < (s.arrs a).length)
    (hv : (s.arrs a)[pos] = v) (hv_w : v < 2 ^ w) :
    Exec w (.assign r (.read a (.reg q))) s (s.setReg r v) 3 :=
  .assign (mv_eval_read (by simp [Expr.eval, checkWord, hq, hpos_w]) hlt hv hv_w)

/-- Reading the word at a computed position. -/
theorem mv_exec_assign_read' {w : ℕ} {s : State} {a : Arr} {r : Reg} {idx : Expr} {pos v : ℕ}
    (hidx : idx.eval w s = some pos) (hlt : pos < (s.arrs a).length)
    (hv : (s.arrs a)[pos] = v) (hv_w : v < 2 ^ w) :
    Exec w (.assign r (.read a idx)) s (s.setReg r v) (idx.cost + 2) :=
  .assign (mv_eval_read hidx hlt hv hv_w)

/-- Evaluation of a register plus a constant. -/
theorem mv_eval_add_const {w : ℕ} {s : State} {q : Reg} {x c : ℕ} (hq : s.regs q = x)
    (h : x + c < 2 ^ w) : (Expr.op .add (.reg q) (.const c)).eval w s = some (x + c) := by
  simp [Expr.eval, checkWord, BinOp.eval, BinOp.raw, hq, h,
    show x < 2 ^ w by omega, show c < 2 ^ w by omega]

/-- Adding a constant to a register. -/
theorem mv_exec_assign_add {w : ℕ} {s : State} {r q : Reg} {x c : ℕ} (hq : s.regs q = x)
    (h : x + c < 2 ^ w) :
    Exec w (.assign r (.op .add (.reg q) (.const c))) s (s.setReg r (x + c)) 4 :=
  .assign (by simp [Expr.eval, checkWord, BinOp.eval, BinOp.raw, hq, h,
    show x < 2 ^ w by omega, show c < 2 ^ w by omega])

/-- Adding a register to a register. -/
theorem mv_exec_assign_add_reg {w : ℕ} {s : State} {r q q' : Reg} {x y : ℕ} (hq : s.regs q = x)
    (hq' : s.regs q' = y) (h : x + y < 2 ^ w) :
    Exec w (.assign r (.op .add (.reg q) (.reg q'))) s (s.setReg r (x + y)) 4 :=
  .assign (by simp [Expr.eval, checkWord, BinOp.eval, BinOp.raw, hq, hq', h,
    show x < 2 ^ w by omega, show y < 2 ^ w by omega])

/-! ### A length followed by a run of vertex words -/

/-- Read the length `k` at position `P`, step over it, and rename the next `k` words. -/
def mvPrefRun (a o : Arr) (r : Reg) : Cmd :=
  .seq (.assign (r + 1) (.read a (.reg r)))
    (.seq (.assign r (.op .add (.reg r) (.const 1))) (mvRun a o r))

/-- **A length and a run.** `mvPrefRun` turns `D ++ (|seg| :: seg) ++ T` into
`D ++ (|seg| :: seg.map (o[·])) ++ T` and moves register `r` past it. -/
theorem mvPrefRun_exec {w : ℕ} {a o : Arr} (hao : a ≠ o) (r : Reg) {s : State}
    {D seg T : List ℕ} (ha : s.arrs a = D ++ (seg.length :: seg) ++ T)
    (hr : s.regs r = D.length) (hseg : ∀ x ∈ seg, x < (s.arrs o).length)
    (hseg_w : ∀ x ∈ seg, x < 2 ^ w) (ho_w : ∀ y ∈ s.arrs o, y < 2 ^ w)
    (hw1 : 1 < 2 ^ w) (hlen_w : (D ++ (seg.length :: seg) ++ T).length < 2 ^ w) :
    ∃ s' t, Exec w (mvPrefRun a o r) s s' t ∧ t ≤ 16 * seg.length + 12 ∧
      s'.arrs a = D ++ (seg.length :: seg.map (fun x => (s.arrs o).getD x 0)) ++ T ∧
      s'.regs r = D.length + 1 + seg.length ∧
      (∀ b, b ≠ a → s'.arrs b = s.arrs b) ∧
      (∀ q, q ≠ r → q ≠ r + 1 → q ≠ r + 2 → s'.regs q = s.regs q) := by
  have hlen : (s.arrs a).length = (D ++ (seg.length :: seg) ++ T).length := by rw [ha]
  have hL : (D ++ (seg.length :: seg) ++ T).length = D.length + 1 + seg.length + T.length := by
    simp
    omega
  have hex₁ := mv_exec_assign_read (w := w) (a := a) (r := r + 1) (v := seg.length) hr (by omega) (by omega)
    (by rw [show (s.arrs a)[D.length] = (D ++ seg.length :: (seg ++ T))[D.length] by
          simp only [ha, List.append_assoc, List.cons_append]]
        simp)
    (by omega)
  set s₁ := s.setReg (r + 1) seg.length
  have hex₂ := mv_exec_assign_add (w := w) (r := r) (c := 1) (s := s₁)
    (show s₁.regs r = D.length by rw [State.setReg_regs_ne _ _ (by romega)]; exact hr)
    (by omega)
  set s₂ := s₁.setReg r (D.length + 1)
  have ha₂ : s₂.arrs a = (D ++ [seg.length]) ++ seg ++ T := by
    change s.arrs a = _
    rw [ha]
    simp
  obtain ⟨s₃, t₃, hex₃, ht₃, hA₃, hP₃, hB₃, hR₃⟩ :=
    mvRun_exec hao r (s := s₂) ha₂ (by simp [s₂])
      (by rw [State.setReg_regs_ne _ _ (by romega)]; simp [s₁])
      (fun x hx => hseg x hx) hseg_w ho_w hw1 (by simpa using hlen_w)
  refine ⟨s₃, 3 + (4 + t₃), Exec.seq hex₁ (Exec.seq hex₂ hex₃), by omega, ?_, ?_, hB₃, ?_⟩
  · rw [hA₃]
    simp [s₂, s₁]
  · rw [hP₃]
    simp
  · intro q h0 h1 h2
    rw [hR₃ q h0 h2, State.setReg_regs_ne _ _ h0, State.setReg_regs_ne _ _ h1]

/-! ### Several runs in a row -/

/-- `m` length-prefixed runs in a row (`m` in register `r + 5`, loop index `r + 6`). -/
def mvPrefRunLoop (a o : Arr) (r : Reg) : Cmd :=
  .seq (.assign (r + 6) (.const 0)) (forUp (r + 6) (.reg (r + 5)) (mvPrefRun a o r))

/-- The code of a list of runs: each run is its length followed by its words. -/
def mvRunsCode (Ls : List (List ℕ)) : List ℕ := Ls.flatMap (fun l => l.length :: l)

theorem mvRunsCode_append (L₁ L₂ : List (List ℕ)) :
    mvRunsCode (L₁ ++ L₂) = mvRunsCode L₁ ++ mvRunsCode L₂ := by
  simp [mvRunsCode]

theorem length_mvRunsCode_map (φ : ℕ → ℕ) (Ls : List (List ℕ)) :
    (mvRunsCode (Ls.map (List.map φ))).length = (mvRunsCode Ls).length := by
  induction Ls with
  | nil => rfl
  | cons l Ls ih =>
    simp only [mvRunsCode, List.map_cons, List.flatMap_cons, List.length_append,
      List.length_cons, List.length_map] at ih ⊢
    omega

theorem length_le_length_mvRunsCode (Ls : List (List ℕ)) :
    Ls.length ≤ (mvRunsCode Ls).length := by
  induction Ls with
  | nil => simp [mvRunsCode]
  | cons l Ls ih =>
    simp only [mvRunsCode, List.flatMap_cons, List.length_append, List.length_cons] at ih ⊢
    omega

/-- **Several runs.** `mvPrefRunLoop` turns `D ++ mvRunsCode Ls ++ T` into
`D ++ mvRunsCode (Ls.map (List.map (o[·]))) ++ T`. -/
theorem mvPrefRunLoop_exec {w : ℕ} {a o : Arr} (hao : a ≠ o) (r : Reg) {s : State}
    {D T : List ℕ} {Ls : List (List ℕ)} (ha : s.arrs a = D ++ mvRunsCode Ls ++ T)
    (hr : s.regs r = D.length) (hm : s.regs (r + 5) = Ls.length)
    (hLs : ∀ l ∈ Ls, ∀ x ∈ l, x < (s.arrs o).length ∧ x < 2 ^ w)
    (ho_w : ∀ y ∈ s.arrs o, y < 2 ^ w)
    (hw1 : 1 < 2 ^ w) (hlen_w : (D ++ mvRunsCode Ls ++ T).length < 2 ^ w) :
    ∃ s' t, Exec w (mvPrefRunLoop a o r) s s' t ∧
      t ≤ 16 * (mvRunsCode Ls).length + 19 * Ls.length + 5 ∧
      s'.arrs a = D ++ mvRunsCode (Ls.map (List.map (fun x => (s.arrs o).getD x 0))) ++ T ∧
      s'.regs r = D.length + (mvRunsCode Ls).length ∧
      (∀ b, b ≠ a → s'.arrs b = s.arrs b) ∧
      (∀ q, q ≠ r → q ≠ r + 1 → q ≠ r + 2 → q ≠ r + 6 → s'.regs q = s.regs q) := by
  set φ : ℕ → ℕ := fun x => (s.arrs o).getD x 0 with hφ
  have hlenLs := length_le_length_mvRunsCode Ls
  have hN_w : Ls.length < 2 ^ w := by
    simp only [List.length_append] at hlen_w
    omega
  let I (i : ℕ) (st : State) : Prop :=
    st.arrs a = D ++ mvRunsCode ((Ls.take i).map (List.map φ)) ++ mvRunsCode (Ls.drop i) ++ T ∧
      st.regs r = D.length + (mvRunsCode (Ls.take i)).length ∧
      st.regs (r + 6) = i ∧ st.regs (r + 5) = Ls.length ∧
      (∀ b, b ≠ a → st.arrs b = s.arrs b) ∧
      (∀ q, q ≠ r → q ≠ r + 1 → q ≠ r + 2 → q ≠ r + 6 → st.regs q = s.regs q)
  have hstep : ∀ i < Ls.length, ⦃I i⦄[w] mvPrefRun a o r
      ⦃fun s' => I (i + 1) (s'.setReg (r + 6) (i + 1)) ∧ s'.regs (r + 6) = i⦄ ≤
        fun _ => 16 * (Ls[i]?.getD []).length + 12 := by
    intro i hi st ⟨hA, hP, hI6, hK, hB, hR⟩
    set l := Ls[i] with hl
    have hsplit : Ls.drop i = l :: Ls.drop (i + 1) := List.drop_eq_getElem_cons hi
    have htake : Ls.take (i + 1) = Ls.take i ++ [l] := by
      rw [List.take_add_one, List.getElem?_eq_getElem hi]
      rfl
    set L₁ := D ++ mvRunsCode ((Ls.take i).map (List.map φ)) with hL₁
    have hL₁len : L₁.length = D.length + (mvRunsCode (Ls.take i)).length := by
      simp only [hL₁, List.length_append, length_mvRunsCode_map]
    have hA' : st.arrs a = L₁ ++ (l.length :: l) ++ (mvRunsCode (Ls.drop (i + 1)) ++ T) := by
      rw [hA, hsplit]
      simp [mvRunsCode]
    have hlen : (L₁ ++ (l.length :: l) ++ (mvRunsCode (Ls.drop (i + 1)) ++ T)).length =
        (D ++ mvRunsCode Ls ++ T).length := by
      rw [← hA', hA]
      conv_rhs => rw [← List.take_append_drop i Ls]
      simp only [List.length_append, mvRunsCode_append, hL₁len]
      omega
    have hlmem : l ∈ Ls := List.getElem_mem hi
    have ho : st.arrs o = s.arrs o := hB o hao.symm
    obtain ⟨st', t', hex, ht', hA'', hP', hB', hR'⟩ :=
      mvPrefRun_exec hao r (s := st) hA' (by rw [hP, hL₁len])
        (fun x hx => ho ▸ (hLs l hlmem x hx).1) (fun x hx => (hLs l hlmem x hx).2)
        (by rw [ho]; exact ho_w) hw1 (hlen ▸ hlen_w)
    refine ⟨st', t', hex, ?_, ⟨?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
    · simp only [List.getElem?_eq_getElem hi, Option.getD_some]
      exact ht'
    · change st'.arrs a = _
      rw [hA'', ho, htake]
      simp [hL₁, mvRunsCode, hφ]
    · rw [State.setReg_regs_ne _ _ (by romega), hP', htake, hL₁len]
      simp [mvRunsCode]
      omega
    · simp
    · rw [State.setReg_regs_ne _ _ (by romega), hR' _ (by romega) (by romega) (by romega)]
      exact hK
    · intro b hb
      change st'.arrs b = _
      rw [hB' b hb]
      exact hB b hb
    · intro q h0 h1 h2 h6
      rw [State.setReg_regs_ne _ _ h6, hR' q h0 h1 h2]
      exact hR q h0 h1 h2 h6
    · rw [hR' _ (by romega) (by romega) (by romega)]
      exact hI6
  have hloop := Triple.forUp_sum I Ls.length (fun i => 16 * (Ls[i]?.getD []).length + 12)
    (r_i := r + 6) (hi := .reg (r + 5)) (body := mvPrefRun a o r) hw1
    hN_w (fun i _ st hI => ⟨hI.2.2.1, by simp [Expr.eval, checkWord, hI.2.2.2.1, hN_w]⟩) hstep
  have hex₀ : Exec w (.assign (r + 6) (.const 0)) s (s.setReg (r + 6) 0) 2 :=
    .assign (by simp [Expr.eval, checkWord])
  have hI₀ : I 0 (s.setReg (r + 6) 0) := by
    refine ⟨by rw [State.setReg_arrs, ha]; simp [mvRunsCode], ?_, by simp, ?_,
      fun _ _ => rfl, fun q _ _ _ hq => State.setReg_regs_ne _ _ hq⟩
    · rw [State.setReg_regs_ne _ _ (by romega)]; simpa [mvRunsCode] using hr
    · rw [State.setReg_regs_ne _ _ (by romega)]; exact hm
  obtain ⟨s', t, hex, ht, hA, hP, -, -, hB, hR⟩ := hloop _ hI₀
  have hsum : ∑ j ∈ Finset.range Ls.length, (Ls[j]?.getD []).length =
      (mvRunsCode Ls).length - Ls.length := by
    have : ∀ L : List (List ℕ), ∑ j ∈ Finset.range L.length, (L[j]?.getD []).length +
        L.length = (mvRunsCode L).length := by
      intro L
      induction L with
      | nil => simp [mvRunsCode]
      | cons l L ih =>
        rw [List.length_cons, Finset.sum_range_succ']
        simp only [List.getElem?_cons_succ, List.getElem?_cons_zero, Option.getD_some,
          mvRunsCode, List.flatMap_cons, List.length_append, List.length_cons] at ih ⊢
        omega
    have := this Ls
    omega
  refine ⟨s', 2 + t, Exec.seq hex₀ hex, ?_, ?_, ?_, hB, ?_⟩
  · simp only [Expr.cost, Finset.sum_add_distrib, Finset.sum_const, Finset.card_range,
      smul_eq_mul, ← Finset.mul_sum, hsum] at ht
    have : 16 * ((mvRunsCode Ls).length - Ls.length) + 16 * Ls.length =
        16 * (mvRunsCode Ls).length := by
      rw [← Nat.mul_add, Nat.sub_add_cancel hlenLs]
    omega
  · rw [hA]
    simp [mvRunsCode]
  · rw [hP]
    simp
  · intro q h0 h1 h2 h6
    rw [hR q h0 h1 h2 h6]

/-! ### The code of a wall -/

namespace WallOfHeight

variable {h v : ℕ} {A : MultiDigraph v}

/-- The words of the branch vertices in `W.encList`. -/
def branchWords (W : WallOfHeight h A) : List ℕ :=
  (List.finRange (elemWallNumVerts h)).map (fun u => (W.branchVert u).1)

/-- The internal vertices of the subdivision paths, one run for each edge of the elementary
wall. -/
def internalRuns (W : WallOfHeight h A) : List (List ℕ) :=
  (List.finRange (elemWallEdges h).length).map (fun k => (W.internalVerts k).map Fin.val)

theorem encList_eq_runs (W : WallOfHeight h A) :
    W.encList = [h, elemWallNumVerts h, (elemWallEdges h).length] ++ W.branchWords ++
      mvRunsCode W.internalRuns := by
  simp [encList, branchWords, internalRuns, mvRunsCode, List.flatMap_map]

/-- The code of `W` with the words of its vertices renamed by `φ`. -/
def renamedEncList (φ : ℕ → ℕ) (W : WallOfHeight h A) : List ℕ :=
  [h, elemWallNumVerts h, (elemWallEdges h).length] ++ W.branchWords.map φ ++
    mvRunsCode (W.internalRuns.map (List.map φ))

/-- If `φ` renames each vertex word as `orig` does, the renamed code is the code of the moved
wall. -/
theorem renamedEncList_eq_encList_moveOrig {n : ℕ} {B : MultiDigraph n} (orig : Fin v → Fin n)
    (φ : ℕ → ℕ) (hφ : ∀ u : Fin v, φ u.1 = (orig u).1) (W : WallOfHeight h A) :
    W.renamedEncList φ = (W.moveOrig B orig).encList := by
  simp [renamedEncList, encList, branchWords, internalRuns, mvRunsCode, moveOrig,
    List.flatMap_map, hφ, Function.comp_def]

theorem mem_branchWords_lt (W : WallOfHeight h A) {x : ℕ} (hx : x ∈ W.branchWords) : x < v := by
  obtain ⟨u, -, rfl⟩ := List.mem_map.mp hx
  exact (W.branchVert u).2

theorem mem_internalRuns_lt (W : WallOfHeight h A) {l : List ℕ} (hl : l ∈ W.internalRuns)
    {x : ℕ} (hx : x ∈ l) : x < v := by
  obtain ⟨k, -, rfl⟩ := List.mem_map.mp hl
  obtain ⟨u, -, rfl⟩ := List.mem_map.mp hx
  exact u.2

theorem length_branchWords (W : WallOfHeight h A) :
    W.branchWords.length = elemWallNumVerts h := by
  simp [branchWords]

theorem length_internalRuns (W : WallOfHeight h A) :
    W.internalRuns.length = (elemWallEdges h).length := by
  simp [internalRuns]

end WallOfHeight

/-- Rename the code of a wall: read the number `nv` of branch vertices and the number `ne` of
subdivision paths, rename the `nv` branch words, then the `ne` runs of internal vertices. -/
def mvWall (a o : Arr) (r : Reg) : Cmd :=
  .seq (.assign (r + 1) (.read a (.op .add (.reg r) (.const 1))))
    (.seq (.assign (r + 5) (.read a (.op .add (.reg r) (.const 2))))
      (.seq (.assign r (.op .add (.reg r) (.const 3)))
        (.seq (mvRun a o r) (mvPrefRunLoop a o r))))

/-- **The code of a wall.** `mvWall` turns `D ++ W.encList ++ T` into
`D ++ W.renamedEncList (o[·]) ++ T`, when the vertices of the graph of `W` are indices of
array `o`. -/
theorem mvWall_exec {w h v : ℕ} {A : MultiDigraph v} (W : WallOfHeight h A) {a o : Arr}
    (hao : a ≠ o) (r : Reg) {s : State} {D T : List ℕ} (ha : s.arrs a = D ++ W.encList ++ T)
    (hr : s.regs r = D.length) (hv : v ≤ (s.arrs o).length) (hv_w : v ≤ 2 ^ w)
    (ho_w : ∀ y ∈ s.arrs o, y < 2 ^ w) (hw1 : 1 < 2 ^ w)
    (hlen_w : (D ++ W.encList ++ T).length < 2 ^ w) :
    ∃ s' t, Exec w (mvWall a o r) s s' t ∧ t ≤ 35 * W.encList.length + 30 ∧
      s'.arrs a = D ++ W.renamedEncList (fun x => (s.arrs o).getD x 0) ++ T ∧
      s'.regs r = D.length + W.encList.length ∧
      (∀ b, b ≠ a → s'.arrs b = s.arrs b) ∧
      (∀ q, q ≠ r → q ≠ r + 1 → q ≠ r + 2 → q ≠ r + 5 → q ≠ r + 6 →
        s'.regs q = s.regs q) := by
  set φ : ℕ → ℕ := fun x => (s.arrs o).getD x 0 with hφ
  set nv := elemWallNumVerts h
  set ne := (elemWallEdges h).length
  have hE := W.encList_eq_runs
  have hlenE : W.encList.length = 3 + nv + (mvRunsCode W.internalRuns).length := by
    rw [hE]
    simp [W.length_branchWords, nv]
    omega
  have hL : (D ++ W.encList ++ T).length = D.length + W.encList.length + T.length := by
    simp
    omega
  have hlenA : (s.arrs a).length < 2 ^ w := by rw [ha]; exact hlen_w
  have hA0 : s.arrs a = D ++ h :: nv :: ne :: (W.branchWords ++ mvRunsCode W.internalRuns ++ T) := by
    rw [ha, hE]
    simp [nv, ne]
  have hlt1 : D.length + 1 < (s.arrs a).length := by rw [ha]; omega
  have hlt2 : D.length + 2 < (s.arrs a).length := by rw [ha]; omega
  have hget1 : (s.arrs a)[D.length + 1] = nv := by
    simp only [hA0]
    rw [List.getElem_append_right (by omega)]
    simp
  have hnv_w : nv < 2 ^ w := by
    have : nv ≤ W.encList.length := by omega
    omega
  have hne_w : ne < 2 ^ w := by
    have : ne = W.internalRuns.length := W.length_internalRuns.symm
    have := length_le_length_mvRunsCode W.internalRuns
    omega
  have hex₁ := mv_exec_assign_read' (r := r + 1) (a := a)
    (idx := .op .add (.reg r) (.const 1)) (s := s)
    (mv_eval_add_const hr (by omega)) hlt1 hget1 hnv_w
  set s₁ := s.setReg (r + 1) nv
  have hget2 : (s₁.arrs a)[D.length + 2] = ne := by
    change (s.arrs a)[D.length + 2] = ne
    simp only [hA0]
    rw [List.getElem_append_right (by omega)]
    simp
  have hr₁ : s₁.regs r = D.length := by rw [State.setReg_regs_ne _ _ (by romega)]; exact hr
  have hex₂ := mv_exec_assign_read' (r := r + 5) (a := a)
    (idx := .op .add (.reg r) (.const 2)) (s := s₁)
    (mv_eval_add_const hr₁ (by omega)) hlt2 hget2 hne_w
  set s₂ := s₁.setReg (r + 5) ne
  have hex₃ := mv_exec_assign_add (w := w) (r := r) (c := 3) (s := s₂)
    (show s₂.regs r = D.length by rw [State.setReg_regs_ne _ _ (by romega)]; exact hr₁)
    (by omega)
  set s₃ := s₂.setReg r (D.length + 3)
  have ho₃ : s₃.arrs o = s.arrs o := rfl
  have ha₃ : s₃.arrs a = (D ++ [h, nv, ne]) ++ W.branchWords ++
      (mvRunsCode W.internalRuns ++ T) := by
    change s.arrs a = _
    rw [hA0]
    simp
  obtain ⟨s₄, t₄, hex₄, ht₄, hA₄, hP₄, hB₄, hR₄⟩ :=
    mvRun_exec hao r (s := s₃) ha₃ (by simp [s₃])
      (by
        simp [s₃, s₂, s₁, State.setReg, Function.update, W.length_branchWords, nv])
      (fun x hx => by rw [ho₃]; exact lt_of_lt_of_le (W.mem_branchWords_lt hx) hv)
      (fun x hx => lt_of_lt_of_le (W.mem_branchWords_lt hx) hv_w) (by rw [ho₃]; exact ho_w)
      hw1 (by rw [← ha₃]; change (s.arrs a).length < _; rw [ha]; exact hlen_w)
  have ho₄ : s₄.arrs o = s.arrs o := (hB₄ o hao.symm).trans ho₃
  rw [ho₃] at hA₄
  have ha₄ : s₄.arrs a = (D ++ [h, nv, ne] ++ W.branchWords.map φ) ++
      mvRunsCode W.internalRuns ++ T := by
    rw [hA₄]
    simp [hφ]
  obtain ⟨s₅, t₅, hex₅, ht₅, hA₅, hP₅, hB₅, hR₅⟩ :=
    mvPrefRunLoop_exec hao r (s := s₄) ha₄ (by rw [hP₄]; simp; omega)
      (by
        rw [hR₄ _ (by romega) (by romega), State.setReg_regs_ne _ _ (by romega),
          State.setReg_regs_self, W.length_internalRuns])
      (fun l hl x hx => ⟨by rw [ho₄]; exact lt_of_lt_of_le (W.mem_internalRuns_lt hl hx) hv,
        lt_of_lt_of_le (W.mem_internalRuns_lt hl hx) hv_w⟩)
      (by rw [ho₄]; exact ho_w) hw1
      (by
        have : (D ++ [h, nv, ne] ++ W.branchWords.map φ ++ mvRunsCode W.internalRuns ++
            T).length = (D ++ W.encList ++ T).length := by
          simp [hlenE, W.length_branchWords, nv]
          omega
        rw [this]
        exact hlen_w)
  refine ⟨s₅, _, Exec.seq hex₁ (Exec.seq hex₂ (Exec.seq hex₃ (Exec.seq hex₄ hex₅))), ?_, ?_, ?_,
    ?_, ?_⟩
  · simp only [Expr.cost]
    have : W.internalRuns.length ≤ (mvRunsCode W.internalRuns).length :=
      length_le_length_mvRunsCode _
    rw [W.length_branchWords] at ht₄
    omega
  · rw [hA₅, ho₄]
    simp [WallOfHeight.renamedEncList, nv, ne, hφ]
  · rw [hP₅, hlenE]
    simp [W.length_branchWords, nv]
    omega
  · intro b hb
    rw [hB₅ b hb, hB₄ b hb]
    rfl
  · intro q h0 h1 h2 h5 h6
    rw [hR₅ q h0 h1 h2 h6, hR₄ q h0 h2, State.setReg_regs_ne _ _ h0,
      State.setReg_regs_ne _ _ h5, State.setReg_regs_ne _ _ h1]

/-! ### Member records -/

/-- The empty member record, used as a default. -/
def emptyMemberRecord : Case3MemberRecord := ⟨[], [], 0, [], []⟩

/-- Rename one member record: its vertex run, then its edge triples, then step over its tree
(`t_len`, the `t_len` parent words and the `e_len` leaf words). -/
def mvRecord (a o : Arr) (r : Reg) : Cmd :=
  .seq (mvPrefRun a o r)
    (.seq (.assign (r + 4) (.read a (.reg r)))
      (.seq (.assign r (.op .add (.reg r) (.const 1)))
        (.seq (mvTriples a o r)
          (.seq (.assign (r + 1) (.read a (.reg r)))
            (.seq (.assign r (.op .add (.reg r) (.const 1)))
              (.seq (.assign r (.op .add (.reg r) (.reg (r + 1))))
                (.assign r (.op .add (.reg r) (.reg (r + 4))))))))))

theorem length_enc_memberRecord (rec : Case3MemberRecord) :
    rec.enc.length = 3 + rec.vList.length + 3 * rec.eList.length + rec.parList.length +
      rec.tauList.length := by
  simp [Case3MemberRecord.enc, length_encEdgeTriples]
  omega

/-- **One member record.** `mvRecord` turns `D ++ rec.enc ++ T` into
`D ++ (rec.rename (o[·]) (mvTriple (o[·]))).enc ++ T`, when the lengths in `rec` are those of
its lists and its vertex words are indices of array `o`. -/
theorem mvRecord_exec {w : ℕ} {a o : Arr} (hao : a ≠ o) (r : Reg) {s : State}
    {D T : List ℕ} {rec : Case3MemberRecord} (ha : s.arrs a = D ++ rec.enc ++ T)
    (hr : s.regs r = D.length) (hpar : rec.parList.length = rec.t_len)
    (htau : rec.tauList.length = rec.eList.length)
    (hv : ∀ x ∈ rec.vList, x < (s.arrs o).length ∧ x < 2 ^ w)
    (he : ∀ e ∈ rec.eList, (e.1 < (s.arrs o).length ∧ e.2.1 < (s.arrs o).length) ∧
      e.1 < 2 ^ w ∧ e.2.1 < 2 ^ w)
    (ho_w : ∀ y ∈ s.arrs o, y < 2 ^ w) (hw3 : 3 < 2 ^ w)
    (hlen_w : (D ++ rec.enc ++ T).length < 2 ^ w) :
    ∃ s' t, Exec w (mvRecord a o r) s s' t ∧ t ≤ 53 * rec.enc.length + 40 ∧
      s'.arrs a = D ++ (rec.rename (fun x => (s.arrs o).getD x 0)
        (mvTriple (fun x => (s.arrs o).getD x 0))).enc ++ T ∧
      s'.regs r = D.length + rec.enc.length ∧
      (∀ b, b ≠ a → s'.arrs b = s.arrs b) ∧
      (∀ q, q ≠ r → q ≠ r + 1 → q ≠ r + 2 → q ≠ r + 3 → q ≠ r + 4 →
        s'.regs q = s.regs q) := by
  set φ : ℕ → ℕ := fun x => (s.arrs o).getD x 0 with hφ
  have hw1 : 1 < 2 ^ w := by omega
  have hlenE := length_enc_memberRecord rec
  have hL : (D ++ rec.enc ++ T).length = D.length + rec.enc.length + T.length := by
    simp
    omega
  -- the vertex run
  have ha₁ : s.arrs a = D ++ (rec.vList.length :: rec.vList) ++
      ((rec.eList.length :: encEdgeTriples rec.eList) ++ (rec.t_len :: rec.parList ++
        rec.tauList) ++ T) := by
    rw [ha]
    simp [Case3MemberRecord.enc]
  obtain ⟨s₁, t₁, hex₁, ht₁, hA₁, hP₁, hB₁, hR₁⟩ :=
    mvPrefRun_exec hao r ha₁ hr (fun x hx => (hv x hx).1) (fun x hx => (hv x hx).2) ho_w hw1
      (by rw [← ha₁, ha]; exact hlen_w)
  have ho₁ : s₁.arrs o = s.arrs o := hB₁ o hao.symm
  set D₁ := D ++ (rec.vList.length :: rec.vList.map φ) with hD₁
  have hA₁' : s₁.arrs a = D₁ ++ rec.eList.length :: (encEdgeTriples rec.eList ++
      (rec.t_len :: rec.parList ++ rec.tauList) ++ T) := by
    rw [hA₁, hD₁]
    simp
  have hD₁len : D₁.length = D.length + 1 + rec.vList.length := by simp [hD₁]; omega
  have hlen₁ : (s₁.arrs a).length = (D ++ rec.enc ++ T).length := by
    rw [hA₁', hL, hlenE]
    simp only [List.length_append, List.length_cons, hD₁len, length_encEdgeTriples]
    omega
  -- the edge triples
  have hel_w : rec.eList.length < 2 ^ w := by omega
  have hex₂ := mv_exec_assign_read (w := w) (a := a) (r := r + 4) (v := rec.eList.length)
    (pos := D₁.length) (s := s₁) (by rw [hP₁, hD₁len]) (by omega) (by omega)
    (by rw [show (s₁.arrs a)[D₁.length] = (D₁ ++ rec.eList.length :: (encEdgeTriples rec.eList ++
          (rec.t_len :: rec.parList ++ rec.tauList) ++ T))[D₁.length] by simp only [hA₁']]
        simp)
    hel_w
  set s₂ := s₁.setReg (r + 4) rec.eList.length
  have hex₃ := mv_exec_assign_add (w := w) (r := r) (c := 1) (s := s₂)
    (show s₂.regs r = D₁.length by
      rw [State.setReg_regs_ne _ _ (by romega), hP₁, hD₁len])
    (by omega)
  set s₃ := s₂.setReg r (D₁.length + 1)
  have ha₃ : s₃.arrs a = (D₁ ++ [rec.eList.length]) ++ encEdgeTriples rec.eList ++
      ((rec.t_len :: rec.parList ++ rec.tauList) ++ T) := by
    change s₁.arrs a = _
    rw [hA₁']
    simp
  obtain ⟨s₄, t₄, hex₄, ht₄, hA₄, hP₄, hB₄, hR₄⟩ :=
    mvTriples_exec hao r (s := s₃) ha₃ (by simp [s₃])
      (by simp [s₃, s₂, State.setReg, Function.update])
      (fun e he' => by
        change e.1 < (s₁.arrs o).length ∧ e.2.1 < (s₁.arrs o).length
        rw [ho₁]
        exact (he e he').1)
      (fun e he' => (he e he').2)
      (by change ∀ y ∈ s₁.arrs o, y < 2 ^ w; rw [ho₁]; exact ho_w) hw3
      (by rw [← ha₃]; change (s₁.arrs a).length < _; rw [hlen₁]; exact hlen_w)
  have ho₄ : s₄.arrs o = s.arrs o := (hB₄ o hao.symm).trans ho₁
  have ho₃ : s₃.arrs o = s.arrs o := ho₁
  rw [ho₃] at hA₄
  set D₂ := D₁ ++ [rec.eList.length] ++ encEdgeTriples (rec.eList.map (mvTriple φ)) with hD₂
  have hD₂len : D₂.length = D₁.length + 1 + 3 * rec.eList.length := by
    simp [hD₂, length_encEdgeTriples]
    omega
  have hA₄' : s₄.arrs a = D₂ ++ rec.t_len :: (rec.parList ++ rec.tauList ++ T) := by
    rw [hA₄, hD₂]
    simp
  have hP₄' : s₄.regs r = D₂.length := by
    rw [hP₄, hD₂len]
    simp
  have hlen₄ : (s₄.arrs a).length = (D ++ rec.enc ++ T).length := by
    rw [hA₄', hL, hlenE]
    simp only [List.length_append, List.length_cons, hD₂len, hD₁len]
    omega
  -- step over the tree
  have ht_w : rec.t_len < 2 ^ w := by omega
  have hex₅ := mv_exec_assign_read (w := w) (a := a) (r := r + 1) (v := rec.t_len)
    (s := s₄) hP₄' (by omega) (by omega)
    (by rw [show (s₄.arrs a)[D₂.length] = (D₂ ++ rec.t_len :: (rec.parList ++ rec.tauList ++
          T))[D₂.length] by simp only [hA₄']]
        simp)
    ht_w
  set s₅ := s₄.setReg (r + 1) rec.t_len
  have hex₆ := mv_exec_assign_add (w := w) (r := r) (c := 1) (s := s₅)
    (show s₅.regs r = D₂.length by rw [State.setReg_regs_ne _ _ (by romega), hP₄'])
    (by omega)
  set s₆ := s₅.setReg r (D₂.length + 1)
  have hex₇ := mv_exec_assign_add_reg (w := w) (r := r) (q := r) (q' := r + 1) (s := s₆)
    (x := D₂.length + 1) (y := rec.t_len)
    (by simp [s₆]) (by simp [s₆, s₅, State.setReg, Function.update]) (by omega)
  set s₇ := s₆.setReg r (D₂.length + 1 + rec.t_len)
  have h4 : s₇.regs (r + 4) = rec.eList.length := by
    simp only [s₇, s₆, s₅, State.setReg_regs_ne _ _ (show (r + 4 : Reg) ≠ r by romega),
      State.setReg_regs_ne _ _ (show (r + 4 : Reg) ≠ r + 1 by romega)]
    rw [hR₄ _ (by romega) (by romega) (by romega) (by romega)]
    simp [s₃, s₂, State.setReg, Function.update]
  have hex₈ := mv_exec_assign_add_reg (w := w) (r := r) (q := r) (q' := r + 4) (s := s₇)
    (x := D₂.length + 1 + rec.t_len) (y := rec.eList.length)
    (by simp [s₇]) h4 (by omega)
  refine ⟨_, _, Exec.seq hex₁ (Exec.seq hex₂ (Exec.seq hex₃ (Exec.seq hex₄ (Exec.seq hex₅
    (Exec.seq hex₆ (Exec.seq hex₇ hex₈)))))), ?_, ?_, ?_, ?_, ?_⟩
  · omega
  · change s₄.arrs a = _
    rw [hA₄', hD₂, hD₁]
    simp [Case3MemberRecord.enc, Case3MemberRecord.rename, hφ]
  · simp only [State.setReg_regs_self]
    rw [hD₂len, hD₁len, hlenE]
    omega
  · intro b hb
    change s₄.arrs b = _
    rw [hB₄ b hb]
    exact hB₁ b hb
  · intro q h0 h1 h2 h3 h4'
    simp only [s₇, s₆, s₅, State.setReg_regs_ne _ _ h0, State.setReg_regs_ne _ _ h1]
    rw [hR₄ q h0 h1 h2 h3]
    simp only [s₃, s₂, State.setReg_regs_ne _ _ h0, State.setReg_regs_ne _ _ h4']
    exact hR₁ q h0 h1 h2

/-- `m` member records in a row (`m` in register `r + 8`, loop index `r + 7`). -/
def mvRecordLoop (a o : Arr) (r : Reg) : Cmd :=
  .seq (.assign (r + 7) (.const 0)) (forUp (r + 7) (.reg (r + 8)) (mvRecord a o r))

theorem length_le_length_flatMap_enc (rs : List Case3MemberRecord) :
    rs.length ≤ (rs.flatMap Case3MemberRecord.enc).length := by
  induction rs with
  | nil => simp
  | cons rec L ih =>
    simp only [List.flatMap_cons, List.length_append, List.length_cons,
      length_enc_memberRecord] at ih ⊢
    omega

theorem sum_length_enc_eq (rs : List Case3MemberRecord) :
    ∑ j ∈ Finset.range rs.length, (rs[j]?.getD emptyMemberRecord).enc.length =
      (rs.flatMap Case3MemberRecord.enc).length := by
  induction rs with
  | nil => simp
  | cons rec L ih =>
    rw [List.length_cons, Finset.sum_range_succ']
    simp only [List.getElem?_cons_succ, List.getElem?_cons_zero, Option.getD_some,
      List.flatMap_cons, List.length_append] at ih ⊢
    rw [ih]
    omega

/-- **The member records.** `mvRecordLoop` turns `D ++ rs.flatMap enc ++ T` into
`D ++ (rs.map (rename (o[·]) (mvTriple (o[·])))).flatMap enc ++ T`. -/
theorem mvRecordLoop_exec {w : ℕ} {a o : Arr} (hao : a ≠ o) (r : Reg) {s : State}
    {D T : List ℕ} {rs : List Case3MemberRecord}
    (ha : s.arrs a = D ++ rs.flatMap Case3MemberRecord.enc ++ T)
    (hr : s.regs r = D.length) (hm : s.regs (r + 8) = rs.length)
    (hrs : ∀ rec ∈ rs, rec.parList.length = rec.t_len ∧
      rec.tauList.length = rec.eList.length ∧
      (∀ x ∈ rec.vList, x < (s.arrs o).length ∧ x < 2 ^ w) ∧
      (∀ e ∈ rec.eList, (e.1 < (s.arrs o).length ∧ e.2.1 < (s.arrs o).length) ∧
        e.1 < 2 ^ w ∧ e.2.1 < 2 ^ w))
    (ho_w : ∀ y ∈ s.arrs o, y < 2 ^ w) (hw3 : 3 < 2 ^ w)
    (hlen_w : (D ++ rs.flatMap Case3MemberRecord.enc ++ T).length < 2 ^ w) :
    ∃ s' t, Exec w (mvRecordLoop a o r) s s' t ∧
      t ≤ 53 * (rs.flatMap Case3MemberRecord.enc).length + 47 * rs.length + 5 ∧
      s'.arrs a = D ++ (rs.map (Case3MemberRecord.rename (fun x => (s.arrs o).getD x 0)
        (mvTriple (fun x => (s.arrs o).getD x 0)))).flatMap Case3MemberRecord.enc ++ T ∧
      s'.regs r = D.length + (rs.flatMap Case3MemberRecord.enc).length ∧
      (∀ b, b ≠ a → s'.arrs b = s.arrs b) ∧
      (∀ q, q ≠ r → q ≠ r + 1 → q ≠ r + 2 → q ≠ r + 3 → q ≠ r + 4 → q ≠ r + 7 →
        s'.regs q = s.regs q) := by
  set φ : ℕ → ℕ := fun x => (s.arrs o).getD x 0 with hφ
  set ρ := Case3MemberRecord.rename φ (mvTriple φ) with hρ
  have hw1 : 1 < 2 ^ w := by omega
  have hlen_rec : ∀ rec : Case3MemberRecord, (ρ rec).enc.length = rec.enc.length := by
    intro rec
    simp [ρ, Case3MemberRecord.rename, length_enc_memberRecord]
  have hlen_map : ∀ L : List Case3MemberRecord,
      ((L.map ρ).flatMap Case3MemberRecord.enc).length =
        (L.flatMap Case3MemberRecord.enc).length := by
    intro L
    induction L with
    | nil => rfl
    | cons rec L ih => simp only [List.map_cons, List.flatMap_cons, List.length_append, ih,
        hlen_rec]
  have hlenRs := length_le_length_flatMap_enc rs
  have hN_w : rs.length < 2 ^ w := by
    simp only [List.length_append] at hlen_w
    omega
  let I (i : ℕ) (st : State) : Prop :=
    st.arrs a = D ++ ((rs.take i).map ρ).flatMap Case3MemberRecord.enc ++
        (rs.drop i).flatMap Case3MemberRecord.enc ++ T ∧
      st.regs r = D.length + ((rs.take i).flatMap Case3MemberRecord.enc).length ∧
      st.regs (r + 7) = i ∧ st.regs (r + 8) = rs.length ∧
      (∀ b, b ≠ a → st.arrs b = s.arrs b) ∧
      (∀ q, q ≠ r → q ≠ r + 1 → q ≠ r + 2 → q ≠ r + 3 → q ≠ r + 4 → q ≠ r + 7 →
        st.regs q = s.regs q)
  have hstep : ∀ i < rs.length, ⦃I i⦄[w] mvRecord a o r
      ⦃fun s' => I (i + 1) (s'.setReg (r + 7) (i + 1)) ∧ s'.regs (r + 7) = i⦄ ≤
        fun _ => 53 * (rs[i]?.getD emptyMemberRecord).enc.length + 40 := by
    intro i hi st ⟨hA, hP, hI7, hK, hB, hR⟩
    set rec := rs[i] with hrec
    have hsplit : rs.drop i = rec :: rs.drop (i + 1) := List.drop_eq_getElem_cons hi
    have htake : rs.take (i + 1) = rs.take i ++ [rec] := by
      rw [List.take_add_one, List.getElem?_eq_getElem hi]
      rfl
    set L₁ := D ++ ((rs.take i).map ρ).flatMap Case3MemberRecord.enc with hL₁
    have hL₁len : L₁.length = D.length + ((rs.take i).flatMap Case3MemberRecord.enc).length := by
      simp only [hL₁, List.length_append, hlen_map]
    have hA' : st.arrs a = L₁ ++ rec.enc ++ ((rs.drop (i + 1)).flatMap Case3MemberRecord.enc ++
        T) := by
      rw [hA, hsplit]
      simp
    have hlen : (L₁ ++ rec.enc ++ ((rs.drop (i + 1)).flatMap Case3MemberRecord.enc ++
        T)).length = (D ++ rs.flatMap Case3MemberRecord.enc ++ T).length := by
      rw [← hA', hA]
      conv_rhs => rw [← List.take_append_drop i rs]
      simp only [List.length_append, List.flatMap_append, hL₁len]
      omega
    have hrmem : rec ∈ rs := List.getElem_mem hi
    have ho : st.arrs o = s.arrs o := hB o hao.symm
    obtain ⟨hpar, htau, hv, he⟩ := hrs rec hrmem
    obtain ⟨st', t', hex, ht', hA'', hP', hB', hR'⟩ :=
      mvRecord_exec hao r (s := st) hA' (by rw [hP, hL₁len]) hpar htau
        (fun x hx => by rw [ho]; exact hv x hx) (fun e he' => by rw [ho]; exact he e he')
        (by rw [ho]; exact ho_w) hw3 (hlen ▸ hlen_w)
    refine ⟨st', t', hex, ?_, ⟨?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
    · simp only [List.getElem?_eq_getElem hi, Option.getD_some]
      exact ht'
    · change st'.arrs a = _
      rw [hA'', ho, htake]
      simp [hL₁, hρ, hφ]
    · rw [State.setReg_regs_ne _ _ (by romega), hP', htake, hL₁len]
      simp
      omega
    · simp
    · rw [State.setReg_regs_ne _ _ (by romega),
        hR' _ (by romega) (by romega) (by romega) (by romega) (by romega)]
      exact hK
    · intro b hb
      change st'.arrs b = _
      rw [hB' b hb]
      exact hB b hb
    · intro q h0 h1 h2 h3 h4 h7
      rw [State.setReg_regs_ne _ _ h7, hR' q h0 h1 h2 h3 h4]
      exact hR q h0 h1 h2 h3 h4 h7
    · rw [hR' _ (by romega) (by romega) (by romega) (by romega) (by romega)]
      exact hI7
  have hloop := Triple.forUp_sum I rs.length
    (fun i => 53 * (rs[i]?.getD emptyMemberRecord).enc.length + 40)
    (r_i := r + 7) (hi := .reg (r + 8)) (body := mvRecord a o r) hw1
    hN_w (fun i _ st hI => ⟨hI.2.2.1, by simp [Expr.eval, checkWord, hI.2.2.2.1, hN_w]⟩) hstep
  have hex₀ : Exec w (.assign (r + 7) (.const 0)) s (s.setReg (r + 7) 0) 2 :=
    .assign (by simp [Expr.eval, checkWord])
  have hI₀ : I 0 (s.setReg (r + 7) 0) := by
    refine ⟨by rw [State.setReg_arrs, ha]; simp, ?_, by simp, ?_,
      fun _ _ => rfl, fun q _ _ _ _ _ hq => State.setReg_regs_ne _ _ hq⟩
    · rw [State.setReg_regs_ne _ _ (by romega)]; simpa using hr
    · rw [State.setReg_regs_ne _ _ (by romega)]; exact hm
  obtain ⟨s', t, hex, ht, hA, hP, -, -, hB, hR⟩ := hloop _ hI₀
  have hsum := sum_length_enc_eq rs
  refine ⟨s', 2 + t, Exec.seq hex₀ hex, ?_, ?_, ?_, hB, ?_⟩
  · simp only [Expr.cost, Finset.sum_add_distrib, Finset.sum_const, Finset.card_range,
      smul_eq_mul, ← Finset.mul_sum, hsum] at ht
    omega
  · rw [hA]
    simp
  · rw [hP]
    simp
  · intro q h0 h1 h2 h3 h4 h7
    rw [hR q h0 h1 h2 h3 h4 h7]

/-! ### The whole block -/

/-- Rename a whole Case (iii) block from position `0` on: the wall, the compass vertices, the
compass edges, the four corners and the member records. -/
def mvBlock (a o : Arr) (r : Reg) : Cmd :=
  .seq (mvWall a o r)
    (.seq (mvPrefRun a o r)
      (.seq (.assign (r + 4) (.read a (.reg r)))
        (.seq (.assign r (.op .add (.reg r) (.const 1)))
          (.seq (mvTriples a o r)
            (.seq (.assign (r + 1) (.const 4))
              (.seq (mvRun a o r)
                (.seq (.assign (r + 8) (.read a (.reg r)))
                  (.seq (.assign r (.op .add (.reg r) (.const 1)))
                    (mvRecordLoop a o r)))))))))

/-- The renamed block, with the renaming `φ` of vertex words. -/
def renamedBlock {h v : ℕ} {A : MultiDigraph v} (φ : ℕ → ℕ) (W : WallOfHeight h A)
    (K_vList : List ℕ) (K_eList : List (ℕ × ℕ × ℕ)) (corners : List ℕ)
    (members : List Case3MemberRecord) : List ℕ :=
  W.renamedEncList φ ++ (K_vList.length :: K_vList.map φ) ++
    (K_eList.length :: encEdgeTriples (K_eList.map (mvTriple φ))) ++ corners.map φ ++
    (members.length :: (members.map (Case3MemberRecord.rename φ (mvTriple φ))).flatMap
      Case3MemberRecord.enc)

/-- **The whole block.** Started with register `r` at `0` on an array
`encCase3Block W K_vList K_eList corners members ++ T`, `mvBlock` writes the renamed block in
place of the block and leaves in register `r` its length. The hypotheses say that the vertex
words are indices of array `o`, that there are four corners, and that the lengths in the
member records are those of their lists. -/
theorem mvBlock_exec {w h v : ℕ} {A : MultiDigraph v} (W : WallOfHeight h A)
    {K_vList : List ℕ} {K_eList : List (ℕ × ℕ × ℕ)} {corners : List ℕ}
    {members : List Case3MemberRecord} {a o : Arr} (hao : a ≠ o) (r : Reg) {s : State}
    {T : List ℕ} (ha : s.arrs a = encCase3Block W K_vList K_eList corners members ++ T)
    (hr : s.regs r = 0) (hv : v ≤ (s.arrs o).length) (hv_w : v ≤ 2 ^ w)
    (hKv : ∀ x ∈ K_vList, x < v) (hKe : ∀ e ∈ K_eList, e.1 < v ∧ e.2.1 < v)
    (hc : corners.length = 4) (hcv : ∀ x ∈ corners, x < v)
    (hms : ∀ rec ∈ members, rec.parList.length = rec.t_len ∧
      rec.tauList.length = rec.eList.length ∧ (∀ x ∈ rec.vList, x < v) ∧
      (∀ e ∈ rec.eList, e.1 < v ∧ e.2.1 < v))
    (ho_w : ∀ y ∈ s.arrs o, y < 2 ^ w) (hw4 : 4 < 2 ^ w)
    (hlen_w : (encCase3Block W K_vList K_eList corners members ++ T).length < 2 ^ w) :
    ∃ s' t, Exec w (mvBlock a o r) s s' t ∧
      t ≤ 100 * (encCase3Block W K_vList K_eList corners members).length + 200 ∧
      s'.arrs a = renamedBlock (fun x => (s.arrs o).getD x 0) W K_vList K_eList corners
        members ++ T ∧
      s'.regs r = (encCase3Block W K_vList K_eList corners members).length ∧
      (∀ b, b ≠ a → s'.arrs b = s.arrs b) ∧
      (∀ q, q < r → s'.regs q = s.regs q) := by
  set φ : ℕ → ℕ := fun x => (s.arrs o).getD x 0 with hφ
  set ρ := Case3MemberRecord.rename φ (mvTriple φ) with hρ
  have hw1 : 1 < 2 ^ w := by omega
  have hw3 : 3 < 2 ^ w := by omega
  set E := encCase3Block W K_vList K_eList corners members with hE
  have hEdef : E = W.encList ++ (K_vList.length :: K_vList) ++
      (K_eList.length :: encEdgeTriples K_eList) ++ corners ++
      (members.length :: members.flatMap Case3MemberRecord.enc) := rfl
  have hlenA : (s.arrs a).length = (E ++ T).length := by rw [ha]
  -- the wall
  set R₁ := (K_vList.length :: K_vList) ++ ((K_eList.length :: encEdgeTriples K_eList) ++
    (corners ++ ((members.length :: members.flatMap Case3MemberRecord.enc) ++ T))) with hR₁
  have ha₁ : s.arrs a = [] ++ W.encList ++ R₁ := by
    rw [ha, hEdef]
    simp [hR₁]
  obtain ⟨s₁, t₁, hex₁, ht₁, hA₁, hP₁, hB₁, hR₁'⟩ :=
    mvWall_exec W hao r ha₁ hr hv hv_w ho_w hw1 (by rw [← ha₁, hlenA]; exact hlen_w)
  have ho₁ : s₁.arrs o = s.arrs o := hB₁ o hao.symm
  -- the compass vertices
  set W' := W.renamedEncList φ with hW'
  set R₂ := (K_eList.length :: encEdgeTriples K_eList) ++
    (corners ++ ((members.length :: members.flatMap Case3MemberRecord.enc) ++ T)) with hR₂
  have hlenW' : W'.length = W.encList.length := by
    rw [hW', WallOfHeight.encList_eq_runs]
    simp [WallOfHeight.renamedEncList, length_mvRunsCode_map]
  have hlen₁ : (W' ++ (K_vList.length :: K_vList) ++ R₂).length = (E ++ T).length := by
    rw [hEdef]
    simp only [List.length_append, List.length_cons, hR₂, hlenW']
    omega
  obtain ⟨s₂, t₂, hex₂, ht₂, hA₂, hP₂, hB₂, hR₂'⟩ :=
    mvPrefRun_exec hao r (s := s₁) (D := W') (seg := K_vList) (T := R₂)
      (by rw [hA₁]; simp [hR₁, hR₂, hW', hφ])
      (by rw [hP₁, hlenW']; simp)
      (fun x hx => by rw [ho₁]; exact lt_of_lt_of_le (hKv x hx) hv)
      (fun x hx => lt_of_lt_of_le (hKv x hx) hv_w) (by rw [ho₁]; exact ho_w) hw1
      (hlen₁ ▸ hlen_w)
  have ho₂ : s₂.arrs o = s.arrs o := (hB₂ o hao.symm).trans ho₁
  rw [ho₁] at hA₂
  -- the compass edges
  set D₂ := W' ++ (K_vList.length :: K_vList.map φ) with hD₂
  have hD₂len : D₂.length = W.encList.length + 1 + K_vList.length := by
    simp [hD₂, hlenW']
    omega
  set R₃ := corners ++ ((members.length :: members.flatMap Case3MemberRecord.enc) ++ T) with hR₃
  have hA₂' : s₂.arrs a = D₂ ++ K_eList.length :: (encEdgeTriples K_eList ++ R₃) := by
    rw [hA₂, hR₂]
    simp [hD₂, hR₃]
  have hlen₂ : (s₂.arrs a).length = (E ++ T).length := by
    rw [hA₂', hEdef]
    simp only [List.length_append, List.length_cons, hR₃, hD₂len]
    omega
  have hP₂' : s₂.regs r = D₂.length := by rw [hP₂, hD₂len, hlenW']
  have hlt₂ : D₂.length < (s₂.arrs a).length := by rw [hA₂']; simp
  have hex₃ := mv_exec_assign_read (w := w) (a := a) (r := r + 4) (v := K_eList.length)
    (pos := D₂.length) (s := s₂) hP₂' (by omega) hlt₂ (mv_getElem_mid hA₂' hlt₂)
    (by
      have h1 : D₂.length + 1 + (encEdgeTriples K_eList).length ≤ (s₂.arrs a).length := by
        rw [hA₂']; simp; omega
      rw [length_encEdgeTriples] at h1
      omega)
  set s₃ := s₂.setReg (r + 4) K_eList.length
  have hex₄ := mv_exec_assign_add (w := w) (r := r) (c := 1) (s := s₃)
    (show s₃.regs r = D₂.length by rw [State.setReg_regs_ne _ _ (by romega), hP₂'])
    (by omega)
  set s₄ := s₃.setReg r (D₂.length + 1)
  obtain ⟨s₅, t₅, hex₅, ht₅, hA₅, hP₅, hB₅, hR₅'⟩ :=
    mvTriples_exec hao r (s := s₄) (D := D₂ ++ [K_eList.length]) (es := K_eList) (T := R₃)
      (by change s₂.arrs a = _; rw [hA₂']; simp)
      (by simp [s₄])
      (by simp [s₄, s₃, State.setReg, Function.update])
      (fun e he => by
        change e.1 < (s₂.arrs o).length ∧ e.2.1 < (s₂.arrs o).length
        rw [ho₂]
        exact ⟨lt_of_lt_of_le (hKe e he).1 hv, lt_of_lt_of_le (hKe e he).2 hv⟩)
      (fun e he => ⟨lt_of_lt_of_le (hKe e he).1 hv_w, lt_of_lt_of_le (hKe e he).2 hv_w⟩)
      (by change ∀ y ∈ s₂.arrs o, y < 2 ^ w; rw [ho₂]; exact ho_w) hw3
      (by
        have : (D₂ ++ [K_eList.length] ++ encEdgeTriples K_eList ++ R₃).length =
            (s₂.arrs a).length := by rw [hA₂']; simp
        rw [this, hlen₂]
        exact hlen_w)
  have ho₄ : s₄.arrs o = s.arrs o := ho₂
  have ho₅ : s₅.arrs o = s.arrs o := (hB₅ o hao.symm).trans ho₄
  rw [ho₄] at hA₅
  -- the corners
  set D₃ := D₂ ++ (K_eList.length :: encEdgeTriples (K_eList.map (mvTriple φ))) with hD₃
  have hD₃len : D₃.length = D₂.length + 1 + 3 * K_eList.length := by
    simp [hD₃, length_encEdgeTriples]
    omega
  set R₄ := (members.length :: members.flatMap Case3MemberRecord.enc) ++ T with hR₄
  have hA₅' : s₅.arrs a = D₃ ++ corners ++ R₄ := by
    rw [hA₅]
    simp [hD₃, hR₃, hR₄, hφ]
  have hlen₅ : (s₅.arrs a).length = (E ++ T).length := by
    rw [hA₅', hEdef]
    simp only [List.length_append, List.length_cons, hR₄, hD₃len, hD₂len,
      length_encEdgeTriples]
    omega
  have hP₅' : s₅.regs r = D₃.length := by rw [hP₅, hD₃len]; simp
  have hex₆ : Exec w (.assign (r + 1) (.const 4)) s₅ (s₅.setReg (r + 1) 4) 2 :=
    .assign (by simp [Expr.eval, checkWord]; omega)
  set s₆ := s₅.setReg (r + 1) 4
  obtain ⟨s₇, t₇, hex₇, ht₇, hA₇, hP₇, hB₇, hR₇'⟩ :=
    mvRun_exec hao r (s := s₆) (D := D₃) (seg := corners) (T := R₄) hA₅'
      (by rw [State.setReg_regs_ne _ _ (by romega)]; exact hP₅')
      (by simp [s₆, hc])
      (fun x hx => by
        change x < (s₅.arrs o).length
        rw [ho₅]
        exact lt_of_lt_of_le (hcv x hx) hv)
      (fun x hx => lt_of_lt_of_le (hcv x hx) hv_w)
      (by change ∀ y ∈ s₅.arrs o, y < 2 ^ w; rw [ho₅]; exact ho_w) hw1
      (by rw [← hA₅']; rw [hlen₅]; exact hlen_w)
  have ho₆ : s₆.arrs o = s.arrs o := ho₅
  have ho₇ : s₇.arrs o = s.arrs o := (hB₇ o hao.symm).trans ho₆
  rw [ho₆] at hA₇
  -- the member records
  set D₄ := D₃ ++ corners.map φ with hD₄
  have hD₄len : D₄.length = D₃.length + 4 := by simp [hD₄, hc]
  have hA₇' : s₇.arrs a = D₄ ++ members.length :: (members.flatMap Case3MemberRecord.enc ++ T) := by
    rw [hA₇, hR₄]
    simp [hD₄, hφ]
  have hlen₇ : (s₇.arrs a).length = (E ++ T).length := by
    rw [hA₇', hEdef]
    simp only [List.length_append, List.length_cons, hD₄len, hD₃len, hD₂len,
      length_encEdgeTriples, hc]
    omega
  have hP₇' : s₇.regs r = D₄.length := by rw [hP₇, hD₄len, hc]
  have hlt₇ : D₄.length < (s₇.arrs a).length := by rw [hA₇']; simp
  have hex₈ := mv_exec_assign_read (w := w) (a := a) (r := r + 8) (v := members.length)
    (pos := D₄.length) (s := s₇) hP₇' (by omega) hlt₇ (mv_getElem_mid hA₇' hlt₇)
    (by
      have := length_le_length_flatMap_enc members
      have h1 : D₄.length + 1 + (members.flatMap Case3MemberRecord.enc).length ≤
          (s₇.arrs a).length := by rw [hA₇']; simp; omega
      omega)
  set s₈ := s₇.setReg (r + 8) members.length
  have hex₉ := mv_exec_assign_add (w := w) (r := r) (c := 1) (s := s₈)
    (show s₈.regs r = D₄.length by rw [State.setReg_regs_ne _ _ (by romega), hP₇'])
    (by omega)
  set s₉ := s₈.setReg r (D₄.length + 1)
  have ho₉ : s₉.arrs o = s.arrs o := ho₇
  obtain ⟨s₁₀, t₁₀, hex₁₀, ht₁₀, hA₁₀, hP₁₀, hB₁₀, hR₁₀'⟩ :=
    mvRecordLoop_exec hao r (s := s₉) (D := D₄ ++ [members.length]) (rs := members) (T := T)
      (by change s₇.arrs a = _; rw [hA₇']; simp)
      (by simp [s₉])
      (by simp [s₉, s₈, State.setReg, Function.update])
      (fun rec hrec => by
        obtain ⟨h1, h2, h3, h4⟩ := hms rec hrec
        refine ⟨h1, h2, fun x hx => ?_, fun e he => ?_⟩
        · rw [ho₉]
          exact ⟨lt_of_lt_of_le (h3 x hx) hv, lt_of_lt_of_le (h3 x hx) hv_w⟩
        · rw [ho₉]
          exact ⟨⟨lt_of_lt_of_le (h4 e he).1 hv, lt_of_lt_of_le (h4 e he).2 hv⟩,
            lt_of_lt_of_le (h4 e he).1 hv_w, lt_of_lt_of_le (h4 e he).2 hv_w⟩)
      (by rw [ho₉]; exact ho_w) hw3
      (by
        have : (D₄ ++ [members.length] ++ members.flatMap Case3MemberRecord.enc ++ T).length =
            (s₇.arrs a).length := by rw [hA₇']; simp
        rw [this, hlen₇]
        exact hlen_w)
  rw [ho₉] at hA₁₀
  have hElen : E.length = D₄.length + 1 + (members.flatMap Case3MemberRecord.enc).length := by
    rw [hEdef, hD₄len, hD₃len, hD₂len]
    simp only [List.length_append, List.length_cons, length_encEdgeTriples, hc]
    omega
  refine ⟨s₁₀, _, Exec.seq hex₁ (Exec.seq hex₂ (Exec.seq hex₃ (Exec.seq hex₄ (Exec.seq hex₅
    (Exec.seq hex₆ (Exec.seq hex₇ (Exec.seq hex₈ (Exec.seq hex₉ hex₁₀)))))))), ?_, ?_, ?_, ?_,
    ?_⟩
  · have := length_le_length_flatMap_enc members
    have hEW : W.encList.length ≤ E.length := by rw [hEdef]; simp
    simp only [hc] at ht₇
    rw [hD₄len, hD₃len, hD₂len] at hElen
    omega
  · rw [hA₁₀]
    simp [renamedBlock, hD₄, hD₃, hD₂, hW', hφ]
  · rw [hP₁₀, hElen]
    simp
  · intro b hb
    rw [hB₁₀ b hb]
    change s₇.arrs b = _
    rw [hB₇ b hb]
    change s₅.arrs b = _
    rw [hB₅ b hb]
    change s₂.arrs b = _
    rw [hB₂ b hb, hB₁ b hb]
  · intro q hq
    rw [hR₁₀' q (by romega) (by romega) (by romega) (by romega) (by romega) (by romega),
      State.setReg_regs_ne _ _ (by romega), State.setReg_regs_ne _ _ (by romega),
      hR₇' q (by romega) (by romega), State.setReg_regs_ne _ _ (by romega),
      hR₅' q (by romega) (by romega) (by romega) (by romega),
      State.setReg_regs_ne _ _ (by romega), State.setReg_regs_ne _ _ (by romega),
      hR₂' q (by romega) (by romega) (by romega),
      hR₁' q (by romega) (by romega) (by romega) (by romega) (by romega)]

end GraphMinor.Compute
