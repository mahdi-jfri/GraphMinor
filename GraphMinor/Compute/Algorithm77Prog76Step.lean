module

public import GraphMinor.Compute.Algorithm77Prog76

/-!
# Word RAM Subroutines for Graph Minors XIII, Step (7.6): Subwall Realization and Ray Extension

This file continues `Algorithm77Prog76.lean` with:
1. **Section 1: Subwall Realization (`realizeSubwallCmd`) and Membership Marking (`markWallEncMemCmd`)**
   (`realizeBranchVertsLoop`, `appendRealizedEdgeCmd`, `condAppendRealizedEdgeCmd`,
   `realizeEdgesLoop`, `realizeSubwallCmd`, `markWallEncMemCmd`).
2. **Section 2: Canonical Elementary-Wall Paths, `pathToSubwallCmd`, and `runStep76Cmd`**.
-/

@[expose] public section

namespace GraphMinor.Compute

open SimpleGraph

set_option linter.deprecated false

attribute [local irreducible] elemWallCoords elemWallNumVerts elemWallEdges elemWallVertCoord

/-! ### Section 1: Subwall Realization (`realizeSubwallCmd`) and Membership Marking (`markWallEncMemCmd`) -/

theorem length_innerOfCode_le_four (h' : ℕ) (code : RealizationCode) (p q : ℕ × ℕ) :
    (innerOfCode h' code p q).length ≤ 4 := by
  unfold innerOfCode natHoleInner natHoleInnerO
  split_ifs <;> simp

theorem isChain_and_adj_getLastD_of_isChain_append_singleton {α : Type*} {R_adj : α → α → Prop}
    (x y : α) :
    ∀ (xs : List α),
      List.IsChain R_adj (x :: (xs ++ [y])) →
      List.IsChain R_adj (x :: xs) ∧ R_adj (xs.getLastD x) y
  | [], hc => by
    simp only [List.nil_append, List.isChain_cons_cons, List.IsChain.singleton,
      and_true, List.getLastD_nil] at hc ⊢
    exact ⟨trivial, hc⟩
  | z :: rest, hc => by
    simp only [List.cons_append, List.isChain_cons_cons] at hc ⊢
    rcases isChain_and_adj_getLastD_of_isChain_append_singleton z y rest hc.2 with ⟨hc_rest, hadj⟩
    have hlast : (z :: rest).getLastD x = rest.getLastD z := by cases rest <;> rfl
    rw [hlast]
    exact ⟨⟨hc.1, hc_rest⟩, hadj⟩

theorem elementaryWallAdj_of_mem_elemWallEdges {h : ℕ}
    {e : Fin (elemWallNumVerts h) × Fin (elemWallNumVerts h)} (he : e ∈ elemWallEdges h) :
    GM13.elementaryWallAdj h (elemWallVertCoord h e.1) (elemWallVertCoord h e.2) := by
  rcases List.mem_iff_getElem.mp he with ⟨i, hi, rfl⟩
  exact elemWallEdge_elementaryWallAdj h ⟨i, hi⟩

theorem mem_elemWallEdgesPrefix_of_le {h u v : ℕ} (huv : u ≤ v)
    {e : Fin (elemWallNumVerts h) × Fin (elemWallNumVerts h)}
    (he : e ∈ elemWallEdgesPrefix h u) :
    e ∈ elemWallEdgesPrefix h v := by
  induction huv with
  | refl => exact he
  | step _ ih =>
    rw [elemWallEdgesPrefix_succ]
    exact List.mem_append_left _ (List.mem_append_left _ ih)

theorem mem_elemWallEdges_of_mem_prefix {h u : ℕ} (hu : u ≤ elemWallNumVerts h)
    {e : Fin (elemWallNumVerts h) × Fin (elemWallNumVerts h)}
    (he : e ∈ elemWallEdgesPrefix h u) :
    e ∈ elemWallEdges h := by
  rw [← elemWallEdgesPrefix_full h]
  exact mem_elemWallEdgesPrefix_of_le hu he

/-- Internal subdivision vertices of `W.realizeSubwall R` along an edge `e' = (u₁', u₂')` of
`elementaryWall h'`. -/
def realizeEdgeInternalVerts {h h' n : ℕ} {G : MultiDigraph n} (W : WallOfHeight h G)
    {τ : GM13.Shape h h'} (R : τ.Realization)
    (e' : Fin (elemWallNumVerts h') × Fin (elemWallNumVerts h')) : List (Fin n) :=
  let p := elemWallVertCoord h' e'.1
  let q := elemWallVertCoord h' e'.2
  W.liftElemPathInternal (R.vmap p) (R.inner p q) (R.vmap q)

/-- Encoded flat list of internal vertex lists of `W.realizeSubwall R` for a list `es` of
elementary-wall edges of height `h'`. -/
def encRealizeEdgeList {h h' n : ℕ} {G : MultiDigraph n} (W : WallOfHeight h G)
    {τ : GM13.Shape h h'} (R : τ.Realization)
    (es : List (Fin (elemWallNumVerts h') × Fin (elemWallNumVerts h'))) : List ℕ :=
  es.flatMap (fun e' =>
    (realizeEdgeInternalVerts W R e').length :: (realizeEdgeInternalVerts W R e').map Fin.val)

@[simp]
theorem encRealizeEdgeList_nil {h h' n : ℕ} {G : MultiDigraph n} (W : WallOfHeight h G)
    {τ : GM13.Shape h h'} (R : τ.Realization) :
    encRealizeEdgeList W R [] = [] := rfl

@[simp]
theorem encRealizeEdgeList_append {h h' n : ℕ} {G : MultiDigraph n} (W : WallOfHeight h G)
    {τ : GM13.Shape h h'} (R : τ.Realization)
    (es₁ es₂ : List (Fin (elemWallNumVerts h') × Fin (elemWallNumVerts h'))) :
    encRealizeEdgeList W R (es₁ ++ es₂) =
      encRealizeEdgeList W R es₁ ++ encRealizeEdgeList W R es₂ :=
  List.flatMap_append

@[simp]
theorem encRealizeEdgeList_singleton {h h' n : ℕ} {G : MultiDigraph n} (W : WallOfHeight h G)
    {τ : GM13.Shape h h'} (R : τ.Realization)
    (e' : Fin (elemWallNumVerts h') × Fin (elemWallNumVerts h')) :
    encRealizeEdgeList W R [e'] =
      (realizeEdgeInternalVerts W R e').length :: (realizeEdgeInternalVerts W R e').map Fin.val := by
  simp [encRealizeEdgeList]

theorem encRealizeEdgeList_elemWallEdges {h h' n : ℕ} {G : MultiDigraph n} (W : WallOfHeight h G)
    {τ : GM13.Shape h h'} (R : τ.Realization) :
    encRealizeEdgeList W R (elemWallEdges h') =
      encInternalSlice (W.realizeSubwall R) (List.finRange (elemWallEdges h').length) := by
  have hmap :
      List.map (fun k' : Fin (elemWallEdges h').length => (elemWallEdges h')[k'.1]'k'.2)
        (List.finRange (elemWallEdges h').length) = elemWallEdges h' :=
    List.ext_getElem (by simp) (fun i _ _ => by simp)
  unfold encRealizeEdgeList encInternalSlice WallOfHeight.realizeSubwall realizeEdgeInternalVerts
  conv_lhs => rw [← hmap]
  rw [List.flatMap_map]

theorem encRealizeEdgeList_prefix_succ {h h' n : ℕ} {G : MultiDigraph n} (W : WallOfHeight h G)
    {τ : GM13.Shape h h'} (R : τ.Realization) (u' : ℕ) :
    encRealizeEdgeList W R (elemWallEdgesPrefix h' (u' + 1)) =
      encRealizeEdgeList W R (elemWallEdgesPrefix h' u') ++
      encRealizeEdgeList W R (elemWallHorizEdge h' u') ++
      encRealizeEdgeList W R (elemWallVertEdge h' u') := by
  rw [elemWallEdgesPrefix_succ, encRealizeEdgeList_append, encRealizeEdgeList_append]

theorem encRealizeEdgeList_prefix_length_mono {h h' n : ℕ} {G : MultiDigraph n}
    (W : WallOfHeight h G) {τ : GM13.Shape h h'} (R : τ.Realization) {u v : ℕ} (huv : u ≤ v) :
    (encRealizeEdgeList W R (elemWallEdgesPrefix h' u)).length ≤
      (encRealizeEdgeList W R (elemWallEdgesPrefix h' v)).length := by
  induction huv with
  | refl => exact le_refl _
  | step _ ih =>
    rw [encRealizeEdgeList_prefix_succ]
    simp only [List.length_append]
    omega

/-- Loop body of `realizeBranchVertsLoop`: computes `p = elemWallVertCoord h' r_32`, maps it by
`vmapOfCodeCmd 18 19`, and pushes `(W.coordBranchVertList (R.vmap p)).map Fin.val` to `bufArr2`. -/
def realizeBranchVertsBody : Cmd :=
  .seq (.assign 18 (.op .mod (.op .add (.reg 32) (.const 1)) (.reg 30)))
    (.seq (.assign 19 (.op .div (.op .add (.reg 32) (.const 1)) (.reg 30)))
      (.seq (vmapOfCodeCmd 18 19)
        (.seq (pushCoordBranchVertCmd bufArr2)
          (.seq (.assign 32 (.op .add (.reg 32) (.const 1)))
            (.assign 33 (.op .sub (.reg 33) (.const 1)))))))

/-- Loop appending all `V_{J'}` branch vertices of `W.realizeSubwall R` to `bufArr2`. -/
def realizeBranchVertsLoop : Cmd :=
  .while (.op .lt (.const 0) (.reg 33)) realizeBranchVertsBody

theorem realizeBranchVertsLoop_exec {w h' n : ℕ} {G : MultiDigraph n}
    (W : WallOfHeight (h' + 2) G)
    {τ : GM13.Shape (h' + 2) h'} (R : τ.Realization)
    (code : RealizationCode)
    (hvmap : ∀ p, vmapOfCode h' code p = R.vmap p)
    (hw4 : 4 < 2 ^ w)
    (hn_w : n < 2 ^ w)
    (hmode_le : code.mode ≤ 3)
    (hY0_w : code.Y0 < 2 ^ w)
    (hc0_w : code.c0 < 2 ^ w)
    (h3h'9_w : 3 * h' + 9 < 2 ^ w)
    (hVJW_w : elemWallNumVerts (h' + 2) + (2 * (h' + 2) + 2) < 2 ^ w)
    (henc_w : W.encList.length < 2 ^ w) :
    ∀ (rem idx : ℕ) (_hrem : idx + rem = elemWallNumVerts h') (pfx : List ℕ) {s : State}
      (_hs : WallStateHolds W s)
      (_hr15 : s.regs 15 = code.mode)
      (_hr16 : s.regs 16 = code.Y0)
      (_hr17 : s.regs 17 = code.c0)
      (_hr22 : s.regs 22 = h')
      (_hr30 : s.regs 30 = 2 * h' + 2)
      (_hr32 : s.regs 32 = idx)
      (_hr33 : s.regs 33 = rem)
      (_hbuf : IsArrBufPrefix (s.arrs bufArr2)
        (pfx ++ ((List.finRange (elemWallNumVerts h')).take idx).map
          (fun u' => ((W.realizeSubwall R).branchVert u').1))
        (s.regs 7))
      (_hcap : pfx.length + elemWallNumVerts h' ≤ (s.arrs bufArr2).length)
      (_hbuf_w : (s.arrs bufArr2).length < 2 ^ w),
      ∃ s' t,
        Exec w realizeBranchVertsLoop s s' t ∧
        t ≤ 260 * rem + 3 ∧
        IsArrBufPrefix (s'.arrs bufArr2)
          (pfx ++ (List.finRange (elemWallNumVerts h')).map
            (fun u' => ((W.realizeSubwall R).branchVert u').1))
          (s'.regs 7) ∧
        (s'.arrs bufArr2).length = (s.arrs bufArr2).length ∧
        (∀ r : Reg, r ≠ 6 → r ≠ 7 → r ≠ 8 → r ≠ 9 → r ≠ 18 → r ≠ 19 →
          r ≠ 32 → r ≠ 33 → s'.regs r = s.regs r) ∧
        (∀ a : Arr, a ≠ bufArr2 → s'.arrs a = s.arrs a)
  | 0, idx, hrem, pfx, s, _, _, _, _, _, _, _, hr33, hbuf, _, _ => by
    have h0_w : 0 < 2 ^ w := by omega
    have hidx : idx = elemWallNumVerts h' := by omega
    subst hidx
    have htake : (List.finRange (elemWallNumVerts h')).take (elemWallNumVerts h') =
        List.finRange (elemWallNumVerts h') :=
      List.take_of_length_le (by simp)
    rw [htake] at hbuf
    have hcond : (Expr.op .lt (.const 0) (.reg 33)).eval w s = some 0 := by
      simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hr33, h0_w]
    exact ⟨s, 3, .while_false hcond, by omega, hbuf, rfl,
      fun _ _ _ _ _ _ _ _ _ => rfl, fun _ _ => rfl⟩
  | rem + 1, idx, hrem, pfx, s, hs, hr15, hr16, hr17, hr22, hr30, hr32, hr33,
      hbuf, hcap, hbuf_w => by
    have h0_w : 0 < 2 ^ w := by omega
    have h1_w : 1 < 2 ^ w := by omega
    have h2_w : 2 < 2 ^ w := by omega
    have hu'_lt : idx < elemWallNumVerts h' := by omega
    let u' : Fin (elemWallNumVerts h') := ⟨idx, hu'_lt⟩
    let p := elemWallVertCoord h' u'
    have hp_eq : p = ((idx + 1) % (2 * h' + 2), (idx + 1) / (2 * h' + 2)) :=
      elemWallVertCoord_eq h' u'
    have hp1_eq : p.1 = (idx + 1) % (2 * h' + 2) := congrArg Prod.fst hp_eq
    have hp2_eq : p.2 = (idx + 1) / (2 * h' + 2) := congrArg Prod.snd hp_eq
    have hp_mem : p ∈ GM13.elementaryWallVerts h' := elemWallVertCoord_mem_elementaryWallVerts h' u'
    have hp_bounds := elemWallVerts_bounds hp_mem
    have hV'_le : elemWallNumVerts h' ≤ elemWallNumVerts (h' + 2) := by
      rw [elemWallNumVerts_eq h', elemWallNumVerts_eq (h' + 2)]
      have hmul : (h' + 1) * (2 * h' + 2) ≤ (h' + 2 + 1) * (2 * (h' + 2) + 2) := by nlinarith
      omega
    have hidx_w : idx < 2 ^ w := by omega
    have hidx1_w : idx + 1 < 2 ^ w := by omega
    have hrem_w : rem + 1 < 2 ^ w := by omega
    have hrem0_w : rem < 2 ^ w := by omega
    have hW'_pos : 0 < 2 * h' + 2 := by omega
    have hW'_w : 2 * h' + 2 < 2 ^ w := by omega
    have hp1_w : p.1 < 2 ^ w := by omega
    have hp2_w : p.2 < 2 ^ w := by omega
    have hmode_w : code.mode < 2 ^ w := by omega
    have hcond : (Expr.op .lt (.const 0) (.reg 33)).eval w s = some 1 := by
      simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hr33, h0_w, h1_w, hrem_w]
    let s₁ := s.setReg 18 p.1
    have hex₁ : Exec w (.assign 18 (.op .mod (.op .add (.reg 32) (.const 1)) (.reg 30))) s s₁ 6 :=
      .assign (by simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hr32, hr30,
        hidx_w, h1_w, hidx1_w, hW'_w, ← hp1_eq, hp1_w])
    let s₂ := s₁.setReg 19 p.2
    have hex₂ : Exec w (.assign 19 (.op .div (.op .add (.reg 32) (.const 1)) (.reg 30))) s₁ s₂ 6 :=
      .assign (by simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, s₁, hr32, hr30,
        hidx_w, h1_w, hidx1_w, hW'_w, ← hp2_eq, hp2_w])
    rcases vmapOfCodeCmd_exec (h' := h') code 18 19 (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        p (s := s₂) hw4 hmode_w hY0_w hc0_w (by omega) (by omega) hp_bounds.2.1
        (by simp [s₂, s₁, hr15]) (by simp [s₂, s₁, hr16])
        (by simp [s₂, s₁, hr17]) (by simp [s₂, s₁, hr22])
        (by simp [s₂, s₁]) (by simp [s₂]) with
      ⟨s₃, t_vm, hex₃, ht_vm, hr18_3, hr19_3, hregs₃, harrs₃⟩
    rw [hvmap p] at hr18_3 hr19_3
    have hRp_mem : R.vmap p ∈ GM13.elementaryWallVerts (h' + 2) := R.vmap_mem p hp_mem
    have hs₃ : WallStateHolds W s₃ := by
      refine hs.of_preserve ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ <;>
        try (rw [harrs₃]; rfl)
      · rw [hregs₃ 0 (by decide) (by decide)]; rfl
      · rw [hregs₃ 3 (by decide) (by decide)]; rfl
      · rw [hregs₃ 12 (by decide) (by decide)]; rfl
      · rw [hregs₃ 13 (by decide) (by decide)]; rfl
      · rw [hregs₃ 14 (by decide) (by decide)]; rfl
    have hr7_3 : s₃.regs 7 = s.regs 7 := by
      rw [hregs₃ 7 (by decide) (by decide)]; rfl
    have hbuf₃ : IsArrBufPrefix (s₃.arrs bufArr2)
        (pfx ++ ((List.finRange (elemWallNumVerts h')).take idx).map
          (fun u' => ((W.realizeSubwall R).branchVert u').1))
        (s₃.regs 7) := by
      rwa [harrs₃, hr7_3]
    rcases pushCoordBranchVertCmd_exec W bufArr2 (by decide) hRp_mem
        (pfx ++ ((List.finRange (elemWallNumVerts h')).take idx).map
          (fun u' => ((W.realizeSubwall R).branchVert u').1))
        (s := s₃)
        h2_w hn_w hVJW_w henc_w hs₃ hbuf₃
        (by
          rw [harrs₃]
          dsimp only [s₂, s₁]
          simp only [State.setReg_arrs, List.length_append, List.length_map, List.length_take,
            List.length_finRange, Nat.min_eq_left (by omega : idx ≤ elemWallNumVerts h')]
          omega)
        (by rwa [harrs₃]) hr18_3 hr19_3 with
      ⟨s₄, t_push, hex₄, ht_push, hbuf₄, hlen₄, hregs₄, harrs₄⟩
    have hbr_eq : (W.coordBranchVertList (R.vmap p)).map Fin.val =
        [((W.realizeSubwall R).branchVert u').1] := by
      rw [W.coordBranchVertList_of_mem hRp_mem]
      rfl
    have htake_succ :
        ((List.finRange (elemWallNumVerts h')).take idx).map
          (fun u' => ((W.realizeSubwall R).branchVert u').1) ++
          [((W.realizeSubwall R).branchVert u').1] =
        ((List.finRange (elemWallNumVerts h')).take (idx + 1)).map
          (fun u' => ((W.realizeSubwall R).branchVert u').1) := by
      rw [List.take_add_one]
      have hlt_fr : idx < (List.finRange (elemWallNumVerts h')).length := by simp [hu'_lt]
      simp [List.getElem?_eq_getElem hlt_fr, u']
    rw [hbr_eq, List.append_assoc, htake_succ] at hbuf₄
    have hr32_4 : s₄.regs 32 = idx := by
      rw [hregs₄ 32 (by decide) (by decide) (by decide),
        hregs₃ 32 (by decide) (by decide)]
      simp [s₂, s₁, hr32]
    have hr33_4 : s₄.regs 33 = rem + 1 := by
      rw [hregs₄ 33 (by decide) (by decide) (by decide),
        hregs₃ 33 (by decide) (by decide)]
      simp [s₂, s₁, hr33]
    let s₅ := s₄.setReg 32 (idx + 1)
    have hex₅ : Exec w (.assign 32 (.op .add (.reg 32) (.const 1))) s₄ s₅ 4 :=
      .assign (by simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hr32_4,
        hidx_w, h1_w, hidx1_w])
    let s₆ := s₅.setReg 33 rem
    have hex₆ : Exec w (.assign 33 (.op .sub (.reg 33) (.const 1))) s₅ s₆ 4 :=
      .assign (by simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, s₅, hr33_4,
        hrem_w, h1_w, hrem0_w])
    have hex_body : Exec w realizeBranchVertsBody s s₆ (6 + (6 + (t_vm + (t_push + (4 + 4))))) :=
      .seq hex₁ (.seq hex₂ (.seq hex₃ (.seq hex₄ (.seq hex₅ hex₆))))
    have hkeep_reg6 : ∀ r : Reg, r ≠ 6 → r ≠ 7 → r ≠ 8 → r ≠ 9 → r ≠ 18 → r ≠ 19 →
        r ≠ 32 → r ≠ 33 → s₆.regs r = s.regs r := by
      intro r h6 h7 h8 _ h18 h19 h32 h33
      dsimp only [s₆, s₅]
      rw [State.setReg_regs_ne _ _ h33, State.setReg_regs_ne _ _ h32,
        hregs₄ r h6 h7 h8, hregs₃ r h18 h19]
      simp [s₂, s₁, h18, h19]
    have hkeep_arr6 : ∀ a : Arr, a ≠ bufArr2 → s₆.arrs a = s.arrs a := by
      intro a ha
      dsimp only [s₆, s₅]
      rw [State.setReg_arrs, State.setReg_arrs, harrs₄ a ha, harrs₃]
      rfl
    have hs₆ : WallStateHolds W s₆ :=
      hs.of_arr_ne
        (hkeep_reg6 0 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))
        (hkeep_reg6 3 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))
        (hkeep_reg6 12 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))
        (hkeep_reg6 13 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))
        (hkeep_reg6 14 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))
        bufArr2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) hkeep_arr6
    have hlen₆ : (s₆.arrs bufArr2).length = (s.arrs bufArr2).length := by
      dsimp only [s₆, s₅]
      rw [State.setReg_arrs, State.setReg_arrs, hlen₄, harrs₃]
      rfl
    rcases realizeBranchVertsLoop_exec W R code hvmap hw4 hn_w hmode_le hY0_w hc0_w
        h3h'9_w hVJW_w henc_w rem (idx + 1) (by omega) pfx (s := s₆)
        hs₆
        (by rw [hkeep_reg6 15 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), hr15])
        (by rw [hkeep_reg6 16 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), hr16])
        (by rw [hkeep_reg6 17 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), hr17])
        (by rw [hkeep_reg6 22 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), hr22])
        (by rw [hkeep_reg6 30 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), hr30])
        (by dsimp only [s₆, s₅]; simp) (by dsimp only [s₆]; simp)
        (by dsimp only [s₆, s₅]; simpa using hbuf₄)
        (by rwa [hlen₆]) (by rwa [hlen₆]) with
      ⟨s', t_rest, hex_rest, ht_rest, hbuf', hlen', hregs', harrs'⟩
    refine ⟨s', 3 + (6 + (6 + (t_vm + (t_push + (4 + 4))))) + t_rest,
      .while_true hcond (by omega) hex_body hex_rest,
      by omega, hbuf', hlen'.trans hlen₆,
      fun r h6 h7 h8 h9 h18 h19 h32 h33 => by
        rw [hregs' r h6 h7 h8 h9 h18 h19 h32 h33, hkeep_reg6 r h6 h7 h8 h9 h18 h19 h32 h33],
      fun a ha => by
        rw [harrs' a ha, hkeep_arr6 a ha]⟩

/-- Append `(realizeEdgeInternalVerts W R e').length :: (realizeEdgeInternalVerts W R e').map Fin.val`
to `bufArr2` at `r_7` for an elementary-wall edge `e'` with `p = (r_26, r_27)` and `q = (r_28, r_29)`,
and increment `r_34`. -/
def appendRealizedEdgeCmd : Cmd :=
  .seq (.assign 25 (.reg 7))
  (.seq (.assign 6 (.const 0))
  (.seq (pushBuf6Cmd bufArr2)
  (.seq (.assign 18 (.reg 26))
  (.seq (.assign 19 (.reg 27))
  (.seq (.assign 20 (.reg 28))
  (.seq (.assign 21 (.reg 29))
  (.seq loadInnerOfCodeCmd
  (.seq (.assign 18 (.reg 26))
  (.seq (.assign 19 (.reg 27))
  (.seq (vmapOfCodeCmd 18 19)
  (.seq (appendLiftElemStepsLoop bufArr2)
  (.seq (.assign 20 (.reg 28))
  (.seq (.assign 21 (.reg 29))
  (.seq (vmapOfCodeCmd 20 21)
  (.seq (appendStepInternalCmd bufArr2)
  (.seq (.write bufArr2 (.reg 25) (.op .sub (.op .sub (.reg 7) (.reg 25)) (.const 1)))
    (.assign 34 (.op .add (.reg 34) (.const 1)))))))))))))))))))

theorem appendRealizedEdgeCmd_exec {w h' n : ℕ} {G : MultiDigraph n}
    (W : WallOfHeight (h' + 2) G)
    {τ : GM13.Shape (h' + 2) h'} (R : τ.Realization)
    (code : RealizationCode)
    (hvmap : ∀ p, vmapOfCode h' code p = R.vmap p)
    (hinner : ∀ p q, innerOfCode h' code p q = R.inner p q)
    (e' : Fin (elemWallNumVerts h') × Fin (elemWallNumVerts h'))
    (he' : e' ∈ elemWallEdges h')
    (pfx : List ℕ) (ecnt : ℕ)
    {s : State}
    (hw4 : 4 < 2 ^ w)
    (hn_w : n < 2 ^ w)
    (hmode_le : code.mode ≤ 3)
    (hY0_w : code.Y0 < 2 ^ w)
    (hc0_w : code.c0 < 2 ^ w)
    (h3h'9_w : 3 * h' + 9 < 2 ^ w)
    (hVJW_w : elemWallNumVerts (h' + 2) + (2 * (h' + 2) + 2) < 2 ^ w)
    (hloc_w : elemWallNumVerts (h' + 2) + (elemWallEdges (h' + 2)).length < 2 ^ w)
    (henc_w : W.encList.length < 2 ^ w)
    (hecnt_w : ecnt + 1 < 2 ^ w)
    (hs : WallStateHolds W s)
    (hr15 : s.regs 15 = code.mode)
    (hr16 : s.regs 16 = code.Y0)
    (hr17 : s.regs 17 = code.c0)
    (hr22 : s.regs 22 = h')
    (hr26 : s.regs 26 = (elemWallVertCoord h' e'.1).1)
    (hr27 : s.regs 27 = (elemWallVertCoord h' e'.1).2)
    (hr28 : s.regs 28 = (elemWallVertCoord h' e'.2).1)
    (hr29 : s.regs 29 = (elemWallVertCoord h' e'.2).2)
    (hr34 : s.regs 34 = ecnt)
    (hbuf : IsArrBufPrefix (s.arrs bufArr2) pfx (s.regs 7))
    (hcap : pfx.length + (encRealizeEdgeList W R [e']).length ≤ (s.arrs bufArr2).length)
    (hbuf_w : (s.arrs bufArr2).length < 2 ^ w) :
    ∃ s' t,
      Exec w appendRealizedEdgeCmd s s' t ∧
      t ≤ 1300 * (encRealizeEdgeList W R [e']).length ∧
      IsArrBufPrefix (s'.arrs bufArr2) (pfx ++ encRealizeEdgeList W R [e']) (s'.regs 7) ∧
      (s'.arrs bufArr2).length = (s.arrs bufArr2).length ∧
      s'.regs 34 = ecnt + 1 ∧
      (∀ r : Reg, r ≠ 6 → r ≠ 7 → r ≠ 8 → r ≠ 9 → r ≠ 10 → r ≠ 11 →
        r ≠ 18 → r ≠ 19 → r ≠ 20 → r ≠ 21 → r ≠ 25 → r ≠ 34 → s'.regs r = s.regs r) ∧
      (∀ a : Arr, a ≠ bufArr2 → a ≠ coordXArr → a ≠ coordYArr → s'.arrs a = s.arrs a) := by
  have h0_w : 0 < 2 ^ w := by omega
  have h1_w : 1 < 2 ^ w := by omega
  have h2_w : 2 < 2 ^ w := by omega
  have hmode_w : code.mode < 2 ^ w := by omega
  let p := elemWallVertCoord h' e'.1
  let q := elemWallVertCoord h' e'.2
  have hpq_adj : GM13.elementaryWallAdj h' p q := elementaryWallAdj_of_mem_elemWallEdges he'
  have hp_bounds := elemWallVerts_bounds hpq_adj.1
  have hq_bounds := elemWallVerts_bounds hpq_adj.2.1
  have hp1_w : p.1 < 2 ^ w := by omega
  have hp2_w : p.2 < 2 ^ w := by omega
  have hq1_w : q.1 < 2 ^ w := by omega
  have hq2_w : q.2 < 2 ^ w := by omega
  have hRp_mem : R.vmap p ∈ GM13.elementaryWallVerts (h' + 2) := R.vmap_mem p hpq_adj.1
  have hRq_mem : R.vmap q ∈ GM13.elementaryWallVerts (h' + 2) := R.vmap_mem q hpq_adj.2.1
  have hfull_chain : List.IsChain (GM13.elementaryWallAdj (h' + 2))
      (R.vmap p :: (R.inner p q ++ [R.vmap q])) := R.chain p q hpq_adj
  rcases isChain_and_adj_getLastD_of_isChain_append_singleton (R.vmap p) (R.vmap q)
      (R.inner p q) hfull_chain with
    ⟨hchain_in, hadj_last⟩
  have hlen_in_le : (R.inner p q).length ≤ 4 := by
    rw [← hinner p q]
    exact length_innerOfCode_le_four h' code p q
  have hrealize_eq :
      realizeEdgeInternalVerts W R e' =
        liftElemSteps W (R.vmap p) (R.inner p q) ++
        W.stepInternalVerts ((R.inner p q).getLastD (R.vmap p)) (R.vmap q) :=
    liftElemPathInternal_eq_liftElemSteps W (R.vmap p) (R.inner p q) (R.vmap q)
  have hrealize_len :
      (realizeEdgeInternalVerts W R e').length =
        (liftElemSteps W (R.vmap p) (R.inner p q)).length +
        (W.stepInternalVerts ((R.inner p q).getLastD (R.vmap p)) (R.vmap q)).length := by
    rw [hrealize_eq, List.length_append]
  have henc_single_len :
      (encRealizeEdgeList W R [e']).length = 1 + (realizeEdgeInternalVerts W R e').length := by
    simp [encRealizeEdgeList_singleton]; omega
  have hpfx_w : pfx.length < 2 ^ w := by omega
  let s₁ := s.setReg 25 pfx.length
  have hex₁ : Exec w (.assign 25 (.reg 7)) s s₁ 2 :=
    .assign (by simp [Expr.eval, checkWord, hbuf.1, hpfx_w])
  let s₂ := s₁.setReg 6 0
  have hex₂ : Exec w (.assign 6 (.const 0)) s₁ s₂ 2 :=
    .assign (by simp [Expr.eval, checkWord, h0_w])
  rcases pushBuf6Cmd_exec bufArr2 0 (s := s₂)
      h1_w h0_w (by simpa [s₂, s₁] using hbuf_w)
      (by simpa [s₂, s₁] using hbuf)
      (by simp [s₂, s₁]; omega) rfl with
    ⟨s₃, t_p0, hex₃, ht_p0, hbuf₃, hlen₃, hregs₃, harrs₃⟩
  have hkeep_reg3 : ∀ r : Reg, r ≠ 6 → r ≠ 7 → r ≠ 25 → s₃.regs r = s.regs r := by
    intro r h6 h7 h25
    rw [hregs₃ r h7]
    simp [s₂, s₁, h6, h25]
  let s₄ := s₃.setReg 18 p.1
  have hr26_3 : s₃.regs 26 = p.1 := by
    rw [hkeep_reg3 26 (by decide) (by decide) (by decide)]; exact hr26
  have hex₄ : Exec w (.assign 18 (.reg 26)) s₃ s₄ 2 :=
    .assign (by simp [Expr.eval, checkWord, hr26_3, hp1_w])
  let s₅ := s₄.setReg 19 p.2
  have hr27_4 : s₄.regs 27 = p.2 := by
    dsimp only [s₄]
    rw [State.setReg_regs_ne _ _ (by decide), hkeep_reg3 27 (by decide) (by decide) (by decide)]
    exact hr27
  have hex₅ : Exec w (.assign 19 (.reg 27)) s₄ s₅ 2 :=
    .assign (by simp [Expr.eval, checkWord, hr27_4, hp2_w])
  let s₆ := s₅.setReg 20 q.1
  have hr28_5 : s₅.regs 28 = q.1 := by
    dsimp only [s₅, s₄]
    rw [State.setReg_regs_ne _ _ (by decide), State.setReg_regs_ne _ _ (by decide),
      hkeep_reg3 28 (by decide) (by decide) (by decide)]
    exact hr28
  have hex₆ : Exec w (.assign 20 (.reg 28)) s₅ s₆ 2 :=
    .assign (by simp [Expr.eval, checkWord, hr28_5, hq1_w])
  let s₇ := s₆.setReg 21 q.2
  have hr29_6 : s₆.regs 29 = q.2 := by
    dsimp only [s₆, s₅, s₄]
    rw [State.setReg_regs_ne _ _ (by decide), State.setReg_regs_ne _ _ (by decide),
      State.setReg_regs_ne _ _ (by decide), hkeep_reg3 29 (by decide) (by decide) (by decide)]
    exact hr29
  have hex₇ : Exec w (.assign 21 (.reg 29)) s₆ s₇ 2 :=
    .assign (by simp [Expr.eval, checkWord, hr29_6, hq2_w])
  rcases loadInnerOfCodeCmd_exec (h' := h') code p q (s := s₇)
      hw4 hmode_le hY0_w hc0_w h3h'9_w (by omega) hp_bounds.2.1 (by omega) hq_bounds.2.1
      (by dsimp only [s₇, s₆, s₅, s₄]; simp [hkeep_reg3 15 (by decide) (by decide) (by decide), hr15])
      (by dsimp only [s₇, s₆, s₅, s₄]; simp [hkeep_reg3 16 (by decide) (by decide) (by decide), hr16])
      (by dsimp only [s₇, s₆, s₅, s₄]; simp [hkeep_reg3 17 (by decide) (by decide) (by decide), hr17])
      (by dsimp only [s₇, s₆, s₅, s₄]; simp [hkeep_reg3 22 (by decide) (by decide) (by decide), hr22])
      (by dsimp only [s₇, s₆, s₅, s₄]; simp) (by dsimp only [s₇, s₆, s₅]; simp)
      (by dsimp only [s₇, s₆]; simp) (by dsimp only [s₇]; simp) with
    ⟨s₈, t_in, hex₈, ht_in, hcx₈, hcy₈, hr10_8, hr11_8, hregs₈, harrs₈⟩
  rw [hinner p q] at hcx₈ hcy₈ hr11_8
  have hkeep_reg8 : ∀ r : Reg, r ≠ 6 → r ≠ 7 → r ≠ 8 → r ≠ 9 → r ≠ 10 → r ≠ 11 →
      r ≠ 18 → r ≠ 19 → r ≠ 20 → r ≠ 21 → r ≠ 25 → s₈.regs r = s.regs r := by
    intro r h6 h7 h8 h9 h10 h11 h18 h19 h20 h21 h25
    rw [hregs₈ r h6 h8 h9 h10 h11 h18 h19 h20 h21]
    dsimp only [s₇, s₆, s₅, s₄]
    simp [h18, h19, h20, h21, hkeep_reg3 r h6 h7 h25]
  let s₉ := s₈.setReg 18 p.1
  have hr26_8 : s₈.regs 26 = p.1 := by
    rw [hkeep_reg8 26 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide)]
    exact hr26
  have hex₉ : Exec w (.assign 18 (.reg 26)) s₈ s₉ 2 :=
    .assign (by simp [Expr.eval, checkWord, hr26_8, hp1_w])
  let s₁₀ := s₉.setReg 19 p.2
  have hr27_9 : s₉.regs 27 = p.2 := by
    dsimp only [s₉]
    rw [State.setReg_regs_ne _ _ (by decide),
      hkeep_reg8 27 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide) (by decide)]
    exact hr27
  have hex₁₀ : Exec w (.assign 19 (.reg 27)) s₉ s₁₀ 2 :=
    .assign (by simp [Expr.eval, checkWord, hr27_9, hp2_w])
  rcases vmapOfCodeCmd_exec (h' := h') code 18 19 (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      p (s := s₁₀) hw4 hmode_w hY0_w hc0_w (by omega) (by omega) hp_bounds.2.1
      (by dsimp only [s₁₀, s₉]; simp [hkeep_reg8 15 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), hr15])
      (by dsimp only [s₁₀, s₉]; simp [hkeep_reg8 16 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), hr16])
      (by dsimp only [s₁₀, s₉]; simp [hkeep_reg8 17 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), hr17])
      (by dsimp only [s₁₀, s₉]; simp [hkeep_reg8 22 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), hr22])
      (by dsimp only [s₁₀, s₉]; simp) (by dsimp only [s₁₀]; simp) with
    ⟨s₁₁, t_vm1, hex₁₁, ht_vm1, hr18_11, hr19_11, hregs₁₁, harrs₁₁⟩
  rw [hvmap p] at hr18_11 hr19_11
  have hkeep_reg11 : ∀ r : Reg, r ≠ 6 → r ≠ 7 → r ≠ 8 → r ≠ 9 → r ≠ 10 → r ≠ 11 →
      r ≠ 18 → r ≠ 19 → r ≠ 20 → r ≠ 21 → r ≠ 25 → s₁₁.regs r = s.regs r := by
    intro r h6 h7 h8 h9 h10 h11 h18 h19 h20 h21 h25
    rw [hregs₁₁ r h18 h19]
    dsimp only [s₁₀, s₉]
    simp [h18, h19, hkeep_reg8 r h6 h7 h8 h9 h10 h11 h18 h19 h20 h21 h25]
  have hkeep_arr11 : ∀ a : Arr, a ≠ bufArr2 → a ≠ coordXArr → a ≠ coordYArr →
      s₁₁.arrs a = s.arrs a := by
    intro a ha1 ha2 ha3
    rw [harrs₁₁]
    dsimp only [s₁₀, s₉]
    rw [State.setReg_arrs, State.setReg_arrs, harrs₈ a ha2 ha3]
    dsimp only [s₇, s₆, s₅, s₄]
    simp only [State.setReg_arrs]
    rw [harrs₃ a ha1]
    rfl
  have hs₁₁ : WallStateHolds W s₁₁ :=
    hs.of_preserve
      (hkeep_reg11 0 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))
      (hkeep_reg11 3 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))
      (hkeep_reg11 12 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))
      (hkeep_reg11 13 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))
      (hkeep_reg11 14 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))
      (hkeep_arr11 wallEncArr (by decide) (by decide) (by decide))
      (hkeep_arr11 locArr (by decide) (by decide) (by decide))
      (hkeep_arr11 wallMemArr (by decide) (by decide) (by decide))
      (hkeep_arr11 edgeOffArr (by decide) (by decide) (by decide))
      (hkeep_arr11 edgeLenArr (by decide) (by decide) (by decide))
      (hkeep_arr11 edgeU1Arr (by decide) (by decide) (by decide))
      (hkeep_arr11 edgeU2Arr (by decide) (by decide) (by decide))
      (hkeep_arr11 horizEdgeIdxArr (by decide) (by decide) (by decide))
      (hkeep_arr11 vertEdgeIdxArr (by decide) (by decide) (by decide))
  have hcx₁₁ : s₁₁.arrs coordXArr = (R.inner p q).map Prod.fst := by
    rw [harrs₁₁]; exact hcx₈
  have hcy₁₁ : s₁₁.arrs coordYArr = (R.inner p q).map Prod.snd := by
    rw [harrs₁₁]; exact hcy₈
  have hbuf₁₁ : IsArrBufPrefix (s₁₁.arrs bufArr2) (pfx ++ [0]) (s₁₁.regs 7) := by
    have h1 : s₁₁.arrs bufArr2 = s₃.arrs bufArr2 := by
      rw [harrs₁₁]
      dsimp only [s₁₀, s₉]
      rw [State.setReg_arrs, State.setReg_arrs, harrs₈ bufArr2 (by decide) (by decide)]
      rfl
    have h2 : s₁₁.regs 7 = s₃.regs 7 := by
      rw [hregs₁₁ 7 (by decide) (by decide)]
      dsimp only [s₁₀, s₉]
      rw [State.setReg_regs_ne _ _ (by decide), State.setReg_regs_ne _ _ (by decide),
        hregs₈ 7 (by decide) (by decide) (by decide) (by decide) (by decide)
          (by decide) (by decide) (by decide) (by decide)]
      rfl
    rw [h1, h2]
    exact hbuf₃
  have hlen₁₁ : (s₁₁.arrs bufArr2).length = (s.arrs bufArr2).length := by
    rw [harrs₁₁]
    dsimp only [s₁₀, s₉]
    rw [State.setReg_arrs, State.setReg_arrs, harrs₈ bufArr2 (by decide) (by decide)]
    exact hlen₃
  rcases appendLiftElemStepsLoop_exec W bufArr2
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide)
      h2_w hn_w hVJW_w hloc_w henc_w
      (R.inner p q) (R.vmap p) 0 (pfx ++ [0]) (s := s₁₁)
      hRp_mem hchain_in hs₁₁ (by omega)
      (by simp [hcx₁₁]) (by simp [hcy₁₁])
      (fun j hj => by simp [hcx₁₁, hcy₁₁, hj])
      hbuf₁₁
      (by rw [hlen₁₁]; simp only [List.length_append, List.length_singleton]; omega)
      (by rwa [hlen₁₁])
      (by rw [hregs₁₁ 10 (by decide) (by decide)]; dsimp only [s₁₀, s₉]; simpa using hr10_8)
      (by rw [hregs₁₁ 11 (by decide) (by decide)]; dsimp only [s₁₀, s₉]; simpa using hr11_8)
      hr18_11 hr19_11 with
    ⟨s₁₂, t_steps, hex₁₂, ht_steps, hbuf₁₂, hlen₁₂, hr18_12, hr19_12, hregs₁₂, harrs₁₂⟩
  have hkeep_reg12 : ∀ r : Reg, r ≠ 6 → r ≠ 7 → r ≠ 8 → r ≠ 9 → r ≠ 10 → r ≠ 11 →
      r ≠ 18 → r ≠ 19 → r ≠ 20 → r ≠ 21 → r ≠ 25 → s₁₂.regs r = s.regs r := by
    intro r h6 h7 h8 h9 h10 h11 h18 h19 h20 h21 h25
    rw [hregs₁₂ r h6 h7 h8 h9 h10 h11 h18 h19 h20 h21,
      hkeep_reg11 r h6 h7 h8 h9 h10 h11 h18 h19 h20 h21 h25]
  let s₁₃ := s₁₂.setReg 20 q.1
  have hr28_12 : s₁₂.regs 28 = q.1 := by
    rw [hkeep_reg12 28 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide)]
    exact hr28
  have hex₁₃ : Exec w (.assign 20 (.reg 28)) s₁₂ s₁₃ 2 :=
    .assign (by simp [Expr.eval, checkWord, hr28_12, hq1_w])
  let s₁₄ := s₁₃.setReg 21 q.2
  have hr29_13 : s₁₃.regs 29 = q.2 := by
    dsimp only [s₁₃]
    rw [State.setReg_regs_ne _ _ (by decide),
      hkeep_reg12 29 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide) (by decide)]
    exact hr29
  have hex₁₄ : Exec w (.assign 21 (.reg 29)) s₁₃ s₁₄ 2 :=
    .assign (by simp [Expr.eval, checkWord, hr29_13, hq2_w])
  rcases vmapOfCodeCmd_exec (h' := h') code 20 21 (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      q (s := s₁₄) hw4 hmode_w hY0_w hc0_w (by omega) (by omega) hq_bounds.2.1
      (by dsimp only [s₁₄, s₁₃]; simp [hkeep_reg12 15 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), hr15])
      (by dsimp only [s₁₄, s₁₃]; simp [hkeep_reg12 16 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), hr16])
      (by dsimp only [s₁₄, s₁₃]; simp [hkeep_reg12 17 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), hr17])
      (by dsimp only [s₁₄, s₁₃]; simp [hkeep_reg12 22 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), hr22])
      (by dsimp only [s₁₄, s₁₃]; simp) (by dsimp only [s₁₄]; simp) with
    ⟨s₁₅, t_vm2, hex₁₅, ht_vm2, hr20_15, hr21_15, hregs₁₅, harrs₁₅⟩
  rw [hvmap q] at hr20_15 hr21_15
  have hkeep_reg15 : ∀ r : Reg, r ≠ 6 → r ≠ 7 → r ≠ 8 → r ≠ 9 → r ≠ 10 → r ≠ 11 →
      r ≠ 18 → r ≠ 19 → r ≠ 20 → r ≠ 21 → r ≠ 25 → s₁₅.regs r = s.regs r := by
    intro r h6 h7 h8 h9 h10 h11 h18 h19 h20 h21 h25
    rw [hregs₁₅ r h20 h21]
    dsimp only [s₁₄, s₁₃]
    simp [h20, h21, hkeep_reg12 r h6 h7 h8 h9 h10 h11 h18 h19 h20 h21 h25]
  have hkeep_arr15 : ∀ a : Arr, a ≠ bufArr2 → a ≠ coordXArr → a ≠ coordYArr →
      s₁₅.arrs a = s.arrs a := by
    intro a ha1 ha2 ha3
    rw [harrs₁₅]
    dsimp only [s₁₄, s₁₃]
    rw [State.setReg_arrs, State.setReg_arrs, harrs₁₂ a ha1]
    exact hkeep_arr11 a ha1 ha2 ha3
  have hs₁₅ : WallStateHolds W s₁₅ :=
    hs.of_preserve
      (hkeep_reg15 0 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))
      (hkeep_reg15 3 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))
      (hkeep_reg15 12 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))
      (hkeep_reg15 13 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))
      (hkeep_reg15 14 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))
      (hkeep_arr15 wallEncArr (by decide) (by decide) (by decide))
      (hkeep_arr15 locArr (by decide) (by decide) (by decide))
      (hkeep_arr15 wallMemArr (by decide) (by decide) (by decide))
      (hkeep_arr15 edgeOffArr (by decide) (by decide) (by decide))
      (hkeep_arr15 edgeLenArr (by decide) (by decide) (by decide))
      (hkeep_arr15 edgeU1Arr (by decide) (by decide) (by decide))
      (hkeep_arr15 edgeU2Arr (by decide) (by decide) (by decide))
      (hkeep_arr15 horizEdgeIdxArr (by decide) (by decide) (by decide))
      (hkeep_arr15 vertEdgeIdxArr (by decide) (by decide) (by decide))
  have hbuf₁₅ : IsArrBufPrefix (s₁₅.arrs bufArr2)
      ((pfx ++ [0]) ++ (liftElemSteps W (R.vmap p) (R.inner p q)).map Fin.val) (s₁₅.regs 7) := by
    have h1 : s₁₅.arrs bufArr2 = s₁₂.arrs bufArr2 := by rw [harrs₁₅]; rfl
    have h2 : s₁₅.regs 7 = s₁₂.regs 7 := by
      rw [hregs₁₅ 7 (by decide) (by decide)]; rfl
    rw [h1, h2]
    exact hbuf₁₂
  have hlen₁₅ : (s₁₅.arrs bufArr2).length = (s.arrs bufArr2).length := by
    rw [harrs₁₅]
    exact hlen₁₂.trans hlen₁₁
  rcases appendStepInternalCmd_exec W bufArr2 (by decide)
      hadj_last
      ((pfx ++ [0]) ++ (liftElemSteps W (R.vmap p) (R.inner p q)).map Fin.val)
      (s := s₁₅)
      h2_w hn_w hVJW_w hloc_w henc_w hs₁₅ hbuf₁₅
      (by rw [hlen₁₅]; simp only [List.length_append, List.length_singleton, List.length_map]; omega)
      (by rwa [hlen₁₅])
      (by rw [hregs₁₅ 18 (by decide) (by decide)]; dsimp only [s₁₄, s₁₃]; simpa using hr18_12)
      (by rw [hregs₁₅ 19 (by decide) (by decide)]; dsimp only [s₁₄, s₁₃]; simpa using hr19_12)
      hr20_15 hr21_15 with
    ⟨s₁₆, t_last, hex₁₆, ht_last, hbuf₁₆, hlen₁₆, hregs₁₆, harrs₁₆⟩
  have hbuf₁₆' : IsArrBufPrefix (s₁₆.arrs bufArr2)
      (pfx ++ (0 :: (realizeEdgeInternalVerts W R e').map Fin.val)) (s₁₆.regs 7) := by
    have heq_list :
        ((pfx ++ [0]) ++ (liftElemSteps W (R.vmap p) (R.inner p q)).map Fin.val) ++
          (W.stepInternalVerts ((R.inner p q).getLastD (R.vmap p)) (R.vmap q)).map Fin.val =
        pfx ++ (0 :: (realizeEdgeInternalVerts W R e').map Fin.val) := by
      rw [hrealize_eq, List.map_append]
      simp [List.append_assoc]
    rwa [heq_list] at hbuf₁₆
  have hr25_3 : s₃.regs 25 = pfx.length := by
    rw [hregs₃ 25 (by decide)]
    simp [s₂, s₁]
  have hr25_8 : s₈.regs 25 = pfx.length := by
    rw [hregs₈ 25 (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide)]
    dsimp only [s₇, s₆, s₅, s₄]
    exact hr25_3
  have hr25_11 : s₁₁.regs 25 = pfx.length := by
    rw [hregs₁₁ 25 (by decide) (by decide)]
    dsimp only [s₁₀, s₉]
    exact hr25_8
  have hr25_12 : s₁₂.regs 25 = pfx.length := by
    rw [hregs₁₂ 25 (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide)]
    exact hr25_11
  have hr25_15 : s₁₅.regs 25 = pfx.length := by
    rw [hregs₁₅ 25 (by decide) (by decide)]
    dsimp only [s₁₄, s₁₃]
    exact hr25_12
  have hr25_16 : s₁₆.regs 25 = pfx.length := by
    rw [hregs₁₆ 25 (by decide) (by decide) (by decide) (by decide)]
    exact hr25_15
  have hr7_16 : s₁₆.regs 7 = pfx.length + 1 + (realizeEdgeInternalVerts W R e').length := by
    have := hbuf₁₆'.1
    simp only [List.length_append, List.length_cons, List.length_map] at this
    omega
  have hlen16 : (s₁₆.arrs bufArr2).length = (s.arrs bufArr2).length :=
    hlen₁₆.trans hlen₁₅
  have hr7_w : s₁₆.regs 7 < 2 ^ w := by
    have := hbuf₁₆'.2.1
    rw [← hbuf₁₆'.1, hlen16] at this
    omega
  have hsub1_w : s₁₆.regs 7 - pfx.length < 2 ^ w := by omega
  have hsub2_w : (realizeEdgeInternalVerts W R e').length < 2 ^ w := by omega
  have hsub2_eq : s₁₆.regs 7 - pfx.length - 1 = (realizeEdgeInternalVerts W R e').length := by
    omega
  let s₁₇ := s₁₆.writeArr bufArr2 pfx.length (realizeEdgeInternalVerts W R e').length
  have hex₁₇ : Exec w (.write bufArr2 (.reg 25) (.op .sub (.op .sub (.reg 7) (.reg 25)) (.const 1)))
      s₁₆ s₁₇ 7 :=
    .write (by simp [Expr.eval, checkWord, hr25_16, hpfx_w])
      (by simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hr25_16,
        hr7_w, hpfx_w, hsub1_w, h1_w, hsub2_eq, hsub2_w])
      (by rw [hlen16]; omega)
  have hbuf₁₇ : IsArrBufPrefix (s₁₇.arrs bufArr2)
      (pfx ++ encRealizeEdgeList W R [e']) (s₁₇.regs 7) := by
    have hset := IsArrBufPrefix.write_at_prefix hbuf₁₆' pfx.length
      (realizeEdgeInternalVerts W R e').length
    rw [set_append_cons_self, ← encRealizeEdgeList_singleton] at hset
    dsimp only [s₁₇]
    rw [State.writeArr_arrs_self, State.writeArr_regs]
    exact hset
  have hr34_17 : s₁₇.regs 34 = ecnt := by
    dsimp only [s₁₇]
    rw [State.writeArr_regs,
      hregs₁₆ 34 (by decide) (by decide) (by decide) (by decide),
      hkeep_reg15 34 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide) (by decide), hr34]
  have hecnt0_w : ecnt < 2 ^ w := by omega
  let s₁₈ := s₁₇.setReg 34 (ecnt + 1)
  have hex₁₈ : Exec w (.assign 34 (.op .add (.reg 34) (.const 1))) s₁₇ s₁₈ 4 :=
    .assign (by simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hr34_17,
      hecnt0_w, h1_w, hecnt_w])
  have hbuf₁₈ : IsArrBufPrefix (s₁₈.arrs bufArr2)
      (pfx ++ encRealizeEdgeList W R [e']) (s₁₈.regs 7) := by
    dsimp only [s₁₈]
    rw [State.setReg_arrs, State.setReg_regs_ne _ _ (by decide)]
    exact hbuf₁₇
  have hlen₁₈ : (s₁₈.arrs bufArr2).length = (s.arrs bufArr2).length := by
    dsimp only [s₁₈, s₁₇]
    rw [State.setReg_arrs, State.writeArr_arrs_self, List.length_set]
    exact hlen16
  have hr34_18 : s₁₈.regs 34 = ecnt + 1 := by
    dsimp only [s₁₈]
    exact State.setReg_regs_self _ _ _
  refine ⟨s₁₈,
    2 + (2 + (t_p0 + (2 + (2 + (2 + (2 + (t_in + (2 + (2 + (t_vm1 + (t_steps + (2 + (2 + (t_vm2 + (t_last + (7 + 4)))))))))))))))),
    .seq hex₁ (.seq hex₂ (.seq hex₃ (.seq hex₄ (.seq hex₅ (.seq hex₆ (.seq hex₇ (.seq hex₈
      (.seq hex₉ (.seq hex₁₀ (.seq hex₁₁ (.seq hex₁₂ (.seq hex₁₃ (.seq hex₁₄ (.seq hex₁₅
        (.seq hex₁₆ (.seq hex₁₇ hex₁₈)))))))))))))))),
    by linarith [ht_p0, ht_in, ht_vm1, ht_steps, ht_vm2, ht_last, hlen_in_le, hrealize_len, henc_single_len],
    hbuf₁₈,
    hlen₁₈,
    hr34_18,
    fun r h6 h7 h8 h9 h10 h11 h18 h19 h20 h21 h25 h34 => by
      dsimp only [s₁₈, s₁₇]
      rw [State.setReg_regs_ne _ _ h34, State.writeArr_regs,
        hregs₁₆ r h6 h7 h8 h9, hkeep_reg15 r h6 h7 h8 h9 h10 h11 h18 h19 h20 h21 h25],
    fun a ha1 ha2 ha3 => by
      dsimp only [s₁₈, s₁₇]
      rw [State.setReg_arrs, State.writeArr_arrs_ne _ _ _ ha1,
        harrs₁₆ a ha1, hkeep_arr15 a ha1 ha2 ha3]⟩

attribute [local irreducible] realizeEdgeInternalVerts encRealizeEdgeList

/-- Conditionally append the realized internal vertex list of a single optional edge `extra`
(with `p = (r_26, r_27)` and `q = (e_q1, e_q2)`) to `bufArr2` and increment `r_34`. -/
def condAppendRealizedEdgeCmd (cond e_q1 e_q2 : Expr) : Cmd :=
  .ite cond
    (.seq (.assign 28 e_q1)
      (.seq (.assign 29 e_q2)
        appendRealizedEdgeCmd))
    .skip

theorem condAppendRealizedEdgeCmd_exec {w h' n : ℕ} {G : MultiDigraph n}
    (W : WallOfHeight (h' + 2) G)
    {τ : GM13.Shape (h' + 2) h'} (R : τ.Realization)
    (code : RealizationCode)
    (hvmap : ∀ p, vmapOfCode h' code p = R.vmap p)
    (hinner : ∀ p q, innerOfCode h' code p q = R.inner p q)
    (cond e_q1 e_q2 : Expr)
    (extra : List (Fin (elemWallNumVerts h') × Fin (elemWallNumVerts h')))
    (P : Prop) [Decidable P]
    (pfx : List ℕ) (ecnt : ℕ)
    {s : State}
    (hw4 : 4 < 2 ^ w)
    (hn_w : n < 2 ^ w)
    (hmode_le : code.mode ≤ 3)
    (hY0_w : code.Y0 < 2 ^ w)
    (hc0_w : code.c0 < 2 ^ w)
    (h3h'9_w : 3 * h' + 9 < 2 ^ w)
    (hVJW_w : elemWallNumVerts (h' + 2) + (2 * (h' + 2) + 2) < 2 ^ w)
    (hloc_w : elemWallNumVerts (h' + 2) + (elemWallEdges (h' + 2)).length < 2 ^ w)
    (henc_w : W.encList.length < 2 ^ w)
    (hecnt_w : ecnt + extra.length < 2 ^ w)
    (hcond : cond.eval w s = some (if P then 1 else 0))
    (hextra_eq : ∀ _ : P, ∃ e' : Fin (elemWallNumVerts h') × Fin (elemWallNumVerts h'),
      extra = [e'] ∧ e' ∈ elemWallEdges h' ∧
      s.regs 26 = (elemWallVertCoord h' e'.1).1 ∧
      s.regs 27 = (elemWallVertCoord h' e'.1).2 ∧
      e_q1.eval w s = some (elemWallVertCoord h' e'.2).1 ∧
      (∀ s' : State, s'.regs 26 = s.regs 26 → s'.regs 27 = s.regs 27 →
        e_q2.eval w s' = some (elemWallVertCoord h' e'.2).2))
    (hextra_nil : ¬ P → extra = [])
    (hs : WallStateHolds W s)
    (hr15 : s.regs 15 = code.mode)
    (hr16 : s.regs 16 = code.Y0)
    (hr17 : s.regs 17 = code.c0)
    (hr22 : s.regs 22 = h')
    (hr34 : s.regs 34 = ecnt)
    (hbuf : IsArrBufPrefix (s.arrs bufArr2) pfx (s.regs 7))
    (hcap : pfx.length + (encRealizeEdgeList W R extra).length ≤ (s.arrs bufArr2).length)
    (hbuf_w : (s.arrs bufArr2).length < 2 ^ w) :
    ∃ s' t,
      Exec w (condAppendRealizedEdgeCmd cond e_q1 e_q2) s s' t ∧
      t ≤ cond.cost + e_q1.cost + e_q2.cost + 10 +
        1300 * (encRealizeEdgeList W R extra).length ∧
      IsArrBufPrefix (s'.arrs bufArr2) (pfx ++ encRealizeEdgeList W R extra) (s'.regs 7) ∧
      (s'.arrs bufArr2).length = (s.arrs bufArr2).length ∧
      s'.regs 34 = ecnt + extra.length ∧
      (∀ r : Reg, r ≠ 6 → r ≠ 7 → r ≠ 8 → r ≠ 9 → r ≠ 10 → r ≠ 11 →
        r ≠ 18 → r ≠ 19 → r ≠ 20 → r ≠ 21 → r ≠ 25 → r ≠ 28 → r ≠ 29 → r ≠ 34 →
        s'.regs r = s.regs r) ∧
      (∀ a : Arr, a ≠ bufArr2 → a ≠ coordXArr → a ≠ coordYArr → s'.arrs a = s.arrs a) := by
  by_cases hP : P
  · rcases hextra_eq hP with ⟨e', rfl, he', hr26, hr27, heq1, heq2⟩
    rw [if_pos hP] at hcond
    simp only [List.length_singleton] at hecnt_w
    let s₁ := s.setReg 28 (elemWallVertCoord h' e'.2).1
    have hex₁ : Exec w (.assign 28 e_q1) s s₁ (e_q1.cost + 1) := .assign heq1
    let s₂ := s₁.setReg 29 (elemWallVertCoord h' e'.2).2
    have hex₂ : Exec w (.assign 29 e_q2) s₁ s₂ (e_q2.cost + 1) :=
      .assign (heq2 s₁ (by dsimp only [s₁]; exact State.setReg_regs_ne _ _ (by decide))
        (by dsimp only [s₁]; exact State.setReg_regs_ne _ _ (by decide)))
    have hs₂ : WallStateHolds W s₂ :=
      hs.of_preserve
        (by dsimp only [s₂, s₁]; rfl) (by dsimp only [s₂, s₁]; rfl)
        (by dsimp only [s₂, s₁]; rfl) (by dsimp only [s₂, s₁]; rfl)
        (by dsimp only [s₂, s₁]; rfl)
        rfl rfl rfl rfl rfl rfl rfl rfl rfl
    rcases appendRealizedEdgeCmd_exec W R code hvmap hinner e' he' pfx ecnt (s := s₂)
        hw4 hn_w hmode_le hY0_w hc0_w h3h'9_w hVJW_w hloc_w henc_w hecnt_w
        hs₂
        (by dsimp only [s₂, s₁]; exact hr15)
        (by dsimp only [s₂, s₁]; exact hr16)
        (by dsimp only [s₂, s₁]; exact hr17)
        (by dsimp only [s₂, s₁]; exact hr22)
        (by dsimp only [s₂, s₁]; exact hr26)
        (by dsimp only [s₂, s₁]; exact hr27)
        (by dsimp only [s₂, s₁]; rfl)
        (by dsimp only [s₂]; rfl)
        (by dsimp only [s₂, s₁]; exact hr34)
        (by dsimp only [s₂, s₁]; exact hbuf)
        (by dsimp only [s₂, s₁]; exact hcap)
        (by dsimp only [s₂, s₁]; exact hbuf_w) with
      ⟨s₃, t₃, hex₃, ht₃, hbuf₃, hlen₃, hr34_3, hregs₃, harrs₃⟩
    refine ⟨s₃, cond.cost + ((e_q1.cost + 1) + ((e_q2.cost + 1) + t₃)),
      .ite_true hcond (by omega) (.seq hex₁ (.seq hex₂ hex₃)),
      by omega, hbuf₃, hlen₃, hr34_3,
      fun r h6 h7 h8 h9 h10 h11 h18 h19 h20 h21 h25 h28 h29 h34 => by
        rw [hregs₃ r h6 h7 h8 h9 h10 h11 h18 h19 h20 h21 h25 h34]
        dsimp only [s₂, s₁]
        rw [State.setReg_regs_ne _ _ h29, State.setReg_regs_ne _ _ h28],
      fun a ha1 ha2 ha3 => by
        rw [harrs₃ a ha1 ha2 ha3]
        rfl⟩
  · rw [if_neg hP] at hcond
    rw [hextra_nil hP]
    simp only [encRealizeEdgeList_nil, List.append_nil, List.length_nil, Nat.add_zero]
    exact ⟨s, cond.cost + 1, .ite_false hcond (.skip s), by omega, hbuf, rfl, hr34,
      fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ => rfl, fun _ _ _ _ => rfl⟩

/-- Condition expression `r_26 + 1 < r_30 ∧ r_32 + 1 < r_31` for a horizontal edge in `elementaryWall h'`. -/
def condRealizeHorizExpr : Expr :=
  exprAnd (exprLt (.op .add (.reg 26) (.const 1)) (.reg 30))
    (exprLt (.op .add (.reg 32) (.const 1)) (.reg 31))

/-- Condition expression `r_32 + r_30 < r_31 ∧ (r_26 + r_27) % 2 == 1` for a vertical edge in `elementaryWall h'`. -/
def condRealizeVertExpr : Expr :=
  exprAnd (exprLt (.op .add (.reg 32) (.reg 30)) (.reg 31))
    (exprEq (.op .mod (.op .add (.reg 26) (.reg 27)) (.const 2)) (.const 1))

/-- Loop body of `realizeEdgesLoop`: computes `(xc, yc) = elemWallVertCoord h' r_32` in `(r_26, r_27)`
and appends the realized internal vertex lists of any horizontal and vertical edges from `r_32`. -/
def realizeEdgesBody : Cmd :=
  .seq (.assign 26 (.op .mod (.op .add (.reg 32) (.const 1)) (.reg 30)))
    (.seq (.assign 27 (.op .div (.op .add (.reg 32) (.const 1)) (.reg 30)))
      (.seq (condAppendRealizedEdgeCmd condRealizeHorizExpr
          (.op .add (.reg 26) (.const 1)) (.reg 27))
        (.seq (condAppendRealizedEdgeCmd condRealizeVertExpr
            (.reg 26) (.op .add (.reg 27) (.const 1)))
          (.seq (.assign 32 (.op .add (.reg 32) (.const 1)))
            (.assign 33 (.op .sub (.reg 33) (.const 1)))))))

/-- Loop appending the encoded internal vertex lists of all `E_{J'}` edges of `W.realizeSubwall R`
to `bufArr2` and counting `E_{J'}` in `r_34`. -/
def realizeEdgesLoop : Cmd :=
  .while (.op .lt (.const 0) (.reg 33)) realizeEdgesBody

theorem elemWallVertCoord_horiz_snd (h' idx : ℕ)
    (h1 : (idx + 1) % (2 * h' + 2) + 1 < 2 * h' + 2)
    (h2 : idx + 1 < elemWallNumVerts h') :
    elemWallVertCoord h' ⟨idx + 1, h2⟩ =
      ((idx + 1) % (2 * h' + 2) + 1, (idx + 1) / (2 * h' + 2)) := by
  rw [elemWallVertCoord_eq]
  set B := 2 * h' + 2
  have hB : 0 < B := by omega
  have hdu : B * ((idx + 1) / B) + (idx + 1) % B = idx + 1 := Nat.div_add_mod (idx + 1) B
  have hv1 : idx + 1 + 1 = ((idx + 1) % B + 1) + B * ((idx + 1) / B) := by omega
  have hmod : (idx + 1 + 1) % B = (idx + 1) % B + 1 := by
    rw [hv1, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt h1]
  have hdiv : (idx + 1 + 1) / B = (idx + 1) / B := by
    rw [hv1, Nat.add_mul_div_left _ _ hB, Nat.div_eq_of_lt h1, Nat.zero_add]
  exact Prod.ext hmod hdiv

theorem elemWallVertCoord_vert_snd (h' idx : ℕ)
    (h1 : idx + (2 * h' + 2) < elemWallNumVerts h') :
    elemWallVertCoord h' ⟨idx + (2 * h' + 2), h1⟩ =
      ((idx + 1) % (2 * h' + 2), (idx + 1) / (2 * h' + 2) + 1) := by
  rw [elemWallVertCoord_eq]
  set B := 2 * h' + 2
  have hB : 0 < B := by omega
  have hdu : B * ((idx + 1) / B) + (idx + 1) % B = idx + 1 := Nat.div_add_mod (idx + 1) B
  have hmu : (idx + 1) % B < B := Nat.mod_lt (idx + 1) hB
  have hv1 : idx + B + 1 = (idx + 1) % B + B * ((idx + 1) / B + 1) := by
    rw [Nat.mul_add, Nat.mul_one]; omega
  have hmod : (idx + B + 1) % B = (idx + 1) % B := by
    rw [hv1, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hmu]
  have hdiv : (idx + B + 1) / B = (idx + 1) / B + 1 := by
    rw [hv1, Nat.add_mul_div_left _ _ hB, Nat.div_eq_of_lt hmu, Nat.zero_add]
  exact Prod.ext hmod hdiv

theorem realizeEdgesLoop_exec {w h' n : ℕ} {G : MultiDigraph n}
    (W : WallOfHeight (h' + 2) G)
    {τ : GM13.Shape (h' + 2) h'} (R : τ.Realization)
    (code : RealizationCode)
    (hvmap : ∀ p, vmapOfCode h' code p = R.vmap p)
    (hinner : ∀ p q, innerOfCode h' code p q = R.inner p q)
    (hw4 : 4 < 2 ^ w)
    (hn_w : n < 2 ^ w)
    (hmode_le : code.mode ≤ 3)
    (hY0_w : code.Y0 < 2 ^ w)
    (hc0_w : code.c0 < 2 ^ w)
    (h3h'9_w : 3 * h' + 9 < 2 ^ w)
    (hVJW'_w : elemWallNumVerts h' + (2 * h' + 2) < 2 ^ w)
    (hEJ'_w : (elemWallEdges h').length < 2 ^ w)
    (hVJW_w : elemWallNumVerts (h' + 2) + (2 * (h' + 2) + 2) < 2 ^ w)
    (hloc_w : elemWallNumVerts (h' + 2) + (elemWallEdges (h' + 2)).length < 2 ^ w)
    (henc_w : W.encList.length < 2 ^ w) :
    ∀ (rem idx : ℕ) (_hrem : idx + rem = elemWallNumVerts h') (pfx : List ℕ) {s : State}
      (_hs : WallStateHolds W s)
      (_hr15 : s.regs 15 = code.mode)
      (_hr16 : s.regs 16 = code.Y0)
      (_hr17 : s.regs 17 = code.c0)
      (_hr22 : s.regs 22 = h')
      (_hr30 : s.regs 30 = 2 * h' + 2)
      (_hr31 : s.regs 31 = elemWallNumVerts h')
      (_hr32 : s.regs 32 = idx)
      (_hr33 : s.regs 33 = rem)
      (_hr34 : s.regs 34 = (elemWallEdgesPrefix h' idx).length)
      (_hbuf : IsArrBufPrefix (s.arrs bufArr2)
        (pfx ++ encRealizeEdgeList W R (elemWallEdgesPrefix h' idx))
        (s.regs 7))
      (_hcap : pfx.length + (encRealizeEdgeList W R (elemWallEdges h')).length ≤
        (s.arrs bufArr2).length)
      (_hbuf_w : (s.arrs bufArr2).length < 2 ^ w),
      ∃ s' t,
        Exec w realizeEdgesLoop s s' t ∧
        t ≤ 120 * rem + 1300 * ((encRealizeEdgeList W R (elemWallEdges h')).length -
          (encRealizeEdgeList W R (elemWallEdgesPrefix h' idx)).length) + 3 ∧
        IsArrBufPrefix (s'.arrs bufArr2)
          (pfx ++ encRealizeEdgeList W R (elemWallEdges h'))
          (s'.regs 7) ∧
        (s'.arrs bufArr2).length = (s.arrs bufArr2).length ∧
        s'.regs 34 = (elemWallEdges h').length ∧
        (∀ r : Reg, r ≠ 6 → r ≠ 7 → r ≠ 8 → r ≠ 9 → r ≠ 10 → r ≠ 11 →
          r ≠ 18 → r ≠ 19 → r ≠ 20 → r ≠ 21 → r ≠ 25 → r ≠ 26 → r ≠ 27 →
          r ≠ 28 → r ≠ 29 → r ≠ 32 → r ≠ 33 → r ≠ 34 → s'.regs r = s.regs r) ∧
        (∀ a : Arr, a ≠ bufArr2 → a ≠ coordXArr → a ≠ coordYArr → s'.arrs a = s.arrs a)
  | 0, idx, hrem, pfx, s, _, _, _, _, _, _, _, _, hr33, hr34, hbuf, _, _ => by
    have h0_w : 0 < 2 ^ w := by omega
    have hidx : idx = elemWallNumVerts h' := by omega
    subst hidx
    rw [elemWallEdgesPrefix_full] at hbuf hr34 ⊢
    have hcond : (Expr.op .lt (.const 0) (.reg 33)).eval w s = some 0 := by
      simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hr33, h0_w]
    exact ⟨s, 3, .while_false hcond, by omega, hbuf, rfl, hr34,
      fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ => rfl, fun _ _ _ _ => rfl⟩
  | rem + 1, idx, hrem, pfx, s, hs, hr15, hr16, hr17, hr22, hr30, hr31, hr32, hr33, hr34,
      hbuf, hcap, hbuf_w => by
    have h0_w : 0 < 2 ^ w := by omega
    have h1_w : 1 < 2 ^ w := by omega
    have h2_w : 2 < 2 ^ w := by omega
    let W' := 2 * h' + 2
    let V' := elemWallNumVerts h'
    have hW'_pos : 0 < W' := by dsimp [W']; omega
    have hW'_w : W' < 2 ^ w := by dsimp [W']; omega
    have hV'_w : V' < 2 ^ w := by dsimp [V']; omega
    have hidx_lt : idx < V' := by dsimp [V']; omega
    have hidx_w : idx < 2 ^ w := by omega
    have hidx1_w : idx + 1 < 2 ^ w := by omega
    have hidxW'_w : idx + W' < 2 ^ w := by dsimp [W', V'] at *; omega
    have hrem_w : rem + 1 < 2 ^ w := by omega
    have hrem0_w : rem < 2 ^ w := by omega
    let xc := (idx + 1) % W'
    let yc := (idx + 1) / W'
    have hxc_lt : xc < W' := Nat.mod_lt _ hW'_pos
    have hxc_w : xc < 2 ^ w := by omega
    have hxc1_w : xc + 1 < 2 ^ w := by omega
    have hyc_le : yc ≤ idx + 1 := Nat.div_le_self (idx + 1) W'
    have hyc_w : yc < 2 ^ w := by omega
    have hyc1_w : yc + 1 < 2 ^ w := by dsimp [W', V'] at *; omega
    have hxcy_w : xc + yc < 2 ^ w := by dsimp [W', V'] at *; omega
    have hmod2_lt : (xc + yc) % 2 < 2 := Nat.mod_lt _ (by omega)
    have hmod2_w : (xc + yc) % 2 < 2 ^ w := by omega
    have hp_eq : elemWallVertCoord h' ⟨idx, hidx_lt⟩ = (xc, yc) :=
      elemWallVertCoord_eq h' ⟨idx, hidx_lt⟩
    have hp1_eq : (elemWallVertCoord h' ⟨idx, hidx_lt⟩).1 = xc := congrArg Prod.fst hp_eq
    have hp2_eq : (elemWallVertCoord h' ⟨idx, hidx_lt⟩).2 = yc := congrArg Prod.snd hp_eq
    have hcond : (Expr.op .lt (.const 0) (.reg 33)).eval w s = some 1 := by
      simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hr33, h0_w, h1_w, hrem_w]
    let s₁ := s.setReg 26 xc
    have hex₁ : Exec w (.assign 26 (.op .mod (.op .add (.reg 32) (.const 1)) (.reg 30))) s s₁ 6 :=
      .assign (by simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hr32, hr30,
        hidx_w, h1_w, hidx1_w, hW'_w, hxc_w, xc, W'])
    let s₂ := s₁.setReg 27 yc
    have hex₂ : Exec w (.assign 27 (.op .div (.op .add (.reg 32) (.const 1)) (.reg 30))) s₁ s₂ 6 :=
      .assign (by simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, s₁, hr32, hr30,
        hidx_w, h1_w, hidx1_w, hW'_w, hyc_w, yc, W'])
    have hprefix_succ := elemWallEdgesPrefix_succ h' idx
    have hprefix_le_full :
        (elemWallEdgesPrefix h' (idx + 1)).length ≤ (elemWallEdges h').length := by
      rw [← elemWallEdgesPrefix_full h']
      exact elemWallEdgesPrefix_length_mono h' (by omega)
    have hhoriz_cnt_w :
        (elemWallEdgesPrefix h' idx).length + (elemWallHorizEdge h' idx).length < 2 ^ w := by
      have := hprefix_le_full
      rw [hprefix_succ, List.length_append, List.length_append] at this
      omega
    have hvert_cnt_w :
        ((elemWallEdgesPrefix h' idx ++ elemWallHorizEdge h' idx).length) +
          (elemWallVertEdge h' idx).length < 2 ^ w := by
      have := hprefix_le_full
      rw [hprefix_succ, List.length_append] at this
      omega
    have henc_succ := encRealizeEdgeList_prefix_succ W R idx
    have henc_le_full :
        (encRealizeEdgeList W R (elemWallEdgesPrefix h' (idx + 1))).length ≤
          (encRealizeEdgeList W R (elemWallEdges h')).length := by
      rw [← elemWallEdgesPrefix_full h']
      exact encRealizeEdgeList_prefix_length_mono W R (by omega)
    have hcap_horiz :
        (pfx ++ encRealizeEdgeList W R (elemWallEdgesPrefix h' idx)).length +
          (encRealizeEdgeList W R (elemWallHorizEdge h' idx)).length ≤
          (s.arrs bufArr2).length := by
      have := henc_le_full
      rw [henc_succ] at this
      simp only [List.length_append] at this ⊢
      omega
    have he_h1 : (Expr.op .add (.reg 26) (.const 1)).eval w s₂ = some (xc + 1) := by
      simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, s₂, s₁, hxc_w, h1_w, hxc1_w]
    have he_h2 : (Expr.reg 30).eval w s₂ = some W' := by
      simp [Expr.eval, checkWord, s₂, s₁, hr30, hW'_w, W']
    have he_h3 : (Expr.op .add (.reg 32) (.const 1)).eval w s₂ = some (idx + 1) := by
      simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, s₂, s₁, hr32, hidx_w, h1_w, hidx1_w]
    have he_h4 : (Expr.reg 31).eval w s₂ = some V' := by
      simp [Expr.eval, checkWord, s₂, s₁, hr31, hV'_w, V']
    have hcondHoriz :
        condRealizeHorizExpr.eval w s₂ = some (if xc + 1 < W' ∧ idx + 1 < V' then 1 else 0) := by
      unfold condRealizeHorizExpr
      rw [eval_exprAnd h1_w (eval_exprLt h1_w he_h1 he_h2) (eval_exprLt h1_w he_h3 he_h4)]
    have hs₂ : WallStateHolds W s₂ :=
      hs.of_preserve rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl
    rcases condAppendRealizedEdgeCmd_exec W R code hvmap hinner
        condRealizeHorizExpr (.op .add (.reg 26) (.const 1)) (.reg 27)
        (elemWallHorizEdge h' idx) (xc + 1 < W' ∧ idx + 1 < V')
        (pfx ++ encRealizeEdgeList W R (elemWallEdgesPrefix h' idx))
        (elemWallEdgesPrefix h' idx).length (s := s₂)
        hw4 hn_w hmode_le hY0_w hc0_w h3h'9_w hVJW_w hloc_w henc_w hhoriz_cnt_w
        hcondHoriz
        (fun hP => by
          let e' : Fin (elemWallNumVerts h') × Fin (elemWallNumVerts h') :=
            (⟨idx, hidx_lt⟩, ⟨idx + 1, hP.2⟩)
          have hextra : elemWallHorizEdge h' idx = [e'] := dif_pos hP
          have he'_mem : e' ∈ elemWallEdges h' := by
            apply mem_elemWallEdges_of_mem_prefix (u := idx + 1) (by omega)
            rw [hprefix_succ, hextra]
            simp
          have hq_eq := elemWallVertCoord_horiz_snd h' idx hP.1 hP.2
          have hq1_eq : (elemWallVertCoord h' e'.2).1 = xc + 1 := congrArg Prod.fst hq_eq
          have hq2_eq : (elemWallVertCoord h' e'.2).2 = yc := congrArg Prod.snd hq_eq
          refine ⟨e', hextra, he'_mem,
            by dsimp only [s₂, s₁, e']; rw [hp1_eq]; rfl,
            by dsimp only [s₂, s₁, e']; rw [hp2_eq]; rfl,
            by rw [hq1_eq]; exact he_h1,
            fun s' _ hs27 => by
              rw [hq2_eq]
              have h27 : s'.regs 27 = yc := by rw [hs27]; rfl
              simp [Expr.eval, checkWord, h27, hyc_w]⟩)
        (fun hP => dif_neg hP)
        hs₂
        (by dsimp only [s₂, s₁]; exact hr15)
        (by dsimp only [s₂, s₁]; exact hr16)
        (by dsimp only [s₂, s₁]; exact hr17)
        (by dsimp only [s₂, s₁]; exact hr22)
        (by dsimp only [s₂, s₁]; exact hr34)
        (by dsimp only [s₂, s₁]; exact hbuf)
        (by dsimp only [s₂, s₁]; exact hcap_horiz)
        (by dsimp only [s₂, s₁]; exact hbuf_w) with
      ⟨s₃, t_h, hex₃, ht_h, hbuf₃, hlen₃, hr34_3, hregs₃, harrs₃⟩
    have hr34_3' : s₃.regs 34 = (elemWallEdgesPrefix h' idx ++ elemWallHorizEdge h' idx).length := by
      rw [List.length_append]; exact hr34_3
    have hbuf₃' : IsArrBufPrefix (s₃.arrs bufArr2)
        (pfx ++ encRealizeEdgeList W R (elemWallEdgesPrefix h' idx ++ elemWallHorizEdge h' idx))
        (s₃.regs 7) := by
      rwa [encRealizeEdgeList_append, ← List.append_assoc]
    have hkeep_reg3 : ∀ r : Reg, r ≠ 6 → r ≠ 7 → r ≠ 8 → r ≠ 9 → r ≠ 10 → r ≠ 11 →
        r ≠ 18 → r ≠ 19 → r ≠ 20 → r ≠ 21 → r ≠ 25 → r ≠ 26 → r ≠ 27 →
        r ≠ 28 → r ≠ 29 → r ≠ 34 → s₃.regs r = s.regs r := by
      intro r h6 h7 h8 h9 h10 h11 h18 h19 h20 h21 h25 h26 h27 h28 h29 h34
      rw [hregs₃ r h6 h7 h8 h9 h10 h11 h18 h19 h20 h21 h25 h28 h29 h34]
      dsimp only [s₂, s₁]
      rw [State.setReg_regs_ne _ _ h27, State.setReg_regs_ne _ _ h26]
    have hr26_3 : s₃.regs 26 = xc := by
      rw [hregs₃ 26 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]
      rfl
    have hr27_3 : s₃.regs 27 = yc := by
      rw [hregs₃ 27 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]
      rfl
    have hr30_3 : s₃.regs 30 = W' := by
      rw [hkeep_reg3 30 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide)]
      exact hr30
    have hr31_3 : s₃.regs 31 = V' := by
      rw [hkeep_reg3 31 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide)]
      exact hr31
    have hr32_3 : s₃.regs 32 = idx := by
      rw [hkeep_reg3 32 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide)]
      exact hr32
    have he_v1 : (Expr.op .add (.reg 32) (.reg 30)).eval w s₃ = some (idx + W') := by
      simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hr32_3, hr30_3, hidx_w, hW'_w, hidxW'_w]
    have he_v2 : (Expr.reg 31).eval w s₃ = some V' := by
      simp [Expr.eval, checkWord, hr31_3, hV'_w]
    have he_v3 : (Expr.op .mod (.op .add (.reg 26) (.reg 27)) (.const 2)).eval w s₃ =
        some ((xc + yc) % 2) := by
      simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hr26_3, hr27_3,
        hxc_w, hyc_w, hxcy_w, h2_w, hmod2_w]
    have he_v4 : (Expr.const 1).eval w s₃ = some 1 := by
      simp [Expr.eval, checkWord, h1_w]
    have hcondVert :
        condRealizeVertExpr.eval w s₃ =
          some (if idx + W' < V' ∧ (xc + yc) % 2 = 1 then 1 else 0) := by
      unfold condRealizeVertExpr
      rw [eval_exprAnd h1_w (eval_exprLt h1_w he_v1 he_v2) (eval_exprEq h1_w he_v3 he_v4)]
    have hs₃ : WallStateHolds W s₃ :=
      hs.of_preserve
        (hkeep_reg3 0 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))
        (hkeep_reg3 3 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))
        (hkeep_reg3 12 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))
        (hkeep_reg3 13 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))
        (hkeep_reg3 14 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))
        (harrs₃ wallEncArr (by decide) (by decide) (by decide))
        (harrs₃ locArr (by decide) (by decide) (by decide))
        (harrs₃ wallMemArr (by decide) (by decide) (by decide))
        (harrs₃ edgeOffArr (by decide) (by decide) (by decide))
        (harrs₃ edgeLenArr (by decide) (by decide) (by decide))
        (harrs₃ edgeU1Arr (by decide) (by decide) (by decide))
        (harrs₃ edgeU2Arr (by decide) (by decide) (by decide))
        (harrs₃ horizEdgeIdxArr (by decide) (by decide) (by decide))
        (harrs₃ vertEdgeIdxArr (by decide) (by decide) (by decide))
    have hcap_vert :
        (pfx ++ encRealizeEdgeList W R
            (elemWallEdgesPrefix h' idx ++ elemWallHorizEdge h' idx)).length +
          (encRealizeEdgeList W R (elemWallVertEdge h' idx)).length ≤
          (s₃.arrs bufArr2).length := by
      have := henc_le_full
      rw [henc_succ] at this
      rw [encRealizeEdgeList_append, hlen₃]
      dsimp only [s₂, s₁]
      simp only [State.setReg_arrs, List.length_append] at this ⊢
      omega
    rcases condAppendRealizedEdgeCmd_exec W R code hvmap hinner
        condRealizeVertExpr (.reg 26) (.op .add (.reg 27) (.const 1))
        (elemWallVertEdge h' idx) (idx + W' < V' ∧ (xc + yc) % 2 = 1)
        (pfx ++ encRealizeEdgeList W R (elemWallEdgesPrefix h' idx ++ elemWallHorizEdge h' idx))
        (elemWallEdgesPrefix h' idx ++ elemWallHorizEdge h' idx).length (s := s₃)
        hw4 hn_w hmode_le hY0_w hc0_w h3h'9_w hVJW_w hloc_w henc_w hvert_cnt_w
        hcondVert
        (fun hP => by
          let e' : Fin (elemWallNumVerts h') × Fin (elemWallNumVerts h') :=
            (⟨idx, hidx_lt⟩, ⟨idx + W', hP.1⟩)
          have hextra : elemWallVertEdge h' idx = [e'] := dif_pos hP
          have he'_mem : e' ∈ elemWallEdges h' := by
            apply mem_elemWallEdges_of_mem_prefix (u := idx + 1) (by omega)
            rw [hprefix_succ, hextra]
            simp
          have hq_eq := elemWallVertCoord_vert_snd h' idx hP.1
          have hq1_eq : (elemWallVertCoord h' e'.2).1 = xc := congrArg Prod.fst hq_eq
          have hq2_eq : (elemWallVertCoord h' e'.2).2 = yc + 1 := congrArg Prod.snd hq_eq
          refine ⟨e', hextra, he'_mem,
            by dsimp only [e']; rw [hp1_eq]; exact hr26_3,
            by dsimp only [e']; rw [hp2_eq]; exact hr27_3,
            by rw [hq1_eq]; simp [Expr.eval, checkWord, hr26_3, hxc_w],
            fun s' _ hs27 => by
              rw [hq2_eq]
              have h27 : s'.regs 27 = yc := by rw [hs27, hr27_3]
              simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, h27, hyc_w, h1_w, hyc1_w]⟩)
        (fun hP => dif_neg hP)
        hs₃
        (by rw [hkeep_reg3 15 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]; exact hr15)
        (by rw [hkeep_reg3 16 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]; exact hr16)
        (by rw [hkeep_reg3 17 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]; exact hr17)
        (by rw [hkeep_reg3 22 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]; exact hr22)
        hr34_3' hbuf₃' hcap_vert (by rw [hlen₃]; exact hbuf_w) with
      ⟨s₄, t_v, hex₄, ht_v, hbuf₄, hlen₄, hr34_4, hregs₄, harrs₄⟩
    have hbuf₄' : IsArrBufPrefix (s₄.arrs bufArr2)
        (pfx ++ encRealizeEdgeList W R (elemWallEdgesPrefix h' (idx + 1)))
        (s₄.regs 7) := by
      rwa [henc_succ, ← encRealizeEdgeList_append, ← List.append_assoc]
    have hr34_4' : s₄.regs 34 = (elemWallEdgesPrefix h' (idx + 1)).length := by
      rw [hprefix_succ, List.length_append]
      exact hr34_4
    have hkeep_reg4 : ∀ r : Reg, r ≠ 6 → r ≠ 7 → r ≠ 8 → r ≠ 9 → r ≠ 10 → r ≠ 11 →
        r ≠ 18 → r ≠ 19 → r ≠ 20 → r ≠ 21 → r ≠ 25 → r ≠ 26 → r ≠ 27 →
        r ≠ 28 → r ≠ 29 → r ≠ 34 → s₄.regs r = s.regs r := by
      intro r h6 h7 h8 h9 h10 h11 h18 h19 h20 h21 h25 h26 h27 h28 h29 h34
      rw [hregs₄ r h6 h7 h8 h9 h10 h11 h18 h19 h20 h21 h25 h28 h29 h34,
        hkeep_reg3 r h6 h7 h8 h9 h10 h11 h18 h19 h20 h21 h25 h26 h27 h28 h29 h34]
    have hkeep_arr4 : ∀ a : Arr, a ≠ bufArr2 → a ≠ coordXArr → a ≠ coordYArr →
        s₄.arrs a = s.arrs a := by
      intro a ha1 ha2 ha3
      rw [harrs₄ a ha1 ha2 ha3, harrs₃ a ha1 ha2 ha3]
      rfl
    have hr32_4 : s₄.regs 32 = idx := by
      rw [hkeep_reg4 32 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide)]
      exact hr32
    have hr33_4 : s₄.regs 33 = rem + 1 := by
      rw [hkeep_reg4 33 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide)]
      exact hr33
    let s₅ := s₄.setReg 32 (idx + 1)
    have hex₅ : Exec w (.assign 32 (.op .add (.reg 32) (.const 1))) s₄ s₅ 4 :=
      .assign (by simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hr32_4, hidx_w, h1_w, hidx1_w])
    let s₆ := s₅.setReg 33 rem
    have hex₆ : Exec w (.assign 33 (.op .sub (.reg 33) (.const 1))) s₅ s₆ 4 :=
      .assign (by simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, s₅, hr33_4,
        hrem_w, h1_w, hrem0_w])
    have hex_body : Exec w realizeEdgesBody s s₆ (6 + (6 + (t_h + (t_v + (4 + 4))))) :=
      .seq hex₁ (.seq hex₂ (.seq hex₃ (.seq hex₄ (.seq hex₅ hex₆))))
    have hkeep_reg6 : ∀ r : Reg, r ≠ 6 → r ≠ 7 → r ≠ 8 → r ≠ 9 → r ≠ 10 → r ≠ 11 →
        r ≠ 18 → r ≠ 19 → r ≠ 20 → r ≠ 21 → r ≠ 25 → r ≠ 26 → r ≠ 27 →
        r ≠ 28 → r ≠ 29 → r ≠ 32 → r ≠ 33 → r ≠ 34 → s₆.regs r = s.regs r := by
      intro r h6 h7 h8 h9 h10 h11 h18 h19 h20 h21 h25 h26 h27 h28 h29 h32 h33 h34
      dsimp only [s₆, s₅]
      rw [State.setReg_regs_ne _ _ h33, State.setReg_regs_ne _ _ h32]
      exact hkeep_reg4 r h6 h7 h8 h9 h10 h11 h18 h19 h20 h21 h25 h26 h27 h28 h29 h34
    have hkeep_arr6 : ∀ a : Arr, a ≠ bufArr2 → a ≠ coordXArr → a ≠ coordYArr →
        s₆.arrs a = s.arrs a := by
      intro a ha1 ha2 ha3
      dsimp only [s₆, s₅]
      rw [State.setReg_arrs, State.setReg_arrs]
      exact hkeep_arr4 a ha1 ha2 ha3
    have hs₆ : WallStateHolds W s₆ :=
      hs.of_preserve
        (hkeep_reg6 0 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))
        (hkeep_reg6 3 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))
        (hkeep_reg6 12 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))
        (hkeep_reg6 13 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))
        (hkeep_reg6 14 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))
        (hkeep_arr6 wallEncArr (by decide) (by decide) (by decide))
        (hkeep_arr6 locArr (by decide) (by decide) (by decide))
        (hkeep_arr6 wallMemArr (by decide) (by decide) (by decide))
        (hkeep_arr6 edgeOffArr (by decide) (by decide) (by decide))
        (hkeep_arr6 edgeLenArr (by decide) (by decide) (by decide))
        (hkeep_arr6 edgeU1Arr (by decide) (by decide) (by decide))
        (hkeep_arr6 edgeU2Arr (by decide) (by decide) (by decide))
        (hkeep_arr6 horizEdgeIdxArr (by decide) (by decide) (by decide))
        (hkeep_arr6 vertEdgeIdxArr (by decide) (by decide) (by decide))
    have hlen₆ : (s₆.arrs bufArr2).length = (s.arrs bufArr2).length := by
      dsimp only [s₆, s₅]
      rw [State.setReg_arrs, State.setReg_arrs, hlen₄, hlen₃]
      rfl
    rcases realizeEdgesLoop_exec W R code hvmap hinner hw4 hn_w hmode_le hY0_w hc0_w
        h3h'9_w hVJW'_w hEJ'_w hVJW_w hloc_w henc_w rem (idx + 1) (by omega) pfx (s := s₆)
        hs₆
        (by rw [hkeep_reg6 15 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), hr15])
        (by rw [hkeep_reg6 16 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), hr16])
        (by rw [hkeep_reg6 17 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), hr17])
        (by rw [hkeep_reg6 22 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), hr22])
        (by rw [hkeep_reg6 30 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), hr30])
        (by rw [hkeep_reg6 31 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), hr31])
        (by dsimp only [s₆, s₅]; simp) (by dsimp only [s₆]; simp)
        (by dsimp only [s₆, s₅]; simpa using hr34_4')
        (by dsimp only [s₆, s₅]; simpa using hbuf₄')
        (by rwa [hlen₆]) (by rwa [hlen₆]) with
      ⟨s', t_rest, hex_rest, ht_rest, hbuf', hlen', hr34', hregs', harrs'⟩
    have hc_h : condRealizeHorizExpr.cost +
        (Expr.op .add (.reg 26) (.const 1)).cost + (Expr.reg 27).cost + 10 ≤ 40 := by decide
    have hc_v : condRealizeVertExpr.cost +
        (Expr.reg 26).cost + (Expr.op .add (.reg 27) (.const 1)).cost + 10 ≤ 50 := by decide
    have henc_len_succ :
        (encRealizeEdgeList W R (elemWallEdgesPrefix h' (idx + 1))).length =
          (encRealizeEdgeList W R (elemWallEdgesPrefix h' idx)).length +
          (encRealizeEdgeList W R (elemWallHorizEdge h' idx)).length +
          (encRealizeEdgeList W R (elemWallVertEdge h' idx)).length := by
      rw [henc_succ, List.length_append, List.length_append]
    have ht_bound :
        3 + (6 + (6 + (t_h + (t_v + (4 + 4))))) + t_rest ≤
          120 * (rem + 1) + 1300 * ((encRealizeEdgeList W R (elemWallEdges h')).length -
            (encRealizeEdgeList W R (elemWallEdgesPrefix h' idx)).length) + 3 := by
      omega
    refine ⟨s', 3 + (6 + (6 + (t_h + (t_v + (4 + 4))))) + t_rest,
      .while_true hcond (by omega) hex_body hex_rest,
      ht_bound, hbuf', hlen'.trans hlen₆, hr34',
      fun r h6 h7 h8 h9 h10 h11 h18 h19 h20 h21 h25 h26 h27 h28 h29 h32 h33 h34 => by
        rw [hregs' r h6 h7 h8 h9 h10 h11 h18 h19 h20 h21 h25 h26 h27 h28 h29 h32 h33 h34,
          hkeep_reg6 r h6 h7 h8 h9 h10 h11 h18 h19 h20 h21 h25 h26 h27 h28 h29 h32 h33 h34],
      fun a ha1 ha2 ha3 => by
        rw [harrs' a ha1 ha2 ha3, hkeep_arr6 a ha1 ha2 ha3]⟩

theorem forall_mem_encInternalSlice_lt {w h n : ℕ} {G : MultiDigraph n}
    (W : WallOfHeight h G) (hn_w : n < 2 ^ w) :
    ∀ (ks : List (Fin (elemWallEdges h).length))
      (_hslice_w : (encInternalSlice W ks).length < 2 ^ w),
      ∀ v ∈ encInternalSlice W ks, v < 2 ^ w
  | [], _, v, hv => by simp [encInternalSlice] at hv
  | k :: rest, hslice_w, v, hv => by
    rw [encInternalSlice_cons] at hslice_w hv
    simp only [List.length_append, List.length_cons, List.length_map] at hslice_w
    rcases List.mem_append.mp hv with hv_head | hv_rest
    · rcases List.mem_cons.mp hv_head with rfl | hv_map
      · omega
      · rcases List.mem_map.mp hv_map with ⟨x, _, rfl⟩
        exact Nat.lt_trans x.2 hn_w
    · exact forall_mem_encInternalSlice_lt W hn_w rest (by omega) v hv_rest

theorem forall_mem_wallEncList_lt {w h n : ℕ} {G : MultiDigraph n}
    (W : WallOfHeight h G)
    (hh_w : h < 2 ^ w)
    (hVJ_w : elemWallNumVerts h < 2 ^ w)
    (hEJ_w : (elemWallEdges h).length < 2 ^ w)
    (hn_w : n < 2 ^ w)
    (henc_w : W.encList.length < 2 ^ w) :
    ∀ v ∈ W.encList, v < 2 ^ w := by
  intro v hv
  rw [wallEncList_eq_append_encInternalSlice] at hv henc_w
  simp only [List.length_append] at henc_w
  rcases List.mem_append.mp hv with hv_pre | hv_slice
  · rcases List.mem_append.mp hv_pre with hv_hdr | hv_br
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hv_hdr
      rcases hv_hdr with rfl | rfl | rfl <;> omega
    · rcases List.mem_map.mp hv_br with ⟨u, _, rfl⟩
      exact Nat.lt_trans (W.branchVert u).2 hn_w
  · exact forall_mem_encInternalSlice_lt W hn_w _ (by omega) v hv_slice

/-- First half of `realizeSubwallCmd`: initializes `r_30 := 2 * h' + 2`, `r_31 := elemWallNumVerts h'`,
allocates `bufArr2` of size `3 + 3 * n`, pushes header `[h', elemWallNumVerts h', 0]`, and runs
`realizeBranchVertsLoop`. -/
def realizeSubwallInitAndBranchCmd : Cmd :=
  .seq (.assign 30 (.op .add (.op .mul (.const 2) (.reg 22)) (.const 2)))
  (.seq (.assign 31 (.op .sub (.op .mul (.op .add (.reg 22) (.const 1)) (.reg 30)) (.const 2)))
  (.seq (initBufCmd bufArr2 7 (.op .add (.const 3) (.op .mul (.const 3) (.reg 0))))
  (.seq (.assign 6 (.reg 22))
  (.seq (pushBuf6Cmd bufArr2)
  (.seq (.assign 6 (.reg 31))
  (.seq (pushBuf6Cmd bufArr2)
  (.seq (.assign 6 (.const 0))
  (.seq (pushBuf6Cmd bufArr2)
  (.seq (.assign 32 (.const 0))
  (.seq (.assign 33 (.reg 31))
    realizeBranchVertsLoop))))))))))

theorem realizeSubwallInitAndBranchCmd_exec {w h' n : ℕ} {G : MultiDigraph n}
    (W : WallOfHeight (h' + 2) G)
    {τ : GM13.Shape (h' + 2) h'} (R : τ.Realization)
    (code : RealizationCode)
    (hvmap : ∀ p, vmapOfCode h' code p = R.vmap p)
    (h2' : 2 ≤ h') (_he' : Even h') (hW : W.IsValid)
    {s : State}
    (hw4 : 4 < 2 ^ w)
    (hn_w : n < 2 ^ w)
    (hcap_w : 3 + 3 * n < 2 ^ w)
    (hmode_le : code.mode ≤ 3)
    (hY0_w : code.Y0 < 2 ^ w)
    (hc0_w : code.c0 < 2 ^ w)
    (h3h'9_w : 3 * h' + 9 < 2 ^ w)
    (hVJW_w : elemWallNumVerts (h' + 2) + (2 * (h' + 2) + 2) < 2 ^ w)
    (henc_w : W.encList.length < 2 ^ w)
    (hs : WallStateHolds W s)
    (hr15 : s.regs 15 = code.mode)
    (hr16 : s.regs 16 = code.Y0)
    (hr17 : s.regs 17 = code.c0)
    (hr22 : s.regs 22 = h') :
    ∃ s' t,
      Exec w realizeSubwallInitAndBranchCmd s s' t ∧
      t ≤ 3 * n + 260 * elemWallNumVerts h' + 70 ∧
      WallStateHolds W s' ∧
      IsArrBufPrefix (s'.arrs bufArr2)
        ([h', elemWallNumVerts h', 0] ++
          (List.finRange (elemWallNumVerts h')).map
            (fun u' => ((W.realizeSubwall R).branchVert u').1))
        (s'.regs 7) ∧
      (s'.arrs bufArr2).length = 3 + 3 * n ∧
      s'.regs 30 = 2 * h' + 2 ∧
      s'.regs 31 = elemWallNumVerts h' ∧
      (∀ r : Reg, r ≠ 6 → r ≠ 7 → r ≠ 8 → r ≠ 9 → r ≠ 18 → r ≠ 19 →
        r ≠ 30 → r ≠ 31 → r ≠ 32 → r ≠ 33 → s'.regs r = s.regs r) ∧
      (∀ a : Arr, a ≠ bufArr2 → s'.arrs a = s.arrs a) := by
  have h0_w : 0 < 2 ^ w := by omega
  have h1_w : 1 < 2 ^ w := by omega
  have h2_w : 2 < 2 ^ w := by omega
  have h3_w : 3 < 2 ^ w := by omega
  have hW'_valid : (W.realizeSubwall R).IsValid := W.realizeSubwall_isValid R hW
  have henc'_le : (W.realizeSubwall R).encList.length ≤ 3 + 3 * n :=
    (W.realizeSubwall R).length_encList_le hW'_valid
  have h3V'_le_enc' : 3 + elemWallNumVerts h' ≤ (W.realizeSubwall R).encList.length := by
    rw [wallEncList_eq_append_encInternalSlice]; simp; omega
  have h3V'_le_cap : 3 + elemWallNumVerts h' ≤ 3 + 3 * n := le_trans h3V'_le_enc' henc'_le
  let W' := 2 * h' + 2
  let V' := elemWallNumVerts h'
  have hh'_w : h' < 2 ^ w := by omega
  have hh'1_w : h' + 1 < 2 ^ w := by omega
  have h2h'_w : 2 * h' < 2 ^ w := by omega
  have hW'_w : W' < 2 ^ w := by dsimp [W']; omega
  have hV'_eq : V' = (h' + 1) * W' - 2 := elemWallNumVerts_eq h'
  have hprod_ge2 : 2 ≤ (h' + 1) * W' := by dsimp [W']; nlinarith
  have hprod_eq : (h' + 1) * W' = V' + 2 := by omega
  have hV'_w : V' < 2 ^ w := by dsimp [V'] at *; omega
  have hprod_w : (h' + 1) * W' < 2 ^ w := by omega
  have h3n_w : 3 * n < 2 ^ w := by omega
  let s₁ := s.setReg 30 W'
  have hex₁ : Exec w (.assign 30 (.op .add (.op .mul (.const 2) (.reg 22)) (.const 2))) s s₁ 6 :=
    .assign (by simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hr22,
      h2_w, hh'_w, h2h'_w, hW'_w, W'])
  let s₂ := s₁.setReg 31 V'
  have hex₂ : Exec w
      (.assign 31 (.op .sub (.op .mul (.op .add (.reg 22) (.const 1)) (.reg 30)) (.const 2)))
      s₁ s₂ 8 :=
    .assign (by simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, s₁, hr22,
      hh'_w, h1_w, hh'1_w, hW'_w, hprod_w, h2_w, ← hV'_eq, hV'_w])
  rcases initBufCmd_exec bufArr2 7 (.op .add (.const 3) (.op .mul (.const 3) (.reg 0)))
      (3 + 3 * n) (s := s₂) h0_w
      (by simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, s₂, s₁, hs.hr0,
        h3_w, hn_w, h3n_w, hcap_w]) with
    ⟨s₃, t_init, hex₃, ht_init, hbuf₃_raw, hregs₃, harrs₃⟩
  have hbuf₃ : IsArrBufPrefix (s₃.arrs bufArr2) [] (s₃.regs 7) :=
    isArrBufPrefix_iff_isBufPrefix.mpr (hbuf₃_raw.1.symm ▸ hbuf₃_raw)
  have hlen₃ : (s₃.arrs bufArr2).length = 3 + 3 * n := hbuf₃_raw.1
  have hr22_3 : s₃.regs 22 = h' := by
    rw [hregs₃ 22 (by decide)]; dsimp only [s₂, s₁]; simp [hr22]
  let s₄ := s₃.setReg 6 h'
  have hex₄ : Exec w (.assign 6 (.reg 22)) s₃ s₄ 2 :=
    .assign (by simp [Expr.eval, checkWord, hr22_3, hh'_w])
  rcases pushBuf6Cmd_exec bufArr2 h' (s := s₄) h1_w hh'_w
      (by dsimp only [s₄]; rw [State.setReg_arrs, hlen₃]; exact hcap_w)
      (by dsimp only [s₄]; exact hbuf₃)
      (by dsimp only [s₄]; rw [State.setReg_arrs, hlen₃]; simp)
      rfl with
    ⟨s₅, t_p1, hex₅, ht_p1, hbuf₅, hlen₅, hregs₅, harrs₅⟩
  have hlen₅' : (s₅.arrs bufArr2).length = 3 + 3 * n := by
    rw [hlen₅]; dsimp only [s₄]; exact hlen₃
  have hr31_5 : s₅.regs 31 = V' := by
    rw [hregs₅ 31 (by decide)]; dsimp only [s₄]; rw [State.setReg_regs_ne _ _ (by decide),
      hregs₃ 31 (by decide)]; dsimp only [s₂]; rfl
  let s₆ := s₅.setReg 6 V'
  have hex₆ : Exec w (.assign 6 (.reg 31)) s₅ s₆ 2 :=
    .assign (by simp [Expr.eval, checkWord, hr31_5, hV'_w])
  rcases pushBuf6Cmd_exec bufArr2 V' (s := s₆) h1_w hV'_w
      (by dsimp only [s₆]; rw [State.setReg_arrs, hlen₅']; exact hcap_w)
      (by dsimp only [s₆]; exact hbuf₅)
      (by dsimp only [s₆]; rw [State.setReg_arrs, hlen₅']; simp; omega)
      rfl with
    ⟨s₇, t_p2, hex₇, ht_p2, hbuf₇, hlen₇, hregs₇, harrs₇⟩
  have hlen₇' : (s₇.arrs bufArr2).length = 3 + 3 * n := by
    rw [hlen₇]; dsimp only [s₆]; exact hlen₅'
  let s₈ := s₇.setReg 6 0
  have hex₈ : Exec w (.assign 6 (.const 0)) s₇ s₈ 2 :=
    .assign (by simp [Expr.eval, checkWord, h0_w])
  rcases pushBuf6Cmd_exec bufArr2 0 (s := s₈) h1_w h0_w
      (by dsimp only [s₈]; rw [State.setReg_arrs, hlen₇']; exact hcap_w)
      (by dsimp only [s₈]; exact hbuf₇)
      (by dsimp only [s₈]; rw [State.setReg_arrs, hlen₇']; simp; omega)
      rfl with
    ⟨s₉, t_p3, hex₉, ht_p3, hbuf₉, hlen₉, hregs₉, harrs₉⟩
  have hlen₉' : (s₉.arrs bufArr2).length = 3 + 3 * n := by
    rw [hlen₉]; dsimp only [s₈]; exact hlen₇'
  have hkeep_reg9 : ∀ r : Reg, r ≠ 6 → r ≠ 7 → r ≠ 30 → r ≠ 31 → s₉.regs r = s.regs r := by
    intro r h6 h7 h30 h31
    rw [hregs₉ r h7]
    dsimp only [s₈]
    rw [State.setReg_regs_ne _ _ h6, hregs₇ r h7]
    dsimp only [s₆]
    rw [State.setReg_regs_ne _ _ h6, hregs₅ r h7]
    dsimp only [s₄]
    rw [State.setReg_regs_ne _ _ h6, hregs₃ r h7]
    dsimp only [s₂, s₁]
    rw [State.setReg_regs_ne _ _ h31, State.setReg_regs_ne _ _ h30]
  have hkeep_arr9 : ∀ a : Arr, a ≠ bufArr2 → s₉.arrs a = s.arrs a := by
    intro a ha
    rw [harrs₉ a ha]
    dsimp only [s₈]
    rw [State.setReg_arrs, harrs₇ a ha]
    dsimp only [s₆]
    rw [State.setReg_arrs, harrs₅ a ha]
    dsimp only [s₄]
    rw [State.setReg_arrs, harrs₃ a ha]
    rfl
  have hr30_9 : s₉.regs 30 = W' := by
    rw [hregs₉ 30 (by decide)]
    dsimp only [s₈]
    rw [State.setReg_regs_ne _ _ (by decide), hregs₇ 30 (by decide)]
    dsimp only [s₆]
    rw [State.setReg_regs_ne _ _ (by decide), hregs₅ 30 (by decide)]
    dsimp only [s₄]
    rw [State.setReg_regs_ne _ _ (by decide), hregs₃ 30 (by decide)]
    dsimp only [s₂, s₁]
    rfl
  have hr31_9 : s₉.regs 31 = V' := by
    rw [hregs₉ 31 (by decide)]
    dsimp only [s₈]
    rw [State.setReg_regs_ne _ _ (by decide), hregs₇ 31 (by decide)]
    dsimp only [s₆]
    rw [State.setReg_regs_ne _ _ (by decide)]
    exact hr31_5
  let s₁₀ := s₉.setReg 32 0
  have hex₁₀ : Exec w (.assign 32 (.const 0)) s₉ s₁₀ 2 :=
    .assign (by simp [Expr.eval, checkWord, h0_w])
  let s₁₁ := s₁₀.setReg 33 V'
  have hex₁₁ : Exec w (.assign 33 (.reg 31)) s₁₀ s₁₁ 2 :=
    .assign (by
      have h31 : s₁₀.regs 31 = V' := by dsimp only [s₁₀]; rw [State.setReg_regs_ne _ _ (by decide)]; exact hr31_9
      simp [Expr.eval, checkWord, h31, hV'_w])
  have hs₁₁ : WallStateHolds W s₁₁ :=
    hs.of_arr_ne
      (by dsimp only [s₁₁, s₁₀]; simp [hkeep_reg9 0 (by decide) (by decide) (by decide) (by decide)])
      (by dsimp only [s₁₁, s₁₀]; simp [hkeep_reg9 3 (by decide) (by decide) (by decide) (by decide)])
      (by dsimp only [s₁₁, s₁₀]; simp [hkeep_reg9 12 (by decide) (by decide) (by decide) (by decide)])
      (by dsimp only [s₁₁, s₁₀]; simp [hkeep_reg9 13 (by decide) (by decide) (by decide) (by decide)])
      (by dsimp only [s₁₁, s₁₀]; simp [hkeep_reg9 14 (by decide) (by decide) (by decide) (by decide)])
      bufArr2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide)
      (fun a ha => by dsimp only [s₁₁, s₁₀]; exact hkeep_arr9 a ha)
  have hbuf₁₁ : IsArrBufPrefix (s₁₁.arrs bufArr2)
      ([h', V', 0] ++ ((List.finRange V').take 0).map
        (fun u' => ((W.realizeSubwall R).branchVert u').1))
      (s₁₁.regs 7) := by
    dsimp only [s₁₁, s₁₀]
    simpa using hbuf₉
  rcases realizeBranchVertsLoop_exec W R code hvmap hw4 hn_w hmode_le hY0_w hc0_w
      h3h'9_w hVJW_w henc_w V' 0 (Nat.zero_add V') [h', V', 0] (s := s₁₁)
      hs₁₁
      (by dsimp only [s₁₁, s₁₀]; simp [hkeep_reg9 15 (by decide) (by decide) (by decide) (by decide), hr15])
      (by dsimp only [s₁₁, s₁₀]; simp [hkeep_reg9 16 (by decide) (by decide) (by decide) (by decide), hr16])
      (by dsimp only [s₁₁, s₁₀]; simp [hkeep_reg9 17 (by decide) (by decide) (by decide) (by decide), hr17])
      (by dsimp only [s₁₁, s₁₀]; simp [hkeep_reg9 22 (by decide) (by decide) (by decide) (by decide), hr22])
      (by dsimp only [s₁₁, s₁₀]; simp [hr30_9, W'])
      (by dsimp only [s₁₁, s₁₀]; simp)
      (by dsimp only [s₁₁]; simp)
      hbuf₁₁
      (by dsimp only [s₁₁, s₁₀]; rw [State.setReg_arrs, State.setReg_arrs, hlen₉']; simp [V']; omega)
      (by dsimp only [s₁₁, s₁₀]; rw [State.setReg_arrs, State.setReg_arrs, hlen₉']; exact hcap_w) with
    ⟨s₁₂, t_br, hex₁₂, ht_br, hbuf₁₂, hlen₁₂, hregs₁₂, harrs₁₂⟩
  have hkeep_reg12 : ∀ r : Reg, r ≠ 6 → r ≠ 7 → r ≠ 8 → r ≠ 9 → r ≠ 18 → r ≠ 19 →
      r ≠ 30 → r ≠ 31 → r ≠ 32 → r ≠ 33 → s₁₂.regs r = s.regs r := by
    intro r h6 h7 h8 h9 h18 h19 h30 h31 h32 h33
    rw [hregs₁₂ r h6 h7 h8 h9 h18 h19 h32 h33]
    dsimp only [s₁₁, s₁₀]
    rw [State.setReg_regs_ne _ _ h33, State.setReg_regs_ne _ _ h32]
    exact hkeep_reg9 r h6 h7 h30 h31
  have hkeep_arr12 : ∀ a : Arr, a ≠ bufArr2 → s₁₂.arrs a = s.arrs a := by
    intro a ha
    rw [harrs₁₂ a ha]
    dsimp only [s₁₁, s₁₀]
    exact hkeep_arr9 a ha
  have hs₁₂ : WallStateHolds W s₁₂ :=
    hs.of_arr_ne
      (hkeep_reg12 0 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))
      (hkeep_reg12 3 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))
      (hkeep_reg12 12 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))
      (hkeep_reg12 13 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))
      (hkeep_reg12 14 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))
      bufArr2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) hkeep_arr12
  have hlen₁₂' : (s₁₂.arrs bufArr2).length = 3 + 3 * n := by
    rw [hlen₁₂]; dsimp only [s₁₁, s₁₀]; exact hlen₉'
  have hr30_12 : s₁₂.regs 30 = W' := by
    rw [hregs₁₂ 30 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]
    dsimp only [s₁₁, s₁₀]
    simp [hr30_9]
  have hr31_12 : s₁₂.regs 31 = V' := by
    rw [hregs₁₂ 31 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]
    dsimp only [s₁₁, s₁₀]
    simp [hr31_9]
  have hc_init : (Expr.op .add (.const 3) (.op .mul (.const 3) (.reg 0))).cost ≤ 10 := by decide
  dsimp only [V'] at ht_br
  refine ⟨s₁₂,
    6 + (8 + (t_init + (2 + (t_p1 + (2 + (t_p2 + (2 + (t_p3 + (2 + (2 + t_br)))))))))),
    .seq hex₁ (.seq hex₂ (.seq hex₃ (.seq hex₄ (.seq hex₅ (.seq hex₆
      (.seq hex₇ (.seq hex₈ (.seq hex₉ (.seq hex₁₀ (.seq hex₁₁ hex₁₂)))))))))),
    by linarith [ht_init, hc_init, ht_p1, ht_p2, ht_p3, ht_br],
    hs₁₂, hbuf₁₂, hlen₁₂', hr30_12, hr31_12, hkeep_reg12, hkeep_arr12⟩

/-- Second half of `realizeSubwallCmd`: runs `realizeEdgesLoop`, writes `r_34` (`= E_{J'}`) to
`bufArr2[2]`, and copies the prefix `(W.realizeSubwall R).encList` of `bufArr2` into `newWallEncArr`. -/
def realizeSubwallEdgesAndCopyCmd : Cmd :=
  .seq (.assign 32 (.const 0))
  (.seq (.assign 33 (.reg 31))
  (.seq (.assign 34 (.const 0))
  (.seq realizeEdgesLoop
  (.seq (.write bufArr2 (.const 2) (.reg 34))
  (.seq (.assign 8 (.const 0))
  (.seq (.assign 9 (.reg 7))
    (copySliceToArrCmd bufArr2 newWallEncArr)))))))

theorem realizeSubwallEdgesAndCopyCmd_exec {w h' n : ℕ} {G : MultiDigraph n}
    (W : WallOfHeight (h' + 2) G)
    {τ : GM13.Shape (h' + 2) h'} (R : τ.Realization)
    (code : RealizationCode)
    (hvmap : ∀ p, vmapOfCode h' code p = R.vmap p)
    (hinner : ∀ p q, innerOfCode h' code p q = R.inner p q)
    (_h2' : 2 ≤ h') (_he' : Even h') (hW : W.IsValid)
    {s : State}
    (hw4 : 4 < 2 ^ w)
    (hn_w : n < 2 ^ w)
    (hcap_w : 3 + 3 * n < 2 ^ w)
    (hmode_le : code.mode ≤ 3)
    (hY0_w : code.Y0 < 2 ^ w)
    (hc0_w : code.c0 < 2 ^ w)
    (h3h'9_w : 3 * h' + 9 < 2 ^ w)
    (hVJW'_w : elemWallNumVerts h' + (2 * h' + 2) < 2 ^ w)
    (hEJ'_w : (elemWallEdges h').length < 2 ^ w)
    (hVJW_w : elemWallNumVerts (h' + 2) + (2 * (h' + 2) + 2) < 2 ^ w)
    (hloc_w : elemWallNumVerts (h' + 2) + (elemWallEdges (h' + 2)).length < 2 ^ w)
    (henc_w : W.encList.length < 2 ^ w)
    (hs : WallStateHolds W s)
    (hr15 : s.regs 15 = code.mode)
    (hr16 : s.regs 16 = code.Y0)
    (hr17 : s.regs 17 = code.c0)
    (hr22 : s.regs 22 = h')
    (hr30 : s.regs 30 = 2 * h' + 2)
    (hr31 : s.regs 31 = elemWallNumVerts h')
    (hbuf : IsArrBufPrefix (s.arrs bufArr2)
      ([h', elemWallNumVerts h', 0] ++
        (List.finRange (elemWallNumVerts h')).map
          (fun u' => ((W.realizeSubwall R).branchVert u').1))
      (s.regs 7))
    (hlen_buf : (s.arrs bufArr2).length = 3 + 3 * n) :
    ∃ s' t,
      Exec w realizeSubwallEdgesAndCopyCmd s s' t ∧
      t ≤ 120 * elemWallNumVerts h' + 1350 * (W.realizeSubwall R).encList.length + 50 ∧
      WallStateHolds W s' ∧
      s'.arrs newWallEncArr = (W.realizeSubwall R).encList ∧
      (∀ r : Reg, r ≠ 6 → r ≠ 7 → r ≠ 8 → r ≠ 9 → r ≠ 10 → r ≠ 11 →
        r ≠ 18 → r ≠ 19 → r ≠ 20 → r ≠ 21 → r ≠ 25 → r ≠ 26 → r ≠ 27 →
        r ≠ 28 → r ≠ 29 → r ≠ 32 → r ≠ 33 → r ≠ 34 → s'.regs r = s.regs r) ∧
      (∀ a : Arr, a ≠ bufArr2 → a ≠ newWallEncArr → a ≠ coordXArr → a ≠ coordYArr →
        s'.arrs a = s.arrs a) := by
  have h0_w : 0 < 2 ^ w := by omega
  have h1_w : 1 < 2 ^ w := by omega
  have h2_w : 2 < 2 ^ w := by omega
  have hh'_w : h' < 2 ^ w := by omega
  let V' := elemWallNumVerts h'
  let E' := (elemWallEdges h').length
  have hV'_w : V' < 2 ^ w := by dsimp [V']; omega
  have hW'_valid : (W.realizeSubwall R).IsValid := W.realizeSubwall_isValid R hW
  have henc'_le : (W.realizeSubwall R).encList.length ≤ 3 + 3 * n :=
    (W.realizeSubwall R).length_encList_le hW'_valid
  have henc'_w : (W.realizeSubwall R).encList.length < 2 ^ w := by omega
  let pfx_br := [h', V', 0] ++
    (List.finRange V').map (fun u' => ((W.realizeSubwall R).branchVert u').1)
  have henc'_eq :
      (W.realizeSubwall R).encList =
        [h', V', E'] ++
          (List.finRange V').map (fun u' => ((W.realizeSubwall R).branchVert u').1) ++
          encRealizeEdgeList W R (elemWallEdges h') := by
    rw [encRealizeEdgeList_elemWallEdges, wallEncList_eq_append_encInternalSlice]
  have henc'_len :
      (W.realizeSubwall R).encList.length =
        pfx_br.length + (encRealizeEdgeList W R (elemWallEdges h')).length := by
    rw [henc'_eq]
    simp only [pfx_br, List.length_append, List.length_cons, List.length_nil,
      List.length_map, List.length_finRange]
  let s₁ := s.setReg 32 0
  have hex₁ : Exec w (.assign 32 (.const 0)) s s₁ 2 :=
    .assign (by simp [Expr.eval, checkWord, h0_w])
  let s₂ := s₁.setReg 33 V'
  have hex₂ : Exec w (.assign 33 (.reg 31)) s₁ s₂ 2 :=
    .assign (by simp [Expr.eval, checkWord, s₁, hr31, hV'_w, V'])
  let s₃ := s₂.setReg 34 0
  have hex₃ : Exec w (.assign 34 (.const 0)) s₂ s₃ 2 :=
    .assign (by simp [Expr.eval, checkWord, h0_w])
  have hs₃ : WallStateHolds W s₃ :=
    hs.of_preserve rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl
  have hbuf₃ : IsArrBufPrefix (s₃.arrs bufArr2)
      (pfx_br ++ encRealizeEdgeList W R (elemWallEdgesPrefix h' 0)) (s₃.regs 7) := by
    rw [elemWallEdgesPrefix_zero, encRealizeEdgeList_nil, List.append_nil]
    dsimp only [s₃, s₂, s₁]
    exact hbuf
  rcases realizeEdgesLoop_exec W R code hvmap hinner hw4 hn_w hmode_le hY0_w hc0_w
      h3h'9_w hVJW'_w hEJ'_w hVJW_w hloc_w henc_w V' 0 (Nat.zero_add V') pfx_br (s := s₃)
      hs₃
      (by dsimp only [s₃, s₂, s₁]; exact hr15)
      (by dsimp only [s₃, s₂, s₁]; exact hr16)
      (by dsimp only [s₃, s₂, s₁]; exact hr17)
      (by dsimp only [s₃, s₂, s₁]; exact hr22)
      (by dsimp only [s₃, s₂, s₁]; exact hr30)
      (by dsimp only [s₃, s₂, s₁]; exact hr31)
      (by dsimp only [s₃, s₂, s₁]; simp)
      (by dsimp only [s₃, s₂]; simp)
      (by dsimp only [s₃]; simp [elemWallEdgesPrefix_zero])
      hbuf₃
      (by dsimp only [s₃, s₂, s₁]; rw [State.setReg_arrs, State.setReg_arrs, State.setReg_arrs, hlen_buf]; omega)
      (by dsimp only [s₃, s₂, s₁]; rw [State.setReg_arrs, State.setReg_arrs, State.setReg_arrs, hlen_buf]; exact hcap_w) with
    ⟨s₄, t_ed, hex₄, ht_ed, hbuf₄, hlen₄, hr34_4, hregs₄, harrs₄⟩
  have hlen₄' : (s₄.arrs bufArr2).length = 3 + 3 * n := by
    rw [hlen₄]; dsimp only [s₃, s₂, s₁]; exact hlen_buf
  let s₅ := s₄.writeArr bufArr2 2 E'
  have hex₅ : Exec w (.write bufArr2 (.const 2) (.reg 34)) s₄ s₅ 3 :=
    .write (by simp [Expr.eval, checkWord, h2_w])
      (by simp [Expr.eval, checkWord, hr34_4, hEJ'_w, E'])
      (by rw [hlen₄']; omega)
  have hbuf₅ : IsArrBufPrefix (s₅.arrs bufArr2) (W.realizeSubwall R).encList (s₅.regs 7) := by
    have hset := IsArrBufPrefix.write_at_prefix hbuf₄ 2 E'
    have hlist_set :
        (pfx_br ++ encRealizeEdgeList W R (elemWallEdges h')).set 2 E' =
          (W.realizeSubwall R).encList := by
      simp [pfx_br, henc'_eq]
    rw [hlist_set] at hset
    dsimp only [s₅]
    rw [State.writeArr_arrs_self, State.writeArr_regs]
    exact hset
  have hlen₅' : (s₅.arrs bufArr2).length = 3 + 3 * n := by
    dsimp only [s₅]
    rw [State.writeArr_arrs_self, List.length_set, hlen₄']
  have hr7_5 : s₅.regs 7 = (W.realizeSubwall R).encList.length := hbuf₅.1
  let s₆ := s₅.setReg 8 0
  have hex₆ : Exec w (.assign 8 (.const 0)) s₅ s₆ 2 :=
    .assign (by simp [Expr.eval, checkWord, h0_w])
  let s₇ := s₆.setReg 9 (W.realizeSubwall R).encList.length
  have hex₇ : Exec w (.assign 9 (.reg 7)) s₆ s₇ 2 :=
    .assign (by
      have h7 : s₆.regs 7 = (W.realizeSubwall R).encList.length := by
        dsimp only [s₆]; rw [State.setReg_regs_ne _ _ (by decide)]; exact hr7_5
      simp [Expr.eval, checkWord, h7, henc'_w])
  have hvals_enc' : ∀ v ∈ (W.realizeSubwall R).encList, v < 2 ^ w :=
    forall_mem_wallEncList_lt (W.realizeSubwall R) hh'_w hV'_w hEJ'_w hn_w henc'_w
  rcases copySliceToArrCmd_exec bufArr2 newWallEncArr (by decide)
      (W.realizeSubwall R).encList 0 (s := s₇) h1_w
      (by dsimp only [s₇, s₆]; rw [State.setReg_arrs, State.setReg_arrs, hlen₅']; exact hcap_w)
      (by dsimp only [s₇, s₆]; rw [State.setReg_arrs, State.setReg_arrs, hlen₅']; simpa using henc'_le)
      (fun j hj => by
        dsimp only [s₇, s₆]
        rw [State.setReg_arrs, State.setReg_arrs, Nat.zero_add]
        exact hbuf₅.2.2 j hj)
      hvals_enc'
      (by dsimp only [s₇, s₆]; simp)
      (by dsimp only [s₇]; simp) with
    ⟨s₈, t_cp, hex₈, ht_cp, hnew_enc8, _, hregs₈, harrs₈⟩
  have hkeep_reg8 : ∀ r : Reg, r ≠ 6 → r ≠ 7 → r ≠ 8 → r ≠ 9 → r ≠ 10 → r ≠ 11 →
      r ≠ 18 → r ≠ 19 → r ≠ 20 → r ≠ 21 → r ≠ 25 → r ≠ 26 → r ≠ 27 →
      r ≠ 28 → r ≠ 29 → r ≠ 32 → r ≠ 33 → r ≠ 34 → s₈.regs r = s.regs r := by
    intro r h6 h7 h8 h9 h10 h11 h18 h19 h20 h21 h25 h26 h27 h28 h29 h32 h33 h34
    rw [hregs₈ r h7 h8 h9 h11]
    dsimp only [s₇, s₆, s₅]
    rw [State.setReg_regs_ne _ _ h9, State.setReg_regs_ne _ _ h8, State.writeArr_regs,
      hregs₄ r h6 h7 h8 h9 h10 h11 h18 h19 h20 h21 h25 h26 h27 h28 h29 h32 h33 h34]
    dsimp only [s₃, s₂, s₁]
    rw [State.setReg_regs_ne _ _ h34, State.setReg_regs_ne _ _ h33, State.setReg_regs_ne _ _ h32]
  have hkeep_arr8 : ∀ a : Arr, a ≠ bufArr2 → a ≠ newWallEncArr → a ≠ coordXArr → a ≠ coordYArr →
      s₈.arrs a = s.arrs a := by
    intro a ha1 ha2 ha3 ha4
    rw [harrs₈ a ha2]
    dsimp only [s₇, s₆, s₅]
    rw [State.setReg_arrs, State.setReg_arrs, State.writeArr_arrs_ne _ _ _ ha1,
      harrs₄ a ha1 ha3 ha4]
    rfl
  have hs₈ : WallStateHolds W s₈ :=
    hs.of_preserve
      (hkeep_reg8 0 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))
      (hkeep_reg8 3 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))
      (hkeep_reg8 12 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))
      (hkeep_reg8 13 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))
      (hkeep_reg8 14 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))
      (hkeep_arr8 wallEncArr (by decide) (by decide) (by decide) (by decide))
      (hkeep_arr8 locArr (by decide) (by decide) (by decide) (by decide))
      (hkeep_arr8 wallMemArr (by decide) (by decide) (by decide) (by decide))
      (hkeep_arr8 edgeOffArr (by decide) (by decide) (by decide) (by decide))
      (hkeep_arr8 edgeLenArr (by decide) (by decide) (by decide) (by decide))
      (hkeep_arr8 edgeU1Arr (by decide) (by decide) (by decide) (by decide))
      (hkeep_arr8 edgeU2Arr (by decide) (by decide) (by decide) (by decide))
      (hkeep_arr8 horizEdgeIdxArr (by decide) (by decide) (by decide) (by decide))
      (hkeep_arr8 vertEdgeIdxArr (by decide) (by decide) (by decide) (by decide))
  simp only [elemWallEdgesPrefix_zero, encRealizeEdgeList_nil, List.length_nil, Nat.sub_zero] at ht_ed
  dsimp only [V'] at ht_ed
  refine ⟨s₈,
    2 + (2 + (2 + (t_ed + (3 + (2 + (2 + t_cp)))))),
    .seq hex₁ (.seq hex₂ (.seq hex₃ (.seq hex₄ (.seq hex₅ (.seq hex₆ (.seq hex₇ hex₈)))))),
    by linarith [ht_ed, ht_cp, henc'_len],
    hs₈, hnew_enc8, hkeep_reg8, hkeep_arr8⟩

/-- Full subwall realization command: computes `(W.realizeSubwall R).encList` into `newWallEncArr`. -/
def realizeSubwallCmd : Cmd :=
  .seq realizeSubwallInitAndBranchCmd realizeSubwallEdgesAndCopyCmd

theorem realizeSubwallCmd_exec {w h' n : ℕ} {G : MultiDigraph n}
    (W : WallOfHeight (h' + 2) G)
    {τ : GM13.Shape (h' + 2) h'} (R : τ.Realization)
    (code : RealizationCode)
    (hvmap : ∀ p, vmapOfCode h' code p = R.vmap p)
    (hinner : ∀ p q, innerOfCode h' code p q = R.inner p q)
    (h2' : 2 ≤ h') (_he' : Even h') (hW : W.IsValid)
    {s : State}
    (hw4 : 4 < 2 ^ w)
    (hn_w : n < 2 ^ w)
    (hcap_w : 3 + 3 * n < 2 ^ w)
    (hmode_le : code.mode ≤ 3)
    (hY0_w : code.Y0 < 2 ^ w)
    (hc0_w : code.c0 < 2 ^ w)
    (h3h'9_w : 3 * h' + 9 < 2 ^ w)
    (hVJW'_w : elemWallNumVerts h' + (2 * h' + 2) < 2 ^ w)
    (hEJ'_w : (elemWallEdges h').length < 2 ^ w)
    (hVJW_w : elemWallNumVerts (h' + 2) + (2 * (h' + 2) + 2) < 2 ^ w)
    (hloc_w : elemWallNumVerts (h' + 2) + (elemWallEdges (h' + 2)).length < 2 ^ w)
    (henc_w : W.encList.length < 2 ^ w)
    (hs : WallStateHolds W s)
    (hr15 : s.regs 15 = code.mode)
    (hr16 : s.regs 16 = code.Y0)
    (hr17 : s.regs 17 = code.c0)
    (hr22 : s.regs 22 = h') :
    ∃ s' t,
      Exec w realizeSubwallCmd s s' t ∧
      t ≤ 3 * n + 380 * elemWallNumVerts h' + 1350 * (W.realizeSubwall R).encList.length + 120 ∧
      WallStateHolds W s' ∧
      s'.arrs newWallEncArr = (W.realizeSubwall R).encList ∧
      (∀ r : Reg, r ≠ 6 → r ≠ 7 → r ≠ 8 → r ≠ 9 → r ≠ 10 → r ≠ 11 →
        r ≠ 18 → r ≠ 19 → r ≠ 20 → r ≠ 21 → r ≠ 25 → r ≠ 26 → r ≠ 27 →
        r ≠ 28 → r ≠ 29 → r ≠ 30 → r ≠ 31 → r ≠ 32 → r ≠ 33 → r ≠ 34 →
        s'.regs r = s.regs r) ∧
      (∀ a : Arr, a ≠ bufArr2 → a ≠ newWallEncArr → a ≠ coordXArr → a ≠ coordYArr →
        s'.arrs a = s.arrs a) := by
  rcases realizeSubwallInitAndBranchCmd_exec W R code hvmap h2' _he' hW hw4 hn_w hcap_w
      hmode_le hY0_w hc0_w h3h'9_w hVJW_w henc_w hs hr15 hr16 hr17 hr22 with
    ⟨s₁, t₁, hex₁, ht₁, hs₁, hbuf₁, hlen₁, hr30_1, hr31_1, hregs₁, harrs₁⟩
  rcases realizeSubwallEdgesAndCopyCmd_exec W R code hvmap hinner h2' _he' hW hw4 hn_w hcap_w
      hmode_le hY0_w hc0_w h3h'9_w hVJW'_w hEJ'_w hVJW_w hloc_w henc_w hs₁
      (by rw [hregs₁ 15 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), hr15])
      (by rw [hregs₁ 16 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), hr16])
      (by rw [hregs₁ 17 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), hr17])
      (by rw [hregs₁ 22 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), hr22])
      hr30_1 hr31_1 hbuf₁ hlen₁ with
    ⟨s₂, t₂, hex₂, ht₂, hs₂, hnew_enc2, hregs₂, harrs₂⟩
  refine ⟨s₂, t₁ + t₂, .seq hex₁ hex₂, by omega, hs₂, hnew_enc2,
    fun r h6 h7 h8 h9 h10 h11 h18 h19 h20 h21 h25 h26 h27 h28 h29 h30 h31 h32 h33 h34 => by
      rw [hregs₂ r h6 h7 h8 h9 h10 h11 h18 h19 h20 h21 h25 h26 h27 h28 h29 h32 h33 h34,
        hregs₁ r h6 h7 h8 h9 h18 h19 h30 h31 h32 h33],
    fun a ha1 ha2 ha3 ha4 => by
      rw [harrs₂ a ha1 ha2 ha3 ha4, harrs₁ a ha1]⟩

/-- Populate `newWallMemArr` with the membership indicator of `W'.vertexFinset` (where
`s.arrs newWallEncArr = W'.encList`) while preserving `WallStateHolds W s`. -/
def computeNewWallMemCmd : Cmd :=
  .seq (copyArrCmd wallEncArr bufArr2)
  (.seq (copyArrCmd newWallEncArr wallEncArr)
  (.seq prepareWallStateCmd
  (.seq (copyArrCmd wallMemArr newWallMemArr)
  (.seq (copyArrCmd bufArr2 wallEncArr)
    prepareWallStateCmd))))

theorem computeNewWallMemCmd_exec {w h h' n : ℕ} {G : MultiDigraph n}
    (W : WallOfHeight h G) (hW : W.IsValid)
    (W' : WallOfHeight h' G) (hW' : W'.IsValid)
    {s : State}
    (hw3 : 3 < 2 ^ w)
    (hn_w : n < 2 ^ w)
    (hVJW_w : elemWallNumVerts h + (2 * h + 2) < 2 ^ w)
    (hloc_w : elemWallNumVerts h + (elemWallEdges h).length < 2 ^ w)
    (henc_w : W.encList.length < 2 ^ w)
    (hVJW'_w : elemWallNumVerts h' + (2 * h' + 2) < 2 ^ w)
    (hloc'_w : elemWallNumVerts h' + (elemWallEdges h').length < 2 ^ w)
    (henc'_w : W'.encList.length < 2 ^ w)
    (hs : WallStateHolds W s)
    (hnew_enc : s.arrs newWallEncArr = W'.encList) :
    ∃ s' t,
      Exec w computeNewWallMemCmd s s' t ∧
      t ≤ 26 * n + 120 * elemWallNumVerts h + 64 * (elemWallEdges h).length +
        64 * W.encList.length + 120 * elemWallNumVerts h' + 64 * (elemWallEdges h').length +
        42 * W'.encList.length + 200 ∧
      WallStateHolds W s' ∧
      s'.arrs newWallEncArr = W'.encList ∧
      (s'.arrs newWallMemArr).length = n ∧
      (∀ v : Fin n,
        (s'.arrs newWallMemArr)[v.1]? = some (if v ∈ W'.vertexFinset then 1 else 0)) ∧
      (∀ r : Reg, r ≠ 3 → r ≠ 4 → r ≠ 5 → r ≠ 6 → r ≠ 7 → r ≠ 8 → r ≠ 9 →
        r ≠ 10 → r ≠ 11 → r ≠ 12 → r ≠ 13 → r ≠ 14 → s'.regs r = s.regs r) ∧
      (∀ a : Arr, a ≠ wallEncArr → a ≠ locArr → a ≠ wallMemArr → a ≠ edgeOffArr →
        a ≠ edgeLenArr → a ≠ edgeU1Arr → a ≠ edgeU2Arr → a ≠ horizEdgeIdxArr →
        a ≠ vertEdgeIdxArr → a ≠ bufArr2 → a ≠ newWallMemArr → s'.arrs a = s.arrs a) := by
  have h1_w : 1 < 2 ^ w := by omega
  have hvals_W : ∀ v ∈ W.encList, v < 2 ^ w :=
    forall_mem_wallEncList_lt W (by omega) (by omega) (by omega) hn_w henc_w
  have hvals_W' : ∀ v ∈ W'.encList, v < 2 ^ w :=
    forall_mem_wallEncList_lt W' (by omega) (by omega) (by omega) hn_w henc'_w
  rcases copyArrCmd_exec wallEncArr bufArr2 (by decide) (s := s) h1_w
      (by rw [hs.henc]; exact henc_w)
      (by rw [hs.henc]; exact hvals_W) with
    ⟨s₁, t₁, hex₁, ht₁, hbuf1, hregs₁, harrs₁⟩
  rw [hs.henc] at hbuf1 ht₁
  have hnew1 : s₁.arrs newWallEncArr = W'.encList := by
    rw [harrs₁ newWallEncArr (by decide), hnew_enc]
  rcases copyArrCmd_exec newWallEncArr wallEncArr (by decide) (s := s₁) h1_w
      (by rw [hnew1]; exact henc'_w)
      (by rw [hnew1]; exact hvals_W') with
    ⟨s₂, t₂, hex₂, ht₂, henc2, hregs₂, harrs₂⟩
  rw [hnew1] at henc2 ht₂
  have hr0_2 : s₂.regs 0 = n := by
    rw [hregs₂ 0 (by decide) (by decide) (by decide) (by decide),
      hregs₁ 0 (by decide) (by decide) (by decide) (by decide), hs.hr0]
  rcases prepareWallStateCmd_exec W' hW' hw3 hn_w hVJW'_w hloc'_w henc'_w henc2 hr0_2 with
    ⟨s₃, t₃, hex₃, ht₃, hs₃, hregs₃, harrs₃⟩
  have hvals_mem3 : ∀ v ∈ s₃.arrs wallMemArr, v < 2 ^ w := by
    intro v hv
    rcases List.mem_iff_getElem.mp hv with ⟨i, hi, rfl⟩
    have hi_n : i < n := by rw [← hs₃.hmem_len]; exact hi
    have hget := hs₃.hmem_val ⟨i, hi_n⟩
    rw [List.getElem?_eq_getElem hi, Option.some.injEq] at hget
    rw [hget]
    split_ifs <;> omega
  rcases copyArrCmd_exec wallMemArr newWallMemArr (by decide) (s := s₃) h1_w
      (by rw [hs₃.hmem_len]; exact hn_w) hvals_mem3 with
    ⟨s₄, t₄, hex₄, ht₄, hnew_mem4, hregs₄, harrs₄⟩
  rw [hs₃.hmem_len] at ht₄
  have hbuf4 : s₄.arrs bufArr2 = W.encList := by
    rw [harrs₄ bufArr2 (by decide),
      harrs₃ bufArr2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
      harrs₂ bufArr2 (by decide), hbuf1]
  rcases copyArrCmd_exec bufArr2 wallEncArr (by decide) (s := s₄) h1_w
      (by rw [hbuf4]; exact henc_w)
      (by rw [hbuf4]; exact hvals_W) with
    ⟨s₅, t₅, hex₅, ht₅, henc5, hregs₅, harrs₅⟩
  rw [hbuf4] at henc5 ht₅
  have hr0_5 : s₅.regs 0 = n := by
    rw [hregs₅ 0 (by decide) (by decide) (by decide) (by decide),
      hregs₄ 0 (by decide) (by decide) (by decide) (by decide), hs₃.hr0]
  rcases prepareWallStateCmd_exec W hW hw3 hn_w hVJW_w hloc_w henc_w henc5 hr0_5 with
    ⟨s₆, t₆, hex₆, ht₆, hs₆, hregs₆, harrs₆⟩
  have hnew_enc6 : s₆.arrs newWallEncArr = W'.encList := by
    rw [harrs₆ newWallEncArr (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
      harrs₅ newWallEncArr (by decide),
      harrs₄ newWallEncArr (by decide),
      harrs₃ newWallEncArr (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
      harrs₂ newWallEncArr (by decide), hnew1]
  have hnew_mem6 : s₆.arrs newWallMemArr = s₃.arrs wallMemArr := by
    rw [harrs₆ newWallMemArr (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
      harrs₅ newWallMemArr (by decide), hnew_mem4]
  refine ⟨s₆, t₁ + (t₂ + (t₃ + (t₄ + (t₅ + t₆)))),
    .seq hex₁ (.seq hex₂ (.seq hex₃ (.seq hex₄ (.seq hex₅ hex₆)))),
    by omega, hs₆, hnew_enc6,
    by rw [hnew_mem6, hs₃.hmem_len],
    fun v => by rw [hnew_mem6]; exact hs₃.hmem_val v,
    fun r h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 => by
      rw [hregs₆ r h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14,
        hregs₅ r h7 h8 h9 h11,
        hregs₄ r h7 h8 h9 h11,
        hregs₃ r h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14,
        hregs₂ r h7 h8 h9 h11,
        hregs₁ r h7 h8 h9 h11],
    fun a ha_enc ha_loc ha_mem ha_off ha_len ha_u1 ha_u2 ha_hor ha_ver ha_buf ha_nmem => by
      rw [harrs₆ a ha_loc ha_mem ha_off ha_len ha_u1 ha_u2 ha_hor ha_ver,
        harrs₅ a ha_enc,
        harrs₄ a ha_nmem,
        harrs₃ a ha_loc ha_mem ha_off ha_len ha_u1 ha_u2 ha_hor ha_ver,
        harrs₂ a ha_enc,
        harrs₁ a ha_buf]⟩

end GraphMinor.Compute
