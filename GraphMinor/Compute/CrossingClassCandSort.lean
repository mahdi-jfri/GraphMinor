module

public import GraphMinor.Compute.CrossingClassAttach

/-!
# Candidate Generation and Stable Counting Sorts

This file implements two parts of $\operatorname{BridgeCross}(K, D)$ in the Word RAM model: the
generation of the candidates of Section 5.1 of `docs/crossing/crossing_extractor.tex` and their
sorting at the start of Section 5.2.

1. **Candidate generation (`candGenProg`)**:
   > "For a bridge with attachment list $t_0,t_1,\ldots,t_{h-1}$, we generate the pairs
   > $\{t_i,t_{i+1}\}$, $\{t_i,t_{i+2}\}$ with indices modulo $h$, and omit pairs whose two elements
   > are equal. Duplicates may be kept. These pairs are the *candidates* of the bridge. There are at
   > most twice as many candidates as attachments." (Section 5.1)
   > "Number the vertices of $D$ as $0,\ldots,c-1$ in cyclic order. We represent a candidate as a
   > triple $(l,r,\gamma)$, $l<r$, where $l$ and $r$ are the numbers of its two attachments and
   > $\gamma$, its *color*, is the identifier of its bridge." (Section 5.2)

2. **Two stable counting sorts (`countingSortProg`, `sortCandProg`)**:
   > "Sort the candidates by increasing $l$, breaking ties by decreasing $r$. Two stable counting
   > sorts do this in linear time." (Section 5.2)
-/

@[expose] public section

namespace GraphMinor.Compute

open SimpleGraph GraphMinor.HP25 GraphMinor.Crossing GraphMinor.Compute.Crossing
  GraphMinor.Compute.TwoPaths
open scoped BigOperators

variable {n : ℕ}

/-! ### Register and Array Assignments for Candidates and Counting Sort -/

/-- Number of generated candidates `cs.length`. -/
abbrev rNumCand : Reg := 110
/-- Allocated capacity `2 * totalAttachments H T bridges` for candidate arrays. -/
abbrev rCandCap : Reg := 111
/-- Extra scratch register 3. -/
abbrev rTmp3 : Reg := 112
/-- Extra scratch register 4. -/
abbrev rTmp4 : Reg := 113

/-- Candidate array: left endpoint `I.l`. -/
abbrev aCandL : Arr := 112
/-- Candidate array: right endpoint `I.r`. -/
abbrev aCandR : Arr := 113
/-- Candidate array: bridge identifier `I.γ`. -/
abbrev aCandG : Arr := 114
/-- Counting sort scratch array: left endpoint `I.l`. -/
abbrev aSortL : Arr := 115
/-- Counting sort scratch array: right endpoint `I.r`. -/
abbrev aSortR : Arr := 116
/-- Counting sort scratch array: bridge identifier `I.γ`. -/
abbrev aSortG : Arr := 117
/-- Bucket lengths during counting sort (`0 .. c - 1`). -/
abbrev aBucketLen : Arr := 118
/-- Bucket write cursors during counting sort (`0 .. c - 1`). -/
abbrev aBucketPos : Arr := 119

/-! ### Part 1: Candidate Array Representation (`IsCandArray`) -/

/-- Predicate stating that arrays `(aL, aR, aG)` of capacity `cap` and length register `rLen`
store the candidate list `cs : List Candidate`. -/
def IsCandArray (cs : List Candidate) (cap : ℕ) (aL aR aG : Arr) (rLen : Reg) (s : State) : Prop :=
  s.regs rLen = cs.length ∧
  (s.arrs aL).length = cap ∧
  (s.arrs aR).length = cap ∧
  (s.arrs aG).length = cap ∧
  cs.length ≤ cap ∧
  ∀ i (hi : i < cs.length),
    (s.arrs aL)[i]? = some (cs[i]'hi).l ∧
    (s.arrs aR)[i]? = some (cs[i]'hi).r ∧
    (s.arrs aG)[i]? = some (cs[i]'hi).γ

theorem IsCandArray.of_eq {cs : List Candidate} {cap : ℕ} {aL aR aG : Arr} {rLen : Reg}
    {s s' : State} (h : IsCandArray cs cap aL aR aG rLen s)
    (hr : s'.regs rLen = s.regs rLen)
    (haL : s'.arrs aL = s.arrs aL)
    (haR : s'.arrs aR = s.arrs aR)
    (haG : s'.arrs aG = s.arrs aG) :
    IsCandArray cs cap aL aR aG rLen s' := by
  rcases h with ⟨h1, h2, h3, h4, h5, h6⟩
  refine ⟨by rw [hr, h1], by rw [haL, h2], by rw [haR, h3],
    by rw [haG, h4], h5, fun i hi => ?_⟩
  rw [haL, haR, haG]
  exact h6 i hi

theorem IsCandArray.append_singleton {cs : List Candidate} {I : Candidate} {cap : ℕ}
    {aL aR aG : Arr} {rLen : Reg} {s : State}
    (h : IsCandArray cs cap aL aR aG rLen s)
    (hlt : cs.length < cap)
    (hneLR : aL ≠ aR) (hneLG : aL ≠ aG) (hneRG : aR ≠ aG) :
    let s₁ := s.writeArr aL cs.length I.l
    let s₂ := s₁.writeArr aR cs.length I.r
    let s₃ := s₂.writeArr aG cs.length I.γ
    let s₄ := s₃.setReg rLen (cs.length + 1)
    IsCandArray (cs ++ [I]) cap aL aR aG rLen s₄ := by
  intro s₁ s₂ s₃ s₄
  rcases h with ⟨_, hlenL, hlenR, hlenG, _, hget⟩
  have haL_eq : s₄.arrs aL = (s.arrs aL).set cs.length I.l := by
    simp [s₄, s₃, s₂, s₁, hneLR, hneLG]
  have haR_eq : s₄.arrs aR = (s.arrs aR).set cs.length I.r := by
    simp [s₄, s₃, s₂, s₁, hneRG, hneLR.symm]
  have haG_eq : s₄.arrs aG = (s.arrs aG).set cs.length I.γ := by
    simp [s₄, s₃, s₂, s₁, hneRG.symm, hneLG.symm]
  refine ⟨by simp [s₄], by simp [haL_eq, hlenL], by simp [haR_eq, hlenR],
    by simp [haG_eq, hlenG], by simp; omega, fun i hi => ?_⟩
  simp only [List.length_append, List.length_singleton] at hi
  rw [haL_eq, haR_eq, haG_eq]
  by_cases hieq : i = cs.length
  · subst hieq
    simp [hlenL, hlenR, hlenG, hlt]
  · have hilt : i < cs.length := by omega
    rw [List.getElem?_set_ne (by omega), List.getElem?_set_ne (by omega),
      List.getElem?_set_ne (by omega), List.getElem_append_left hilt]
    exact hget i hilt

/-! ### Part 2: Mathematical Lemmas for Candidate Generation -/

/-- Prefix of cyclic distance-`d` candidates for bridge `γ` with attachment list `t`,
after scanning the first `k` indices `0 .. k - 1`. -/
def stepCandsOf (d γ : ℕ) (t : List ℕ) (k : ℕ) : List Candidate :=
  ((List.range k).filterMap fun i =>
    if h : 0 < t.length then
      let a := t[i % t.length]'(Nat.mod_lt _ h)
      let b := t[(i + d) % t.length]'(Nat.mod_lt _ h)
      if a = b then none else some (a, b)
    else none).map (fun p => ⟨min p.1 p.2, max p.1 p.2, γ⟩)

@[simp]
theorem stepCandsOf_zero (d γ : ℕ) (t : List ℕ) : stepCandsOf d γ t 0 = [] := rfl

theorem stepCandsOf_succ (d γ : ℕ) (t : List ℕ) {i : ℕ} (hi : i < t.length) :
    stepCandsOf d γ t (i + 1) =
      stepCandsOf d γ t i ++
        let a := t[i]'hi
        let b := t[(i + d) % t.length]'(Nat.mod_lt _ (by omega))
        if a = b then [] else [⟨min a b, max a b, γ⟩] := by
  have hpos : 0 < t.length := by omega
  have hmod : i % t.length = i := Nat.mod_eq_of_lt hi
  unfold stepCandsOf
  rw [List.range_succ, List.filterMap_append, List.map_append]
  simp only [List.filterMap_cons, List.filterMap_nil, hpos, ↓reduceDIte]
  have ha : t[i % t.length]'(Nat.mod_lt _ hpos) = t[i]'hi := by simp [hmod]
  rw [ha]
  split_ifs <;> rfl

theorem candidatesOfIndices_eq_stepCandsOf (γ : ℕ) (t : List ℕ) :
    candidatesOfIndices γ t = stepCandsOf 1 γ t t.length ++ stepCandsOf 2 γ t t.length := by
  unfold candidatesOfIndices attachmentCandidates stepCandsOf stepCandidates
  rw [List.map_append]

theorem length_stepCandsOf_le (d γ : ℕ) (t : List ℕ) (k : ℕ) :
    (stepCandsOf d γ t k).length ≤ k := by
  unfold stepCandsOf
  rw [List.length_map]
  exact (List.length_filterMap_le _ _).trans (by simp)

/-- Prefix of `allBridgeCandidates H T bridges` across bridges `0 .. k - 1`. -/
def candsUpTo (H : SimpleGraph (Fin n)) [DecidableRel H.Adj]
    (T : List (Fin n)) (bridges : List (BridgeData (Fin n))) (k : ℕ) : List Candidate :=
  (List.range k).flatMap (fun γ =>
    match bridges[γ]? with
    | some bd => candidatesOfIndices γ (bd.attachmentIndices H T)
    | none => [])

@[simp]
theorem candsUpTo_zero (H : SimpleGraph (Fin n)) [DecidableRel H.Adj]
    (T : List (Fin n)) (bridges : List (BridgeData (Fin n))) :
    candsUpTo H T bridges 0 = [] := rfl

theorem candsUpTo_succ (H : SimpleGraph (Fin n)) [DecidableRel H.Adj]
    (T : List (Fin n)) (bridges : List (BridgeData (Fin n))) {γ : ℕ} (hγ : γ < bridges.length) :
    candsUpTo H T bridges (γ + 1) =
      candsUpTo H T bridges γ ++
        candidatesOfIndices γ ((bridges[γ]'hγ).attachmentIndices H T) := by
  unfold candsUpTo
  rw [List.range_succ, List.flatMap_append, List.flatMap_singleton]
  simp [List.getElem?_eq_getElem hγ]

theorem candsUpTo_length (H : SimpleGraph (Fin n)) [DecidableRel H.Adj]
    (T : List (Fin n)) (bridges : List (BridgeData (Fin n))) :
    candsUpTo H T bridges bridges.length = allBridgeCandidates H T bridges := by
  unfold candsUpTo allBridgeCandidates
  congr 1
  funext γ
  cases bridges[γ]? <;> rfl

theorem length_candsUpTo_le_two_mul_attOffset (H : SimpleGraph (Fin n)) [DecidableRel H.Adj]
    (T : List (Fin n)) (bridges : List (BridgeData (Fin n))) :
    ∀ {γ : ℕ}, γ ≤ bridges.length →
      (candsUpTo H T bridges γ).length ≤ 2 * attOffset H T bridges γ
  | 0, _ => by simp [attOffset_zero]
  | γ + 1, hγ => by
    have hlt : γ < bridges.length := by omega
    rw [candsUpTo_succ H T bridges hlt, List.length_append, attOffset_succ H T bridges hlt,
      Nat.mul_add]
    exact Nat.add_le_add (length_candsUpTo_le_two_mul_attOffset H T bridges (by omega))
      (length_candidatesOfIndices_le γ _)

theorem length_candsUpTo_add_att_le (H : SimpleGraph (Fin n)) [DecidableRel H.Adj]
    (T : List (Fin n)) (bridges : List (BridgeData (Fin n))) {γ : ℕ} (hγ : γ < bridges.length) :
    (candsUpTo H T bridges γ).length +
      2 * ((bridges[γ]'hγ).attachmentIndices H T).length ≤
      2 * totalAttachments H T bridges := by
  have h1 := length_candsUpTo_le_two_mul_attOffset H T bridges (le_of_lt hγ)
  have h2 := attOffset_succ H T bridges hγ
  have h3 := attOffset_mono H T bridges (show γ + 1 ≤ bridges.length by omega) le_rfl
  rw [attOffset_length] at h3
  omega

theorem sum_range_attachmentIndices_length (H : SimpleGraph (Fin n)) [DecidableRel H.Adj]
    (T : List (Fin n)) (bridges : List (BridgeData (Fin n))) :
    ∀ {γ : ℕ}, γ ≤ bridges.length →
      ∑ j ∈ Finset.range γ,
        (match bridges[j]? with
          | some bd => (bd.attachmentIndices H T).length
          | none => 0) =
        attOffset H T bridges γ
  | 0, _ => by simp [attOffset_zero]
  | γ + 1, hγ => by
    have hlt : γ < bridges.length := by omega
    rw [Finset.sum_range_succ, sum_range_attachmentIndices_length H T bridges (by omega),
      List.getElem?_eq_getElem hlt, attOffset_succ H T bridges hlt]

/-! ### Part 3: Candidate Generation Program (`candGenProg`) -/

/-- Append candidate `(lExpr, rExpr, gExpr)` at index `rNumCand` in `(aCandL, aCandR, aCandG)`
and increment `rNumCand`. -/
def pushCandCmd (lExpr rExpr gExpr : Expr) : Cmd :=
  .seq (.write aCandL (.reg rNumCand) lExpr)
    (.seq (.write aCandR (.reg rNumCand) rExpr)
      (.seq (.write aCandG (.reg rNumCand) gExpr)
        (.assign rNumCand (.op .add (.reg rNumCand) (.const 1)))))

/-- Inner loop body for `stepCandsOf d`: at index `rM < rTmp2`, read `a = aAttEnt[rTmp1 + rM]`
and `b = aAttEnt[rTmp1 + (rM + d) % rTmp2]`; if `a ≠ b`, emit `(min a b, max a b, rG)`. -/
def stepCandBody (d : ℕ) : Cmd :=
  let r_st := rTmp1
  let r_h := rTmp2
  let r_g := rG
  let r_i := rM
  let r_a := rTmp3
  let r_b := rTmp4
  .seq (.assign r_a (.read aAttEnt (.op .add (.reg r_st) (.reg r_i))))
    (.seq (.assign r_b (.read aAttEnt
        (.op .add (.reg r_st) (.op .mod (.op .add (.reg r_i) (.const d)) (.reg r_h)))))
      (.ite (.op .eq (.reg r_a) (.reg r_b))
        .skip
        (.ite (.op .lt (.reg r_a) (.reg r_b))
          (pushCandCmd (.reg r_a) (.reg r_b) (.reg r_g))
          (pushCandCmd (.reg r_b) (.reg r_a) (.reg r_g)))))

/-- Outer loop body for bridge `γ = rG`: read `st = aAttSt[γ]`, `en = aAttEn[γ]`,
set `rTmp2 = en - st`, and run `stepCandBody 1` and `stepCandBody 2`. -/
def bridgeCandBody : Cmd :=
  let r_st := rTmp1
  let r_h := rTmp2
  let r_g := rG
  let r_i := rM
  .seq (.assign r_st (.read aAttSt (.reg r_g)))
    (.seq (.assign r_h (.op .sub (.read aAttEn (.reg r_g)) (.reg r_st)))
      (.seq (.seq (.assign r_i (.const 0)) (forUp r_i (.reg r_h) (stepCandBody 1)))
        (.seq (.assign r_i (.const 0)) (forUp r_i (.reg r_h) (stepCandBody 2)))))

/-- Complete candidate generation program: allocate `(aCandL, aCandR, aCandG)` of capacity
`2 * rTotAtt`, initialize `rNumCand := 0`, and scan all bridges `0 .. rNumBridges - 1`. -/
def candGenProg : Cmd :=
  .seq (.assign rCandCap (.op .mul (.const 2) (.reg rTotAtt)))
    (.seq (.alloc aCandL (.reg rCandCap))
      (.seq (.alloc aCandR (.reg rCandCap))
        (.seq (.alloc aCandG (.reg rCandCap))
          (.seq (.assign rNumCand (.const 0))
            (.seq (.assign rG (.const 0))
              (forUp rG (.reg rNumBridges) bridgeCandBody))))))

/-- Registers modified by `candGenProg`. -/
def candGenRegs : List Reg :=
  [rNumCand, rCandCap, rG, rM, rTmp1, rTmp2, rTmp3, rTmp4]

/-- Arrays modified by `candGenProg`. -/
def candGenArrs : List Arr :=
  [aCandL, aCandR, aCandG]

theorem read_eval {w : ℕ} {a : Arr} {idx : Expr} {i val : ℕ} {s : State}
    (hidx : idx.eval w s = some i)
    (hget : (s.arrs a)[i]? = some val) (hval_w : val < 2 ^ w) :
    (Expr.read a idx).eval w s = some val := by
  obtain ⟨hlt, hval⟩ := List.getElem?_eq_some_iff.mp hget
  unfold Expr.eval
  rw [hidx]
  simp [hlt, hval, checkWord, hval_w]

theorem stepCandBody_exec {w : ℕ} (d γ : ℕ) (t : List ℕ) (cs₀ : List Candidate)
    (cap st i : ℕ) (hi : i < t.length) (s : State)
    (hr_st : s.regs rTmp1 = st)
    (hr_h : s.regs rTmp2 = t.length)
    (hr_g : s.regs rG = γ)
    (hr_i : s.regs rM = i)
    (hcand : IsCandArray cs₀ cap aCandL aCandR aCandG rNumCand s)
    (hcap : cs₀.length + 1 ≤ cap)
    (ht_slice : ∀ k (hk : k < t.length), (s.arrs aAttEnt)[st + k]? = some (t[k]'hk))
    (hd_w : d < 2 ^ w) (hγ_w : γ < 2 ^ w) (hw1 : 1 < 2 ^ w)
    (hst_w : st + t.length + d < 2 ^ w) (ht_val_w : ∀ x ∈ t, x < 2 ^ w)
    (hnum_w : cs₀.length + 1 < 2 ^ w) :
    ∃ s' k,
      Exec w (stepCandBody d) s s' k ∧
      k ≤ 36 ∧
      Keeps [rTmp3, rTmp4, rNumCand] [aCandL, aCandR, aCandG] s s' ∧
      IsCandArray
        (cs₀ ++
          let a := t[i]'hi
          let b := t[(i + d) % t.length]'(Nat.mod_lt _ (by omega))
          if a = b then [] else [⟨min a b, max a b, γ⟩])
        cap aCandL aCandR aCandG rNumCand s' := by
  have hpos : 0 < t.length := by omega
  set a := t[i]'hi
  set j := (i + d) % t.length
  have hj : j < t.length := Nat.mod_lt _ hpos
  set b := t[j]'hj
  have ha_w : a < 2 ^ w := ht_val_w a (List.getElem_mem hi)
  have hb_w : b < 2 ^ w := ht_val_w b (List.getElem_mem hj)
  have hst_i_w : st + i < 2 ^ w := by omega
  have hst_j_w : st + j < 2 ^ w := by omega
  have h_eval_a : (Expr.read aAttEnt (.op .add (.reg rTmp1) (.reg rM))).eval w s =
      some a := by
    refine read_eval ?_ (ht_slice i hi) ha_w
    simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hr_st, hr_i,
      show st < 2 ^ w by omega, show i < 2 ^ w by omega, hst_i_w]
  let s₁ := s.setReg rTmp3 a
  have hex₁ : Exec w (.assign rTmp3 (.read aAttEnt (.op .add (.reg rTmp1) (.reg rM))))
      s s₁ 5 := .assign h_eval_a
  have h_eval_b : (Expr.read aAttEnt
      (.op .add (.reg rTmp1) (.op .mod (.op .add (.reg rM) (.const d)) (.reg rTmp2)))).eval w s₁ =
      some b := by
    have hmod_eval : (Expr.op .mod (.op .add (.reg rM) (.const d)) (.reg rTmp2)).eval w s₁ =
        some j := by
      simp [s₁, Expr.eval, BinOp.eval, BinOp.raw, checkWord, hr_i, hr_h, hd_w,
        show i < 2 ^ w by omega, show i + d < 2 ^ w by omega,
        show t.length < 2 ^ w by omega, show t.length ≠ 0 by omega,
        show j < 2 ^ w by omega, j]
    have h_st_eval : (Expr.reg rTmp1).eval w s₁ = some st := by
      simp [s₁, Expr.eval, checkWord, hr_st, show st < 2 ^ w by omega]
    refine read_eval (i := st + j) ?_ (by simpa [s₁, b] using ht_slice j hj) hb_w
    unfold Expr.eval
    rw [h_st_eval, hmod_eval]
    simp [BinOp.eval, BinOp.raw, checkWord, hst_j_w]
  let s₂ := s₁.setReg rTmp4 b
  have hex₂ : Exec w (.assign rTmp4 (.read aAttEnt
      (.op .add (.reg rTmp1) (.op .mod (.op .add (.reg rM) (.const d)) (.reg rTmp2)))))
      s₁ s₂ 9 := .assign h_eval_b
  have hk₂ : Keeps [rTmp3, rTmp4, rNumCand] [aCandL, aCandR, aCandG] s s₂ :=
    ((Keeps.refl _ _ s).setReg (by decide) _).setReg (by decide) _
  by_cases hab : a = b
  · have hcond : (Expr.op .eq (.reg rTmp3) (.reg rTmp4)).eval w s₂ = some 1 := by
      simp [s₂, s₁, Expr.eval, BinOp.eval, BinOp.raw, checkWord, hab, hb_w, hw1]
    have hex₃ : Exec w (.ite (.op .eq (.reg rTmp3) (.reg rTmp4)) .skip
        (.ite (.op .lt (.reg rTmp3) (.reg rTmp4))
          (pushCandCmd (.reg rTmp3) (.reg rTmp4) (.reg rG))
          (pushCandCmd (.reg rTmp4) (.reg rTmp3) (.reg rG)))) s₂ s₂ (3 + 1) :=
      .ite_true hcond (by decide) (.skip _)
    refine ⟨s₂, _, .seq hex₁ (.seq hex₂ hex₃), by omega, hk₂, ?_⟩
    simp only [hab, ↓reduceIte, List.append_nil]
    exact hcand.of_eq (s' := s₂) (by simp [s₂, s₁]) rfl rfl rfl
  · have hcond : (Expr.op .eq (.reg rTmp3) (.reg rTmp4)).eval w s₂ = some 0 := by
      simp [s₂, s₁, Expr.eval, BinOp.eval, BinOp.raw, checkWord, hab, ha_w, hb_w,
        show (0 : ℕ) < 2 ^ w by omega]
    have hcand₂ : IsCandArray cs₀ cap aCandL aCandR aCandG rNumCand s₂ :=
      hcand.of_eq (s' := s₂) (by simp [s₂, s₁]) rfl rfl rfl
    have hnum₂ : s₂.regs rNumCand = cs₀.length := hcand₂.1
    have hlenL₂ : (s₂.arrs aCandL).length = cap := hcand₂.2.1
    have hlenR₂ : (s₂.arrs aCandR).length = cap := hcand₂.2.2.1
    have hlenG₂ : (s₂.arrs aCandG).length = cap := hcand₂.2.2.2.1
    have hnum_w₀ : cs₀.length < 2 ^ w := by omega
    by_cases hlt : a < b
    · have hlt_cond : (Expr.op .lt (.reg rTmp3) (.reg rTmp4)).eval w s₂ = some 1 := by
        simp [s₂, s₁, Expr.eval, BinOp.eval, BinOp.raw, checkWord, hlt, ha_w, hb_w, hw1]
      let s₃ := s₂.writeArr aCandL cs₀.length a
      have hex_w1 : Exec w (.write aCandL (.reg rNumCand) (.reg rTmp3)) s₂ s₃ 3 :=
        .write (by simp [Expr.eval, checkWord, hnum₂, hnum_w₀])
          (by simp [s₂, s₁, Expr.eval, checkWord, ha_w]) (by omega)
      let s₄ := s₃.writeArr aCandR cs₀.length b
      have hex_w2 : Exec w (.write aCandR (.reg rNumCand) (.reg rTmp4)) s₃ s₄ 3 :=
        .write (by simp [s₃, Expr.eval, checkWord, hnum₂, hnum_w₀])
          (by simp [s₃, s₂, s₁, Expr.eval, checkWord, hb_w]) (by simp [s₃]; omega)
      let s₅ := s₄.writeArr aCandG cs₀.length γ
      have hex_w3 : Exec w (.write aCandG (.reg rNumCand) (.reg rG)) s₄ s₅ 3 :=
        .write (by simp [s₄, s₃, Expr.eval, checkWord, hnum₂, hnum_w₀])
          (by simp [s₄, s₃, s₂, s₁, Expr.eval, checkWord, hr_g, hγ_w])
          (by simp [s₄, s₃]; omega)
      let s₆ := s₅.setReg rNumCand (cs₀.length + 1)
      have hex_inc : Exec w (.assign rNumCand (.op .add (.reg rNumCand) (.const 1))) s₅ s₆ 4 :=
        .assign (by simp [s₅, s₄, s₃, Expr.eval, BinOp.eval, BinOp.raw, checkWord,
          hnum₂, hnum_w₀, hw1, hnum_w])
      have hex_push : Exec w (pushCandCmd (.reg rTmp3) (.reg rTmp4) (.reg rG)) s₂ s₆ (3 + (3 + (3 + 4))) :=
        .seq hex_w1 (.seq hex_w2 (.seq hex_w3 hex_inc))
      have hex_inner : Exec w (.ite (.op .lt (.reg rTmp3) (.reg rTmp4))
          (pushCandCmd (.reg rTmp3) (.reg rTmp4) (.reg rG))
          (pushCandCmd (.reg rTmp4) (.reg rTmp3) (.reg rG))) s₂ s₆ (3 + (3 + (3 + (3 + 4)))) :=
        .ite_true hlt_cond (by decide) hex_push
      have hex₃ : Exec w (.ite (.op .eq (.reg rTmp3) (.reg rTmp4)) .skip
          (.ite (.op .lt (.reg rTmp3) (.reg rTmp4))
            (pushCandCmd (.reg rTmp3) (.reg rTmp4) (.reg rG))
            (pushCandCmd (.reg rTmp4) (.reg rTmp3) (.reg rG)))) s₂ s₆ (3 + (3 + (3 + (3 + (3 + 4))))) :=
        .ite_false hcond hex_inner
      have hk₆ : Keeps [rTmp3, rTmp4, rNumCand] [aCandL, aCandR, aCandG] s s₆ :=
        (((hk₂.writeArr (by decide) _ _).writeArr (by decide) _ _).writeArr (by decide) _ _).setReg
          (by decide) _
      refine ⟨s₆, _, .seq hex₁ (.seq hex₂ hex₃), by omega, hk₆, ?_⟩
      have hmin : min a b = a := Nat.min_eq_left (le_of_lt hlt)
      have hmax : max a b = b := Nat.max_eq_right (le_of_lt hlt)
      simp only [hab, ↓reduceIte, hmin, hmax]
      exact hcand₂.append_singleton (I := ⟨a, b, γ⟩) (by omega)
        (by decide) (by decide) (by decide)
    · have hlt_cond : (Expr.op .lt (.reg rTmp3) (.reg rTmp4)).eval w s₂ = some 0 := by
        simp [s₂, s₁, Expr.eval, BinOp.eval, BinOp.raw, checkWord, hlt, ha_w, hb_w,
          show (0 : ℕ) < 2 ^ w by omega]
      let s₃ := s₂.writeArr aCandL cs₀.length b
      have hex_w1 : Exec w (.write aCandL (.reg rNumCand) (.reg rTmp4)) s₂ s₃ 3 :=
        .write (by simp [Expr.eval, checkWord, hnum₂, hnum_w₀])
          (by simp [s₂, s₁, Expr.eval, checkWord, hb_w]) (by omega)
      let s₄ := s₃.writeArr aCandR cs₀.length a
      have hex_w2 : Exec w (.write aCandR (.reg rNumCand) (.reg rTmp3)) s₃ s₄ 3 :=
        .write (by simp [s₃, Expr.eval, checkWord, hnum₂, hnum_w₀])
          (by simp [s₃, s₂, s₁, Expr.eval, checkWord, ha_w]) (by simp [s₃]; omega)
      let s₅ := s₄.writeArr aCandG cs₀.length γ
      have hex_w3 : Exec w (.write aCandG (.reg rNumCand) (.reg rG)) s₄ s₅ 3 :=
        .write (by simp [s₄, s₃, Expr.eval, checkWord, hnum₂, hnum_w₀])
          (by simp [s₄, s₃, s₂, s₁, Expr.eval, checkWord, hr_g, hγ_w])
          (by simp [s₄, s₃]; omega)
      let s₆ := s₅.setReg rNumCand (cs₀.length + 1)
      have hex_inc : Exec w (.assign rNumCand (.op .add (.reg rNumCand) (.const 1))) s₅ s₆ 4 :=
        .assign (by simp [s₅, s₄, s₃, Expr.eval, BinOp.eval, BinOp.raw, checkWord,
          hnum₂, hnum_w₀, hw1, hnum_w])
      have hex_push : Exec w (pushCandCmd (.reg rTmp4) (.reg rTmp3) (.reg rG)) s₂ s₆ (3 + (3 + (3 + 4))) :=
        .seq hex_w1 (.seq hex_w2 (.seq hex_w3 hex_inc))
      have hex_inner : Exec w (.ite (.op .lt (.reg rTmp3) (.reg rTmp4))
          (pushCandCmd (.reg rTmp3) (.reg rTmp4) (.reg rG))
          (pushCandCmd (.reg rTmp4) (.reg rTmp3) (.reg rG))) s₂ s₆ (3 + (3 + (3 + (3 + 4)))) :=
        .ite_false hlt_cond hex_push
      have hex₃ : Exec w (.ite (.op .eq (.reg rTmp3) (.reg rTmp4)) .skip
          (.ite (.op .lt (.reg rTmp3) (.reg rTmp4))
            (pushCandCmd (.reg rTmp3) (.reg rTmp4) (.reg rG))
            (pushCandCmd (.reg rTmp4) (.reg rTmp3) (.reg rG)))) s₂ s₆ (3 + (3 + (3 + (3 + (3 + 4))))) :=
        .ite_false hcond hex_inner
      have hk₆ : Keeps [rTmp3, rTmp4, rNumCand] [aCandL, aCandR, aCandG] s s₆ :=
        (((hk₂.writeArr (by decide) _ _).writeArr (by decide) _ _).writeArr (by decide) _ _).setReg
          (by decide) _
      refine ⟨s₆, _, .seq hex₁ (.seq hex₂ hex₃), by omega, hk₆, ?_⟩
      have hle_ba : b ≤ a := by omega
      have hmin : min a b = b := Nat.min_eq_right hle_ba
      have hmax : max a b = a := Nat.max_eq_left hle_ba
      simp only [hab, ↓reduceIte, hmin, hmax]
      exact hcand₂.append_singleton (I := ⟨b, a, γ⟩) (by omega)
        (by decide) (by decide) (by decide)

private theorem mem_stepLoopRegs_of_mem_stepBodyRegs {r : Reg}
    (hr : r ∈ ([rTmp3, rTmp4, rNumCand] : List Reg)) :
    r ∈ ([rM, rTmp3, rTmp4, rNumCand] : List Reg) := by
  revert r hr; decide

theorem stepCandLoop_exec {w : ℕ} (d γ : ℕ) (t : List ℕ) (cs₀ : List Candidate)
    (cap st : ℕ) (s₀ : State)
    (hr_st : s₀.regs rTmp1 = st)
    (hr_h : s₀.regs rTmp2 = t.length)
    (hr_g : s₀.regs rG = γ)
    (hcand₀ : IsCandArray cs₀ cap aCandL aCandR aCandG rNumCand s₀)
    (hcap : cs₀.length + t.length ≤ cap)
    (ht_slice : ∀ k (hk : k < t.length), (s₀.arrs aAttEnt)[st + k]? = some (t[k]'hk))
    (hd_w : d < 2 ^ w) (hγ_w : γ < 2 ^ w) (hw1 : 1 < 2 ^ w)
    (hst_w : st + t.length + d < 2 ^ w) (ht_val_w : ∀ x ∈ t, x < 2 ^ w)
    (hnum_w : cs₀.length + t.length < 2 ^ w) :
    ∃ s' k,
      Exec w (.seq (.assign rM (.const 0)) (forUp rM (.reg rTmp2) (stepCandBody d)))
        s₀ s' k ∧
      k ≤ 6 + 44 * t.length ∧
      Keeps [rM, rTmp3, rTmp4, rNumCand] [aCandL, aCandR, aCandG] s₀ s' ∧
      IsCandArray (cs₀ ++ stepCandsOf d γ t t.length) cap aCandL aCandR aCandG rNumCand s' := by
  let Inv (i : ℕ) (s : State) : Prop :=
    s.regs rM = i ∧
    Keeps [rM, rTmp3, rTmp4, rNumCand] [aCandL, aCandR, aCandG] s₀ s ∧
    IsCandArray (cs₀ ++ stepCandsOf d γ t i) cap aCandL aCandR aCandG rNumCand s
  let s₁ := s₀.setReg rM 0
  have hex_init : Exec w (.assign rM (.const 0)) s₀ s₁ 2 :=
    .assign (by simp [Expr.eval, checkWord, show (0 : ℕ) < 2 ^ w by omega])
  have hInv₀ : Inv 0 s₁ :=
    ⟨by simp [s₁], (Keeps.refl _ _ s₀).setReg (by decide) _,
      by simpa [stepCandsOf_zero] using hcand₀.of_eq (s' := s₁) (by simp [s₁]) rfl rfl rfl⟩
  have hloop : ⦃Inv 0⦄[w] forUp rM (.reg rTmp2) (stepCandBody d) ⦃Inv t.length⦄ ≤
      fun _ => (Expr.reg rTmp2).cost + 2 + t.length * ((Expr.reg rTmp2).cost + 6 + 36) := by
    apply Triple.forUp_const Inv t.length 36 hw1 (by omega)
    · intro i _ s ⟨hr_i, hk, _⟩
      have hr_h_s : s.regs rTmp2 = t.length := (hk.1 rTmp2 (by decide)).trans hr_h
      exact ⟨hr_i, by simp [Expr.eval, checkWord, hr_h_s, show t.length < 2 ^ w by omega]⟩
    · intro i hi s ⟨hr_i, hk, hcand_s⟩
      have hr_st_s : s.regs rTmp1 = st := (hk.1 rTmp1 (by decide)).trans hr_st
      have hr_h_s : s.regs rTmp2 = t.length := (hk.1 rTmp2 (by decide)).trans hr_h
      have hr_g_s : s.regs rG = γ := (hk.1 rG (by decide)).trans hr_g
      have hlen_step : (stepCandsOf d γ t i).length ≤ i := length_stepCandsOf_le d γ t i
      have hlen_tot : (cs₀ ++ stepCandsOf d γ t i).length + 1 ≤ cap := by
        rw [List.length_append]; omega
      have hnum_w_i : (cs₀ ++ stepCandsOf d γ t i).length + 1 < 2 ^ w := by
        rw [List.length_append]; omega
      have ht_slice_s : ∀ k (hk : k < t.length), (s.arrs aAttEnt)[st + k]? = some (t[k]'hk) := by
        rw [hk.2 aAttEnt (by decide)]
        exact ht_slice
      obtain ⟨s', k, hex, hk_le, hk_body, hcand'⟩ :=
        stepCandBody_exec d γ t (cs₀ ++ stepCandsOf d γ t i) cap st i hi s
          hr_st_s hr_h_s hr_g_s hr_i hcand_s hlen_tot ht_slice_s
          hd_w hγ_w hw1 hst_w ht_val_w hnum_w_i
      refine ⟨s', k, hex, hk_le, ⟨by simp, ?_, ?_⟩, ?_⟩
      · exact (hk.trans hk_body (fun _ hr => mem_stepLoopRegs_of_mem_stepBodyRegs hr)
          (fun _ ha => ha)).setReg (by decide) _
      · rw [stepCandsOf_succ d γ t hi, ← List.append_assoc]
        exact hcand'.of_eq (s' := s'.setReg rM (i + 1)) (by simp) rfl rfl rfl
      · rw [hk_body.1 rM (by decide), hr_i]
  obtain ⟨s', k_loop, hex_loop, hk_loop, _, hk_final, hcand_final⟩ := hloop s₁ hInv₀
  refine ⟨s', 2 + k_loop, .seq hex_init hex_loop, ?_, hk_final, hcand_final⟩
  simp only [Expr.cost] at hk_loop
  omega

/-- **Execution of `bridgeCandBody` for bridge `γ < bridges.length`.** -/
theorem bridgeCandBody_exec {w : ℕ} (H : SimpleGraph (Fin n)) [DecidableRel H.Adj]
    (T : List (Fin n)) (bridges : List (BridgeData (Fin n)))
    {γ : ℕ} (hγ : γ < bridges.length) (cap : ℕ) (s₀ : State)
    (hr_g : s₀.regs rG = γ)
    (hatt : ∃ st en, IsListAt aAttSt aAttEn aAttEnt γ st en
      ((bridges[γ]'hγ).attachmentIndices H T) s₀)
    (hcand₀ : IsCandArray (candsUpTo H T bridges γ) cap aCandL aCandR aCandG rNumCand s₀)
    (hcap : (candsUpTo H T bridges γ).length +
      2 * ((bridges[γ]'hγ).attachmentIndices H T).length ≤ cap)
    (hcap_w : cap < 2 ^ w)
    (hγ_w : γ < 2 ^ w) (hw2 : 2 < 2 ^ w)
    (hent_w : (s₀.arrs aAttEnt).length + 2 < 2 ^ w)
    (hT_w : T.length < 2 ^ w) :
    ∃ s' k,
      Exec w bridgeCandBody s₀ s' k ∧
      k ≤ 21 + 88 * ((bridges[γ]'hγ).attachmentIndices H T).length ∧
      Keeps [rTmp1, rTmp2, rM, rTmp3, rTmp4, rNumCand] [aCandL, aCandR, aCandG] s₀ s' ∧
      IsCandArray (candsUpTo H T bridges (γ + 1)) cap aCandL aCandR aCandG rNumCand s' := by
  set t := (bridges[γ]'hγ).attachmentIndices H T
  obtain ⟨st, en, hγ_st, hγ_en, hen_ent, hdiff, hst_eq, hen_eq, hst_le_en, hslice⟩ := hatt
  have hen_w : en < 2 ^ w := by omega
  have hst_w : st < 2 ^ w := by omega
  have ht_w : t.length < 2 ^ w := by omega
  have h_eval_st : (Expr.read aAttSt (.reg rG)).eval w s₀ = some st :=
    read_reg_eval hr_g hγ_w (by rw [List.getElem?_eq_getElem hγ_st, hst_eq]) hst_w
  let s₁ := s₀.setReg rTmp1 st
  have hex₁ : Exec w (.assign rTmp1 (.read aAttSt (.reg rG))) s₀ s₁ 3 :=
    .assign h_eval_st
  have h_eval_en : (Expr.read aAttEn (.reg rG)).eval w s₁ = some en :=
    read_reg_eval (by simp [s₁, hr_g]) hγ_w
      (by simp [s₁, List.getElem?_eq_getElem hγ_en, hen_eq]) hen_w
  have h_eval_h : (Expr.op .sub (.read aAttEn (.reg rG)) (.reg rTmp1)).eval w s₁ =
      some t.length := by
    have h_st_s1 : (Expr.reg rTmp1).eval w s₁ = some st := by
      simp [s₁, Expr.eval, checkWord, hst_w]
    unfold Expr.eval
    rw [h_eval_en, h_st_s1]
    simp [BinOp.eval, BinOp.raw, checkWord, ht_w, hdiff]
  let s₂ := s₁.setReg rTmp2 t.length
  have hex₂ : Exec w (.assign rTmp2 (.op .sub (.read aAttEn (.reg rG)) (.reg rTmp1)))
      s₁ s₂ 5 := .assign h_eval_h
  have hcand₂ : IsCandArray (candsUpTo H T bridges γ) cap aCandL aCandR aCandG rNumCand s₂ :=
    hcand₀.of_eq (s' := s₂) (by simp [s₂, s₁]) rfl rfl rfl
  have ht_slice : ∀ k (hk : k < t.length), (s₂.arrs aAttEnt)[st + k]? = some (t[k]'hk) := by
    intro k hk
    have hlt : st + k < (s₀.arrs aAttEnt).length := by omega
    simp only [s₂, s₁, State.setReg_arrs, List.getElem?_eq_getElem hlt]
    exact congrArg some (hslice k hk)
  have ht_val_w : ∀ x ∈ t, x < 2 ^ w := by
    intro x hx
    have hlt := (bridges[γ]'hγ).mem_attachmentIndices_lt H hx
    omega
  obtain ⟨s₃, k₃, hex₃, hk₃, hkeep₃, hcand₃⟩ :=
    stepCandLoop_exec 1 γ t (candsUpTo H T bridges γ) cap st s₂
      (by simp [s₂, s₁]) (by simp [s₂]) (by simp [s₂, s₁, hr_g])
      hcand₂ (by omega) ht_slice (by omega) hγ_w (by omega) (by omega) ht_val_w (by omega)
  have hr_st₃ : s₃.regs rTmp1 = st := by
    rw [hkeep₃.1 rTmp1 (by decide)]; simp [s₂, s₁]
  have hr_h₃ : s₃.regs rTmp2 = t.length := by
    rw [hkeep₃.1 rTmp2 (by decide)]; simp [s₂]
  have hr_g₃ : s₃.regs rG = γ := by
    rw [hkeep₃.1 rG (by decide)]; simp [s₂, s₁, hr_g]
  have ht_slice₃ : ∀ k (hk : k < t.length), (s₃.arrs aAttEnt)[st + k]? = some (t[k]'hk) := by
    rw [hkeep₃.2 aAttEnt (by decide)]
    exact ht_slice
  have hlen_step1 : (stepCandsOf 1 γ t t.length).length ≤ t.length :=
    length_stepCandsOf_le 1 γ t t.length
  obtain ⟨s₄, k₄, hex₄, hk₄, hkeep₄, hcand₄⟩ :=
    stepCandLoop_exec 2 γ t (candsUpTo H T bridges γ ++ stepCandsOf 1 γ t t.length) cap st s₃
      hr_st₃ hr_h₃ hr_g₃ hcand₃
      (by rw [List.length_append]; omega) ht_slice₃
      (by omega) hγ_w (by omega) (by omega) ht_val_w
      (by rw [List.length_append]; omega)
  refine ⟨s₄, _,
    .seq hex₁ (.seq hex₂ (.seq hex₃ hex₄)),
    by omega, ?_, ?_⟩
  · have hk₂ : Keeps [rTmp1, rTmp2, rM, rTmp3, rTmp4, rNumCand]
        [aCandL, aCandR, aCandG] s₀ s₂ :=
      ((Keeps.refl _ _ s₀).setReg (by decide) _).setReg (by decide) _
    exact (hk₂.trans hkeep₃ (fun r hr => by revert r hr; decide) (fun _ ha => ha)).trans
      hkeep₄ (fun r hr => by revert r hr; decide) (fun _ ha => ha)
  · rw [candsUpTo_succ H T bridges hγ, candidatesOfIndices_eq_stepCandsOf, ← List.append_assoc]
    exact hcand₄

/-- **Execution of `candGenProg`.**
Generates `allBridgeCandidates H T bridges` into `(aCandL, aCandR, aCandG)` with length in
`rNumCand`, in time `O(1 + bridges.length + totalAttachments H T bridges)`. -/
theorem candGenProg_exec {w : ℕ} (H : SimpleGraph (Fin n)) [DecidableRel H.Adj]
    (T : List (Fin n)) (bridges : List (BridgeData (Fin n))) (s₀ : State)
    (hrB : s₀.regs rNumBridges = bridges.length)
    (hrTot : s₀.regs rTotAtt = totalAttachments H T bridges)
    (hatt : IsListFamily bridges.length aAttSt aAttEn aAttEnt
      (fun γ : Fin bridges.length => (bridges[γ.1]'γ.2).attachmentIndices H T) s₀)
    (hw2 : 2 < 2 ^ w)
    (hB_w : bridges.length < 2 ^ w)
    (hcap_w : 2 * totalAttachments H T bridges < 2 ^ w)
    (hent_w : (s₀.arrs aAttEnt).length + 2 < 2 ^ w)
    (hT_w : T.length < 2 ^ w) :
    ∃ s' k,
      Exec w candGenProg s₀ s' k ∧
      k ≤ 17 + 29 * bridges.length + 94 * totalAttachments H T bridges ∧
      Keeps candGenRegs candGenArrs s₀ s' ∧
      IsCandArray (allBridgeCandidates H T bridges)
        (2 * totalAttachments H T bridges) aCandL aCandR aCandG rNumCand s' := by
  set cap := 2 * totalAttachments H T bridges
  have htot_w : totalAttachments H T bridges < 2 ^ w := by omega
  have h_eval_cap : (Expr.op .mul (.const 2) (.reg rTotAtt)).eval w s₀ = some cap := by
    simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hrTot, hw2, htot_w, hcap_w, cap]
  let s₁ := s₀.setReg rCandCap cap
  have hex₁ : Exec w (.assign rCandCap (.op .mul (.const 2) (.reg rTotAtt))) s₀ s₁ 4 :=
    .assign h_eval_cap
  let s₂ := s₁.setArr aCandL (List.replicate cap 0)
  have hex₂ : Exec w (.alloc aCandL (.reg rCandCap)) s₁ s₂ (1 + cap) :=
    .alloc (by simp [s₁, Expr.eval, checkWord, hcap_w])
  let s₃ := s₂.setArr aCandR (List.replicate cap 0)
  have hex₃ : Exec w (.alloc aCandR (.reg rCandCap)) s₂ s₃ (1 + cap) :=
    .alloc (by simp [s₂, s₁, Expr.eval, checkWord, hcap_w])
  let s₄ := s₃.setArr aCandG (List.replicate cap 0)
  have hex₄ : Exec w (.alloc aCandG (.reg rCandCap)) s₃ s₄ (1 + cap) :=
    .alloc (by simp [s₃, s₂, s₁, Expr.eval, checkWord, hcap_w])
  let s₅ := s₄.setReg rNumCand 0
  have hex₅ : Exec w (.assign rNumCand (.const 0)) s₄ s₅ 2 :=
    .assign (by simp [Expr.eval, checkWord, show (0 : ℕ) < 2 ^ w by omega])
  let s₆ := s₅.setReg rG 0
  have hex₆ : Exec w (.assign rG (.const 0)) s₅ s₆ 2 :=
    .assign (by simp [Expr.eval, checkWord, show (0 : ℕ) < 2 ^ w by omega])
  let Inv (γ : ℕ) (s : State) : Prop :=
    s.regs rG = γ ∧
    Keeps candGenRegs candGenArrs s₀ s ∧
    IsCandArray (candsUpTo H T bridges γ) cap aCandL aCandR aCandG rNumCand s
  have hInv₀ : Inv 0 s₆ := by
    refine ⟨by simp [s₆], ?_, ?_⟩
    · exact ((((((Keeps.refl candGenRegs candGenArrs s₀).setReg (by decide) _).setArr
        (by decide) _).setArr (by decide) _).setArr (by decide) _).setReg (by decide) _).setReg
        (by decide) _
    · refine ⟨by simp [s₆, s₅], by simp [s₆, s₅, s₄, s₃, s₂],
        by simp [s₆, s₅, s₄, s₃], by simp [s₆, s₅, s₄], by simp, fun i hi => by simp at hi⟩
  let stepCost (γ : ℕ) : ℕ :=
    21 + 88 * (match bridges[γ]? with
      | some bd => (bd.attachmentIndices H T).length
      | none => 0)
  have hloop : ⦃Inv 0⦄[w] forUp rG (.reg rNumBridges) bridgeCandBody ⦃Inv bridges.length⦄ ≤
      fun _ => (Expr.reg rNumBridges).cost + 2 +
        ∑ γ ∈ Finset.range bridges.length,
          ((Expr.reg rNumBridges).cost + 6 + stepCost γ) := by
    apply Triple.forUp_sum Inv bridges.length stepCost (by omega) hB_w
    · intro γ _ s ⟨hr_g, hk, _⟩
      have hrB_s : s.regs rNumBridges = bridges.length :=
        (hk.1 rNumBridges (by decide)).trans hrB
      exact ⟨hr_g, by simp [Expr.eval, checkWord, hrB_s, hB_w]⟩
    · intro γ hγ s ⟨hr_g, hk, hcand_s⟩
      obtain ⟨st_γ, en_γ, hlist_γ⟩ := hatt.2.2 ⟨γ, hγ⟩
      have hatt_s : ∃ st en, IsListAt aAttSt aAttEn aAttEnt γ st en
          ((bridges[γ]'hγ).attachmentIndices H T) s :=
        ⟨st_γ, en_γ, IsListAt.of_arrs_eq hlist_γ
          (hk.2 aAttSt (by decide))
          (hk.2 aAttEn (by decide))
          (hk.2 aAttEnt (by decide))⟩
      have hent_w_s : (s.arrs aAttEnt).length + 2 < 2 ^ w := by
        rw [hk.2 aAttEnt (by decide)]; exact hent_w
      have hcap_γ : (candsUpTo H T bridges γ).length +
          2 * ((bridges[γ]'hγ).attachmentIndices H T).length ≤ cap :=
        length_candsUpTo_add_att_le H T bridges hγ
      obtain ⟨s', k, hex, hk_le, hk_body, hcand'⟩ :=
        bridgeCandBody_exec H T bridges hγ cap s hr_g hatt_s hcand_s hcap_γ
          hcap_w (by omega) hw2 hent_w_s hT_w
      have hcost : k ≤ stepCost γ := by
        dsimp only [stepCost]
        rw [List.getElem?_eq_getElem hγ]
        exact hk_le
      refine ⟨s', k, hex, hcost, ⟨by simp, ?_, ?_⟩, ?_⟩
      · exact (hk.trans hk_body (fun r hr => by revert r hr; decide)
          (fun _ ha => ha)).setReg (by decide) _
      · exact hcand'.of_eq (s' := s'.setReg rG (γ + 1)) (by simp) rfl rfl rfl
      · rw [hk_body.1 rG (by decide), hr_g]
  obtain ⟨s₇, k₇, hex₇, hk₇, _, hk_final, hcand_final⟩ := hloop s₆ hInv₀
  rw [candsUpTo_length] at hcand_final
  refine ⟨s₇, _,
    .seq hex₁ (.seq hex₂ (.seq hex₃ (.seq hex₄ (.seq hex₅ (.seq hex₆ hex₇))))),
    ?_, hk_final, hcand_final⟩
  simp only [Expr.cost, stepCost] at hk₇
  have hsum : ∑ γ ∈ Finset.range bridges.length,
      (1 + 6 + (21 + 88 * match bridges[γ]? with
        | some bd => (bd.attachmentIndices H T).length
        | none => 0)) =
      28 * bridges.length + 88 * totalAttachments H T bridges := by
    have htot := (sum_range_attachmentIndices_length H T bridges le_rfl).trans
      (attOffset_length H T bridges)
    rw [← htot, Finset.mul_sum,
      show 28 * bridges.length = ∑ _γ ∈ Finset.range bridges.length, 28 by simp [mul_comm],
      ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun _ _ => by ring
  rw [hsum] at hk₇
  omega

/-! ### Part 4: Mathematical Lemmas for Counting Sort -/

/-- Offset of bucket `k` in `countingSort c key xs`: total length of buckets `0 .. k - 1`. -/
def bucketOff (key : Candidate → ℕ) (xs : List Candidate) (k : ℕ) : ℕ :=
  ((List.range k).flatMap (fun j => xs.filter (fun x => key x == j))).length

@[simp]
theorem bucketOff_zero (key : Candidate → ℕ) (xs : List Candidate) :
    bucketOff key xs 0 = 0 := rfl

theorem bucketOff_succ (key : Candidate → ℕ) (xs : List Candidate) (k : ℕ) :
    bucketOff key xs (k + 1) =
      bucketOff key xs k + (xs.filter (fun x => key x == k)).length := by
  unfold bucketOff
  rw [List.range_succ, List.flatMap_append, List.flatMap_singleton, List.length_append]

theorem bucketOff_mono (key : Candidate → ℕ) (xs : List Candidate) {j k : ℕ} (h : j ≤ k) :
    bucketOff key xs j ≤ bucketOff key xs k := by
  obtain ⟨d, rfl⟩ : ∃ d, k = j + d := ⟨k - j, by omega⟩
  induction d with
  | zero => simp
  | succ d' ih =>
    rw [Nat.add_succ, bucketOff_succ]
    have := ih (by omega)
    omega

theorem bucketOff_le_length (key : Candidate → ℕ) (xs : List Candidate) (k : ℕ) :
    bucketOff key xs k ≤ xs.length :=
  length_flatMap_filter_le key List.nodup_range xs

theorem bucketOff_eq_length_countingSort (c : ℕ) (key : Candidate → ℕ) (xs : List Candidate) :
    bucketOff key xs c = (countingSort c key xs).length := rfl

theorem take_succ_filter {α : Type*} (P : α → Bool) (xs : List α) {i : ℕ} (hi : i < xs.length) :
    (xs.take (i + 1)).filter P =
      (xs.take i).filter P ++ if P (xs[i]'hi) then [xs[i]'hi] else [] := by
  rw [List.take_add_one, List.getElem?_eq_getElem hi, Option.toList_some, List.filter_append]
  cases hP : P (xs[i]'hi) <;> simp [hP]

theorem length_take_filter_lt {α : Type*} (P : α → Bool) (xs : List α) {i : ℕ}
    (hi : i < xs.length) (hP : P (xs[i]'hi) = true) :
    ((xs.take i).filter P).length < (xs.filter P).length := by
  have h1 : ((xs.take (i + 1)).filter P).length = ((xs.take i).filter P).length + 1 := by
    rw [take_succ_filter P xs hi, hP]
    simp
  have h2 : ((xs.take (i + 1)).filter P).length ≤ (xs.filter P).length :=
    ((List.take_sublist (i + 1) xs).filter P).length_le
  omega

theorem length_take_filter_le {α : Type*} (P : α → Bool) (xs : List α) (i : ℕ) :
    ((xs.take i).filter P).length ≤ (xs.filter P).length :=
  ((List.take_sublist i xs).filter P).length_le

theorem getElem_flatMap_range_of_slices {key : Candidate → ℕ} {xs : List Candidate}
    {aL aR aG : List ℕ} {m : ℕ}
    (hslice : ∀ k < m, ∀ j (hj : j < (xs.filter (fun x => key x == k)).length),
      let cand := (xs.filter (fun x => key x == k))[j]'hj
      aL[bucketOff key xs k + j]? = some cand.l ∧
      aR[bucketOff key xs k + j]? = some cand.r ∧
      aG[bucketOff key xs k + j]? = some cand.γ) :
    ∀ p (hp : p < ((List.range m).flatMap (fun k => xs.filter (fun x => key x == k))).length),
      let cand := ((List.range m).flatMap (fun k => xs.filter (fun x => key x == k)))[p]'hp
      aL[p]? = some cand.l ∧ aR[p]? = some cand.r ∧ aG[p]? = some cand.γ := by
  induction m with
  | zero =>
    intro p hp
    simp at hp
  | succ m' ih =>
    intro p hp
    have heq : (List.range (m' + 1)).flatMap (fun k => xs.filter (fun x => key x == k)) =
        (List.range m').flatMap (fun k => xs.filter (fun x => key x == k)) ++
          xs.filter (fun x => key x == m') := by
      rw [List.range_succ, List.flatMap_append, List.flatMap_singleton]
    by_cases hp_lt : p < bucketOff key xs m'
    · have hp_lt' : p < ((List.range m').flatMap (fun k => xs.filter (fun x => key x == k))).length :=
        hp_lt
      have hget : ((List.range (m' + 1)).flatMap (fun k => xs.filter (fun x => key x == k)))[p]'hp =
          ((List.range m').flatMap (fun k => xs.filter (fun x => key x == k)))[p]'hp_lt' := by
        simp only [heq]
        exact List.getElem_append_left hp_lt'
      dsimp only
      rw [hget]
      exact ih (fun k hk => hslice k (by omega)) p hp_lt'
    · set j := p - bucketOff key xs m'
      have hj : j < (xs.filter (fun x => key x == m')).length := by
        have hp' : p < bucketOff key xs (m' + 1) := hp
        rw [bucketOff_succ] at hp'
        omega
      have hp_eq : bucketOff key xs m' + j = p := by omega
      have hle_p : ((List.range m').flatMap (fun k => xs.filter (fun x => key x == k))).length ≤ p :=
        Nat.le_of_not_lt hp_lt
      have hget : ((List.range (m' + 1)).flatMap (fun k => xs.filter (fun x => key x == k)))[p]'hp =
          (xs.filter (fun x => key x == m'))[j]'hj := by
        simp only [heq]
        rw [List.getElem_append_right hle_p]
        rfl
      dsimp only
      rw [hget, ← hp_eq]
      exact hslice m' (by omega) j hj

/-! ### Part 5: Counting Sort Program (`countingSortProg`, `sortCandProg`) -/

/-- Pass 1 body of counting sort: read candidate `i = rG` from `(aInL, aInR, aInG)` into
`(rTmp1, rTmp2, rTmp3)`, evaluate `keyExpr` into `rTmp4`, and increment `aBucketLen[rTmp4]`. -/
def countPassBody (aInL aInR : Arr) (keyExpr : Expr) : Cmd :=
  let r_i := rG
  let r_l := rTmp1
  let r_r := rTmp2
  let r_k := rTmp4
  .seq (.assign r_l (.read aInL (.reg r_i)))
    (.seq (.assign r_r (.read aInR (.reg r_i)))
      (.seq (.assign r_k keyExpr)
        (.write aBucketLen (.reg r_k)
          (.op .add (.read aBucketLen (.reg r_k)) (.const 1)))))

/-- Pass 2 (prefix sums) of counting sort: allocate `aBucketPos` of length `rk` and fill
`aBucketPos[k] = bucketOff key xs k`. -/
def bucketPrefixProg : Cmd :=
  let r_k := rG
  let r_sum := rTmp1
  .seq (.alloc aBucketPos (.reg rk))
    (.seq (.assign r_sum (.const 0))
      (.seq (.assign r_k (.const 0))
        (forUp r_k (.reg rk)
          (.seq (.write aBucketPos (.reg r_k) (.reg r_sum))
            (.assign r_sum (.op .add (.reg r_sum) (.read aBucketLen (.reg r_k))))))))

/-- Pass 3 (scatter) body of counting sort: read candidate `i = rG` from `(aInL, aInR, aInG)`
into `(rTmp1, rTmp2, rTmp3)`, evaluate `keyExpr` into `rTmp4`, read `pos = aBucketPos[rTmp4]` into
`rM`, write candidate to `(aOutL, aOutR, aOutG)` at `pos`, and increment `aBucketPos[rTmp4]`. -/
def scatterPassBody (aInL aInR aInG aOutL aOutR aOutG : Arr) (keyExpr : Expr) : Cmd :=
  let r_i := rG
  let r_pos := rM
  let r_l := rTmp1
  let r_r := rTmp2
  let r_g := rTmp3
  let r_k := rTmp4
  .seq (.assign r_l (.read aInL (.reg r_i)))
    (.seq (.assign r_r (.read aInR (.reg r_i)))
      (.seq (.assign r_g (.read aInG (.reg r_i)))
        (.seq (.assign r_k keyExpr)
          (.seq (.assign r_pos (.read aBucketPos (.reg r_k)))
            (.seq (.write aOutL (.reg r_pos) (.reg r_l))
              (.seq (.write aOutR (.reg r_pos) (.reg r_r))
                (.seq (.write aOutG (.reg r_pos) (.reg r_g))
                  (.write aBucketPos (.reg r_k) (.op .add (.reg r_pos) (.const 1))))))))))

/-- Complete one-pass stable counting sort from `(aInL, aInR, aInG)` into `(aOutL, aOutR, aOutG)`
using bucket count `rk` and key expression `keyExpr` (which may read `rk`, `rTmp1`, `rTmp2`). -/
def countingSortProg (aInL aInR aInG aOutL aOutR aOutG : Arr) (keyExpr : Expr) : Cmd :=
  let r_i := rG
  .seq (.alloc aBucketLen (.reg rk))
    (.seq (.assign r_i (.const 0))
      (.seq (forUp r_i (.reg rNumCand) (countPassBody aInL aInR keyExpr))
        (.seq bucketPrefixProg
          (.seq (.alloc aOutL (.reg rNumCand))
            (.seq (.alloc aOutR (.reg rNumCand))
              (.seq (.alloc aOutG (.reg rNumCand))
                (.seq (.assign r_i (.const 0))
                  (forUp r_i (.reg rNumCand)
                    (scatterPassBody aInL aInR aInG aOutL aOutR aOutG keyExpr)))))))))

/-- Key expression for Pass 1 of `sortCandidates`: `(c - 1) - I.r`. -/
def sortKeyExpr1 : Expr :=
  .op .sub (.op .sub (.reg rk) (.const 1)) (.reg rTmp2)

/-- Key expression for Pass 2 of `sortCandidates`: `I.l`. -/
def sortKeyExpr2 : Expr :=
  .reg rTmp1

/-- Two-pass stable counting sort `sortCandProg`:
Pass 1 sorts `(aCandL, aCandR, aCandG)` into `(aSortL, aSortR, aSortG)` by decreasing `r`
(key `c - 1 - r`);
Pass 2 sorts `(aSortL, aSortR, aSortG)` back into `(aCandL, aCandR, aCandG)` by increasing `l`. -/
def sortCandProg : Cmd :=
  .seq (countingSortProg aCandL aCandR aCandG aSortL aSortR aSortG sortKeyExpr1)
    (countingSortProg aSortL aSortR aSortG aCandL aCandR aCandG sortKeyExpr2)

/-- Registers modified by `countingSortProg` and `sortCandProg`. -/
def sortCandRegs : List Reg :=
  [rG, rM, rTmp1, rTmp2, rTmp3, rTmp4]

/-- Arrays modified by `sortCandProg`. -/
def sortCandArrs : List Arr :=
  [aCandL, aCandR, aCandG, aSortL, aSortR, aSortG, aBucketLen, aBucketPos]

theorem countingSortProg_exec {w : ℕ}
    (aInL aInR aInG aOutL aOutR aOutG : Arr)
    (keyExpr : Expr) (key : Candidate → ℕ)
    (c capIn : ℕ) (xs : List Candidate) (s₀ : State)
    (h_disj_in : aInL ≠ aBucketLen ∧ aInR ≠ aBucketLen ∧ aInG ≠ aBucketLen ∧
      aInL ≠ aBucketPos ∧ aInR ≠ aBucketPos ∧ aInG ≠ aBucketPos ∧
      aInL ≠ aOutL ∧ aInL ≠ aOutR ∧ aInL ≠ aOutG ∧
      aInR ≠ aOutL ∧ aInR ≠ aOutR ∧ aInR ≠ aOutG ∧
      aInG ≠ aOutL ∧ aInG ≠ aOutR ∧ aInG ≠ aOutG)
    (h_disj_out : aOutL ≠ aOutR ∧ aOutL ≠ aOutG ∧ aOutR ≠ aOutG ∧
      aOutL ≠ aBucketLen ∧ aOutR ≠ aBucketLen ∧ aOutG ≠ aBucketLen ∧
      aOutL ≠ aBucketPos ∧ aOutR ≠ aBucketPos ∧ aOutG ≠ aBucketPos)
    (hrC : s₀.regs rk = c)
    (hxs : IsCandArray xs capIn aInL aInR aInG rNumCand s₀)
    (hbounds : ∀ I ∈ xs, I.l < c ∧ I.r < c ∧ I.γ < 2 ^ w ∧ key I < c)
    (hkey_eval : ∀ (s : State) (I : Candidate),
      s.regs rk = c → s.regs rTmp1 = I.l → s.regs rTmp2 = I.r →
      I.l < c → I.r < c → keyExpr.eval w s = some (key I))
    (hkey_cost : keyExpr.cost ≤ 5)
    (hw1 : 1 < 2 ^ w) (hc_w : c < 2 ^ w) (hxs_w : xs.length < 2 ^ w) :
    ∃ s' k,
      Exec w (countingSortProg aInL aInR aInG aOutL aOutR aOutG keyExpr) s₀ s' k ∧
      k ≤ 31 + 29 * c + 78 * xs.length ∧
      Keeps sortCandRegs [aOutL, aOutR, aOutG, aBucketLen, aBucketPos] s₀ s' ∧
      IsCandArray (countingSort c key xs) xs.length aOutL aOutR aOutG rNumCand s' := by
  obtain ⟨hne_LR, hne_LG, hne_RG, hne_LBlen, hne_RBlen, hne_GBlen,
    hne_LBpos, hne_RBpos, hne_GBpos⟩ := h_disj_out
  -- Step 1: alloc aBucketLen (.reg rk)
  let s₁ := s₀.setArr aBucketLen (List.replicate c 0)
  have hex₁ : Exec w (.alloc aBucketLen (.reg rk)) s₀ s₁ (1 + c) :=
    .alloc (by simp [Expr.eval, checkWord, hrC, hc_w])
  -- Step 2: Count pass loop
  let s₂ := s₁.setReg rG 0
  have hex₂ : Exec w (.assign rG (.const 0)) s₁ s₂ 2 :=
    .assign (by simp [Expr.eval, checkWord, show (0 : ℕ) < 2 ^ w by omega])
  let Inv1 (i : ℕ) (s : State) : Prop :=
    s.regs rG = i ∧
    Keeps sortCandRegs [aBucketLen] s₀ s ∧
    (s.arrs aBucketLen).length = c ∧
    ∀ k < c, (s.arrs aBucketLen)[k]? = some (((xs.take i).filter (fun x => key x == k)).length)
  have hInv1_0 : Inv1 0 s₂ := by
    refine ⟨by simp [s₂],
      ((Keeps.refl sortCandRegs [aBucketLen] s₀).setArr (by decide) _).setReg (by decide) _,
      by simp [s₂, s₁], fun k hk => ?_⟩
    simp [s₂, s₁, hk]
  have hloop1 : ⦃Inv1 0⦄[w]
      forUp rG (.reg rNumCand) (countPassBody aInL aInR keyExpr)
      ⦃Inv1 xs.length⦄ ≤
      fun _ => (Expr.reg rNumCand).cost + 2 + xs.length * ((Expr.reg rNumCand).cost + 6 + 21) := by
    apply Triple.forUp_const Inv1 xs.length 21 hw1 hxs_w
    · intro i _ s ⟨hri, hk, _, _⟩
      have hrN : s.regs rNumCand = xs.length := (hk.1 rNumCand (by decide)).trans hxs.1
      exact ⟨hri, by simp [Expr.eval, checkWord, hrN, hxs_w]⟩
    · intro i hi s ⟨hri, hk, hblen, hbcnt⟩
      have hi_w : i < 2 ^ w := by omega
      have hxs_s : IsCandArray xs capIn aInL aInR aInG rNumCand s :=
        hxs.of_eq (hk.1 rNumCand (by decide))
          (hk.2 aInL (by simp [h_disj_in.1]))
          (hk.2 aInR (by simp [h_disj_in.2.1]))
          (hk.2 aInG (by simp [h_disj_in.2.2.1]))
      set I := xs[i]'hi
      obtain ⟨hIl_c, hIr_c, hIg_w, hkey_c⟩ := hbounds I (List.getElem_mem hi)
      obtain ⟨hgetL, hgetR, _⟩ := hxs_s.2.2.2.2.2 i hi
      have h_eval_l : (Expr.read aInL (.reg rG)).eval w s = some I.l :=
        read_reg_eval hri hi_w hgetL (by omega)
      let st₁ := s.setReg rTmp1 I.l
      have hex_s1 : Exec w (.assign rTmp1 (.read aInL (.reg rG))) s st₁ 3 :=
        .assign h_eval_l
      have h_eval_r : (Expr.read aInR (.reg rG)).eval w st₁ = some I.r :=
        read_reg_eval (by simp [st₁, hri]) hi_w (by simpa [st₁, I] using hgetR) (by omega)
      let st₂ := st₁.setReg rTmp2 I.r
      have hex_s2 : Exec w (.assign rTmp2 (.read aInR (.reg rG))) st₁ st₂ 3 :=
        .assign h_eval_r
      have hrC_st₂ : st₂.regs rk = c := by
        simp [st₂, st₁]; exact (hk.1 rk (by decide)).trans hrC
      have h_eval_k : keyExpr.eval w st₂ = some (key I) :=
        hkey_eval st₂ I hrC_st₂ (by simp [st₂, st₁]) (by simp [st₂]) hIl_c hIr_c
      let st₃ := st₂.setReg rTmp4 (key I)
      have hex_s3 : Exec w (.assign rTmp4 keyExpr) st₂ st₃ (keyExpr.cost + 1) :=
        .assign h_eval_k
      set k₀ := key I
      have hk₀_w : k₀ < 2 ^ w := by omega
      set cnt := ((xs.take i).filter (fun x => key x == k₀)).length
      have hcnt_lt : cnt < xs.length := by
        have := length_take_filter_lt (fun x => key x == k₀) xs hi (by simp [I, k₀])
        have := List.length_filter_le (fun x => key x == k₀) xs
        omega
      have hget_cnt : (st₃.arrs aBucketLen)[k₀]? = some cnt := by
        simpa [st₃, st₂, st₁, cnt] using hbcnt k₀ hkey_c
      have h_read_cnt : (Expr.read aBucketLen (.reg rTmp4)).eval w st₃ = some cnt :=
        read_reg_eval (by simp [st₃, k₀]) hk₀_w hget_cnt (by omega)
      have h_inc_cnt : (Expr.op .add (.read aBucketLen (.reg rTmp4)) (.const 1)).eval w st₃ =
          some (cnt + 1) := by
        unfold Expr.eval
        rw [h_read_cnt]
        simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hw1,
          show cnt + 1 < 2 ^ w by omega]
      let st₄ := st₃.writeArr aBucketLen k₀ (cnt + 1)
      have hex_s4 : Exec w (.write aBucketLen (.reg rTmp4)
          (.op .add (.read aBucketLen (.reg rTmp4)) (.const 1))) st₃ st₄ 6 :=
        .write (by simp [st₃, Expr.eval, checkWord, hk₀_w, k₀]) h_inc_cnt
          (by simp [st₃, st₂, st₁, hblen, hkey_c, k₀])
      refine ⟨st₄, _,
        .seq hex_s1 (.seq hex_s2 (.seq hex_s3 hex_s4)), by dsimp only; omega,
        ⟨by simp,
          ((((hk.setReg (by decide) _).setReg (by decide) _).setReg (by decide) _).writeArr
            (by decide) _ _).setReg (by decide) _,
          by simp [st₄, st₃, st₂, st₁, hblen], fun k hk_c => ?_⟩,
        by simp [st₄, st₃, st₂, st₁, hri]⟩
      simp only [State.setReg_arrs, st₄, st₃, st₂, st₁, State.writeArr_arrs_self]
      rw [take_succ_filter (fun x => key x == k) xs hi]
      by_cases hkk₀ : k = k₀
      · subst hkk₀
        rw [List.getElem?_set_self (by omega)]
        simp [cnt, I, k₀]
      · rw [List.getElem?_set_ne (Ne.symm hkk₀)]
        have hne_k : key (xs[i]'hi) ≠ k := by
          dsimp [I, k₀] at hkk₀; exact Ne.symm hkk₀
        simp [hne_k, hbcnt k hk_c]
  obtain ⟨s₃, k₃, hex₃, hk₃, _, hkeep₃, hblen₃, hbcnt₃⟩ := hloop1 s₂ hInv1_0
  have hbcnt₃_full : ∀ k < c,
      (s₃.arrs aBucketLen)[k]? = some ((xs.filter (fun x => key x == k)).length) := by
    intro k hk
    simpa [List.take_length] using hbcnt₃ k hk
  -- Step 3: bucketPrefixProg
  have hrC₃ : s₃.regs rk = c := (hkeep₃.1 rk (by decide)).trans hrC
  let s₄_0 := s₃.setArr aBucketPos (List.replicate c 0)
  have hex₄_0 : Exec w (.alloc aBucketPos (.reg rk)) s₃ s₄_0 (1 + c) :=
    .alloc (by simp [Expr.eval, checkWord, hrC₃, hc_w])
  let s₄_1 := s₄_0.setReg rTmp1 0
  have hex₄_1 : Exec w (.assign rTmp1 (.const 0)) s₄_0 s₄_1 2 :=
    .assign (by simp [Expr.eval, checkWord, show (0 : ℕ) < 2 ^ w by omega])
  let s₄_2 := s₄_1.setReg rG 0
  have hex₄_2 : Exec w (.assign rG (.const 0)) s₄_1 s₄_2 2 :=
    .assign (by simp [Expr.eval, checkWord, show (0 : ℕ) < 2 ^ w by omega])
  let Inv2 (k : ℕ) (s : State) : Prop :=
    s.regs rG = k ∧
    s.regs rTmp1 = bucketOff key xs k ∧
    Keeps sortCandRegs [aBucketLen, aBucketPos] s₀ s ∧
    (s.arrs aBucketLen) = (s₃.arrs aBucketLen) ∧
    (s.arrs aBucketPos).length = c ∧
    ∀ j < k, (s.arrs aBucketPos)[j]? = some (bucketOff key xs j)
  have hInv2_0 : Inv2 0 s₄_2 :=
    ⟨by simp [s₄_2], by simp [s₄_2, s₄_1],
      (((hkeep₃.mono (fun _ hr => hr) (fun a ha => by revert a ha; decide)).setArr
        (by decide) _).setReg (by decide) _).setReg (by decide) _,
      by simp [s₄_2, s₄_1, s₄_0], by simp [s₄_2, s₄_1, s₄_0], fun j hj => by omega⟩
  have hloop2 : ⦃Inv2 0⦄[w]
      forUp rG (.reg rk)
        (.seq (.write aBucketPos (.reg rG) (.reg rTmp1))
          (.assign rTmp1 (.op .add (.reg rTmp1) (.read aBucketLen (.reg rG)))))
      ⦃Inv2 c⦄ ≤ fun _ => (Expr.reg rk).cost + 2 + c * ((Expr.reg rk).cost + 6 + 9) := by
    apply Triple.forUp_const Inv2 c 9 hw1 hc_w
    · intro k _ s ⟨hrk, _, hk, _, _, _⟩
      have hrC_s : s.regs rk = c := (hk.1 rk (by decide)).trans hrC
      exact ⟨hrk, by simp [Expr.eval, checkWord, hrC_s, hc_w]⟩
    · intro k hk_c s ⟨hrk, hrsum, hk, hbl_eq, hbplen, hbp_prev⟩
      have hk_w : k < 2 ^ w := by omega
      have hoff_le : bucketOff key xs (k + 1) ≤ xs.length := bucketOff_le_length key xs (k + 1)
      have hoff_k_w : bucketOff key xs k < 2 ^ w := by
        have := bucketOff_le_length key xs k; omega
      let st₁ := s.writeArr aBucketPos k (bucketOff key xs k)
      have hex_w : Exec w (.write aBucketPos (.reg rG) (.reg rTmp1)) s st₁ 3 :=
        .write (by simp [Expr.eval, checkWord, hrk, hk_w])
          (by simp [Expr.eval, checkWord, hrsum, hoff_k_w])
          (by omega)
      have hget_len : (st₁.arrs aBucketLen)[k]? =
          some ((xs.filter (fun x => key x == k)).length) := by
        simp [st₁, hbl_eq, hbcnt₃_full k hk_c]
      have hlen_k_w : (xs.filter (fun x => key x == k)).length < 2 ^ w := by
        have := List.length_filter_le (fun x => key x == k) xs; omega
      have h_read_len : (Expr.read aBucketLen (.reg rG)).eval w st₁ =
          some ((xs.filter (fun x => key x == k)).length) :=
        read_reg_eval (by simp [st₁, hrk]) hk_w hget_len hlen_k_w
      have h_add_sum : (Expr.op .add (.reg rTmp1) (.read aBucketLen (.reg rG))).eval w st₁ =
          some (bucketOff key xs (k + 1)) := by
        rw [bucketOff_succ]
        have h_reg_sum : (Expr.reg rTmp1).eval w st₁ = some (bucketOff key xs k) := by
          simp [Expr.eval, st₁, hrsum, checkWord, hoff_k_w]
        unfold Expr.eval
        rw [h_reg_sum, h_read_len]
        simp [BinOp.eval, BinOp.raw, checkWord,
          show bucketOff key xs k + (xs.filter (fun x => key x == k)).length < 2 ^ w by
            rw [← bucketOff_succ]; omega]
      let st₂ := st₁.setReg rTmp1 (bucketOff key xs (k + 1))
      have hex_add : Exec w (.assign rTmp1
          (.op .add (.reg rTmp1) (.read aBucketLen (.reg rG)))) st₁ st₂ 5 :=
        .assign h_add_sum
      refine ⟨st₂, _, .seq hex_w hex_add, by dsimp only; omega,
        ⟨by simp, by simp [st₂],
          ((hk.writeArr (by decide) _ _).setReg (by decide) _).setReg (by decide) _,
          by simp [st₂, st₁, hbl_eq], by simp [st₂, st₁, hbplen], fun j hj => ?_⟩,
        by simp [st₂, st₁, hrk]⟩
      simp only [State.setReg_arrs, st₂, st₁, State.writeArr_arrs_self]
      by_cases hjk : j = k
      · subst hjk
        rw [List.getElem?_set_self (by omega)]
      · rw [List.getElem?_set_ne (by omega)]
        exact hbp_prev j (by omega)
  obtain ⟨s₄, k₄, hex₄_loop, hk₄, _, _, hkeep₄, _, hbplen₄, hbp₄⟩ := hloop2 s₄_2 hInv2_0
  have hex₄ : Exec w bucketPrefixProg s₃ s₄ ((1 + c) + (2 + (2 + k₄))) :=
    .seq hex₄_0 (.seq hex₄_1 (.seq hex₄_2 hex₄_loop))
  -- Step 4: Allocate aOutL, aOutR, aOutG and run scatter loop
  have hrN₄ : s₄.regs rNumCand = xs.length := (hkeep₄.1 rNumCand (by decide)).trans hxs.1
  let s₅_0 := s₄.setArr aOutL (List.replicate xs.length 0)
  have hex₅_0 : Exec w (.alloc aOutL (.reg rNumCand)) s₄ s₅_0 (1 + xs.length) :=
    .alloc (by simp [Expr.eval, checkWord, hrN₄, hxs_w])
  let s₅_1 := s₅_0.setArr aOutR (List.replicate xs.length 0)
  have hex₅_1 : Exec w (.alloc aOutR (.reg rNumCand)) s₅_0 s₅_1 (1 + xs.length) :=
    .alloc (by simp [s₅_0, Expr.eval, checkWord, hrN₄, hxs_w])
  let s₅_2 := s₅_1.setArr aOutG (List.replicate xs.length 0)
  have hex₅_2 : Exec w (.alloc aOutG (.reg rNumCand)) s₅_1 s₅_2 (1 + xs.length) :=
    .alloc (by simp [s₅_1, s₅_0, Expr.eval, checkWord, hrN₄, hxs_w])
  let s₅_3 := s₅_2.setReg rG 0
  have hex₅_3 : Exec w (.assign rG (.const 0)) s₅_2 s₅_3 2 :=
    .assign (by simp [Expr.eval, checkWord, show (0 : ℕ) < 2 ^ w by omega])
  let Inv3 (i : ℕ) (s : State) : Prop :=
    s.regs rG = i ∧
    Keeps sortCandRegs [aOutL, aOutR, aOutG, aBucketLen, aBucketPos] s₀ s ∧
    (s.arrs aOutL).length = xs.length ∧
    (s.arrs aOutR).length = xs.length ∧
    (s.arrs aOutG).length = xs.length ∧
    (s.arrs aBucketPos).length = c ∧
    (∀ k < c, (s.arrs aBucketPos)[k]? =
      some (bucketOff key xs k + ((xs.take i).filter (fun x => key x == k)).length)) ∧
    (∀ k < c, ∀ j (hj : j < ((xs.take i).filter (fun x => key x == k)).length),
      let cand := ((xs.take i).filter (fun x => key x == k))[j]'hj
      (s.arrs aOutL)[bucketOff key xs k + j]? = some cand.l ∧
      (s.arrs aOutR)[bucketOff key xs k + j]? = some cand.r ∧
      (s.arrs aOutG)[bucketOff key xs k + j]? = some cand.γ)
  have hbp_s5_3 : s₅_3.arrs aBucketPos = s₄.arrs aBucketPos := by
    simp [s₅_3, s₅_2, s₅_1, s₅_0, Ne.symm hne_LBpos, Ne.symm hne_RBpos, Ne.symm hne_GBpos]
  have hInv3_0 : Inv3 0 s₅_3 := by
    refine ⟨by simp [s₅_3], ?_,
      by simp [s₅_3, s₅_2, s₅_1, s₅_0, hne_LR, hne_LG],
      by simp [s₅_3, s₅_2, s₅_1, hne_RG],
      by simp [s₅_3, s₅_2],
      by rw [hbp_s5_3]; exact hbplen₄,
      fun k hk => ?_, fun k _ j hj => by simp at hj⟩
    · exact ((((hkeep₄.mono (fun _ hr => hr) (fun a ha => by simp at ha ⊢; tauto)).setArr
        (by simp) _).setArr (by simp) _).setArr (by simp) _).setReg (by decide) _
    · rw [hbp_s5_3]; simpa using hbp₄ k hk
  have hloop3 : ⦃Inv3 0⦄[w]
      forUp rG (.reg rNumCand)
        (scatterPassBody aInL aInR aInG aOutL aOutR aOutG keyExpr)
      ⦃Inv3 xs.length⦄ ≤
      fun _ => (Expr.reg rNumCand).cost + 2 + xs.length * ((Expr.reg rNumCand).cost + 6 + 36) := by
    apply Triple.forUp_const Inv3 xs.length 36 hw1 hxs_w
    · intro i _ s ⟨hri, hk, _, _, _, _, _, _⟩
      have hrN : s.regs rNumCand = xs.length := (hk.1 rNumCand (by decide)).trans hxs.1
      exact ⟨hri, by simp [Expr.eval, checkWord, hrN, hxs_w]⟩
    · intro i hi s ⟨hri, hk, hlenL, hlenR, hlenG, hbplen, hbp_cur, hslice⟩
      have hi_w : i < 2 ^ w := by omega
      have hxs_s : IsCandArray xs capIn aInL aInR aInG rNumCand s :=
        hxs.of_eq (hk.1 rNumCand (by decide))
          (hk.2 aInL (by simp [h_disj_in.1, h_disj_in.2.2.2.1,
            h_disj_in.2.2.2.2.2.2.1, h_disj_in.2.2.2.2.2.2.2.1, h_disj_in.2.2.2.2.2.2.2.2.1]))
          (hk.2 aInR (by simp [h_disj_in.2.1, h_disj_in.2.2.2.2.1,
            h_disj_in.2.2.2.2.2.2.2.2.2.1, h_disj_in.2.2.2.2.2.2.2.2.2.2.1,
            h_disj_in.2.2.2.2.2.2.2.2.2.2.2.1]))
          (hk.2 aInG (by simp [h_disj_in.2.2.1, h_disj_in.2.2.2.2.2.1,
            h_disj_in.2.2.2.2.2.2.2.2.2.2.2.2.1, h_disj_in.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
            h_disj_in.2.2.2.2.2.2.2.2.2.2.2.2.2.2]))
      set I := xs[i]'hi
      obtain ⟨hIl_c, hIr_c, hIg_w, hkey_c⟩ := hbounds I (List.getElem_mem hi)
      obtain ⟨hgetL, hgetR, hgetG⟩ := hxs_s.2.2.2.2.2 i hi
      have h_eval_l : (Expr.read aInL (.reg rG)).eval w s = some I.l :=
        read_reg_eval hri hi_w hgetL (by omega)
      let st₁ := s.setReg rTmp1 I.l
      have hex_s1 : Exec w (.assign rTmp1 (.read aInL (.reg rG))) s st₁ 3 :=
        .assign h_eval_l
      have h_eval_r : (Expr.read aInR (.reg rG)).eval w st₁ = some I.r :=
        read_reg_eval (by simp [st₁, hri]) hi_w (by simpa [st₁, I] using hgetR) (by omega)
      let st₂ := st₁.setReg rTmp2 I.r
      have hex_s2 : Exec w (.assign rTmp2 (.read aInR (.reg rG))) st₁ st₂ 3 :=
        .assign h_eval_r
      have h_eval_g : (Expr.read aInG (.reg rG)).eval w st₂ = some I.γ :=
        read_reg_eval (by simp [st₂, st₁, hri]) hi_w (by simpa [st₂, st₁, I] using hgetG) hIg_w
      let st₃ := st₂.setReg rTmp3 I.γ
      have hex_s3 : Exec w (.assign rTmp3 (.read aInG (.reg rG))) st₂ st₃ 3 :=
        .assign h_eval_g
      have hrC_st₃ : st₃.regs rk = c := by
        simp [st₃, st₂, st₁]; exact (hk.1 rk (by decide)).trans hrC
      have h_eval_k : keyExpr.eval w st₃ = some (key I) :=
        hkey_eval st₃ I hrC_st₃ (by simp [st₃, st₂, st₁]) (by simp [st₃, st₂]) hIl_c hIr_c
      let st₄ := st₃.setReg rTmp4 (key I)
      have hex_s4 : Exec w (.assign rTmp4 keyExpr) st₃ st₄ (keyExpr.cost + 1) :=
        .assign h_eval_k
      set k₀ := key I
      have hk₀_w : k₀ < 2 ^ w := by omega
      set cnt := ((xs.take i).filter (fun x => key x == k₀)).length
      set pos := bucketOff key xs k₀ + cnt
      have hcnt_lt : cnt < (xs.filter (fun x => key x == k₀)).length :=
        length_take_filter_lt (fun x => key x == k₀) xs hi (by simp [I, k₀])
      have hpos_lt_next : pos < bucketOff key xs (k₀ + 1) := by
        rw [bucketOff_succ]; omega
      have hpos_lt_len : pos < xs.length :=
        lt_of_lt_of_le hpos_lt_next (bucketOff_le_length key xs (k₀ + 1))
      have hpos_w : pos < 2 ^ w := by omega
      have hget_pos : (st₄.arrs aBucketPos)[k₀]? = some pos := by
        simp [st₄, st₃, st₂, st₁, hbp_cur k₀ hkey_c, pos, cnt]
      have h_eval_pos : (Expr.read aBucketPos (.reg rTmp4)).eval w st₄ = some pos :=
        read_reg_eval (by simp [st₄, k₀]) hk₀_w hget_pos hpos_w
      let st₅ := st₄.setReg rM pos
      have hex_s5 : Exec w (.assign rM (.read aBucketPos (.reg rTmp4))) st₄ st₅ 3 :=
        .assign h_eval_pos
      let st₆ := st₅.writeArr aOutL pos I.l
      have hex_s6 : Exec w (.write aOutL (.reg rM) (.reg rTmp1)) st₅ st₆ 3 :=
        .write (by simp [st₅, Expr.eval, checkWord, hpos_w])
          (by simp [st₅, st₄, st₃, st₂, st₁, Expr.eval, checkWord, show I.l < 2 ^ w by omega])
          (by simp [st₅, st₄, st₃, st₂, st₁, hlenL, hpos_lt_len])
      let st₇ := st₆.writeArr aOutR pos I.r
      have hex_s7 : Exec w (.write aOutR (.reg rM) (.reg rTmp2)) st₆ st₇ 3 :=
        .write (by simp [st₆, st₅, Expr.eval, checkWord, hpos_w])
          (by simp [st₆, st₅, st₄, st₃, st₂, Expr.eval, checkWord, show I.r < 2 ^ w by omega])
          (by simp [st₆, st₅, st₄, st₃, st₂, st₁, Ne.symm hne_LR, hlenR, hpos_lt_len])
      let st₈ := st₇.writeArr aOutG pos I.γ
      have hex_s8 : Exec w (.write aOutG (.reg rM) (.reg rTmp3)) st₇ st₈ 3 :=
        .write (by simp [st₇, st₆, st₅, Expr.eval, checkWord, hpos_w])
          (by simp [st₇, st₆, st₅, st₄, st₃, Expr.eval, checkWord, hIg_w])
          (by simp [st₇, st₆, st₅, st₄, st₃, st₂, st₁,
            Ne.symm hne_LG, Ne.symm hne_RG, hlenG, hpos_lt_len])
      let st₉ := st₈.writeArr aBucketPos k₀ (pos + 1)
      have hex_s9 : Exec w (.write aBucketPos (.reg rTmp4)
          (.op .add (.reg rM) (.const 1))) st₈ st₉ 5 :=
        .write (by simp [st₈, st₇, st₆, st₅, st₄, Expr.eval, checkWord, hk₀_w, k₀])
          (by simp [st₈, st₇, st₆, st₅, Expr.eval, BinOp.eval, BinOp.raw, checkWord,
            hpos_w, hw1, show pos + 1 < 2 ^ w by omega])
          (by simp [st₈, st₇, st₆, st₅, st₄, st₃, st₂, st₁,
            Ne.symm hne_LBpos, Ne.symm hne_RBpos, Ne.symm hne_GBpos, hbplen, hkey_c, k₀])
      have haL_st₉ : st₉.arrs aOutL = (s.arrs aOutL).set pos I.l := by
        simp [st₉, st₈, st₇, st₆, st₅, st₄, st₃, st₂, st₁, hne_LR, hne_LG, hne_LBpos]
      have haR_st₉ : st₉.arrs aOutR = (s.arrs aOutR).set pos I.r := by
        simp [st₉, st₈, st₇, st₆, st₅, st₄, st₃, st₂, st₁, Ne.symm hne_LR, hne_RG, hne_RBpos]
      have haG_st₉ : st₉.arrs aOutG = (s.arrs aOutG).set pos I.γ := by
        simp [st₉, st₈, st₇, st₆, st₅, st₄, st₃, st₂, st₁,
          Ne.symm hne_LG, Ne.symm hne_RG, hne_GBpos]
      have hbp_st₉ : st₉.arrs aBucketPos = (s.arrs aBucketPos).set k₀ (pos + 1) := by
        simp [st₉, st₈, st₇, st₆, st₅, st₄, st₃, st₂, st₁,
          Ne.symm hne_LBpos, Ne.symm hne_RBpos, Ne.symm hne_GBpos]
      refine ⟨st₉, _,
        .seq hex_s1 (.seq hex_s2 (.seq hex_s3 (.seq hex_s4
          (.seq hex_s5 (.seq hex_s6 (.seq hex_s7 (.seq hex_s8 hex_s9))))))),
        by dsimp only; omega,
        ⟨by simp,
          (((((((((hk.setReg (by decide) _).setReg (by decide) _).setReg (by decide) _).setReg
            (by decide) _).setReg (by decide) _).writeArr (by simp) _ _).writeArr
            (by simp) _ _).writeArr (by simp) _ _).writeArr (by simp) _ _).setReg (by decide) _,
          by simp [haL_st₉, hlenL], by simp [haR_st₉, hlenR],
          by simp [haG_st₉, hlenG], by simp [hbp_st₉, hbplen],
          fun k hk_c => ?_, fun k hk_c j hj => ?_⟩,
        by simp [st₉, st₈, st₇, st₆, st₅, st₄, st₃, st₂, st₁, hri]⟩
      · simp only [State.setReg_arrs, hbp_st₉]
        rw [take_succ_filter (fun x => key x == k) xs hi]
        by_cases hkk₀ : k = k₀
        · subst hkk₀
          rw [List.getElem?_set_self (by omega)]
          simp [pos, cnt, I, k₀, Nat.add_assoc]
        · rw [List.getElem?_set_ne (Ne.symm hkk₀)]
          have hne_k : key (xs[i]'hi) ≠ k := by
            dsimp [I, k₀] at hkk₀; exact Ne.symm hkk₀
          simp [hne_k, hbp_cur k hk_c]
      · simp only [State.setReg_arrs, haL_st₉, haR_st₉, haG_st₉]
        have hj_old_or : (k = k₀ ∧ j = cnt) ∨
            j < ((xs.take i).filter (fun x => key x == k)).length := by
          rw [take_succ_filter (fun x => key x == k) xs hi] at hj
          by_cases hkk₀ : k = k₀
          · subst hkk₀
            simp [I, k₀] at hj
            rcases Nat.lt_or_eq_of_le hj with hlt | rfl
            · exact Or.inr hlt
            · exact Or.inl ⟨rfl, rfl⟩
          · have hne_k : key (xs[i]'hi) ≠ k := by
              dsimp [I, k₀] at hkk₀; exact Ne.symm hkk₀
            simp [hne_k] at hj
            exact Or.inr hj
        rcases hj_old_or with ⟨rfl, rfl⟩ | hj_lt
        · have hcand_eq : ((xs.take (i + 1)).filter (fun x => key x == k₀))[cnt]'hj = I := by
            simp only [take_succ_filter (fun x => key x == k₀) xs hi, I, k₀, beq_self_eq_true,
              ↓reduceIte]
            rw [List.getElem_append_right (le_refl cnt)]
            simp [cnt]
          rw [hcand_eq]
          simp [hlenL, hlenR, hlenG, hpos_lt_len, pos]
        · have hcand_eq : ((xs.take (i + 1)).filter (fun x => key x == k))[j]'hj =
              ((xs.take i).filter (fun x => key x == k))[j]'hj_lt := by
            simp only [take_succ_filter (fun x => key x == k) xs hi]
            exact List.getElem_append_left hj_lt
          have hne_pos : bucketOff key xs k + j ≠ pos := by
            by_cases hkk₀ : k = k₀
            · subst hkk₀; dsimp only [pos]; omega
            · rcases lt_trichotomy k k₀ with hlt | rfl | hgt
              · have h1 := bucketOff_mono key xs (show k + 1 ≤ k₀ by omega)
                have h2 := length_take_filter_le (fun x => key x == k) xs i
                rw [bucketOff_succ] at h1
                dsimp only [pos]; omega
              · contradiction
              · have h1 := bucketOff_mono key xs (show k₀ + 1 ≤ k by omega)
                dsimp only [pos]; omega
          rw [hcand_eq, List.getElem?_set_ne (Ne.symm hne_pos),
            List.getElem?_set_ne (Ne.symm hne_pos),
            List.getElem?_set_ne (Ne.symm hne_pos)]
          exact hslice k hk_c j hj_lt
  obtain ⟨s₅, k₅, hex₅_loop, hk₅, _, hkeep₅, hlenL₅, hlenR₅, hlenG₅, _, _, hslice₅⟩ :=
    hloop3 s₅_3 hInv3_0
  have hperm : (countingSort c key xs).Perm xs :=
    countingSort_perm c key xs (fun I hI => (hbounds I hI).2.2.2)
  have hlen_cs : (countingSort c key xs).length = xs.length := hperm.length_eq
  have hrN₅ : s₅.regs rNumCand = (countingSort c key xs).length := by
    rw [hlen_cs, hkeep₅.1 rNumCand (by decide), hxs.1]
  have hslice_full : ∀ k < c, ∀ j (hj : j < (xs.filter (fun x => key x == k)).length),
      let cand := (xs.filter (fun x => key x == k))[j]'hj
      (s₅.arrs aOutL)[bucketOff key xs k + j]? = some cand.l ∧
      (s₅.arrs aOutR)[bucketOff key xs k + j]? = some cand.r ∧
      (s₅.arrs aOutG)[bucketOff key xs k + j]? = some cand.γ := by
    intro k hk j hj
    simpa [List.take_length] using hslice₅ k hk j (by simpa [List.take_length] using hj)
  have hget_cs := getElem_flatMap_range_of_slices hslice_full
  refine ⟨s₅, _,
    .seq hex₁ (.seq hex₂ (.seq hex₃ (.seq hex₄
      (.seq hex₅_0 (.seq hex₅_1 (.seq hex₅_2 (.seq hex₅_3 hex₅_loop))))))),
    ?_, hkeep₅,
    ⟨hrN₅, hlenL₅, hlenR₅, hlenG₅, le_of_eq hlen_cs, fun i hi => hget_cs i hi⟩⟩
  simp only [Expr.cost] at hk₃ hk₄ hk₅
  omega

/-- **Execution of `sortCandProg`.**
Runs the two stable counting sorts on `(aCandL, aCandR, aCandG)` and produces
`sortCandidates c cs` back in `(aCandL, aCandR, aCandG)` in time
`O(1 + sortCandidatesSteps c cs)`. -/
theorem sortCandProg_exec {w : ℕ} (c capIn : ℕ) (cs : List Candidate) (s₀ : State)
    (hrC : s₀.regs rk = c)
    (hcs : IsCandArray cs capIn aCandL aCandR aCandG rNumCand s₀)
    (hbounds : ∀ I ∈ cs, I.l < c ∧ I.r < c ∧ I.γ < 2 ^ w)
    (hw1 : 1 < 2 ^ w) (hc_w : c < 2 ^ w) (hcs_w : cs.length < 2 ^ w) :
    ∃ s' k,
      Exec w sortCandProg s₀ s' k ∧
      k ≤ 62 + 78 * sortCandidatesSteps c cs ∧
      Keeps sortCandRegs sortCandArrs s₀ s' ∧
      IsCandArray (sortCandidates c cs) cs.length aCandL aCandR aCandG rNumCand s' := by
  let key₁ : Candidate → ℕ := fun I => c - 1 - I.r
  have hbounds₁ : ∀ I ∈ cs, I.l < c ∧ I.r < c ∧ I.γ < 2 ^ w ∧ key₁ I < c := by
    intro I hI
    obtain ⟨hl, hr, hg⟩ := hbounds I hI
    exact ⟨hl, hr, hg, by dsimp [key₁]; omega⟩
  have hkey₁_eval : ∀ (s : State) (I : Candidate),
      s.regs rk = c → s.regs rTmp1 = I.l → s.regs rTmp2 = I.r →
      I.l < c → I.r < c → sortKeyExpr1.eval w s = some (key₁ I) := by
    intro s I hrc _ hrr _ hIr
    simp [sortKeyExpr1, key₁, Expr.eval, BinOp.eval, BinOp.raw, checkWord, hrc, hrr,
      hc_w, hw1, show c - 1 < 2 ^ w by omega, show I.r < 2 ^ w by omega,
      show c - 1 - I.r < 2 ^ w by omega]
  obtain ⟨s₁, k₁, hex₁, hk₁, hkeep₁, hcand₁⟩ :=
    countingSortProg_exec aCandL aCandR aCandG aSortL aSortR aSortG sortKeyExpr1 key₁ c capIn cs s₀
      (by decide) (by decide) hrC hcs hbounds₁ hkey₁_eval (by decide) hw1 hc_w hcs_w
  set pass1 := countingSort c key₁ cs
  have hperm₁ : pass1.Perm cs :=
    countingSort_perm c key₁ cs (fun I hI => (hbounds₁ I hI).2.2.2)
  have hlen₁ : pass1.length = cs.length := hperm₁.length_eq
  have hrC₁ : s₁.regs rk = c := (hkeep₁.1 rk (by decide)).trans hrC
  let key₂ : Candidate → ℕ := fun I => I.l
  have hbounds₂ : ∀ I ∈ pass1, I.l < c ∧ I.r < c ∧ I.γ < 2 ^ w ∧ key₂ I < c := by
    intro I hI
    obtain ⟨hl, hr, hg⟩ := hbounds I (hperm₁.subset hI)
    exact ⟨hl, hr, hg, hl⟩
  have hkey₂_eval : ∀ (s : State) (I : Candidate),
      s.regs rk = c → s.regs rTmp1 = I.l → s.regs rTmp2 = I.r →
      I.l < c → I.r < c → sortKeyExpr2.eval w s = some (key₂ I) := by
    intro s I _ hrl _ _ _
    simp [sortKeyExpr2, key₂, checkWord, hrl, show I.l < 2 ^ w by omega]
  obtain ⟨s₂, k₂, hex₂, hk₂, hkeep₂, hcand₂⟩ :=
    countingSortProg_exec aSortL aSortR aSortG aCandL aCandR aCandG sortKeyExpr2 key₂
      c cs.length pass1 s₁
      (by decide) (by decide) hrC₁ hcand₁ hbounds₂ hkey₂_eval (by decide) hw1 hc_w
      (by rw [hlen₁]; exact hcs_w)
  rw [hlen₁] at hcand₂
  refine ⟨s₂, k₁ + k₂, .seq hex₁ hex₂, ?_, ?_, hcand₂⟩
  · dsimp only [sortCandidatesSteps, countingSortSteps]
    rw [hlen₁] at hk₂ ⊢
    omega
  · have hsub₁ : ∀ a ∈ ([aSortL, aSortR, aSortG, aBucketLen, aBucketPos] : List Arr),
        a ∈ sortCandArrs := by intro a ha; revert a ha; decide
    have hsub₂ : ∀ a ∈ ([aCandL, aCandR, aCandG, aBucketLen, aBucketPos] : List Arr),
        a ∈ sortCandArrs := by intro a ha; revert a ha; decide
    have hk₁_all : Keeps sortCandRegs sortCandArrs s₀ s₁ :=
      hkeep₁.mono (fun _ hr => hr) hsub₁
    have hk₂_all : Keeps sortCandRegs sortCandArrs s₁ s₂ :=
      hkeep₂.mono (fun _ hr => hr) hsub₂
    exact hk₁_all.trans hk₂_all (fun _ hr => hr) (fun _ ha => ha)

end GraphMinor.Compute
