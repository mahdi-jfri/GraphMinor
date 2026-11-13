module

public import GraphMinor.Compute.Algorithm101TildeA
public import GraphMinor.Compute.Algorithm105Step2

/-!
# Graph Minors XIII, Algorithm (10.1): Step 2 & Step 3 Word RAM Subprograms

This file implements the Word RAM subprograms for Step 2 and Step 3 of Graph Minors XIII,
Algorithm (10.1) (page 105) on each interior member `r = p.members[j]` (`j : Fin p.members.length`):

1. **Section 1 (`buildTildeAEListProg`):**
   - Copies `encEdgeTriples r.eList` and scans `G.enc` to append all incident edges assigned to
     member `j` by `incidentOwner p xSeq`, producing `encEdgeTriples (memberTildeAEList G p xSeq j)`
     in `a_tildeE` and `(memberTildeAEList G p xSeq j).length` in `r_tildeELen`.
2. **Section 2 (`buildVIdxProg`, `buildEdgeMultMatProg`, `buildEncFromMultMatProg`,
   `buildFTau0Prog`):**
   - Builds the inverse vertex-index table `a_vIdx`, the `n_A × n_A` edge-multiplicity matrices for
     `G_A = tildeAMultiDigraph vList eList` and `G_del = tildeAMultiDigraph vList r.eList`, the
     serialized `G_A.enc`, and the leaf-assignment array
     `List.ofFn (fun i : Fin G_del.toComputeDigraph.numEdges => memberFTau0 vList r i.1)`.
3. **Section 3 (`runInteriorStep2And3Prog`):**
   - Invokes `(convertBDProg b).shiftMem R_off A_off` to extend the branch-decomposition of
     `G_A \ X_A = G_del` of width `≤ ω` to a branch-decomposition of `G_A` of width
     `≤ max ω 2 + q`, then invokes `prog41.shiftMem R_off A_off` (`Alg41Spec101`) and
     `computeFolioRepCodeProg` to compute the canonical folio code `folioRepCode q out.folio`.
-/

@[expose] public section

namespace GraphMinor.Compute

open Classical

/-! ### Section 1: Step 2 Edge List Builder (`buildTildeAEListProg`) -/

abbrev Cmd.ifEq (e₁ e₂ : Expr) (c₁ c₂ : Cmd) : Cmd :=
  .ite (.op .eq e₁ e₂) c₁ c₂

abbrev Cmd.ifLt (e₁ e₂ : Expr) (c₁ c₂ : Cmd) : Cmd :=
  .ite (.op .lt e₁ e₂) c₁ c₂

theorem Exec.if_true {w : ℕ} {e : Expr} {c₁ c₂ : Cmd} {s s' : State} {v t : ℕ}
    (he : e.eval w s = some v) (hv : v ≠ 0) (hc : Exec w c₁ s s' t) :
    Exec w (.ite e c₁ c₂) s s' (e.cost + t) :=
  .ite_true he hv hc

theorem Exec.if_false {w : ℕ} {e : Expr} {c₁ c₂ : Cmd} {s s' : State} {t : ℕ}
    (he : e.eval w s = some 0) (hc : Exec w c₂ s s' t) :
    Exec w (.ite e c₁ c₂) s s' (e.cost + t) :=
  .ite_false he hc

@[simp]
theorem MultiDigraph.sumEdgeMult_nil {n : ℕ} (G : MultiDigraph n) :
    G.sumEdgeMult [] = 0 := rfl

@[simp]
theorem MultiDigraph.sumEdgeMult_cons {n : ℕ} (G : MultiDigraph n)
    (pair : Fin n × Fin n) (ps : List (Fin n × Fin n)) :
    G.sumEdgeMult (pair :: ps) = G.edgeMult pair.1 pair.2 + G.sumEdgeMult ps := rfl

@[simp]
theorem encEdgeTriples_append (L₁ L₂ : List (ℕ × ℕ × ℕ)) :
    encEdgeTriples (L₁ ++ L₂) = encEdgeTriples L₁ ++ encEdgeTriples L₂ := by
  induction L₁ with
  | nil => rfl
  | cons e es ih =>
    rcases e with ⟨u, v, k⟩
    simp [encEdgeTriples, ih]

theorem encEdgeTriples_map_range' (u v : ℕ) :
    ∀ (d k : ℕ),
      encEdgeTriples ((List.range' k d).map (fun c => (u, v, c))) =
        (List.range' k d).flatMap (fun c => [u, v, c])
  | 0, _ => rfl
  | d + 1, k => by simp [List.range'_succ, encEdgeTriples, encEdgeTriples_map_range' u v d (k + 1)]

@[simp]
theorem encEdgeTriples_map_range (u v m : ℕ) :
    encEdgeTriples ((List.range m).map (fun k => (u, v, k))) =
      (List.range m).flatMap (fun k => [u, v, k]) := by
  rw [List.range_eq_range']
  exact encEdgeTriples_map_range' u v m 0

theorem mem_encEdgeTriples_iff :
    ∀ (es : List (ℕ × ℕ × ℕ)) (x : ℕ),
      x ∈ encEdgeTriples es ↔ ∃ e ∈ es, x = e.1 ∨ x = e.2.1 ∨ x = e.2.2
  | [], _ => by simp [encEdgeTriples]
  | (u, v, k) :: es, x => by
    simp only [encEdgeTriples, List.mem_cons, mem_encEdgeTriples_iff es x]
    constructor
    · rintro (h | h | h | ⟨e, he, h⟩)
      · exact ⟨(u, v, k), Or.inl rfl, Or.inl h⟩
      · exact ⟨(u, v, k), Or.inl rfl, Or.inr (Or.inl h)⟩
      · exact ⟨(u, v, k), Or.inl rfl, Or.inr (Or.inr h)⟩
      · exact ⟨e, Or.inr he, h⟩
    · rintro ⟨e, rfl | he, h⟩
      · rcases h with h | h | h
        · exact Or.inl h
        · exact Or.inr (Or.inl h)
        · exact Or.inr (Or.inr (Or.inl h))
      · exact Or.inr (Or.inr (Or.inr ⟨e, he, h⟩))

/-- Extra edges from a suffix `suff : List (Fin n × Fin n)` of `G.activePairsList` assigned to
member `j`. -/
def extraEdgesFromPairs {n : ℕ} (G : MultiDigraph n) {X' : Finset (Fin n)}
    (p : ParsedCase3Block (G.deleteVertices X') X') (xSeq : List ℕ)
    (j : ℕ) (pairs : List (Fin n × Fin n)) : List (ℕ × ℕ × ℕ) :=
  pairs.flatMap fun pair =>
    let u := pair.1
    let v := pair.2
    if (u.1 ∈ xSeq ∨ v.1 ∈ xSeq) ∧
       (u.1 ∈ xSeq ∨ u.1 ∈ p.K_vList) ∧
       (v.1 ∈ xSeq ∨ v.1 ∈ p.K_vList) ∧
       incidentOwner p xSeq u.1 v.1 = j then
      (List.range (G.edgeMult u v)).map fun k => (u.1, v.1, k)
    else []

@[simp]
theorem extraEdgesFromPairs_nil {n : ℕ} (G : MultiDigraph n) {X' : Finset (Fin n)}
    (p : ParsedCase3Block (G.deleteVertices X') X') (xSeq : List ℕ) (j : ℕ) :
    extraEdgesFromPairs G p xSeq j [] = [] := rfl

@[simp]
theorem extraEdgesFromPairs_cons {n : ℕ} (G : MultiDigraph n) {X' : Finset (Fin n)}
    (p : ParsedCase3Block (G.deleteVertices X') X') (xSeq : List ℕ) (j : ℕ)
    (pair : Fin n × Fin n) (suff : List (Fin n × Fin n)) :
    extraEdgesFromPairs G p xSeq j (pair :: suff) =
      (if (pair.1.1 ∈ xSeq ∨ pair.2.1 ∈ xSeq) ∧
          (pair.1.1 ∈ xSeq ∨ pair.1.1 ∈ p.K_vList) ∧
          (pair.2.1 ∈ xSeq ∨ pair.2.1 ∈ p.K_vList) ∧
          incidentOwner p xSeq pair.1.1 pair.2.1 = j then
        (List.range (G.edgeMult pair.1 pair.2)).map (fun k => (pair.1.1, pair.2.1, k))
      else []) ++ extraEdgesFromPairs G p xSeq j suff := rfl

@[simp]
theorem extraEdgesFromPairs_append {n : ℕ} (G : MultiDigraph n) {X' : Finset (Fin n)}
    (p : ParsedCase3Block (G.deleteVertices X') X') (xSeq : List ℕ) (j : ℕ)
    (L₁ L₂ : List (Fin n × Fin n)) :
    extraEdgesFromPairs G p xSeq j (L₁ ++ L₂) =
      extraEdgesFromPairs G p xSeq j L₁ ++ extraEdgesFromPairs G p xSeq j L₂ := by
  simp [extraEdgesFromPairs, List.flatMap_append]

theorem extraEdgesFromPairs_activePairsList {n : ℕ} (G : MultiDigraph n) {X' : Finset (Fin n)}
    (p : ParsedCase3Block (G.deleteVertices X') X') (xSeq : List ℕ)
    (j : Fin p.members.length) :
    extraEdgesFromPairs G p xSeq j.1 G.activePairsList = extraEdges G p xSeq j := rfl

theorem length_extraEdgesFromPairs_le {n : ℕ} (G : MultiDigraph n) {X' : Finset (Fin n)}
    (p : ParsedCase3Block (G.deleteVertices X') X') (xSeq : List ℕ) (j : ℕ)
    (pairs : List (Fin n × Fin n)) :
    (extraEdgesFromPairs G p xSeq j pairs).length ≤ G.sumEdgeMult pairs := by
  induction pairs with
  | nil => simp [MultiDigraph.sumEdgeMult]
  | cons pair suff ih =>
    rw [extraEdgesFromPairs_cons, List.length_append, MultiDigraph.sumEdgeMult_cons]
    split_ifs <;> simp <;> omega

theorem length_extraEdges_le_numEdges {n : ℕ} (G : MultiDigraph n) {X' : Finset (Fin n)}
    (p : ParsedCase3Block (G.deleteVertices X') X') (xSeq : List ℕ)
    (j : Fin p.members.length) :
    (extraEdges G p xSeq j).length ≤ G.numEdges := by
  rw [← extraEdgesFromPairs_activePairsList, ← G.sumEdgeMult_activePairsList]
  exact length_extraEdgesFromPairs_le G p xSeq j.1 G.activePairsList

theorem length_memberTildeAEList_le {n : ℕ} (G : MultiDigraph n) {X' : Finset (Fin n)}
    (p : ParsedCase3Block (G.deleteVertices X') X') (xSeq : List ℕ)
    (j : Fin p.members.length) :
    (memberTildeAEList G p xSeq j).length ≤ (p.members[j.1]'j.2).eList.length + G.numEdges := by
  rw [memberTildeAEList, List.length_append]
  have h := length_extraEdges_le_numEdges G p xSeq j
  omega

/-- Inner loop pushing `(u, v, 0), ..., (u, v, mult - 1)` to `a_buf`. -/
def pushPairEdgesLoop (a_buf : Arr) (r_pos r_u r_v r_mult r_c : Reg) : Cmd :=
  .seq (.assign r_c (.const 0))
    (forUp r_c (.reg r_mult) (bufPush3 a_buf r_pos r_u r_v r_c))

theorem pushPairEdgesLoop_exec {w : ℕ} (a_buf r_pos r_u r_v r_mult r_c : ℕ)
    (hne_pc : r_pos ≠ r_c) (hne_uc : r_u ≠ r_c) (hne_vc : r_v ≠ r_c) (hne_mc : r_mult ≠ r_c)
    (hne_pu : r_pos ≠ r_u) (hne_pv : r_pos ≠ r_v) (hne_pm : r_pos ≠ r_mult)
    (u v mult rem : ℕ) (hw : 3 < 2 ^ w) (hu_w : u < 2 ^ w) (hv_w : v < 2 ^ w)
    (hm_w : mult < 2 ^ w) :
    ∀ (k : ℕ),
      k ≤ mult →
      ∀ (pfx : List ℕ) {s : State},
        pfx.length + 3 * (mult - k) < 2 ^ w →
        s.arrs a_buf = pfx ++ List.replicate (3 * (mult - k) + rem) 0 →
        s.regs r_pos = pfx.length →
        s.regs r_u = u →
        s.regs r_v = v →
        s.regs r_mult = mult →
        s.regs r_c = k →
        ∃ s' t,
          Exec w (forUp r_c (.reg r_mult) (bufPush3 a_buf r_pos r_u r_v r_c)) s s' t ∧
          t ≤ 3 + 26 * (mult - k) ∧
          s'.arrs a_buf =
            pfx ++ ((List.range' k (mult - k)).flatMap (fun c => [u, v, c])) ++
              List.replicate rem 0 ∧
          s'.regs r_pos = pfx.length + 3 * (mult - k) ∧
          (∀ a : ℕ, a ≠ a_buf → s'.arrs a = s.arrs a) ∧
          (∀ r : ℕ, r ≠ r_pos → r ≠ r_c → s'.regs r = s.regs r) := by
  have h0_w : 0 < 2 ^ w := by omega
  have h1_w : 1 < 2 ^ w := by omega
  intro k hk
  generalize hdiff : mult - k = d
  induction d generalizing k with
  | zero =>
    intro pfx s _ hbuf hrpos _ _ hrmult hrc
    have hk_eq : k = mult := by omega
    subst hk_eq
    have hcond : (Expr.op .lt (.reg r_c) (.reg r_mult)).eval w s = some 0 := by
      simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hrc, hrmult, hm_w, h0_w]
    simp only [Nat.mul_zero, Nat.zero_add, List.range'_zero, List.flatMap_nil, List.append_nil] at hbuf ⊢
    exact ⟨s, 3, .while_false hcond, by omega, hbuf, hrpos, fun _ _ => rfl, fun _ _ _ => rfl⟩
  | succ d ih =>
    intro pfx s hpfx_w hbuf hrpos hru hrv hrmult hrc
    have hk_lt : k < mult := by omega
    have hk_w : k < 2 ^ w := by omega
    have hk1_w : k + 1 < 2 ^ w := by omega
    have hcond : (Expr.op .lt (.reg r_c) (.reg r_mult)).eval w s = some 1 := by
      simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hrc, hrmult, hk_w, hm_w, hk_lt, h1_w]
    have hbuf_split :
        s.arrs a_buf = pfx ++ List.replicate ((3 * d + rem) + 3) 0 := by
      have hrep : 3 * (d + 1) + rem = (3 * d + rem) + 3 := by omega
      rwa [← hrep]
    rcases bufPush3_exec a_buf r_pos r_u r_v r_c pfx (3 * d + rem) u v k
        hw (by omega) hu_w hv_w hk_w hbuf_split hrpos hru hrv hrc with
      ⟨s₁, t₁, hex₁, ht₁, hbuf₁, hrpos₁, harr₁, hreg₁⟩
    have hrc₁ : s₁.regs r_c = k := by rw [hreg₁ r_c hne_pc.symm, hrc]
    let s₂ := s₁.setReg r_c (k + 1)
    have hex₂ : Exec w (.assign r_c (.op .add (.reg r_c) (.const 1))) s₁ s₂ 4 :=
      .assign (by simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hrc₁, hk_w, h1_w, hk1_w])
    rcases ih (k + 1) (by omega) (by omega) (pfx ++ [u, v, k]) (s := s₂)
        (by simp; omega)
        (by simpa [s₂] using hbuf₁)
        (by simp [s₂, State.setReg, hne_pc, hrpos₁])
        (by simp [s₂, State.setReg, hne_uc, hreg₁ r_u hne_pu.symm, hru])
        (by simp [s₂, State.setReg, hne_vc, hreg₁ r_v hne_pv.symm, hrv])
        (by simp [s₂, State.setReg, hne_mc, hreg₁ r_mult hne_pm.symm, hrmult])
        (by simp [s₂]) with
      ⟨s₃, t₃, hex₃, ht₃, hbuf₃, hrpos₃, harr₃, hreg₃⟩
    have hrng :
        (pfx ++ [u, v, k]) ++ (List.range' (k + 1) d).flatMap (fun c => [u, v, c]) =
          pfx ++ (List.range' k (d + 1)).flatMap (fun c => [u, v, c]) := by
      simp [List.range'_succ, List.append_assoc]
    rw [hrng] at hbuf₃
    refine ⟨s₃, 3 + (t₁ + 4) + t₃,
      .while_true hcond (by omega) (.seq hex₁ hex₂) hex₃,
      by omega, hbuf₃,
      by simp only [List.length_append, List.length_cons, List.length_nil] at hrpos₃; omega,
      fun a ha => (harr₃ a ha).trans (harr₁ a ha),
      fun r hr₁ hr₂ => by
        rw [hreg₃ r hr₁ hr₂]
        simp [s₂, State.setReg, hr₂, hreg₁ r hr₁]⟩

/-- Expression evaluating to `1` if and only if `(u, v)` satisfies the extra-edge condition for
member `j`. -/
def evalExtraCondExpr (r_ux r_vx r_uK r_vK r_own r_j : Reg) : Expr :=
  .op .mul
    (.op .mul
      (.op .lt (.const 0) (.op .add (.reg r_ux) (.reg r_vx)))
      (.op .lt (.const 0) (.op .add (.reg r_ux) (.reg r_uK))))
    (.op .mul
      (.op .lt (.const 0) (.op .add (.reg r_vx) (.reg r_vK)))
      (.op .eq (.reg r_own) (.reg r_j)))

theorem evalExtraCondExpr_eval {w : ℕ} (r_ux r_vx r_uK r_vK r_own r_j : Reg)
    (P_ux P_vx P_uK P_vK : Prop) [Decidable P_ux] [Decidable P_vx] [Decidable P_uK] [Decidable P_vK]
    (own j : ℕ) (hw : 2 < 2 ^ w) (hown_w : own < 2 ^ w) (hj_w : j < 2 ^ w)
    (st : State)
    (hux : st.regs r_ux = if P_ux then 1 else 0)
    (hvx : st.regs r_vx = if P_vx then 1 else 0)
    (huK : st.regs r_uK = if P_uK then 1 else 0)
    (hvK : st.regs r_vK = if P_vK then 1 else 0)
    (hown : st.regs r_own = own)
    (hrj : st.regs r_j = j) :
    (evalExtraCondExpr r_ux r_vx r_uK r_vK r_own r_j).eval w st =
      some (if (P_ux ∨ P_vx) ∧ (P_ux ∨ P_uK) ∧ (P_vx ∨ P_vK) ∧ own = j then 1 else 0) := by
  have h0_w : 0 < 2 ^ w := by omega
  have h1_w : 1 < 2 ^ w := by omega
  have hc1 :
      (Expr.op .lt (.const 0) (.op .add (.reg r_ux) (.reg r_vx))).eval w st =
        some (if P_ux ∨ P_vx then 1 else 0) := by
    by_cases h1 : P_ux <;> by_cases h2 : P_vx <;>
      simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hux, hvx, h1, h2, h0_w, h1_w, hw]
  have hc2 :
      (Expr.op .lt (.const 0) (.op .add (.reg r_ux) (.reg r_uK))).eval w st =
        some (if P_ux ∨ P_uK then 1 else 0) := by
    by_cases h1 : P_ux <;> by_cases h2 : P_uK <;>
      simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hux, huK, h1, h2, h0_w, h1_w, hw]
  have hc3 :
      (Expr.op .lt (.const 0) (.op .add (.reg r_vx) (.reg r_vK))).eval w st =
        some (if P_vx ∨ P_vK then 1 else 0) := by
    by_cases h1 : P_vx <;> by_cases h2 : P_vK <;>
      simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hvx, hvK, h1, h2, h0_w, h1_w, hw]
  have hc4 :
      (Expr.op .eq (.reg r_own) (.reg r_j)).eval w st =
        some (if own = j then 1 else 0) := by
    by_cases h5 : own = j <;>
      simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hown, hrj, h5, hown_w, hj_w, h0_w, h1_w]
  unfold evalExtraCondExpr
  generalize (Expr.op .lt (.const 0) (.op .add (.reg r_ux) (.reg r_vx))) = e1 at hc1 ⊢
  generalize (Expr.op .lt (.const 0) (.op .add (.reg r_ux) (.reg r_uK))) = e2 at hc2 ⊢
  generalize (Expr.op .lt (.const 0) (.op .add (.reg r_vx) (.reg r_vK))) = e3 at hc3 ⊢
  generalize (Expr.op .eq (.reg r_own) (.reg r_j)) = e4 at hc4 ⊢
  simp only [Expr.eval, hc1, hc2, hc3, hc4, BinOp.eval, BinOp.raw]
  by_cases ha : P_ux ∨ P_vx <;> by_cases hb : P_ux ∨ P_uK <;>
    by_cases hc : P_vx ∨ P_vK <;> by_cases hd : own = j <;>
    simp [ha, hb, hc, hd, checkWord, h0_w, h1_w]

/-- If `r_flag = 0`, read `a_arr[r_idx]` into `r_dst`; otherwise `.skip`. -/
def condReadArrProg (a_arr : Arr) (r_flag r_idx r_dst : Reg) : Cmd :=
  .ifEq (.reg r_flag) (.const 0)
    (.assign r_dst (.read a_arr (.reg r_idx)))
    .skip

theorem condReadArrProg_exec {w : ℕ} (a_arr r_flag r_idx r_dst : ℕ)
    (P : Prop) [Decidable P] (idx val : ℕ)
    (hw : 1 < 2 ^ w) (hidx_w : idx < 2 ^ w) (hval_w : val < 2 ^ w)
    {s : State}
    (hflag : s.regs r_flag = if P then 1 else 0)
    (hridx : s.regs r_idx = idx)
    (hlen : idx < (s.arrs a_arr).length)
    (hget : (s.arrs a_arr)[idx]'hlen = val) :
    ∃ s' t,
      Exec w (condReadArrProg a_arr r_flag r_idx r_dst) s s' t ∧
      t ≤ 6 ∧
      s'.regs r_dst = (if ¬P then val else s.regs r_dst) ∧
      (∀ a : ℕ, s'.arrs a = s.arrs a) ∧
      (∀ r : ℕ, r ≠ r_dst → s'.regs r = s.regs r) := by
  have h0_w : 0 < 2 ^ w := by omega
  by_cases hP : P
  · have hcond : (Expr.op .eq (.reg r_flag) (.const 0)).eval w s = some 0 := by
      simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hflag, hP, h0_w, hw]
    refine ⟨s, 3 + 1, .if_false hcond (.skip s), by omega,
      by simp [hP], fun _ => rfl, fun _ _ => rfl⟩
  · have hcond : (Expr.op .eq (.reg r_flag) (.const 0)).eval w s = some 1 := by
      simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hflag, hP, h0_w, hw]
    have hex_rd : Exec w (.assign r_dst (.read a_arr (.reg r_idx))) s (s.setReg r_dst val) 3 :=
      .assign (by simp [Expr.eval, checkWord, hridx, hidx_w, hlen, hget, hval_w])
    refine ⟨s.setReg r_dst val, 3 + 3, .if_true hcond (by omega) hex_rd, by omega,
      by simp [hP], fun _ => rfl, fun r hr => by simp [State.setReg, hr]⟩

/-- Loop body for scanning active pairs of `G` in `buildTildeAEListProg`. -/
def scanExtraEdgesBody (a_G a_xInd a_KInd a_owner a_buf : Arr)
    (r_j r_pos r_tildeELen r_base : Reg) : Cmd :=
  let r_k := r_base
  let r_idx := r_base + 1
  let r_u := r_base + 2
  let r_v := r_base + 3
  let r_ux := r_base + 4
  let r_vx := r_base + 5
  let r_uK := r_base + 6
  let r_vK := r_base + 7
  let r_own := r_base + 8
  let r_keep := r_base + 9
  let r_mult := r_base + 10
  let r_c := r_base + 11
  .seq (readTripleEndpoints a_G r_k r_idx r_u r_v)
    (.seq (.assign r_ux (.read a_xInd (.reg r_u)))
      (.seq (.assign r_vx (.read a_xInd (.reg r_v)))
        (.seq (.assign r_uK (.read a_KInd (.reg r_u)))
          (.seq (.assign r_vK (.read a_KInd (.reg r_v)))
            (.seq (.assign r_own (.const 0))
              (.seq (condReadArrProg a_owner r_vx r_v r_own)
                (.seq (condReadArrProg a_owner r_ux r_u r_own)
                  (.seq (.assign r_keep (evalExtraCondExpr r_ux r_vx r_uK r_vK r_own r_j))
                    (.ifEq (.reg r_keep) (.const 1)
                      (.seq (.assign r_mult (.read a_G (.op .add (.reg r_idx) (.const 2))))
                        (.seq (.assign r_tildeELen (.op .add (.reg r_tildeELen) (.reg r_mult)))
                          (pushPairEdgesLoop a_buf r_pos r_u r_v r_mult r_c)))
                      .skip)))))))))

theorem scanExtraEdgesLoop_exec {w n : ℕ} (G : MultiDigraph n) {X' : Finset (Fin n)}
    (p : ParsedCase3Block (G.deleteVertices X') X') (xSeq : List ℕ)
    (j : Fin p.members.length)
    (a_G a_xInd a_KInd a_owner a_buf : ℕ)
    (r_j r_pos r_tildeELen r_numP r_base : ℕ)
    (hne_Gb : a_G ≠ a_buf) (hne_xb : a_xInd ≠ a_buf)
    (hne_Kb : a_KInd ≠ a_buf) (hne_ob : a_owner ≠ a_buf)
    (hr_j : r_j < r_base) (hr_pos : r_pos < r_base)
    (hr_len : r_tildeELen < r_base) (hr_numP : r_numP < r_base)
    (hne_pl : r_pos ≠ r_tildeELen) (hne_pj : r_pos ≠ r_j) (hne_pn : r_pos ≠ r_numP)
    (hne_lj : r_tildeELen ≠ r_j) (hne_ln : r_tildeELen ≠ r_numP)
    (hw : 3 < 2 ^ w) (hn_w : n < 2 ^ w) (hM_w : p.members.length < 2 ^ w)
    (henc_w : 2 + 3 * G.numActivePairs < 2 ^ w)
    (extraG : List ℕ) (suff : List (Fin n × Fin n)) :
    ∀ (pref : List (Fin n × Fin n)) (esSoFar : List (ℕ × ℕ × ℕ)) (rem : ℕ) {s : State},
      G.activePairsList = pref ++ suff →
      3 * (esSoFar.length + G.sumEdgeMult suff) + 1 < 2 ^ w →
      s.arrs a_G = G.enc ++ extraG →
      s.arrs a_xInd = bitSetList (Finset.univ.filter (fun u : Fin n => u.1 ∈ xSeq)) →
      s.arrs a_KInd = bitSetList (Finset.univ.filter (fun u : Fin n => u.1 ∈ p.K_vList)) →
      s.arrs a_owner = List.ofFn (fun u : Fin n => vertOwner p u.1) →
      s.arrs a_buf =
        encEdgeTriples esSoFar ++ List.replicate (3 * G.sumEdgeMult suff + rem) 0 →
      s.regs r_j = j.1 →
      s.regs r_pos = 3 * esSoFar.length →
      s.regs r_tildeELen = esSoFar.length →
      s.regs r_numP = G.numActivePairs →
      s.regs r_base = pref.length →
      ∃ s' t,
        Exec w
          (forUp r_base (.reg r_numP)
            (scanExtraEdgesBody a_G a_xInd a_KInd a_owner a_buf r_j r_pos r_tildeELen r_base))
          s s' t ∧
        t ≤ 3 + 95 * suff.length + 26 * G.sumEdgeMult suff ∧
        s'.arrs a_buf =
          encEdgeTriples (esSoFar ++ extraEdgesFromPairs G p xSeq j.1 suff) ++
            List.replicate
              (3 * (G.sumEdgeMult suff - (extraEdgesFromPairs G p xSeq j.1 suff).length) + rem) 0 ∧
        s'.regs r_pos = 3 * (esSoFar ++ extraEdgesFromPairs G p xSeq j.1 suff).length ∧
        s'.regs r_tildeELen = (esSoFar ++ extraEdgesFromPairs G p xSeq j.1 suff).length ∧
        (∀ a : ℕ, a ≠ a_buf → s'.arrs a = s.arrs a) ∧
        (∀ r < r_base, r ≠ r_pos → r ≠ r_tildeELen → s'.regs r = s.regs r) := by
  have h0_w : 0 < 2 ^ w := by omega
  have h1_w : 1 < 2 ^ w := by omega
  have h2_w : 2 < 2 ^ w := by omega
  induction suff with
  | nil =>
    intro pref esSoFar rem s hsplit _ _ _ _ _ hbuf _ hrpos hrlen hrnumP hrbase
    rw [List.append_nil] at hsplit
    have hk_eq : pref.length = G.numActivePairs := by
      unfold MultiDigraph.numActivePairs; rw [hsplit]
    have hnp_w : G.numActivePairs < 2 ^ w := by omega
    have hcond : (Expr.op .lt (.reg r_base) (.reg r_numP)).eval w s = some 0 := by
      simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hrbase, hrnumP, hk_eq, hnp_w, h0_w]
    simp only [MultiDigraph.sumEdgeMult_nil, Nat.mul_zero, Nat.zero_add] at hbuf
    simp only [extraEdgesFromPairs_nil, List.append_nil, List.length_nil,
      MultiDigraph.sumEdgeMult_nil, Nat.sub_zero, Nat.mul_zero, Nat.zero_add]
    exact ⟨s, 3, .while_false hcond, by omega, hbuf, hrpos, hrlen,
      fun _ _ => rfl, fun _ _ _ _ => rfl⟩
  | cons pair suff ih =>
    intro pref esSoFar rem s hsplit hcap_w hG hxInd hKInd howner hbuf hrj hrpos hrlen hrnumP hrbase
    rcases pair with ⟨u, v⟩
    let k := pref.length
    have hk_lt : k < G.numActivePairs := by
      unfold MultiDigraph.numActivePairs
      rw [hsplit, List.length_append, List.length_cons]
      omega
    have hk_w : k < 2 ^ w := by omega
    have hnp_w : G.numActivePairs < 2 ^ w := by omega
    have hpair_eq : G.activePairsList[k]'hk_lt = (u, v) := by
      have hlen : k < (pref ++ (u, v) :: suff).length := by rw [← hsplit]; exact hk_lt
      have hget : G.activePairsList[k]'hk_lt = (pref ++ (u, v) :: suff)[k]'hlen := by simp [hsplit]
      rw [hget, List.getElem_append_right (le_refl k)]
      simp [k]
    have hcond : (Expr.op .lt (.reg r_base) (.reg r_numP)).eval w s = some 1 := by
      simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hrbase, hrnumP, hk_w, hnp_w, hk_lt, h1_w, k]
    rcases readTripleEndpoints_exec G extraG a_G r_base (r_base + 1) (r_base + 2) (r_base + 3)
        k s (by omega) (by omega) (by omega) hw hn_w henc_w hk_lt hG hrbase with
      ⟨s₁, t₁, hex₁, ht₁, hridx₁, hru₁, hrv₁, harr₁, hreg₁⟩
    rw [hpair_eq] at hru₁ hrv₁
    dsimp only at hru₁ hrv₁
    have hG₁ : s₁.arrs a_G = G.enc ++ extraG := by rw [harr₁]; exact hG
    have hxInd₁ : s₁.arrs a_xInd = bitSetList (Finset.univ.filter (fun x : Fin n => x.1 ∈ xSeq)) := by
      rw [harr₁]; exact hxInd
    have hKInd₁ : s₁.arrs a_KInd = bitSetList (Finset.univ.filter (fun x : Fin n => x.1 ∈ p.K_vList)) := by
      rw [harr₁]; exact hKInd
    have howner₁ : s₁.arrs a_owner = List.ofFn (fun x : Fin n => vertOwner p x.1) := by
      rw [harr₁]; exact howner
    have hu_w : u.1 < 2 ^ w := Nat.lt_trans u.2 hn_w
    have hv_w : v.1 < 2 ^ w := Nat.lt_trans v.2 hn_w
    let ux := if u.1 ∈ xSeq then 1 else 0
    let vx := if v.1 ∈ xSeq then 1 else 0
    let uK := if u.1 ∈ p.K_vList then 1 else 0
    let vK := if v.1 ∈ p.K_vList then 1 else 0
    have hux_w : ux < 2 ^ w := by dsimp [ux]; split_ifs <;> omega
    have hvx_w : vx < 2 ^ w := by dsimp [vx]; split_ifs <;> omega
    have huK_w : uK < 2 ^ w := by dsimp [uK]; split_ifs <;> omega
    have hvK_w : vK < 2 ^ w := by dsimp [vK]; split_ifs <;> omega
    have hu_xlen : u.1 < (s₁.arrs a_xInd).length := by rw [hxInd₁, length_bitSetList]; exact u.2
    have hget_ux : (s₁.arrs a_xInd)[u.1]'hu_xlen = ux := by simp [hxInd₁, bitSetList, ux]
    let s₂ := s₁.setReg (r_base + 4) ux
    have hex₂ : Exec w (.assign (r_base + 4) (.read a_xInd (.reg (r_base + 2)))) s₁ s₂ 3 :=
      .assign (by simp [Expr.eval, checkWord, hru₁, hu_w, hu_xlen, hget_ux, hux_w])
    have hv_xlen : v.1 < (s₂.arrs a_xInd).length := by simp [s₂, hxInd₁, length_bitSetList, v.2]
    have hget_vx : (s₂.arrs a_xInd)[v.1]'hv_xlen = vx := by simp [s₂, hxInd₁, bitSetList, vx]
    let s₃ := s₂.setReg (r_base + 5) vx
    have hex₃ : Exec w (.assign (r_base + 5) (.read a_xInd (.reg (r_base + 3)))) s₂ s₃ 3 :=
      .assign (by
        have hrv₂ : s₂.regs (r_base + 3) = v.1 := by simp [s₂, State.setReg, hrv₁]
        simp [Expr.eval, checkWord, hrv₂, hv_w, hv_xlen, hget_vx, hvx_w])
    have hu_Klen : u.1 < (s₃.arrs a_KInd).length := by simp [s₃, s₂, hKInd₁, length_bitSetList, u.2]
    have hget_uK : (s₃.arrs a_KInd)[u.1]'hu_Klen = uK := by simp [s₃, s₂, hKInd₁, bitSetList, uK]
    let s₄ := s₃.setReg (r_base + 6) uK
    have hex₄ : Exec w (.assign (r_base + 6) (.read a_KInd (.reg (r_base + 2)))) s₃ s₄ 3 :=
      .assign (by
        have hru₃ : s₃.regs (r_base + 2) = u.1 := by simp [s₃, s₂, State.setReg, hru₁]
        simp [Expr.eval, checkWord, hru₃, hu_w, hu_Klen, hget_uK, huK_w])
    have hv_Klen : v.1 < (s₄.arrs a_KInd).length := by
      simp [s₄, s₃, s₂, hKInd₁, length_bitSetList, v.2]
    have hget_vK : (s₄.arrs a_KInd)[v.1]'hv_Klen = vK := by
      simp [s₄, s₃, s₂, hKInd₁, bitSetList, vK]
    let s₅ := s₄.setReg (r_base + 7) vK
    have hex₅ : Exec w (.assign (r_base + 7) (.read a_KInd (.reg (r_base + 3)))) s₄ s₅ 3 :=
      .assign (by
        have hrv₄ : s₄.regs (r_base + 3) = v.1 := by simp [s₄, s₃, s₂, State.setReg, hrv₁]
        simp [Expr.eval, checkWord, hrv₄, hv_w, hv_Klen, hget_vK, hvK_w])
    let s₆ := s₅.setReg (r_base + 8) 0
    have hex₆ : Exec w (.assign (r_base + 8) (.const 0)) s₅ s₆ 2 :=
      .assign (by simp [Expr.eval, checkWord, h0_w])
    have hown_lt : ∀ x : Fin n, vertOwner p x.1 < 2 ^ w := by
      intro x
      unfold vertOwner
      cases (List.finRange p.members.length).find?
          (fun j' => decide (x.1 ∈ (p.members[j'.1]'j'.2).vList)) with
      | none => exact h0_w
      | some j' => exact Nat.lt_trans j'.2 hM_w
    have hv_olen₆ : v.1 < (s₆.arrs a_owner).length := by
      simp [s₆, s₅, s₄, s₃, s₂, howner₁, v.2]
    rcases condReadArrProg_exec a_owner (r_base + 5) (r_base + 3) (r_base + 8)
        (v.1 ∈ xSeq) v.1 (vertOwner p v.1) h1_w hv_w (hown_lt v) (s := s₆)
        (by simp [s₆, s₅, s₄, s₃, State.setReg, vx])
        (by simp [s₆, s₅, s₄, s₃, s₂, State.setReg, hrv₁])
        hv_olen₆
        (by simp [s₆, s₅, s₄, s₃, s₂, howner₁]) with
      ⟨s₇, t₇, hex₇, ht₇, hown₇, harr₇, hreg₇⟩
    have hr8_s₆ : s₆.regs (r_base + 8) = 0 := by simp [s₆]
    rw [hr8_s₆] at hown₇
    have hu_olen₇ : u.1 < (s₇.arrs a_owner).length := by
      rw [harr₇]
      simp [s₆, s₅, s₄, s₃, s₂, howner₁, u.2]
    rcases condReadArrProg_exec a_owner (r_base + 4) (r_base + 2) (r_base + 8)
        (u.1 ∈ xSeq) u.1 (vertOwner p u.1) h1_w hu_w (hown_lt u) (s := s₇)
        (by rw [hreg₇ (r_base + 4) (by omega)]; simp [s₆, s₅, s₄, s₃, s₂, State.setReg, ux])
        (by rw [hreg₇ (r_base + 2) (by omega)]; simp [s₆, s₅, s₄, s₃, s₂, State.setReg, hru₁])
        hu_olen₇
        (by simp [harr₇, s₆, s₅, s₄, s₃, s₂, howner₁]) with
      ⟨s₈, t₈, hex₈, ht₈, hown₈, harr₈, hreg₈⟩
    let own := incidentOwner p xSeq u.1 v.1
    have hown₈_eq : s₈.regs (r_base + 8) = own := by
      rw [hown₈, hown₇]
      rfl
    let condProp : Prop :=
      (u.1 ∈ xSeq ∨ v.1 ∈ xSeq) ∧
      (u.1 ∈ xSeq ∨ u.1 ∈ p.K_vList) ∧
      (v.1 ∈ xSeq ∨ v.1 ∈ p.K_vList) ∧
      own = j.1
    let keepVal : ℕ := if condProp then 1 else 0
    have hown_w : own < 2 ^ w := by
      dsimp [own, incidentOwner]
      split_ifs <;> first | exact hown_lt u | exact hown_lt v | exact h0_w
    have hj_w : j.1 < 2 ^ w := Nat.lt_trans j.2 hM_w
    have hrj₈ : s₈.regs r_j = j.1 := by
      rw [hreg₈ r_j (by omega), hreg₇ r_j (by omega)]
      simp [s₆, s₅, s₄, s₃, s₂, State.setReg,
        show r_j ≠ r_base + 8 by omega, show r_j ≠ r_base + 7 by omega,
        show r_j ≠ r_base + 6 by omega, show r_j ≠ r_base + 5 by omega,
        show r_j ≠ r_base + 4 by omega,
        hreg₁ r_j (by omega) (by omega) (by omega), hrj]
    have hux₈ : s₈.regs (r_base + 4) = ux := by
      rw [hreg₈ (r_base + 4) (by omega), hreg₇ (r_base + 4) (by omega)]
      simp [s₆, s₅, s₄, s₃, s₂, State.setReg]
    have hvx₈ : s₈.regs (r_base + 5) = vx := by
      rw [hreg₈ (r_base + 5) (by omega), hreg₇ (r_base + 5) (by omega)]
      simp [s₆, s₅, s₄, s₃, State.setReg]
    have huK₈ : s₈.regs (r_base + 6) = uK := by
      rw [hreg₈ (r_base + 6) (by omega), hreg₇ (r_base + 6) (by omega)]
      simp [s₆, s₅, s₄, State.setReg]
    have hvK₈ : s₈.regs (r_base + 7) = vK := by
      rw [hreg₈ (r_base + 7) (by omega), hreg₇ (r_base + 7) (by omega)]
      simp [s₆, s₅, State.setReg]
    have heval_keep :
        (evalExtraCondExpr (r_base + 4) (r_base + 5) (r_base + 6) (r_base + 7)
          (r_base + 8) r_j).eval w s₈ = some keepVal :=
      evalExtraCondExpr_eval (r_base + 4) (r_base + 5) (r_base + 6) (r_base + 7)
        (r_base + 8) r_j (u.1 ∈ xSeq) (v.1 ∈ xSeq) (u.1 ∈ p.K_vList) (v.1 ∈ p.K_vList)
        own j.1 h2_w hown_w hj_w s₈ hux₈ hvx₈ huK₈ hvK₈ hown₈_eq hrj₈
    let s₉ := s₈.setReg (r_base + 9) keepVal
    have hex₉ :
        Exec w
          (.assign (r_base + 9)
            (evalExtraCondExpr (r_base + 4) (r_base + 5) (r_base + 6) (r_base + 7)
              (r_base + 8) r_j))
          s₈ s₉ 22 :=
      .assign heval_keep
    let pairEdges : List (ℕ × ℕ × ℕ) :=
      if condProp then (List.range (G.edgeMult u v)).map (fun c => (u.1, v.1, c)) else []
    have hpairEdges_eq :
        extraEdgesFromPairs G p xSeq j.1 ((u, v) :: suff) =
          pairEdges ++ extraEdgesFromPairs G p xSeq j.1 suff := rfl
    have hsum_cons : G.sumEdgeMult ((u, v) :: suff) = G.edgeMult u v + G.sumEdgeMult suff :=
      G.sumEdgeMult_cons (u, v) suff
    have harr_s₉ : ∀ a : ℕ, s₉.arrs a = s.arrs a := fun a => by
      simp [s₉, harr₈, harr₇, s₆, s₅, s₄, s₃, s₂, harr₁]
    have hreg_s₉ : ∀ r : ℕ, r < r_base + 4 → r ≠ r_base + 1 → r ≠ r_base + 2 → r ≠ r_base + 3 →
        s₉.regs r = s.regs r := fun r hr h1 h2 h3 => by
      simp only [s₉, State.setReg_regs]
      rw [hreg₈ r (by omega), hreg₇ r (by omega)]
      simp [s₆, s₅, s₄, s₃, s₂, State.setReg,
        show r ≠ r_base + 9 by omega,
        show r ≠ r_base + 8 by omega, show r ≠ r_base + 7 by omega,
        show r ≠ r_base + 6 by omega, show r ≠ r_base + 5 by omega,
        show r ≠ r_base + 4 by omega, hreg₁ r h1 h2 h3]
    have hru₉ : s₉.regs (r_base + 2) = u.1 := by
      simp only [s₉, State.setReg_regs]
      rw [hreg₈ (r_base + 2) (by omega), hreg₇ (r_base + 2) (by omega)]
      simp [s₆, s₅, s₄, s₃, s₂, State.setReg, hru₁]
    have hrv₉ : s₉.regs (r_base + 3) = v.1 := by
      simp only [s₉, State.setReg_regs]
      rw [hreg₈ (r_base + 3) (by omega), hreg₇ (r_base + 3) (by omega)]
      simp [s₆, s₅, s₄, s₃, s₂, State.setReg, hrv₁]
    have hridx₉ : s₉.regs (r_base + 1) = 2 + 3 * k := by
      simp only [s₉, State.setReg_regs]
      rw [hreg₈ (r_base + 1) (by omega), hreg₇ (r_base + 1) (by omega)]
      simp [s₆, s₅, s₄, s₃, s₂, State.setReg, hridx₁]
    have hbranch :
        ∃ s₁₀ t₁₀,
          Exec w
            (.ifEq (.reg (r_base + 9)) (.const 1)
              (.seq (.assign (r_base + 10) (.read a_G (.op .add (.reg (r_base + 1)) (.const 2))))
                (.seq (.assign r_tildeELen (.op .add (.reg r_tildeELen) (.reg (r_base + 10))))
                  (pushPairEdgesLoop a_buf r_pos (r_base + 2) (r_base + 3) (r_base + 10) (r_base + 11))))
              .skip)
            s₉ s₁₀ t₁₀ ∧
          t₁₀ ≤ 17 + 26 * G.edgeMult u v ∧
          s₁₀.arrs a_buf =
            encEdgeTriples (esSoFar ++ pairEdges) ++
              List.replicate
                (3 * (G.edgeMult u v - pairEdges.length + G.sumEdgeMult suff) + rem) 0 ∧
          s₁₀.regs r_pos = 3 * (esSoFar ++ pairEdges).length ∧
          s₁₀.regs r_tildeELen = (esSoFar ++ pairEdges).length ∧
          (∀ a : ℕ, a ≠ a_buf → s₁₀.arrs a = s.arrs a) ∧
          (∀ r ≤ r_base, r ≠ r_pos → r ≠ r_tildeELen → s₁₀.regs r = s.regs r) := by
      have hrk₉ : s₉.regs (r_base + 9) = keepVal := by simp [s₉]
      have hrpos₉ : s₉.regs r_pos = 3 * esSoFar.length := by
        rw [hreg_s₉ r_pos (by omega) (by omega) (by omega) (by omega), hrpos]
      have hrlen₉ : s₉.regs r_tildeELen = esSoFar.length := by
        rw [hreg_s₉ r_tildeELen (by omega) (by omega) (by omega) (by omega), hrlen]
      have hbuf₉ : s₉.arrs a_buf =
          encEdgeTriples esSoFar ++ List.replicate (3 * G.sumEdgeMult ((u, v) :: suff) + rem) 0 := by
        rw [harr_s₉ a_buf, hbuf]
      by_cases hc : condProp
      · have hkeep1 : keepVal = 1 := by simp [keepVal, hc]
        have hpe_eq : pairEdges = (List.range (G.edgeMult u v)).map (fun c => (u.1, v.1, c)) := by
          simp [pairEdges, hc]
        have hG₉ : s₉.arrs a_G = G.enc ++ extraG := by
          rw [harr_s₉ a_G, hG]
        have hidx_w : 2 + 3 * k < 2 ^ w := by omega
        have hidx2_w : 2 + 3 * k + 2 < 2 ^ w := by omega
        rcases enc_getElem_triple_mult G extraG hG₉ hk_lt with ⟨hidx2_len, hget_m⟩
        rw [hpair_eq] at hget_m
        have hm_w : G.edgeMult u v < 2 ^ w := by
          rw [hsum_cons] at hcap_w; omega
        let s_m := s₉.setReg (r_base + 10) (G.edgeMult u v)
        have hex_m :
            Exec w (.assign (r_base + 10) (.read a_G (.op .add (.reg (r_base + 1)) (.const 2))))
              s₉ s_m 5 :=
          .assign (by simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord,
            hridx₉, hidx_w, h2_w, hidx2_w, hidx2_len, hget_m, hm_w])
        have hnewlen_w : esSoFar.length + G.edgeMult u v < 2 ^ w := by
          rw [hsum_cons] at hcap_w; omega
        let s_l := s_m.setReg r_tildeELen (esSoFar.length + G.edgeMult u v)
        have hex_l :
            Exec w (.assign r_tildeELen (.op .add (.reg r_tildeELen) (.reg (r_base + 10))))
              s_m s_l 4 :=
          .assign (by simp [s_m, State.setReg, show r_tildeELen ≠ r_base + 10 by omega,
            Expr.eval, BinOp.eval, BinOp.raw, checkWord, hrlen₉, hm_w, hnewlen_w,
            show esSoFar.length < 2 ^ w by omega])
        let s_c0 := s_l.setReg (r_base + 11) 0
        have hex_c0 : Exec w (.assign (r_base + 11) (.const 0)) s_l s_c0 2 :=
          .assign (by simp [Expr.eval, checkWord, h0_w])
        have hbuf_c0 :
            s_c0.arrs a_buf =
              encEdgeTriples esSoFar ++
                List.replicate (3 * (G.edgeMult u v - 0) + (3 * G.sumEdgeMult suff + rem)) 0 := by
          simp only [s_c0, s_l, s_m, State.setReg_arrs, hbuf₉, hsum_cons]
          have hrep : 3 * (G.edgeMult u v + G.sumEdgeMult suff) + rem =
              3 * (G.edgeMult u v - 0) + (3 * G.sumEdgeMult suff + rem) := by omega
          rw [hrep]
        rcases pushPairEdgesLoop_exec a_buf r_pos (r_base + 2) (r_base + 3)
            (r_base + 10) (r_base + 11)
            (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
            u.1 v.1 (G.edgeMult u v) (3 * G.sumEdgeMult suff + rem)
            hw hu_w hv_w hm_w 0 (Nat.zero_le _) (encEdgeTriples esSoFar) (s := s_c0)
            (by rw [length_encEdgeTriples]; rw [hsum_cons] at hcap_w; omega)
            hbuf_c0
            (by simp [s_c0, s_l, s_m, State.setReg, hne_pl,
              show r_pos ≠ r_base + 11 by omega, show r_pos ≠ r_base + 10 by omega,
              hrpos₉, length_encEdgeTriples])
            (by simp [s_c0, s_l, s_m, State.setReg, show r_base + 2 ≠ r_tildeELen by omega, hru₉])
            (by simp [s_c0, s_l, s_m, State.setReg, show r_base + 3 ≠ r_tildeELen by omega, hrv₉])
            (by simp [s_c0, s_l, s_m, State.setReg, show r_base + 10 ≠ r_tildeELen by omega])
            (by simp [s_c0]) with
          ⟨s₁₀, t_push, hex_push, ht_push, hbuf₁₀, hrpos₁₀, harr₁₀, hreg₁₀⟩
        rw [Nat.sub_zero] at ht_push hrpos₁₀
        have henc_pe :
            encEdgeTriples esSoFar ++
              (List.range' 0 (G.edgeMult u v - 0)).flatMap (fun c => [u.1, v.1, c]) =
              encEdgeTriples (esSoFar ++ pairEdges) := by
          rw [Nat.sub_zero, ← List.range_eq_range', hpe_eq, encEdgeTriples_append,
            encEdgeTriples_map_range]
        rw [henc_pe] at hbuf₁₀
        have hpe_len : pairEdges.length = G.edgeMult u v := by simp [hpe_eq]
        have hrem_eq :
            3 * G.sumEdgeMult suff + rem =
              3 * (G.edgeMult u v - pairEdges.length + G.sumEdgeMult suff) + rem := by
          rw [hpe_len, Nat.sub_self, Nat.zero_add]
        rw [hrem_eq] at hbuf₁₀
        refine ⟨s₁₀, 3 + (5 + (4 + (2 + t_push))),
          .if_true (v := 1) (by simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hrk₉, hkeep1, h1_w])
            (by decide) (.seq hex_m (.seq hex_l (.seq hex_c0 hex_push))),
          by omega, hbuf₁₀,
          by rw [hrpos₁₀, length_encEdgeTriples, List.length_append, hpe_len]; omega,
          by rw [hreg₁₀ r_tildeELen hne_pl.symm (by omega)]
             simp [s_c0, s_l, List.length_append, hpe_len, show r_tildeELen ≠ r_base + 11 by omega],
          fun a ha => by rw [harr₁₀ a ha]; simp [s_c0, s_l, s_m, harr_s₉ a],
          fun r hr hne₁ hne₂ => by
            rw [hreg₁₀ r hne₁ (by omega)]
            simp [s_c0, s_l, s_m, State.setReg,
              hne₂, show r ≠ r_base + 11 by omega, show r ≠ r_base + 10 by omega,
              hreg_s₉ r (by omega) (by omega) (by omega) (by omega)]⟩
      · have hkeep0 : keepVal = 0 := by simp [keepVal, hc]
        have hpe_eq : pairEdges = [] := by simp [pairEdges, hc]
        refine ⟨s₉, 3 + 1,
          .if_false (by simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hrk₉, hkeep0, h0_w, h1_w])
            (.skip s₉),
          by omega,
          by simpa [hpe_eq, hsum_cons] using hbuf₉,
          by simpa [hpe_eq] using hrpos₉,
          by simpa [hpe_eq] using hrlen₉,
          fun a _ => harr_s₉ a,
          fun r hr _ _ => hreg_s₉ r (by omega) (by omega) (by omega) (by omega)⟩
    rcases hbranch with ⟨s₁₀, t₁₀, hex₁₀, ht₁₀, hbuf₁₀, hrpos₁₀, hrlen₁₀, harr₁₀, hreg₁₀⟩
    have hrb₁₀ : s₁₀.regs r_base = k := by
      rw [hreg₁₀ r_base (le_refl r_base) (by omega) (by omega)]
      exact hrbase
    have hk1_w : k + 1 < 2 ^ w := by omega
    let s₁₁ := s₁₀.setReg r_base (k + 1)
    have hex_inc : Exec w (.assign r_base (.op .add (.reg r_base) (.const 1))) s₁₀ s₁₁ 4 :=
      .assign (by simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hrb₁₀, hk_w, h1_w, hk1_w])
    have hex_body :
        Exec w
          (.seq (scanExtraEdgesBody a_G a_xInd a_KInd a_owner a_buf r_j r_pos r_tildeELen r_base)
            (.assign r_base (.op .add (.reg r_base) (.const 1))))
          s s₁₁
          ((t₁ + (3 + (3 + (3 + (3 + (2 + (t₇ + (t₈ + (22 + t₁₀))))))))) + 4) :=
      .seq
        (.seq hex₁ (.seq hex₂ (.seq hex₃ (.seq hex₄ (.seq hex₅ (.seq hex₆ (.seq hex₇ (.seq hex₈
          (.seq hex₉ hex₁₀)))))))))
        hex_inc
    let rem' := 3 * (G.edgeMult u v - pairEdges.length) + rem
    have hbuf₁₁ :
        s₁₁.arrs a_buf =
          encEdgeTriples (esSoFar ++ pairEdges) ++
            List.replicate (3 * G.sumEdgeMult suff + rem') 0 := by
      simp only [s₁₁, State.setReg_arrs, hbuf₁₀, rem']
      have hrep :
          3 * (G.edgeMult u v - pairEdges.length + G.sumEdgeMult suff) + rem =
            3 * G.sumEdgeMult suff + (3 * (G.edgeMult u v - pairEdges.length) + rem) := by omega
      rw [hrep]
    have hpe_le : pairEdges.length ≤ G.edgeMult u v := by
      dsimp [pairEdges]; split_ifs <;> simp
    have hsplit' : G.activePairsList = (pref ++ [(u, v)]) ++ suff := by
      rw [List.append_assoc, List.singleton_append]; exact hsplit
    rcases ih (pref ++ [(u, v)]) (esSoFar ++ pairEdges) rem' (s := s₁₁)
        hsplit'
        (by rw [List.length_append]; rw [hsum_cons] at hcap_w; omega)
        (by simp [s₁₁, harr₁₀ a_G hne_Gb, hG])
        (by simp [s₁₁, harr₁₀ a_xInd hne_xb, hxInd])
        (by simp [s₁₁, harr₁₀ a_KInd hne_Kb, hKInd])
        (by simp [s₁₁, harr₁₀ a_owner hne_ob, howner])
        hbuf₁₁
        (by simp [s₁₁, State.setReg, show r_j ≠ r_base by omega,
          hreg₁₀ r_j (by omega) hne_pj.symm hne_lj.symm, hrj])
        (by simp [s₁₁, State.setReg, show r_pos ≠ r_base by omega, hrpos₁₀])
        (by simp [s₁₁, State.setReg, show r_tildeELen ≠ r_base by omega, hrlen₁₀])
        (by simp [s₁₁, State.setReg, show r_numP ≠ r_base by omega,
          hreg₁₀ r_numP (by omega) hne_pn.symm hne_ln.symm, hrnumP])
        (by simp [s₁₁, k]) with
      ⟨s₁₂, t₁₂, hex₁₂, ht₁₂, hbuf₁₂, hrpos₁₂, hrlen₁₂, harr₁₂, hreg₁₂⟩
    have hext_len :
        (extraEdgesFromPairs G p xSeq j.1 suff).length ≤ G.sumEdgeMult suff :=
      length_extraEdgesFromPairs_le G p xSeq j.1 suff
    have hrem_final :
        3 * (G.sumEdgeMult suff - (extraEdgesFromPairs G p xSeq j.1 suff).length) + rem' =
          3 * (G.sumEdgeMult ((u, v) :: suff) -
            (extraEdgesFromPairs G p xSeq j.1 ((u, v) :: suff)).length) + rem := by
      rw [hsum_cons, hpairEdges_eq, List.length_append]
      dsimp [rem']
      omega
    rw [List.append_assoc, ← hpairEdges_eq] at hbuf₁₂ hrpos₁₂ hrlen₁₂
    rw [hrem_final] at hbuf₁₂
    refine ⟨s₁₂,
      3 + ((t₁ + (3 + (3 + (3 + (3 + (2 + (t₇ + (t₈ + (22 + t₁₀))))))))) + 4) + t₁₂,
      .while_true hcond (by omega) hex_body hex₁₂,
      by rw [List.length_cons, hsum_cons]; omega, hbuf₁₂, hrpos₁₂, hrlen₁₂,
      fun a ha => (harr₁₂ a ha).trans (harr₁₀ a ha),
      fun r hr hne₁ hne₂ => by
        rw [hreg₁₂ r hr hne₁ hne₂]
        simp [s₁₁, State.setReg, show r ≠ r_base by omega,
          hreg₁₀ r (by omega) hne₁ hne₂]⟩

/-- Word RAM subprogram for Step 2 edge list construction (`buildTildeAEListProg`). -/
def buildTildeAEListProg (a_G a_xInd a_KInd a_owner a_rE a_buf a_tildeE : Arr)
    (r_rELen r_j r_m r_tildeELen r_base : Reg) : Cmd :=
  let r_pos := r_base
  let r_numP := r_base + 1
  let r_rEWords := r_base + 2
  let r_cap := r_base + 3
  let r_loop := r_base + 4
  .seq (.assign r_rEWords (.op .mul (.const 3) (.reg r_rELen)))
    (.seq (.assign r_cap (.op .add (.reg r_rEWords) (.op .mul (.const 3) (.reg r_m))))
      (.seq (initPrefixBufferProg a_buf (.reg r_cap) r_pos)
        (.seq (appendBufSliceProg a_rE a_buf r_rEWords r_pos r_loop)
          (.seq (.assign r_tildeELen (.reg r_rELen))
            (.seq (.assign r_numP (.read a_G (.const 1)))
              (.seq (.assign r_loop (.const 0))
                (.seq
                  (forUp r_loop (.reg r_numP)
                    (scanExtraEdgesBody a_G a_xInd a_KInd a_owner a_buf
                      r_j r_pos r_tildeELen r_loop))
                  (copyBufPrefixProg a_buf a_tildeE r_pos r_loop))))))))

theorem buildTildeAEListProg_exec {w n : ℕ} (G : MultiDigraph n) {X' : Finset (Fin n)}
    (p : ParsedCase3Block (G.deleteVertices X') X') (xSeq : List ℕ)
    (j : Fin p.members.length) (extraG : List ℕ)
    (a_G a_xInd a_KInd a_owner a_rE a_buf a_tildeE : ℕ)
    (r_rELen r_j r_m r_tildeELen r_base : ℕ)
    (hne_Gb : a_G ≠ a_buf) (hne_xb : a_xInd ≠ a_buf)
    (hne_Kb : a_KInd ≠ a_buf) (hne_ob : a_owner ≠ a_buf)
    (hne_rEb : a_rE ≠ a_buf) (hne_bt : a_buf ≠ a_tildeE)
    (hr_rELen : r_rELen < r_base) (hr_j : r_j < r_base)
    (hr_m : r_m < r_base) (hr_tildeELen : r_tildeELen < r_base)
    (_hne_rl : r_rELen ≠ r_tildeELen) (hne_jl : r_j ≠ r_tildeELen) (_hne_ml : r_m ≠ r_tildeELen)
    (hw : 3 < 2 ^ w) (hn_w : n < 2 ^ w) (hM_w : p.members.length < 2 ^ w)
    (henc_w : 2 + 3 * G.numActivePairs < 2 ^ w)
    (hcap_w : 3 * ((p.members[j.1]'j.2).eList.length + G.numEdges) + 1 < 2 ^ w)
    (hrE_words_w : ∀ x ∈ encEdgeTriples (p.members[j.1]'j.2).eList, x < 2 ^ w)
    {s : State}
    (hG : s.arrs a_G = G.enc ++ extraG)
    (hxInd : s.arrs a_xInd = bitSetList (Finset.univ.filter (fun u : Fin n => u.1 ∈ xSeq)))
    (hKInd : s.arrs a_KInd = bitSetList (Finset.univ.filter (fun u : Fin n => u.1 ∈ p.K_vList)))
    (howner : s.arrs a_owner = List.ofFn (fun u : Fin n => vertOwner p u.1))
    (hrE : s.arrs a_rE = encEdgeTriples (p.members[j.1]'j.2).eList)
    (hrrELen : s.regs r_rELen = (p.members[j.1]'j.2).eList.length)
    (hrj : s.regs r_j = j.1)
    (hrm : s.regs r_m = G.numEdges) :
    ∃ s' t,
      Exec w
        (buildTildeAEListProg a_G a_xInd a_KInd a_owner a_rE a_buf a_tildeE
          r_rELen r_j r_m r_tildeELen r_base)
        s s' t ∧
      t ≤ 102 * (p.members[j.1]'j.2).eList.length + 172 * G.numEdges + 50 ∧
      s'.arrs a_tildeE = encEdgeTriples (memberTildeAEList G p xSeq j) ∧
      s'.regs r_tildeELen = (memberTildeAEList G p xSeq j).length ∧
      (∀ a : ℕ, a ≠ a_buf → a ≠ a_tildeE → s'.arrs a = s.arrs a) ∧
      (∀ r < r_base, r ≠ r_tildeELen → s'.regs r = s.regs r) := by
  have h0_w : 0 < 2 ^ w := by omega
  have h1_w : 1 < 2 ^ w := by omega
  have h3_w : 3 < 2 ^ w := hw
  have hrELen_w : (p.members[j.1]'j.2).eList.length < 2 ^ w := by omega
  have h3rELen_w : 3 * (p.members[j.1]'j.2).eList.length < 2 ^ w := by omega
  have hm_w : G.numEdges < 2 ^ w := by omega
  have h3m_w : 3 * G.numEdges < 2 ^ w := by omega
  have hcap_lt : 3 * (p.members[j.1]'j.2).eList.length + 3 * G.numEdges < 2 ^ w := by omega
  let s₁ := s.setReg (r_base + 2) (3 * (p.members[j.1]'j.2).eList.length)
  have hex₁ : Exec w (.assign (r_base + 2) (.op .mul (.const 3) (.reg r_rELen))) s s₁ 4 :=
    .assign (by simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hrrELen, h3_w, hrELen_w, h3rELen_w])
  let s₂ := s₁.setReg (r_base + 3) (3 * (p.members[j.1]'j.2).eList.length + 3 * G.numEdges)
  have hex₂ :
      Exec w
        (.assign (r_base + 3)
          (.op .add (.reg (r_base + 2)) (.op .mul (.const 3) (.reg r_m))))
        s₁ s₂ 6 :=
    .assign (by simp [s₁, State.setReg, show r_m ≠ r_base + 2 by omega,
      Expr.eval, BinOp.eval, BinOp.raw, checkWord, hrm, h3_w, hm_w, h3m_w, h3rELen_w, hcap_lt])
  rcases initPrefixBufferProg_exec
      (cap := 3 * (p.members[j.1]'j.2).eList.length + 3 * G.numEdges)
      a_buf (.reg (r_base + 3)) r_base h1_w (s := s₂)
      (by simp [s₂, Expr.eval, checkWord, hcap_lt]) with
    ⟨s₃, t₃, hex₃, ht₃, hbuf₃, hrpos₃, harr₃, hreg₃⟩
  have hbuf₃' :
      IsPrefixBuffer a_buf [] ((encEdgeTriples (p.members[j.1]'j.2).eList).length + 3 * G.numEdges) s₃ := by
    rwa [length_encEdgeTriples]
  have hrE₃ : s₃.arrs a_rE = encEdgeTriples (p.members[j.1]'j.2).eList := by
    rw [harr₃ a_rE hne_rEb]
    exact hrE
  have hrEWords₃ : s₃.regs (r_base + 2) = (encEdgeTriples (p.members[j.1]'j.2).eList).length := by
    rw [hreg₃ (r_base + 2) (by omega), length_encEdgeTriples]
    simp [s₂, s₁, State.setReg]
  rcases appendBufSliceProg_exec a_rE a_buf (r_base + 2) r_base (r_base + 4)
      hne_rEb (by omega) (by omega) (by omega) hrE_words_w h1_w
      (by rw [List.length_nil, Nat.zero_add, length_encEdgeTriples]; omega)
      hrE₃ hbuf₃' hrEWords₃ hrpos₃ with
    ⟨s₄, t₄, hex₄, ht₄, hbuf₄, hrpos₄, _, harr₄, hreg₄⟩
  rw [List.nil_append] at hbuf₄ hrpos₄
  have hrrELen₄ : s₄.regs r_rELen = (p.members[j.1]'j.2).eList.length := by
    rw [hreg₄ r_rELen (by omega) (by omega), hreg₃ r_rELen (by omega)]
    simp [s₂, s₁, State.setReg, show r_rELen ≠ r_base + 3 by omega,
      show r_rELen ≠ r_base + 2 by omega, hrrELen]
  let s₅ := s₄.setReg r_tildeELen (p.members[j.1]'j.2).eList.length
  have hex₅ : Exec w (.assign r_tildeELen (.reg r_rELen)) s₄ s₅ 2 :=
    .assign (by simp [Expr.eval, checkWord, hrrELen₄, hrELen_w])
  have hG₅ : s₅.arrs a_G = G.enc ++ extraG := by
    simp [s₅, harr₄ a_G hne_Gb, harr₃ a_G hne_Gb, s₂, s₁, hG]
  rcases enc_getElem_one G extraG hG₅ with ⟨h1_len, hget1⟩
  have hnp_w : G.numActivePairs < 2 ^ w := by omega
  let s₆ := s₅.setReg (r_base + 1) G.numActivePairs
  have hex₆ : Exec w (.assign (r_base + 1) (.read a_G (.const 1))) s₅ s₆ 3 :=
    .assign (by simp [Expr.eval, checkWord, h1_w, h1_len, hget1, hnp_w])
  let s₇ := s₆.setReg (r_base + 4) 0
  have hex₇ : Exec w (.assign (r_base + 4) (.const 0)) s₆ s₇ 2 :=
    .assign (by simp [Expr.eval, checkWord, h0_w])
  have hbuf₇ :
      s₇.arrs a_buf =
        encEdgeTriples (p.members[j.1]'j.2).eList ++
          List.replicate (3 * G.sumEdgeMult G.activePairsList + 0) 0 := by
    rw [G.sumEdgeMult_activePairsList, Nat.add_zero]
    exact hbuf₄
  rcases scanExtraEdgesLoop_exec G p xSeq j
      a_G a_xInd a_KInd a_owner a_buf
      r_j r_base r_tildeELen (r_base + 1) (r_base + 4)
      hne_Gb hne_xb hne_Kb hne_ob
      (by omega) (by omega) (by omega) (by omega)
      (by omega) (by omega) (by omega) hne_jl.symm (by omega)
      hw hn_w hM_w henc_w extraG G.activePairsList [] (p.members[j.1]'j.2).eList 0 (s := s₇)
      (by simp)
      (by rw [G.sumEdgeMult_activePairsList]; exact hcap_w)
      (by simp [s₇, s₆, hG₅])
      (by simp [s₇, s₆, s₅, harr₄ a_xInd hne_xb, harr₃ a_xInd hne_xb, s₂, s₁, hxInd])
      (by simp [s₇, s₆, s₅, harr₄ a_KInd hne_Kb, harr₃ a_KInd hne_Kb, s₂, s₁, hKInd])
      (by simp [s₇, s₆, s₅, harr₄ a_owner hne_ob, harr₃ a_owner hne_ob, s₂, s₁, howner])
      hbuf₇
      (by simp [s₇, s₆, s₅, State.setReg, hne_jl,
        show r_j ≠ r_base + 4 by omega, show r_j ≠ r_base + 1 by omega,
        hreg₄ r_j (by omega) (by omega), hreg₃ r_j (by omega),
        s₂, s₁, show r_j ≠ r_base + 3 by omega, show r_j ≠ r_base + 2 by omega, hrj])
      (by simp [s₇, s₆, s₅, State.setReg, show r_base ≠ r_tildeELen by omega,
        hrpos₄, length_encEdgeTriples])
      (by simp [s₇, s₆, s₅, State.setReg, show r_tildeELen ≠ r_base + 4 by omega,
        show r_tildeELen ≠ r_base + 1 by omega])
      (by simp [s₇, s₆, State.setReg])
      (by simp [s₇]) with
    ⟨s₈, t₈, hex₈, ht₈, hbuf₈, hrpos₈, hrlen₈, harr₈, hreg₈⟩
  rw [extraEdgesFromPairs_activePairsList] at hbuf₈ hrpos₈ hrlen₈
  change s₈.arrs a_buf =
      encEdgeTriples (memberTildeAEList G p xSeq j) ++
        List.replicate (3 * (G.sumEdgeMult G.activePairsList - (extraEdges G p xSeq j).length) + 0) 0 at hbuf₈
  change s₈.regs r_base = 3 * (memberTildeAEList G p xSeq j).length at hrpos₈
  change s₈.regs r_tildeELen = (memberTildeAEList G p xSeq j).length at hrlen₈
  have hwords_tildeE : ∀ x ∈ encEdgeTriples (memberTildeAEList G p xSeq j), x < 2 ^ w := by
    intro x hx
    rw [memberTildeAEList, encEdgeTriples_append, List.mem_append] at hx
    rcases hx with hx₁ | hx₂
    · exact hrE_words_w x hx₁
    · rcases (mem_encEdgeTriples_iff _ x).mp hx₂ with ⟨e, he, hx_e⟩
      rcases (mem_extraEdges_iff G p xSeq j e).mp he with ⟨⟨hu, hv, hk⟩, _⟩
      have hk_m : e.2.2 < G.numEdges :=
        Nat.lt_of_lt_of_le hk (G.edgeMult_le_numEdges ⟨e.1, hu⟩ ⟨e.2.1, hv⟩)
      rcases hx_e with rfl | rfl | rfl <;> omega
  have hlen_tildeE_w : (encEdgeTriples (memberTildeAEList G p xSeq j)).length < 2 ^ w := by
    rw [length_encEdgeTriples]
    have hle := length_memberTildeAEList_le G p xSeq j
    omega
  rcases copyBufPrefixProg_exec a_buf a_tildeE r_base (r_base + 4)
      hne_bt (by omega) hwords_tildeE h1_w hlen_tildeE_w hbuf₈
      (by rw [hrpos₈, length_encEdgeTriples]) with
    ⟨s₉, t₉, hex₉, ht₉, htildeE₉, harr₉, hreg₉⟩
  have hnp_le_m : G.numActivePairs ≤ G.numEdges := G.numActivePairs_le_numEdges
  have hsum_eq_m : G.sumEdgeMult G.activePairsList = G.numEdges := G.sumEdgeMult_activePairsList
  have hlen_le := length_memberTildeAEList_le G p xSeq j
  change t₈ ≤ 3 + 95 * G.numActivePairs + 26 * G.sumEdgeMult G.activePairsList at ht₈
  rw [length_encEdgeTriples] at ht₄ ht₉
  refine ⟨s₉,
    4 + (6 + (t₃ + (t₄ + (2 + (3 + (2 + (t₈ + t₉))))))),
    .seq hex₁ (.seq hex₂ (.seq hex₃ (.seq hex₄ (.seq hex₅ (.seq hex₆ (.seq hex₇ (.seq hex₈ hex₉))))))),
    by simp [Expr.cost] at ht₃; omega,
    htildeE₉,
    by rw [hreg₉ r_tildeELen (by omega), hrlen₈],
    fun a ha₁ ha₂ => by
      rw [harr₉ a ha₂, harr₈ a ha₁]
      simp [s₇, s₆, s₅, harr₄ a ha₁, harr₃ a ha₁, s₂, s₁],
    fun reg hlt hne => by
      rw [hreg₉ reg (by omega), hreg₈ reg (by omega) (by omega) hne]
      simp [s₇, s₆, s₅, State.setReg, hne,
        show reg ≠ r_base + 4 by omega, show reg ≠ r_base + 1 by omega,
        hreg₄ reg (by omega) (by omega), hreg₃ reg (by omega),
        s₂, s₁, show reg ≠ r_base + 3 by omega, show reg ≠ r_base + 2 by omega]⟩

/-! ### Section 2: `buildVIdxProg`, `buildEdgeMultMatProg` -/

private theorem getD_set_of_lt' {l : List ℕ} {i j x d : ℕ} (_hi : i < l.length) (hj : j < l.length) :
    (l.set i x).getD j d = if i = j then x else l.getD j d := by
  have hj' : j < (l.set i x).length := by simp [hj]
  rw [List.getD_eq_getElem _ _ hj', List.getD_eq_getElem _ _ hj, List.getElem_set]

private theorem mul_add_inj_of_lt {n a₁ b₁ a₂ b₂ : ℕ}
    (hb₁ : b₁ < n) (hb₂ : b₂ < n) :
    a₁ * n + b₁ = a₂ * n + b₂ ↔ a₁ = a₂ ∧ b₁ = b₂ := by
  constructor
  · intro h
    have ha : a₁ = a₂ := by
      rcases lt_trichotomy a₁ a₂ with hlt | rfl | hgt
      · have : a₁ * n + n ≤ a₂ * n := by
          calc a₁ * n + n = (a₁ + 1) * n := by ring
            _ ≤ a₂ * n := Nat.mul_le_mul_right n hlt
        omega
      · rfl
      · have : a₂ * n + n ≤ a₁ * n := by
          calc a₂ * n + n = (a₂ + 1) * n := by ring
            _ ≤ a₁ * n := Nat.mul_le_mul_right n hgt
        omega
    subst ha
    exact ⟨rfl, by omega⟩
  · rintro ⟨rfl, rfl⟩
    rfl

/-- Build the inverse vertex-index table `a_vIdx` of length `n` mapping `vList[u]` to `u`. -/
def buildVIdxProg (a_vList a_vIdx : Arr) (r_n r_nA r_k : Reg) : Cmd :=
  .seq (.alloc a_vIdx (.reg r_n))
    (.seq (.assign r_k (.const 0))
      (forUp r_k (.reg r_nA)
        (.write a_vIdx (.read a_vList (.reg r_k)) (.reg r_k))))

theorem buildVIdxProg_exec {w n : ℕ} (vList : List ℕ)
    (hv_nd : vList.Nodup) (hv_lt : ∀ v ∈ vList, v < n)
    (a_vList a_vIdx r_n r_nA r_k : ℕ)
    (hne_arr : a_vList ≠ a_vIdx)
    (_hr_n : r_n < r_k) (hr_nA : r_nA < r_k)
    (hw : 1 < 2 ^ w) (hn_w : n < 2 ^ w) (hnA_w : vList.length < 2 ^ w)
    {s : State}
    (hvList : s.arrs a_vList = vList)
    (hrn : s.regs r_n = n)
    (hrnA : s.regs r_nA = vList.length) :
    ∃ s' t,
      Exec w (buildVIdxProg a_vList a_vIdx r_n r_nA r_k) s s' t ∧
      t ≤ n + 11 * vList.length + 10 ∧
      (s'.arrs a_vIdx).length = n ∧
      (∀ u : Fin vList.length, (s'.arrs a_vIdx).getD (vList[u.1]'u.2) 0 = u.1) ∧
      (∀ a : ℕ, a ≠ a_vIdx → s'.arrs a = s.arrs a) ∧
      (∀ r < r_k, s'.regs r = s.regs r) := by
  let n_A := vList.length
  have h0_w : 0 < 2 ^ w := by omega
  let s₁ := s.setArr a_vIdx (List.replicate n 0)
  have hex₁ : Exec w (.alloc a_vIdx (.reg r_n)) s s₁ (1 + n) :=
    .alloc (by simp [Expr.eval, checkWord, hrn, hn_w])
  let s₂ := s₁.setReg r_k 0
  have hex₂ : Exec w (.assign r_k (.const 0)) s₁ s₂ 2 :=
    .assign (by simp [Expr.eval, checkWord, h0_w])
  let Inv (j : ℕ) (st : State) : Prop :=
    (st.arrs a_vIdx).length = n ∧
    (∀ u : Fin n_A, u.1 < j → (st.arrs a_vIdx).getD (vList[u.1]'u.2) 0 = u.1) ∧
    st.regs r_nA = n_A ∧
    st.regs r_k = j ∧
    (∀ a : ℕ, a ≠ a_vIdx → st.arrs a = s.arrs a) ∧
    (∀ r < r_k, st.regs r = s.regs r)
  have hInv₀ : Inv 0 s₂ := by
    refine ⟨by simp [s₂, s₁], fun u hu => by omega,
      by simp [s₂, s₁, show r_nA ≠ r_k by omega, hrnA, n_A],
      by simp [s₂],
      fun a ha => by simp [s₂, s₁, ha],
      fun r hr => by simp [s₂, s₁, show r ≠ r_k by omega]⟩
  have hLoop :
      ⦃Inv 0⦄[w]
        forUp r_k (.reg r_nA)
          (.write a_vIdx (.read a_vList (.reg r_k)) (.reg r_k))
      ⦃Inv n_A⦄ ≤ fun _ => 3 + n_A * (7 + 4) := by
    apply Triple.forUp_const Inv n_A 4 hw hnA_w
    · intro j _ st ⟨_, _, hrnA_st, hrk_st, _, _⟩
      exact ⟨hrk_st, by simp [Expr.eval, checkWord, hrnA_st, hnA_w, n_A]⟩
    · intro j hj st ⟨hlen_st, hget_st, hrnA_st, hrk_st, harr_st, hreg_st⟩
      have hj_w : j < 2 ^ w := by omega
      let v := vList[j]'hj
      have hv_n : v < n := hv_lt v (List.getElem_mem hj)
      have hv_w : v < 2 ^ w := by omega
      have hv_st : st.arrs a_vList = vList := (harr_st a_vList hne_arr).trans hvList
      have hj_vlen : j < (st.arrs a_vList).length := by rw [hv_st]; exact hj
      have hget_v : (st.arrs a_vList)[j]'hj_vlen = v := by simp [hv_st, v]
      have hv_ilen : v < (st.arrs a_vIdx).length := by rw [hlen_st]; exact hv_n
      let st₁ := st.writeArr a_vIdx v j
      have hex_w :
          Exec w (.write a_vIdx (.read a_vList (.reg r_k)) (.reg r_k)) st st₁ 4 :=
        .write
          (by simp [Expr.eval, checkWord, hrk_st, hj_w, hj_vlen, hget_v, hv_w])
          (by simp [Expr.eval, checkWord, hrk_st, hj_w])
          hv_ilen
      refine ⟨st₁, 4, hex_w, le_rfl,
        ⟨by simp [st₁, hlen_st],
         fun u hu => by
           have hu_n : vList[u.1]'u.2 < (st.arrs a_vIdx).length := by
             rw [hlen_st]; exact hv_lt _ (List.getElem_mem u.2)
           simp only [st₁, State.setReg_arrs, State.writeArr_arrs_self]
           rw [getD_set_of_lt' hv_ilen hu_n]
           by_cases hju : j = u.1
           · subst hju
             simp [v]
           · have hne_v : v ≠ vList[u.1]'u.2 := fun heq =>
               hju ((hv_nd.getElem_inj_iff (hi := hj) (hj := u.2)).mp heq)
             rw [ite_eq_right hne_v]
             exact hget_st u (by omega),
         by simp [st₁, State.setReg, show r_nA ≠ r_k by omega, hrnA_st],
         by simp [st₁, State.setReg],
         fun a ha => by simp [st₁, ha, harr_st a ha],
         fun r hr => by simp [st₁, State.setReg, show r ≠ r_k by omega, hreg_st r hr]⟩,
        by simp [st₁, hrk_st]⟩
  rcases hLoop s₂ hInv₀ with ⟨s₃, t₃, hex₃, ht₃, ⟨hlen₃, hget₃, _, _, harr₃, hreg₃⟩⟩
  dsimp only at ht₃
  refine ⟨s₃, (1 + n) + (2 + t₃), .seq hex₁ (.seq hex₂ hex₃), by omega,
    hlen₃, fun u => hget₃ u u.2, harr₃, hreg₃⟩

@[simp]
theorem edgesBetween_append (L₁ L₂ : List (ℕ × ℕ × ℕ)) (u v : ℕ) :
    edgesBetween (L₁ ++ L₂) u v = edgesBetween L₁ u v ++ edgesBetween L₂ u v := by
  simp [edgesBetween, List.filter_append]

theorem length_edgesBetween_take_succ (es : List (ℕ × ℕ × ℕ)) {k : ℕ} (hk : k < es.length)
    (u v : ℕ) :
    (edgesBetween (es.take (k + 1)) u v).length =
      (edgesBetween (es.take k) u v).length +
        if (es[k]'hk).1 = u ∧ (es[k]'hk).2.1 = v then 1 else 0 := by
  rw [take_add_one_eq_append_getElem es k hk, edgesBetween_append, List.length_append]
  congr 1
  unfold edgesBetween
  split_ifs with h <;> simp [h]

theorem length_edgesBetween_le (es : List (ℕ × ℕ × ℕ)) (u v : ℕ) :
    (edgesBetween es u v).length ≤ es.length :=
  List.length_filter_le _ _

/-- Loop body for `buildEdgeMultMatProg`. -/
def buildEdgeMultMatBody (a_vIdx a_edges a_mult : Arr) (r_nA r_base : Reg) : Cmd :=
  let r_k := r_base
  let r_idx := r_base + 1
  let r_u := r_base + 2
  let r_v := r_base + 3
  let r_cell := r_base + 4
  .seq (.assign r_idx (.op .mul (.const 3) (.reg r_k)))
    (.seq (.assign r_u (.read a_vIdx (.read a_edges (.reg r_idx))))
      (.seq (.assign r_v (.read a_vIdx (.read a_edges (.op .add (.reg r_idx) (.const 1)))))
        (.seq (.assign r_cell (.op .add (.op .mul (.reg r_u) (.reg r_nA)) (.reg r_v)))
          (.write a_mult (.reg r_cell)
            (.op .add (.read a_mult (.reg r_cell)) (.const 1))))))

/-- Build the `n_A × n_A` edge-multiplicity matrix `a_mult` for `tildeAMultiDigraph vList es`. -/
def buildEdgeMultMatProg (a_vIdx a_edges a_mult : Arr) (r_nA r_m r_base : Reg) : Cmd :=
  .seq (.alloc a_mult (.op .mul (.reg r_nA) (.reg r_nA)))
    (.seq (.assign r_base (.const 0))
      (forUp r_base (.reg r_m)
        (buildEdgeMultMatBody a_vIdx a_edges a_mult r_nA r_base)))

theorem buildEdgeMultMatProg_exec {w n : ℕ} (vList : List ℕ) (es : List (ℕ × ℕ × ℕ))
    (hv_nd : vList.Nodup) (hv_lt : ∀ v ∈ vList, v < n)
    (he_ends : ∀ e ∈ es, e.1 ∈ vList ∧ e.2.1 ∈ vList)
    (a_vIdx a_edges a_mult r_nA r_m r_base : ℕ)
    (hne_im : a_vIdx ≠ a_mult) (hne_em : a_edges ≠ a_mult)
    (hr_nA : r_nA < r_base) (hr_m : r_m < r_base)
    (hw : 3 < 2 ^ w) (hn_w : n < 2 ^ w)
    (hnA_sq_w : vList.length * vList.length < 2 ^ w)
    (hm_w : 3 * es.length + 1 < 2 ^ w)
    {s : State}
    (hvIdx_len : (s.arrs a_vIdx).length = n)
    (hvIdx_get : ∀ u : Fin vList.length, (s.arrs a_vIdx).getD (vList[u.1]'u.2) 0 = u.1)
    (hedges : s.arrs a_edges = encEdgeTriples es)
    (hrnA : s.regs r_nA = vList.length)
    (hrm : s.regs r_m = es.length) :
    ∃ s' t,
      Exec w (buildEdgeMultMatProg a_vIdx a_edges a_mult r_nA r_m r_base) s s' t ∧
      t ≤ vList.length * vList.length + 39 * es.length + 12 ∧
      (s'.arrs a_mult).length = vList.length * vList.length ∧
      (∀ x y : Fin vList.length,
        (s'.arrs a_mult).getD (x.1 * vList.length + y.1) 0 =
          (tildeAMultiDigraph vList es).edgeMult x y) ∧
      (∀ a : ℕ, a ≠ a_mult → s'.arrs a = s.arrs a) ∧
      (∀ r < r_base, s'.regs r = s.regs r) := by
  let n_A := vList.length
  have h0_w : 0 < 2 ^ w := by omega
  have h1_w : 1 < 2 ^ w := by omega
  have h3_w : 3 < 2 ^ w := hw
  have hnA_w : n_A < 2 ^ w := by
    rcases Nat.eq_zero_or_pos n_A with h0 | hpos
    · omega
    · nlinarith
  have hes_w : es.length < 2 ^ w := by omega
  let s₁ := s.setArr a_mult (List.replicate (n_A * n_A) 0)
  have hex₁ :
      Exec w (.alloc a_mult (.op .mul (.reg r_nA) (.reg r_nA))) s s₁ (3 + n_A * n_A) :=
    .alloc (by simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hrnA, hnA_w, hnA_sq_w, n_A])
  let s₂ := s₁.setReg r_base 0
  have hex₂ : Exec w (.assign r_base (.const 0)) s₁ s₂ 2 :=
    .assign (by simp [Expr.eval, checkWord, h0_w])
  let Inv (k : ℕ) (st : State) : Prop :=
    (st.arrs a_mult).length = n_A * n_A ∧
    (∀ x y : Fin n_A,
      (st.arrs a_mult).getD (x.1 * n_A + y.1) 0 =
        (edgesBetween (es.take k) (vList[x.1]'x.2) (vList[y.1]'y.2)).length) ∧
    st.regs r_nA = n_A ∧
    st.regs r_m = es.length ∧
    st.regs r_base = k ∧
    (∀ a : ℕ, a ≠ a_mult → st.arrs a = s.arrs a) ∧
    (∀ r < r_base, st.regs r = s.regs r)
  have hInv₀ : Inv 0 s₂ := by
    refine ⟨by simp [s₂, s₁], ?_,
      by simp [s₂, s₁, show r_nA ≠ r_base by omega, hrnA, n_A],
      by simp [s₂, s₁, show r_m ≠ r_base by omega, hrm],
      by simp [s₂],
      fun a ha => by simp [s₂, s₁, ha],
      fun r hr => by simp [s₂, s₁, show r ≠ r_base by omega]⟩
    intro x y
    have hxy_lt : x.1 * n_A + y.1 < n_A * n_A := by
      calc x.1 * n_A + y.1 < x.1 * n_A + n_A := by omega
        _ = (x.1 + 1) * n_A := by ring
        _ ≤ n_A * n_A := Nat.mul_le_mul_right n_A x.2
    simp only [s₂, s₁, State.setReg_arrs, State.setArr_arrs_self, edgesBetween,
      List.take_zero, List.filter_nil, List.length_nil]
    rw [List.getD_eq_getElem _ _ (by simp [hxy_lt]), List.getElem_replicate]
  have hLoop :
      ⦃Inv 0⦄[w]
        forUp r_base (.reg r_m)
          (buildEdgeMultMatBody a_vIdx a_edges a_mult r_nA r_base)
      ⦃Inv es.length⦄ ≤ fun _ => 3 + es.length * (7 + 32) := by
    apply Triple.forUp_const Inv es.length 32 h1_w hes_w
    · intro k _ st ⟨_, _, _, hrm_st, hrb_st, _, _⟩
      exact ⟨hrb_st, by simp [Expr.eval, checkWord, hrm_st, hes_w]⟩
    · intro k hk st ⟨hlen_st, hget_st, hrnA_st, hrm_st, hrb_st, harr_st, hreg_st⟩
      have hk_w : k < 2 ^ w := by omega
      have h3k_w : 3 * k < 2 ^ w := by omega
      have h3k1_w : 3 * k + 1 < 2 ^ w := by omega
      let e := es[k]'hk
      rcases he_ends e (List.getElem_mem hk) with ⟨hu_mem, hv_mem⟩
      rcases List.mem_iff_getElem.mp hu_mem with ⟨u_idx, hu_idx, hu_eq⟩
      rcases List.mem_iff_getElem.mp hv_mem with ⟨v_idx, hv_idx, hv_eq⟩
      let u₀ : Fin n_A := ⟨u_idx, hu_idx⟩
      let v₀ : Fin n_A := ⟨v_idx, hv_idx⟩
      have he1_n : e.1 < n := hv_lt e.1 hu_mem
      have he2_n : e.2.1 < n := hv_lt e.2.1 hv_mem
      have he1_w : e.1 < 2 ^ w := by omega
      have he2_w : e.2.1 < 2 ^ w := by omega
      have hu₀_w : u₀.1 < 2 ^ w := by omega
      have hv₀_w : v₀.1 < 2 ^ w := by omega
      have hedges_st : st.arrs a_edges = encEdgeTriples es :=
        (harr_st a_edges hne_em).trans hedges
      have hvIdx_st : st.arrs a_vIdx = s.arrs a_vIdx := harr_st a_vIdx hne_im
      have h3k_len' : 3 * k < (st.arrs a_edges).length := by
        rw [hedges_st, length_encEdgeTriples]; omega
      have h3k1_len' : 3 * k + 1 < (st.arrs a_edges).length := by
        rw [hedges_st, length_encEdgeTriples]; omega
      have hget_e1' : (st.arrs a_edges)[3 * k]'h3k_len' = e.1 := by
        rw [← List.getD_eq_getElem _ 0 h3k_len', hedges_st,
          List.getD_eq_getElem _ 0 (by rw [length_encEdgeTriples]; omega)]
        exact getElem_encEdgeTriples_u es hk
      have hget_e2' : (st.arrs a_edges)[3 * k + 1]'h3k1_len' = e.2.1 := by
        rw [← List.getD_eq_getElem _ 0 h3k1_len', hedges_st,
          List.getD_eq_getElem _ 0 (by rw [length_encEdgeTriples]; omega)]
        exact getElem_encEdgeTriples_v es hk
      have he1_ilen : e.1 < (st.arrs a_vIdx).length := by rw [hvIdx_st, hvIdx_len]; exact he1_n
      have he2_ilen : e.2.1 < (st.arrs a_vIdx).length := by rw [hvIdx_st, hvIdx_len]; exact he2_n
      have hget_u₀ : (st.arrs a_vIdx)[e.1]'he1_ilen = u₀.1 := by
        have h := hvIdx_get u₀
        simp only [u₀, hu_eq, List.getD_eq_getElem _ _ (by rw [hvIdx_len]; exact he1_n)] at h
        simpa [hvIdx_st] using h
      have hget_v₀ : (st.arrs a_vIdx)[e.2.1]'he2_ilen = v₀.1 := by
        have h := hvIdx_get v₀
        simp only [v₀, hv_eq, List.getD_eq_getElem _ _ (by rw [hvIdx_len]; exact he2_n)] at h
        simpa [hvIdx_st] using h
      let st₁ := st.setReg (r_base + 1) (3 * k)
      have hex_idx :
          Exec w (.assign (r_base + 1) (.op .mul (.const 3) (.reg r_base))) st st₁ 4 :=
        .assign (by simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hrb_st, h3_w, hk_w, h3k_w])
      let st₂ := st₁.setReg (r_base + 2) u₀.1
      have hex_u :
          Exec w (.assign (r_base + 2) (.read a_vIdx (.read a_edges (.reg (r_base + 1))))) st₁ st₂ 4 :=
        .assign (by simp [st₁, State.setReg, Expr.eval, checkWord, h3k_w, h3k_len', hget_e1',
          he1_w, he1_ilen, hget_u₀, hu₀_w])
      let st₃ := st₂.setReg (r_base + 3) v₀.1
      have hex_v :
          Exec w
            (.assign (r_base + 3)
              (.read a_vIdx (.read a_edges (.op .add (.reg (r_base + 1)) (.const 1)))))
            st₂ st₃ 6 :=
        .assign (by simp [st₂, st₁, State.setReg, Expr.eval, BinOp.eval, BinOp.raw, checkWord,
          h3k_w, h1_w, h3k1_w, h3k1_len', hget_e2', he2_w, he2_ilen, hget_v₀, hv₀_w])
      let cell := u₀.1 * n_A + v₀.1
      have hcell_lt : cell < n_A * n_A := by
        calc u₀.1 * n_A + v₀.1 < u₀.1 * n_A + n_A := by omega
          _ = (u₀.1 + 1) * n_A := by ring
          _ ≤ n_A * n_A := Nat.mul_le_mul_right n_A u₀.2
      have hcell_w : cell < 2 ^ w := lt_trans hcell_lt hnA_sq_w
      have hmul_w : u₀.1 * n_A < 2 ^ w := lt_of_le_of_lt (Nat.le_add_right _ _) hcell_w
      let st₄ := st₃.setReg (r_base + 4) cell
      have hex_cell :
          Exec w
            (.assign (r_base + 4)
              (.op .add (.op .mul (.reg (r_base + 2)) (.reg r_nA)) (.reg (r_base + 3))))
            st₃ st₄ 6 :=
        .assign (by simp [st₃, st₂, st₁, State.setReg,
          show r_nA ≠ r_base + 3 by omega, show r_nA ≠ r_base + 2 by omega,
          show r_nA ≠ r_base + 1 by omega,
          Expr.eval, BinOp.eval, BinOp.raw, checkWord,
          hrnA_st, hu₀_w, hnA_w, hmul_w, hv₀_w, hcell_w, cell])
      have hcell_mlen : cell < (st₄.arrs a_mult).length := by
        simp [st₄, st₃, st₂, st₁, hlen_st, hcell_lt]
      let oldMult := (edgesBetween (es.take k) (vList[u₀.1]'u₀.2) (vList[v₀.1]'v₀.2)).length
      have hget_old : (st₄.arrs a_mult)[cell]'hcell_mlen = oldMult := by
        have h := hget_st u₀ v₀
        rw [List.getD_eq_getElem _ _ (by rw [hlen_st]; exact hcell_lt)] at h
        simpa [st₄, st₃, st₂, st₁, cell, oldMult] using h
      have hold_le : oldMult ≤ k := by
        calc oldMult ≤ (es.take k).length := length_edgesBetween_le _ _ _
          _ = k := List.length_take_of_le (by omega)
      have hold_w : oldMult < 2 ^ w := by omega
      have hold1_w : oldMult + 1 < 2 ^ w := by omega
      let st₅ := st₄.writeArr a_mult cell (oldMult + 1)
      have hr4_st₄ : st₄.regs (r_base + 4) = cell := by simp [st₄]
      have hex_wr :
          Exec w
            (.write a_mult (.reg (r_base + 4))
              (.op .add (.read a_mult (.reg (r_base + 4))) (.const 1)))
            st₄ st₅ 6 :=
        .write
          (by simp [hr4_st₄, Expr.eval, checkWord, hcell_w])
          (by simp [hr4_st₄, Expr.eval, BinOp.eval, BinOp.raw, checkWord,
            hcell_w, hcell_mlen, hget_old, hold_w, h1_w, hold1_w])
          hcell_mlen
      refine ⟨st₅, 4 + (4 + (6 + (6 + 6))),
        .seq hex_idx (.seq hex_u (.seq hex_v (.seq hex_cell hex_wr))),
        by dsimp only; omega,
        ⟨by simp [st₅, st₄, st₃, st₂, st₁, hlen_st],
         fun x y => by
           have hxy_lt : x.1 * n_A + y.1 < (st.arrs a_mult).length := by
             rw [hlen_st]
             calc x.1 * n_A + y.1 < x.1 * n_A + n_A := by omega
               _ = (x.1 + 1) * n_A := by ring
               _ ≤ n_A * n_A := Nat.mul_le_mul_right n_A x.2
           have hcell_lt' : cell < (st.arrs a_mult).length := by rw [hlen_st]; exact hcell_lt
           simp only [st₅, st₄, st₃, st₂, st₁, State.writeArr_arrs_self, State.setReg_arrs]
           rw [getD_set_of_lt' hcell_lt' hxy_lt, length_edgesBetween_take_succ es hk]
           have heq_iff :
               (cell = x.1 * n_A + y.1) ↔
                 (e.1 = vList[x.1]'x.2 ∧ e.2.1 = vList[y.1]'y.2) := by
             dsimp [cell]
             rw [mul_add_inj_of_lt v₀.2 y.2, ← hu_eq, ← hv_eq,
               hv_nd.getElem_inj_iff, hv_nd.getElem_inj_iff]
           by_cases hcell_eq : cell = x.1 * n_A + y.1
           · have hxy_eq := (mul_add_inj_of_lt v₀.2 y.2).mp hcell_eq
             have hu_x : u₀ = x := Fin.ext hxy_eq.1
             have hv_y : v₀ = y := Fin.ext hxy_eq.2
             have he_xy : e.1 = vList[x.1]'x.2 ∧ e.2.1 = vList[y.1]'y.2 :=
               heq_iff.mp hcell_eq
             rw [ite_eq_left hcell_eq, ite_eq_left he_xy]
             simp [oldMult, hu_x, hv_y]
           · have hne_xy : ¬(e.1 = vList[x.1]'x.2 ∧ e.2.1 = vList[y.1]'y.2) :=
               fun h => hcell_eq (heq_iff.mpr h)
             rw [ite_eq_right hcell_eq, ite_eq_right hne_xy, Nat.add_zero]
             exact hget_st x y,
         by simp [st₅, st₄, st₃, st₂, st₁, State.setReg,
           show r_nA ≠ r_base by omega,
           show r_nA ≠ r_base + 4 by omega, show r_nA ≠ r_base + 3 by omega,
           show r_nA ≠ r_base + 2 by omega, show r_nA ≠ r_base + 1 by omega, hrnA_st],
         by simp [st₅, st₄, st₃, st₂, st₁, State.setReg,
           show r_m ≠ r_base by omega,
           show r_m ≠ r_base + 4 by omega, show r_m ≠ r_base + 3 by omega,
           show r_m ≠ r_base + 2 by omega, show r_m ≠ r_base + 1 by omega, hrm_st],
         by simp [st₅, st₄, st₃, st₂, st₁, State.setReg],
         fun a ha => by simp [st₅, st₄, st₃, st₂, st₁, ha, harr_st a ha],
         fun r hr => by
           simp [st₅, st₄, st₃, st₂, st₁, State.setReg,
             show r ≠ r_base by omega,
             show r ≠ r_base + 4 by omega, show r ≠ r_base + 3 by omega,
             show r ≠ r_base + 2 by omega, show r ≠ r_base + 1 by omega, hreg_st r hr]⟩,
        by simp [st₅, st₄, st₃, st₂, st₁, State.setReg, hrb_st]⟩
  rcases hLoop s₂ hInv₀ with ⟨s₃, t₃, hex₃, ht₃, ⟨hlen₃, hget₃, _, _, _, harr₃, hreg₃⟩⟩
  dsimp only at ht₃
  have htake_all : es.take es.length = es := List.take_of_length_le le_rfl
  rw [htake_all] at hget₃
  refine ⟨s₃, (3 + n_A * n_A) + (2 + t₃), .seq hex₁ (.seq hex₂ hex₃),
    by dsimp [n_A] at ht₃ ⊢; omega,
    hlen₃, hget₃, harr₃, hreg₃⟩

end GraphMinor.Compute

