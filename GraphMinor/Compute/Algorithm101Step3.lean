module

public import GraphMinor.Compute.Algorithm101Step2
public import GraphMinor.Compute.Algorithm105Step2

/-!
# $\tilde{A}$ Encoding and Leaf Map `f_tau0` of Algorithm (10.1)

This file implements:
1. **Building `G_A.enc` from Multiplicity Matrix (`Section 1`):**
   `buildEncFromMultMatProg` constructs `G_A.enc` and `G_A.numActivePairs` from the `n_A × n_A`
   edge-multiplicity matrix of `G_A = tildeAMultiDigraph vList eList` in `O(n_A^2)` time.
2. **Building the Initial Leaf Map `memberFTau0` (`Section 2`):**
   `buildFTau0Prog` constructs `List.ofFn (fun e => memberFTau0 vList r e.1)` for
   `G_del = tildeAMultiDigraph vList r.eList` in `O(n_A^2 + |r.eList|^2)` time.
-/

@[expose] public section

namespace GraphMinor.Compute

open Classical

/-! ### Section 1: Building `G_A.enc` from the Multiplicity Matrix (`buildEncFromMultMatProg`) -/

/-- Upper-triangular active block of `G : MultiDigraph n` at `(u, v) : Fin n × Fin n`. -/
def upperActiveBlock {n : ℕ} (G : MultiDigraph n) (u v : Fin n) : List (Fin n × Fin n) :=
  if u.1 ≤ v.1 then G.activeBlock (u, v) else []

private theorem filter_flatMap_eq_flatMap_ite {α β : Type*} (L : List α) (p : α → Bool)
    (f : α → List β) :
    (L.filter p).flatMap f = L.flatMap (fun x => if p x then f x else []) := by
  induction L with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.filter_cons]
    cases hp : p x <;> simp [hp, ih]

private theorem flatMap_flatMap {α β γ : Type*} (L : List α) (f : α → List β) (g : β → List γ) :
    (L.flatMap f).flatMap g = L.flatMap (fun x => (f x).flatMap g) := by
  induction L with
  | nil => rfl
  | cons x xs ih => simp [List.flatMap_append, ih]

theorem MultiDigraph.activePairsList_eq_flatMap_finRange {n : ℕ} (G : MultiDigraph n) :
    G.activePairsList =
      (List.finRange n).flatMap (fun u =>
        (List.finRange n).flatMap (fun v => upperActiveBlock G u v)) := by
  rw [G.activePairsList_eq_flatMap_upperPairs]
  dsimp only [upperPairs, allPairs]
  rw [filter_flatMap_eq_flatMap_ite, flatMap_flatMap]
  refine List.flatMap_congr fun u _ => ?_
  rw [List.flatMap_map]
  refine List.flatMap_congr fun v _ => ?_
  by_cases h : u.1 ≤ v.1 <;> simp [upperActiveBlock, h]

theorem upperActiveBlock_eq_of_eq {n : ℕ} (G : MultiDigraph n) (u : Fin n) :
    upperActiveBlock G u u = if 0 < G.edgeMult u u then [(u, u)] else [] := by
  unfold upperActiveBlock MultiDigraph.activeBlock
  simp only [le_refl, ↓reduceIte, List.filter_cons, List.filter_nil]
  by_cases h : 0 < G.edgeMult u u <;> simp [h]

theorem upperActiveBlock_eq_of_lt {n : ℕ} (G : MultiDigraph n) {u v : Fin n} (hlt : u.1 < v.1) :
    upperActiveBlock G u v =
      (if 0 < G.edgeMult u v then [(u, v)] else []) ++
        (if 0 < G.edgeMult v u then [(v, u)] else []) := by
  have hle : u.1 ≤ v.1 := Nat.le_of_lt hlt
  have hne : u ≠ v := fun h => Nat.ne_of_lt hlt (congrArg Fin.val h)
  unfold upperActiveBlock MultiDigraph.activeBlock
  simp only [hle, ↓reduceIte, hne, List.filter_cons, List.filter_nil]
  by_cases h1 : 0 < G.edgeMult u v <;> by_cases h2 : 0 < G.edgeMult v u <;> simp [h1, h2]

theorem upperActiveBlock_eq_of_gt {n : ℕ} (G : MultiDigraph n) {u v : Fin n} (hgt : v.1 < u.1) :
    upperActiveBlock G u v = [] := by
  unfold upperActiveBlock
  rw [ite_eq_right (by omega)]

theorem length_upperActiveBlock_le {n : ℕ} (G : MultiDigraph n) (u v : Fin n) :
    (upperActiveBlock G u v).length ≤ 2 := by
  rcases lt_trichotomy u.1 v.1 with hlt | heq | hgt
  · rw [upperActiveBlock_eq_of_lt G hlt, List.length_append]; split_ifs <;> simp
  · rcases Fin.ext heq with rfl; rw [upperActiveBlock_eq_of_eq]; split_ifs <;> simp
  · rw [upperActiveBlock_eq_of_gt G hgt]; simp

/-- Conditionally push `[x, y, m]` to `a_buf` and increment `r_numP` when `0 < m`. -/
def maybePushPairProg (a_buf : Arr) (r_pos r_numP r_x r_y r_m : Reg) : Cmd :=
  .ifLt (.const 0) (.reg r_m)
    (.seq (bufPush3 a_buf r_pos r_x r_y r_m) (.assign r_numP (.op .add (.reg r_numP) (.const 1))))
    .skip

theorem maybePushPairProg_exec {w n cap : ℕ} (G : MultiDigraph n) (x y : Fin n)
    (ps : List (Fin n × Fin n)) (a_buf r_pos r_numP r_x r_y r_m : ℕ)
    (hne_pn : r_pos ≠ r_numP) (_hne_px : r_pos ≠ r_x) (_hne_py : r_pos ≠ r_y) (_hne_pm : r_pos ≠ r_m)
    (_hne_nx : r_numP ≠ r_x) (_hne_ny : r_numP ≠ r_y) (_hne_nm : r_numP ≠ r_m)
    (hcap : 3 * (ps.length + 1) ≤ cap) (hw : 1 < 2 ^ w) (hn_w : n < 2 ^ w)
    (hm_w : G.edgeMult x y < 2 ^ w) (hpos_w : 2 + 3 * (ps.length + 1) < 2 ^ w)
    {s : State}
    (hbuf : s.arrs a_buf = [n, 0] ++ G.flatTriples ps ++ List.replicate (cap - 3 * ps.length) 0)
    (hrpos : s.regs r_pos = 2 + 3 * ps.length) (hrnumP : s.regs r_numP = ps.length)
    (hrx : s.regs r_x = x.1) (hry : s.regs r_y = y.1) (hrm : s.regs r_m = G.edgeMult x y) :
    let ps' := ps ++ if 0 < G.edgeMult x y then [(x, y)] else []
    ∃ s' t,
      Exec w (maybePushPairProg a_buf r_pos r_numP r_x r_y r_m) s s' t ∧ t ≤ 26 ∧
      s'.arrs a_buf = [n, 0] ++ G.flatTriples ps' ++ List.replicate (cap - 3 * ps'.length) 0 ∧
      s'.regs r_pos = 2 + 3 * ps'.length ∧ s'.regs r_numP = ps'.length ∧
      (∀ a : ℕ, a ≠ a_buf → s'.arrs a = s.arrs a) ∧
      (∀ r : ℕ, r ≠ r_pos → r ≠ r_numP → s'.regs r = s.regs r) := by
  intro ps'
  have h0_w : 0 < 2 ^ w := by omega
  have hw3 : 3 < 2 ^ w := by omega
  have hx_w : x.1 < 2 ^ w := Nat.lt_trans x.2 hn_w
  have hy_w : y.1 < 2 ^ w := Nat.lt_trans y.2 hn_w
  by_cases hm : 0 < G.edgeMult x y
  · have hps' : ps' = ps ++ [(x, y)] := by simp [ps', hm]
    have hcond : (Expr.op .lt (.const 0) (.reg r_m)).eval w s = some 1 := by
      simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hrm, h0_w, hm_w, hm, hw]
    have hbuf_split : s.arrs a_buf =
        ([n, 0] ++ G.flatTriples ps) ++ List.replicate ((cap - 3 * (ps.length + 1)) + 3) 0 := by
      have hrep : cap - 3 * ps.length = (cap - 3 * (ps.length + 1)) + 3 := by omega
      rw [← hrep]; exact hbuf
    have hpfx_len : ([n, 0] ++ G.flatTriples ps).length = 2 + 3 * ps.length := by
      simp [G.length_flatTriples]; omega
    rcases bufPush3_exec a_buf r_pos r_x r_y r_m
        ([n, 0] ++ G.flatTriples ps) (cap - 3 * (ps.length + 1))
        x.1 y.1 (G.edgeMult x y) hw3 (by rw [hpfx_len]; omega) hx_w hy_w hm_w
        hbuf_split (by rw [hpfx_len]; exact hrpos) hrx hry hrm with
      ⟨s₁, t₁, hex₁, ht₁, hbuf₁, hrpos₁, harr₁, hreg₁⟩
    have hrnumP₁ : s₁.regs r_numP = ps.length := by rw [hreg₁ r_numP hne_pn.symm, hrnumP]
    have hps_w : ps.length < 2 ^ w := by omega
    have hps1_w : ps.length + 1 < 2 ^ w := by omega
    let s₂ := s₁.setReg r_numP (ps.length + 1)
    have hex₂ : Exec w (.assign r_numP (.op .add (.reg r_numP) (.const 1))) s₁ s₂ 4 :=
      .assign (by simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hrnumP₁, hps_w, hw, hps1_w])
    have hflat : ([n, 0] ++ G.flatTriples ps) ++ [x.1, y.1, G.edgeMult x y] =
        [n, 0] ++ G.flatTriples ps' := by rw [hps', G.flatTriples_append, List.append_assoc]; rfl
    have hlen_ps' : ps'.length = ps.length + 1 := by simp [hps']
    refine ⟨s₂, 3 + (t₁ + 4), .if_true (v := 1) hcond (by decide) (.seq hex₁ hex₂), by omega,
      by rw [hflat, ← hlen_ps'] at hbuf₁; exact hbuf₁,
      by simp [s₂, State.setReg, hne_pn, hrpos₁, hlen_ps']; omega,
      by simp [s₂, hlen_ps'], fun a ha => by simp [s₂, harr₁ a ha],
      fun r hr₁ hr₂ => by simp [s₂, State.setReg, hr₂, hreg₁ r hr₁]⟩
  · have hps' : ps' = ps := by simp [ps', hm]
    have hcond : (Expr.op .lt (.const 0) (.reg r_m)).eval w s = some 0 := by
      simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hrm, h0_w, hm_w, hm]
    refine ⟨s, 3 + 1, .if_false hcond (.skip s), by omega,
      by simpa [hps'] using hbuf, by simpa [hps'] using hrpos,
      by simpa [hps'] using hrnumP, fun _ _ => rfl, fun _ _ _ => rfl⟩

/-- Active pairs of `G` in row `u` before column `j`. -/
def activeRowPairs {n : ℕ} (G : MultiDigraph n) (u : Fin n) (j : ℕ) : List (Fin n × Fin n) :=
  ((List.finRange n).take j).flatMap (fun v => upperActiveBlock G u v)

@[simp]
theorem activeRowPairs_zero {n : ℕ} (G : MultiDigraph n) (u : Fin n) :
    activeRowPairs G u 0 = [] := rfl

theorem activeRowPairs_succ {n : ℕ} (G : MultiDigraph n) (u : Fin n) {j : ℕ} (hj : j < n) :
    activeRowPairs G u (j + 1) = activeRowPairs G u j ++ upperActiveBlock G u ⟨j, hj⟩ := by
  unfold activeRowPairs
  have hj_len : j < (List.finRange n).length := by simp [hj]
  rw [take_add_one_eq_append_getElem (List.finRange n) j hj_len,
    List.getElem_finRange, List.flatMap_append, List.flatMap_singleton]
  rfl

theorem length_activeRowPairs_le {n : ℕ} (G : MultiDigraph n) (u : Fin n) :
    ∀ j ≤ n, (activeRowPairs G u j).length ≤ 2 * j
  | 0, _ => by simp
  | j + 1, hj => by
    rw [activeRowPairs_succ G u hj, List.length_append]
    have h1 := length_activeRowPairs_le G u j (Nat.le_of_lt hj)
    have h2 := length_upperActiveBlock_le G u ⟨j, hj⟩
    omega

/-- Active pairs of `G` in rows `< i`. -/
def activePrefixPairs {n : ℕ} (G : MultiDigraph n) (i : ℕ) : List (Fin n × Fin n) :=
  ((List.finRange n).take i).flatMap (fun u => activeRowPairs G u n)

@[simp]
theorem activePrefixPairs_zero {n : ℕ} (G : MultiDigraph n) :
    activePrefixPairs G 0 = [] := rfl

theorem activePrefixPairs_succ {n : ℕ} (G : MultiDigraph n) {i : ℕ} (hi : i < n) :
    activePrefixPairs G (i + 1) = activePrefixPairs G i ++ activeRowPairs G ⟨i, hi⟩ n := by
  unfold activePrefixPairs
  have hi_len : i < (List.finRange n).length := by simp [hi]
  rw [take_add_one_eq_append_getElem (List.finRange n) i hi_len,
    List.getElem_finRange, List.flatMap_append, List.flatMap_singleton]
  rfl

theorem activePrefixPairs_full {n : ℕ} (G : MultiDigraph n) :
    activePrefixPairs G n = G.activePairsList := by
  unfold activePrefixPairs activeRowPairs
  rw [List.take_of_length_le (by simp), G.activePairsList_eq_flatMap_finRange]

theorem length_activePrefixPairs_le {n : ℕ} (G : MultiDigraph n) :
    ∀ i ≤ n, (activePrefixPairs G i).length ≤ 2 * (i * n)
  | 0, _ => by simp
  | i + 1, hi => by
    rw [activePrefixPairs_succ G hi, List.length_append]
    have h1 := length_activePrefixPairs_le G i (Nat.le_of_lt hi)
    have h2 := length_activeRowPairs_le G ⟨i, hi⟩ n le_rfl
    have hmul : (i + 1) * n = i * n + n := Nat.succ_mul i n
    omega

/-- Inner loop body for `buildEncFromMultMatProg` at `(r_u, r_v)`. -/
def buildEncPairBody (a_mult a_buf : Arr) (r_nA r_pos r_numP r_u r_v r_m : Reg) : Cmd :=
  .ifLt (.reg r_v) (.reg r_u)
    .skip
    (.ifEq (.reg r_u) (.reg r_v)
      (.seq (.assign r_m (.read a_mult (.op .add (.op .mul (.reg r_u) (.reg r_nA)) (.reg r_u))))
        (maybePushPairProg a_buf r_pos r_numP r_u r_u r_m))
      (.seq (.assign r_m (.read a_mult (.op .add (.op .mul (.reg r_u) (.reg r_nA)) (.reg r_v))))
        (.seq (maybePushPairProg a_buf r_pos r_numP r_u r_v r_m)
          (.seq (.assign r_m (.read a_mult (.op .add (.op .mul (.reg r_v) (.reg r_nA)) (.reg r_u))))
            (maybePushPairProg a_buf r_pos r_numP r_v r_u r_m)))))

/-- Build `G_A.enc` in `a_enc` and `G_A.numActivePairs` in `r_numP` from `a_mult` (`G_A.edgeMult`). -/
def buildEncFromMultMatProg (a_mult a_buf a_enc : Arr) (r_nA r_numP r_base : Reg) : Cmd :=
  let r_pos := r_base
  let r_cap := r_base + 1
  let r_u := r_base + 2
  let r_v := r_base + 3
  let r_m := r_base + 4
  .seq
    (.assign r_cap
      (.op .add (.const 2) (.op .mul (.const 6) (.op .mul (.reg r_nA) (.reg r_nA)))))
    (.seq (initPrefixBufferProg a_buf (.reg r_cap) r_pos)
      (.seq (appendWordProg a_buf r_pos (.reg r_nA))
        (.seq (appendWordProg a_buf r_pos (.const 0))
          (.seq (.assign r_numP (.const 0))
            (.seq (.assign r_u (.const 0))
              (.seq
                (forUp r_u (.reg r_nA)
                  (.seq (.assign r_v (.const 0))
                    (forUp r_v (.reg r_nA)
                      (buildEncPairBody a_mult a_buf r_nA r_pos r_numP r_u r_v r_m))))
                (.seq (.write a_buf (.const 1) (.reg r_numP))
                  (copyBufPrefixProg a_buf a_enc r_pos r_u))))))))

theorem buildEncFromMultMatProg_exec {w n_A : ℕ} (G_A : MultiDigraph n_A)
    (a_mult a_buf a_enc r_nA r_numP r_base : ℕ)
    (hne_mb : a_mult ≠ a_buf) (hne_be : a_buf ≠ a_enc)
    (hr_nA : r_nA < r_base) (hr_numP : r_numP < r_base) (hne_nP : r_nA ≠ r_numP)
    (hw : 6 < 2 ^ w) (hcap_w : 2 + 6 * (n_A * n_A) < 2 ^ w)
    (hm_w : ∀ x y : Fin n_A, G_A.edgeMult x y < 2 ^ w)
    {s : State}
    (hmult_len : (s.arrs a_mult).length = n_A * n_A)
    (hmult_get : ∀ x y : Fin n_A, (s.arrs a_mult).getD (x.1 * n_A + y.1) 0 = G_A.edgeMult x y)
    (hrnA : s.regs r_nA = n_A) :
    ∃ s' t,
      Exec w (buildEncFromMultMatProg a_mult a_buf a_enc r_nA r_numP r_base) s s' t ∧
      t ≤ 135 * (n_A * n_A) + 32 * n_A + 78 ∧
      s'.arrs a_enc = G_A.enc ∧
      s'.regs r_numP = G_A.numActivePairs ∧
      (∀ a : ℕ, a ≠ a_buf → a ≠ a_enc → s'.arrs a = s.arrs a) ∧
      (∀ r < r_base, r ≠ r_numP → s'.regs r = s.regs r) := by
  have h0_w : 0 < 2 ^ w := by omega
  have h1_w : 1 < 2 ^ w := by omega
  have h2_w : 2 < 2 ^ w := by omega
  have h6_w : 6 < 2 ^ w := hw
  have hnA_sq_w : n_A * n_A < 2 ^ w := by omega
  have h6sq_w : 6 * (n_A * n_A) < 2 ^ w := by omega
  have hnA_w : n_A < 2 ^ w := by
    rcases Nat.eq_zero_or_pos n_A with rfl | hpos
    · omega
    · nlinarith
  let cap := 6 * (n_A * n_A)
  let s₁ := s.setReg (r_base + 1) (2 + cap)
  have hex₁ :
      Exec w
        (.assign (r_base + 1)
          (.op .add (.const 2) (.op .mul (.const 6) (.op .mul (.reg r_nA) (.reg r_nA)))))
        s s₁ 8 :=
    .assign (by simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord,
      hrnA, h2_w, h6_w, hnA_w, hnA_sq_w, h6sq_w, hcap_w, cap])
  rcases initPrefixBufferProg_exec (cap := 2 + cap) (s := s₁) a_buf (.reg (r_base + 1)) r_base h1_w
      (by simp [s₁, Expr.eval, checkWord, hcap_w, cap]) with
    ⟨s₂, t₂, hex₂, ht₂, hbuf₂, hrpos₂, harr₂, hreg₂⟩
  have hbuf₂' : IsPrefixBuffer a_buf [] ((cap + 1) + 1) s₂ := by
    unfold IsPrefixBuffer at hbuf₂ ⊢
    have hrep : 2 + cap = (cap + 1) + 1 := by omega
    rwa [← hrep]
  have hrnA₂ : s₂.regs r_nA = n_A := by
    rw [hreg₂ r_nA (by omega)]
    simp [s₁, State.setReg, show r_nA ≠ r_base + 1 by omega, hrnA]
  rcases appendWordProg_exec (val := n_A) a_buf r_base (.reg r_nA) h1_w
      (by simp [h1_w]) hbuf₂' hrpos₂ (by simp [Expr.eval, checkWord, hrnA₂, hnA_w]) with
    ⟨s₃, t₃, hex₃, ht₃, hbuf₃, hrpos₃, harr₃, hreg₃⟩
  rcases appendWordProg_exec (val := 0) a_buf r_base (.const 0) h1_w
      (by simp [h2_w]) hbuf₃ hrpos₃ (by simp [Expr.eval, checkWord, h0_w]) with
    ⟨s₄, t₄, hex₄, ht₄, hbuf₄, hrpos₄, harr₄, hreg₄⟩
  let s₅ := s₄.setReg r_numP 0
  have hex₅ : Exec w (.assign r_numP (.const 0)) s₄ s₅ 2 :=
    .assign (by simp [Expr.eval, checkWord, h0_w])
  let s₆ := s₅.setReg (r_base + 2) 0
  have hex₆ : Exec w (.assign (r_base + 2) (.const 0)) s₅ s₆ 2 :=
    .assign (by simp [Expr.eval, checkWord, h0_w])
  let OuterInv (i : ℕ) (st : State) : Prop :=
    let ps := activePrefixPairs G_A i
    st.arrs a_buf = [n_A, 0] ++ G_A.flatTriples ps ++ List.replicate (cap - 3 * ps.length) 0 ∧
    st.regs r_base = 2 + 3 * ps.length ∧
    st.regs r_numP = ps.length ∧
    st.regs r_nA = n_A ∧
    st.regs (r_base + 2) = i ∧
    (∀ a : ℕ, a ≠ a_buf → st.arrs a = s.arrs a) ∧
    (∀ r < r_base, r ≠ r_numP → st.regs r = s.regs r)
  have hOuter₀ : OuterInv 0 s₆ := by
    refine ⟨?_, ?_,
      by simp [s₆, s₅, State.setReg, show r_numP ≠ r_base + 2 by omega],
      by simp [s₆, s₅, State.setReg, hne_nP, show r_nA ≠ r_base + 2 by omega,
        hreg₄ r_nA (by omega), hreg₃ r_nA (by omega), hrnA₂],
      by simp [s₆],
      fun a ha => by simp [s₆, s₅, harr₄ a ha, harr₃ a ha, harr₂ a ha, s₁],
      fun r hr hne => by
        simp [s₆, s₅, State.setReg, hne, show r ≠ r_base + 2 by omega,
          hreg₄ r (by omega), hreg₃ r (by omega), hreg₂ r (by omega),
          s₁, show r ≠ r_base + 1 by omega]⟩
    · simpa [s₆, s₅, IsPrefixBuffer, MultiDigraph.flatTriples] using hbuf₄
    · simpa [s₆, s₅, State.setReg, show r_base ≠ r_numP by omega] using hrpos₄
  have hOuterLoop :
      ⦃OuterInv 0⦄[w]
        forUp (r_base + 2) (.reg r_nA)
          (.seq (.assign (r_base + 3) (.const 0))
            (forUp (r_base + 3) (.reg r_nA)
              (buildEncPairBody a_mult a_buf r_nA r_base r_numP
                (r_base + 2) (r_base + 3) (r_base + 4))))
      ⦃OuterInv n_A⦄ ≤ fun _ => 3 + n_A * (7 + (5 + n_A * (7 + 72))) := by
    apply Triple.forUp_const OuterInv n_A (5 + n_A * (7 + 72)) h1_w hnA_w
    · intro i _ st ⟨_, _, _, hrnA_st, hru_st, _, _⟩
      exact ⟨hru_st, by simp [Expr.eval, checkWord, hrnA_st, hnA_w]⟩
    · intro i hi st ⟨hbuf_st, hrpos_st, hrnumP_st, hrnA_st, hru_st, harr_st, hreg_st⟩
      let u : Fin n_A := ⟨i, hi⟩
      let st₀ := st.setReg (r_base + 3) 0
      have hex_v0 : Exec w (.assign (r_base + 3) (.const 0)) st st₀ 2 :=
        .assign (by simp [Expr.eval, checkWord, h0_w])
      let InnerInv (j : ℕ) (st' : State) : Prop :=
        let ps := activePrefixPairs G_A i ++ activeRowPairs G_A u j
        st'.arrs a_buf = [n_A, 0] ++ G_A.flatTriples ps ++ List.replicate (cap - 3 * ps.length) 0 ∧
        st'.regs r_base = 2 + 3 * ps.length ∧
        st'.regs r_numP = ps.length ∧
        st'.regs r_nA = n_A ∧
        st'.regs (r_base + 2) = i ∧
        st'.regs (r_base + 3) = j ∧
        (∀ a : ℕ, a ≠ a_buf → st'.arrs a = s.arrs a) ∧
        (∀ r < r_base, r ≠ r_numP → st'.regs r = s.regs r)
      have hInner₀ : InnerInv 0 st₀ := by
        refine ⟨by simpa [st₀] using hbuf_st,
          by simpa [st₀, State.setReg] using hrpos_st,
          by simpa [st₀, State.setReg, show r_numP ≠ r_base + 3 by omega] using hrnumP_st,
          by simpa [st₀, State.setReg, show r_nA ≠ r_base + 3 by omega] using hrnA_st,
          by simpa [st₀, State.setReg] using hru_st,
          by simp [st₀],
          fun a ha => by simp [st₀, harr_st a ha],
          fun r hr hne => by simp [st₀, State.setReg, show r ≠ r_base + 3 by omega, hreg_st r hr hne]⟩
      have hInnerLoop :
          ⦃InnerInv 0⦄[w]
            forUp (r_base + 3) (.reg r_nA)
              (buildEncPairBody a_mult a_buf r_nA r_base r_numP
                (r_base + 2) (r_base + 3) (r_base + 4))
          ⦃InnerInv n_A⦄ ≤ fun _ => 3 + n_A * (7 + 72) := by
        apply Triple.forUp_const InnerInv n_A 72 h1_w hnA_w
        · intro j _ st' ⟨_, _, _, hrnA', _, hrv', _, _⟩
          exact ⟨hrv', by simp [Expr.eval, checkWord, hrnA', hnA_w]⟩
        · intro j hj st' ⟨hbuf', hrpos', hrnumP', hrnA', hru', hrv', harr', hreg'⟩
          let v : Fin n_A := ⟨j, hj⟩
          let ps := activePrefixPairs G_A i ++ activeRowPairs G_A u j
          change st'.regs r_base = 2 + 3 * ps.length at hrpos'
          change st'.regs r_numP = ps.length at hrnumP'
          have hps_le : ps.length ≤ 2 * (i * n_A + j) := by
            rw [List.length_append]
            have h1 := length_activePrefixPairs_le G_A i (Nat.le_of_lt hi)
            have h2 := length_activeRowPairs_le G_A u j (Nat.le_of_lt hj)
            omega
          have hij_lt : i * n_A + j + 1 ≤ n_A * n_A := by
            calc i * n_A + j + 1 ≤ i * n_A + n_A := by omega
              _ = (i + 1) * n_A := by ring
              _ ≤ n_A * n_A := Nat.mul_le_mul_right n_A hi
          have hcap_ps2 : 3 * (ps.length + 2) ≤ cap := by
            dsimp [cap]; omega
          have hi_w : i < 2 ^ w := by omega
          have hj_w : j < 2 ^ w := by omega
          have hmult_st' : st'.arrs a_mult = s.arrs a_mult := harr' a_mult hne_mb
          unfold buildEncPairBody
          rcases lt_trichotomy j i with hlt | rfl | hgt
          · have hcond_lt : (Expr.op .lt (.reg (r_base + 3)) (.reg (r_base + 2))).eval w st' = some 1 := by
              simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hrv', hru', hj_w, hi_w, hlt, h1_w]
            have hblk : upperActiveBlock G_A u v = [] := upperActiveBlock_eq_of_gt G_A hlt
            have hps_step : activePrefixPairs G_A i ++ activeRowPairs G_A u (j + 1) = ps := by
              rw [activeRowPairs_succ G_A u hj, hblk, List.append_nil]
            refine ⟨st', 3 + 1, .if_true (v := 1) hcond_lt (by decide) (.skip st'),
              by dsimp only; omega,
              ⟨by rw [State.setReg_arrs, hps_step]; exact hbuf',
               by rw [hps_step]; simp [State.setReg, hrpos'],
               by rw [hps_step]; simp [State.setReg, show r_numP ≠ r_base + 3 by omega, hrnumP'],
               by simp [State.setReg, show r_nA ≠ r_base + 3 by omega, hrnA'],
               by simp [State.setReg, hru'],
               by simp [State.setReg],
               fun a ha => by simp [harr' a ha],
               fun r hr hne => by simp [State.setReg, show r ≠ r_base + 3 by omega, hreg' r hr hne]⟩,
              hrv'⟩
          · have hcond_lt : (Expr.op .lt (.reg (r_base + 3)) (.reg (r_base + 2))).eval w st' = some 0 := by
              simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hrv', hru', hj_w, h0_w]
            have hcond_eq : (Expr.op .eq (.reg (r_base + 2)) (.reg (r_base + 3))).eval w st' = some 1 := by
              simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hru', hrv', hj_w, h1_w]
            have huu_lt : j * n_A + j < n_A * n_A := by omega
            have huu_mlen : j * n_A + j < (st'.arrs a_mult).length := by
              rw [hmult_st', hmult_len]; exact huu_lt
            have hget_uu : (st'.arrs a_mult)[j * n_A + j]'huu_mlen = G_A.edgeMult u u := by
              have h := hmult_get u u
              rw [List.getD_eq_getElem _ _ (by rw [hmult_len]; exact huu_lt)] at h
              simpa [hmult_st', u] using h
            have hmul_w : j * n_A < 2 ^ w := by omega
            have huu_w : j * n_A + j < 2 ^ w := by omega
            have hmuu_w : G_A.edgeMult u u < 2 ^ w := hm_w u u
            let st₁ := st'.setReg (r_base + 4) (G_A.edgeMult u u)
            have hex_rd :
                Exec w
                  (.assign (r_base + 4)
                    (.read a_mult (.op .add (.op .mul (.reg (r_base + 2)) (.reg r_nA)) (.reg (r_base + 2)))))
                  st' st₁ 7 :=
              .assign (by simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord,
                hru', hrnA', hj_w, hnA_w, hmul_w, huu_w, huu_mlen, hget_uu, hmuu_w])
            rcases maybePushPairProg_exec G_A u u ps
                a_buf r_base r_numP (r_base + 2) (r_base + 2) (r_base + 4)
                (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                (by omega) h1_w hnA_w hmuu_w (by omega) (s := st₁)
                hbuf'
                (by simp [st₁, State.setReg, hrpos'])
                (by simp [st₁, State.setReg, show r_numP ≠ r_base + 4 by omega, hrnumP'])
                (by simp [st₁, State.setReg, hru', u])
                (by simp [st₁, State.setReg, hru', u])
                (by simp [st₁]) with
              ⟨st₂, t_push, hex_push, ht_push, hbuf₂, hrpos₂, hrnumP₂, harr₂, hreg₂⟩
            have hps_step :
                activePrefixPairs G_A j ++ activeRowPairs G_A u (j + 1) =
                  ps ++ if 0 < G_A.edgeMult u u then [(u, u)] else [] := by
              rw [activeRowPairs_succ G_A u hj, upperActiveBlock_eq_of_eq G_A u, List.append_assoc]
            refine ⟨st₂, 3 + (3 + (7 + t_push)),
              .if_false hcond_lt (.if_true (v := 1) hcond_eq (by decide) (.seq hex_rd hex_push)),
              by dsimp only; omega,
              ⟨by rw [State.setReg_arrs, hps_step]; exact hbuf₂,
               by rw [hps_step]; simp [State.setReg, hrpos₂],
               by rw [hps_step]; simp [State.setReg, show r_numP ≠ r_base + 3 by omega, hrnumP₂],
               by simp [State.setReg, show r_nA ≠ r_base + 3 by omega,
                 hreg₂ r_nA (by omega) hne_nP, st₁, show r_nA ≠ r_base + 4 by omega, hrnA'],
               by simp [State.setReg, hreg₂ (r_base + 2) (by omega) (by omega), st₁, hru'],
               by simp [State.setReg],
               fun a ha => by simp [(harr₂ a ha).trans (harr' a ha)],
               fun r hr hne => by
                 simp [State.setReg, show r ≠ r_base + 3 by omega,
                   hreg₂ r (by omega) hne, st₁, show r ≠ r_base + 4 by omega, hreg' r hr hne]⟩,
              by rw [hreg₂ (r_base + 3) (by omega) (by omega)]; simp [st₁, State.setReg, hrv']⟩
          · have hcond_lt : (Expr.op .lt (.reg (r_base + 3)) (.reg (r_base + 2))).eval w st' = some 0 := by
              have : ¬(j < i) := by omega
              simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hrv', hru', hj_w, hi_w, this, h0_w]
            have hcond_eq : (Expr.op .eq (.reg (r_base + 2)) (.reg (r_base + 3))).eval w st' = some 0 := by
              have : i ≠ j := by omega
              simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hru', hrv', hi_w, hj_w, this, h0_w]
            have huv_lt : i * n_A + j < n_A * n_A := by omega
            have hvu_lt : j * n_A + i < n_A * n_A := by
              calc j * n_A + i < j * n_A + n_A := by omega
                _ = (j + 1) * n_A := by ring
                _ ≤ n_A * n_A := Nat.mul_le_mul_right n_A hj
            have huv_mlen : i * n_A + j < (st'.arrs a_mult).length := by
              rw [hmult_st', hmult_len]; exact huv_lt
            have hget_uv : (st'.arrs a_mult)[i * n_A + j]'huv_mlen = G_A.edgeMult u v := by
              have h := hmult_get u v
              rw [List.getD_eq_getElem _ _ (by rw [hmult_len]; exact huv_lt)] at h
              simpa [hmult_st', u, v] using h
            have hmul1_w : i * n_A < 2 ^ w := by omega
            have huv_w : i * n_A + j < 2 ^ w := by omega
            have hmuv_w : G_A.edgeMult u v < 2 ^ w := hm_w u v
            let st₁ := st'.setReg (r_base + 4) (G_A.edgeMult u v)
            have hex_rd1 :
                Exec w
                  (.assign (r_base + 4)
                    (.read a_mult (.op .add (.op .mul (.reg (r_base + 2)) (.reg r_nA)) (.reg (r_base + 3)))))
                  st' st₁ 7 :=
              .assign (by simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord,
                hru', hrv', hrnA', hi_w, hj_w, hnA_w, hmul1_w, huv_w, huv_mlen, hget_uv, hmuv_w])
            rcases maybePushPairProg_exec G_A u v ps
                a_buf r_base r_numP (r_base + 2) (r_base + 3) (r_base + 4)
                (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                (by omega) h1_w hnA_w hmuv_w (by omega) (s := st₁)
                hbuf'
                (by simp [st₁, State.setReg, hrpos'])
                (by simp [st₁, State.setReg, show r_numP ≠ r_base + 4 by omega, hrnumP'])
                (by simp [st₁, State.setReg, hru', u])
                (by simp [st₁, State.setReg, hrv', v])
                (by simp [st₁]) with
              ⟨st₂, t_push1, hex_push1, ht_push1, hbuf₂, hrpos₂, hrnumP₂, harr₂, hreg₂⟩
            let ps₁ := ps ++ if 0 < G_A.edgeMult u v then [(u, v)] else []
            change st₂.regs r_base = 2 + 3 * ps₁.length at hrpos₂
            change st₂.regs r_numP = ps₁.length at hrnumP₂
            have hps₁_le : ps₁.length ≤ ps.length + 1 := by
              dsimp [ps₁]; rw [List.length_append]; split_ifs <;> simp
            have hmult_st₂ : st₂.arrs a_mult = s.arrs a_mult :=
              (harr₂ a_mult hne_mb).trans hmult_st'
            have hvu_mlen : j * n_A + i < (st₂.arrs a_mult).length := by
              rw [hmult_st₂, hmult_len]; exact hvu_lt
            have hget_vu : (st₂.arrs a_mult)[j * n_A + i]'hvu_mlen = G_A.edgeMult v u := by
              have h := hmult_get v u
              rw [List.getD_eq_getElem _ _ (by rw [hmult_len]; exact hvu_lt)] at h
              simpa [hmult_st₂, u, v] using h
            have hmul2_w : j * n_A < 2 ^ w := by omega
            have hvu_w : j * n_A + i < 2 ^ w := by omega
            have hmvu_w : G_A.edgeMult v u < 2 ^ w := hm_w v u
            have hru₂ : st₂.regs (r_base + 2) = i := by
              rw [hreg₂ (r_base + 2) (by omega) (by omega)]
              simp [st₁, State.setReg, hru']
            have hrv₂ : st₂.regs (r_base + 3) = j := by
              rw [hreg₂ (r_base + 3) (by omega) (by omega)]
              simp [st₁, State.setReg, hrv']
            have hrnA₂ : st₂.regs r_nA = n_A := by
              rw [hreg₂ r_nA (by omega) hne_nP]
              simp [st₁, State.setReg, show r_nA ≠ r_base + 4 by omega, hrnA']
            let st₃ := st₂.setReg (r_base + 4) (G_A.edgeMult v u)
            have hex_rd2 :
                Exec w
                  (.assign (r_base + 4)
                    (.read a_mult (.op .add (.op .mul (.reg (r_base + 3)) (.reg r_nA)) (.reg (r_base + 2)))))
                  st₂ st₃ 7 :=
              .assign (by simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord,
                hru₂, hrv₂, hrnA₂, hi_w, hj_w, hnA_w, hmul2_w, hvu_w, hvu_mlen, hget_vu, hmvu_w])
            rcases maybePushPairProg_exec G_A v u ps₁
                a_buf r_base r_numP (r_base + 3) (r_base + 2) (r_base + 4)
                (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
                (by omega) h1_w hnA_w hmvu_w (by omega) (s := st₃)
                hbuf₂
                (by simp [st₃, State.setReg, hrpos₂])
                (by simp [st₃, State.setReg, show r_numP ≠ r_base + 4 by omega, hrnumP₂])
                (by simp [st₃, State.setReg, hrv₂, v])
                (by simp [st₃, State.setReg, hru₂, u])
                (by simp [st₃]) with
              ⟨st₄, t_push2, hex_push2, ht_push2, hbuf₄, hrpos₄, hrnumP₄, harr₄, hreg₄⟩
            have hps_step :
                activePrefixPairs G_A i ++ activeRowPairs G_A u (j + 1) =
                  ps₁ ++ if 0 < G_A.edgeMult v u then [(v, u)] else [] := by
              rw [activeRowPairs_succ G_A u hj, upperActiveBlock_eq_of_lt G_A hgt]
              simp [ps₁, ps, v, List.append_assoc]
            refine ⟨st₄, 3 + (3 + (7 + (t_push1 + (7 + t_push2)))),
              .if_false hcond_lt (.if_false hcond_eq
                (.seq hex_rd1 (.seq hex_push1 (.seq hex_rd2 hex_push2)))),
              by dsimp only; omega,
              ⟨by rw [State.setReg_arrs, hps_step]; exact hbuf₄,
               by rw [hps_step]; simp [State.setReg, hrpos₄],
               by rw [hps_step]; simp [State.setReg, show r_numP ≠ r_base + 3 by omega, hrnumP₄],
               by simp [State.setReg, show r_nA ≠ r_base + 3 by omega,
                 hreg₄ r_nA (by omega) hne_nP, st₃, show r_nA ≠ r_base + 4 by omega, hrnA₂],
               by simp [State.setReg, hreg₄ (r_base + 2) (by omega) (by omega), st₃, hru₂],
               by simp [State.setReg],
               fun a ha => by simp [(harr₄ a ha).trans ((harr₂ a ha).trans (harr' a ha))],
               fun r hr hne => by
                 simp [State.setReg, show r ≠ r_base + 3 by omega,
                   hreg₄ r (by omega) hne, st₃, show r ≠ r_base + 4 by omega,
                   hreg₂ r (by omega) hne, st₁, hreg' r hr hne]⟩,
              by rw [hreg₄ (r_base + 3) (by omega) (by omega)]; simp [st₃, State.setReg, hrv₂]⟩
      rcases hInnerLoop st₀ hInner₀ with
        ⟨st_end, t_inner, hex_inner, ht_inner,
          ⟨hbuf_end, hrpos_end, hrnumP_end, hrnA_end, hru_end, _, harr_end, hreg_end⟩⟩
      dsimp only at ht_inner
      rw [← activePrefixPairs_succ G_A hi] at hbuf_end hrpos_end hrnumP_end
      exact ⟨st_end, 2 + t_inner, .seq hex_v0 hex_inner, by dsimp only; omega,
        ⟨by simpa using hbuf_end,
         by simp [State.setReg, hrpos_end],
         by simp [State.setReg, show r_numP ≠ r_base + 2 by omega, hrnumP_end],
         by simp [State.setReg, show r_nA ≠ r_base + 2 by omega, hrnA_end],
         by simp [State.setReg],
         fun a ha => by simp [harr_end a ha],
         fun r hr hne => by simp [State.setReg, show r ≠ r_base + 2 by omega, hreg_end r hr hne]⟩,
        hru_end⟩
  rcases hOuterLoop s₆ hOuter₀ with
    ⟨s₇, t₇, hex₇, ht₇, ⟨hbuf₇, hrpos₇, hrnumP₇, _, _, harr₇, hreg₇⟩⟩
  dsimp only at ht₇
  rw [activePrefixPairs_full] at hbuf₇ hrpos₇ hrnumP₇
  change s₇.regs r_numP = G_A.numActivePairs at hrnumP₇
  change s₇.regs r_base = 2 + 3 * G_A.numActivePairs at hrpos₇
  have hnp_le_sq : G_A.numActivePairs ≤ n_A * n_A := G_A.numActivePairs_le_sq
  have hnp_w : G_A.numActivePairs < 2 ^ w := by omega
  have h1_len : 1 < (s₇.arrs a_buf).length := by simp [hbuf₇]
  let s₈ := s₇.writeArr a_buf 1 G_A.numActivePairs
  have hex₈ : Exec w (.write a_buf (.const 1) (.reg r_numP)) s₇ s₈ 3 :=
    .write (by simp [Expr.eval, checkWord, h1_w])
      (by simp [Expr.eval, checkWord, hrnumP₇, hnp_w]) h1_len
  have hbuf₈ : IsPrefixBuffer a_buf G_A.enc (cap - 3 * G_A.numActivePairs) s₈ := by
    have hnp_eq : G_A.activePairsList.length = G_A.numActivePairs := rfl
    rw [hnp_eq] at hbuf₇
    unfold IsPrefixBuffer MultiDigraph.enc
    simp [s₈, State.writeArr, hbuf₇]
  have henc_words_w : ∀ x ∈ G_A.enc, x < 2 ^ w := by
    intro x hx
    simp only [MultiDigraph.enc, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with (rfl | rfl) | hx_flat
    · exact hnA_w
    · exact hnp_w
    · exact all_lt_flatTriples G_A G_A.activePairsList hnA_w
        (fun p hp => hm_w p.1 p.2) x hx_flat
  have henc_len_w : G_A.enc.length < 2 ^ w := by
    rw [G_A.length_enc]; omega
  rcases copyBufPrefixProg_exec a_buf a_enc r_base (r_base + 2)
      hne_be (by omega) henc_words_w h1_w henc_len_w hbuf₈
      (by simp [s₈, hrpos₇, G_A.length_enc]) with
    ⟨s₉, t₉, hex₉, ht₉, henc₉, harr₉, hreg₉⟩
  have hmul_expand :
      n_A * (7 + (5 + n_A * (7 + 72))) = 79 * (n_A * n_A) + 12 * n_A := by ring
  rw [hmul_expand] at ht₇
  rw [G_A.length_enc] at ht₉
  refine ⟨s₉,
    8 + (t₂ + (t₃ + (t₄ + (2 + (2 + (t₇ + (3 + t₉))))))),
    .seq hex₁ (.seq hex₂ (.seq hex₃ (.seq hex₄ (.seq hex₅ (.seq hex₆ (.seq hex₇ (.seq hex₈ hex₉))))))),
    by simp [Expr.cost, cap] at ht₂ ht₃ ht₄; omega,
    henc₉,
    by rw [hreg₉ r_numP (by omega)]; exact hrnumP₇,
    fun a ha₁ ha₂ => by
      rw [harr₉ a ha₂]
      simp [s₈, ha₁, harr₇ a ha₁],
    fun r hr hne => by
      rw [hreg₉ r (by omega)]
      exact hreg₇ r hr hne⟩

/-! ### Section 2: Building the Leaf Map `memberFTau0` (`buildFTau0Prog`) -/

/-- For a given pair of vertex labels `(x, y)` and `k ≤ r.eList.length`, the `tauList` values of
the edges in `r.eList.take k` with tail `x` and head `y`. -/
def fTau0RowPrefix (r : Case3MemberRecord) (x y k : ℕ) : List ℕ :=
  (List.range k).flatMap (fun idx =>
    if (r.eList.getD idx (0, 0, 0)).1 = x ∧ (r.eList.getD idx (0, 0, 0)).2.1 = y then
      [r.tauList.getD idx 0]
    else [])

/-- Full row `fTau0RowPrefix r x y r.eList.length`. -/
def fTau0RowList (r : Case3MemberRecord) (x y : ℕ) : List ℕ :=
  fTau0RowPrefix r x y r.eList.length

@[simp]
theorem fTau0RowPrefix_zero (r : Case3MemberRecord) (x y : ℕ) :
    fTau0RowPrefix r x y 0 = [] := rfl

theorem fTau0RowPrefix_succ (r : Case3MemberRecord) (x y k : ℕ) :
    fTau0RowPrefix r x y (k + 1) =
      fTau0RowPrefix r x y k ++
        (if (r.eList.getD k (0, 0, 0)).1 = x ∧ (r.eList.getD k (0, 0, 0)).2.1 = y then
          [r.tauList.getD k 0]
        else []) := by
  simp [fTau0RowPrefix, List.range_succ, List.flatMap_append]

theorem length_fTau0RowPrefix_le (r : Case3MemberRecord) (x y k : ℕ) :
    (fTau0RowPrefix r x y k).length ≤ k := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [fTau0RowPrefix_succ, List.length_append]
    split_ifs <;> simp <;> omega

theorem fTau0RowPrefix_eq_map_filter_take (r : Case3MemberRecord) (hr_nd : r.eList.Nodup)
    (x y k : ℕ) (hk : k ≤ r.eList.length) :
    fTau0RowPrefix r x y k =
      ((r.eList.take k).filter (fun e => decide (e.1 = x ∧ e.2.1 = y))).map
        (fun e => r.tauList.getD (r.eList.idxOf e) 0) := by
  induction k with
  | zero => simp [fTau0RowPrefix]
  | succ k ih =>
    have hk_lt : k < r.eList.length := by omega
    rw [fTau0RowPrefix_succ, ih (by omega), List.take_add_one,
      List.getElem?_eq_getElem hk_lt, Option.toList_some,
      List.filter_append, List.map_append]
    congr 1
    rw [List.getD_eq_getElem _ _ hk_lt]
    by_cases hxy : (r.eList[k]'hk_lt).1 = x ∧ (r.eList[k]'hk_lt).2.1 = y
    · simp [hxy, hr_nd.idxOf_getElem k hk_lt]
    · simp [hxy]

theorem fTau0RowList_eq_map_edgesBetween (r : Case3MemberRecord) (hr_nd : r.eList.Nodup)
    (x y : ℕ) :
    fTau0RowList r x y =
      (edgesBetween r.eList x y).map (fun e => r.tauList.getD (r.eList.idxOf e) 0) := by
  simpa [fTau0RowList, edgesBetween] using
    fTau0RowPrefix_eq_map_filter_take r hr_nd x y r.eList.length le_rfl

theorem length_fTau0RowList_eq_edgeMult (vList : List ℕ) (r : Case3MemberRecord)
    (hr_nd : r.eList.Nodup) (u v : Fin vList.length) :
    (fTau0RowList r (vList[u.1]'u.2) (vList[v.1]'v.2)).length =
      (tildeAMultiDigraph vList r.eList).edgeMult u v := by
  rw [fTau0RowList_eq_map_edgesBetween r hr_nd, List.length_map]
  rfl

theorem fTau0RowList_eq_nil_of_edgeMult_eq_zero (vList : List ℕ) (r : Case3MemberRecord)
    (hr_nd : r.eList.Nodup) (u v : Fin vList.length)
    (h0 : (tildeAMultiDigraph vList r.eList).edgeMult u v = 0) :
    fTau0RowList r (vList[u.1]'u.2) (vList[v.1]'v.2) = [] := by
  rw [← List.length_eq_zero_iff, length_fTau0RowList_eq_edgeMult vList r hr_nd u v, h0]

/-- Prefix of `fTau0` for fixed `u : Fin vList.length` and `0 ≤ v ≤ vList.length`. -/
def fTau0ColPrefix (vList : List ℕ) (r : Case3MemberRecord) (u : Fin vList.length) (v : ℕ) :
    List ℕ :=
  ((List.finRange vList.length).take v).flatMap (fun v' =>
    fTau0RowList r (vList[u.1]'u.2) (vList[v'.1]'v'.2))

private theorem take_finRange_succ {n i : ℕ} (hi : i < n) :
    (List.finRange n).take (i + 1) = (List.finRange n).take i ++ [⟨i, hi⟩] := by
  have hi_len : i < (List.finRange n).length := by simp [hi]
  rw [take_add_one_eq_append_getElem (List.finRange n) i hi_len, List.getElem_finRange]
  rfl

@[simp]
theorem fTau0ColPrefix_zero (vList : List ℕ) (r : Case3MemberRecord) (u : Fin vList.length) :
    fTau0ColPrefix vList r u 0 = [] := rfl

theorem fTau0ColPrefix_succ (vList : List ℕ) (r : Case3MemberRecord) (u : Fin vList.length)
    {v : ℕ} (hv : v < vList.length) :
    fTau0ColPrefix vList r u (v + 1) =
      fTau0ColPrefix vList r u v ++ fTau0RowList r (vList[u.1]'u.2) (vList[v]'hv) := by
  unfold fTau0ColPrefix
  rw [take_finRange_succ hv, List.flatMap_append]
  simp

/-- Prefix of `fTau0` for `0 ≤ u ≤ vList.length`. -/
def fTau0OuterPrefix (vList : List ℕ) (r : Case3MemberRecord) (u : ℕ) : List ℕ :=
  ((List.finRange vList.length).take u).flatMap (fun u' =>
    fTau0ColPrefix vList r u' vList.length)

@[simp]
theorem fTau0OuterPrefix_zero (vList : List ℕ) (r : Case3MemberRecord) :
    fTau0OuterPrefix vList r 0 = [] := rfl

theorem fTau0OuterPrefix_succ (vList : List ℕ) (r : Case3MemberRecord)
    {u : ℕ} (hu : u < vList.length) :
    fTau0OuterPrefix vList r (u + 1) =
      fTau0OuterPrefix vList r u ++ fTau0ColPrefix vList r ⟨u, hu⟩ vList.length := by
  unfold fTau0OuterPrefix
  rw [take_finRange_succ hu, List.flatMap_append]
  simp

private theorem map_range_getD {α : Type*} (L : List α) (d : α) :
    (List.range L.length).map (fun k => L.getD k d) = L := by
  apply List.ext_getElem (by simp)
  intro i hi₁ hi₂
  simp [List.getElem?_eq_getElem hi₂]

theorem ofFn_tildeADelEdgeTriple (vList : List ℕ) (eList : List (ℕ × ℕ × ℕ)) :
    List.ofFn (fun i : Fin (tildeAMultiDigraph vList eList).toComputeDigraph.numEdges =>
      tildeADelEdgeTriple vList eList i) =
    (List.finRange vList.length).flatMap (fun u =>
      (List.finRange vList.length).flatMap (fun v =>
        edgesBetween eList (vList[u.1]'u.2) (vList[v.1]'v.2))) := by
  let G_del := tildeAMultiDigraph vList eList
  have h1 :
      List.ofFn (fun i : Fin G_del.toComputeDigraph.numEdges =>
        tildeADelEdgeTriple vList eList i) =
      G_del.directedEdgeTriples.map (fun p =>
        (edgesBetween eList (vList.getD p.1 0) (vList.getD p.2.1 0)).getD p.2.2 (0, 0, 0)) := by
    apply List.ext_getElem (by simp [G_del, MultiDigraph.length_directedEdgeTriples])
    intro i hi₁ hi₂
    simp [tildeADelEdgeTriple, MultiDigraph.edgeEquiv, MultiDigraph.edgeToGMTriple, G_del]
  rw [h1]
  unfold G_del MultiDigraph.directedEdgeTriples
  simp only [List.map_flatMap, List.map_map]
  refine List.flatMap_congr fun u _ => List.flatMap_congr fun v _ => ?_
  have hfn :
      ((fun p : ℕ × ℕ × ℕ =>
          (edgesBetween eList (vList.getD p.1 0) (vList.getD p.2.1 0)).getD p.2.2 (0, 0, 0)) ∘
        fun k : ℕ => (u.1, v.1, k)) =
      fun k : ℕ => (edgesBetween eList (vList[u.1]'u.2) (vList[v.1]'v.2)).getD k (0, 0, 0) := by
    funext k; simp
  rw [hfn]
  exact map_range_getD (edgesBetween eList (vList[u.1]'u.2) (vList[v.1]'v.2)) (0, 0, 0)

theorem fTau0OuterPrefix_full_eq_ofFn (vList : List ℕ) (r : Case3MemberRecord)
    (hr_nd : r.eList.Nodup) :
    fTau0OuterPrefix vList r vList.length =
      List.ofFn (fun i : Fin (tildeAMultiDigraph vList r.eList).toComputeDigraph.numEdges =>
        memberFTau0 vList r i.1) := by
  have hfn :
      List.ofFn (fun i : Fin (tildeAMultiDigraph vList r.eList).toComputeDigraph.numEdges =>
        memberFTau0 vList r i.1) =
      (List.ofFn (fun i : Fin (tildeAMultiDigraph vList r.eList).toComputeDigraph.numEdges =>
        tildeADelEdgeTriple vList r.eList i)).map
          (fun e => r.tauList.getD (r.eList.idxOf e) 0) := by
    apply List.ext_getElem (by simp)
    intro i hi₁ hi₂
    simp only [List.getElem_ofFn, List.getElem_map]
    unfold memberFTau0
    have hi_lt : i < (tildeAMultiDigraph vList r.eList).toComputeDigraph.numEdges := by simpa using hi₁
    rw [dite_eq_left hi_lt]
  rw [hfn, ofFn_tildeADelEdgeTriple, List.map_flatMap]
  unfold fTau0OuterPrefix fTau0ColPrefix
  rw [List.take_of_length_le (by simp)]
  refine List.flatMap_congr fun u _ => ?_
  rw [List.map_flatMap]
  refine List.flatMap_congr fun v _ => ?_
  exact fTau0RowList_eq_map_edgesBetween r hr_nd (vList[u.1]'u.2) (vList[v.1]'v.2)

theorem length_fTau0OuterPrefix_add_colPrefix_le (vList : List ℕ) (r : Case3MemberRecord)
    (hv_nd : vList.Nodup) (hr_nd : r.eList.Nodup)
    (he_ends : ∀ e ∈ r.eList, e.1 ∈ vList ∧ e.2.1 ∈ vList)
    (u : Fin vList.length) (v : ℕ) (hv : v ≤ vList.length) :
    (fTau0OuterPrefix vList r u.1 ++ fTau0ColPrefix vList r u v).length ≤ r.eList.length := by
  have hnum := (tildeADelEdgeTriple_mem_and_bijOn vList r.eList hv_nd hr_nd he_ends).1
  have hfull_len : (fTau0OuterPrefix vList r vList.length).length = r.eList.length := by
    rw [fTau0OuterPrefix_full_eq_ofFn vList r hr_nd, List.length_ofFn, hnum]
  rw [← hfull_len]
  have hcol_le : (fTau0ColPrefix vList r u v).length ≤
      (fTau0ColPrefix vList r u vList.length).length := by
    unfold fTau0ColPrefix
    have hsplit := (List.take_append_drop v ((List.finRange vList.length).take vList.length)).symm
    have htake : ((List.finRange vList.length).take vList.length).take v =
        (List.finRange vList.length).take v := by
      rw [List.take_take, Nat.min_eq_left hv]
    rw [htake] at hsplit
    conv_rhs => rw [hsplit, List.flatMap_append]
    rw [List.length_append]; omega
  have hout_le :
      (fTau0OuterPrefix vList r u.1 ++ fTau0ColPrefix vList r u vList.length).length ≤
        (fTau0OuterPrefix vList r vList.length).length := by
    rw [← fTau0OuterPrefix_succ vList r u.2]
    unfold fTau0OuterPrefix
    have hsplit :=
      (List.take_append_drop (u.1 + 1) ((List.finRange vList.length).take vList.length)).symm
    have htake : ((List.finRange vList.length).take vList.length).take (u.1 + 1) =
        (List.finRange vList.length).take (u.1 + 1) := by
      rw [List.take_take, Nat.min_eq_left u.2]
    rw [htake] at hsplit
    conv_rhs => rw [hsplit, List.flatMap_append]
    rw [List.length_append]; omega
  rw [List.length_append] at hout_le ⊢
  omega

/-- Inner loop body scanning `idx = s.regs (r_base + 3) < r.eList.length` and appending
`r.tauList[idx]` to `a_buf` when `r.eList[idx].1 == s.regs (r_base + 4)` and
`r.eList[idx].2.1 == s.regs (r_base + 5)`. -/
def scanFTau0EdgeBody (a_rE a_rTau a_buf : Arr) (r_base : Reg) : Cmd :=
  .seq (.assign (r_base + 6) (.read a_rE (.op .mul (.const 3) (.reg (r_base + 3)))))
    (.seq (.assign (r_base + 7)
        (.read a_rE (.op .add (.op .mul (.const 3) (.reg (r_base + 3))) (.const 1))))
      (.ite (.op .mul
          (.op .eq (.reg (r_base + 6)) (.reg (r_base + 4)))
          (.op .eq (.reg (r_base + 7)) (.reg (r_base + 5))))
        (.seq (.assign (r_base + 8) (.read a_rTau (.reg (r_base + 3))))
          (appendWordProg a_buf r_base (.reg (r_base + 8))))
        .skip))

theorem scanFTau0EdgeLoop_exec {w : ℕ}
    (r : Case3MemberRecord) (htau_len : r.tauList.length = r.eList.length)
    (he_w : ∀ x ∈ encEdgeTriples r.eList, x < 2 ^ w)
    (htau_w : ∀ x ∈ r.tauList, x < 2 ^ w)
    (x y : ℕ) (hx_w : x < 2 ^ w) (hy_w : y < 2 ^ w)
    (a_rE a_rTau a_buf r_eLen r_base : ℕ)
    (hne_eb : a_rE ≠ a_buf) (hne_tb : a_rTau ≠ a_buf)
    (hr_eLen : r_eLen < r_base)
    (hw3 : 3 < 2 ^ w) (he3_w : 3 * r.eList.length < 2 ^ w)
    (pfx : List ℕ) (hpfx_le : pfx.length ≤ r.eList.length)
    {s : State}
    (hrE : s.arrs a_rE = encEdgeTriples r.eList)
    (hrTau : s.arrs a_rTau = r.tauList)
    (hbuf : IsPrefixBuffer a_buf pfx (2 * r.eList.length - pfx.length) s)
    (hreLen : s.regs r_eLen = r.eList.length)
    (hrpos : s.regs r_base = pfx.length)
    (hridx : s.regs (r_base + 3) = 0)
    (hrx : s.regs (r_base + 4) = x)
    (hry : s.regs (r_base + 5) = y) :
    ∃ s' t,
      Exec w (forUp (r_base + 3) (.reg r_eLen) (scanFTau0EdgeBody a_rE a_rTau a_buf r_base)) s s' t ∧
      t ≤ 36 * r.eList.length + 5 ∧
      IsPrefixBuffer a_buf (pfx ++ fTau0RowList r x y)
        (2 * r.eList.length - (pfx ++ fTau0RowList r x y).length) s' ∧
      s'.regs r_base = (pfx ++ fTau0RowList r x y).length ∧
      s'.regs (r_base + 1) = s.regs (r_base + 1) ∧
      s'.regs (r_base + 2) = s.regs (r_base + 2) ∧
      s'.regs (r_base + 4) = x ∧
      (∀ a : ℕ, a ≠ a_buf → s'.arrs a = s.arrs a) ∧
      (∀ reg < r_base, s'.regs reg = s.regs reg) := by
  let m_r := r.eList.length
  have h0_w : 0 < 2 ^ w := by omega
  have h1_w : 1 < 2 ^ w := by omega
  have hmr_w : m_r < 2 ^ w := by omega
  let Inv (k : ℕ) (st : State) : Prop :=
    let cur := pfx ++ fTau0RowPrefix r x y k
    st.arrs a_rE = encEdgeTriples r.eList ∧
    st.arrs a_rTau = r.tauList ∧
    IsPrefixBuffer a_buf cur (2 * m_r - cur.length) st ∧
    st.regs r_eLen = m_r ∧
    st.regs r_base = cur.length ∧
    st.regs (r_base + 1) = s.regs (r_base + 1) ∧
    st.regs (r_base + 2) = s.regs (r_base + 2) ∧
    st.regs (r_base + 3) = k ∧
    st.regs (r_base + 4) = x ∧
    st.regs (r_base + 5) = y ∧
    (∀ a : ℕ, a ≠ a_buf → st.arrs a = s.arrs a) ∧
    (∀ reg < r_base, st.regs reg = s.regs reg)
  have hInv₀ : Inv 0 s :=
    ⟨hrE, hrTau, by simpa [m_r] using hbuf, hreLen, by simpa using hrpos,
      rfl, rfl, hridx, hrx, hry, fun _ _ => rfl, fun _ _ => rfl⟩
  have hLoop :
      ⦃Inv 0⦄[w]
        forUp (r_base + 3) (.reg r_eLen) (scanFTau0EdgeBody a_rE a_rTau a_buf r_base)
      ⦃Inv m_r⦄ ≤ fun _ => 3 + m_r * (7 + 29) := by
    apply Triple.forUp_const Inv m_r 29 h1_w hmr_w
    · intro k _ st ⟨_, _, _, hre_st, _, _, _, hridx_st, _, _, _, _⟩
      exact ⟨hridx_st, by simp [Expr.eval, checkWord, hre_st, hmr_w]⟩
    · intro k hk st ⟨hrE_st, hrTau_st, hbuf_st, hre_st, hrpos_st,
        hru_st, hrv_st, hridx_st, hrx_st, hry_st, harr_st, hreg_st⟩
      let cur := pfx ++ fTau0RowPrefix r x y k
      have hk_w : k < 2 ^ w := by omega
      have h3k_w : 3 * k < 2 ^ w := by omega
      have h3k1_w : 3 * k + 1 < 2 ^ w := by omega
      let e := r.eList[k]'hk
      have h3k_len : 3 * k < (st.arrs a_rE).length := by rw [hrE_st, length_encEdgeTriples]; omega
      have h3k1_len : 3 * k + 1 < (st.arrs a_rE).length := by rw [hrE_st, length_encEdgeTriples]; omega
      have hget_eu : (st.arrs a_rE)[3 * k]'h3k_len = e.1 := by
        rw [← List.getD_eq_getElem _ 0 h3k_len, hrE_st,
          List.getD_eq_getElem _ 0 (by rw [length_encEdgeTriples]; omega)]
        exact getElem_encEdgeTriples_u r.eList hk
      have hget_ev : (st.arrs a_rE)[3 * k + 1]'h3k1_len = e.2.1 := by
        rw [← List.getD_eq_getElem _ 0 h3k1_len, hrE_st,
          List.getD_eq_getElem _ 0 (by rw [length_encEdgeTriples]; omega)]
        exact getElem_encEdgeTriples_v r.eList hk
      have he1_w : e.1 < 2 ^ w :=
        he_w e.1 (by rw [mem_encEdgeTriples_iff]; exact ⟨e, List.getElem_mem hk, Or.inl rfl⟩)
      have he2_w : e.2.1 < 2 ^ w :=
        he_w e.2.1 (by rw [mem_encEdgeTriples_iff]; exact ⟨e, List.getElem_mem hk, Or.inr (Or.inl rfl)⟩)
      let st₁ := st.setReg (r_base + 6) e.1
      have hex₁ : Exec w (.assign (r_base + 6)
          (.read a_rE (.op .mul (.const 3) (.reg (r_base + 3))))) st st₁ 5 :=
        .assign (by simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord,
          hridx_st, hw3, hk_w, h3k_w, h3k_len, hget_eu, he1_w])
      let st₂ := st₁.setReg (r_base + 7) e.2.1
      have hex₂ : Exec w (.assign (r_base + 7)
          (.read a_rE (.op .add (.op .mul (.const 3) (.reg (r_base + 3))) (.const 1)))) st₁ st₂ 7 :=
        .assign (by simp [st₁, Expr.eval, BinOp.eval, BinOp.raw, checkWord,
          hridx_st, hw3, hk_w, h3k_w, h1_w, h3k1_w, h3k1_len, hget_ev, he2_w])
      have hsub_le : (fTau0RowPrefix r x y k).length ≤ k := length_fTau0RowPrefix_le r x y k
      have hcur_lt : cur.length < 2 * m_r := by dsimp [cur]; rw [List.length_append]; omega
      have hcur1_w : cur.length + 1 < 2 ^ w := by omega
      by_cases hxy : e.1 = x ∧ e.2.1 = y
      · have hcond :
            (Expr.op .mul
              (.op .eq (.reg (r_base + 6)) (.reg (r_base + 4)))
              (.op .eq (.reg (r_base + 7)) (.reg (r_base + 5)))).eval w st₂ = some 1 := by
          simp [st₂, st₁, Expr.eval, BinOp.eval, BinOp.raw, checkWord,
            hrx_st, hry_st, hx_w, hy_w, hxy.1, hxy.2, h1_w]
        have hk_tau : k < r.tauList.length := by rw [htau_len]; exact hk
        let tau := r.tauList[k]'hk_tau
        have htau_k_w : tau < 2 ^ w := htau_w tau (List.getElem_mem hk_tau)
        have hk_tau_len : k < (st.arrs a_rTau).length := by rw [hrTau_st]; exact hk_tau
        have hget_tau : (st.arrs a_rTau)[k]'hk_tau_len = tau := by simp [hrTau_st, tau]
        let st₃ := st₂.setReg (r_base + 8) tau
        have hex₃ : Exec w (.assign (r_base + 8) (.read a_rTau (.reg (r_base + 3)))) st₂ st₃ 3 :=
          .assign (by simp [st₂, st₁, Expr.eval, checkWord, hridx_st, hk_w, hk_tau_len, hget_tau, htau_k_w])
        have hbuf₃ : IsPrefixBuffer a_buf cur ((2 * m_r - (cur.length + 1)) + 1) st₃ := by
          unfold IsPrefixBuffer at hbuf_st ⊢
          have hrep : 2 * m_r - cur.length = (2 * m_r - (cur.length + 1)) + 1 := by omega
          rw [← hrep]; exact hbuf_st
        have hrpos₃ : st₃.regs r_base = cur.length := by simp [st₃, st₂, st₁, hrpos_st, cur]
        rcases appendWordProg_exec (val := tau) a_buf r_base (.reg (r_base + 8))
            h1_w hcur1_w hbuf₃ hrpos₃
            (by simp [st₃, Expr.eval, checkWord, htau_k_w]) with
          ⟨st₄, t₄, hex₄, ht₄, hbuf₄, hrpos₄, harr₄, hreg₄⟩
        have hcur_succ : pfx ++ fTau0RowPrefix r x y (k + 1) = cur ++ [tau] := by
          rw [fTau0RowPrefix_succ, List.getD_eq_getElem _ _ hk, List.getD_eq_getElem _ _ hk_tau]
          change pfx ++ (fTau0RowPrefix r x y k ++ (if e.1 = x ∧ e.2.1 = y then [tau] else [])) = cur ++ [tau]
          rw [ite_eq_left hxy, ← List.append_assoc]
        have hcur_len : (pfx ++ fTau0RowPrefix r x y (k + 1)).length = cur.length + 1 := by
          rw [hcur_succ, List.length_append, List.length_singleton]
        rw [← hcur_succ] at hbuf₄ hrpos₄
        refine ⟨st₄, 5 + (7 + (7 + (3 + t₄))),
          .seq hex₁ (.seq hex₂ (.if_true (v := 1) hcond (by decide) (.seq hex₃ hex₄))),
          by dsimp [Expr.cost] at ht₄ ⊢; omega,
          ⟨by simp only [State.setReg_arrs]; rw [harr₄ a_rE hne_eb]; simp [st₃, st₂, st₁, hrE_st],
           by simp only [State.setReg_arrs]; rw [harr₄ a_rTau hne_tb]; simp [st₃, st₂, st₁, hrTau_st],
           by rw [hcur_len]; exact hbuf₄,
           by simp only [State.setReg_regs, ite_eq_right (show r_eLen ≠ r_base + 3 by omega)]
              rw [hreg₄ r_eLen hr_eLen.ne]; simp [st₃, st₂, st₁, show r_eLen ≠ r_base + 8 by omega,
                show r_eLen ≠ r_base + 7 by omega, show r_eLen ≠ r_base + 6 by omega, hre_st],
           by simp only [State.setReg_regs, ite_eq_right (show r_base ≠ r_base + 3 by omega), hrpos₄],
           by simp only [State.setReg_regs, ite_eq_right (show r_base + 1 ≠ r_base + 3 by omega)]
              rw [hreg₄ (r_base + 1) (by omega)]; simp [st₃, st₂, st₁, hru_st],
           by simp only [State.setReg_regs, ite_eq_right (show r_base + 2 ≠ r_base + 3 by omega)]
              rw [hreg₄ (r_base + 2) (by omega)]; simp [st₃, st₂, st₁, hrv_st],
           by simp,
           by simp only [State.setReg_regs, ite_eq_right (show r_base + 4 ≠ r_base + 3 by omega)]
              rw [hreg₄ (r_base + 4) (by omega)]; simp [st₃, st₂, st₁, hrx_st],
           by simp only [State.setReg_regs, ite_eq_right (show r_base + 5 ≠ r_base + 3 by omega)]
              rw [hreg₄ (r_base + 5) (by omega)]; simp [st₃, st₂, st₁, hry_st],
           fun a ha => by simp only [State.setReg_arrs]; rw [harr₄ a ha]; simp [st₃, st₂, st₁, harr_st a ha],
           fun reg hlt => by
             simp only [State.setReg_regs, ite_eq_right (show reg ≠ r_base + 3 by omega)]
             rw [hreg₄ reg hlt.ne]
             simp [st₃, st₂, st₁, show reg ≠ r_base + 8 by omega,
               show reg ≠ r_base + 7 by omega, show reg ≠ r_base + 6 by omega, hreg_st reg hlt]⟩,
          by rw [hreg₄ (r_base + 3) (by omega)]; simp [st₃, st₂, st₁, hridx_st]⟩
      · have hcond :
            (Expr.op .mul
              (.op .eq (.reg (r_base + 6)) (.reg (r_base + 4)))
              (.op .eq (.reg (r_base + 7)) (.reg (r_base + 5)))).eval w st₂ = some 0 := by
          by_cases h1 : e.1 = x <;> by_cases h2 : e.2.1 = y
          · exact False.elim (hxy ⟨h1, h2⟩)
          · simp [st₂, st₁, Expr.eval, BinOp.eval, BinOp.raw, checkWord,
              hrx_st, hry_st, he2_w, hx_w, hy_w, h1, h2, h0_w, h1_w]
          · simp [st₂, st₁, Expr.eval, BinOp.eval, BinOp.raw, checkWord,
              hrx_st, hry_st, he1_w, hx_w, hy_w, h1, h2, h0_w, h1_w]
          · simp [st₂, st₁, Expr.eval, BinOp.eval, BinOp.raw, checkWord,
              hrx_st, hry_st, he1_w, he2_w, hx_w, hy_w, h1, h2, h0_w]
        have hcur_succ : pfx ++ fTau0RowPrefix r x y (k + 1) = cur := by
          rw [fTau0RowPrefix_succ, List.getD_eq_getElem _ _ hk]
          change pfx ++ (fTau0RowPrefix r x y k ++
            (if e.1 = x ∧ e.2.1 = y then [r.tauList.getD k 0] else [])) = cur
          rw [ite_eq_right hxy, List.append_nil]
        refine ⟨st₂, 5 + (7 + (7 + 1)),
          .seq hex₁ (.seq hex₂ (.if_false hcond (.skip st₂))),
          by dsimp only; omega,
          ⟨by simp [st₂, st₁, hrE_st],
           by simp [st₂, st₁, hrTau_st],
           by rw [hcur_succ]; exact hbuf_st,
           by simp [st₂, st₁, show r_eLen ≠ r_base + 3 by omega,
             show r_eLen ≠ r_base + 7 by omega, show r_eLen ≠ r_base + 6 by omega, hre_st],
           by rw [hcur_succ]; simp [st₂, st₁, hrpos_st, cur],
           by simp [st₂, st₁, hru_st],
           by simp [st₂, st₁, hrv_st],
           by simp,
           by simp [st₂, st₁, hrx_st],
           by simp [st₂, st₁, hry_st],
           fun a ha => by simp [st₂, st₁, harr_st a ha],
           fun reg hlt => by
             simp [st₂, st₁, show reg ≠ r_base + 3 by omega,
               show reg ≠ r_base + 7 by omega, show reg ≠ r_base + 6 by omega, hreg_st reg hlt]⟩,
          by simp [st₂, st₁, hridx_st]⟩
  rcases hLoop s hInv₀ with
    ⟨s', t, hex, ht, _, _, hbuf', _, hrpos', hru', hrv', _, hrx', _, harr', hreg'⟩
  exact ⟨s', t, hex, by dsimp only [m_r] at ht; omega,
    hbuf', hrpos', hru', hrv', hrx', harr', hreg'⟩

/-- Middle loop body for `v = s.regs (r_base + 2) < n_A` at fixed `u = s.regs (r_base + 1)`. -/
def buildFTau0ColBody (a_tildeV a_rE a_rTau a_multDel a_buf : Arr)
    (r_nA r_eLen r_base : Reg) : Cmd :=
  .seq (.assign (r_base + 6)
      (.op .add (.op .mul (.reg (r_base + 1)) (.reg r_nA)) (.reg (r_base + 2))))
    (.seq (.assign (r_base + 7) (.read a_multDel (.reg (r_base + 6))))
      (.ite (.op .lt (.const 0) (.reg (r_base + 7)))
        (.seq (.assign (r_base + 5) (.read a_tildeV (.reg (r_base + 2))))
          (.seq (.assign (r_base + 3) (.const 0))
            (forUp (r_base + 3) (.reg r_eLen)
              (scanFTau0EdgeBody a_rE a_rTau a_buf r_base))))
        .skip))

theorem buildFTau0ColLoop_exec {w : ℕ}
    (vList : List ℕ) (hv_nd : vList.Nodup) (hv_w : ∀ x ∈ vList, x < 2 ^ w)
    (r : Case3MemberRecord) (hr_nd : r.eList.Nodup)
    (htau_len : r.tauList.length = r.eList.length)
    (he_ends : ∀ e ∈ r.eList, e.1 ∈ vList ∧ e.2.1 ∈ vList)
    (he_w : ∀ x ∈ encEdgeTriples r.eList, x < 2 ^ w)
    (htau_w : ∀ x ∈ r.tauList, x < 2 ^ w)
    (u : Fin vList.length)
    (a_tildeV a_rE a_rTau a_multDel a_buf r_nA r_eLen r_base : ℕ)
    (hne_vb : a_tildeV ≠ a_buf) (hne_eb : a_rE ≠ a_buf)
    (hne_tb : a_rTau ≠ a_buf) (hne_mb : a_multDel ≠ a_buf)
    (hr_nA : r_nA < r_base) (hr_eLen : r_eLen < r_base)
    (hw3 : 3 < 2 ^ w) (hnA_sq_w : vList.length * vList.length < 2 ^ w)
    (he3_w : 3 * r.eList.length < 2 ^ w)
    {s : State}
    (hvList : s.arrs a_tildeV = vList)
    (hrE : s.arrs a_rE = encEdgeTriples r.eList)
    (hrTau : s.arrs a_rTau = r.tauList)
    (hmult : (s.arrs a_multDel).length = vList.length * vList.length ∧
      ∀ x y : Fin vList.length,
        (s.arrs a_multDel).getD (x.1 * vList.length + y.1) 0 =
          (tildeAMultiDigraph vList r.eList).edgeMult x y)
    (hbuf : IsPrefixBuffer a_buf (fTau0OuterPrefix vList r u.1)
      (2 * r.eList.length - (fTau0OuterPrefix vList r u.1).length) s)
    (hrnA : s.regs r_nA = vList.length)
    (hreLen : s.regs r_eLen = r.eList.length)
    (hrpos : s.regs r_base = (fTau0OuterPrefix vList r u.1).length)
    (hru : s.regs (r_base + 1) = u.1)
    (hrv : s.regs (r_base + 2) = 0)
    (hrx : s.regs (r_base + 4) = vList[u.1]'u.2) :
    ∃ s' t,
      Exec w
        (forUp (r_base + 2) (.reg r_nA)
          (buildFTau0ColBody a_tildeV a_rE a_rTau a_multDel a_buf r_nA r_eLen r_base))
        s s' t ∧
      t ≤ 3 + 20 * vList.length +
        (36 * r.eList.length + 9) *
          ∑ v : Fin vList.length, (tildeAMultiDigraph vList r.eList).edgeMult u v ∧
      IsPrefixBuffer a_buf (fTau0OuterPrefix vList r (u.1 + 1))
        (2 * r.eList.length - (fTau0OuterPrefix vList r (u.1 + 1)).length) s' ∧
      s'.regs r_base = (fTau0OuterPrefix vList r (u.1 + 1)).length ∧
      s'.regs (r_base + 1) = u.1 ∧
      (∀ a : ℕ, a ≠ a_buf → s'.arrs a = s.arrs a) ∧
      (∀ reg < r_base, s'.regs reg = s.regs reg) := by
  let n_A := vList.length
  let G_del := tildeAMultiDigraph vList r.eList
  have h0_w : 0 < 2 ^ w := by omega
  have h1_w : 1 < 2 ^ w := by omega
  have hnA_w : n_A < 2 ^ w := by nlinarith [u.2, hnA_sq_w]
  have hu_w : u.1 < 2 ^ w := by omega
  have hx_w : vList[u.1]'u.2 < 2 ^ w := hv_w _ (List.getElem_mem u.2)
  let InnerInv (v : ℕ) (st : State) : Prop :=
    let cur := fTau0OuterPrefix vList r u.1 ++ fTau0ColPrefix vList r u v
    st.arrs a_tildeV = vList ∧
    st.arrs a_rE = encEdgeTriples r.eList ∧
    st.arrs a_rTau = r.tauList ∧
    ((st.arrs a_multDel).length = n_A * n_A ∧
      ∀ x y : Fin n_A,
        (st.arrs a_multDel).getD (x.1 * n_A + y.1) 0 = G_del.edgeMult x y) ∧
    IsPrefixBuffer a_buf cur (2 * r.eList.length - cur.length) st ∧
    st.regs r_nA = n_A ∧
    st.regs r_eLen = r.eList.length ∧
    st.regs r_base = cur.length ∧
    st.regs (r_base + 1) = u.1 ∧
    st.regs (r_base + 2) = v ∧
    st.regs (r_base + 4) = vList[u.1]'u.2 ∧
    (∀ a : ℕ, a ≠ a_buf → st.arrs a = s.arrs a) ∧
    (∀ reg < r_base, st.regs reg = s.regs reg)
  have hInner₀ : InnerInv 0 s :=
    ⟨hvList, hrE, hrTau, hmult, by simpa using hbuf, hrnA, hreLen,
      by simpa using hrpos, hru, hrv, hrx, fun _ _ => rfl, fun _ _ => rfl⟩
  let colCost (v : ℕ) : ℕ :=
    13 + (36 * r.eList.length + 9) * (if hv : v < n_A then G_del.edgeMult u ⟨v, hv⟩ else 0)
  have hLoop :
      ⦃InnerInv 0⦄[w]
        forUp (r_base + 2) (.reg r_nA)
          (buildFTau0ColBody a_tildeV a_rE a_rTau a_multDel a_buf r_nA r_eLen r_base)
      ⦃InnerInv n_A⦄ ≤ fun _ => 3 + ∑ v ∈ Finset.range n_A, (7 + colCost v) := by
    apply Triple.forUp_sum InnerInv n_A colCost h1_w hnA_w
    · intro v _ st ⟨_, _, _, _, _, hrnA_st, _, _, _, hrv_st, _, _, _⟩
      exact ⟨hrv_st, by simp [Expr.eval, checkWord, hrnA_st, hnA_w]⟩
    · intro v hv st ⟨hvL_st, hrE_st, hrTau_st, ⟨hlen_m, hget_m⟩, hbuf_st,
        hrnA_st, hre_st, hrpos_st, hru_st, hrv_st, hrx_st, harr_st, hreg_st⟩
      let cur := fTau0OuterPrefix vList r u.1 ++ fTau0ColPrefix vList r u v
      have hv_lt_w : v < 2 ^ w := by omega
      have hcell_lt : u.1 * n_A + v < n_A * n_A := by nlinarith [u.2, hv]
      have hcell_w : u.1 * n_A + v < 2 ^ w := lt_trans hcell_lt hnA_sq_w
      have hunA_w : u.1 * n_A < 2 ^ w := by omega
      let mult := G_del.edgeMult u ⟨v, hv⟩
      have hmult_le : mult ≤ r.eList.length := by
        dsimp [mult, G_del, tildeAMultiDigraph, edgesBetween]
        exact List.length_filter_le _ _
      have hmult_w : mult < 2 ^ w := by omega
      let st₁ := st.setReg (r_base + 6) (u.1 * n_A + v)
      have hex₁ : Exec w (.assign (r_base + 6)
          (.op .add (.op .mul (.reg (r_base + 1)) (.reg r_nA)) (.reg (r_base + 2)))) st st₁ 6 :=
        .assign (by simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord,
          hru_st, hrnA_st, hrv_st, hu_w, hnA_w, hunA_w, hv_lt_w, hcell_w])
      have hcell_len : u.1 * n_A + v < (st.arrs a_multDel).length := by rw [hlen_m]; exact hcell_lt
      have hget_cell : (st.arrs a_multDel)[u.1 * n_A + v]'hcell_len = mult := by
        rw [← List.getD_eq_getElem _ 0 hcell_len]
        exact hget_m u ⟨v, hv⟩
      let st₂ := st₁.setReg (r_base + 7) mult
      have hex₂ : Exec w (.assign (r_base + 7) (.read a_multDel (.reg (r_base + 6)))) st₁ st₂ 3 :=
        .assign (by simp [st₁, Expr.eval, checkWord, hcell_w, hcell_len, hget_cell, hmult_w])
      have hcol_eq : colCost v = 13 + (36 * r.eList.length + 9) * mult := by
        simp [colCost, hv, mult]
      by_cases hpos : 0 < mult
      · have hcond : (Expr.op .lt (.const 0) (.reg (r_base + 7))).eval w st₂ = some 1 := by
          simp [st₂, st₁, Expr.eval, BinOp.eval, BinOp.raw, checkWord, h0_w, hmult_w, hpos, h1_w]
        let y := vList[v]'hv
        have hy_w : y < 2 ^ w := hv_w y (List.getElem_mem hv)
        have hv_len : v < (st.arrs a_tildeV).length := by rw [hvL_st]; exact hv
        have hget_y : (st.arrs a_tildeV)[v]'hv_len = y := by simp [hvL_st, y]
        let st₃ := st₂.setReg (r_base + 5) y
        have hex₃ : Exec w (.assign (r_base + 5) (.read a_tildeV (.reg (r_base + 2)))) st₂ st₃ 3 :=
          .assign (by simp [st₂, st₁, Expr.eval, checkWord, hrv_st, hv_lt_w, hv_len, hget_y, hy_w])
        let st₄ := st₃.setReg (r_base + 3) 0
        have hex₄ : Exec w (.assign (r_base + 3) (.const 0)) st₃ st₄ 2 :=
          .assign (by simp [Expr.eval, checkWord, h0_w])
        have hcur_le : cur.length ≤ r.eList.length :=
          length_fTau0OuterPrefix_add_colPrefix_le vList r hv_nd hr_nd he_ends u v (by omega)
        have hbuf₄ : IsPrefixBuffer a_buf cur (2 * r.eList.length - cur.length) st₄ := hbuf_st
        rcases scanFTau0EdgeLoop_exec r htau_len he_w htau_w (vList[u.1]'u.2) y hx_w hy_w
            a_rE a_rTau a_buf r_eLen r_base hne_eb hne_tb hr_eLen hw3 he3_w cur hcur_le
            (by simp [st₄, st₃, st₂, st₁, hrE_st])
            (by simp [st₄, st₃, st₂, st₁, hrTau_st])
            hbuf₄
            (by simp [st₄, st₃, st₂, st₁, show r_eLen ≠ r_base + 3 by omega,
              show r_eLen ≠ r_base + 5 by omega, show r_eLen ≠ r_base + 7 by omega,
              show r_eLen ≠ r_base + 6 by omega, hre_st])
            (by simp [st₄, st₃, st₂, st₁, hrpos_st, cur])
            (by simp [st₄])
            (by simp [st₄, st₃, st₂, st₁, hrx_st])
            (by simp [st₄, st₃]) with
          ⟨st₅, t₅, hex₅, ht₅, hbuf₅, hrpos₅, hru₅, hrv₅, hrx₅, harr₅, hreg₅⟩
        have hcur_succ :
            fTau0OuterPrefix vList r u.1 ++ fTau0ColPrefix vList r u (v + 1) =
              cur ++ fTau0RowList r (vList[u.1]'u.2) y := by
          rw [fTau0ColPrefix_succ vList r u hv, ← List.append_assoc]
        rw [← hcur_succ] at hbuf₅ hrpos₅
        have hmul_ge : 36 * r.eList.length + 9 ≤ (36 * r.eList.length + 9) * mult :=
          Nat.le_mul_of_pos_right _ hpos
        refine ⟨st₅, 6 + (3 + (3 + (3 + (2 + t₅)))),
          .seq hex₁ (.seq hex₂ (.if_true (v := 1) hcond (by decide) (.seq hex₃ (.seq hex₄ hex₅)))),
          by dsimp only; omega,
          ⟨by simp only [State.setReg_arrs]; rw [harr₅ a_tildeV hne_vb]; simp [st₄, st₃, st₂, st₁, hvL_st],
           by simp only [State.setReg_arrs]; rw [harr₅ a_rE hne_eb]; simp [st₄, st₃, st₂, st₁, hrE_st],
           by simp only [State.setReg_arrs]; rw [harr₅ a_rTau hne_tb]; simp [st₄, st₃, st₂, st₁, hrTau_st],
           ⟨by simp only [State.setReg_arrs]; rw [harr₅ a_multDel hne_mb]; simp [st₄, st₃, st₂, st₁, hlen_m],
            fun x' y' => by
              simp only [State.setReg_arrs, harr₅ a_multDel hne_mb]
              simpa [st₄, st₃, st₂, st₁] using hget_m x' y'⟩,
           hbuf₅,
           by simp only [State.setReg_regs, ite_eq_right (show ¬(r_nA = r_base + 2) by omega)]
              rw [hreg₅ r_nA hr_nA]; simp [st₄, st₃, st₂, st₁, show r_nA ≠ r_base + 3 by omega,
                show r_nA ≠ r_base + 5 by omega, show r_nA ≠ r_base + 7 by omega,
                show r_nA ≠ r_base + 6 by omega, hrnA_st],
           by simp only [State.setReg_regs, ite_eq_right (show ¬(r_eLen = r_base + 2) by omega)]
              rw [hreg₅ r_eLen hr_eLen]; simp [st₄, st₃, st₂, st₁, show r_eLen ≠ r_base + 3 by omega,
                show r_eLen ≠ r_base + 5 by omega, show r_eLen ≠ r_base + 7 by omega,
                show r_eLen ≠ r_base + 6 by omega, hre_st],
           by simp only [State.setReg_regs, ite_eq_right (show ¬(r_base = r_base + 2) by omega), hrpos₅],
           by simp only [State.setReg_regs, ite_eq_right (show ¬(r_base + 1 = r_base + 2) by omega)]
              rw [hru₅]; simp [st₄, st₃, st₂, st₁, hru_st],
           by simp,
           by simp only [State.setReg_regs, ite_eq_right (show ¬(r_base + 4 = r_base + 2) by omega), hrx₅],
           fun a ha => by simp only [State.setReg_arrs]; rw [harr₅ a ha]; simp [st₄, st₃, st₂, st₁, harr_st a ha],
           fun reg hlt => by
             simp only [State.setReg_regs, ite_eq_right (show ¬(reg = r_base + 2) by omega)]
             rw [hreg₅ reg hlt]
             simp [st₄, st₃, st₂, st₁, show reg ≠ r_base + 3 by omega,
               show reg ≠ r_base + 5 by omega, show reg ≠ r_base + 7 by omega,
               show reg ≠ r_base + 6 by omega, hreg_st reg hlt]⟩,
          by rw [hrv₅]; simp [st₄, st₃, st₂, st₁, hrv_st]⟩
      · have hm0 : mult = 0 := by omega
        have hcond : (Expr.op .lt (.const 0) (.reg (r_base + 7))).eval w st₂ = some 0 := by
          simp [st₂, st₁, Expr.eval, BinOp.eval, BinOp.raw, checkWord, h0_w, hm0]
        have hrow_nil : fTau0RowList r (vList[u.1]'u.2) (vList[v]'hv) = [] :=
          fTau0RowList_eq_nil_of_edgeMult_eq_zero vList r hr_nd u ⟨v, hv⟩ hm0
        have hcur_succ :
            fTau0OuterPrefix vList r u.1 ++ fTau0ColPrefix vList r u (v + 1) = cur := by
          rw [fTau0ColPrefix_succ vList r u hv, hrow_nil, List.append_nil]
        refine ⟨st₂, 6 + (3 + (3 + 1)),
          .seq hex₁ (.seq hex₂ (.if_false hcond (.skip st₂))),
          by dsimp only; omega,
          ⟨by simp [st₂, st₁, hvL_st],
           by simp [st₂, st₁, hrE_st],
           by simp [st₂, st₁, hrTau_st],
           ⟨by simp [st₂, st₁, hlen_m], fun x' y' => by simpa [st₂, st₁] using hget_m x' y'⟩,
           by rw [hcur_succ]; exact hbuf_st,
           by simp [st₂, st₁, show r_nA ≠ r_base + 2 by omega,
             show r_nA ≠ r_base + 7 by omega, show r_nA ≠ r_base + 6 by omega, hrnA_st],
           by simp [st₂, st₁, show r_eLen ≠ r_base + 2 by omega,
             show r_eLen ≠ r_base + 7 by omega, show r_eLen ≠ r_base + 6 by omega, hre_st],
           by rw [hcur_succ]; simp [st₂, st₁, hrpos_st, cur],
           by simp [st₂, st₁, hru_st],
           by simp,
           by simp [st₂, st₁, hrx_st],
           fun a ha => by simp [st₂, st₁, harr_st a ha],
           fun reg hlt => by
             simp [st₂, st₁, show reg ≠ r_base + 2 by omega,
               show reg ≠ r_base + 7 by omega, show reg ≠ r_base + 6 by omega, hreg_st reg hlt]⟩,
          by simp [st₂, st₁, hrv_st]⟩
  rcases hLoop s hInner₀ with
    ⟨s', t, hex, ht, _, _, _, _, hbuf', _, _, hrpos', hru', _, _, harr', hreg'⟩
  dsimp only at ht
  have hsum_col :
      ∑ v ∈ Finset.range n_A, (7 + colCost v) =
        20 * n_A + (36 * r.eList.length + 9) * ∑ v : Fin n_A, G_del.edgeMult u v := by
    have hcongr :
        ∑ v ∈ Finset.range n_A, (7 + colCost v) =
          ∑ v : Fin n_A, (20 + (36 * r.eList.length + 9) * G_del.edgeMult u v) := by
      rw [Finset.sum_fin_eq_sum_range]
      refine Finset.sum_congr rfl fun v hv => ?_
      rw [Finset.mem_range] at hv
      simp [colCost, hv]; omega
    rw [hcongr, Finset.sum_add_distrib, ← Finset.mul_sum]
    simp [Nat.mul_comm]
  rw [hsum_col] at ht
  rw [← fTau0OuterPrefix_succ vList r u.2] at hbuf' hrpos'
  exact ⟨s', t, hex, by dsimp only [n_A, G_del] at ht; omega, hbuf', hrpos', hru', harr', hreg'⟩

/-- Outer loop body for `u = s.regs (r_base + 1) < n_A`. -/
def buildFTau0OuterBody (a_tildeV a_rE a_rTau a_multDel a_buf : Arr)
    (r_nA r_eLen r_base : Reg) : Cmd :=
  .seq (.assign (r_base + 4) (.read a_tildeV (.reg (r_base + 1))))
    (.seq (.assign (r_base + 2) (.const 0))
      (forUp (r_base + 2) (.reg r_nA)
        (buildFTau0ColBody a_tildeV a_rE a_rTau a_multDel a_buf r_nA r_eLen r_base)))

/-- Complete Word RAM program building `a_ftau0 = List.ofFn (fun i => memberFTau0 vList r i.1)`
for `G_del = tildeAMultiDigraph vList r.eList` from `a_tildeV = vList`, `a_vIdx`,
`a_rE = encEdgeTriples r.eList`, and `a_rTau = r.tauList`. -/
def buildFTau0Prog (a_tildeV a_vIdx a_rE a_rTau a_multDel a_buf a_ftau0 : Arr)
    (r_nA r_eLen r_base : Reg) : Cmd :=
  .seq (buildEdgeMultMatProg a_vIdx a_rE a_multDel r_nA r_eLen r_base)
    (.seq (initPrefixBufferProg a_buf (.op .mul (.const 2) (.reg r_eLen)) r_base)
      (.seq (.assign (r_base + 1) (.const 0))
        (.seq (forUp (r_base + 1) (.reg r_nA)
            (buildFTau0OuterBody a_tildeV a_rE a_rTau a_multDel a_buf r_nA r_eLen r_base))
          (copyBufPrefixProg a_buf a_ftau0 r_base (r_base + 1)))))

theorem buildFTau0Prog_exec {w n : ℕ}
    (vList : List ℕ) (hv_nd : vList.Nodup) (hv_lt : ∀ v ∈ vList, v < n)
    (r : Case3MemberRecord) (hr_nd : r.eList.Nodup)
    (htau_len : r.tauList.length = r.eList.length)
    (he_ends : ∀ e ∈ r.eList, e.1 ∈ vList ∧ e.2.1 ∈ vList)
    (he_w : ∀ x ∈ encEdgeTriples r.eList, x < 2 ^ w)
    (htau_w : ∀ x ∈ r.tauList, x < 2 ^ w)
    (a_tildeV a_vIdx a_rE a_rTau a_multDel a_buf a_ftau0 r_nA r_eLen r_base : ℕ)
    (hne_vm : a_tildeV ≠ a_multDel) (hne_vb : a_tildeV ≠ a_buf)
    (hne_im : a_vIdx ≠ a_multDel)
    (hne_em : a_rE ≠ a_multDel) (hne_eb : a_rE ≠ a_buf)
    (hne_tm : a_rTau ≠ a_multDel) (hne_tb : a_rTau ≠ a_buf)
    (hne_mb : a_multDel ≠ a_buf) (hne_bf : a_buf ≠ a_ftau0)
    (hr_nA : r_nA < r_base) (hr_eLen : r_eLen < r_base)
    (hw3 : 3 < 2 ^ w) (hn_w : n < 2 ^ w)
    (hnA_sq_w : vList.length * vList.length < 2 ^ w)
    (he3_w : 3 * r.eList.length + 1 < 2 ^ w)
    {s : State}
    (hvList : s.arrs a_tildeV = vList)
    (hvIdx_len : (s.arrs a_vIdx).length = n)
    (hvIdx_get : ∀ i : Fin vList.length, (s.arrs a_vIdx).getD (vList[i.1]'i.2) 0 = i.1)
    (hrE : s.arrs a_rE = encEdgeTriples r.eList)
    (hrTau : s.arrs a_rTau = r.tauList)
    (hrnA : s.regs r_nA = vList.length)
    (hreLen : s.regs r_eLen = r.eList.length) :
    ∃ s' t,
      Exec w (buildFTau0Prog a_tildeV a_vIdx a_rE a_rTau a_multDel a_buf a_ftau0
        r_nA r_eLen r_base) s s' t ∧
      t ≤ 42 * (vList.length * vList.length) + 15 * vList.length +
        36 * (r.eList.length * r.eList.length) + 66 * r.eList.length + 34 ∧
      s'.arrs a_ftau0 =
        List.ofFn (fun i : Fin (tildeAMultiDigraph vList r.eList).toComputeDigraph.numEdges =>
          memberFTau0 vList r i.1) ∧
      (∀ a : ℕ, a ≠ a_multDel → a ≠ a_buf → a ≠ a_ftau0 → s'.arrs a = s.arrs a) ∧
      (∀ reg < r_base, s'.regs reg = s.regs reg) := by
  let n_A := vList.length
  let G_del := tildeAMultiDigraph vList r.eList
  have h0_w : 0 < 2 ^ w := by omega
  have h1_w : 1 < 2 ^ w := by omega
  have h2_w : 2 < 2 ^ w := by omega
  have hnA_w : n_A < 2 ^ w := by
    rcases Nat.eq_zero_or_pos n_A with h0 | hpos
    · omega
    · nlinarith
  have hv_w : ∀ x ∈ vList, x < 2 ^ w := fun x hx => lt_trans (hv_lt x hx) hn_w
  -- 1. buildEdgeMultMatProg
  rcases buildEdgeMultMatProg_exec vList r.eList hv_nd hv_lt he_ends
      a_vIdx a_rE a_multDel r_nA r_eLen r_base hne_im hne_em hr_nA hr_eLen
      hw3 hn_w hnA_sq_w he3_w hvIdx_len hvIdx_get hrE hrnA hreLen with
    ⟨s₁, t₁, hex₁, ht₁, hmult_len₁, hmult_get₁, harr₁, hreg₁⟩
  -- 2. initPrefixBufferProg a_buf (2 * r_eLen) r_base
  have hreLen₁ : s₁.regs r_eLen = r.eList.length := by rw [hreg₁ r_eLen hr_eLen, hreLen]
  have hrnA₁ : s₁.regs r_nA = n_A := by rw [hreg₁ r_nA hr_nA, hrnA]
  have h2e_w : 2 * r.eList.length < 2 ^ w := by omega
  have he_w_len : r.eList.length < 2 ^ w := by omega
  rcases initPrefixBufferProg_exec (cap := 2 * r.eList.length) (s := s₁) a_buf
      (.op .mul (.const 2) (.reg r_eLen)) r_base h1_w
      (by simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hreLen₁, h2_w, he_w_len, h2e_w]) with
    ⟨s₂, t₂, hex₂, ht₂, hbuf₂, hrpos₂, harr₂, hreg₂⟩
  -- 3. r_base + 1 := 0
  let s₃ := s₂.setReg (r_base + 1) 0
  have hex₃ : Exec w (.assign (r_base + 1) (.const 0)) s₂ s₃ 2 :=
    .assign (by simp [Expr.eval, checkWord, h0_w])
  -- 4. Outer loop over u = 0 .. n_A - 1
  let OuterInv (u : ℕ) (st : State) : Prop :=
    let cur := fTau0OuterPrefix vList r u
    st.arrs a_tildeV = vList ∧
    st.arrs a_rE = encEdgeTriples r.eList ∧
    st.arrs a_rTau = r.tauList ∧
    ((st.arrs a_multDel).length = n_A * n_A ∧
      ∀ x y : Fin n_A,
        (st.arrs a_multDel).getD (x.1 * n_A + y.1) 0 = G_del.edgeMult x y) ∧
    IsPrefixBuffer a_buf cur (2 * r.eList.length - cur.length) st ∧
    st.regs r_nA = n_A ∧
    st.regs r_eLen = r.eList.length ∧
    st.regs r_base = cur.length ∧
    st.regs (r_base + 1) = u ∧
    (∀ a : ℕ, a ≠ a_multDel → a ≠ a_buf → st.arrs a = s.arrs a) ∧
    (∀ reg < r_base, st.regs reg = s.regs reg)
  have hOuter₀ : OuterInv 0 s₃ := by
    refine ⟨by simp [s₃, harr₂ a_tildeV hne_vb, harr₁ a_tildeV hne_vm, hvList],
      by simp [s₃, harr₂ a_rE hne_eb, harr₁ a_rE hne_em, hrE],
      by simp [s₃, harr₂ a_rTau hne_tb, harr₁ a_rTau hne_tm, hrTau],
      ⟨by simp [s₃, harr₂ a_multDel hne_mb, hmult_len₁, n_A],
       fun x y => by simpa [s₃, harr₂ a_multDel hne_mb, n_A] using hmult_get₁ x y⟩,
      by simpa [IsPrefixBuffer, s₃] using hbuf₂,
      by simp [s₃, show r_nA ≠ r_base + 1 by omega, hreg₂ r_nA hr_nA.ne, hrnA₁],
      by simp [s₃, show r_eLen ≠ r_base + 1 by omega, hreg₂ r_eLen hr_eLen.ne, hreLen₁],
      by simp [s₃, hrpos₂],
      by simp [s₃],
      fun a ha₁ ha₂ => by simp [s₃, harr₂ a ha₂, harr₁ a ha₁],
      fun reg hlt => by
        simp [s₃, show reg ≠ r_base + 1 by omega, hreg₂ reg hlt.ne, hreg₁ reg hlt]⟩
  let rowCost (u : ℕ) : ℕ :=
    8 + 20 * n_A +
      (36 * r.eList.length + 9) *
        (if hu : u < n_A then ∑ v : Fin n_A, G_del.edgeMult ⟨u, hu⟩ v else 0)
  have hOuterLoop :
      ⦃OuterInv 0⦄[w]
        forUp (r_base + 1) (.reg r_nA)
          (buildFTau0OuterBody a_tildeV a_rE a_rTau a_multDel a_buf r_nA r_eLen r_base)
      ⦃OuterInv n_A⦄ ≤ fun _ => 3 + ∑ u ∈ Finset.range n_A, (7 + rowCost u) := by
    apply Triple.forUp_sum OuterInv n_A rowCost h1_w hnA_w
    · intro u _ st ⟨_, _, _, _, _, hrnA_st, _, _, hru_st, _, _⟩
      exact ⟨hru_st, by simp [Expr.eval, checkWord, hrnA_st, hnA_w]⟩
    · intro u hu st ⟨hvL_st, hrE_st, hrTau_st, hmult_st, hbuf_st,
        hrnA_st, hre_st, hrpos_st, hru_st, harr_st, hreg_st⟩
      have hu_w : u < 2 ^ w := by omega
      let x := vList[u]'hu
      have hx_w : x < 2 ^ w := hv_w x (List.getElem_mem hu)
      have hu_len : u < (st.arrs a_tildeV).length := by rw [hvL_st]; exact hu
      have hget_x : (st.arrs a_tildeV)[u]'hu_len = x := by simp [hvL_st, x]
      let st₁ := st.setReg (r_base + 4) x
      have hex_x : Exec w (.assign (r_base + 4) (.read a_tildeV (.reg (r_base + 1)))) st st₁ 3 :=
        .assign (by simp [Expr.eval, checkWord, hru_st, hu_w, hu_len, hget_x, hx_w])
      let st₂ := st₁.setReg (r_base + 2) 0
      have hex_v0 : Exec w (.assign (r_base + 2) (.const 0)) st₁ st₂ 2 :=
        .assign (by simp [Expr.eval, checkWord, h0_w])
      rcases buildFTau0ColLoop_exec (s := st₂) vList hv_nd hv_w r hr_nd htau_len he_ends he_w htau_w ⟨u, hu⟩
          a_tildeV a_rE a_rTau a_multDel a_buf r_nA r_eLen r_base
          hne_vb hne_eb hne_tb hne_mb hr_nA hr_eLen hw3 hnA_sq_w (by omega)
          hvL_st hrE_st hrTau_st hmult_st hbuf_st
          (by simp [st₂, st₁, show r_nA ≠ r_base + 2 by omega, show r_nA ≠ r_base + 4 by omega, hrnA_st, n_A])
          (by simp [st₂, st₁, show r_eLen ≠ r_base + 2 by omega, show r_eLen ≠ r_base + 4 by omega, hre_st])
          (by simp [st₂, st₁, hrpos_st])
          (by simp [st₂, st₁, hru_st])
          (by simp [st₂])
          (by simp [st₂, st₁, x]) with
        ⟨st₃, t₃, hex₃, ht₃, hbuf₃, hrpos₃, hru₃, harr₃, hreg₃⟩
      have hrow_eq :
          rowCost u = 8 + 20 * n_A + (36 * r.eList.length + 9) * ∑ v : Fin n_A, G_del.edgeMult ⟨u, hu⟩ v := by
        simp [rowCost, hu]
      refine ⟨st₃, 3 + (2 + t₃), .seq hex_x (.seq hex_v0 hex₃),
        by dsimp only [n_A, G_del] at hrow_eq ⊢; omega,
        ⟨by simp only [State.setReg_arrs]; rw [harr₃ a_tildeV hne_vb]; exact hvL_st,
         by simp only [State.setReg_arrs]; rw [harr₃ a_rE hne_eb]; exact hrE_st,
         by simp only [State.setReg_arrs]; rw [harr₃ a_rTau hne_tb]; exact hrTau_st,
         ⟨by simp only [State.setReg_arrs]; rw [harr₃ a_multDel hne_mb]; exact hmult_st.1,
          fun x' y' => by
            simp only [State.setReg_arrs, harr₃ a_multDel hne_mb]
            exact hmult_st.2 x' y'⟩,
         hbuf₃,
         by simp only [State.setReg_regs, ite_eq_right (show ¬(r_nA = r_base + 1) by omega)]
            rw [hreg₃ r_nA hr_nA]; simp [st₂, st₁, show r_nA ≠ r_base + 2 by omega,
              show r_nA ≠ r_base + 4 by omega, hrnA_st],
         by simp only [State.setReg_regs, ite_eq_right (show ¬(r_eLen = r_base + 1) by omega)]
            rw [hreg₃ r_eLen hr_eLen]; simp [st₂, st₁, show r_eLen ≠ r_base + 2 by omega,
              show r_eLen ≠ r_base + 4 by omega, hre_st],
         by simp only [State.setReg_regs, ite_eq_right (show ¬(r_base = r_base + 1) by omega), hrpos₃],
         by simp,
         fun a ha₁ ha₂ => by
           simp only [State.setReg_arrs]; rw [harr₃ a ha₂]; exact harr_st a ha₁ ha₂,
         fun reg hlt => by
           simp only [State.setReg_regs, ite_eq_right (show ¬(reg = r_base + 1) by omega)]
           rw [hreg₃ reg hlt]
           simp [st₂, st₁, show reg ≠ r_base + 2 by omega,
             show reg ≠ r_base + 4 by omega, hreg_st reg hlt]⟩,
        hru₃⟩
  rcases hOuterLoop s₃ hOuter₀ with
    ⟨s₄, t₄, hex₄, ht₄, _, _, _, _, hbuf₄, _, _, hrpos₄, _, harr₄, hreg₄⟩
  dsimp only at ht₄
  have hnum_del : G_del.toComputeDigraph.numEdges = r.eList.length :=
    (tildeADelEdgeTriple_mem_and_bijOn vList r.eList hv_nd hr_nd he_ends).1
  have hnum_sum : (∑ u : Fin n_A, ∑ v : Fin n_A, G_del.edgeMult u v) = r.eList.length := by
    have h1 : (∑ u : Fin n_A, ∑ v : Fin n_A, G_del.edgeMult u v) = G_del.numEdges := by
      unfold MultiDigraph.numEdges; rw [← Finset.sum_product']
    rw [h1, ← G_del.length_directedEdgesList]; exact hnum_del
  have hsum_row :
      ∑ u ∈ Finset.range n_A, (7 + rowCost u) =
        15 * n_A + 20 * (n_A * n_A) + (36 * r.eList.length + 9) * r.eList.length := by
    have hcongr :
        ∑ u ∈ Finset.range n_A, (7 + rowCost u) =
          ∑ u : Fin n_A, ((15 + 20 * n_A) + (36 * r.eList.length + 9) * ∑ v : Fin n_A, G_del.edgeMult u v) := by
      rw [Finset.sum_fin_eq_sum_range]
      refine Finset.sum_congr rfl fun u hu => ?_
      rw [Finset.mem_range] at hu; simp [rowCost, hu]; omega
    rw [hcongr, Finset.sum_add_distrib, ← Finset.mul_sum, hnum_sum]
    simp [n_A]; ring
  rw [hsum_row] at ht₄
  -- 5. copyBufPrefixProg a_buf a_ftau0 r_base (r_base + 1)
  have hfull_eq := fTau0OuterPrefix_full_eq_ofFn vList r hr_nd
  let ftauList :=
    List.ofFn (fun i : Fin G_del.toComputeDigraph.numEdges => memberFTau0 vList r i.1)
  have hftau_len : ftauList.length = r.eList.length := by rw [List.length_ofFn]; exact hnum_del
  have hftau_w : ∀ x ∈ ftauList, x < 2 ^ w := by
    intro x hx
    rcases List.mem_ofFn.mp hx with ⟨i, rfl⟩
    unfold memberFTau0
    rw [dite_eq_left i.2]
    set idx := r.eList.idxOf (tildeADelEdgeTriple vList r.eList i)
    by_cases hlt : idx < r.tauList.length
    · rw [List.getD_eq_getElem _ _ hlt]; exact htau_w _ (List.getElem_mem hlt)
    · rw [List.getD_eq_default _ _ (by omega)]; exact h0_w
  rw [hfull_eq] at hbuf₄ hrpos₄
  rcases copyBufPrefixProg_exec a_buf a_ftau0 r_base (r_base + 1)
      hne_bf (by omega) hftau_w h1_w (by rw [hftau_len]; omega) hbuf₄ hrpos₄ with
    ⟨s₅, t₅, hex₅, ht₅, hftau₅, harr₅, hreg₅⟩
  rw [hftau_len] at ht₅
  have hmul_r : (36 * r.eList.length + 9) * r.eList.length =
      36 * (r.eList.length * r.eList.length) + 9 * r.eList.length := by ring
  rw [hmul_r] at ht₄
  dsimp only [n_A] at ht₄
  refine ⟨s₅, t₁ + (t₂ + (2 + (t₄ + t₅))),
    .seq hex₁ (.seq hex₂ (.seq hex₃ (.seq hex₄ hex₅))),
    by simp [Expr.cost] at ht₂; omega, hftau₅,
    fun a ha₁ ha₂ ha₃ => by rw [harr₅ a ha₃, harr₄ a ha₁ ha₂],
    fun reg hlt => by rw [hreg₅ reg (by omega), hreg₄ reg hlt]⟩

end GraphMinor.Compute
