module

public import GraphMinor.Compute.Algorithm86Aux2

/-!
# Auxiliary Word RAM Subroutines for GM XIII Algorithm (8.6) (Part 3)

Type II Pass (`alg86TypeIIPassProg`) and Case (c) Pass (`alg86CaseCPassProg`).
-/

@[expose] public section

namespace GraphMinor.Compute

open SimpleGraph

/-- Loop body of `checkMinInKProg`: if `a_12[r_2] ≠ 0`, clears `r_23 := 0`. -/
def checkMinInKBody : Cmd :=
  .seq (.assign 3 (.read 12 (.reg 2)))
    (.ite (.op .eq (.reg 3) (.const 0))
      .skip
      (.assign 23 (.const 0)))

/-- Checks whether `r` (in `r_20`) is the minimum vertex in the bitset `S` stored in `a_12`.
Leaves `r_23 = 1` if `∀ u ∈ S, r.1 ≤ u.1` and `r_23 = 0` otherwise. -/
def checkMinInKProg : Cmd :=
  .seq (.assign 23 (.const 1))
    (.seq (.assign 2 (.const 0))
      (forUp 2 (.reg 20) checkMinInKBody))

private theorem checkMinInKLoop_exec {w n : ℕ} (S : Finset (Fin n)) (r : Fin n)
    (hw : 1 < 2 ^ w) (hn_w : n < 2 ^ w)
    (rem k : ℕ) (hrem : k + rem = r.1) {s : State}
    (hS : IsBitSet S 12 s)
    (hr20 : s.regs 20 = r.1)
    (hr2 : s.regs 2 = k)
    (hr23 : s.regs 23 = (if (∀ u : Fin n, u.1 < k → u ∉ S) then 1 else 0)) :
    ∃ s' t,
      Exec w (forUp 2 (.reg 20) checkMinInKBody) s s' t ∧
      t ≤ 15 * rem + 3 ∧
      s'.regs 23 = (if (∀ u : Fin n, u.1 < r.1 → u ∉ S) then 1 else 0) ∧
      s'.arrs = s.arrs ∧
      (∀ reg : Reg, reg ≠ 2 → reg ≠ 3 → reg ≠ 23 → s'.regs reg = s.regs reg) := by
  induction rem generalizing k s with
  | zero =>
    have hk_eq : k = r.1 := by omega
    subst hk_eq
    have h0_w : 0 < 2 ^ w := by omega
    have hr_w : r.1 < 2 ^ w := by omega
    have hcond : (Expr.op .lt (.reg 2) (.reg 20)).eval w s = some 0 := by
      simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hr2, hr20, hr_w, h0_w]
    exact ⟨s, 3, .while_false hcond, by omega, hr23, rfl, fun _ _ _ _ => rfl⟩
  | succ rem ih =>
    have h0_w : 0 < 2 ^ w := by omega
    have hk_lt_r : k < r.1 := by omega
    have hk_lt_n : k < n := by omega
    have hk_w : k < 2 ^ w := by omega
    have hr_w : r.1 < 2 ^ w := by omega
    let uFin : Fin n := ⟨k, hk_lt_n⟩
    have hcond : (Expr.op .lt (.reg 2) (.reg 20)).eval w s = some 1 := by
      simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hr2, hr20, hk_w, hr_w, hk_lt_r, hw]
    have hk_lt_12 : k < (s.arrs 12).length := by rw [hS.1]; exact hk_lt_n
    have hval12 : (s.arrs 12)[k] = if uFin ∈ S then 1 else 0 := hS.getElem_eq_ite uFin
    have hval12_w : (s.arrs 12)[k] < 2 ^ w := by rw [hval12]; split_ifs <;> omega
    let s₁ := s.setReg 3 (s.arrs 12)[k]
    have hex₁ : Exec w (.assign 3 (.read 12 (.reg 2))) s s₁ 3 :=
      .assign (by simp [Expr.eval, checkWord, hr2, hk_w, hk_lt_12, hval12_w])
    have hex_ite : ∃ s₂ t_i,
        Exec w (.ite (.op .eq (.reg 3) (.const 0)) .skip (.assign 23 (.const 0))) s₁ s₂ t_i ∧
        t_i ≤ 5 ∧
        s₂.regs 23 = (if (∀ u : Fin n, u.1 < k + 1 → u ∉ S) then 1 else 0) ∧
        s₂.arrs = s.arrs ∧
        (∀ reg : Reg, reg ≠ 3 → reg ≠ 23 → s₂.regs reg = s.regs reg) := by
      by_cases huS : uFin ∈ S
      · have hcond_i : (Expr.op .eq (.reg 3) (.const 0)).eval w s₁ = some 0 := by
          simp [s₁, Expr.eval, BinOp.eval, BinOp.raw, checkWord, hval12, huS, h0_w, hw]
        have hnot_all : ¬ (∀ u : Fin n, u.1 < k + 1 → u ∉ S) := by
          intro hall
          exact hall uFin (by show k < k + 1; omega) huS
        refine ⟨s₁.setReg 23 0, 3 + 2,
          .ite_false hcond_i (.assign (by simp [Expr.eval, checkWord, h0_w])),
          by omega,
          by rw [State.setReg_regs_self]; exact (ite_eq_right hnot_all).symm,
          rfl,
          fun reg h3 h23 => by simp [s₁, State.setReg, h3, h23]⟩
      · have hcond_i : (Expr.op .eq (.reg 3) (.const 0)).eval w s₁ = some 1 := by
          simp [s₁, Expr.eval, BinOp.eval, BinOp.raw, checkWord, hval12, huS, h0_w, hw]
        have hall_iff : (∀ u : Fin n, u.1 < k + 1 → u ∉ S) ↔ (∀ u : Fin n, u.1 < k → u ∉ S) := by
          constructor
          · intro hall u hu; exact hall u (by omega)
          · intro hall u hu
            by_cases huk : u.1 = k
            · have hu_eq : u = uFin := Fin.ext huk
              rwa [hu_eq]
            · exact hall u (by omega)
        refine ⟨s₁, 3 + 1, .ite_true hcond_i (by omega) (.skip s₁), by omega,
          by
            change s.regs 23 = _
            rw [hr23, if_congr hall_iff rfl rfl],
          rfl,
          fun reg h3 _ => by simp [s₁, State.setReg, h3]⟩
    rcases hex_ite with ⟨s₂, t_i, hex_i, ht_i, hr23₂, harr₂, hreg₂⟩
    have hr2₂ : s₂.regs 2 = k := by rw [hreg₂ 2 (by decide) (by decide), hr2]
    let s₃ := s₂.setReg 2 (k + 1)
    have hex_inc : Exec w (.assign 2 (.op .add (.reg 2) (.const 1))) s₂ s₃ 4 :=
      .assign (by simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hr2₂, hk_w, hw,
        show k + 1 < 2 ^ w by omega])
    rcases ih (k + 1) (by omega) (s := s₃)
        (hS.of_arr_eq (by simp [s₃, harr₂]))
        (by
          change (s₂.setReg 2 (k + 1)).regs 20 = r.1
          rw [State.setReg_regs_ne _ _ (by decide), hreg₂ 20 (by decide) (by decide), hr20])
        rfl
        (by
          change (s₂.setReg 2 (k + 1)).regs 23 = _
          rw [State.setReg_regs_ne _ _ (by decide), hr23₂]) with
      ⟨s₄, t₄, hex₄, ht₄, hr23₄, harr₄, hreg₄⟩
    refine ⟨s₄, 3 + ((3 + t_i) + 4) + t₄,
      .while_true hcond (by omega) (.seq (.seq hex₁ hex_i) hex_inc) hex₄,
      by omega, hr23₄, by rw [harr₄]; exact harr₂,
      fun reg h2 h3 h23 => by
        rw [hreg₄ reg h2 h3 h23]
        change (s₂.setReg 2 (k + 1)).regs reg = s.regs reg
        rw [State.setReg_regs_ne _ _ h2]
        exact hreg₂ reg h3 h23⟩

theorem checkMinInKProg_exec {w n : ℕ} (S : Finset (Fin n)) (r : Fin n)
    (hw : 1 < 2 ^ w) (hn_w : n < 2 ^ w) {s : State}
    (hS : IsBitSet S 12 s)
    (hr20 : s.regs 20 = r.1) :
    ∃ s' t,
      Exec w checkMinInKProg s s' t ∧
      t ≤ 15 * n + 7 ∧
      s'.regs 23 = (if (∀ u ∈ S, r.1 ≤ u.1) then 1 else 0) ∧
      s'.arrs = s.arrs ∧
      (∀ reg : Reg, reg ≠ 2 → reg ≠ 3 → reg ≠ 23 → s'.regs reg = s.regs reg) := by
  have h0_w : 0 < 2 ^ w := by omega
  let s₁ := s.setReg 23 1
  have hex₁ : Exec w (.assign 23 (.const 1)) s s₁ 2 :=
    .assign (by simp [Expr.eval, checkWord, hw])
  let s₂ := s₁.setReg 2 0
  have hex₂ : Exec w (.assign 2 (.const 0)) s₁ s₂ 2 :=
    .assign (by simp [Expr.eval, checkWord, h0_w])
  rcases checkMinInKLoop_exec S r hw hn_w r.1 0 (by omega) (s := s₂)
      (hS.of_arr_eq rfl)
      (by simp [s₂, s₁, State.setReg, hr20])
      rfl
      (by simp [s₂, s₁, State.setReg]) with
    ⟨s₃, t₃, hex₃, ht₃, hr23₃, harr₃, hreg₃⟩
  have hr_le : r.1 ≤ n := by omega
  have hiff : (∀ u : Fin n, u.1 < r.1 → u ∉ S) ↔ (∀ u ∈ S, r.1 ≤ u.1) := by
    constructor
    · intro h u huS
      by_contra hlt
      exact h u (by omega) huS
    · intro h u hlt huS
      have := h u huS
      omega
  rw [if_congr hiff rfl rfl] at hr23₃
  refine ⟨s₃, 2 + (2 + t₃), .seq hex₁ (.seq hex₂ hex₃), by omega, hr23₃, harr₃,
    fun reg h2 h3 h23 => by
      rw [hreg₃ reg h2 h3 h23]
      simp [s₂, s₁, State.setReg, h2, h23]⟩

/-- Pure list of Type II subgraphs `(K ∪ X, E(K) ∪ E(K, X))` emitted by Pass R2 for
vertices `r < k` with `r ∉ Z` and `r = min K`. -/
noncomputable def alg86TypeIIPairs {n : ℕ} (G : SimpleGraph (Fin n))
    (Z : Finset (Fin n)) (edges₀ : List (Fin n × Fin n)) :
    ℕ → List (Finset (Fin n) × List (Fin n × Fin n))
  | 0 => []
  | k + 1 =>
    let prev := alg86TypeIIPairs G Z edges₀ k
    if hk : k < n then
      let r : Fin n := ⟨k, hk⟩
      let K := alg86K G Z r
      let X := alg86X G Z r
      if r ∉ Z ∧ (∀ u ∈ K, r.1 ≤ u.1) then
        prev ++ [(K ∪ X, edges₀.filter (alg86KeepEdge K X false))]
      else
        prev
    else
      prev

theorem length_alg86TypeIIPairs_le {n : ℕ} (G : SimpleGraph (Fin n))
    (Z : Finset (Fin n)) (edges₀ : List (Fin n × Fin n)) :
    ∀ k, (alg86TypeIIPairs G Z edges₀ k).length ≤ k
  | 0 => by simp [alg86TypeIIPairs]
  | k + 1 => by
    have ih := length_alg86TypeIIPairs_le G Z edges₀ k
    dsimp [alg86TypeIIPairs]
    split_ifs <;> simp <;> omega

theorem length_flatMap_alg86TypeIIPairs_le {n : ℕ} (G : SimpleGraph (Fin n))
    (Z : Finset (Fin n)) (edges₀ : List (Fin n × Fin n)) :
    ∀ k, ((alg86TypeIIPairs G Z edges₀ k).flatMap (fun p => encAlg86Subgraph p.1 p.2)).length ≤
      k * (n + 2 + 2 * edges₀.length)
  | 0 => by simp [alg86TypeIIPairs]
  | k + 1 => by
    have ih := length_flatMap_alg86TypeIIPairs_le G Z edges₀ k
    dsimp [alg86TypeIIPairs]
    rw [Nat.add_one_mul k (n + 2 + 2 * edges₀.length)]
    split_ifs
    · rw [List.flatMap_append, List.length_append]
      simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil, length_encAlg86Subgraph]
      have hlen_f : (edges₀.filter (alg86KeepEdge (alg86K G Z ⟨k, ‹_›⟩) (alg86X G Z ⟨k, ‹_›⟩) false)).length ≤
          edges₀.length := List.length_filter_le _ _
      omega
    · omega
    · omega

/-- Loop body of `alg86TypeIIPassProg` (Pass R2). -/
def alg86TypeIIBody : Cmd :=
  .seq (.assign 21 (.read 14 (.reg 20)))
    (.ite (.op .eq (.reg 21) (.const 0))
      (.seq computeKAndExtNhdProg
        (.seq checkMinInKProg
          (.ite (.op .eq (.reg 23) (.const 0))
            .skip
            (.seq (.assign 28 (.const 0))
              emitUXSubgraphProg))))
      .skip)

/-- Pass R2 of Algorithm (8.6): emits Type II bridges `(K ∪ X, E(K) ∪ E(K, X))` for each
component `K` of `G \ Z` (indexed by its minimum vertex `r ∉ Z`). -/
def alg86TypeIIPassProg : Cmd :=
  .seq (.assign 20 (.const 0))
    (forUp 20 (.reg 14) alg86TypeIIBody)

private theorem alg86TypeIILoop_exec {w n cap : ℕ} (G : SimpleGraph (Fin n))
    (lists_G lists_Y : Fin n → List ℕ) (Z : Finset (Fin n))
    (edges₀ : List (Fin n × Fin n)) (pref₀ : List ℕ) (cnt₀ : ℕ)
    (htot_G : totalAdjEntries lists_G ≤ 2 * edges₀.length)
    (htot_Y : totalAdjEntries lists_Y ≤ 2 * edges₀.length)
    (hcap_le : pref₀.length + n * (n + 2 + 2 * edges₀.length) ≤ cap)
    (hw3 : 3 < 2 ^ w) (hn_w : n < 2 ^ w) (hm8_w : 8 + 2 * edges₀.length < 2 ^ w)
    (hcap_w : cap < 2 ^ w) (hcnt_w : cnt₀ + n < 2 ^ w)
    (rem k : ℕ) (hrem : k + rem = n) {s : State}
    (hin : s.arrs 0 = [n, edges₀.length] ++ flatEdges edges₀)
    (hadj_G : IsAdjList G 3 4 5 lists_G s)
    (hent_G : (s.arrs 5).length < 2 ^ w)
    (hadj_Y : IsAdjList (restrictGraph G (Finset.univ \ Z)) 6 7 8 lists_Y s)
    (hent_Y : (s.arrs 8).length < 2 ^ w)
    (hZ : IsBitSet Z 14 s)
    (hout : s.arrs outArr =
      (pref₀ ++ (alg86TypeIIPairs G Z edges₀ k).flatMap (fun p => encAlg86Subgraph p.1 p.2)) ++
        List.replicate (cap - (pref₀ ++ (alg86TypeIIPairs G Z edges₀ k).flatMap (fun p => encAlg86Subgraph p.1 p.2)).length) 0)
    (hr1 : s.regs 1 = edges₀.length)
    (hr14 : s.regs 14 = n)
    (hr20 : s.regs 20 = k)
    (hr25 : s.regs 25 = (pref₀ ++ (alg86TypeIIPairs G Z edges₀ k).flatMap (fun p => encAlg86Subgraph p.1 p.2)).length)
    (hr26 : s.regs 26 = cnt₀ + (alg86TypeIIPairs G Z edges₀ k).length) :
    ∃ s' t,
      Exec w (forUp 20 (.reg 14) alg86TypeIIBody) s s' t ∧
      t ≤ rem * (107 * n + 184 * edges₀.length + 149) + 3 ∧
      s'.arrs outArr =
        (pref₀ ++ (alg86TypeIIPairs G Z edges₀ n).flatMap (fun p => encAlg86Subgraph p.1 p.2)) ++
          List.replicate (cap - (pref₀ ++ (alg86TypeIIPairs G Z edges₀ n).flatMap (fun p => encAlg86Subgraph p.1 p.2)).length) 0 ∧
      s'.regs 25 = (pref₀ ++ (alg86TypeIIPairs G Z edges₀ n).flatMap (fun p => encAlg86Subgraph p.1 p.2)).length ∧
      s'.regs 26 = cnt₀ + (alg86TypeIIPairs G Z edges₀ n).length ∧
      (∀ a : Arr, a ≠ outArr → a ≠ 12 → a ≠ 13 → a ≠ 15 → a ≠ 17 → a ≠ 18 → s'.arrs a = s.arrs a) ∧
      (∀ reg : Reg, reg ≠ 2 → reg ≠ 3 → reg ≠ 4 → reg ≠ 5 → reg ≠ 6 → reg ≠ 7 → reg ≠ 8 → reg ≠ 9 →
        reg ≠ 20 → reg ≠ 21 → reg ≠ 22 → reg ≠ 23 → reg ≠ 25 → reg ≠ 26 → reg ≠ 28 → s'.regs reg = s.regs reg) := by
  induction rem generalizing k s with
  | zero =>
    have hk_eq : k = n := by omega
    subst hk_eq
    have h0_w : 0 < 2 ^ w := by omega
    have hcond : (Expr.op .lt (.reg 20) (.reg 14)).eval w s = some 0 := by
      simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hr20, hr14, hn_w, h0_w]
    exact ⟨s, 3, .while_false hcond, by omega, hout, hr25, hr26,
      fun _ _ _ _ _ _ _ => rfl, fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ => rfl⟩
  | succ rem ih =>
    have hw : 1 < 2 ^ w := by omega
    have h0_w : 0 < 2 ^ w := by omega
    have hk_lt : k < n := by omega
    have hk_w : k < 2 ^ w := by omega
    let rFin : Fin n := ⟨k, hk_lt⟩
    let L_k := alg86TypeIIPairs G Z edges₀ k
    let L_next := alg86TypeIIPairs G Z edges₀ (k + 1)
    let pref_k := pref₀ ++ L_k.flatMap (fun p => encAlg86Subgraph p.1 p.2)
    let pref_next := pref₀ ++ L_next.flatMap (fun p => encAlg86Subgraph p.1 p.2)
    have hcond : (Expr.op .lt (.reg 20) (.reg 14)).eval w s = some 1 := by
      simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hr20, hr14, hk_w, hn_w, hk_lt, hw]
    have hk_lt_14 : k < (s.arrs 14).length := by rw [hZ.1]; exact hk_lt
    have hval14 : (s.arrs 14)[k] = if rFin ∈ Z then 1 else 0 := hZ.getElem_eq_ite rFin
    have hval14_w : (s.arrs 14)[k] < 2 ^ w := by rw [hval14]; split_ifs <;> omega
    let s₁ := s.setReg 21 (s.arrs 14)[k]
    have hex₁ : Exec w (.assign 21 (.read 14 (.reg 20))) s s₁ 3 :=
      .assign (by simp [Expr.eval, checkWord, hr20, hk_w, hk_lt_14, hval14_w])
    have hex_body : ∃ s₂ t_b,
        Exec w (.ite (.op .eq (.reg 21) (.const 0))
          (.seq computeKAndExtNhdProg
            (.seq checkMinInKProg
              (.ite (.op .eq (.reg 23) (.const 0))
                .skip
                (.seq (.assign 28 (.const 0)) emitUXSubgraphProg))))
          .skip) s₁ s₂ t_b ∧
        t_b ≤ 107 * n + 184 * edges₀.length + 139 ∧
        s₂.arrs outArr = pref_next ++ List.replicate (cap - pref_next.length) 0 ∧
        s₂.regs 25 = pref_next.length ∧
        s₂.regs 26 = cnt₀ + L_next.length ∧
        (∀ a : Arr, a ≠ outArr → a ≠ 12 → a ≠ 13 → a ≠ 15 → a ≠ 17 → a ≠ 18 → s₂.arrs a = s.arrs a) ∧
        (∀ reg : Reg, reg ≠ 2 → reg ≠ 3 → reg ≠ 4 → reg ≠ 5 → reg ≠ 6 → reg ≠ 7 → reg ≠ 8 → reg ≠ 9 →
          reg ≠ 21 → reg ≠ 22 → reg ≠ 23 → reg ≠ 25 → reg ≠ 26 → reg ≠ 28 → s₂.regs reg = s.regs reg) := by
      by_cases hrZ : rFin ∈ Z
      · have hcond_b : (Expr.op .eq (.reg 21) (.const 0)).eval w s₁ = some 0 := by
          simp [s₁, Expr.eval, BinOp.eval, BinOp.raw, checkWord, hval14, hrZ, h0_w, hw]
        have hL_next : L_next = L_k := by simp [L_next, L_k, alg86TypeIIPairs, hk_lt, rFin, hrZ]
        have hpref_next : pref_next = pref_k := by simp [pref_next, pref_k, hL_next]
        refine ⟨s₁, 3 + 1, .ite_false hcond_b (.skip s₁), by omega,
          by simpa [s₁, hpref_next, pref_k] using hout,
          by simpa [s₁, State.setReg, hpref_next, pref_k] using hr25,
          by simpa [s₁, State.setReg, hL_next, L_k] using hr26,
          fun _ _ _ _ _ _ _ => rfl,
          fun reg _ _ _ _ _ _ _ _ h21 _ _ _ _ _ => by simp [s₁, State.setReg, h21]⟩
      · have hcond_b : (Expr.op .eq (.reg 21) (.const 0)).eval w s₁ = some 1 := by
          simp [s₁, Expr.eval, BinOp.eval, BinOp.raw, checkWord, hval14, hrZ, h0_w, hw]
        rcases computeKAndExtNhdProg_exec G lists_G lists_Y Z rFin htot_G htot_Y hw hn_w (s := s₁)
            (hadj_G.of_arrs_eq rfl rfl rfl) hent_G
            (hadj_Y.of_arrs_eq rfl rfl rfl) hent_Y
            (by simp [s₁, State.setReg, hr14])
            (by simp [s₁, State.setReg, hr20, rFin]) with
          ⟨s₂, t₂, hex₂, ht₂, hK₂, hN₂, harr₂, hreg₂⟩
        have hr20₂ : s₂.regs 20 = rFin.1 := by
          rw [hreg₂ 20 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]
          simp [s₁, State.setReg, hr20, rFin]
        rcases checkMinInKProg_exec (alg86K G Z rFin) rFin hw hn_w hK₂ hr20₂ with
          ⟨s₃, t₃, hex₃, ht₃, hr23₃, harr₃, hreg₃⟩
        by_cases hmin : ∀ u ∈ alg86K G Z rFin, rFin.1 ≤ u.1
        · have hr23_val : s₃.regs 23 = 1 := by rw [hr23₃]; exact ite_eq_left hmin
          have hcond_m : (Expr.op .eq (.reg 23) (.const 0)).eval w s₃ = some 0 := by
            simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hr23_val, h0_w, hw]
          let s₄ := s₃.setReg 28 0
          have hex₄ : Exec w (.assign 28 (.const 0)) s₃ s₄ 2 :=
            .assign (by simp [Expr.eval, checkWord, h0_w])
          have hX₄ : IsBitSet (alg86X G Z rFin) 13 s₄ := by
            rw [alg86X_eq_extNeighborhood_of_not_mem G Z hrZ]
            exact hN₂.of_arr_eq (by simp [s₄, harr₃])
          have hlen_Lk : (L_k.flatMap (fun p => encAlg86Subgraph p.1 p.2)).length ≤
              k * (n + 2 + 2 * edges₀.length) :=
            length_flatMap_alg86TypeIIPairs_le G Z edges₀ k
          have h1_mul : (k + 1) * (n + 2 + 2 * edges₀.length) ≤ n * (n + 2 + 2 * edges₀.length) :=
            Nat.mul_le_mul_right _ (by omega)
          have h1_eq : (k + 1) * (n + 2 + 2 * edges₀.length) =
              k * (n + 2 + 2 * edges₀.length) + (n + 2 + 2 * edges₀.length) :=
            Nat.add_one_mul k _
          have hcap_k : pref_k.length + (n + 2 + 2 * edges₀.length) ≤ cap := by
            have : pref_k.length = pref₀.length + (L_k.flatMap (fun p => encAlg86Subgraph p.1 p.2)).length := by
              simp [pref_k]
            omega
          have hcnt_k : (cnt₀ + L_k.length) + 1 < 2 ^ w := by
            have : L_k.length ≤ k := length_alg86TypeIIPairs_le G Z edges₀ k
            omega
          rcases emitUXSubgraphProg_exec (alg86K G Z rFin) (alg86X G Z rFin) false edges₀
              pref_k hcap_k hw3 hm8_w hcap_w (cnt := cnt₀ + L_k.length) hcnt_k (s := s₄)
              (by
                change s₃.arrs 0 = _
                rw [harr₃, harr₂ 0 (by decide) (by decide) (by decide)]
                exact hin)
              (hK₂.of_arr_eq (by simp [s₄, harr₃]))
              hX₄
              (by
                change s₃.arrs outArr = _
                rw [harr₃, harr₂ outArr (by decide) (by decide) (by decide)]
                exact hout)
              (by
                change (s₃.setReg 28 0).regs 1 = edges₀.length
                rw [State.setReg_regs_ne _ _ (by decide), hreg₃ 1 (by decide) (by decide) (by decide),
                    hreg₂ 1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]
                simp [s₁, State.setReg, hr1])
              (by
                change (s₃.setReg 28 0).regs 14 = n
                rw [State.setReg_regs_ne _ _ (by decide), hreg₃ 14 (by decide) (by decide) (by decide),
                    hreg₂ 14 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]
                simp [s₁, State.setReg, hr14])
              (by
                change (s₃.setReg 28 0).regs 25 = pref_k.length
                rw [State.setReg_regs_ne _ _ (by decide), hreg₃ 25 (by decide) (by decide) (by decide),
                    hreg₂ 25 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]
                simpa [s₁, State.setReg, pref_k] using hr25)
              (by
                change (s₃.setReg 28 0).regs 26 = cnt₀ + L_k.length
                rw [State.setReg_regs_ne _ _ (by decide), hreg₃ 26 (by decide) (by decide) (by decide),
                    hreg₂ 26 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]
                simpa [s₁, State.setReg, L_k] using hr26)
              rfl with
            ⟨s₅, t₅, hex₅, ht₅, hout₅, hr25₅, hr26₅, harr₅, hreg₅⟩
          have hL_next : L_next = L_k ++ [(alg86K G Z rFin ∪ alg86X G Z rFin,
              edges₀.filter (alg86KeepEdge (alg86K G Z rFin) (alg86X G Z rFin) false))] := by
            dsimp [L_next, L_k, alg86TypeIIPairs]
            rw [dite_eq_left hk_lt]
            exact ite_eq_left ⟨hrZ, hmin⟩
          have hpref_next : pref_next = pref_k ++ encAlg86Subgraph (alg86K G Z rFin ∪ alg86X G Z rFin)
              (edges₀.filter (alg86KeepEdge (alg86K G Z rFin) (alg86X G Z rFin) false)) := by
            simp [pref_next, pref_k, hL_next, List.flatMap_append, List.append_assoc]
          have hcnt_next : cnt₀ + L_next.length = (cnt₀ + L_k.length) + 1 := by
            simp [hL_next, List.length_append]
            omega
          refine ⟨s₅, 3 + (t₂ + (t₃ + (3 + (2 + t₅)))),
            .ite_true hcond_b (by omega)
              (.seq hex₂ (.seq hex₃ (.ite_false hcond_m (.seq hex₄ hex₅)))),
            by omega,
            by rw [hpref_next]; exact hout₅,
            by rw [hpref_next]; exact hr25₅,
            by rw [hcnt_next]; exact hr26₅,
            fun a hout h12 h13 h15 h17 h18 => by
              rw [harr₅ a hout h17 h18]
              change s₃.arrs a = s.arrs a
              rw [harr₃, harr₂ a h12 h13 h15]
              rfl,
            fun reg h2 h3 h4 h5 h6 h7 h8 h9 h21 h22 h23 h25 h26 h28 => by
              rw [hreg₅ reg h2 h3 h4 h5 h6 h7 h8 h9 h21 h22 h25 h26]
              change (s₃.setReg 28 0).regs reg = s.regs reg
              rw [State.setReg_regs_ne _ _ h28, hreg₃ reg h2 h3 h23,
                  hreg₂ reg h2 h3 h4 h5 h6 h7 h8]
              simp [s₁, State.setReg, h21]⟩
        · have hr23_val : s₃.regs 23 = 0 := by rw [hr23₃]; exact ite_eq_right hmin
          have hcond_m : (Expr.op .eq (.reg 23) (.const 0)).eval w s₃ = some 1 := by
            simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hr23_val, h0_w, hw]
          have hL_next : L_next = L_k := by
            dsimp [L_next, L_k, alg86TypeIIPairs]
            rw [dite_eq_left hk_lt]
            exact ite_eq_right (fun h => hmin h.2)
          have hpref_next : pref_next = pref_k := by simp [pref_next, pref_k, hL_next]
          refine ⟨s₃, 3 + (t₂ + (t₃ + (3 + 1))),
            .ite_true hcond_b (by omega) (.seq hex₂ (.seq hex₃ (.ite_true hcond_m (by omega) (.skip s₃)))),
            by omega,
            by
              rw [harr₃, harr₂ outArr (by decide) (by decide) (by decide)]
              simpa [s₁, hpref_next, pref_k] using hout,
            by
              rw [hreg₃ 25 (by decide) (by decide) (by decide),
                  hreg₂ 25 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]
              simpa [s₁, State.setReg, hpref_next, pref_k] using hr25,
            by
              rw [hreg₃ 26 (by decide) (by decide) (by decide),
                  hreg₂ 26 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]
              simpa [s₁, State.setReg, hL_next, L_k] using hr26,
            fun a _ h12 h13 h15 _ _ => by
              rw [harr₃, harr₂ a h12 h13 h15]; rfl,
            fun reg h2 h3 h4 h5 h6 h7 h8 _ h21 _ h23 _ _ _ => by
              rw [hreg₃ reg h2 h3 h23, hreg₂ reg h2 h3 h4 h5 h6 h7 h8]
              simp [s₁, State.setReg, h21]⟩
    rcases hex_body with ⟨s₂, t_b, hex_b, ht_b, hout₂, hr25₂, hr26₂, harr₂, hreg₂⟩
    have hr20₂ : s₂.regs 20 = k := by
      rw [hreg₂ 20 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
            (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), hr20]
    let s₃ := s₂.setReg 20 (k + 1)
    have hex_inc : Exec w (.assign 20 (.op .add (.reg 20) (.const 1))) s₂ s₃ 4 :=
      .assign (by simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hr20₂, hk_w, hw,
        show k + 1 < 2 ^ w by omega])
    have harr₂_lt : ∀ a : Arr, a ≠ outArr → a < 12 → s₂.arrs a = s.arrs a := by
      intro a hout ha
      dsimp [Arr, outArr] at *
      exact harr₂ a hout (by omega) (by omega) (by omega) (by omega) (by omega)
    rcases ih (k + 1) (by omega) (s := s₃)
        (by rw [show s₃.arrs 0 = s₂.arrs 0 from rfl, harr₂_lt 0 (by decide) (by decide), hin])
        (hadj_G.of_arrs_eq (harr₂_lt 3 (by decide) (by decide))
          (harr₂_lt 4 (by decide) (by decide)) (harr₂_lt 5 (by decide) (by decide)))
        (by simp [s₃, harr₂_lt 5 (by decide) (by decide), hent_G])
        (hadj_Y.of_arrs_eq (harr₂_lt 6 (by decide) (by decide))
          (harr₂_lt 7 (by decide) (by decide)) (harr₂_lt 8 (by decide) (by decide)))
        (by simp [s₃, harr₂_lt 8 (by decide) (by decide), hent_Y])
        (hZ.of_arr_eq (harr₂ 14 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)))
        hout₂
        (by
          change (s₂.setReg 20 (k + 1)).regs 1 = edges₀.length
          rw [State.setReg_regs_ne _ _ (by decide),
              hreg₂ 1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
                (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), hr1])
        (by
          change (s₂.setReg 20 (k + 1)).regs 14 = n
          rw [State.setReg_regs_ne _ _ (by decide),
              hreg₂ 14 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
                (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), hr14])
        rfl
        (by
          change (s₂.setReg 20 (k + 1)).regs 25 = pref_next.length
          rw [State.setReg_regs_ne _ _ (by decide), hr25₂])
        (by
          change (s₂.setReg 20 (k + 1)).regs 26 = cnt₀ + L_next.length
          rw [State.setReg_regs_ne _ _ (by decide), hr26₂]) with
      ⟨s₄, t₄, hex₄, ht₄, hout₄, hr25₄, hr26₄, harr₄, hreg₄⟩
    have hmul : (rem + 1) * (107 * n + 184 * edges₀.length + 149) =
        (107 * n + 184 * edges₀.length + 149) + rem * (107 * n + 184 * edges₀.length + 149) := by ring
    refine ⟨s₄, 3 + ((3 + t_b) + 4) + t₄,
      .while_true hcond (by omega) (.seq (.seq hex₁ hex_b) hex_inc) hex₄,
      by linarith [ht_b, ht₄, hmul], hout₄, hr25₄, hr26₄,
      fun a hout h12 h13 h15 h17 h18 => by
        rw [harr₄ a hout h12 h13 h15 h17 h18]
        exact harr₂ a hout h12 h13 h15 h17 h18,
      fun reg h2 h3 h4 h5 h6 h7 h8 h9 h20 h21 h22 h23 h25 h26 h28 => by
        rw [hreg₄ reg h2 h3 h4 h5 h6 h7 h8 h9 h20 h21 h22 h23 h25 h26 h28]
        change (s₂.setReg 20 (k + 1)).regs reg = s.regs reg
        rw [State.setReg_regs_ne _ _ h20]
        exact hreg₂ reg h2 h3 h4 h5 h6 h7 h8 h9 h21 h22 h23 h25 h26 h28⟩

theorem alg86TypeIIPassProg_exec {w n cap : ℕ} (G : SimpleGraph (Fin n))
    (lists_G lists_Y : Fin n → List ℕ) (Z : Finset (Fin n))
    (edges₀ : List (Fin n × Fin n)) (pref₀ : List ℕ) (cnt₀ : ℕ)
    (htot_G : totalAdjEntries lists_G ≤ 2 * edges₀.length)
    (htot_Y : totalAdjEntries lists_Y ≤ 2 * edges₀.length)
    (hcap_le : pref₀.length + n * (n + 2 + 2 * edges₀.length) ≤ cap)
    (hw3 : 3 < 2 ^ w) (hn_w : n < 2 ^ w) (hm8_w : 8 + 2 * edges₀.length < 2 ^ w)
    (hcap_w : cap < 2 ^ w) (hcnt_w : cnt₀ + n < 2 ^ w) {s : State}
    (hin : s.arrs 0 = [n, edges₀.length] ++ flatEdges edges₀)
    (hadj_G : IsAdjList G 3 4 5 lists_G s)
    (hent_G : (s.arrs 5).length < 2 ^ w)
    (hadj_Y : IsAdjList (restrictGraph G (Finset.univ \ Z)) 6 7 8 lists_Y s)
    (hent_Y : (s.arrs 8).length < 2 ^ w)
    (hZ : IsBitSet Z 14 s)
    (hout : s.arrs outArr = pref₀ ++ List.replicate (cap - pref₀.length) 0)
    (hr1 : s.regs 1 = edges₀.length)
    (hr14 : s.regs 14 = n)
    (hr25 : s.regs 25 = pref₀.length)
    (hr26 : s.regs 26 = cnt₀) :
    let L := alg86TypeIIPairs G Z edges₀ n
    ∃ s' t,
      Exec w alg86TypeIIPassProg s s' t ∧
      t ≤ n * (107 * n + 184 * edges₀.length + 149) + 5 ∧
      s'.arrs outArr =
        (pref₀ ++ L.flatMap (fun p => encAlg86Subgraph p.1 p.2)) ++
          List.replicate (cap - (pref₀ ++ L.flatMap (fun p => encAlg86Subgraph p.1 p.2)).length) 0 ∧
      s'.regs 25 = (pref₀ ++ L.flatMap (fun p => encAlg86Subgraph p.1 p.2)).length ∧
      s'.regs 26 = cnt₀ + L.length ∧
      (∀ a : Arr, a ≠ outArr → a ≠ 12 → a ≠ 13 → a ≠ 15 → a ≠ 17 → a ≠ 18 → s'.arrs a = s.arrs a) ∧
      (∀ reg : Reg, reg ≠ 2 → reg ≠ 3 → reg ≠ 4 → reg ≠ 5 → reg ≠ 6 → reg ≠ 7 → reg ≠ 8 → reg ≠ 9 →
        reg ≠ 20 → reg ≠ 21 → reg ≠ 22 → reg ≠ 23 → reg ≠ 25 → reg ≠ 26 → reg ≠ 28 → s'.regs reg = s.regs reg) := by
  intro L
  have h0_w : 0 < 2 ^ w := by omega
  let s₁ := s.setReg 20 0
  have hex₁ : Exec w (.assign 20 (.const 0)) s s₁ 2 :=
    .assign (by simp [Expr.eval, checkWord, h0_w])
  rcases alg86TypeIILoop_exec G lists_G lists_Y Z edges₀ pref₀ cnt₀ htot_G htot_Y
      hcap_le hw3 hn_w hm8_w hcap_w hcnt_w n 0 (by omega) (s := s₁)
      hin (hadj_G.of_arrs_eq rfl rfl rfl) hent_G
      (hadj_Y.of_arrs_eq rfl rfl rfl) hent_Y
      (hZ.of_arr_eq rfl)
      (by simpa [s₁, alg86TypeIIPairs] using hout)
      (by simp [s₁, State.setReg, hr1])
      (by simp [s₁, State.setReg, hr14])
      rfl
      (by simpa [s₁, State.setReg, alg86TypeIIPairs] using hr25)
      (by simpa [s₁, State.setReg, alg86TypeIIPairs] using hr26) with
    ⟨s₂, t₂, hex₂, ht₂, hout₂, hr25₂, hr26₂, harr₂, hreg₂⟩
  refine ⟨s₂, 2 + t₂, .seq hex₁ hex₂, by omega, hout₂, hr25₂, hr26₂,
    fun a hout h12 h13 h15 h17 h18 => by rw [harr₂ a hout h12 h13 h15 h17 h18]; rfl,
    fun reg h2 h3 h4 h5 h6 h7 h8 h9 h20 h21 h22 h23 h25 h26 h28 => by
      rw [hreg₂ reg h2 h3 h4 h5 h6 h7 h8 h9 h20 h21 h22 h23 h25 h26 h28]
      simp [s₁, State.setReg, h20]⟩

/-- Helper lemma for testing `r_3 == r_target` and clearing flag register `r_4` if unequal. -/
private lemma guardEqReg_exec {w : ℕ} (r_target : Reg) (val target : ℕ) (P : Prop) [Decidable P]
    (hw : 1 < 2 ^ w) (hval_w : val < 2 ^ w) (htarget_w : target < 2 ^ w) {s : State}
    (hr3 : s.regs 3 = val) (hrt : s.regs r_target = target)
    (hr4 : s.regs 4 = if P then 1 else 0) :
    ∃ s' t,
      Exec w (.ite (.op .eq (.reg 3) (.reg r_target)) .skip (.assign 4 (.const 0))) s s' t ∧
      t ≤ 5 ∧
      s'.regs 4 = (if (P ∧ val = target) then 1 else 0) ∧
      s'.arrs = s.arrs ∧
      (∀ reg : Reg, reg ≠ 4 → s'.regs reg = s.regs reg) := by
  have h0_w : 0 < 2 ^ w := by omega
  by_cases heq : val = target
  · have hcond : (Expr.op .eq (.reg 3) (.reg r_target)).eval w s = some 1 := by
      simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hr3, hrt, htarget_w, heq, hw]
    refine ⟨s, 3 + 1, .ite_true hcond (by omega) (.skip s), by omega,
      by rw [hr4]; simp [heq], rfl, fun _ _ => rfl⟩
  · have hcond : (Expr.op .eq (.reg 3) (.reg r_target)).eval w s = some 0 := by
      simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hr3, hrt, hval_w, htarget_w, heq, h0_w]
    refine ⟨s.setReg 4 0, 3 + 2,
      .ite_false hcond (.assign (by simp [Expr.eval, checkWord, h0_w])),
      by omega, by simp [State.setReg, heq], rfl,
      fun reg h4 => by simp [State.setReg, h4]⟩

/-- Loop body of `buildUBitSetProg`: sets `a_12[r_2] := 1` if `a_14[r_2] == 0` and
`(a_52[r_2], a_53[r_2], a_54[r_2], a_55[r_2]) == (r_5, r_6, r_7, r_8)`, and `0` otherwise. -/
def buildUBitSetBody : Cmd :=
  .seq (.assign 4 (.const 1))
    (.seq (.assign 3 (.read 14 (.reg 2)))
      (.seq (.ite (.op .eq (.reg 3) (.const 0)) .skip (.assign 4 (.const 0)))
        (.seq (.assign 3 (.read 52 (.reg 2)))
          (.seq (.ite (.op .eq (.reg 3) (.reg 5)) .skip (.assign 4 (.const 0)))
            (.seq (.assign 3 (.read 53 (.reg 2)))
              (.seq (.ite (.op .eq (.reg 3) (.reg 6)) .skip (.assign 4 (.const 0)))
                (.seq (.assign 3 (.read 54 (.reg 2)))
                  (.seq (.ite (.op .eq (.reg 3) (.reg 7)) .skip (.assign 4 (.const 0)))
                    (.seq (.assign 3 (.read 55 (.reg 2)))
                      (.seq (.ite (.op .eq (.reg 3) (.reg 8)) .skip (.assign 4 (.const 0)))
                        (.write 12 (.reg 2) (.reg 4))))))))))))

/-- Builds `IsBitSet (alg86U G Z r) 12` for `r` in `r_20` from `HasAlg86Tuples G Z`. -/
def buildUBitSetProg : Cmd :=
  .seq (.alloc 12 (.reg 14))
    (.seq (.assign 5 (.read 52 (.reg 20)))
      (.seq (.assign 6 (.read 53 (.reg 20)))
        (.seq (.assign 7 (.read 54 (.reg 20)))
          (.seq (.assign 8 (.read 55 (.reg 20)))
            (.seq (.assign 2 (.const 0))
              (forUp 2 (.reg 14) buildUBitSetBody))))))

private theorem buildUBitSetLoop_exec {w n : ℕ} (G : SimpleGraph (Fin n))
    (Z : Finset (Fin n)) (r : Fin n)
    (hw : 1 < 2 ^ w) (hn_w : n < 2 ^ w)
    (rem k : ℕ) (hrem : k + rem = n) {s : State}
    (hZ : IsBitSet Z 14 s)
    (htup : HasAlg86Tuples G Z s)
    (h12_len : (s.arrs 12).length = n)
    (h12_val : ∀ u : Fin n, u.1 < k → (s.arrs 12)[u.1]'(by omega) = if u ∈ alg86U G Z r then 1 else 0)
    (hr14 : s.regs 14 = n)
    (hr2 : s.regs 2 = k)
    (hr5 : s.regs 5 = (alg86L G Z r).length)
    (hr6 : s.regs 6 = (if h0 : 0 < (alg86L G Z r).length then ((alg86L G Z r)[0]'h0).1 else 0))
    (hr7 : s.regs 7 = (if h1 : 1 < (alg86L G Z r).length then ((alg86L G Z r)[1]'h1).1 else 0))
    (hr8 : s.regs 8 = (if h2 : 2 < (alg86L G Z r).length then ((alg86L G Z r)[2]'h2).1 else 0)) :
    ∃ s' t,
      Exec w (forUp 2 (.reg 14) buildUBitSetBody) s s' t ∧
      t ≤ 52 * rem + 3 ∧
      IsBitSet (alg86U G Z r) 12 s' ∧
      (∀ a : Arr, a ≠ 12 → s'.arrs a = s.arrs a) ∧
      (∀ reg : Reg, reg ≠ 2 → reg ≠ 3 → reg ≠ 4 → s'.regs reg = s.regs reg) := by
  induction rem generalizing k s with
  | zero =>
    have hk_eq : k = n := by omega
    subst hk_eq
    have h0_w : 0 < 2 ^ w := by omega
    have hcond : (Expr.op .lt (.reg 2) (.reg 14)).eval w s = some 0 := by
      simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hr2, hr14, hn_w, h0_w]
    refine ⟨s, 3, .while_false hcond, by omega,
      ⟨h12_len,
        fun u => by rw [h12_val u u.2]; split_ifs <;> omega,
        fun u => by rw [h12_val u u.2]; split_ifs with h <;> simp [h]⟩,
      fun _ _ => rfl, fun _ _ _ _ => rfl⟩
  | succ rem ih =>
    have h0_w : 0 < 2 ^ w := by omega
    have hk_lt : k < n := by omega
    have hk_w : k < 2 ^ w := by omega
    let uFin : Fin n := ⟨k, hk_lt⟩
    have hcond : (Expr.op .lt (.reg 2) (.reg 14)).eval w s = some 1 := by
      simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hr2, hr14, hk_w, hn_w, hk_lt, hw]
    have hLr_le : (alg86L G Z r).length ≤ n :=
      (List.length_filter_le _ _).trans (by simp)
    have hLu_le : (alg86L G Z uFin).length ≤ n :=
      (List.length_filter_le _ _).trans (by simp)
    have hc0r_w : (alg86L G Z r).length < 2 ^ w := by omega
    have hc1r_w : (if h0 : 0 < (alg86L G Z r).length then ((alg86L G Z r)[0]'h0).1 else 0) < 2 ^ w := by
      split_ifs with h0
      · have := ((alg86L G Z r)[0]'h0).2; omega
      · omega
    have hc2r_w : (if h1 : 1 < (alg86L G Z r).length then ((alg86L G Z r)[1]'h1).1 else 0) < 2 ^ w := by
      split_ifs with h1
      · have := ((alg86L G Z r)[1]'h1).2; omega
      · omega
    have hc3r_w : (if h2 : 2 < (alg86L G Z r).length then ((alg86L G Z r)[2]'h2).1 else 0) < 2 ^ w := by
      split_ifs with h2
      · have := ((alg86L G Z r)[2]'h2).2; omega
      · omega
    have htup_u := htup.val uFin hk_lt
    have hc0u_w : (s.arrs 52)[k]'(by rw [htup.len52]; exact hk_lt) < 2 ^ w := by
      rw [htup_u.1]; omega
    have hc1u_w : (s.arrs 53)[k]'(by rw [htup.len53]; exact hk_lt) < 2 ^ w := by
      rw [htup_u.2.1]
      split_ifs with h0
      · have := ((alg86L G Z uFin)[0]'h0).2; omega
      · omega
    have hc2u_w : (s.arrs 54)[k]'(by rw [htup.len54]; exact hk_lt) < 2 ^ w := by
      rw [htup_u.2.2.1]
      split_ifs with h1
      · have := ((alg86L G Z uFin)[1]'h1).2; omega
      · omega
    have hc3u_w : (s.arrs 55)[k]'(by rw [htup.len55]; exact hk_lt) < 2 ^ w := by
      rw [htup_u.2.2.2]
      split_ifs with h2
      · have := ((alg86L G Z uFin)[2]'h2).2; omega
      · omega
    -- 1. r_4 := 1
    let s₁ := s.setReg 4 1
    have hex₁ : Exec w (.assign 4 (.const 1)) s s₁ 2 :=
      .assign (by simp [Expr.eval, checkWord, hw])
    -- 2. r_3 := a_14[r_2]
    have hk_lt_14 : k < (s.arrs 14).length := by rw [hZ.1]; exact hk_lt
    have hval14 : (s.arrs 14)[k] = if uFin ∈ Z then 1 else 0 := hZ.getElem_eq_ite uFin
    have hval14_w : (s.arrs 14)[k] < 2 ^ w := by rw [hval14]; split_ifs <;> omega
    let s₂ := s₁.setReg 3 (s.arrs 14)[k]
    have hex₂ : Exec w (.assign 3 (.read 14 (.reg 2))) s₁ s₂ 3 :=
      .assign (by simp [s₁, Expr.eval, checkWord, hr2, hk_w, hk_lt_14, hval14_w])
    -- 3. check r_3 == 0 (uFin ∉ Z)
    have hex₃ : ∃ s₃ t₃,
        Exec w (.ite (.op .eq (.reg 3) (.const 0)) .skip (.assign 4 (.const 0))) s₂ s₃ t₃ ∧
        t₃ ≤ 5 ∧
        s₃.regs 4 = (if uFin ∉ Z then 1 else 0) ∧
        s₃.arrs = s.arrs ∧
        (∀ reg : Reg, reg ≠ 3 → reg ≠ 4 → s₃.regs reg = s.regs reg) := by
      by_cases huZ : uFin ∈ Z
      · have hcond₃ : (Expr.op .eq (.reg 3) (.const 0)).eval w s₂ = some 0 := by
          simp [s₂, Expr.eval, BinOp.eval, BinOp.raw, checkWord, hval14, huZ, h0_w, hw]
        refine ⟨s₂.setReg 4 0, 3 + 2,
          .ite_false hcond₃ (.assign (by simp [Expr.eval, checkWord, h0_w])),
          by omega, by simp [State.setReg, huZ], rfl,
          fun reg h3 h4 => by simp [s₂, s₁, State.setReg, h3, h4]⟩
      · have hcond₃ : (Expr.op .eq (.reg 3) (.const 0)).eval w s₂ = some 1 := by
          simp [s₂, Expr.eval, BinOp.eval, BinOp.raw, checkWord, hval14, huZ, h0_w, hw]
        refine ⟨s₂, 3 + 1, .ite_true hcond₃ (by omega) (.skip s₂), by omega,
          by simp [s₂, s₁, State.setReg, huZ], rfl,
          fun reg h3 h4 => by simp [s₂, s₁, State.setReg, h3, h4]⟩
    rcases hex₃ with ⟨s₃, t₃, hex₃, ht₃, hr4₃, harr₃, hreg₃⟩
    -- 4. r_3 := a_52[r_2], guardEqReg 5
    have hr2₃ : s₃.regs 2 = k := by rw [hreg₃ 2 (by decide) (by decide), hr2]
    let s₄ := s₃.setReg 3 ((s.arrs 52)[k]'(by rw [htup.len52]; exact hk_lt))
    have hex₄ : Exec w (.assign 3 (.read 52 (.reg 2))) s₃ s₄ 3 := by
      have hk_52 : k < (s₃.arrs 52).length := by rw [harr₃, htup.len52]; exact hk_lt
      have hval_eq : (s₃.arrs 52)[k] = (s.arrs 52)[k]'(by rw [htup.len52]; exact hk_lt) := by simp [harr₃]
      exact .assign (by simp [Expr.eval, checkWord, hr2₃, hk_w, hk_52, hval_eq, hc0u_w])
    rcases guardEqReg_exec 5 ((s.arrs 52)[k]'(by rw [htup.len52]; exact hk_lt)) (alg86L G Z r).length
        (uFin ∉ Z) hw hc0u_w hc0r_w (s := s₄) rfl
        (by simp [s₄, State.setReg, hreg₃ 5 (by decide) (by decide), hr5])
        (by simp [s₄, State.setReg, hr4₃]) with
      ⟨s₅, t₅, hex₅, ht₅, hr4₅, harr₅, hreg₅⟩
    -- 5. r_3 := a_53[r_2], guardEqReg 6
    have hr2₅ : s₅.regs 2 = k := by rw [hreg₅ 2 (by decide)]; exact hr2₃
    have harr₅_eq : s₅.arrs = s.arrs := by rw [harr₅]; exact harr₃
    let s₆ := s₅.setReg 3 ((s.arrs 53)[k]'(by rw [htup.len53]; exact hk_lt))
    have hex₆ : Exec w (.assign 3 (.read 53 (.reg 2))) s₅ s₆ 3 := by
      have hk_53 : k < (s₅.arrs 53).length := by rw [harr₅_eq, htup.len53]; exact hk_lt
      have hval_eq : (s₅.arrs 53)[k] = (s.arrs 53)[k]'(by rw [htup.len53]; exact hk_lt) := by simp [harr₅_eq]
      exact .assign (by simp [Expr.eval, checkWord, hr2₅, hk_w, hk_53, hval_eq, hc1u_w])
    rcases guardEqReg_exec 6 ((s.arrs 53)[k]'(by rw [htup.len53]; exact hk_lt))
        (if h0 : 0 < (alg86L G Z r).length then ((alg86L G Z r)[0]'h0).1 else 0)
        (uFin ∉ Z ∧ (s.arrs 52)[k]'(by rw [htup.len52]; exact hk_lt) = (alg86L G Z r).length)
        hw hc1u_w hc1r_w (s := s₆) rfl
        (by simp [s₆, State.setReg, hreg₅ 6 (by decide), s₄, hreg₃ 6 (by decide) (by decide), hr6])
        (by simp [s₆, State.setReg, hr4₅]) with
      ⟨s₇, t₇, hex₇, ht₇, hr4₇, harr₇, hreg₇⟩
    -- 6. r_3 := a_54[r_2], guardEqReg 7
    have hr2₇ : s₇.regs 2 = k := by rw [hreg₇ 2 (by decide)]; exact hr2₅
    have harr₇_eq : s₇.arrs = s.arrs := by rw [harr₇]; exact harr₅_eq
    let s₈ := s₇.setReg 3 ((s.arrs 54)[k]'(by rw [htup.len54]; exact hk_lt))
    have hex₈ : Exec w (.assign 3 (.read 54 (.reg 2))) s₇ s₈ 3 := by
      have hk_54 : k < (s₇.arrs 54).length := by rw [harr₇_eq, htup.len54]; exact hk_lt
      have hval_eq : (s₇.arrs 54)[k] = (s.arrs 54)[k]'(by rw [htup.len54]; exact hk_lt) := by simp [harr₇_eq]
      exact .assign (by simp [Expr.eval, checkWord, hr2₇, hk_w, hk_54, hval_eq, hc2u_w])
    rcases guardEqReg_exec 7 ((s.arrs 54)[k]'(by rw [htup.len54]; exact hk_lt))
        (if h1 : 1 < (alg86L G Z r).length then ((alg86L G Z r)[1]'h1).1 else 0)
        ((uFin ∉ Z ∧ (s.arrs 52)[k]'(by rw [htup.len52]; exact hk_lt) = (alg86L G Z r).length) ∧
          (s.arrs 53)[k]'(by rw [htup.len53]; exact hk_lt) =
            (if h0 : 0 < (alg86L G Z r).length then ((alg86L G Z r)[0]'h0).1 else 0))
        hw hc2u_w hc2r_w (s := s₈) rfl
        (by simp [s₈, State.setReg, hreg₇ 7 (by decide), s₆, hreg₅ 7 (by decide), s₄,
            hreg₃ 7 (by decide) (by decide), hr7])
        (by simp [s₈, State.setReg, hr4₇]) with
      ⟨s₉, t₉, hex₉, ht₉, hr4₉, harr₉, hreg₉⟩
    -- 7. r_3 := a_55[r_2], guardEqReg 8
    have hr2₉ : s₉.regs 2 = k := by rw [hreg₉ 2 (by decide)]; exact hr2₇
    have harr₉_eq : s₉.arrs = s.arrs := by rw [harr₉]; exact harr₇_eq
    let s₁₀ := s₉.setReg 3 ((s.arrs 55)[k]'(by rw [htup.len55]; exact hk_lt))
    have hex₁₀ : Exec w (.assign 3 (.read 55 (.reg 2))) s₉ s₁₀ 3 := by
      have hk_55 : k < (s₉.arrs 55).length := by rw [harr₉_eq, htup.len55]; exact hk_lt
      have hval_eq : (s₉.arrs 55)[k] = (s.arrs 55)[k]'(by rw [htup.len55]; exact hk_lt) := by simp [harr₉_eq]
      exact .assign (by simp [Expr.eval, checkWord, hr2₉, hk_w, hk_55, hval_eq, hc3u_w])
    rcases guardEqReg_exec 8 ((s.arrs 55)[k]'(by rw [htup.len55]; exact hk_lt))
        (if h2 : 2 < (alg86L G Z r).length then ((alg86L G Z r)[2]'h2).1 else 0)
        (((uFin ∉ Z ∧ (s.arrs 52)[k]'(by rw [htup.len52]; exact hk_lt) = (alg86L G Z r).length) ∧
          (s.arrs 53)[k]'(by rw [htup.len53]; exact hk_lt) =
            (if h0 : 0 < (alg86L G Z r).length then ((alg86L G Z r)[0]'h0).1 else 0)) ∧
          (s.arrs 54)[k]'(by rw [htup.len54]; exact hk_lt) =
            (if h1 : 1 < (alg86L G Z r).length then ((alg86L G Z r)[1]'h1).1 else 0))
        hw hc3u_w hc3r_w (s := s₁₀) rfl
        (by simp [s₁₀, State.setReg, hreg₉ 8 (by decide), s₈, hreg₇ 8 (by decide), s₆,
            hreg₅ 8 (by decide), s₄, hreg₃ 8 (by decide) (by decide), hr8])
        (by simp [s₁₀, State.setReg, hr4₉]) with
      ⟨s₁₁, t₁₁, hex₁₁, ht₁₁, hr4₁₁, harr₁₁, hreg₁₁⟩
    -- 8. write 12 (.reg 2) (.reg 4)
    have hr2₁₁ : s₁₁.regs 2 = k := by rw [hreg₁₁ 2 (by decide)]; exact hr2₉
    have harr₁₁_eq : s₁₁.arrs = s.arrs := by rw [harr₁₁]; exact harr₉_eq
    have hmem_iff :
        ((((uFin ∉ Z ∧ (s.arrs 52)[k]'(by rw [htup.len52]; exact hk_lt) = (alg86L G Z r).length) ∧
          (s.arrs 53)[k]'(by rw [htup.len53]; exact hk_lt) =
            (if h0 : 0 < (alg86L G Z r).length then ((alg86L G Z r)[0]'h0).1 else 0)) ∧
          (s.arrs 54)[k]'(by rw [htup.len54]; exact hk_lt) =
            (if h1 : 1 < (alg86L G Z r).length then ((alg86L G Z r)[1]'h1).1 else 0)) ∧
          (s.arrs 55)[k]'(by rw [htup.len55]; exact hk_lt) =
            (if h2 : 2 < (alg86L G Z r).length then ((alg86L G Z r)[2]'h2).1 else 0)) ↔
        uFin ∈ alg86U G Z r := by
      rw [htup_u.1, htup_u.2.1, htup_u.2.2.1, htup_u.2.2.2]
      dsimp [alg86U, alg86Tuple]
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Prod.mk.injEq]
      tauto
    have hr4₁₁_U : s₁₁.regs 4 = if uFin ∈ alg86U G Z r then 1 else 0 := by
      rw [hr4₁₁]
      by_cases hU : uFin ∈ alg86U G Z r
      · rw [ite_eq_left (hmem_iff.mpr hU), ite_eq_left hU]
      · rw [ite_eq_right (fun h => hU (hmem_iff.mp h)), ite_eq_right hU]
    have hr4₁₁_w : s₁₁.regs 4 < 2 ^ w := by rw [hr4₁₁_U]; split_ifs <;> omega
    let s₁₂ := s₁₁.writeArr 12 k (s₁₁.regs 4)
    have hex₁₂ : Exec w (.write 12 (.reg 2) (.reg 4)) s₁₁ s₁₂ 3 :=
      .write (by simp [Expr.eval, checkWord, hr2₁₁, hk_w])
        (by simp [Expr.eval, checkWord, hr4₁₁_w])
        (by rw [harr₁₁_eq, h12_len]; exact hk_lt)
    have hreg₁₂ : ∀ reg : Reg, reg ≠ 3 → reg ≠ 4 → s₁₂.regs reg = s.regs reg := by
      intro reg h3 h4
      change s₁₁.regs reg = s.regs reg
      rw [hreg₁₁ reg h4, State.setReg_regs_ne _ _ h3,
          hreg₉ reg h4, State.setReg_regs_ne _ _ h3,
          hreg₇ reg h4, State.setReg_regs_ne _ _ h3,
          hreg₅ reg h4, State.setReg_regs_ne _ _ h3]
      exact hreg₃ reg h3 h4
    let s₁₃ := s₁₂.setReg 2 (k + 1)
    have hex_inc : Exec w (.assign 2 (.op .add (.reg 2) (.const 1))) s₁₂ s₁₃ 4 :=
      .assign (by simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord,
        hreg₁₂ 2 (by decide) (by decide), hr2, hk_w, hw, show k + 1 < 2 ^ w by omega])
    have harr₁₃_ne : ∀ a : Arr, a ≠ 12 → s₁₃.arrs a = s.arrs a := by
      intro a ha
      simp [s₁₃, s₁₂, State.writeArr_arrs_ne _ _ _ ha, harr₁₁_eq]
    have h12_len₁₃ : (s₁₃.arrs 12).length = n := by
      simp [s₁₃, s₁₂, State.writeArr, harr₁₁_eq, h12_len]
    have h12_arr₁₃ : s₁₃.arrs 12 = (s.arrs 12).set k (if uFin ∈ alg86U G Z r then 1 else 0) := by
      simp [s₁₃, s₁₂, State.writeArr, harr₁₁_eq, hr4₁₁_U]
    have h12_val₁₃ : ∀ u : Fin n, u.1 < k + 1 →
        (s₁₃.arrs 12)[u.1]'(by omega) = if u ∈ alg86U G Z r then 1 else 0 := by
      intro u hu
      simp only [h12_arr₁₃]
      by_cases huk : u.1 = k
      · have hu_eq : u = uFin := Fin.ext huk
        subst hu_eq
        simp [uFin, List.getElem_set_self]
      · rw [List.getElem_set_ne (Ne.symm huk)]
        exact h12_val u (by omega)
    rcases ih (k + 1) (by omega) (s := s₁₃)
        (hZ.of_arr_eq (harr₁₃_ne 14 (by decide)))
        (htup.of_arrs_eq (harr₁₃_ne 52 (by decide)) (harr₁₃_ne 53 (by decide))
          (harr₁₃_ne 54 (by decide)) (harr₁₃_ne 55 (by decide)))
        h12_len₁₃ h12_val₁₃
        (by
          change (s₁₂.setReg 2 (k + 1)).regs 14 = n
          rw [State.setReg_regs_ne _ _ (by decide), hreg₁₂ 14 (by decide) (by decide), hr14])
        rfl
        (by
          change (s₁₂.setReg 2 (k + 1)).regs 5 = _
          rw [State.setReg_regs_ne _ _ (by decide), hreg₁₂ 5 (by decide) (by decide), hr5])
        (by
          change (s₁₂.setReg 2 (k + 1)).regs 6 = _
          rw [State.setReg_regs_ne _ _ (by decide), hreg₁₂ 6 (by decide) (by decide), hr6])
        (by
          change (s₁₂.setReg 2 (k + 1)).regs 7 = _
          rw [State.setReg_regs_ne _ _ (by decide), hreg₁₂ 7 (by decide) (by decide), hr7])
        (by
          change (s₁₂.setReg 2 (k + 1)).regs 8 = _
          rw [State.setReg_regs_ne _ _ (by decide), hreg₁₂ 8 (by decide) (by decide), hr8]) with
      ⟨s₁₄, t₁₄, hex₁₄, ht₁₄, hU₁₄, harr₁₄, hreg₁₄⟩
    have hex_b : Exec w buildUBitSetBody s s₁₂
        (2 + (3 + (t₃ + (3 + (t₅ + (3 + (t₇ + (3 + (t₉ + (3 + (t₁₁ + 3))))))))))) :=
      .seq hex₁ (.seq hex₂ (.seq hex₃ (.seq hex₄ (.seq hex₅
        (.seq hex₆ (.seq hex₇ (.seq hex₈ (.seq hex₉ (.seq hex₁₀ (.seq hex₁₁ hex₁₂))))))))))
    refine ⟨s₁₄, 3 + ((2 + (3 + (t₃ + (3 + (t₅ + (3 + (t₇ + (3 + (t₉ + (3 + (t₁₁ + 3))))))))))) + 4) + t₁₄,
      .while_true hcond (by omega) (.seq hex_b hex_inc) hex₁₄,
      by omega, hU₁₄,
      fun a ha => by rw [harr₁₄ a ha, harr₁₃_ne a ha],
      fun reg h2 h3 h4 => by
        rw [hreg₁₄ reg h2 h3 h4]
        change (s₁₂.setReg 2 (k + 1)).regs reg = s.regs reg
        rw [State.setReg_regs_ne _ _ h2]
        exact hreg₁₂ reg h3 h4⟩

theorem buildUBitSetProg_exec {w n : ℕ} (G : SimpleGraph (Fin n))
    (Z : Finset (Fin n)) (r : Fin n)
    (hw : 1 < 2 ^ w) (hn_w : n < 2 ^ w) {s : State}
    (hZ : IsBitSet Z 14 s)
    (htup : HasAlg86Tuples G Z s)
    (hr14 : s.regs 14 = n)
    (hr20 : s.regs 20 = r.1) :
    ∃ s' t,
      Exec w buildUBitSetProg s s' t ∧
      t ≤ 53 * n + 18 ∧
      IsBitSet (alg86U G Z r) 12 s' ∧
      (∀ a : Arr, a ≠ 12 → s'.arrs a = s.arrs a) ∧
      (∀ reg : Reg, reg ≠ 2 → reg ≠ 3 → reg ≠ 4 → reg ≠ 5 →
        reg ≠ 6 → reg ≠ 7 → reg ≠ 8 → s'.regs reg = s.regs reg) := by
  have h0_w : 0 < 2 ^ w := by omega
  have hr_lt : r.1 < n := r.2
  have hr_w : r.1 < 2 ^ w := by omega
  have htup_r := htup.val r hr_lt
  have hLr_le : (alg86L G Z r).length ≤ n :=
    (List.length_filter_le _ _).trans (by simp)
  have hc0_w : (s.arrs 52)[r.1]'(by rw [htup.len52]; exact hr_lt) < 2 ^ w := by
    rw [htup_r.1]; omega
  have hc1_w : (s.arrs 53)[r.1]'(by rw [htup.len53]; exact hr_lt) < 2 ^ w := by
    rw [htup_r.2.1]; split_ifs with h0
    · have := ((alg86L G Z r)[0]'h0).2; omega
    · omega
  have hc2_w : (s.arrs 54)[r.1]'(by rw [htup.len54]; exact hr_lt) < 2 ^ w := by
    rw [htup_r.2.2.1]; split_ifs with h1
    · have := ((alg86L G Z r)[1]'h1).2; omega
    · omega
  have hc3_w : (s.arrs 55)[r.1]'(by rw [htup.len55]; exact hr_lt) < 2 ^ w := by
    rw [htup_r.2.2.2]; split_ifs with h2
    · have := ((alg86L G Z r)[2]'h2).2; omega
    · omega
  let s₁ := s.setArr 12 (List.replicate n 0)
  have hex₁ : Exec w (.alloc 12 (.reg 14)) s s₁ (1 + n) :=
    .alloc (by simp [Expr.eval, checkWord, hr14, hn_w])
  let s₂ := s₁.setReg 5 ((s.arrs 52)[r.1]'(by rw [htup.len52]; exact hr_lt))
  have hex₂ : Exec w (.assign 5 (.read 52 (.reg 20))) s₁ s₂ 3 :=
    .assign (by simp [s₁, State.setArr, Expr.eval, checkWord, hr20, hr_w, htup.len52, hr_lt, hc0_w])
  let s₃ := s₂.setReg 6 ((s.arrs 53)[r.1]'(by rw [htup.len53]; exact hr_lt))
  have hex₃ : Exec w (.assign 6 (.read 53 (.reg 20))) s₂ s₃ 3 :=
    .assign (by simp [s₂, s₁, State.setReg, State.setArr, Expr.eval, checkWord, hr20, hr_w, htup.len53, hr_lt, hc1_w])
  let s₄ := s₃.setReg 7 ((s.arrs 54)[r.1]'(by rw [htup.len54]; exact hr_lt))
  have hex₄ : Exec w (.assign 7 (.read 54 (.reg 20))) s₃ s₄ 3 :=
    .assign (by simp [s₃, s₂, s₁, State.setReg, State.setArr, Expr.eval, checkWord, hr20, hr_w, htup.len54, hr_lt, hc2_w])
  let s₅ := s₄.setReg 8 ((s.arrs 55)[r.1]'(by rw [htup.len55]; exact hr_lt))
  have hex₅ : Exec w (.assign 8 (.read 55 (.reg 20))) s₄ s₅ 3 :=
    .assign (by simp [s₄, s₃, s₂, s₁, State.setReg, State.setArr, Expr.eval, checkWord, hr20, hr_w, htup.len55, hr_lt, hc3_w])
  let s₆ := s₅.setReg 2 0
  have hex₆ : Exec w (.assign 2 (.const 0)) s₅ s₆ 2 :=
    .assign (by simp [Expr.eval, checkWord, h0_w])
  have harr₆ : ∀ a : Arr, a ≠ 12 → s₆.arrs a = s.arrs a := by
    intro a ha; simp [s₆, s₅, s₄, s₃, s₂, s₁, State.setArr, ha]
  rcases buildUBitSetLoop_exec G Z r hw hn_w n 0 (by omega) (s := s₆)
      (hZ.of_arr_eq (harr₆ 14 (by decide)))
      (htup.of_arrs_eq (harr₆ 52 (by decide)) (harr₆ 53 (by decide))
        (harr₆ 54 (by decide)) (harr₆ 55 (by decide)))
      (by simp [s₆, s₅, s₄, s₃, s₂, s₁, State.setArr])
      (fun u hu => by omega)
      (by simp [s₆, s₅, s₄, s₃, s₂, s₁, State.setReg, hr14])
      rfl
      (by simp [s₆, s₅, s₄, s₃, s₂, State.setReg, htup_r.1])
      (by simp [s₆, s₅, s₄, s₃, State.setReg, htup_r.2.1])
      (by simp [s₆, s₅, s₄, s₃, State.setReg, htup_r.2.2.1])
      (by simp [s₆, s₅, s₄, s₃, State.setReg, htup_r.2.2.2]) with
    ⟨s₇, t₇, hex₇, ht₇, hU₇, harr₇, hreg₇⟩
  refine ⟨s₇, (1 + n) + (3 + (3 + (3 + (3 + (2 + t₇))))),
    .seq hex₁ (.seq hex₂ (.seq hex₃ (.seq hex₄ (.seq hex₅ (.seq hex₆ hex₇))))),
    by omega, hU₇,
    fun a ha => by rw [harr₇ a ha, harr₆ a ha],
    fun reg h2 h3 h4 h5 h6 h7 h8 => by
      rw [hreg₇ reg h2 h3 h4]
      simp [s₆, s₅, s₄, s₃, s₂, s₁, State.setReg, h2, h5, h6, h7, h8]⟩

/-- Pure list of Case (c) subgraphs `(U ∪ X, edges)` emitted by Pass D1 for `r < k`
with `r ∉ Z` and `r = min U`. -/
noncomputable def alg86CaseCPairs {n : ℕ} (G : SimpleGraph (Fin n))
    (Z : Finset (Fin n)) (edges₀ : List (Fin n × Fin n)) :
    ℕ → List (Finset (Fin n) × List (Fin n × Fin n))
  | 0 => []
  | k + 1 =>
    let prev := alg86CaseCPairs G Z edges₀ k
    if hk : k < n then
      let r : Fin n := ⟨k, hk⟩
      let U := alg86U G Z r
      let X := alg86X G Z r
      let incX := decide ((alg86L G Z r).length = 2)
      if r ∉ Z ∧ (∀ u ∈ U, r.1 ≤ u.1) then
        prev ++ [(U ∪ X, edges₀.filter (alg86KeepEdge U X incX))]
      else
        prev
    else
      prev

/-- Pure set of marked edge indices accumulated by Pass D1 up to vertex `k`. -/
noncomputable def alg86CaseCMarked {n : ℕ} (G : SimpleGraph (Fin n))
    (Z : Finset (Fin n)) (edges₀ : List (Fin n × Fin n))
    (M₀ : Finset (Fin edges₀.length)) : ℕ → Finset (Fin edges₀.length)
  | 0 => M₀
  | k + 1 =>
    let prev := alg86CaseCMarked G Z edges₀ M₀ k
    if hk : k < n then
      let r : Fin n := ⟨k, hk⟩
      let U := alg86U G Z r
      let X := alg86X G Z r
      if (r ∉ Z ∧ (∀ u ∈ U, r.1 ≤ u.1)) ∧ (alg86L G Z r).length = 2 then
        prev ∪ alg86XEdgeIndices edges₀ X
      else
        prev
    else
      prev

theorem length_alg86CaseCPairs_le {n : ℕ} (G : SimpleGraph (Fin n))
    (Z : Finset (Fin n)) (edges₀ : List (Fin n × Fin n)) :
    ∀ k, (alg86CaseCPairs G Z edges₀ k).length ≤ k
  | 0 => by simp [alg86CaseCPairs]
  | k + 1 => by
    have ih := length_alg86CaseCPairs_le G Z edges₀ k
    dsimp [alg86CaseCPairs]
    split_ifs <;> simp <;> omega

theorem length_flatMap_alg86CaseCPairs_le {n : ℕ} (G : SimpleGraph (Fin n))
    (Z : Finset (Fin n)) (edges₀ : List (Fin n × Fin n)) :
    ∀ k, ((alg86CaseCPairs G Z edges₀ k).flatMap (fun p => encAlg86Subgraph p.1 p.2)).length ≤
      k * (n + 2 + 2 * edges₀.length)
  | 0 => by simp [alg86CaseCPairs]
  | k + 1 => by
    have ih := length_flatMap_alg86CaseCPairs_le G Z edges₀ k
    dsimp [alg86CaseCPairs]
    rw [Nat.add_one_mul k (n + 2 + 2 * edges₀.length)]
    split_ifs
    · rw [List.flatMap_append, List.length_append]
      simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil, length_encAlg86Subgraph]
      have hlen_f : (edges₀.filter (alg86KeepEdge (alg86U G Z ⟨k, ‹_›⟩) (alg86X G Z ⟨k, ‹_›⟩)
          (decide ((alg86L G Z ⟨k, ‹_›⟩).length = 2)))).length ≤
          edges₀.length := List.length_filter_le _ _
      omega
    · omega
    · omega

/-- Loop body of `alg86CaseCPassProg` (Pass D1). -/
def alg86CaseCBody : Cmd :=
  .seq (.assign 21 (.read 14 (.reg 20)))
    (.ite (.op .eq (.reg 21) (.const 0))
      (.seq computeKAndExtNhdProg
        (.seq buildUBitSetProg
          (.seq checkMinInKProg
            (.ite (.op .eq (.reg 23) (.const 0))
              .skip
              (.seq (.assign 21 (.read 52 (.reg 20)))
                (.seq (.ite (.op .eq (.reg 21) (.const 2))
                    (.assign 28 (.const 1))
                    (.assign 28 (.const 0)))
                  (.seq emitUXSubgraphProg
                    (.ite (.op .eq (.reg 28) (.const 0))
                      .skip
                      markXEdgesProg))))))))
      .skip)

/-- Pass D1 of Algorithm (8.6): emits merged Case (c) subgraphs `(U ∪ X, edges)` for each
nonempty attachment class `U` (indexed by its minimum vertex `r ∉ Z`), and marks edges of `G|Z`
when `|X| = 2`. -/
def alg86CaseCPassProg : Cmd :=
  .seq (.assign 20 (.const 0))
    (forUp 20 (.reg 14) alg86CaseCBody)

private theorem alg86CaseCLoop_exec {w n cap : ℕ} (G : SimpleGraph (Fin n))
    (lists_G lists_Y : Fin n → List ℕ) (Z : Finset (Fin n))
    (edges₀ : List (Fin n × Fin n)) (M₀ : Finset (Fin edges₀.length))
    (pref₀ : List ℕ) (cnt₀ : ℕ)
    (htot_G : totalAdjEntries lists_G ≤ 2 * edges₀.length)
    (htot_Y : totalAdjEntries lists_Y ≤ 2 * edges₀.length)
    (hcap_le : pref₀.length + n * (n + 2 + 2 * edges₀.length) ≤ cap)
    (hw3 : 3 < 2 ^ w) (hn_w : n < 2 ^ w) (hm8_w : 8 + 2 * edges₀.length < 2 ^ w)
    (hcap_w : cap < 2 ^ w) (hcnt_w : cnt₀ + n < 2 ^ w)
    (rem k : ℕ) (hrem : k + rem = n) {s : State}
    (hin : s.arrs 0 = [n, edges₀.length] ++ flatEdges edges₀)
    (hadj_G : IsAdjList G 3 4 5 lists_G s)
    (hent_G : (s.arrs 5).length < 2 ^ w)
    (hadj_Y : IsAdjList (restrictGraph G (Finset.univ \ Z)) 6 7 8 lists_Y s)
    (hent_Y : (s.arrs 8).length < 2 ^ w)
    (hZ : IsBitSet Z 14 s)
    (htup : HasAlg86Tuples G Z s)
    (hM : IsBitSet (alg86CaseCMarked G Z edges₀ M₀ k) 51 s)
    (hout : s.arrs outArr =
      (pref₀ ++ (alg86CaseCPairs G Z edges₀ k).flatMap (fun p => encAlg86Subgraph p.1 p.2)) ++
        List.replicate (cap - (pref₀ ++ (alg86CaseCPairs G Z edges₀ k).flatMap (fun p => encAlg86Subgraph p.1 p.2)).length) 0)
    (hr1 : s.regs 1 = edges₀.length)
    (hr14 : s.regs 14 = n)
    (hr20 : s.regs 20 = k)
    (hr25 : s.regs 25 = (pref₀ ++ (alg86CaseCPairs G Z edges₀ k).flatMap (fun p => encAlg86Subgraph p.1 p.2)).length)
    (hr26 : s.regs 26 = cnt₀ + (alg86CaseCPairs G Z edges₀ k).length) :
    ∃ s' t,
      Exec w (forUp 20 (.reg 14) alg86CaseCBody) s s' t ∧
      t ≤ rem * (163 * n + 217 * edges₀.length + 181) + 3 ∧
      IsBitSet (alg86CaseCMarked G Z edges₀ M₀ n) 51 s' ∧
      s'.arrs outArr =
        (pref₀ ++ (alg86CaseCPairs G Z edges₀ n).flatMap (fun p => encAlg86Subgraph p.1 p.2)) ++
          List.replicate (cap - (pref₀ ++ (alg86CaseCPairs G Z edges₀ n).flatMap (fun p => encAlg86Subgraph p.1 p.2)).length) 0 ∧
      s'.regs 25 = (pref₀ ++ (alg86CaseCPairs G Z edges₀ n).flatMap (fun p => encAlg86Subgraph p.1 p.2)).length ∧
      s'.regs 26 = cnt₀ + (alg86CaseCPairs G Z edges₀ n).length ∧
      (∀ a : Arr, a ≠ outArr → a ≠ 12 → a ≠ 13 → a ≠ 15 → a ≠ 17 → a ≠ 18 → a ≠ 51 → s'.arrs a = s.arrs a) ∧
      (∀ reg : Reg, reg ≠ 2 → reg ≠ 3 → reg ≠ 4 → reg ≠ 5 → reg ≠ 6 → reg ≠ 7 → reg ≠ 8 → reg ≠ 9 →
        reg ≠ 20 → reg ≠ 21 → reg ≠ 22 → reg ≠ 23 → reg ≠ 25 → reg ≠ 26 → reg ≠ 28 → s'.regs reg = s.regs reg) := by
  induction rem generalizing k s with
  | zero =>
    have hk_eq : k = n := by omega
    subst hk_eq
    have h0_w : 0 < 2 ^ w := by omega
    have hcond : (Expr.op .lt (.reg 20) (.reg 14)).eval w s = some 0 := by
      simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hr20, hr14, hn_w, h0_w]
    exact ⟨s, 3, .while_false hcond, by omega, hM, hout, hr25, hr26,
      fun _ _ _ _ _ _ _ _ => rfl, fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ => rfl⟩
  | succ rem ih =>
    have hw : 1 < 2 ^ w := by omega
    have hw2 : 2 < 2 ^ w := by omega
    have hm3_w : 3 + 2 * edges₀.length < 2 ^ w := by omega
    have h0_w : 0 < 2 ^ w := by omega
    have hk_lt : k < n := by omega
    have hk_w : k < 2 ^ w := by omega
    let rFin : Fin n := ⟨k, hk_lt⟩
    let L_k := alg86CaseCPairs G Z edges₀ k
    let L_next := alg86CaseCPairs G Z edges₀ (k + 1)
    let M_k := alg86CaseCMarked G Z edges₀ M₀ k
    let M_next := alg86CaseCMarked G Z edges₀ M₀ (k + 1)
    let pref_k := pref₀ ++ L_k.flatMap (fun p => encAlg86Subgraph p.1 p.2)
    let pref_next := pref₀ ++ L_next.flatMap (fun p => encAlg86Subgraph p.1 p.2)
    have hcond : (Expr.op .lt (.reg 20) (.reg 14)).eval w s = some 1 := by
      simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hr20, hr14, hk_w, hn_w, hk_lt, hw]
    have hk_lt_14 : k < (s.arrs 14).length := by rw [hZ.1]; exact hk_lt
    have hval14 : (s.arrs 14)[k] = if rFin ∈ Z then 1 else 0 := hZ.getElem_eq_ite rFin
    have hval14_w : (s.arrs 14)[k] < 2 ^ w := by rw [hval14]; split_ifs <;> omega
    let s₁ := s.setReg 21 (s.arrs 14)[k]
    have hex₁ : Exec w (.assign 21 (.read 14 (.reg 20))) s s₁ 3 :=
      .assign (by simp [Expr.eval, checkWord, hr20, hk_w, hk_lt_14, hval14_w])
    have hex_body : ∃ s₂ t_b,
        Exec w (.ite (.op .eq (.reg 21) (.const 0))
          (.seq computeKAndExtNhdProg
            (.seq buildUBitSetProg
              (.seq checkMinInKProg
                (.ite (.op .eq (.reg 23) (.const 0))
                  .skip
                  (.seq (.assign 21 (.read 52 (.reg 20)))
                    (.seq (.ite (.op .eq (.reg 21) (.const 2))
                        (.assign 28 (.const 1))
                        (.assign 28 (.const 0)))
                      (.seq emitUXSubgraphProg
                        (.ite (.op .eq (.reg 28) (.const 0))
                          .skip
                          markXEdgesProg))))))))
          .skip) s₁ s₂ t_b ∧
        t_b ≤ 163 * n + 217 * edges₀.length + 171 ∧
        IsBitSet M_next 51 s₂ ∧
        s₂.arrs outArr = pref_next ++ List.replicate (cap - pref_next.length) 0 ∧
        s₂.regs 25 = pref_next.length ∧
        s₂.regs 26 = cnt₀ + L_next.length ∧
        (∀ a : Arr, a ≠ outArr → a ≠ 12 → a ≠ 13 → a ≠ 15 → a ≠ 17 → a ≠ 18 → a ≠ 51 → s₂.arrs a = s.arrs a) ∧
        (∀ reg : Reg, reg ≠ 2 → reg ≠ 3 → reg ≠ 4 → reg ≠ 5 → reg ≠ 6 → reg ≠ 7 → reg ≠ 8 → reg ≠ 9 →
          reg ≠ 21 → reg ≠ 22 → reg ≠ 23 → reg ≠ 25 → reg ≠ 26 → reg ≠ 28 → s₂.regs reg = s.regs reg) := by
      by_cases hrZ : rFin ∈ Z
      · have hcond_b : (Expr.op .eq (.reg 21) (.const 0)).eval w s₁ = some 0 := by
          simp [s₁, Expr.eval, BinOp.eval, BinOp.raw, checkWord, hval14, hrZ, h0_w, hw]
        have hL_next : L_next = L_k := by simp [L_next, L_k, alg86CaseCPairs, hk_lt, rFin, hrZ]
        have hM_next : M_next = M_k := by simp [M_next, M_k, alg86CaseCMarked, hk_lt, rFin, hrZ]
        have hpref_next : pref_next = pref_k := by simp [pref_next, pref_k, hL_next]
        refine ⟨s₁, 3 + 1, .ite_false hcond_b (.skip s₁), by omega,
          by rw [hM_next]; exact hM.of_arr_eq rfl,
          by simpa [s₁, hpref_next, pref_k] using hout,
          by simpa [s₁, State.setReg, hpref_next, pref_k] using hr25,
          by simpa [s₁, State.setReg, hL_next, L_k] using hr26,
          fun _ _ _ _ _ _ _ _ => rfl,
          fun reg _ _ _ _ _ _ _ _ h21 _ _ _ _ _ => by simp [s₁, State.setReg, h21]⟩
      · have hcond_b : (Expr.op .eq (.reg 21) (.const 0)).eval w s₁ = some 1 := by
          simp [s₁, Expr.eval, BinOp.eval, BinOp.raw, checkWord, hval14, hrZ, h0_w, hw]
        rcases computeKAndExtNhdProg_exec G lists_G lists_Y Z rFin htot_G htot_Y hw hn_w (s := s₁)
            (hadj_G.of_arrs_eq rfl rfl rfl) hent_G
            (hadj_Y.of_arrs_eq rfl rfl rfl) hent_Y
            (by simp [s₁, State.setReg, hr14])
            (by simp [s₁, State.setReg, hr20, rFin]) with
          ⟨s₂, t₂, hex₂, ht₂, _, hN₂, harr₂, hreg₂⟩
        have hr14₂ : s₂.regs 14 = n := by
          rw [hreg₂ 14 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]
          simp [s₁, State.setReg, hr14]
        have hr20₂ : s₂.regs 20 = rFin.1 := by
          rw [hreg₂ 20 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]
          simp [s₁, State.setReg, hr20, rFin]
        rcases buildUBitSetProg_exec G Z rFin hw hn_w
            (hZ.of_arr_eq (harr₂ 14 (by decide) (by decide) (by decide)))
            (htup.of_arrs_eq (harr₂ 52 (by decide) (by decide) (by decide))
              (harr₂ 53 (by decide) (by decide) (by decide))
              (harr₂ 54 (by decide) (by decide) (by decide))
              (harr₂ 55 (by decide) (by decide) (by decide)))
            hr14₂ hr20₂ with
          ⟨s₃, t₃, hex₃, ht₃, hU₃, harr₃, hreg₃⟩
        have hr20₃ : s₃.regs 20 = rFin.1 := by
          rw [hreg₃ 20 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]
          exact hr20₂
        rcases checkMinInKProg_exec (alg86U G Z rFin) rFin hw hn_w hU₃ hr20₃ with
          ⟨s₄, t₄, hex₄, ht₄, hr23₄, harr₄, hreg₄⟩
        have harr₄_ne : ∀ a : Arr, a ≠ 12 → a ≠ 13 → a ≠ 15 → s₄.arrs a = s.arrs a := by
          intro a h12 h13 h15
          rw [harr₄, harr₃ a h12, harr₂ a h12 h13 h15]
          rfl
        have hreg₄_ne : ∀ reg : Reg, reg ≠ 2 → reg ≠ 3 → reg ≠ 4 → reg ≠ 5 →
            reg ≠ 6 → reg ≠ 7 → reg ≠ 8 → reg ≠ 21 → reg ≠ 23 → s₄.regs reg = s.regs reg := by
          intro reg h2 h3 h4 h5 h6 h7 h8 h21 h23
          rw [hreg₄ reg h2 h3 h23, hreg₃ reg h2 h3 h4 h5 h6 h7 h8,
              hreg₂ reg h2 h3 h4 h5 h6 h7 h8]
          simp [s₁, State.setReg, h21]
        by_cases hmin : ∀ u ∈ alg86U G Z rFin, rFin.1 ≤ u.1
        · have hr23_val : s₄.regs 23 = 1 := by rw [hr23₄]; exact ite_eq_left hmin
          have hcond_m : (Expr.op .eq (.reg 23) (.const 0)).eval w s₄ = some 0 := by
            simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hr23_val, h0_w, hw]
          have hr20₄ : s₄.regs 20 = k := by
            rw [hreg₄_ne 20 (by decide) (by decide) (by decide) (by decide) (by decide)
                  (by decide) (by decide) (by decide) (by decide), hr20]
          have h52₄ : s₄.arrs 52 = s.arrs 52 := harr₄_ne 52 (by decide) (by decide) (by decide)
          have hLr_le : (alg86L G Z rFin).length ≤ n :=
            (List.length_filter_le _ _).trans (by simp)
          have hLr_w : (alg86L G Z rFin).length < 2 ^ w := by omega
          have hk_52 : k < (s₄.arrs 52).length := by rw [h52₄, htup.len52]; exact hk_lt
          have hval52 : (s₄.arrs 52)[k]'hk_52 = (alg86L G Z rFin).length := by
            simp only [h52₄]; exact (htup.val rFin hk_lt).1
          let s₅ := s₄.setReg 21 (alg86L G Z rFin).length
          have hex₅ : Exec w (.assign 21 (.read 52 (.reg 20))) s₄ s₅ 3 :=
            .assign (by simp [Expr.eval, checkWord, hr20₄, hk_w, hk_52, hval52, hLr_w])
          let incX := decide ((alg86L G Z rFin).length = 2)
          have hex_incX : ∃ s₆ t₆,
              Exec w (.ite (.op .eq (.reg 21) (.const 2))
                (.assign 28 (.const 1))
                (.assign 28 (.const 0))) s₅ s₆ t₆ ∧
              t₆ ≤ 5 ∧
              s₆.regs 28 = (if incX then 1 else 0) ∧
              s₆.arrs = s₄.arrs ∧
              (∀ reg : Reg, reg ≠ 21 → reg ≠ 28 → s₆.regs reg = s₄.regs reg) := by
            by_cases hlen2 : (alg86L G Z rFin).length = 2
            · have hcond_2 : (Expr.op .eq (.reg 21) (.const 2)).eval w s₅ = some 1 := by
                simp [s₅, Expr.eval, BinOp.eval, BinOp.raw, checkWord, hlen2, hw2, hw]
              refine ⟨s₅.setReg 28 1, 3 + 2,
                .ite_true hcond_2 (by omega) (.assign (by simp [Expr.eval, checkWord, hw])),
                by omega, by simp [State.setReg, incX, hlen2], rfl,
                fun reg h21 h28 => by simp [s₅, State.setReg, h21, h28]⟩
            · have hcond_2 : (Expr.op .eq (.reg 21) (.const 2)).eval w s₅ = some 0 := by
                simp [s₅, Expr.eval, BinOp.eval, BinOp.raw, checkWord, hlen2, hLr_w, hw2, h0_w]
              refine ⟨s₅.setReg 28 0, 3 + 2,
                .ite_false hcond_2 (.assign (by simp [Expr.eval, checkWord, h0_w])),
                by omega, by simp [State.setReg, incX, hlen2], rfl,
                fun reg h21 h28 => by simp [s₅, State.setReg, h21, h28]⟩
          rcases hex_incX with ⟨s₆, t₆, hex₆, ht₆, hr28₆, harr₆, hreg₆⟩
          have hX₆ : IsBitSet (alg86X G Z rFin) 13 s₆ := by
            rw [alg86X_eq_extNeighborhood_of_not_mem G Z hrZ]
            exact hN₂.of_arr_eq (by rw [harr₆, harr₄, harr₃ 13 (by decide)])
          have hlen_Lk : (L_k.flatMap (fun p => encAlg86Subgraph p.1 p.2)).length ≤
              k * (n + 2 + 2 * edges₀.length) :=
            length_flatMap_alg86CaseCPairs_le G Z edges₀ k
          have h1_mul : (k + 1) * (n + 2 + 2 * edges₀.length) ≤ n * (n + 2 + 2 * edges₀.length) :=
            Nat.mul_le_mul_right _ (by omega)
          have h1_eq : (k + 1) * (n + 2 + 2 * edges₀.length) =
              k * (n + 2 + 2 * edges₀.length) + (n + 2 + 2 * edges₀.length) :=
            Nat.add_one_mul k _
          have hcap_k : pref_k.length + (n + 2 + 2 * edges₀.length) ≤ cap := by
            have : pref_k.length = pref₀.length + (L_k.flatMap (fun p => encAlg86Subgraph p.1 p.2)).length := by
              simp [pref_k]
            omega
          have hcnt_k : (cnt₀ + L_k.length) + 1 < 2 ^ w := by
            have : L_k.length ≤ k := length_alg86CaseCPairs_le G Z edges₀ k
            omega
          rcases emitUXSubgraphProg_exec (alg86U G Z rFin) (alg86X G Z rFin) incX edges₀
              pref_k hcap_k hw3 hm8_w hcap_w (cnt := cnt₀ + L_k.length) hcnt_k (s := s₆)
              (by rw [harr₆, harr₄_ne 0 (by decide) (by decide) (by decide), hin])
              (hU₃.of_arr_eq (by rw [harr₆, harr₄]))
              hX₆
              (by rw [harr₆, harr₄_ne outArr (by decide) (by decide) (by decide)]; exact hout)
              (by
                rw [hreg₆ 1 (by decide) (by decide),
                    hreg₄_ne 1 (by decide) (by decide) (by decide) (by decide) (by decide)
                      (by decide) (by decide) (by decide) (by decide), hr1])
              (by
                rw [hreg₆ 14 (by decide) (by decide),
                    hreg₄_ne 14 (by decide) (by decide) (by decide) (by decide) (by decide)
                      (by decide) (by decide) (by decide) (by decide), hr14])
              (by
                rw [hreg₆ 25 (by decide) (by decide),
                    hreg₄_ne 25 (by decide) (by decide) (by decide) (by decide) (by decide)
                      (by decide) (by decide) (by decide) (by decide), hr25])
              (by
                rw [hreg₆ 26 (by decide) (by decide),
                    hreg₄_ne 26 (by decide) (by decide) (by decide) (by decide) (by decide)
                      (by decide) (by decide) (by decide) (by decide), hr26])
              hr28₆ with
            ⟨s₇, t₇, hex₇, ht₇, hout₇, hr25₇, hr26₇, harr₇, hreg₇⟩
          have hr28₇ : s₇.regs 28 = (if incX then 1 else 0) := by
            rw [hreg₇ 28 (by decide) (by decide) (by decide) (by decide) (by decide)
                  (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), hr28₆]
          have hM₇ : IsBitSet M_k 51 s₇ :=
            hM.of_arr_eq (by rw [harr₇ 51 (by decide) (by decide) (by decide), harr₆,
              harr₄_ne 51 (by decide) (by decide) (by decide)])
          have hX₇ : IsBitSet (alg86X G Z rFin) 13 s₇ :=
            hX₆.of_arr_eq (harr₇ 13 (by decide) (by decide) (by decide))
          have hin₇ : s₇.arrs 0 = [n, edges₀.length] ++ flatEdges edges₀ := by
            rw [harr₇ 0 (by decide) (by decide) (by decide), harr₆,
                harr₄_ne 0 (by decide) (by decide) (by decide), hin]
          have hr1₇ : s₇.regs 1 = edges₀.length := by
            rw [hreg₇ 1 (by decide) (by decide) (by decide) (by decide) (by decide)
                  (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
                hreg₆ 1 (by decide) (by decide),
                hreg₄_ne 1 (by decide) (by decide) (by decide) (by decide) (by decide)
                  (by decide) (by decide) (by decide) (by decide), hr1]
          have hex_mark : ∃ s₈ t₈,
              Exec w (.ite (.op .eq (.reg 28) (.const 0)) .skip markXEdgesProg) s₇ s₈ t₈ ∧
              t₈ ≤ 33 * edges₀.length + 8 ∧
              IsBitSet M_next 51 s₈ ∧
              (∀ a : Arr, a ≠ 51 → s₈.arrs a = s₇.arrs a) ∧
              (∀ reg : Reg, reg ≠ 2 → reg ≠ 3 → reg ≠ 4 → reg ≠ 5 → reg ≠ 6 → s₈.regs reg = s₇.regs reg) := by
            by_cases hlen2 : (alg86L G Z rFin).length = 2
            · have hincX_true : incX = true := decide_eq_true hlen2
              have hcond_mk : (Expr.op .eq (.reg 28) (.const 0)).eval w s₇ = some 0 := by
                simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hr28₇, hincX_true, h0_w, hw]
              rcases markXEdgesProg_exec edges₀ (alg86X G Z rFin) M_k hw3 hn_w hm3_w
                  hin₇ hX₇ hM₇ hr1₇ with
                ⟨s₈, t₈, hex₈, ht₈, hM₈, harr₈, hreg₈⟩
              have hM_next : M_next = M_k ∪ alg86XEdgeIndices edges₀ (alg86X G Z rFin) := by
                dsimp [M_next, M_k, alg86CaseCMarked]
                rw [dite_eq_left hk_lt]
                exact ite_eq_left ⟨⟨hrZ, hmin⟩, hlen2⟩
              refine ⟨s₈, 3 + t₈, .ite_false hcond_mk hex₈, by omega,
                by rw [hM_next]; exact hM₈, harr₈, hreg₈⟩
            · have hincX_false : incX = false := decide_eq_false hlen2
              have hcond_mk : (Expr.op .eq (.reg 28) (.const 0)).eval w s₇ = some 1 := by
                simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hr28₇, hincX_false, h0_w, hw]
              have hM_next : M_next = M_k := by
                dsimp [M_next, M_k, alg86CaseCMarked]
                rw [dite_eq_left hk_lt]
                exact ite_eq_right (fun h => hlen2 h.2)
              refine ⟨s₇, 3 + 1, .ite_true hcond_mk (by omega) (.skip s₇), by omega,
                by rw [hM_next]; exact hM₇, fun _ _ => rfl, fun _ _ _ _ _ _ => rfl⟩
          rcases hex_mark with ⟨s₈, t₈, hex₈, ht₈, hM₈, harr₈, hreg₈⟩
          have hL_next : L_next = L_k ++ [(alg86U G Z rFin ∪ alg86X G Z rFin,
              edges₀.filter (alg86KeepEdge (alg86U G Z rFin) (alg86X G Z rFin) incX))] := by
            dsimp [L_next, L_k, alg86CaseCPairs]
            rw [dite_eq_left hk_lt]
            exact ite_eq_left ⟨hrZ, hmin⟩
          have hpref_next : pref_next = pref_k ++ encAlg86Subgraph (alg86U G Z rFin ∪ alg86X G Z rFin)
              (edges₀.filter (alg86KeepEdge (alg86U G Z rFin) (alg86X G Z rFin) incX)) := by
            simp [pref_next, pref_k, hL_next, List.flatMap_append, List.append_assoc]
          have hcnt_next : cnt₀ + L_next.length = (cnt₀ + L_k.length) + 1 := by
            simp [hL_next, List.length_append]
            omega
          refine ⟨s₈, 3 + (t₂ + (t₃ + (t₄ + (3 + (3 + (t₆ + (t₇ + t₈))))))),
            .ite_true hcond_b (by omega)
              (.seq hex₂ (.seq hex₃ (.seq hex₄ (.ite_false hcond_m
                (.seq hex₅ (.seq hex₆ (.seq hex₇ hex₈))))))),
            by omega, hM₈,
            by rw [harr₈ outArr (by decide), hpref_next]; exact hout₇,
            by rw [hreg₈ 25 (by decide) (by decide) (by decide) (by decide) (by decide), hpref_next]; exact hr25₇,
            by rw [hreg₈ 26 (by decide) (by decide) (by decide) (by decide) (by decide), hcnt_next]; exact hr26₇,
            fun a hout h12 h13 h15 h17 h18 h51 => by
              rw [harr₈ a h51, harr₇ a hout h17 h18, harr₆, harr₄_ne a h12 h13 h15],
            fun reg h2 h3 h4 h5 h6 h7 h8 h9 h21 h22 h23 h25 h26 h28 => by
              rw [hreg₈ reg h2 h3 h4 h5 h6, hreg₇ reg h2 h3 h4 h5 h6 h7 h8 h9 h21 h22 h25 h26,
                  hreg₆ reg h21 h28, hreg₄_ne reg h2 h3 h4 h5 h6 h7 h8 h21 h23]⟩
        · have hr23_val : s₄.regs 23 = 0 := by rw [hr23₄]; exact ite_eq_right hmin
          have hcond_m : (Expr.op .eq (.reg 23) (.const 0)).eval w s₄ = some 1 := by
            simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hr23_val, h0_w, hw]
          have hL_next : L_next = L_k := by
            dsimp [L_next, L_k, alg86CaseCPairs]
            rw [dite_eq_left hk_lt]
            exact ite_eq_right (fun h => hmin h.2)
          have hM_next : M_next = M_k := by
            dsimp [M_next, M_k, alg86CaseCMarked]
            rw [dite_eq_left hk_lt]
            exact ite_eq_right (fun h => hmin h.1.2)
          have hpref_next : pref_next = pref_k := by simp [pref_next, pref_k, hL_next]
          refine ⟨s₄, 3 + (t₂ + (t₃ + (t₄ + (3 + 1)))),
            .ite_true hcond_b (by omega)
              (.seq hex₂ (.seq hex₃ (.seq hex₄ (.ite_true hcond_m (by omega) (.skip s₄))))),
            by omega,
            by rw [hM_next]; exact hM.of_arr_eq (harr₄_ne 51 (by decide) (by decide) (by decide)),
            by rw [harr₄_ne outArr (by decide) (by decide) (by decide), hpref_next]; exact hout,
            by
              rw [hreg₄_ne 25 (by decide) (by decide) (by decide) (by decide) (by decide)
                    (by decide) (by decide) (by decide) (by decide), hpref_next]
              exact hr25,
            by
              rw [hreg₄_ne 26 (by decide) (by decide) (by decide) (by decide) (by decide)
                    (by decide) (by decide) (by decide) (by decide), hL_next]
              exact hr26,
            fun a _ h12 h13 h15 _ _ _ => harr₄_ne a h12 h13 h15,
            fun reg h2 h3 h4 h5 h6 h7 h8 _ h21 _ h23 _ _ _ =>
              hreg₄_ne reg h2 h3 h4 h5 h6 h7 h8 h21 h23⟩
    rcases hex_body with ⟨s₂, t_b, hex_b, ht_b, hM₂, hout₂, hr25₂, hr26₂, harr₂, hreg₂⟩
    have hr20₂ : s₂.regs 20 = k := by
      rw [hreg₂ 20 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
            (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), hr20]
    let s₃ := s₂.setReg 20 (k + 1)
    have hex_inc : Exec w (.assign 20 (.op .add (.reg 20) (.const 1))) s₂ s₃ 4 :=
      .assign (by simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hr20₂, hk_w, hw,
        show k + 1 < 2 ^ w by omega])
    have harr₂_lt : ∀ a : Arr, a ≠ outArr → a < 12 → s₂.arrs a = s.arrs a := by
      intro a hout ha
      dsimp [Arr, outArr] at *
      exact harr₂ a hout (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
    have harr₂_tup : ∀ a : Arr, 52 ≤ a → s₂.arrs a = s.arrs a := by
      intro a ha
      dsimp [Arr, outArr] at *
      exact harr₂ a (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
    rcases ih (k + 1) (by omega) (s := s₃)
        (by rw [show s₃.arrs 0 = s₂.arrs 0 from rfl, harr₂_lt 0 (by decide) (by decide), hin])
        (hadj_G.of_arrs_eq (harr₂_lt 3 (by decide) (by decide))
          (harr₂_lt 4 (by decide) (by decide)) (harr₂_lt 5 (by decide) (by decide)))
        (by simp [s₃, harr₂_lt 5 (by decide) (by decide), hent_G])
        (hadj_Y.of_arrs_eq (harr₂_lt 6 (by decide) (by decide))
          (harr₂_lt 7 (by decide) (by decide)) (harr₂_lt 8 (by decide) (by decide)))
        (by simp [s₃, harr₂_lt 8 (by decide) (by decide), hent_Y])
        (hZ.of_arr_eq (harr₂ 14 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)))
        (htup.of_arrs_eq (harr₂_tup 52 (by decide)) (harr₂_tup 53 (by decide))
          (harr₂_tup 54 (by decide)) (harr₂_tup 55 (by decide)))
        (hM₂.of_arr_eq rfl)
        hout₂
        (by
          change (s₂.setReg 20 (k + 1)).regs 1 = edges₀.length
          rw [State.setReg_regs_ne _ _ (by decide),
              hreg₂ 1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
                (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), hr1])
        (by
          change (s₂.setReg 20 (k + 1)).regs 14 = n
          rw [State.setReg_regs_ne _ _ (by decide),
              hreg₂ 14 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
                (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), hr14])
        rfl
        (by
          change (s₂.setReg 20 (k + 1)).regs 25 = pref_next.length
          rw [State.setReg_regs_ne _ _ (by decide), hr25₂])
        (by
          change (s₂.setReg 20 (k + 1)).regs 26 = cnt₀ + L_next.length
          rw [State.setReg_regs_ne _ _ (by decide), hr26₂]) with
      ⟨s₄, t₄, hex₄, ht₄, hM₄, hout₄, hr25₄, hr26₄, harr₄, hreg₄⟩
    have hmul : (rem + 1) * (163 * n + 217 * edges₀.length + 181) =
        (163 * n + 217 * edges₀.length + 181) + rem * (163 * n + 217 * edges₀.length + 181) := by ring
    refine ⟨s₄, 3 + ((3 + t_b) + 4) + t₄,
      .while_true hcond (by omega) (.seq (.seq hex₁ hex_b) hex_inc) hex₄,
      by linarith [ht_b, ht₄, hmul], hM₄, hout₄, hr25₄, hr26₄,
      fun a hout h12 h13 h15 h17 h18 h51 => by
        rw [harr₄ a hout h12 h13 h15 h17 h18 h51]
        exact harr₂ a hout h12 h13 h15 h17 h18 h51,
      fun reg h2 h3 h4 h5 h6 h7 h8 h9 h20 h21 h22 h23 h25 h26 h28 => by
        rw [hreg₄ reg h2 h3 h4 h5 h6 h7 h8 h9 h20 h21 h22 h23 h25 h26 h28]
        change (s₂.setReg 20 (k + 1)).regs reg = s.regs reg
        rw [State.setReg_regs_ne _ _ h20]
        exact hreg₂ reg h2 h3 h4 h5 h6 h7 h8 h9 h21 h22 h23 h25 h26 h28⟩

theorem alg86CaseCPassProg_exec {w n cap : ℕ} (G : SimpleGraph (Fin n))
    (lists_G lists_Y : Fin n → List ℕ) (Z : Finset (Fin n))
    (edges₀ : List (Fin n × Fin n)) (M₀ : Finset (Fin edges₀.length))
    (pref₀ : List ℕ) (cnt₀ : ℕ)
    (htot_G : totalAdjEntries lists_G ≤ 2 * edges₀.length)
    (htot_Y : totalAdjEntries lists_Y ≤ 2 * edges₀.length)
    (hcap_le : pref₀.length + n * (n + 2 + 2 * edges₀.length) ≤ cap)
    (hw3 : 3 < 2 ^ w) (hn_w : n < 2 ^ w) (hm8_w : 8 + 2 * edges₀.length < 2 ^ w)
    (hcap_w : cap < 2 ^ w) (hcnt_w : cnt₀ + n < 2 ^ w) {s : State}
    (hin : s.arrs 0 = [n, edges₀.length] ++ flatEdges edges₀)
    (hadj_G : IsAdjList G 3 4 5 lists_G s)
    (hent_G : (s.arrs 5).length < 2 ^ w)
    (hadj_Y : IsAdjList (restrictGraph G (Finset.univ \ Z)) 6 7 8 lists_Y s)
    (hent_Y : (s.arrs 8).length < 2 ^ w)
    (hZ : IsBitSet Z 14 s)
    (htup : HasAlg86Tuples G Z s)
    (hM : IsBitSet M₀ 51 s)
    (hout : s.arrs outArr = pref₀ ++ List.replicate (cap - pref₀.length) 0)
    (hr1 : s.regs 1 = edges₀.length)
    (hr14 : s.regs 14 = n)
    (hr25 : s.regs 25 = pref₀.length)
    (hr26 : s.regs 26 = cnt₀) :
    let L := alg86CaseCPairs G Z edges₀ n
    let M' := alg86CaseCMarked G Z edges₀ M₀ n
    ∃ s' t,
      Exec w alg86CaseCPassProg s s' t ∧
      t ≤ n * (163 * n + 217 * edges₀.length + 181) + 5 ∧
      IsBitSet M' 51 s' ∧
      s'.arrs outArr =
        (pref₀ ++ L.flatMap (fun p => encAlg86Subgraph p.1 p.2)) ++
          List.replicate (cap - (pref₀ ++ L.flatMap (fun p => encAlg86Subgraph p.1 p.2)).length) 0 ∧
      s'.regs 25 = (pref₀ ++ L.flatMap (fun p => encAlg86Subgraph p.1 p.2)).length ∧
      s'.regs 26 = cnt₀ + L.length ∧
      (∀ a : Arr, a ≠ outArr → a ≠ 12 → a ≠ 13 → a ≠ 15 → a ≠ 17 → a ≠ 18 → a ≠ 51 → s'.arrs a = s.arrs a) ∧
      (∀ reg : Reg, reg ≠ 2 → reg ≠ 3 → reg ≠ 4 → reg ≠ 5 → reg ≠ 6 → reg ≠ 7 → reg ≠ 8 → reg ≠ 9 →
        reg ≠ 20 → reg ≠ 21 → reg ≠ 22 → reg ≠ 23 → reg ≠ 25 → reg ≠ 26 → reg ≠ 28 → s'.regs reg = s.regs reg) := by
  intro L M'
  have h0_w : 0 < 2 ^ w := by omega
  let s₁ := s.setReg 20 0
  have hex₁ : Exec w (.assign 20 (.const 0)) s s₁ 2 :=
    .assign (by simp [Expr.eval, checkWord, h0_w])
  rcases alg86CaseCLoop_exec G lists_G lists_Y Z edges₀ M₀ pref₀ cnt₀ htot_G htot_Y
      hcap_le hw3 hn_w hm8_w hcap_w hcnt_w n 0 (by omega) (s := s₁)
      hin (hadj_G.of_arrs_eq rfl rfl rfl) hent_G
      (hadj_Y.of_arrs_eq rfl rfl rfl) hent_Y
      (hZ.of_arr_eq rfl)
      (htup.of_arrs_eq rfl rfl rfl rfl)
      (hM.of_arr_eq rfl)
      (by simpa [s₁, alg86CaseCPairs] using hout)
      (by simp [s₁, State.setReg, hr1])
      (by simp [s₁, State.setReg, hr14])
      rfl
      (by simpa [s₁, State.setReg, alg86CaseCPairs] using hr25)
      (by simpa [s₁, State.setReg, alg86CaseCPairs] using hr26) with
    ⟨s₂, t₂, hex₂, ht₂, hM₂, hout₂, hr25₂, hr26₂, harr₂, hreg₂⟩
  refine ⟨s₂, 2 + t₂, .seq hex₁ hex₂, by omega, hM₂, hout₂, hr25₂, hr26₂,
    fun a hout h12 h13 h15 h17 h18 h51 => by rw [harr₂ a hout h12 h13 h15 h17 h18 h51]; rfl,
    fun reg h2 h3 h4 h5 h6 h7 h8 h9 h20 h21 h22 h23 h25 h26 h28 => by
      rw [hreg₂ reg h2 h3 h4 h5 h6 h7 h8 h9 h20 h21 h22 h23 h25 h26 h28]
      simp [s₁, State.setReg, h20]⟩

end GraphMinor.Compute
