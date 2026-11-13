module

public import GraphMinor.Compute.Algorithm86Aux1

/-!
# Auxiliary Word RAM Subroutines for GM XIII Algorithm (8.6) (Part 2)

Type (i) Pass (`alg86TypeIPassProg`), Type (iii) Pass (`alg86TypeIIIPassProg`),
and attachment tuple precomputation (`precomputeXTuplesProg`).
-/

@[expose] public section

namespace GraphMinor.Compute

open SimpleGraph

/-! ### Section 5: Type (i) Pass (`alg86TypeIPassProg`) and Type (iii) Pass (`alg86TypeIIIPassProg`) -/

/-- List of Type (i) `(V, edges)` pairs emitted for the first `k` edges of `edges₀` whose endpoints
both lie in `Z` and whose edge index is not in `M`. -/
def alg86TypeIPairs {n : ℕ} (Z : Finset (Fin n)) (edges₀ : List (Fin n × Fin n))
    (M : Finset (Fin edges₀.length)) : ℕ → List (Finset (Fin n) × List (Fin n × Fin n))
  | 0 => []
  | k + 1 =>
    if hk : k < edges₀.length then
      let jk : Fin edges₀.length := ⟨k, hk⟩
      let e := edges₀[k]'hk
      if e.1 ∈ Z ∧ e.2 ∈ Z ∧ jk ∉ M then
        alg86TypeIPairs Z edges₀ M k ++ [({e.1, e.2}, [e])]
      else
        alg86TypeIPairs Z edges₀ M k
    else
      alg86TypeIPairs Z edges₀ M k

theorem mem_alg86TypeIPairs_iff {n : ℕ} (Z : Finset (Fin n))
    (edges₀ : List (Fin n × Fin n)) (M : Finset (Fin edges₀.length))
    (k : ℕ) (hk_le : k ≤ edges₀.length)
    (p : Finset (Fin n) × List (Fin n × Fin n)) :
    p ∈ alg86TypeIPairs Z edges₀ M k ↔
      ∃ j : Fin edges₀.length,
        j.1 < k ∧
        (edges₀[j.1]'j.2).1 ∈ Z ∧ (edges₀[j.1]'j.2).2 ∈ Z ∧ j ∉ M ∧
        p = ({(edges₀[j.1]'j.2).1, (edges₀[j.1]'j.2).2}, [edges₀[j.1]'j.2]) := by
  induction k with
  | zero => simp [alg86TypeIPairs]
  | succ k ih =>
    have hk_lt : k < edges₀.length := by omega
    simp only [alg86TypeIPairs, hk_lt, ↓reduceDIte]
    split_ifs with hcond
    · rw [List.mem_append, List.mem_singleton, ih (by omega)]
      constructor
      · rintro (⟨j, hj_lt, h1, h2, hM, hp⟩ | rfl)
        · exact ⟨j, by omega, h1, h2, hM, hp⟩
        · exact ⟨⟨k, hk_lt⟩, Nat.lt_succ_self k, hcond.1, hcond.2.1, hcond.2.2, rfl⟩
      · rintro ⟨j, hj_lt, h1, h2, hM, hp⟩
        rcases Nat.lt_succ_iff_lt_or_eq.mp hj_lt with hlt' | heq
        · exact Or.inl ⟨j, hlt', h1, h2, hM, hp⟩
        · have hj_eq : j = ⟨k, hk_lt⟩ := Fin.ext heq
          subst hj_eq
          exact Or.inr hp
    · rw [ih (by omega)]
      constructor
      · rintro ⟨j, hj_lt, h1, h2, hM, hp⟩
        exact ⟨j, by omega, h1, h2, hM, hp⟩
      · rintro ⟨j, hj_lt, h1, h2, hM, hp⟩
        rcases Nat.lt_succ_iff_lt_or_eq.mp hj_lt with hlt' | heq
        · exact ⟨j, hlt', h1, h2, hM, hp⟩
        · exfalso
          have hj_eq : j = ⟨k, hk_lt⟩ := Fin.ext heq
          subst hj_eq
          exact hcond ⟨h1, h2, hM⟩

lemma length_alg86TypeIPairs_le {n : ℕ} (Z : Finset (Fin n))
    (edges₀ : List (Fin n × Fin n)) (M : Finset (Fin edges₀.length)) (k : ℕ) :
    ((alg86TypeIPairs Z edges₀ M k).flatMap (fun p => encAlg86Subgraph p.1 p.2)).length ≤
      k * (n + 4) ∧
    (alg86TypeIPairs Z edges₀ M k).length ≤ k := by
  induction k with
  | zero => simp [alg86TypeIPairs]
  | succ k ih =>
    rcases ih with ⟨ih1, ih2⟩
    simp only [alg86TypeIPairs]
    split_ifs with hk hcond
    · simp only [List.flatMap_append, List.flatMap_cons, List.flatMap_nil, List.append_nil,
        List.length_append, length_encAlg86Subgraph, List.length_singleton]
      rw [Nat.add_one_mul k]
      omega
    · rw [Nat.add_one_mul k]; omega
    · rw [Nat.add_one_mul k]; omega

/-- Emits the single-edge subgraph `({u, v}, [(u, v)])` where `r_3 = u.1` and `r_4 = v.1`. -/
def alg86TypeIEmitProg : Cmd :=
  .seq (.alloc 18 (.reg 14))
    (.seq (.write 18 (.reg 3) (.const 1))
      (.seq (.write 18 (.reg 4) (.const 1))
        (.seq (.alloc 17 (.const 4))
          (.seq (.write 17 (.const 0) (.reg 14))
            (.seq (.write 17 (.const 1) (.const 1))
              (.seq (.write 17 (.const 2) (.reg 3))
                (.seq (.write 17 (.const 3) (.reg 4))
                  (.seq (.assign 22 (.const 1))
                    appendSubgraphToOutProg))))))))

theorem alg86TypeIEmitProg_exec {w n cap cnt : ℕ} (u v : Fin n) (pref : List ℕ)
    (hcap_le : pref.length + (n + 4) ≤ cap)
    (hw4 : 4 < 2 ^ w) (hn_w : n < 2 ^ w) (hcap_w : cap < 2 ^ w) (hcnt_w : cnt + 1 < 2 ^ w)
    {s : State}
    (hout : s.arrs outArr = pref ++ List.replicate (cap - pref.length) 0)
    (hr3 : s.regs 3 = u.1) (hr4 : s.regs 4 = v.1)
    (hr14 : s.regs 14 = n) (hr25 : s.regs 25 = pref.length) (hr26 : s.regs 26 = cnt) :
    ∃ s' t,
      Exec w alg86TypeIEmitProg s s' t ∧
      t ≤ 18 * n + 115 ∧
      s'.arrs outArr =
        (pref ++ encAlg86Subgraph ({u, v} : Finset (Fin n)) [(u, v)]) ++
          List.replicate (cap - (pref ++ encAlg86Subgraph ({u, v} : Finset (Fin n)) [(u, v)]).length) 0 ∧
      s'.regs 25 = (pref ++ encAlg86Subgraph ({u, v} : Finset (Fin n)) [(u, v)]).length ∧
      s'.regs 26 = cnt + 1 ∧
      (∀ a : Arr, a ≠ outArr → a ≠ 17 → a ≠ 18 → s'.arrs a = s.arrs a) ∧
      (∀ r : Reg, r ≠ 2 → r ≠ 3 → r ≠ 21 → r ≠ 22 → r ≠ 25 → r ≠ 26 → s'.regs r = s.regs r) := by
  have h0_w : 0 < 2 ^ w := by omega
  have hw : 1 < 2 ^ w := by omega
  have hw2 : 2 < 2 ^ w := by omega
  have hw3 : 3 < 2 ^ w := by omega
  have hu_w : u.1 < 2 ^ w := Nat.lt_trans u.2 hn_w
  have hv_w : v.1 < 2 ^ w := Nat.lt_trans v.2 hn_w
  let s₁ := s.setArr 18 (List.replicate n 0)
  have hex₁ : Exec w (.alloc 18 (.reg 14)) s s₁ (1 + n) :=
    .alloc (by simp [Expr.eval, checkWord, hr14, hn_w])
  have hbit₁ : IsBitSet (∅ : Finset (Fin n)) 18 s₁ :=
    IsBitSet.empty_of_replicate rfl
  let s₂ := s₁.writeArr 18 u.1 1
  have hex₂ : Exec w (.write 18 (.reg 3) (.const 1)) s₁ s₂ 3 :=
    .write (by simp [s₁, Expr.eval, checkWord, hr3, hu_w])
      (by simp [Expr.eval, checkWord, hw])
      (by simp [s₁, u.2])
  have hbit₂ : IsBitSet ({u} : Finset (Fin n)) 18 s₂ := hbit₁.write_one u
  let s₃ := s₂.writeArr 18 v.1 1
  have hex₃ : Exec w (.write 18 (.reg 4) (.const 1)) s₂ s₃ 3 :=
    .write (by simp [s₂, s₁, Expr.eval, checkWord, hr4, hv_w])
      (by simp [Expr.eval, checkWord, hw])
      (by simp [s₂, s₁, v.2])
  have hbit₃ : IsBitSet ({u, v} : Finset (Fin n)) 18 s₃ := by
    have h := hbit₂.write_one v
    rwa [Finset.pair_comm v u] at h
  let s₄ := s₃.setArr 17 (List.replicate 4 0)
  have hex₄ : Exec w (.alloc 17 (.const 4)) s₃ s₄ 5 :=
    .alloc (by simp [Expr.eval, checkWord, hw4])
  let s₅ := s₄.writeArr 17 0 n
  have hex₅ : Exec w (.write 17 (.const 0) (.reg 14)) s₄ s₅ 3 :=
    .write (by simp [Expr.eval, checkWord, h0_w])
      (by simp [s₄, s₃, s₂, s₁, Expr.eval, checkWord, hr14, hn_w])
      (by simp [s₄])
  let s₆ := s₅.writeArr 17 1 1
  have hex₆ : Exec w (.write 17 (.const 1) (.const 1)) s₅ s₆ 3 :=
    .write (by simp [Expr.eval, checkWord, hw])
      (by simp [Expr.eval, checkWord, hw])
      (by simp [s₅, s₄])
  let s₇ := s₆.writeArr 17 2 u.1
  have hex₇ : Exec w (.write 17 (.const 2) (.reg 3)) s₆ s₇ 3 :=
    .write (by simp [Expr.eval, checkWord, hw2])
      (by simp [s₆, s₅, s₄, s₃, s₂, s₁, Expr.eval, checkWord, hr3, hu_w])
      (by simp [s₆, s₅, s₄])
  let s₈ := s₇.writeArr 17 3 v.1
  have hex₈ : Exec w (.write 17 (.const 3) (.reg 4)) s₇ s₈ 3 :=
    .write (by simp [Expr.eval, checkWord, hw3])
      (by simp [s₇, s₆, s₅, s₄, s₃, s₂, s₁, Expr.eval, checkWord, hr4, hv_w])
      (by simp [s₇, s₆, s₅, s₄])
  let s₉ := s₈.setReg 22 1
  have hex₉ : Exec w (.assign 22 (.const 1)) s₈ s₉ 2 :=
    .assign (by simp [Expr.eval, checkWord, hw])
  have h17_₉ : s₉.arrs 17 = ([n, ([(u, v)] : List (Fin n × Fin n)).length] ++ flatEdges [(u, v)]) ++ [] := by
    rfl
  rcases appendSubgraphToOutProg_exec ({u, v} : Finset (Fin n)) [(u, v)] pref []
      (by simpa using hcap_le) hw2 hcap_w hcnt_w (s := s₉)
      (hbit₃.of_arr_eq rfl) h17_₉ hout hr14 rfl hr25 hr26 with
    ⟨s₁₀, t₁₀, hex₁₀, ht₁₀, hout₁₀, hr25₁₀, hr26₁₀, harr₁₀, hreg₁₀⟩
  simp only [List.length_singleton] at ht₁₀
  refine ⟨s₁₀, (1 + n) + (3 + (3 + (5 + (3 + (3 + (3 + (3 + (2 + t₁₀)))))))),
    .seq hex₁ (.seq hex₂ (.seq hex₃ (.seq hex₄ (.seq hex₅ (.seq hex₆ (.seq hex₇ (.seq hex₈ (.seq hex₉ hex₁₀)))))))),
    by omega, hout₁₀, hr25₁₀, hr26₁₀,
    fun a hout h17 h18 => by
      rw [harr₁₀ a hout]
      simp [s₉, s₈, s₇, s₆, s₅, s₄, s₃, s₂, s₁, h17, h18],
    fun r h2 h3 h21 h22 h25 h26 => by
      rw [hreg₁₀ r h2 h3 h21 h25 h26]
      change (s₈.setReg 22 1).regs r = s.regs r
      rw [State.setReg_regs_ne _ _ h22]
      rfl⟩

/-- Loop body of `alg86TypeIPassProg`: checks whether the `r_27`-th edge `(u, v)` in `inArr = 0`
has `u ∈ Z`, `v ∈ Z`, and `r_27 ∉ M` (`a_51[r_27] = 0`); if so, emits `({u, v}, [(u, v)])`. -/
def alg86TypeIBody : Cmd :=
  .seq (.assign 3 (.read 0 (.op .add (.const 2) (.op .mul (.const 2) (.reg 27)))))
    (.seq (.assign 4 (.read 0 (.op .add (.const 3) (.op .mul (.const 2) (.reg 27)))))
      (.seq (.assign 5 (.read 14 (.reg 3)))
        (.seq (.assign 6 (.read 14 (.reg 4)))
          (.seq (.assign 7 (.read 51 (.reg 27)))
            (.seq (.assign 8 (.op .mul (.op .mul (.reg 5) (.reg 6))
                (.op .sub (.const 1) (.reg 7))))
              (.ite (.reg 8)
                alg86TypeIEmitProg
                .skip))))))

/-- Emits all Type (i) single-edge subgraphs of `edges₀` whose edge index is not in `M` (`a_51`). -/
def alg86TypeIPassProg : Cmd :=
  .seq (.assign 27 (.const 0))
    (forUp 27 (.reg 1) alg86TypeIBody)

theorem alg86TypeILoop_exec {w n cap : ℕ} (Z : Finset (Fin n))
    (edges₀ : List (Fin n × Fin n)) (M : Finset (Fin edges₀.length))
    (pref₀ : List ℕ) (cnt₀ : ℕ)
    (hcap_le : pref₀.length + edges₀.length * (n + 4) ≤ cap)
    (hw4 : 4 < 2 ^ w) (hn_w : n < 2 ^ w) (hm3_w : 3 + 2 * edges₀.length < 2 ^ w)
    (hcap_w : cap < 2 ^ w) (hcnt_w : cnt₀ + edges₀.length < 2 ^ w)
    (rem k : ℕ) (hrem : k + rem = edges₀.length) {s : State}
    (hin : s.arrs 0 = [n, edges₀.length] ++ flatEdges edges₀)
    (hZ : IsBitSet Z 14 s) (hM : IsBitSet M 51 s)
    (hout : s.arrs outArr =
      (pref₀ ++ (alg86TypeIPairs Z edges₀ M k).flatMap (fun p => encAlg86Subgraph p.1 p.2)) ++
        List.replicate (cap - (pref₀ ++ (alg86TypeIPairs Z edges₀ M k).flatMap (fun p => encAlg86Subgraph p.1 p.2)).length) 0)
    (hr1 : s.regs 1 = edges₀.length) (hr14 : s.regs 14 = n)
    (hr25 : s.regs 25 = (pref₀ ++ (alg86TypeIPairs Z edges₀ M k).flatMap (fun p => encAlg86Subgraph p.1 p.2)).length)
    (hr26 : s.regs 26 = cnt₀ + (alg86TypeIPairs Z edges₀ M k).length)
    (hr27 : s.regs 27 = k) :
    let L := alg86TypeIPairs Z edges₀ M edges₀.length
    ∃ s' t,
      Exec w (forUp 27 (.reg 1) alg86TypeIBody) s s' t ∧
      t ≤ 3 + rem * (18 * n + 158) ∧
      s'.arrs outArr =
        (pref₀ ++ L.flatMap (fun p => encAlg86Subgraph p.1 p.2)) ++
          List.replicate (cap - (pref₀ ++ L.flatMap (fun p => encAlg86Subgraph p.1 p.2)).length) 0 ∧
      s'.regs 25 = (pref₀ ++ L.flatMap (fun p => encAlg86Subgraph p.1 p.2)).length ∧
      s'.regs 26 = cnt₀ + L.length ∧
      (∀ a : Arr, a ≠ outArr → a ≠ 17 → a ≠ 18 → s'.arrs a = s.arrs a) ∧
      (∀ r : Reg, r ≠ 2 → r ≠ 3 → r ≠ 4 → r ≠ 5 → r ≠ 6 → r ≠ 7 → r ≠ 8 →
        r ≠ 21 → r ≠ 22 → r ≠ 25 → r ≠ 26 → r ≠ 27 → s'.regs r = s.regs r) := by
  intro L
  have h0_w : 0 < 2 ^ w := by omega
  have hw : 1 < 2 ^ w := by omega
  have hw2 : 2 < 2 ^ w := by omega
  have hw3 : 3 < 2 ^ w := by omega
  have hm_w : edges₀.length < 2 ^ w := by omega
  induction rem generalizing k s with
  | zero =>
    have hk_eq : k = edges₀.length := by omega
    subst hk_eq
    have hcond : (Expr.op .lt (.reg 27) (.reg 1)).eval w s = some 0 := by
      simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hr27, hr1, hm_w]
    exact ⟨s, 3, .while_false hcond, by omega, hout, hr25, hr26,
      fun _ _ _ _ => rfl, fun _ _ _ _ _ _ _ _ _ _ _ _ _ => rfl⟩
  | succ rem ih =>
    have hk_lt : k < edges₀.length := by omega
    have hk_w : k < 2 ^ w := by omega
    have h2k_w : 2 * k < 2 ^ w := by omega
    have h2k2_w : 2 + 2 * k < 2 ^ w := by omega
    have h2k3_w : 3 + 2 * k < 2 ^ w := by omega
    let jk : Fin edges₀.length := ⟨k, hk_lt⟩
    let e := edges₀[k]'hk_lt
    let u := e.1
    let v := e.2
    let L_k := alg86TypeIPairs Z edges₀ M k
    let L_next := alg86TypeIPairs Z edges₀ M (k + 1)
    let pref_k := pref₀ ++ L_k.flatMap (fun p => encAlg86Subgraph p.1 p.2)
    let pref_next := pref₀ ++ L_next.flatMap (fun p => encAlg86Subgraph p.1 p.2)
    obtain ⟨hflat_le, hlen_le⟩ := length_alg86TypeIPairs_le Z edges₀ M k
    have hpref_k_cap : pref_k.length + (n + 4) ≤ cap := by
      have h1 : pref_k.length ≤ pref₀.length + k * (n + 4) := by
        dsimp [pref_k, L_k]; rw [List.length_append]; omega
      have h2 : (k + 1) * (n + 4) ≤ edges₀.length * (n + 4) :=
        Nat.mul_le_mul_right (n + 4) (by omega)
      rw [Nat.succ_mul] at h2
      omega
    have hcond : (Expr.op .lt (.reg 27) (.reg 1)).eval w s = some 1 := by
      simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hr27, hr1, hk_w, hm_w, hk_lt, hw]
    have hin_u_lt : 2 + 2 * k < (s.arrs 0).length := by
      rw [hin]; simp [length_flatEdges]; omega
    have hin_u_get : (s.arrs 0)[2 + 2 * k]'hin_u_lt = u.1 := by
      have hidx : 2 + 2 * k = (2 * k) + 1 + 1 := by omega
      simp only [hin, hidx, List.cons_append, List.nil_append, List.getElem_cons_succ]
      exact getElem_flatEdges_even edges₀ hk_lt
    have hin_v_lt : 3 + 2 * k < (s.arrs 0).length := by
      rw [hin]; simp [length_flatEdges]; omega
    have hin_v_get : (s.arrs 0)[3 + 2 * k]'hin_v_lt = v.1 := by
      have hidx : 3 + 2 * k = (2 * k + 1) + 1 + 1 := by omega
      simp only [hin, hidx, List.cons_append, List.nil_append, List.getElem_cons_succ]
      exact getElem_flatEdges_odd edges₀ hk_lt
    have hu_w : u.1 < 2 ^ w := Nat.lt_trans u.2 hn_w
    have hv_w : v.1 < 2 ^ w := Nat.lt_trans v.2 hn_w
    let s₁ := s.setReg 3 u.1
    have hex₁ : Exec w (.assign 3 (.read 0 (.op .add (.const 2) (.op .mul (.const 2) (.reg 27))))) s s₁ 7 :=
      .assign (by
        simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hr27, hw2, hk_w, h2k_w, h2k2_w,
          hin_u_lt, hin_u_get, hu_w])
    let s₂ := s₁.setReg 4 v.1
    have hex₂ : Exec w (.assign 4 (.read 0 (.op .add (.const 3) (.op .mul (.const 2) (.reg 27))))) s₁ s₂ 7 :=
      .assign (by
        simp [s₁, State.setReg, Expr.eval, BinOp.eval, BinOp.raw, checkWord, hr27, hw2, hw3,
          hk_w, h2k_w, h2k3_w, hin_v_lt, hin_v_get, hv_w])
    have hu_Z_lt : u.1 < (s.arrs 14).length := by rw [hZ.1]; exact u.2
    let b_u := (s.arrs 14)[u.1]'hu_Z_lt
    have hbu_eq : b_u = if u ∈ Z then 1 else 0 := hZ.getElem_eq_ite u
    have hbu_w : b_u < 2 ^ w := by rw [hbu_eq]; split_ifs <;> omega
    let s₃ := s₂.setReg 5 b_u
    have hex₃ : Exec w (.assign 5 (.read 14 (.reg 3))) s₂ s₃ 3 :=
      .assign (by simp [s₂, s₁, State.setReg, Expr.eval, checkWord, hu_w, hu_Z_lt, b_u, hbu_w])
    have hv_Z_lt : v.1 < (s.arrs 14).length := by rw [hZ.1]; exact v.2
    let b_v := (s.arrs 14)[v.1]'hv_Z_lt
    have hbv_eq : b_v = if v ∈ Z then 1 else 0 := hZ.getElem_eq_ite v
    have hbv_w : b_v < 2 ^ w := by rw [hbv_eq]; split_ifs <;> omega
    let s₄ := s₃.setReg 6 b_v
    have hex₄ : Exec w (.assign 6 (.read 14 (.reg 4))) s₃ s₄ 3 :=
      .assign (by simp [s₃, s₂, s₁, State.setReg, Expr.eval, checkWord, hv_w, hv_Z_lt, b_v, hbv_w])
    have hk_M_lt : k < (s.arrs 51).length := by rw [hM.1]; exact hk_lt
    let b_m := (s.arrs 51)[k]'hk_M_lt
    have hbm_eq : b_m = if jk ∈ M then 1 else 0 := hM.getElem_eq_ite jk
    have hbm_w : b_m < 2 ^ w := by rw [hbm_eq]; split_ifs <;> omega
    let s₅ := s₄.setReg 7 b_m
    have hex₅ : Exec w (.assign 7 (.read 51 (.reg 27))) s₄ s₅ 3 :=
      .assign (by simp [s₄, s₃, s₂, s₁, State.setReg, Expr.eval, checkWord, hr27, hk_w, hk_M_lt, b_m, hbm_w])
    let flag := (b_u * b_v) * (1 - b_m)
    have hbu_bv_w : b_u * b_v < 2 ^ w := by rw [hbu_eq, hbv_eq]; split_ifs <;> omega
    have hsub_w : 1 - b_m < 2 ^ w := by rw [hbm_eq]; split_ifs <;> omega
    have hflag_w : flag < 2 ^ w := by dsimp [flag]; rw [hbu_eq, hbv_eq, hbm_eq]; split_ifs <;> omega
    let s₆ := s₅.setReg 8 flag
    have hex₆ : Exec w (.assign 8 (.op .mul (.op .mul (.reg 5) (.reg 6))
        (.op .sub (.const 1) (.reg 7)))) s₅ s₆ 8 :=
      .assign (by
        simp [s₅, s₄, s₃, s₂, s₁, State.setReg, Expr.eval, BinOp.eval, BinOp.raw, checkWord,
          hbu_w, hbv_w, hbm_w, hw, hbu_bv_w, hsub_w, flag, hflag_w])
    have hstep : ∃ s₇ t_b,
        Exec w (.ite (.reg 8) alg86TypeIEmitProg .skip) s₆ s₇ t_b ∧
        t_b ≤ 18 * n + 116 ∧
        s₇.arrs outArr = pref_next ++ List.replicate (cap - pref_next.length) 0 ∧
        s₇.regs 25 = pref_next.length ∧
        s₇.regs 26 = cnt₀ + L_next.length ∧
        s₇.regs 27 = k ∧
        (∀ a : Arr, a ≠ outArr → a ≠ 17 → a ≠ 18 → s₇.arrs a = s.arrs a) ∧
        (∀ r : Reg, r ≠ 2 → r ≠ 3 → r ≠ 4 → r ≠ 5 → r ≠ 6 → r ≠ 7 → r ≠ 8 →
          r ≠ 21 → r ≠ 22 → r ≠ 25 → r ≠ 26 → s₇.regs r = s.regs r) := by
      by_cases hkeep : u ∈ Z ∧ v ∈ Z ∧ jk ∉ M
      · have hflag1 : flag = 1 := by simp [flag, hbu_eq, hbv_eq, hbm_eq, hkeep.1, hkeep.2.1, hkeep.2.2]
        have hcond8 : (Expr.reg 8).eval w s₆ = some 1 := by
          simp [s₆, State.setReg, Expr.eval, checkWord, hflag1, hw]
        have hL_next_eq : L_next = L_k ++ [({u, v}, [e])] := by
          simp [L_next, L_k, alg86TypeIPairs, hk_lt, e, u, v, jk, hkeep.1, hkeep.2.1, hkeep.2.2]
        have hpref_next_eq : pref_next = pref_k ++ encAlg86Subgraph ({u, v} : Finset (Fin n)) [(u, v)] := by
          simp [pref_next, pref_k, hL_next_eq, e, u, v, List.append_assoc]
        rcases alg86TypeIEmitProg_exec u v pref_k hpref_k_cap hw4 hn_w hcap_w (by omega) (s := s₆)
            hout
            (by simp [s₆, s₅, s₄, s₃, s₂, s₁, State.setReg])
            (by simp [s₆, s₅, s₄, s₃, s₂, State.setReg])
            hr14 hr25 hr26 with
          ⟨s₇, t₇, hex₇, ht₇, hout₇, hr25₇, hr26₇, harr₇, hreg₇⟩
        have hr27₇ : s₇.regs 27 = k := by
          rw [hreg₇ 27 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]
          exact hr27
        refine ⟨s₇, 1 + t₇, .ite_true hcond8 (by decide) hex₇, by omega,
          by simpa [hpref_next_eq] using hout₇,
          by simpa [hpref_next_eq] using hr25₇,
          by simp [hr26₇, hL_next_eq, L_k, Nat.add_assoc],
          hr27₇,
          fun a hout h17 h18 => by rw [harr₇ a hout h17 h18]; rfl,
          fun r h2 h3 h4 h5 h6 h7 h8 h21 h22 h25 h26 => by
            rw [hreg₇ r h2 h3 h21 h22 h25 h26]
            simp [s₆, s₅, s₄, s₃, s₂, s₁, State.setReg, h3, h4, h5, h6, h7, h8]⟩
      · have hflag0 : flag = 0 := by
          dsimp [flag]
          rw [hbu_eq, hbv_eq, hbm_eq]
          by_cases hu : u ∈ Z <;> by_cases hv : v ∈ Z <;> by_cases hm : jk ∈ M <;>
            simp [hu, hv, hm] at hkeep ⊢
        have hcond8 : (Expr.reg 8).eval w s₆ = some 0 := by
          simp [s₆, State.setReg, Expr.eval, checkWord, hflag0, h0_w]
        have hL_next_eq : L_next = L_k := by
          simp [L_next, L_k, alg86TypeIPairs, hk_lt, e, u, v, jk, hkeep]
        have hpref_next_eq : pref_next = pref_k := by
          simp [pref_next, pref_k, hL_next_eq]
        refine ⟨s₆, 1 + 1, .ite_false hcond8 (.skip s₆), by omega,
          by change s.arrs outArr = _; rw [hpref_next_eq]; exact hout,
          by change s.regs 25 = _; rw [hpref_next_eq]; exact hr25,
          by change s.regs 26 = _; rw [hL_next_eq]; exact hr26,
          hr27,
          fun _ _ _ _ => rfl,
          fun r _ h3 h4 h5 h6 h7 h8 _ _ _ _ => by
            simp [s₆, s₅, s₄, s₃, s₂, s₁, State.setReg, h3, h4, h5, h6, h7, h8]⟩
    rcases hstep with ⟨s₇, t_b, hex_b, ht_b, hout₇, hr25₇, hr26₇, hr27₇, harr₇, hreg₇⟩
    let s₈ := s₇.setReg 27 (k + 1)
    have hex_inc : Exec w (.assign 27 (.op .add (.reg 27) (.const 1))) s₇ s₈ 4 :=
      .assign (by
        simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hr27₇, hk_w, hw,
          show k + 1 < 2 ^ w by omega])
    rcases ih (k + 1) (by omega) (s := s₈)
        (by change s₇.arrs 0 = _; rw [harr₇ 0 (by decide) (by decide) (by decide), hin])
        (hZ.of_arr_eq (harr₇ 14 (by decide) (by decide) (by decide)))
        (hM.of_arr_eq (harr₇ 51 (by decide) (by decide) (by decide)))
        hout₇
        (by
          change (s₇.setReg 27 (k + 1)).regs 1 = edges₀.length
          rw [State.setReg_regs_ne _ _ (by decide),
              hreg₇ 1 (by decide) (by decide) (by decide) (by decide) (by decide)
                (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), hr1])
        (by
          change (s₇.setReg 27 (k + 1)).regs 14 = n
          rw [State.setReg_regs_ne _ _ (by decide),
              hreg₇ 14 (by decide) (by decide) (by decide) (by decide) (by decide)
                (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), hr14])
        (by
          change (s₇.setReg 27 (k + 1)).regs 25 = pref_next.length
          rw [State.setReg_regs_ne _ _ (by decide), hr25₇])
        (by
          change (s₇.setReg 27 (k + 1)).regs 26 = cnt₀ + L_next.length
          rw [State.setReg_regs_ne _ _ (by decide), hr26₇])
        rfl with
      ⟨s₉, t₉, hex₉, ht₉, hout₉, hr25₉, hr26₉, harr₉, hreg₉⟩
    have hmul : (rem + 1) * (18 * n + 158) = (18 * n + 158) + rem * (18 * n + 158) := by ring
    refine ⟨s₉, 3 + ((7 + (7 + (3 + (3 + (3 + (8 + t_b)))))) + 4) + t₉,
      .while_true hcond (by omega)
        (.seq (.seq hex₁ (.seq hex₂ (.seq hex₃ (.seq hex₄ (.seq hex₅ (.seq hex₆ hex_b)))))) hex_inc)
        hex₉,
      by linarith [ht_b, ht₉, hmul], hout₉, hr25₉, hr26₉,
      fun a hout h17 h18 => by rw [harr₉ a hout h17 h18]; exact harr₇ a hout h17 h18,
      fun r h2 h3 h4 h5 h6 h7 h8 h21 h22 h25 h26 h27 => by
        rw [hreg₉ r h2 h3 h4 h5 h6 h7 h8 h21 h22 h25 h26 h27]
        change (s₇.setReg 27 (k + 1)).regs r = s.regs r
        rw [State.setReg_regs_ne _ _ h27]
        exact hreg₇ r h2 h3 h4 h5 h6 h7 h8 h21 h22 h25 h26⟩

theorem alg86TypeIPassProg_exec {w n cap : ℕ} (Z : Finset (Fin n))
    (edges₀ : List (Fin n × Fin n)) (M : Finset (Fin edges₀.length))
    (pref₀ : List ℕ) (cnt₀ : ℕ)
    (hcap_le : pref₀.length + edges₀.length * (n + 4) ≤ cap)
    (hw4 : 4 < 2 ^ w) (hn_w : n < 2 ^ w) (hm3_w : 3 + 2 * edges₀.length < 2 ^ w)
    (hcap_w : cap < 2 ^ w) (hcnt_w : cnt₀ + edges₀.length < 2 ^ w) {s : State}
    (hin : s.arrs 0 = [n, edges₀.length] ++ flatEdges edges₀)
    (hZ : IsBitSet Z 14 s) (hM : IsBitSet M 51 s)
    (hout : s.arrs outArr = pref₀ ++ List.replicate (cap - pref₀.length) 0)
    (hr1 : s.regs 1 = edges₀.length) (hr14 : s.regs 14 = n)
    (hr25 : s.regs 25 = pref₀.length) (hr26 : s.regs 26 = cnt₀) :
    let L := alg86TypeIPairs Z edges₀ M edges₀.length
    ∃ s' t,
      Exec w alg86TypeIPassProg s s' t ∧
      t ≤ edges₀.length * (18 * n + 158) + 5 ∧
      s'.arrs outArr =
        (pref₀ ++ L.flatMap (fun p => encAlg86Subgraph p.1 p.2)) ++
          List.replicate (cap - (pref₀ ++ L.flatMap (fun p => encAlg86Subgraph p.1 p.2)).length) 0 ∧
      s'.regs 25 = (pref₀ ++ L.flatMap (fun p => encAlg86Subgraph p.1 p.2)).length ∧
      s'.regs 26 = cnt₀ + L.length ∧
      (∀ a : Arr, a ≠ outArr → a ≠ 17 → a ≠ 18 → s'.arrs a = s.arrs a) ∧
      (∀ r : Reg, r ≠ 2 → r ≠ 3 → r ≠ 4 → r ≠ 5 → r ≠ 6 → r ≠ 7 → r ≠ 8 →
        r ≠ 21 → r ≠ 22 → r ≠ 25 → r ≠ 26 → r ≠ 27 → s'.regs r = s.regs r) := by
  intro L
  have h0_w : 0 < 2 ^ w := by omega
  let s₁ := s.setReg 27 0
  have hex₁ : Exec w (.assign 27 (.const 0)) s s₁ 2 :=
    .assign (by simp [Expr.eval, checkWord, h0_w])
  rcases alg86TypeILoop_exec Z edges₀ M pref₀ cnt₀ hcap_le hw4 hn_w hm3_w hcap_w hcnt_w
      edges₀.length 0 (by omega) (s := s₁)
      hin (hZ.of_arr_eq rfl) (hM.of_arr_eq rfl)
      (by simpa [s₁, alg86TypeIPairs] using hout)
      (by simp [s₁, State.setReg, hr1])
      (by simp [s₁, State.setReg, hr14])
      (by simpa [s₁, State.setReg, alg86TypeIPairs] using hr25)
      (by simpa [s₁, State.setReg, alg86TypeIPairs] using hr26)
      rfl with
    ⟨s₂, t₂, hex₂, ht₂, hout₂, hr25₂, hr26₂, harr₂, hreg₂⟩
  refine ⟨s₂, 2 + t₂, .seq hex₁ hex₂, by omega, hout₂, hr25₂, hr26₂,
    fun a hout h17 h18 => by rw [harr₂ a hout h17 h18]; rfl,
    fun r h2 h3 h4 h5 h6 h7 h8 h21 h22 h25 h26 h27 => by
      rw [hreg₂ r h2 h3 h4 h5 h6 h7 h8 h21 h22 h25 h26 h27]
      simp [s₁, State.setReg, h27]⟩

/-- List of Type (iii) `(V, edges)` pairs emitted for the first `k` vertices in `Fin n` that lie in
`omegaSet` and have degree `0` in `edges₀`. -/
def alg86TypeIIIPairs {n : ℕ} (omegaSet : Finset (Fin n))
    (edges₀ : List (Fin n × Fin n)) : ℕ → List (Finset (Fin n) × List (Fin n × Fin n))
  | 0 => []
  | k + 1 =>
    if hk : k < n then
      let vk : Fin n := ⟨k, hk⟩
      if vk ∈ omegaSet ∧ (edgeNeighbors edges₀ vk).length = 0 then
        alg86TypeIIIPairs omegaSet edges₀ k ++ [({vk}, [])]
      else
        alg86TypeIIIPairs omegaSet edges₀ k
    else
      alg86TypeIIIPairs omegaSet edges₀ k

theorem mem_alg86TypeIIIPairs_iff {n : ℕ} (omegaSet : Finset (Fin n))
    (edges₀ : List (Fin n × Fin n)) (k : ℕ) (hk_le : k ≤ n)
    (p : Finset (Fin n) × List (Fin n × Fin n)) :
    p ∈ alg86TypeIIIPairs omegaSet edges₀ k ↔
      ∃ v : Fin n,
        v.1 < k ∧ v ∈ omegaSet ∧ (edgeNeighbors edges₀ v).length = 0 ∧
        p = ({v}, []) := by
  induction k with
  | zero => simp [alg86TypeIIIPairs]
  | succ k ih =>
    have hk_lt : k < n := by omega
    simp only [alg86TypeIIIPairs, hk_lt, ↓reduceDIte]
    split_ifs with hcond
    · rw [List.mem_append, List.mem_singleton, ih (by omega)]
      constructor
      · rintro (⟨v, hv_lt, h1, h2, hp⟩ | rfl)
        · exact ⟨v, by omega, h1, h2, hp⟩
        · exact ⟨⟨k, hk_lt⟩, Nat.lt_succ_self k, hcond.1, hcond.2, rfl⟩
      · rintro ⟨v, hv_lt, h1, h2, hp⟩
        rcases Nat.lt_succ_iff_lt_or_eq.mp hv_lt with hlt' | heq
        · exact Or.inl ⟨v, hlt', h1, h2, hp⟩
        · have hv_eq : v = ⟨k, hk_lt⟩ := Fin.ext heq
          subst hv_eq
          exact Or.inr hp
    · rw [ih (by omega)]
      constructor
      · rintro ⟨v, hv_lt, h1, h2, hp⟩
        exact ⟨v, by omega, h1, h2, hp⟩
      · rintro ⟨v, hv_lt, h1, h2, hp⟩
        rcases Nat.lt_succ_iff_lt_or_eq.mp hv_lt with hlt' | heq
        · exact ⟨v, hlt', h1, h2, hp⟩
        · exfalso
          have hv_eq : v = ⟨k, hk_lt⟩ := Fin.ext heq
          subst hv_eq
          exact hcond ⟨h1, h2⟩

lemma length_alg86TypeIIIPairs_le {n : ℕ} (omegaSet : Finset (Fin n))
    (edges₀ : List (Fin n × Fin n)) (k : ℕ) :
    ((alg86TypeIIIPairs omegaSet edges₀ k).flatMap (fun p => encAlg86Subgraph p.1 p.2)).length ≤
      k * (n + 2) ∧
    (alg86TypeIIIPairs omegaSet edges₀ k).length ≤ k := by
  induction k with
  | zero => simp [alg86TypeIIIPairs]
  | succ k ih =>
    rcases ih with ⟨ih1, ih2⟩
    simp only [alg86TypeIIIPairs]
    split_ifs with hk hcond
    · simp only [List.flatMap_append, List.flatMap_cons, List.flatMap_nil, List.append_nil,
        List.length_append, length_encAlg86Subgraph, List.length_singleton, List.length_nil]
      rw [Nat.add_one_mul k]
      omega
    · rw [Nat.add_one_mul k]; omega
    · rw [Nat.add_one_mul k]; omega

/-- Emits the single-vertex subgraph `({v}, [])` where `r_20 = v.1`. -/
def alg86TypeIIIEmitProg : Cmd :=
  .seq (alg83SingletonProg 18 14 20)
    (.seq (.alloc 17 (.const 2))
      (.seq (.write 17 (.const 0) (.reg 14))
        (.seq (.assign 22 (.const 0))
          appendSubgraphToOutProg)))

theorem alg86TypeIIIEmitProg_exec {w n cap cnt : ℕ} (v : Fin n) (pref : List ℕ)
    (hcap_le : pref.length + (n + 2) ≤ cap)
    (hw2 : 2 < 2 ^ w) (hn_w : n < 2 ^ w) (hcap_w : cap < 2 ^ w) (hcnt_w : cnt + 1 < 2 ^ w)
    {s : State}
    (hout : s.arrs outArr = pref ++ List.replicate (cap - pref.length) 0)
    (hr14 : s.regs 14 = n) (hr20 : s.regs 20 = v.1)
    (hr25 : s.regs 25 = pref.length) (hr26 : s.regs 26 = cnt) :
    ∃ s' t,
      Exec w alg86TypeIIIEmitProg s s' t ∧
      t ≤ 18 * n + 67 ∧
      s'.arrs outArr =
        (pref ++ encAlg86Subgraph ({v} : Finset (Fin n)) []) ++
          List.replicate (cap - (pref ++ encAlg86Subgraph ({v} : Finset (Fin n)) []).length) 0 ∧
      s'.regs 25 = (pref ++ encAlg86Subgraph ({v} : Finset (Fin n)) []).length ∧
      s'.regs 26 = cnt + 1 ∧
      (∀ a : Arr, a ≠ outArr → a ≠ 17 → a ≠ 18 → s'.arrs a = s.arrs a) ∧
      (∀ r : Reg, r ≠ 2 → r ≠ 3 → r ≠ 21 → r ≠ 22 → r ≠ 25 → r ≠ 26 → s'.regs r = s.regs r) := by
  have h0_w : 0 < 2 ^ w := by omega
  have hw : 1 < 2 ^ w := by omega
  rcases alg83SingletonProg_exec v 18 14 20 hw hn_w hr14 hr20 with
    ⟨s₁, t₁, hex₁, ht₁, hbit₁, harr₁, hreg₁⟩
  let s₂ := s₁.setArr 17 (List.replicate 2 0)
  have hex₂ : Exec w (.alloc 17 (.const 2)) s₁ s₂ 3 :=
    .alloc (by simp [Expr.eval, checkWord, hw2])
  have hr14_₂ : s₂.regs 14 = n := by
    change s₁.regs 14 = n
    rw [congrFun hreg₁ 14]; exact hr14
  let s₃ := s₂.writeArr 17 0 n
  have hex₃ : Exec w (.write 17 (.const 0) (.reg 14)) s₂ s₃ 3 :=
    .write (by simp [Expr.eval, checkWord, h0_w])
      (by simp [Expr.eval, checkWord, hr14_₂, hn_w])
      (by simp [s₂])
  let s₄ := s₃.setReg 22 0
  have hex₄ : Exec w (.assign 22 (.const 0)) s₃ s₄ 2 :=
    .assign (by simp [Expr.eval, checkWord, h0_w])
  have h17_₄ : s₄.arrs 17 =
      ([n, ([] : List (Fin n × Fin n)).length] ++ flatEdges ([] : List (Fin n × Fin n))) ++ [] := rfl
  have hout₄ : s₄.arrs outArr = pref ++ List.replicate (cap - pref.length) 0 := by
    change s₁.arrs outArr = _
    rw [harr₁ outArr (by decide), hout]
  have hr14_₄ : s₄.regs 14 = n := by
    change (s₃.setReg 22 0).regs 14 = n
    rw [State.setReg_regs_ne _ _ (by decide)]
    exact hr14_₂
  have hr25_₄ : s₄.regs 25 = pref.length := by
    change (s₃.setReg 22 0).regs 25 = pref.length
    rw [State.setReg_regs_ne _ _ (by decide)]
    exact (congrFun hreg₁ 25).trans hr25
  have hr26_₄ : s₄.regs 26 = cnt := by
    change (s₃.setReg 22 0).regs 26 = cnt
    rw [State.setReg_regs_ne _ _ (by decide)]
    exact (congrFun hreg₁ 26).trans hr26
  rcases appendSubgraphToOutProg_exec ({v} : Finset (Fin n)) [] pref []
      (by simpa using hcap_le) hw2 hcap_w hcnt_w (s := s₄)
      (hbit₁.of_arr_eq rfl) h17_₄ hout₄ hr14_₄ rfl hr25_₄ hr26_₄ with
    ⟨s₅, t₅, hex₅, ht₅, hout₅, hr25₅, hr26₅, harr₅, hreg₅⟩
  simp only [List.length_nil, Nat.mul_zero, Nat.add_zero] at ht₅
  refine ⟨s₅, t₁ + (3 + (3 + (2 + t₅))),
    .seq hex₁ (.seq hex₂ (.seq hex₃ (.seq hex₄ hex₅))),
    by omega, hout₅, hr25₅, hr26₅,
    fun a hout h17 h18 => by
      rw [harr₅ a hout]
      simp only [s₄, s₃, s₂, State.setReg_arrs, State.writeArr_arrs_ne _ _ _ h17,
        State.setArr_arrs_ne _ _ h17]
      exact harr₁ a h18,
    fun r h2 h3 h21 h22 h25 h26 => by
      rw [hreg₅ r h2 h3 h21 h25 h26]
      change (s₃.setReg 22 0).regs r = s.regs r
      rw [State.setReg_regs_ne _ _ h22]
      exact congrFun hreg₁ r⟩

/-- Loop body of `alg86TypeIIIPassProg`: checks whether vertex `r_20` lies in `a_9` (`omegaSet`)
and has degree `0` in `a_2`; if so, emits `({v}, [])`. -/
def alg86TypeIIIBody : Cmd :=
  .seq (.assign 3 (.read 9 (.reg 20)))
    (.seq (.assign 4 (.read 2 (.reg 20)))
      (.seq (.assign 5 (.op .mul (.reg 3) (.op .eq (.reg 4) (.const 0))))
        (.ite (.reg 5)
          alg86TypeIIIEmitProg
          .skip)))

/-- Emits all Type (iii) isolated-boundary-vertex subgraphs of `x.G`. -/
def alg86TypeIIIPassProg : Cmd :=
  .seq (.assign 20 (.const 0))
    (forUp 20 (.reg 14) alg86TypeIIIBody)

theorem alg86TypeIIILoop_exec {w n cap : ℕ} (omegaSet : Finset (Fin n))
    (edges₀ : List (Fin n × Fin n))
    (pref₀ : List ℕ) (cnt₀ : ℕ)
    (hcap_le : pref₀.length + n * (n + 2) ≤ cap)
    (hw2 : 2 < 2 ^ w) (hn_w : n < 2 ^ w) (hm2_w : 2 * edges₀.length < 2 ^ w)
    (hcap_w : cap < 2 ^ w) (hcnt_w : cnt₀ + n < 2 ^ w)
    (rem k : ℕ) (hrem : k + rem = n) {s : State}
    (hom : IsBitSet omegaSet 9 s)
    (hdeg_len : (s.arrs 2).length = n)
    (hdeg_val : ∀ v : Fin n, (s.arrs 2)[v.1]'(by rw [hdeg_len]; exact v.2) = (edgeNeighbors edges₀ v).length)
    (hdeg_w : ∀ v : Fin n, (edgeNeighbors edges₀ v).length < 2 ^ w)
    (hout : s.arrs outArr =
      (pref₀ ++ (alg86TypeIIIPairs omegaSet edges₀ k).flatMap (fun p => encAlg86Subgraph p.1 p.2)) ++
        List.replicate (cap - (pref₀ ++ (alg86TypeIIIPairs omegaSet edges₀ k).flatMap (fun p => encAlg86Subgraph p.1 p.2)).length) 0)
    (hr14 : s.regs 14 = n) (hr20 : s.regs 20 = k)
    (hr25 : s.regs 25 = (pref₀ ++ (alg86TypeIIIPairs omegaSet edges₀ k).flatMap (fun p => encAlg86Subgraph p.1 p.2)).length)
    (hr26 : s.regs 26 = cnt₀ + (alg86TypeIIIPairs omegaSet edges₀ k).length) :
    let L := alg86TypeIIIPairs omegaSet edges₀ n
    ∃ s' t,
      Exec w (forUp 20 (.reg 14) alg86TypeIIIBody) s s' t ∧
      t ≤ 3 + rem * (18 * n + 91) ∧
      s'.arrs outArr =
        (pref₀ ++ L.flatMap (fun p => encAlg86Subgraph p.1 p.2)) ++
          List.replicate (cap - (pref₀ ++ L.flatMap (fun p => encAlg86Subgraph p.1 p.2)).length) 0 ∧
      s'.regs 25 = (pref₀ ++ L.flatMap (fun p => encAlg86Subgraph p.1 p.2)).length ∧
      s'.regs 26 = cnt₀ + L.length ∧
      (∀ a : Arr, a ≠ outArr → a ≠ 17 → a ≠ 18 → s'.arrs a = s.arrs a) ∧
      (∀ r : Reg, r ≠ 2 → r ≠ 3 → r ≠ 4 → r ≠ 5 →
        r ≠ 20 → r ≠ 21 → r ≠ 22 → r ≠ 25 → r ≠ 26 → s'.regs r = s.regs r) := by
  intro L
  have h0_w : 0 < 2 ^ w := by omega
  have hw : 1 < 2 ^ w := by omega
  induction rem generalizing k s with
  | zero =>
    have hk_eq : k = n := by omega
    subst hk_eq
    have hcond : (Expr.op .lt (.reg 20) (.reg 14)).eval w s = some 0 := by
      simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hr20, hr14, hn_w]
    exact ⟨s, 3, .while_false hcond, by omega, hout, hr25, hr26,
      fun _ _ _ _ => rfl, fun _ _ _ _ _ _ _ _ _ _ => rfl⟩
  | succ rem ih =>
    have hk_lt : k < n := by omega
    have hk_w : k < 2 ^ w := by omega
    let vk : Fin n := ⟨k, hk_lt⟩
    let L_k := alg86TypeIIIPairs omegaSet edges₀ k
    let L_next := alg86TypeIIIPairs omegaSet edges₀ (k + 1)
    let pref_k := pref₀ ++ L_k.flatMap (fun p => encAlg86Subgraph p.1 p.2)
    let pref_next := pref₀ ++ L_next.flatMap (fun p => encAlg86Subgraph p.1 p.2)
    obtain ⟨hflat_le, hlen_le⟩ := length_alg86TypeIIIPairs_le omegaSet edges₀ k
    have hpref_k_cap : pref_k.length + (n + 2) ≤ cap := by
      have h1 : pref_k.length ≤ pref₀.length + k * (n + 2) := by
        dsimp [pref_k, L_k]; rw [List.length_append]; omega
      have h2 : (k + 1) * (n + 2) ≤ n * (n + 2) :=
        Nat.mul_le_mul_right (n + 2) (by omega)
      rw [Nat.succ_mul] at h2
      omega
    have hcond : (Expr.op .lt (.reg 20) (.reg 14)).eval w s = some 1 := by
      simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hr20, hr14, hk_w, hn_w, hk_lt, hw]
    have hk_om_lt : k < (s.arrs 9).length := by rw [hom.1]; exact hk_lt
    let b_om := (s.arrs 9)[k]'hk_om_lt
    have hbom_eq : b_om = if vk ∈ omegaSet then 1 else 0 := hom.getElem_eq_ite vk
    have hbom_w : b_om < 2 ^ w := by rw [hbom_eq]; split_ifs <;> omega
    let s₁ := s.setReg 3 b_om
    have hex₁ : Exec w (.assign 3 (.read 9 (.reg 20))) s s₁ 3 :=
      .assign (by simp [Expr.eval, checkWord, hr20, hk_w, hk_om_lt, b_om, hbom_w])
    have hk_deg_lt : k < (s.arrs 2).length := by rw [hdeg_len]; exact hk_lt
    let deg_k := (edgeNeighbors edges₀ vk).length
    have hdeg_get : (s.arrs 2)[k]'hk_deg_lt = deg_k := hdeg_val vk
    have hdeg_k_w : deg_k < 2 ^ w := hdeg_w vk
    let s₂ := s₁.setReg 4 deg_k
    have hex₂ : Exec w (.assign 4 (.read 2 (.reg 20))) s₁ s₂ 3 :=
      .assign (by simp [s₁, State.setReg, Expr.eval, checkWord, hr20, hk_w, hk_deg_lt, hdeg_get, hdeg_k_w])
    let b_iso := if deg_k = 0 then 1 else 0
    have hbiso_eq : (if deg_k = 0 then 1 else 0) = b_iso := rfl
    let flag := b_om * b_iso
    have hbiso_w : b_iso < 2 ^ w := by dsimp [b_iso]; split_ifs <;> omega
    have hflag_w : flag < 2 ^ w := by dsimp [flag, b_iso]; rw [hbom_eq]; split_ifs <;> omega
    let s₃ := s₂.setReg 5 flag
    have hex₃ : Exec w (.assign 5 (.op .mul (.reg 3) (.op .eq (.reg 4) (.const 0)))) s₂ s₃ 6 :=
      .assign (by
        simp [s₂, s₁, State.setReg, Expr.eval, BinOp.eval, BinOp.raw, checkWord,
          hbom_w, hdeg_k_w, h0_w, hbiso_eq, hbiso_w, flag, hflag_w])
    have hstep : ∃ s₄ t_b,
        Exec w (.ite (.reg 5) alg86TypeIIIEmitProg .skip) s₃ s₄ t_b ∧
        t_b ≤ 18 * n + 68 ∧
        s₄.arrs outArr = pref_next ++ List.replicate (cap - pref_next.length) 0 ∧
        s₄.regs 20 = k ∧
        s₄.regs 25 = pref_next.length ∧
        s₄.regs 26 = cnt₀ + L_next.length ∧
        (∀ a : Arr, a ≠ outArr → a ≠ 17 → a ≠ 18 → s₄.arrs a = s.arrs a) ∧
        (∀ r : Reg, r ≠ 2 → r ≠ 3 → r ≠ 4 → r ≠ 5 →
          r ≠ 21 → r ≠ 22 → r ≠ 25 → r ≠ 26 → s₄.regs r = s.regs r) := by
      by_cases hkeep : vk ∈ omegaSet ∧ deg_k = 0
      · have hflag1 : flag = 1 := by simp [flag, b_iso, hbom_eq, hkeep.1, hkeep.2]
        have hcond5 : (Expr.reg 5).eval w s₃ = some 1 := by
          simp [s₃, State.setReg, Expr.eval, checkWord, hflag1, hw]
        have hL_next_eq : L_next = L_k ++ [({vk}, [])] := by
          simp [L_next, L_k, alg86TypeIIIPairs, hk_lt, vk, deg_k, hkeep.1, hkeep.2]
        have hpref_next_eq : pref_next = pref_k ++ encAlg86Subgraph ({vk} : Finset (Fin n)) [] := by
          simp [pref_next, pref_k, hL_next_eq, List.append_assoc]
        rcases alg86TypeIIIEmitProg_exec vk pref_k hpref_k_cap hw2 hn_w hcap_w (by omega) (s := s₃)
            hout hr14 hr20 hr25 hr26 with
          ⟨s₄, t₄, hex₄, ht₄, hout₄, hr25₄, hr26₄, harr₄, hreg₄⟩
        have hr20₄ : s₄.regs 20 = k := by
          rw [hreg₄ 20 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]
          exact hr20
        refine ⟨s₄, 1 + t₄, .ite_true hcond5 (by decide) hex₄, by omega,
          by simpa [hpref_next_eq] using hout₄,
          hr20₄,
          by simpa [hpref_next_eq] using hr25₄,
          by simp [hr26₄, hL_next_eq, L_k, Nat.add_assoc],
          fun a hout h17 h18 => by rw [harr₄ a hout h17 h18]; rfl,
          fun r h2 h3 h4 h5 h21 h22 h25 h26 => by
            rw [hreg₄ r h2 h3 h21 h22 h25 h26]
            simp [s₃, s₂, s₁, State.setReg, h3, h4, h5]⟩
      · have hflag0 : flag = 0 := by
          dsimp [flag, b_iso]
          rw [hbom_eq]
          by_cases hom_k : vk ∈ omegaSet
          · have hdeg0 : deg_k ≠ 0 := fun h => hkeep ⟨hom_k, h⟩
            simp [hom_k, hdeg0]
          · simp [hom_k]
        have hcond5 : (Expr.reg 5).eval w s₃ = some 0 := by
          simp [s₃, State.setReg, Expr.eval, checkWord, hflag0, h0_w]
        have hL_next_eq : L_next = L_k := by
          have hkeep' : ¬((⟨k, hk_lt⟩ : Fin n) ∈ omegaSet ∧ (edgeNeighbors edges₀ ⟨k, hk_lt⟩).length = 0) := hkeep
          simp only [L_next, L_k, alg86TypeIIIPairs, hk_lt, ↓reduceDIte, hkeep', ↓reduceIte]
        have hpref_next_eq : pref_next = pref_k := by
          simp [pref_next, pref_k, hL_next_eq]
        refine ⟨s₃, 1 + 1, .ite_false hcond5 (.skip s₃), by omega,
          by change s.arrs outArr = _; rw [hpref_next_eq]; exact hout,
          hr20,
          by change s.regs 25 = _; rw [hpref_next_eq]; exact hr25,
          by change s.regs 26 = _; rw [hL_next_eq]; exact hr26,
          fun _ _ _ _ => rfl,
          fun r _ h3 h4 h5 _ _ _ _ => by
            simp [s₃, s₂, s₁, State.setReg, h3, h4, h5]⟩
    rcases hstep with ⟨s₄, t_b, hex_b, ht_b, hout₄, hr20₄, hr25₄, hr26₄, harr₄, hreg₄⟩
    let s₅ := s₄.setReg 20 (k + 1)
    have hex_inc : Exec w (.assign 20 (.op .add (.reg 20) (.const 1))) s₄ s₅ 4 :=
      .assign (by
        simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hr20₄, hk_w, hw,
          show k + 1 < 2 ^ w by omega])
    have harr2_₅ : s₅.arrs 2 = s.arrs 2 := harr₄ 2 (by decide) (by decide) (by decide)
    rcases ih (k + 1) (by omega) (s := s₅)
        (hom.of_arr_eq (harr₄ 9 (by decide) (by decide) (by decide)))
        (by rw [harr2_₅, hdeg_len])
        (fun v => by simp only [harr2_₅]; exact hdeg_val v)
        hout₄
        (by
          change (s₄.setReg 20 (k + 1)).regs 14 = n
          rw [State.setReg_regs_ne _ _ (by decide),
              hreg₄ 14 (by decide) (by decide) (by decide) (by decide)
                (by decide) (by decide) (by decide) (by decide), hr14])
        rfl
        (by
          change (s₄.setReg 20 (k + 1)).regs 25 = pref_next.length
          rw [State.setReg_regs_ne _ _ (by decide), hr25₄])
        (by
          change (s₄.setReg 20 (k + 1)).regs 26 = cnt₀ + L_next.length
          rw [State.setReg_regs_ne _ _ (by decide), hr26₄]) with
      ⟨s₆, t₆, hex₆, ht₆, hout₆, hr25₆, hr26₆, harr₆, hreg₆⟩
    have hmul : (rem + 1) * (18 * n + 91) = (18 * n + 91) + rem * (18 * n + 91) := by ring
    refine ⟨s₆, 3 + ((3 + (3 + (6 + t_b))) + 4) + t₆,
      .while_true hcond (by omega) (.seq (.seq hex₁ (.seq hex₂ (.seq hex₃ hex_b))) hex_inc) hex₆,
      by linarith [ht_b, ht₆, hmul], hout₆, hr25₆, hr26₆,
      fun a hout h17 h18 => by rw [harr₆ a hout h17 h18]; exact harr₄ a hout h17 h18,
      fun r h2 h3 h4 h5 h20 h21 h22 h25 h26 => by
        rw [hreg₆ r h2 h3 h4 h5 h20 h21 h22 h25 h26]
        change (s₄.setReg 20 (k + 1)).regs r = s.regs r
        rw [State.setReg_regs_ne _ _ h20]
        exact hreg₄ r h2 h3 h4 h5 h21 h22 h25 h26⟩

theorem alg86TypeIIIPassProg_exec {w n cap : ℕ} (omegaSet : Finset (Fin n))
    (edges₀ : List (Fin n × Fin n))
    (pref₀ : List ℕ) (cnt₀ : ℕ)
    (hcap_le : pref₀.length + n * (n + 2) ≤ cap)
    (hw2 : 2 < 2 ^ w) (hn_w : n < 2 ^ w) (hm2_w : 2 * edges₀.length < 2 ^ w)
    (hcap_w : cap < 2 ^ w) (hcnt_w : cnt₀ + n < 2 ^ w) {s : State}
    (hom : IsBitSet omegaSet 9 s)
    (hdeg_len : (s.arrs 2).length = n)
    (hdeg_val : ∀ v : Fin n, (s.arrs 2)[v.1]'(by rw [hdeg_len]; exact v.2) = (edgeNeighbors edges₀ v).length)
    (hdeg_w : ∀ v : Fin n, (edgeNeighbors edges₀ v).length < 2 ^ w)
    (hout : s.arrs outArr = pref₀ ++ List.replicate (cap - pref₀.length) 0)
    (hr14 : s.regs 14 = n)
    (hr25 : s.regs 25 = pref₀.length)
    (hr26 : s.regs 26 = cnt₀) :
    let L := alg86TypeIIIPairs omegaSet edges₀ n
    ∃ s' t,
      Exec w alg86TypeIIIPassProg s s' t ∧
      t ≤ n * (18 * n + 91) + 5 ∧
      s'.arrs outArr =
        (pref₀ ++ L.flatMap (fun p => encAlg86Subgraph p.1 p.2)) ++
          List.replicate (cap - (pref₀ ++ L.flatMap (fun p => encAlg86Subgraph p.1 p.2)).length) 0 ∧
      s'.regs 25 = (pref₀ ++ L.flatMap (fun p => encAlg86Subgraph p.1 p.2)).length ∧
      s'.regs 26 = cnt₀ + L.length ∧
      (∀ a : Arr, a ≠ outArr → a ≠ 17 → a ≠ 18 → s'.arrs a = s.arrs a) ∧
      (∀ r : Reg, r ≠ 2 → r ≠ 3 → r ≠ 4 → r ≠ 5 →
        r ≠ 20 → r ≠ 21 → r ≠ 22 → r ≠ 25 → r ≠ 26 → s'.regs r = s.regs r) := by
  intro L
  have h0_w : 0 < 2 ^ w := by omega
  let s₁ := s.setReg 20 0
  have hex₁ : Exec w (.assign 20 (.const 0)) s s₁ 2 :=
    .assign (by simp [Expr.eval, checkWord, h0_w])
  rcases alg86TypeIIILoop_exec omegaSet edges₀ pref₀ cnt₀ hcap_le hw2 hn_w hm2_w hcap_w hcnt_w
      n 0 (by omega) (s := s₁)
      (hom.of_arr_eq rfl) hdeg_len hdeg_val hdeg_w
      (by simpa [s₁, alg86TypeIIIPairs] using hout)
      (by simp [s₁, State.setReg, hr14])
      rfl
      (by simpa [s₁, State.setReg, alg86TypeIIIPairs] using hr25)
      (by simpa [s₁, State.setReg, alg86TypeIIIPairs] using hr26) with
    ⟨s₂, t₂, hex₂, ht₂, hout₂, hr25₂, hr26₂, harr₂, hreg₂⟩
  refine ⟨s₂, 2 + t₂, .seq hex₁ hex₂, by omega, hout₂, hr25₂, hr26₂,
    fun a hout h17 h18 => by rw [harr₂ a hout h17 h18]; rfl,
    fun r h2 h3 h4 h5 h20 h21 h22 h25 h26 => by
      rw [hreg₂ r h2 h3 h4 h5 h20 h21 h22 h25 h26]
      simp [s₁, State.setReg, h20]⟩

/-! ## Section 6: Component, Tuple, Type II (Pass R2), and Case (c) (Pass D1) Subroutines -/

/-- The vertex set of the connected component of `G \ Z` containing `r`, computed as
`reachSet (restrictGraph G (Finset.univ \ Z)) r`. -/
noncomputable def alg86K {n : ℕ} (G : SimpleGraph (Fin n)) (Z : Finset (Fin n)) (r : Fin n) :
    Finset (Fin n) :=
  reachSet (restrictGraph G (Finset.univ \ Z)) r

/-- The attachment set `X ⊆ Z` of `alg86K G Z r`, defined as `extNeighborhood G (alg86K G Z r) ∩ Z`. -/
noncomputable def alg86X {n : ℕ} (G : SimpleGraph (Fin n)) (Z : Finset (Fin n)) (r : Fin n) :
    Finset (Fin n) :=
  extNeighborhood G (alg86K G Z r) ∩ Z

theorem alg86K_subset_sdiff_of_not_mem {n : ℕ} (G : SimpleGraph (Fin n))
    (Z : Finset (Fin n)) {r : Fin n} (hr : r ∉ Z) :
    alg86K G Z r ⊆ Finset.univ \ Z := by
  apply reachSet_subset_of_adj_closed
  · intro x _ y hadj
    exact (restrictGraph_adj G (Finset.univ \ Z) x y).mp hadj |>.2.1
  · exact Finset.mem_sdiff.mpr ⟨Finset.mem_univ r, hr⟩

theorem extNeighborhood_alg86K_subset_of_not_mem {n : ℕ} (G : SimpleGraph (Fin n))
    (Z : Finset (Fin n)) {r : Fin n} (hr : r ∉ Z) :
    extNeighborhood G (alg86K G Z r) ⊆ Z := by
  intro y hy
  rcases (mem_extNeighborhood G (alg86K G Z r) y).mp hy with ⟨hy_not, x, hxK, hadj⟩
  by_contra hyZ
  have hx_sdiff : x ∈ Finset.univ \ Z := alg86K_subset_sdiff_of_not_mem G Z hr hxK
  have hy_sdiff : y ∈ Finset.univ \ Z := Finset.mem_sdiff.mpr ⟨Finset.mem_univ y, hyZ⟩
  have hadj_r : (restrictGraph G (Finset.univ \ Z)).Adj x y :=
    (restrictGraph_adj G (Finset.univ \ Z) x y).mpr ⟨hx_sdiff, hy_sdiff, hadj⟩
  have hyK : y ∈ alg86K G Z r :=
    reachSet_adj_closed (restrictGraph G (Finset.univ \ Z)) r x hxK y hadj_r
  exact hy_not hyK

theorem alg86X_eq_extNeighborhood_of_not_mem {n : ℕ} (G : SimpleGraph (Fin n))
    (Z : Finset (Fin n)) {r : Fin n} (hr : r ∉ Z) :
    alg86X G Z r = extNeighborhood G (alg86K G Z r) :=
  Finset.inter_eq_left.mpr (extNeighborhood_alg86K_subset_of_not_mem G Z hr)

/-- Sorted list of vertices of `alg86X G Z r` in increasing order of `Fin n`. -/
noncomputable def alg86L {n : ℕ} (G : SimpleGraph (Fin n)) (Z : Finset (Fin n)) (r : Fin n) :
    List (Fin n) :=
  (List.finRange n).filter (· ∈ alg86X G Z r)

/-- 4-word tuple `(len, x₀, x₁, x₂)` summarizing `alg86L G Z r` (for `|alg86X G Z r| ≤ 3`). -/
noncomputable def alg86Tuple {n : ℕ} (G : SimpleGraph (Fin n)) (Z : Finset (Fin n)) (r : Fin n) :
    ℕ × ℕ × ℕ × ℕ :=
  let L := alg86L G Z r
  (L.length,
   if h0 : 0 < L.length then (L[0]'h0).1 else 0,
   if h1 : 1 < L.length then (L[1]'h1).1 else 0,
   if h2 : 2 < L.length then (L[2]'h2).1 else 0)

/-- The union `U` of all vertices `u ∉ Z` whose component in `G \ Z` has the same attachment
tuple `alg86Tuple G Z u = alg86Tuple G Z r`. -/
noncomputable def alg86U {n : ℕ} (G : SimpleGraph (Fin n)) (Z : Finset (Fin n)) (r : Fin n) :
    Finset (Fin n) :=
  (open Classical in Finset.univ.filter (fun u : Fin n => u ∉ Z ∧ alg86Tuple G Z u = alg86Tuple G Z r))

/-- Computes `alg86K G Z r` in `a_12` and `extNeighborhood G (alg86K G Z r)` in `a_13`
for the vertex `r` in `r_20`, using `G \ Z` in `(6, 7, 8)` and `G` in `(3, 4, 5)`. -/
def computeKAndExtNhdProg : Cmd :=
  .seq (bfsRegProg 14 20 6 7 8 12 15 2 3 4 5 6 7 8)
    (buildComplAndExtNhdProg 3 4 5 12 15 13)

theorem computeKAndExtNhdProg_exec {w n m : ℕ} (G : SimpleGraph (Fin n))
    (lists_G lists_Y : Fin n → List ℕ) (Z : Finset (Fin n)) (r : Fin n)
    (htot_G : totalAdjEntries lists_G ≤ 2 * m)
    (htot_Y : totalAdjEntries lists_Y ≤ 2 * m)
    (hw : 1 < 2 ^ w) (hn_w : n < 2 ^ w) {s : State}
    (hadj_G : IsAdjList G 3 4 5 lists_G s)
    (hent_G : (s.arrs 5).length < 2 ^ w)
    (hadj_Y : IsAdjList (restrictGraph G (Finset.univ \ Z)) 6 7 8 lists_Y s)
    (hent_Y : (s.arrs 8).length < 2 ^ w)
    (hr14 : s.regs 14 = n)
    (hr20 : s.regs 20 = r.1) :
    ∃ s' t,
      Exec w computeKAndExtNhdProg s s' t ∧
      t ≤ 53 * n + 86 * m + 33 ∧
      IsBitSet (alg86K G Z r) 12 s' ∧
      IsBitSet (extNeighborhood G (alg86K G Z r)) 13 s' ∧
      (∀ a : Arr, a ≠ 12 → a ≠ 13 → a ≠ 15 → s'.arrs a = s.arrs a) ∧
      (∀ reg : Reg, reg ≠ 2 → reg ≠ 3 → reg ≠ 4 → reg ≠ 5 →
        reg ≠ 6 → reg ≠ 7 → reg ≠ 8 → s'.regs reg = s.regs reg) := by
  rcases Triple.bfsRegProg_spec (w := w) (restrictGraph G (Finset.univ \ Z)) lists_Y r
      14 20 6 7 8 12 15 2 3 4 5 6 7 8
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      hw hn_w s ⟨hr14, hr20, hadj_Y, hent_Y⟩ with
    ⟨s₁, t₁, hex₁, ht₁, hvis₁⟩
  dsimp only at ht₁
  have harr₁ : ∀ a : Arr, a ≠ 12 → a ≠ 15 → s₁.arrs a = s.arrs a := by
    intro a ha12 ha15
    apply Exec.arrs_eq_of_not_mem_writtenArrs hex₁
    simp [bfsRegProg, bfsStepProg, queueInit, queuePush, queuePop, bfsLoopProg, forList, forUp,
      Cmd.writtenArrs, ha12, ha15]
  have hreg₁ : ∀ reg : Reg, reg ≠ 2 → reg ≠ 3 → reg ≠ 4 → reg ≠ 5 →
      reg ≠ 6 → reg ≠ 7 → reg ≠ 8 → s₁.regs reg = s.regs reg := by
    intro reg h2 h3 h4 h5 h6 h7 h8
    apply Exec.regs_eq_of_not_mem_writtenRegs hex₁
    simp [bfsRegProg, bfsStepProg, queueInit, queuePush, queuePop, bfsLoopProg, forList, forUp,
      Cmd.writtenRegs, h2, h3, h4, h5, h6, h7, h8]
  have hK₁ : IsBitSet (alg86K G Z r) 12 s₁ :=
    isBitSet_reachSet_of_bfs (restrictGraph G (Finset.univ \ Z)) r hvis₁
  have hadj_G₁ : IsAdjList G 3 4 5 lists_G s₁ :=
    hadj_G.of_arrs_eq (harr₁ 3 (by decide) (by decide))
      (harr₁ 4 (by decide) (by decide)) (harr₁ 5 (by decide) (by decide))
  have hent_G₁ : (s₁.arrs 5).length < 2 ^ w := by
    rw [harr₁ 5 (by decide) (by decide)]; exact hent_G
  have hr14₁ : s₁.regs 14 = n := by
    rw [hreg₁ 14 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), hr14]
  rcases buildComplAndExtNhdProg_exec G lists_G (alg86K G Z r) 3 4 5 12 15 13
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide)
      hw hn_w hadj_G₁ hent_G₁ hK₁ hr14₁ with
    ⟨s₂, t₂, hex₂, ht₂, _, hN₂, harr₂, hreg₂⟩
  refine ⟨s₂, t₁ + t₂, .seq hex₁ hex₂, by omega,
    hK₁.of_arr_eq (harr₂ 12 (by decide) (by decide)), hN₂,
    fun a h12 h13 h15 => by rw [harr₂ a h15 h13, harr₁ a h12 h15],
    fun reg h2 h3 h4 h5 h6 h7 h8 => by
      rw [hreg₂ reg h2 h3 h4 h5 h6 h7 h8, hreg₁ reg h2 h3 h4 h5 h6 h7 h8]⟩

/-- Writes coordinate `idx` of `a_16` (if `idx < r_21`) or `0` (otherwise) into `a_dst[r_20]`. -/
def writeTupleCoordProg (a_dst : Arr) (idx : ℕ) : Cmd :=
  .ite (.op .lt (.const idx) (.reg 21))
    (.seq (.assign 2 (.read 16 (.const idx)))
      (.write a_dst (.reg 20) (.reg 2)))
    (.write a_dst (.reg 20) (.const 0))

theorem writeTupleCoordProg_exec {w n : ℕ} (a_dst : Arr) (idx : ℕ) (r : Fin n) (L : List (Fin n))
    (hidx_w : idx < 2 ^ w) (hL_le : L.length ≤ n)
    (hw : 1 < 2 ^ w) (hn_w : n < 2 ^ w) {s : State}
    (hdst_len : (s.arrs a_dst).length = n)
    (h16_len : (s.arrs 16).length = n)
    (h16_get : ∀ i (hi : i < L.length), (s.arrs 16).getD i 0 = (L[i]'hi).1)
    (hr20 : s.regs 20 = r.1)
    (hr21 : s.regs 21 = L.length) :
    let val := if h : idx < L.length then (L[idx]'h).1 else 0
    ∃ s' t,
      Exec w (writeTupleCoordProg a_dst idx) s s' t ∧
      t ≤ 9 ∧
      s'.arrs a_dst = (s.arrs a_dst).set r.1 val ∧
      (∀ a : Arr, a ≠ a_dst → s'.arrs a = s.arrs a) ∧
      (∀ reg : Reg, reg ≠ 2 → s'.regs reg = s.regs reg) := by
  intro val
  have h0_w : 0 < 2 ^ w := by omega
  have hr_lt : r.1 < n := r.2
  have hr_w : r.1 < 2 ^ w := by omega
  have hL_w : L.length < 2 ^ w := by omega
  by_cases hlt : idx < L.length
  · have hcond : (Expr.op .lt (.const idx) (.reg 21)).eval w s = some 1 := by
      simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hr21, hidx_w, hL_w, hlt, hw]
    have hidx_lt_16 : idx < (s.arrs 16).length := by omega
    have hget_eq : (s.arrs 16)[idx] = (L[idx]'hlt).1 := by
      have h1 := h16_get idx hlt
      rwa [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hidx_lt_16, Option.getD_some] at h1
    have hval_lt_n : (L[idx]'hlt).1 < n := (L[idx]'hlt).2
    have hval_w : (s.arrs 16)[idx] < 2 ^ w := by rw [hget_eq]; omega
    let s₁ := s.setReg 2 (s.arrs 16)[idx]
    have hex₁ : Exec w (.assign 2 (.read 16 (.const idx))) s s₁ 3 :=
      .assign (by simp [Expr.eval, checkWord, hidx_w, hidx_lt_16, hval_w])
    let s₂ := s₁.writeArr a_dst r.1 (s.arrs 16)[idx]
    have hex₂ : Exec w (.write a_dst (.reg 20) (.reg 2)) s₁ s₂ 3 :=
      .write (by simp [s₁, Expr.eval, checkWord, hr20, hr_w])
        (by simp [s₁, Expr.eval, checkWord, hval_w]) (by simp [s₁, hdst_len, hr_lt])
    refine ⟨s₂, 3 + (3 + 3), .ite_true hcond (by omega) (.seq hex₁ hex₂), by omega, ?_,
      fun a ha => by simp [s₂, s₁, State.writeArr_arrs_ne _ _ _ ha],
      fun reg h2 => by simp [s₂, s₁, State.setReg, h2]⟩
    simp [s₂, s₁, State.writeArr, val, hlt, hget_eq]
  · have hcond : (Expr.op .lt (.const idx) (.reg 21)).eval w s = some 0 := by
      simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hr21, hidx_w, hL_w, hlt, h0_w]
    let s₁ := s.writeArr a_dst r.1 0
    have hex₁ : Exec w (.write a_dst (.reg 20) (.const 0)) s s₁ 3 :=
      .write (by simp [Expr.eval, checkWord, hr20, hr_w])
        (by simp [Expr.eval, checkWord, h0_w]) (by simp [hdst_len, hr_lt])
    refine ⟨s₁, 3 + 3, .ite_false hcond hex₁, by omega, ?_,
      fun a ha => by simp [s₁, State.writeArr_arrs_ne _ _ _ ha],
      fun reg _ => rfl⟩
    simp [s₁, State.writeArr, val, hlt]

/-- State predicate stating that arrays `52, 53, 54, 55` have length `n` and store
`alg86Tuple G Z u` for all `u : Fin n` with `u.1 < k`. -/
structure HasAlg86TuplesUpTo {n : ℕ} (G : SimpleGraph (Fin n)) (Z : Finset (Fin n))
    (k : ℕ) (s : State) : Prop where
  len52 : (s.arrs 52).length = n
  len53 : (s.arrs 53).length = n
  len54 : (s.arrs 54).length = n
  len55 : (s.arrs 55).length = n
  val : ∀ u : Fin n, u.1 < k →
    let L := alg86L G Z u
    (s.arrs 52)[u.1]'(by rw [len52]; exact u.2) = L.length ∧
    (s.arrs 53)[u.1]'(by rw [len53]; exact u.2) = (if h0 : 0 < L.length then (L[0]'h0).1 else 0) ∧
    (s.arrs 54)[u.1]'(by rw [len54]; exact u.2) = (if h1 : 1 < L.length then (L[1]'h1).1 else 0) ∧
    (s.arrs 55)[u.1]'(by rw [len55]; exact u.2) = (if h2 : 2 < L.length then (L[2]'h2).1 else 0)

theorem HasAlg86TuplesUpTo.of_arrs_eq {n k : ℕ} {G : SimpleGraph (Fin n)} {Z : Finset (Fin n)}
    {s s' : State} (h : HasAlg86TuplesUpTo G Z k s)
    (h52 : s'.arrs 52 = s.arrs 52) (h53 : s'.arrs 53 = s.arrs 53)
    (h54 : s'.arrs 54 = s.arrs 54) (h55 : s'.arrs 55 = s.arrs 55) :
    HasAlg86TuplesUpTo G Z k s' := by
  rcases h with ⟨hl52, hl53, hl54, hl55, hval⟩
  refine ⟨by rw [h52, hl52], by rw [h53, hl53], by rw [h54, hl54], by rw [h55, hl55], ?_⟩
  intro u hu
  simp only [h52, h53, h54, h55]
  exact hval u hu

/-- Full tuple-table predicate `HasAlg86TuplesUpTo G Z n s`. -/
abbrev HasAlg86Tuples {n : ℕ} (G : SimpleGraph (Fin n)) (Z : Finset (Fin n)) (s : State) : Prop :=
  HasAlg86TuplesUpTo G Z n s

theorem HasAlg86Tuples.of_arrs_eq {n : ℕ} {G : SimpleGraph (Fin n)} {Z : Finset (Fin n)}
    {s s' : State} (h : HasAlg86Tuples G Z s)
    (h52 : s'.arrs 52 = s.arrs 52) (h53 : s'.arrs 53 = s.arrs 53)
    (h54 : s'.arrs 54 = s.arrs 54) (h55 : s'.arrs 55 = s.arrs 55) :
    HasAlg86Tuples G Z s' :=
  HasAlg86TuplesUpTo.of_arrs_eq h h52 h53 h54 h55

/-- Per-vertex step of `precomputeXTuplesProg`: computes `alg86K G Z r` and `alg86L G Z r`,
and stores `(len, x₀, x₁, x₂)` into `52[r_20]..55[r_20]`. -/
def precomputeXTupleStepProg : Cmd :=
  .seq computeKAndExtNhdProg
    (.seq collectKProg
      (.seq (.write 52 (.reg 20) (.reg 21))
        (.seq (writeTupleCoordProg 53 0)
          (.seq (writeTupleCoordProg 54 1)
            (writeTupleCoordProg 55 2)))))

/-- Precomputes `alg86Tuple G Z u` for all `u : Fin n` into arrays `52, 53, 54, 55`. -/
def precomputeXTuplesProg : Cmd :=
  .seq (.alloc 52 (.reg 14))
    (.seq (.alloc 53 (.reg 14))
      (.seq (.alloc 54 (.reg 14))
        (.seq (.alloc 55 (.reg 14))
          (.seq (.assign 20 (.const 0))
            (forUp 20 (.reg 14) precomputeXTupleStepProg)))))

theorem precomputeXTupleStepProg_exec {w n m : ℕ} (G : SimpleGraph (Fin n))
    (lists_G lists_Y : Fin n → List ℕ) (Z : Finset (Fin n)) (r : Fin n)
    (htot_G : totalAdjEntries lists_G ≤ 2 * m)
    (htot_Y : totalAdjEntries lists_Y ≤ 2 * m)
    (hw2 : 2 < 2 ^ w) (hn_w : n < 2 ^ w) {s : State}
    (hadj_G : IsAdjList G 3 4 5 lists_G s)
    (hent_G : (s.arrs 5).length < 2 ^ w)
    (hadj_Y : IsAdjList (restrictGraph G (Finset.univ \ Z)) 6 7 8 lists_Y s)
    (hent_Y : (s.arrs 8).length < 2 ^ w)
    (hZ : IsBitSet Z 14 s)
    (htup : HasAlg86TuplesUpTo G Z r.1 s)
    (hr14 : s.regs 14 = n)
    (hr20 : s.regs 20 = r.1) :
    ∃ s' t,
      Exec w precomputeXTupleStepProg s s' t ∧
      t ≤ 77 * n + 86 * m + 71 ∧
      HasAlg86TuplesUpTo G Z (r.1 + 1) s' ∧
      (∀ a : Arr, a ≠ 12 → a ≠ 13 → a ≠ 15 → a ≠ 16 →
        a ≠ 52 → a ≠ 53 → a ≠ 54 → a ≠ 55 → s'.arrs a = s.arrs a) ∧
      (∀ reg : Reg, reg ≠ 2 → reg ≠ 3 → reg ≠ 4 → reg ≠ 5 →
        reg ≠ 6 → reg ≠ 7 → reg ≠ 8 → reg ≠ 21 → s'.regs reg = s.regs reg) := by
  have hw : 1 < 2 ^ w := by omega
  have h0_w : 0 < 2 ^ w := by omega
  rcases computeKAndExtNhdProg_exec G lists_G lists_Y Z r htot_G htot_Y hw hn_w
      hadj_G hent_G hadj_Y hent_Y hr14 hr20 with
    ⟨s₁, t₁, hex₁, ht₁, _, hN₁, harr₁, hreg₁⟩
  have hZ₁ : IsBitSet Z 14 s₁ := hZ.of_arr_eq (harr₁ 14 (by decide) (by decide) (by decide))
  have hr14₁ : s₁.regs 14 = n := by
    rw [hreg₁ 14 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), hr14]
  have hAB_iff : ∀ u : Fin n, u ∈ extNeighborhood G (alg86K G Z r) ∩ Z ↔
      u ∈ Z ∧ u ∈ extNeighborhood G (alg86K G Z r) := by
    intro u; rw [Finset.mem_inter, and_comm]
  rcases collectKProg_exec (extNeighborhood G (alg86K G Z r)) Z (extNeighborhood G (alg86K G Z r))
      hAB_iff hw hn_w hZ₁ hN₁ hr14₁ with
    ⟨s₂, t₂, hex₂, ht₂, hr21₂, h16_len₂, h16_get₂, harr₂, hreg₂⟩
  have hL_eq : (List.finRange n).filter (· ∈ extNeighborhood G (alg86K G Z r) ∩ Z) =
      alg86L G Z r := rfl
  rw [hL_eq] at hr21₂ h16_get₂
  have hL_le : (alg86L G Z r).length ≤ n := by
    dsimp [alg86L]
    exact (List.length_filter_le _ _).trans (by simp)
  have hL_w : (alg86L G Z r).length < 2 ^ w := by omega
  have hr20₂ : s₂.regs 20 = r.1 := by
    rw [hreg₂ 20 (by decide) (by decide) (by decide) (by decide),
        hreg₁ 20 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), hr20]
  have hr_w : r.1 < 2 ^ w := by omega
  have h52_eq₂ : s₂.arrs 52 = s.arrs 52 := by
    rw [harr₂ 52 (by decide), harr₁ 52 (by decide) (by decide) (by decide)]
  have h53_eq₂ : s₂.arrs 53 = s.arrs 53 := by
    rw [harr₂ 53 (by decide), harr₁ 53 (by decide) (by decide) (by decide)]
  have h54_eq₂ : s₂.arrs 54 = s.arrs 54 := by
    rw [harr₂ 54 (by decide), harr₁ 54 (by decide) (by decide) (by decide)]
  have h55_eq₂ : s₂.arrs 55 = s.arrs 55 := by
    rw [harr₂ 55 (by decide), harr₁ 55 (by decide) (by decide) (by decide)]
  let s₃ := s₂.writeArr 52 r.1 (alg86L G Z r).length
  have hex₃ : Exec w (.write 52 (.reg 20) (.reg 21)) s₂ s₃ 3 :=
    .write (by simp [Expr.eval, checkWord, hr20₂, hr_w])
      (by simp [Expr.eval, checkWord, hr21₂, hL_w])
      (by rw [h52_eq₂, htup.len52]; exact r.2)
  have h53_s₃ : s₃.arrs 53 = s.arrs 53 := by simp [s₃, h53_eq₂]
  have h54_s₃ : s₃.arrs 54 = s.arrs 54 := by simp [s₃, h54_eq₂]
  have h55_s₃ : s₃.arrs 55 = s.arrs 55 := by simp [s₃, h55_eq₂]
  have h16_s₃ : s₃.arrs 16 = s₂.arrs 16 := by simp [s₃]
  rcases writeTupleCoordProg_exec 53 0 r (alg86L G Z r) h0_w hL_le hw hn_w (s := s₃)
      (by rw [h53_s₃, htup.len53])
      (by rw [h16_s₃, h16_len₂])
      (fun i hi => by rw [h16_s₃]; exact h16_get₂ i hi)
      hr20₂ hr21₂ with
    ⟨s₄, t₄, hex₄, ht₄, h53₄, harr₄, hreg₄⟩
  have hr20₄ : s₄.regs 20 = r.1 := by rw [hreg₄ 20 (by decide)]; exact hr20₂
  have hr21₄ : s₄.regs 21 = (alg86L G Z r).length := by rw [hreg₄ 21 (by decide)]; exact hr21₂
  have h16_s₄ : s₄.arrs 16 = s₂.arrs 16 := by rw [harr₄ 16 (by decide), h16_s₃]
  rcases writeTupleCoordProg_exec 54 1 r (alg86L G Z r) hw hL_le hw hn_w (s := s₄)
      (by rw [harr₄ 54 (by decide), h54_s₃, htup.len54])
      (by rw [h16_s₄, h16_len₂])
      (fun i hi => by rw [h16_s₄]; exact h16_get₂ i hi)
      hr20₄ hr21₄ with
    ⟨s₅, t₅, hex₅, ht₅, h54₅, harr₅, hreg₅⟩
  have hr20₅ : s₅.regs 20 = r.1 := by rw [hreg₅ 20 (by decide)]; exact hr20₄
  have hr21₅ : s₅.regs 21 = (alg86L G Z r).length := by rw [hreg₅ 21 (by decide)]; exact hr21₄
  have h16_s₅ : s₅.arrs 16 = s₂.arrs 16 := by rw [harr₅ 16 (by decide), h16_s₄]
  rcases writeTupleCoordProg_exec 55 2 r (alg86L G Z r) hw2 hL_le hw hn_w (s := s₅)
      (by rw [harr₅ 55 (by decide), harr₄ 55 (by decide), h55_s₃, htup.len55])
      (by rw [h16_s₅, h16_len₂])
      (fun i hi => by rw [h16_s₅]; exact h16_get₂ i hi)
      hr20₅ hr21₅ with
    ⟨s₆, t₆, hex₆, ht₆, h55₆, harr₆, hreg₆⟩
  have h52₆ : s₆.arrs 52 = (s.arrs 52).set r.1 (alg86L G Z r).length := by
    rw [harr₆ 52 (by decide), harr₅ 52 (by decide), harr₄ 52 (by decide)]
    simp [s₃, State.writeArr, h52_eq₂]
  have h53₆ : s₆.arrs 53 = (s.arrs 53).set r.1 (if h0 : 0 < (alg86L G Z r).length then ((alg86L G Z r)[0]'h0).1 else 0) := by
    rw [harr₆ 53 (by decide), harr₅ 53 (by decide), h53₄, h53_s₃]
  have h54₆ : s₆.arrs 54 = (s.arrs 54).set r.1 (if h1 : 1 < (alg86L G Z r).length then ((alg86L G Z r)[1]'h1).1 else 0) := by
    rw [harr₆ 54 (by decide), h54₅, harr₄ 54 (by decide), h54_s₃]
  have h55₆' : s₆.arrs 55 = (s.arrs 55).set r.1 (if h2 : 2 < (alg86L G Z r).length then ((alg86L G Z r)[2]'h2).1 else 0) := by
    rw [h55₆, harr₅ 55 (by decide), harr₄ 55 (by decide), h55_s₃]
  have htup₆ : HasAlg86TuplesUpTo G Z (r.1 + 1) s₆ := by
    refine ⟨by rw [h52₆, List.length_set, htup.len52],
      by rw [h53₆, List.length_set, htup.len53],
      by rw [h54₆, List.length_set, htup.len54],
      by rw [h55₆', List.length_set, htup.len55], ?_⟩
    intro u hu
    simp only [h52₆, h53₆, h54₆, h55₆']
    by_cases hur : u.1 = r.1
    · have hu_eq : u = r := Fin.ext hur
      subst hu_eq
      simp [List.getElem_set_self]
    · have hu_lt : u.1 < r.1 := by omega
      have hne : r.1 ≠ u.1 := Ne.symm hur
      rw [List.getElem_set_ne hne, List.getElem_set_ne hne,
          List.getElem_set_ne hne, List.getElem_set_ne hne]
      exact htup.val u hu_lt
  refine ⟨s₆, t₁ + (t₂ + (3 + (t₄ + (t₅ + t₆)))),
    .seq hex₁ (.seq hex₂ (.seq hex₃ (.seq hex₄ (.seq hex₅ hex₆)))),
    by omega, htup₆,
    fun a h12 h13 h15 h16 h52 h53 h54 h55 => by
      rw [harr₆ a h55, harr₅ a h54, harr₄ a h53]
      simp [s₃, State.writeArr_arrs_ne _ _ _ h52, harr₂ a h16, harr₁ a h12 h13 h15],
    fun reg h2 h3 h4 h5 h6 h7 h8 h21 => by
      rw [hreg₆ reg h2, hreg₅ reg h2, hreg₄ reg h2]
      change s₂.regs reg = s.regs reg
      rw [hreg₂ reg h2 h3 h4 h21, hreg₁ reg h2 h3 h4 h5 h6 h7 h8]⟩

private theorem precomputeXTuplesLoop_exec {w n m : ℕ} (G : SimpleGraph (Fin n))
    (lists_G lists_Y : Fin n → List ℕ) (Z : Finset (Fin n))
    (htot_G : totalAdjEntries lists_G ≤ 2 * m)
    (htot_Y : totalAdjEntries lists_Y ≤ 2 * m)
    (hw2 : 2 < 2 ^ w) (hn_w : n < 2 ^ w)
    (rem k : ℕ) (hrem : k + rem = n) {s : State}
    (hadj_G : IsAdjList G 3 4 5 lists_G s)
    (hent_G : (s.arrs 5).length < 2 ^ w)
    (hadj_Y : IsAdjList (restrictGraph G (Finset.univ \ Z)) 6 7 8 lists_Y s)
    (hent_Y : (s.arrs 8).length < 2 ^ w)
    (hZ : IsBitSet Z 14 s)
    (htup : HasAlg86TuplesUpTo G Z k s)
    (hr14 : s.regs 14 = n)
    (hr20 : s.regs 20 = k) :
    ∃ s' t,
      Exec w (forUp 20 (.reg 14) precomputeXTupleStepProg) s s' t ∧
      t ≤ rem * (77 * n + 86 * m + 78) + 3 ∧
      HasAlg86TuplesUpTo G Z n s' ∧
      (∀ a : Arr, a ≠ 12 → a ≠ 13 → a ≠ 15 → a ≠ 16 →
        a ≠ 52 → a ≠ 53 → a ≠ 54 → a ≠ 55 → s'.arrs a = s.arrs a) ∧
      (∀ reg : Reg, reg ≠ 2 → reg ≠ 3 → reg ≠ 4 → reg ≠ 5 →
        reg ≠ 6 → reg ≠ 7 → reg ≠ 8 → reg ≠ 20 → reg ≠ 21 → s'.regs reg = s.regs reg) := by
  induction rem generalizing k s with
  | zero =>
    have hk_eq : k = n := by omega
    subst hk_eq
    have h0_w : 0 < 2 ^ w := by omega
    have hcond : (Expr.op .lt (.reg 20) (.reg 14)).eval w s = some 0 := by
      simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hr20, hr14, hn_w, h0_w]
    exact ⟨s, 3, .while_false hcond, by omega, htup, fun _ _ _ _ _ _ _ _ _ => rfl,
      fun _ _ _ _ _ _ _ _ _ _ => rfl⟩
  | succ rem ih =>
    have hw : 1 < 2 ^ w := by omega
    have hk_lt : k < n := by omega
    have hk_w : k < 2 ^ w := by omega
    let rFin : Fin n := ⟨k, hk_lt⟩
    have hcond : (Expr.op .lt (.reg 20) (.reg 14)).eval w s = some 1 := by
      simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hr20, hr14, hk_w, hn_w, hk_lt, hw]
    rcases precomputeXTupleStepProg_exec G lists_G lists_Y Z rFin htot_G htot_Y hw2 hn_w
        hadj_G hent_G hadj_Y hent_Y hZ htup hr14 hr20 with
      ⟨s₁, t₁, hex₁, ht₁, htup₁, harr₁, hreg₁⟩
    have hr20₁ : s₁.regs 20 = k := by
      rw [hreg₁ 20 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), hr20]
    let s₂ := s₁.setReg 20 (k + 1)
    have hex_inc : Exec w (.assign 20 (.op .add (.reg 20) (.const 1))) s₁ s₂ 4 :=
      .assign (by simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hr20₁, hk_w, hw,
        show k + 1 < 2 ^ w by omega])
    have harr₁_lt : ∀ a : Arr, a < 12 → s₁.arrs a = s.arrs a := by
      intro a ha
      dsimp [Arr] at *
      exact harr₁ a (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
    rcases ih (k + 1) (by omega) (s := s₂)
        (hadj_G.of_arrs_eq (harr₁_lt 3 (by decide)) (harr₁_lt 4 (by decide)) (harr₁_lt 5 (by decide)))
        (by simp [s₂, harr₁_lt 5 (by decide), hent_G])
        (hadj_Y.of_arrs_eq (harr₁_lt 6 (by decide)) (harr₁_lt 7 (by decide)) (harr₁_lt 8 (by decide)))
        (by simp [s₂, harr₁_lt 8 (by decide), hent_Y])
        (hZ.of_arr_eq (harr₁ 14 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)))
        (htup₁.of_arrs_eq rfl rfl rfl rfl)
        (by
          change (s₁.setReg 20 (k + 1)).regs 14 = n
          rw [State.setReg_regs_ne _ _ (by decide),
              hreg₁ 14 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), hr14])
        rfl with
      ⟨s₃, t₃, hex₃, ht₃, htup₃, harr₃, hreg₃⟩
    have hmul : (rem + 1) * (77 * n + 86 * m + 78) =
        (77 * n + 86 * m + 78) + rem * (77 * n + 86 * m + 78) := by ring
    refine ⟨s₃, 3 + (t₁ + 4) + t₃, .while_true hcond (by omega) (.seq hex₁ hex_inc) hex₃,
      by linarith [ht₁, ht₃, hmul], htup₃,
      fun a h12 h13 h15 h16 h52 h53 h54 h55 => by
        rw [harr₃ a h12 h13 h15 h16 h52 h53 h54 h55]
        exact harr₁ a h12 h13 h15 h16 h52 h53 h54 h55,
      fun reg h2 h3 h4 h5 h6 h7 h8 h20 h21 => by
        rw [hreg₃ reg h2 h3 h4 h5 h6 h7 h8 h20 h21]
        change (s₁.setReg 20 (k + 1)).regs reg = s.regs reg
        rw [State.setReg_regs_ne _ _ h20]
        exact hreg₁ reg h2 h3 h4 h5 h6 h7 h8 h21⟩

theorem precomputeXTuplesProg_exec {w n m : ℕ} (G : SimpleGraph (Fin n))
    (lists_G lists_Y : Fin n → List ℕ) (Z : Finset (Fin n))
    (htot_G : totalAdjEntries lists_G ≤ 2 * m)
    (htot_Y : totalAdjEntries lists_Y ≤ 2 * m)
    (hw2 : 2 < 2 ^ w) (hn_w : n < 2 ^ w) {s : State}
    (hadj_G : IsAdjList G 3 4 5 lists_G s)
    (hent_G : (s.arrs 5).length < 2 ^ w)
    (hadj_Y : IsAdjList (restrictGraph G (Finset.univ \ Z)) 6 7 8 lists_Y s)
    (hent_Y : (s.arrs 8).length < 2 ^ w)
    (hZ : IsBitSet Z 14 s)
    (hr14 : s.regs 14 = n) :
    ∃ s' t,
      Exec w precomputeXTuplesProg s s' t ∧
      t ≤ n * (77 * n + 86 * m + 82) + 9 ∧
      HasAlg86Tuples G Z s' ∧
      (∀ a : Arr, a ≠ 12 → a ≠ 13 → a ≠ 15 → a ≠ 16 →
        a ≠ 52 → a ≠ 53 → a ≠ 54 → a ≠ 55 → s'.arrs a = s.arrs a) ∧
      (∀ reg : Reg, reg ≠ 2 → reg ≠ 3 → reg ≠ 4 → reg ≠ 5 →
        reg ≠ 6 → reg ≠ 7 → reg ≠ 8 → reg ≠ 20 → reg ≠ 21 → s'.regs reg = s.regs reg) := by
  have h0_w : 0 < 2 ^ w := by omega
  let s₁ := s.setArr 52 (List.replicate n 0)
  have hex₁ : Exec w (.alloc 52 (.reg 14)) s s₁ (1 + n) :=
    .alloc (by simp [Expr.eval, checkWord, hr14, hn_w])
  let s₂ := s₁.setArr 53 (List.replicate n 0)
  have hex₂ : Exec w (.alloc 53 (.reg 14)) s₁ s₂ (1 + n) :=
    .alloc (by simp [s₁, Expr.eval, checkWord, hr14, hn_w])
  let s₃ := s₂.setArr 54 (List.replicate n 0)
  have hex₃ : Exec w (.alloc 54 (.reg 14)) s₂ s₃ (1 + n) :=
    .alloc (by simp [s₂, s₁, Expr.eval, checkWord, hr14, hn_w])
  let s₄ := s₃.setArr 55 (List.replicate n 0)
  have hex₄ : Exec w (.alloc 55 (.reg 14)) s₃ s₄ (1 + n) :=
    .alloc (by simp [s₃, s₂, s₁, Expr.eval, checkWord, hr14, hn_w])
  let s₅ := s₄.setReg 20 0
  have hex₅ : Exec w (.assign 20 (.const 0)) s₄ s₅ 2 :=
    .assign (by simp [Expr.eval, checkWord, h0_w])
  have harr₅ : ∀ a : Arr, a ≠ 52 → a ≠ 53 → a ≠ 54 → a ≠ 55 → s₅.arrs a = s.arrs a := by
    intro a h52 h53 h54 h55
    simp [s₅, s₄, s₃, s₂, s₁, State.setArr, h52, h53, h54, h55]
  have htup₅ : HasAlg86TuplesUpTo G Z 0 s₅ := by
    refine ⟨by simp [s₅, s₄, s₃, s₂, s₁, State.setArr],
      by simp [s₅, s₄, s₃, s₂, State.setArr],
      by simp [s₅, s₄, s₃, State.setArr],
      by simp [s₅, s₄, State.setArr],
      fun u hu => by omega⟩
  rcases precomputeXTuplesLoop_exec G lists_G lists_Y Z htot_G htot_Y hw2 hn_w n 0 (by omega)
      (s := s₅)
      (hadj_G.of_arrs_eq (harr₅ 3 (by decide) (by decide) (by decide) (by decide))
        (harr₅ 4 (by decide) (by decide) (by decide) (by decide))
        (harr₅ 5 (by decide) (by decide) (by decide) (by decide)))
      (by rw [harr₅ 5 (by decide) (by decide) (by decide) (by decide)]; exact hent_G)
      (hadj_Y.of_arrs_eq (harr₅ 6 (by decide) (by decide) (by decide) (by decide))
        (harr₅ 7 (by decide) (by decide) (by decide) (by decide))
        (harr₅ 8 (by decide) (by decide) (by decide) (by decide)))
      (by rw [harr₅ 8 (by decide) (by decide) (by decide) (by decide)]; exact hent_Y)
      (hZ.of_arr_eq (harr₅ 14 (by decide) (by decide) (by decide) (by decide)))
      htup₅
      (by simp [s₅, s₄, s₃, s₂, s₁, State.setReg, hr14])
      rfl with
    ⟨s₆, t₆, hex₆, ht₆, htup₆, harr₆, hreg₆⟩
  have hmul : n * (77 * n + 86 * m + 82) = 4 * n + n * (77 * n + 86 * m + 78) := by ring
  refine ⟨s₆, (1 + n) + ((1 + n) + ((1 + n) + ((1 + n) + (2 + t₆)))),
    .seq hex₁ (.seq hex₂ (.seq hex₃ (.seq hex₄ (.seq hex₅ hex₆)))),
    by linarith [ht₆, hmul], htup₆,
    fun a h12 h13 h15 h16 h52 h53 h54 h55 => by
      rw [harr₆ a h12 h13 h15 h16 h52 h53 h54 h55, harr₅ a h52 h53 h54 h55],
    fun reg h2 h3 h4 h5 h6 h7 h8 h20 h21 => by
      rw [hreg₆ reg h2 h3 h4 h5 h6 h7 h8 h20 h21]
      simp [s₅, s₄, s₃, s₂, s₁, State.setReg, h20]⟩

end GraphMinor.Compute
