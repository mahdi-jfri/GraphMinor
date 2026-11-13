module

public import GraphMinor.Compute.GM13PairCap

/-!
# One step of the pair cap of Graph Minors XIII, (4.3), Step (1)

The program of `GM13PairCapProg.lean` reads the encoding of `G` triple by triple. For the `k`-th
triple `(u, v, m)` it computes `(G.capPair δ).edgeMult u v`. For a loop this is `min m δ`. For
`v < u`, it subtracts the number of edges from `v` to `u` kept so far; these are in the triple
just before, if that triple is `(v, u, m')`. This file defines that step, `capPairValue`, and
proves that it computes the value in at most 40 steps.
-/

@[expose] public section

namespace GraphMinor.Compute

open MultiDigraph

/-- One step of the pair cap. Registers `r_base + 6`, `r_base + 7` and `r_base + 8` hold the
index `2 + 3k` of the `k`-th triple and its two ends `u, v`. The step writes the kept number of
edges from `u` to `v` into `r_base + 9`, using `r_base + 10` for the number of edges from `v` to
`u` that are already kept. -/
def capPairValue (δ : ℕ) (a_src : Arr) (r_base : Reg) : Cmd :=
  .seq (.assign (r_base + 10) (.const 0))
    (.ite (.op .eq (.reg (r_base + 7)) (.reg (r_base + 8)))
      (.assign (r_base + 9)
        (.readMin a_src (.op .add (.reg (r_base + 6)) (.const 2)) (.const δ)))
      (.seq
        (.ite (.op .lt (.reg (r_base + 8)) (.reg (r_base + 7)))
          (.ite (.op .eq (.read a_src (.op .sub (.reg (r_base + 6)) (.const 3)))
              (.reg (r_base + 8)))
            (.ite (.op .eq (.read a_src (.op .sub (.reg (r_base + 6)) (.const 2)))
                (.reg (r_base + 7)))
              (.assign (r_base + 10)
                (.readMin a_src (.op .sub (.reg (r_base + 6)) (.const 1)) (.const (δ + 1))))
              .skip)
            .skip)
          .skip)
        (.assign (r_base + 9)
          (.readMin a_src (.op .add (.reg (r_base + 6)) (.const 2))
            (.op .sub (.const (δ + 1)) (.reg (r_base + 10)))))))

private theorem eval_reg_eq {w : ℕ} {s : State} {r : Reg} {x : ℕ} (h : s.regs r = x)
    (hx : x < 2 ^ w) : (Expr.reg r).eval w s = some x := by
  simp [Expr.eval, h, checkWord, hx]

private theorem eval_const_eq {w x : ℕ} {s : State} (hx : x < 2 ^ w) :
    (Expr.const x).eval w s = some x := by
  simp [Expr.eval, checkWord, hx]

private theorem eval_op_eq {w : ℕ} {s : State} {bop : BinOp} {e₁ e₂ : Expr} {a b v : ℕ}
    (h₁ : e₁.eval w s = some a) (h₂ : e₂.eval w s = some b) (h : bop.eval w a b = some v) :
    (Expr.op bop e₁ e₂).eval w s = some v := by
  simp [Expr.eval, h₁, h₂, h]

private theorem binop_add {w a b : ℕ} (h : a + b < 2 ^ w) : BinOp.eval w .add a b = some (a + b) := by
  simp [BinOp.eval, BinOp.raw, checkWord, h]

private theorem binop_sub {w a b : ℕ} (h : a - b < 2 ^ w) : BinOp.eval w .sub a b = some (a - b) := by
  simp [BinOp.eval, BinOp.raw, checkWord, h]

private theorem binop_eq {w a b : ℕ} (hw : 1 < 2 ^ w) :
    BinOp.eval w .eq a b = some (if a = b then 1 else 0) := by
  have h0 : 0 < 2 ^ w := by omega
  by_cases h : a = b <;> simp [BinOp.eval, BinOp.raw, checkWord, h, hw, h0]

private theorem binop_lt {w a b : ℕ} (hw : 1 < 2 ^ w) :
    BinOp.eval w .lt a b = some (if a < b then 1 else 0) := by
  have h0 : 0 < 2 ^ w := by omega
  by_cases h : a < b <;> simp [BinOp.eval, BinOp.raw, checkWord, h, hw, h0]

private theorem eval_read_eq {w : ℕ} {s : State} {a : Arr} {idx : Expr} {i x : ℕ}
    (hi : idx.eval w s = some i) (hlen : i < (s.arrs a).length) (hget : (s.arrs a)[i] = x)
    (hx : x < 2 ^ w) : (Expr.read a idx).eval w s = some x := by
  simp [Expr.eval, hi, hlen, hget, checkWord, hx]

private theorem eval_readMin_eq {w : ℕ} {s : State} {a : Arr} {idx cap : Expr} {i c x : ℕ}
    (hi : idx.eval w s = some i) (hc : cap.eval w s = some c) (hlen : i < (s.arrs a).length)
    (hget : (s.arrs a)[i] = x) (hx : Nat.min x c < 2 ^ w) :
    (Expr.readMin a idx cap).eval w s = some (Nat.min x c) := by
  simp [Expr.eval, hi, hc, hlen, hget, checkWord, hx]

/-- The step `capPairValue` computes `(G.capPair δ).edgeMult u v` for the `k`-th active pair
`(u, v)` of `G`, in at most 40 steps. It changes only the registers `r_base + 9` and
`r_base + 10`. -/
theorem capPairValue_exec {w n : ℕ} (G : MultiDigraph n) (δ : ℕ) (extra : List ℕ)
    (a_src r_base k : ℕ) (hk : k < G.numActivePairs) {u v : Fin n}
    (hget : G.activePairsList[k]'hk = (u, v))
    (hw3 : 3 < 2 ^ w) (hn_w : n < 2 ^ w) (hδ_w : δ + 1 < 2 ^ w)
    (hm3_w : 2 + 3 * G.numActivePairs < 2 ^ w)
    {s : State} (hsrc : s.arrs a_src = G.enc ++ extra)
    (hr6 : s.regs (r_base + 6) = 2 + 3 * k) (hr7 : s.regs (r_base + 7) = u.1)
    (hr8 : s.regs (r_base + 8) = v.1) :
    ∃ x t, Exec w (capPairValue δ a_src r_base) s
      ((s.setReg (r_base + 10) x).setReg (r_base + 9) ((G.capPair δ).edgeMult u v)) t ∧
      t ≤ 40 := by
  have hw : 1 < 2 ^ w := by omega
  have h0_w : 0 < 2 ^ w := by omega
  have hδ0_w : δ < 2 ^ w := by omega
  have hk_lt : 2 + 3 * k + 2 < 2 ^ w := by omega
  have hu_w : u.1 < 2 ^ w := Nat.lt_trans u.2 hn_w
  have hv_w : v.1 < 2 ^ w := Nat.lt_trans v.2 hn_w
  have hm_le := G.capPair_edgeMult_le_succ δ u v
  -- the current multiplicity
  obtain ⟨hlen_m, hget_m⟩ := enc_getElem_triple_mult G extra hsrc hk
  rw [hget] at hget_m
  -- step 1: r_base + 10 := 0
  let s₁ := s.setReg (r_base + 10) 0
  have hex₁ : Exec w (.assign (r_base + 10) (.const 0)) s s₁ 2 := .assign (eval_const_eq h0_w)
  have hr6₁ : s₁.regs (r_base + 6) = 2 + 3 * k := by simp [s₁, hr6]
  have hr7₁ : s₁.regs (r_base + 7) = u.1 := by simp [s₁, hr7]
  have hr8₁ : s₁.regs (r_base + 8) = v.1 := by simp [s₁, hr8]
  have hr10₁ : s₁.regs (r_base + 10) = 0 := by simp [s₁]
  have hsrc₁ : s₁.arrs a_src = G.enc ++ extra := by simp [s₁, hsrc]
  have hidx2 : (Expr.op .add (.reg (r_base + 6)) (.const 2)).eval w s₁ = some (2 + 3 * k + 2) :=
    eval_op_eq (eval_reg_eq hr6₁ (by omega)) (eval_const_eq (by omega)) (binop_add hk_lt)
  have hlen_m₁ : 2 + 3 * k + 2 < (s₁.arrs a_src).length := by rw [hsrc₁, ← hsrc]; exact hlen_m
  have hget_m₁ : (s₁.arrs a_src)[2 + 3 * k + 2]'hlen_m₁ = G.edgeMult u v := by
    simp only [s₁, State.setReg_arrs]; exact hget_m
  by_cases huv : u = v
  · -- a loop
    subst huv
    have hcond : (Expr.op .eq (.reg (r_base + 7)) (.reg (r_base + 8))).eval w s₁ = some 1 := by
      rw [eval_op_eq (eval_reg_eq hr7₁ hu_w) (eval_reg_eq hr8₁ hu_w) (binop_eq hw)]
      simp
    have hval : (G.capPair δ).edgeMult u u = Nat.min (G.edgeMult u u) δ := G.capPair_loop δ u
    have hrd : (Expr.readMin a_src (.op .add (.reg (r_base + 6)) (.const 2)) (.const δ)).eval w s₁ =
        some ((G.capPair δ).edgeMult u u) := by
      rw [hval]
      exact eval_readMin_eq hidx2 (eval_const_eq hδ0_w) hlen_m₁ hget_m₁ (by rw [← hval]; omega)
    exact ⟨0, _, .seq hex₁ (.ite_true hcond (by decide) (.assign hrd)), by simp⟩
  have huv_val : u.1 ≠ v.1 := fun h => huv (Fin.ext h)
  have hcond₀ : (Expr.op .eq (.reg (r_base + 7)) (.reg (r_base + 8))).eval w s₁ = some 0 := by
    rw [eval_op_eq (eval_reg_eq hr7₁ hu_w) (eval_reg_eq hr8₁ hv_w) (binop_eq hw)]
    simp [huv_val]
  -- the last assignment, once `r_base + 10` holds `P`
  have hlast : ∀ (s₂ : State) (P : ℕ), P ≤ δ + 1 →
      s₂.regs (r_base + 6) = 2 + 3 * k → s₂.regs (r_base + 10) = P →
      s₂.arrs a_src = s₁.arrs a_src →
      (G.capPair δ).edgeMult u v = Nat.min (G.edgeMult u v) (δ + 1 - P) →
      Exec w (.assign (r_base + 9)
          (.readMin a_src (.op .add (.reg (r_base + 6)) (.const 2))
            (.op .sub (.const (δ + 1)) (.reg (r_base + 10)))))
        s₂ (s₂.setReg (r_base + 9) ((G.capPair δ).edgeMult u v)) 9 := by
    intro s₂ P hP hr6₂ hr10₂ harr₂ hval
    have hidx : (Expr.op .add (.reg (r_base + 6)) (.const 2)).eval w s₂ = some (2 + 3 * k + 2) :=
      eval_op_eq (eval_reg_eq hr6₂ (by omega)) (eval_const_eq (by omega)) (binop_add hk_lt)
    have hcap : (Expr.op .sub (.const (δ + 1)) (.reg (r_base + 10))).eval w s₂ =
        some (δ + 1 - P) :=
      eval_op_eq (eval_const_eq hδ_w) (eval_reg_eq hr10₂ (by omega)) (binop_sub (by omega))
    have hlen₂ : 2 + 3 * k + 2 < (s₂.arrs a_src).length := by rw [harr₂]; exact hlen_m₁
    have hget₂ : (s₂.arrs a_src)[2 + 3 * k + 2]'hlen₂ = G.edgeMult u v := by
      simp only [harr₂]; exact hget_m₁
    have hrd := eval_readMin_eq hidx hcap hlen₂ hget₂ (by rw [← hval]; omega)
    rw [← hval] at hrd
    exact .assign hrd
  have hcost_last : (Expr.readMin a_src (.op .add (.reg (r_base + 6)) (.const 2))
      (.op .sub (.const (δ + 1)) (.reg (r_base + 10)))).cost + 1 = 9 := by simp
  by_cases hvu : v.1 < u.1
  · have hcond_lt : (Expr.op .lt (.reg (r_base + 8)) (.reg (r_base + 7))).eval w s₁ = some 1 := by
      rw [eval_op_eq (eval_reg_eq hr8₁ hv_w) (eval_reg_eq hr7₁ hu_w) (binop_lt hw)]
      simp [hvu]
    by_cases hpos : 0 < G.edgeMult v u
    · -- the triple just before is `(v, u, m(v, u))`
      obtain ⟨hk1, hprev⟩ := G.activePairsList_getElem_pred hk hget hvu hpos
      have hk' : k - 1 < G.numActivePairs := by omega
      obtain ⟨hlen_a, hget_a⟩ := enc_getElem_triple_fst G extra hsrc hk'
      obtain ⟨hlen_b, hget_b⟩ := enc_getElem_triple_snd G extra hsrc hk'
      obtain ⟨hlen_c, hget_c⟩ := enc_getElem_triple_mult G extra hsrc hk'
      have hprev' : G.activePairsList[k - 1]'hk' = (v, u) := hprev
      rw [hprev'] at hget_a hget_b hget_c
      have e3 : 2 + 3 * k - 3 = 2 + 3 * (k - 1) := by omega
      have e2 : 2 + 3 * k - 2 = 2 + 3 * (k - 1) + 1 := by omega
      have e1 : 2 + 3 * k - 1 = 2 + 3 * (k - 1) + 2 := by omega
      have hi3 : (Expr.op .sub (.reg (r_base + 6)) (.const 3)).eval w s₁ =
          some (2 + 3 * (k - 1)) := by
        rw [← e3]
        exact eval_op_eq (eval_reg_eq hr6₁ (by omega)) (eval_const_eq hw3) (binop_sub (by omega))
      have hi2 : (Expr.op .sub (.reg (r_base + 6)) (.const 2)).eval w s₁ =
          some (2 + 3 * (k - 1) + 1) := by
        rw [← e2]
        exact eval_op_eq (eval_reg_eq hr6₁ (by omega)) (eval_const_eq (by omega))
          (binop_sub (by omega))
      have hi1 : (Expr.op .sub (.reg (r_base + 6)) (.const 1)).eval w s₁ =
          some (2 + 3 * (k - 1) + 2) := by
        rw [← e1]
        exact eval_op_eq (eval_reg_eq hr6₁ (by omega)) (eval_const_eq hw) (binop_sub (by omega))
      have hlen_a₁ : 2 + 3 * (k - 1) < (s₁.arrs a_src).length := by rw [hsrc₁, ← hsrc]; exact hlen_a
      have hlen_b₁ : 2 + 3 * (k - 1) + 1 < (s₁.arrs a_src).length := by
        rw [hsrc₁, ← hsrc]; exact hlen_b
      have hlen_c₁ : 2 + 3 * (k - 1) + 2 < (s₁.arrs a_src).length := by
        rw [hsrc₁, ← hsrc]; exact hlen_c
      have hc1 : (Expr.op .eq (.read a_src (.op .sub (.reg (r_base + 6)) (.const 3)))
          (.reg (r_base + 8))).eval w s₁ = some 1 := by
        rw [eval_op_eq (eval_read_eq hi3 hlen_a₁ (by simp only [s₁, State.setReg_arrs]; exact hget_a)
          hv_w) (eval_reg_eq hr8₁ hv_w) (binop_eq hw)]
        simp
      have hc2 : (Expr.op .eq (.read a_src (.op .sub (.reg (r_base + 6)) (.const 2)))
          (.reg (r_base + 7))).eval w s₁ = some 1 := by
        rw [eval_op_eq (eval_read_eq hi2 hlen_b₁ (by simp only [s₁, State.setReg_arrs]; exact hget_b)
          hu_w) (eval_reg_eq hr7₁ hu_w) (binop_eq hw)]
        simp
      let P := Nat.min (G.edgeMult v u) (δ + 1)
      have hP : P ≤ δ + 1 := Nat.min_le_right _ _
      have hrdP : (Expr.readMin a_src (.op .sub (.reg (r_base + 6)) (.const 1))
          (.const (δ + 1))).eval w s₁ = some P :=
        eval_readMin_eq hi1 (eval_const_eq hδ_w) hlen_c₁
          (by simp only [s₁, State.setReg_arrs]; exact hget_c) (by omega)
      let s₂ := s₁.setReg (r_base + 10) P
      have hval : (G.capPair δ).edgeMult u v = Nat.min (G.edgeMult u v) (δ + 1 - P) := by
        simp [capPair_edgeMult, huv, hvu, P]
      have hex₃ := hlast s₂ P hP (by simp [s₂, hr6₁]) (by simp [s₂]) (by simp [s₂]) hval
      have hs₂ : s₂ = s.setReg (r_base + 10) P := by simp [s₂, s₁]
      have hall : Exec w (capPairValue δ a_src r_base) s
          (s₂.setReg (r_base + 9) ((G.capPair δ).edgeMult u v)) _ := Exec.seq hex₁ (.ite_false hcond₀ (.seq
        (.ite_true hcond_lt (by decide) (.ite_true hc1 (by decide)
          (.ite_true hc2 (by decide) (.assign hrdP)))) hex₃))
      rw [hs₂] at hall
      exact ⟨P, _, hall, by simp⟩
    · -- no edge from `v` to `u`, so the triple just before is not `(v, u, _)`
      have hzero : G.edgeMult v u = 0 := by omega
      have hval : (G.capPair δ).edgeMult u v = Nat.min (G.edgeMult u v) (δ + 1 - 0) := by
        simp [capPair_edgeMult, huv, hvu, hzero]
      have hex₃ := hlast s₁ 0 (Nat.zero_le _) hr6₁ hr10₁ rfl hval
      have hskip : ∃ t ≤ 20, Exec w
          (.ite (.op .eq (.read a_src (.op .sub (.reg (r_base + 6)) (.const 3)))
              (.reg (r_base + 8)))
            (.ite (.op .eq (.read a_src (.op .sub (.reg (r_base + 6)) (.const 2)))
                (.reg (r_base + 7)))
              (.assign (r_base + 10)
                (.readMin a_src (.op .sub (.reg (r_base + 6)) (.const 1)) (.const (δ + 1))))
              .skip)
            .skip) s₁ s₁ t := by
        by_cases hk0 : k = 0
        · subst hk0
          obtain ⟨h0len, h0val⟩ := enc_getElem_zero G extra hsrc
          have hi3 : (Expr.op .sub (.reg (r_base + 6)) (.const 3)).eval w s₁ = some 0 :=
            eval_op_eq (eval_reg_eq hr6₁ (by omega)) (eval_const_eq hw3) (binop_sub (by omega))
          have hc1 : (Expr.op .eq (.read a_src (.op .sub (.reg (r_base + 6)) (.const 3)))
              (.reg (r_base + 8))).eval w s₁ = some 0 := by
            rw [eval_op_eq (eval_read_eq hi3 (by rw [hsrc₁, ← hsrc]; exact h0len)
              (by simp only [s₁, State.setReg_arrs]; exact h0val) hn_w)
              (eval_reg_eq hr8₁ hv_w) (binop_eq hw)]
            simp [Nat.ne_of_gt v.2]
          exact ⟨_, by simp, .ite_false hc1 (.skip s₁)⟩
        · have hk' : k - 1 < G.numActivePairs := by omega
          obtain ⟨hlen_a, hget_a⟩ := enc_getElem_triple_fst G extra hsrc hk'
          obtain ⟨hlen_b, hget_b⟩ := enc_getElem_triple_snd G extra hsrc hk'
          have e3 : 2 + 3 * k - 3 = 2 + 3 * (k - 1) := by omega
          have e2 : 2 + 3 * k - 2 = 2 + 3 * (k - 1) + 1 := by omega
          have hi3 : (Expr.op .sub (.reg (r_base + 6)) (.const 3)).eval w s₁ =
              some (2 + 3 * (k - 1)) := by
            rw [← e3]
            exact eval_op_eq (eval_reg_eq hr6₁ (by omega)) (eval_const_eq hw3)
              (binop_sub (by omega))
          have hi2 : (Expr.op .sub (.reg (r_base + 6)) (.const 2)).eval w s₁ =
              some (2 + 3 * (k - 1) + 1) := by
            rw [← e2]
            exact eval_op_eq (eval_reg_eq hr6₁ (by omega)) (eval_const_eq (by omega))
              (binop_sub (by omega))
          set p := G.activePairsList[k - 1]'hk' with hp
          have hpa : p.1.1 < 2 ^ w := Nat.lt_trans p.1.2 hn_w
          have hpb : p.2.1 < 2 ^ w := Nat.lt_trans p.2.2 hn_w
          have hra := eval_read_eq hi3 (by rw [hsrc₁, ← hsrc]; exact hlen_a)
            (by simp only [s₁, State.setReg_arrs]; exact hget_a) hpa
          by_cases ha : p.1.1 = v.1
          · have hb : p.2.1 ≠ u.1 := by
              intro hb
              have hpe : p = (v, u) := Prod.ext (Fin.ext ha) (Fin.ext hb)
              have hmem : p ∈ G.activePairsList := List.getElem_mem hk'
              rw [hpe, mem_activePairsList] at hmem
              simp only at hmem
              omega
            have hc1 : (Expr.op .eq (.read a_src (.op .sub (.reg (r_base + 6)) (.const 3)))
                (.reg (r_base + 8))).eval w s₁ = some 1 := by
              rw [eval_op_eq hra (eval_reg_eq hr8₁ hv_w) (binop_eq hw)]
              simp [ha]
            have hrb := eval_read_eq hi2 (by rw [hsrc₁, ← hsrc]; exact hlen_b)
              (by simp only [s₁, State.setReg_arrs]; exact hget_b) hpb
            have hc2 : (Expr.op .eq (.read a_src (.op .sub (.reg (r_base + 6)) (.const 2)))
                (.reg (r_base + 7))).eval w s₁ = some 0 := by
              rw [eval_op_eq hrb (eval_reg_eq hr7₁ hu_w) (binop_eq hw)]
              simp [hb]
            exact ⟨_, by simp, .ite_true hc1 (by decide) (.ite_false hc2 (.skip s₁))⟩
          · have hc1 : (Expr.op .eq (.read a_src (.op .sub (.reg (r_base + 6)) (.const 3)))
                (.reg (r_base + 8))).eval w s₁ = some 0 := by
              rw [eval_op_eq hra (eval_reg_eq hr8₁ hv_w) (binop_eq hw)]
              simp [ha]
            exact ⟨_, by simp, .ite_false hc1 (.skip s₁)⟩
      obtain ⟨t₂, ht₂, hex₂⟩ := hskip
      refine ⟨0, _, .seq hex₁ (.ite_false hcond₀ (.seq (.ite_true hcond_lt (by decide) hex₂)
        hex₃)), ?_⟩
      simp only [Expr.cost_op, Expr.cost_reg]
      omega
  · have hcond_lt : (Expr.op .lt (.reg (r_base + 8)) (.reg (r_base + 7))).eval w s₁ = some 0 := by
      rw [eval_op_eq (eval_reg_eq hr8₁ hv_w) (eval_reg_eq hr7₁ hu_w) (binop_lt hw)]
      simp [hvu]
    have hval : (G.capPair δ).edgeMult u v = Nat.min (G.edgeMult u v) (δ + 1 - 0) := by
      simp [capPair_edgeMult, huv, hvu]
    have hex₃ := hlast s₁ 0 (Nat.zero_le _) hr6₁ hr10₁ rfl hval
    exact ⟨0, _, .seq hex₁ (.ite_false hcond₀ (.seq (.ite_false hcond_lt (.skip s₁)) hex₃)),
      by simp⟩

end GraphMinor.Compute
