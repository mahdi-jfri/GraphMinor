module

public import GraphMinor.Compute.Algorithm99Step8
import GraphMinor.Compute.Algorithm99Step4Scan

/-!
# Step (8) of Algorithm (9.9): keeping the edges of `G_{i+1}`

Step (8) of Algorithm (9.9) (Graph Minors XIII, page 105) lets `G_{i+1}` have "edges those edges
of $G_i$ with an end in $V(A)$ and the other end in $V(A) \cup X$". In the labels of `G_i` this is
the multigraph `G_i.restrictMult (step8Pred V_A X)` (`Algorithm99Step8.lean`).

This file writes its code. The program `step8RestrictProg` reads the triples `(u, w, m)` of
`G_i.enc` in order, and keeps a triple when `u ∈ V_A` and `w ∈ V_A ∪ X`, or `w ∈ V_A` and
`u ∈ V_A ∪ X`. It reads the two bit sets of `V_A` and `V_A ∪ X`, and the test is the word
`[u ∈ V_A] [w ∈ V_A ∪ X] + [w ∈ V_A] [u ∈ V_A ∪ X]`, which is nonzero exactly when the triple is
kept. The kept triples are pushed to a buffer, and the buffer is copied out at the end. The
program is the one of `deleteVerticesZProg` (`Algorithm105.lean`) with this test in place of the
test of `Z`. Since the kept pairs are the active pairs of the new graph in the same order
(`activePairsList_restrictMult`), the result is the code of the new graph
(`step8RestrictProg_exec`), in time `O(|active pairs of G_i|)`.
-/

@[expose] public section

namespace GraphMinor.Compute

/-- The triples of the pairs `ps` for which `P` holds, with the multiplicities of `G`. -/
def MultiDigraph.restrictTriplesAux {n : ℕ} (G : MultiDigraph n) (P : Fin n → Fin n → Prop)
    [DecidableRel P] : List (Fin n × Fin n) → List ℕ
  | [] => []
  | (u, v) :: ps =>
    if P u v then
      u.1 :: v.1 :: G.edgeMult u v :: G.restrictTriplesAux P ps
    else
      G.restrictTriplesAux P ps

theorem MultiDigraph.restrictTriplesAux_eq_flatTriples {n : ℕ}
    (G : MultiDigraph n) (P : Fin n → Fin n → Prop) [DecidableRel P]
    (ps : List (Fin n × Fin n)) :
    G.restrictTriplesAux P ps =
      (G.restrictMult P).flatTriples (ps.filter (fun p => decide (P p.1 p.2))) := by
  induction ps with
  | nil => rfl
  | cons p ps ih =>
    rcases p with ⟨u, v⟩
    by_cases h : P u v
    · simp [MultiDigraph.restrictTriplesAux, MultiDigraph.flatTriples, h, ih,
        MultiDigraph.restrictMult]
    · simp [MultiDigraph.restrictTriplesAux, h, ih]

theorem MultiDigraph.length_restrictTriplesAux {n : ℕ}
    (G : MultiDigraph n) (P : Fin n → Fin n → Prop) [DecidableRel P]
    (ps : List (Fin n × Fin n)) :
    (G.restrictTriplesAux P ps).length =
      3 * (ps.filter (fun p => decide (P p.1 p.2))).length := by
  rw [G.restrictTriplesAux_eq_flatTriples P, MultiDigraph.length_flatTriples]

/-- The active pairs of `G.restrictMult P` are the active pairs of `G` with `P`, in order. -/
theorem MultiDigraph.activePairsList_restrictMult {n : ℕ} (G : MultiDigraph n)
    (P : Fin n → Fin n → Prop) [DecidableRel P] :
    (G.restrictMult P).activePairsList =
      G.activePairsList.filter (fun p => decide (P p.1 p.2)) := by
  unfold MultiDigraph.activePairsList
  rw [List.filter_filter]
  refine List.filter_congr fun p _ => ?_
  simp only [MultiDigraph.restrictMult]
  by_cases h : P p.1 p.2 <;> simp [h, and_comm]

theorem MultiDigraph.enc_restrictMult_eq {n : ℕ} (G : MultiDigraph n)
    (P : Fin n → Fin n → Prop) [DecidableRel P] :
    (G.restrictMult P).enc =
      [n, (G.activePairsList.filter (fun p => decide (P p.1 p.2))).length] ++
        G.restrictTriplesAux P G.activePairsList := by
  rw [MultiDigraph.enc, MultiDigraph.numActivePairs, G.activePairsList_restrictMult P,
    G.restrictTriplesAux_eq_flatTriples P]

theorem MultiDigraph.numActivePairs_restrictMult_le {n : ℕ} (G : MultiDigraph n)
    (P : Fin n → Fin n → Prop) [DecidableRel P] :
    (G.restrictMult P).numActivePairs ≤ G.numActivePairs := by
  rw [MultiDigraph.numActivePairs, G.activePairsList_restrictMult P]
  exact List.length_filter_le _ _

/-- The test word of the program is nonzero exactly for the kept pairs. -/
theorem step8Pred_iff_word {v : ℕ} (V X : Finset (Fin v)) (u w : Fin v) :
    step8Pred V X u w ↔
      (if u ∈ V then 1 else 0) * (if w ∈ V ∪ X then 1 else 0) +
        (if w ∈ V then 1 else 0) * (if u ∈ V ∪ X then 1 else 0) ≠ 0 := by
  unfold step8Pred
  by_cases hu : u ∈ V <;> by_cases hw : w ∈ V <;> by_cases hu' : u ∈ V ∪ X <;>
    by_cases hw' : w ∈ V ∪ X <;> simp [hu, hw, hu', hw']

/-- One triple of `step8RestrictProg`: reads `(u, w)`, computes the test word in register
`r_base + 9`, and if it is nonzero appends `(u, w, m)` to `a_buf` and counts it in
`r_base + 1`. -/
def step8RestrictBody (a_src a_V a_U a_buf : Arr) (r_base : Reg) : Cmd :=
  .seq (readTripleEndpoints a_src (r_base + 4) (r_base + 6) (r_base + 7) (r_base + 8))
    (.seq (.assign (r_base + 9)
        (.op .add (.op .mul (.read a_V (.reg (r_base + 7))) (.read a_U (.reg (r_base + 8))))
          (.op .mul (.read a_V (.reg (r_base + 8))) (.read a_U (.reg (r_base + 7))))))
      (.ite (.reg (r_base + 9))
        (.seq (.assign (r_base + 9) (.read a_src (.op .add (.reg (r_base + 6)) (.const 2))))
          (.seq (bufPush3 a_buf (r_base + 5) (r_base + 7) (r_base + 8) (r_base + 9))
            (.assign (r_base + 1) (.op .add (.reg (r_base + 1)) (.const 1)))))
        .skip))

/-- The program of step (8) that writes `(G.restrictMult (step8Pred V X)).enc` into `a_dst`,
from `G.enc` in `a_src` and the bit sets of `V` and `V ∪ X` in `a_V` and `a_U`. -/
def step8RestrictProg (a_src a_V a_U a_buf a_dst : Arr) (r_base : Reg) : Cmd :=
  .seq (.assign r_base (.read a_src (.const 0)))
    (.seq (.assign (r_base + 3) (.read a_src (.const 1)))
      (.seq (.assign (r_base + 1) (.const 0))
        (.seq (.assign (r_base + 5) (.op .add (.const 2) (.op .mul (.const 3) (.reg (r_base + 3)))))
          (.seq (.alloc a_buf (.reg (r_base + 5)))
            (.seq (.write a_buf (.const 0) (.reg r_base))
              (.seq (.assign (r_base + 5) (.const 2))
                (.seq (.assign (r_base + 4) (.const 0))
                  (.seq (forUp (r_base + 4) (.reg (r_base + 3))
                      (step8RestrictBody a_src a_V a_U a_buf r_base))
                    (.seq (.write a_buf (.const 1) (.reg (r_base + 1)))
                      (readSliceProg a_buf (.const 0) a_dst
                        (.reg (r_base + 5)) (r_base + 6)))))))))))

theorem step8RestrictLoop_exec {w n : ℕ} (G : MultiDigraph n) (V X : Finset (Fin n))
    (a_src a_V a_U a_buf : ℕ) (r_base : ℕ)
    (hne_sb : a_src ≠ a_buf) (hne_vb : a_V ≠ a_buf) (hne_ub : a_U ≠ a_buf)
    (hw3 : 3 < 2 ^ w) (hn_w : n < 2 ^ w)
    (hm3_w : 2 + 3 * G.numActivePairs < 2 ^ w)
    (hedges_w : G.numEdges < 2 ^ w)
    (suff : List (Fin n × Fin n)) :
    ∀ (pref : List (Fin n × Fin n)),
      G.activePairsList = pref ++ suff →
      ∀ (pfx : List ℕ) (extra_buf m_acc : ℕ),
        pfx.length = 2 + 3 * m_acc →
        m_acc + (suff.filter (fun p => decide (step8Pred V X p.1 p.2))).length ≤ G.numActivePairs →
        ∀ {s : State},
          s.arrs a_src = G.enc ++ [] →
          s.arrs a_V = bitSetList V →
          s.arrs a_U = bitSetList (V ∪ X) →
          s.arrs a_buf = pfx ++ List.replicate (3 * suff.length + extra_buf) 0 →
          s.regs r_base = n →
          s.regs (r_base + 1) = m_acc →
          s.regs (r_base + 3) = G.numActivePairs →
          s.regs (r_base + 4) = pref.length →
          s.regs (r_base + 5) = pfx.length →
          ∃ s' t extra_buf',
            Exec w (forUp (r_base + 4) (.reg (r_base + 3))
              (step8RestrictBody a_src a_V a_U a_buf r_base)) s s' t ∧
            t ≤ 3 + 75 * suff.length ∧
            s'.arrs a_buf = pfx ++ G.restrictTriplesAux (step8Pred V X) suff ++ List.replicate extra_buf' 0 ∧
            s'.regs r_base = n ∧
            s'.regs (r_base + 1) =
              m_acc + (suff.filter (fun p => decide (step8Pred V X p.1 p.2))).length ∧
            s'.regs (r_base + 5) = (pfx ++ G.restrictTriplesAux (step8Pred V X) suff).length ∧
            (∀ a : ℕ, a ≠ a_buf → s'.arrs a = s.arrs a) ∧
            (∀ r < r_base, s'.regs r = s.regs r) := by
  have hw : 1 < 2 ^ w := by omega
  have hw2 : 2 < 2 ^ w := by omega
  have h0_w : 0 < 2 ^ w := by omega
  have hm'_w : G.numActivePairs < 2 ^ w := by omega
  induction suff with
  | nil =>
    intro pref hsplit pfx extra_buf m_acc hpfx_len hm_bound
      s hsrc hV hU hbuf hr0 hr1 hr3 hr4 hr5
    have hlen_pref : pref.length = G.numActivePairs := by
      have := congrArg List.length hsplit
      simp only [List.append_nil] at this
      exact this.symm
    have hcond : (Expr.op .lt (.reg (r_base + 4)) (.reg (r_base + 3))).eval w s = some 0 := by
      simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hr4, hr3, hlen_pref, hm'_w]
    refine ⟨s, 3, extra_buf, .while_false hcond, by simp, ?_, hr0, ?_, ?_,
      fun _ _ => rfl, fun _ _ => rfl⟩
    · simpa [MultiDigraph.restrictTriplesAux] using hbuf
    · simpa using hr1
    · simpa [MultiDigraph.restrictTriplesAux] using hr5
  | cons p ps ih =>
    rcases p with ⟨u, v⟩
    intro pref hsplit pfx extra_buf m_acc hpfx_len hm_bound
      s hsrc hV hU hbuf hr0 hr1 hr3 hr4 hr5
    let k := pref.length
    obtain ⟨hk_lt, hget_k⟩ := getElem_of_eq_append_cons hsplit
    have hk_m' : k < G.numActivePairs := hk_lt
    have hk_w : k < 2 ^ w := by omega
    have hcond : (Expr.op .lt (.reg (r_base + 4)) (.reg (r_base + 3))).eval w s = some 1 := by
      simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hr4, hr3, k, hk_m', hk_w, hm'_w, hw]
    -- 1. readTripleEndpoints a_src (r_base + 4) (r_base + 6) (r_base + 7) (r_base + 8)
    rcases readTripleEndpoints_exec G [] a_src (r_base + 4) (r_base + 6) (r_base + 7) (r_base + 8)
        k s (by omega) (by omega) (by omega)
        hw3 hn_w hm3_w hk_m' hsrc hr4 with
      ⟨s₁, t₁, hex₁, ht₁, hr6_1, hr7_1, hr8_1, harr₁, hreg₁⟩
    have hget_u : (G.activePairsList[k]'hk_m').1 = u := congrArg Prod.fst hget_k
    have hget_v : (G.activePairsList[k]'hk_m').2 = v := congrArg Prod.snd hget_k
    rw [hget_u] at hr7_1
    rw [hget_v] at hr8_1
    have hu_w : u.1 < 2 ^ w := Nat.lt_trans u.2 hn_w
    have hv_w : v.1 < 2 ^ w := Nat.lt_trans v.2 hn_w
    have hV₁ : s₁.arrs a_V = bitSetList V := by rw [harr₁]; exact hV
    have hU₁ : s₁.arrs a_U = bitSetList (V ∪ X) := by rw [harr₁]; exact hU
    have hu_lenV : u.1 < (s₁.arrs a_V).length := by rw [hV₁, length_bitSetList]; exact u.2
    have hv_lenV : v.1 < (s₁.arrs a_V).length := by rw [hV₁, length_bitSetList]; exact v.2
    have hu_lenU : u.1 < (s₁.arrs a_U).length := by rw [hU₁, length_bitSetList]; exact u.2
    have hv_lenU : v.1 < (s₁.arrs a_U).length := by rw [hU₁, length_bitSetList]; exact v.2
    let zu := if u ∈ V then 1 else 0
    let zv := if v ∈ V then 1 else 0
    let yu := if u ∈ V ∪ X then 1 else 0
    let yv := if v ∈ V ∪ X then 1 else 0
    have hzu_eq : (s₁.arrs a_V)[u.1]'hu_lenV = zu := by simp [hV₁, bitSetList, zu]
    have hzv_eq : (s₁.arrs a_V)[v.1]'hv_lenV = zv := by simp [hV₁, bitSetList, zv]
    have hyu_eq : (s₁.arrs a_U)[u.1]'hu_lenU = yu := by simp [hU₁, bitSetList, yu]
    have hyv_eq : (s₁.arrs a_U)[v.1]'hv_lenU = yv := by simp [hU₁, bitSetList, yv]
    have hzu_w : zu < 2 ^ w := by dsimp [zu]; split_ifs <;> omega
    have hzv_w : zv < 2 ^ w := by dsimp [zv]; split_ifs <;> omega
    have hyu_w : yu < 2 ^ w := by dsimp [yu]; split_ifs <;> omega
    have hyv_w : yv < 2 ^ w := by dsimp [yv]; split_ifs <;> omega
    have hzy1_w : zu * yv < 2 ^ w := by dsimp [zu, yv]; split_ifs <;> omega
    have hzy2_w : zv * yu < 2 ^ w := by dsimp [zv, yu]; split_ifs <;> omega
    have hzuv_w : zu * yv + zv * yu < 2 ^ w := by dsimp [zu, zv, yu, yv]; split_ifs <;> omega
    -- 2. assign (r_base + 9) the test word
    let s₂ := s₁.setReg (r_base + 9) (zu * yv + zv * yu)
    have hex₂ : Exec w (.assign (r_base + 9)
        (.op .add (.op .mul (.read a_V (.reg (r_base + 7))) (.read a_U (.reg (r_base + 8))))
          (.op .mul (.read a_V (.reg (r_base + 8))) (.read a_U (.reg (r_base + 7)))))) s₁ s₂ 12 :=
      .assign (by simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord,
        hr7_1, hr8_1, hu_w, hv_w, hu_lenV, hv_lenV, hu_lenU, hv_lenU, hzu_eq, hzv_eq, hyu_eq,
        hyv_eq, hzu_w, hzv_w, hyu_w, hyv_w, hzy1_w, hzy2_w, hzuv_w])
    have hsplit' : G.activePairsList = (pref ++ [(u, v)]) ++ ps := by
      simp [hsplit, List.append_assoc]
    -- 3. Branch on the test word
    have hword := step8Pred_iff_word V X u v
    by_cases hkeep : step8Pred V X u v
    · have hzuv_0 : zu * yv + zv * yu ≠ 0 := hword.mp hkeep
      have hcond_z : (Expr.reg (r_base + 9)).eval w s₂ = some (zu * yv + zv * yu) := by
        simp [s₂, Expr.eval, checkWord, hzuv_w]
      let m := G.edgeMult u v
      have hm_le : m ≤ G.numEdges := G.edgeMult_le_numEdges u v
      have hm_w : m < 2 ^ w := Nat.lt_of_le_of_lt hm_le hedges_w
      obtain ⟨hlen_m, hget_m⟩ := enc_getElem_triple_mult G [] hsrc hk_m'
      rw [hget_u, hget_v] at hget_m
      have hsrc₂ : s₂.arrs a_src = s.arrs a_src := by simp [s₂, harr₁]
      have hr6_2 : s₂.regs (r_base + 6) = 2 + 3 * k := by
        simp [s₂, hr6_1]
      have hidx_w : 2 + 3 * k < 2 ^ w := by omega
      have hidx2_w : 2 + 3 * k + 2 < 2 ^ w := by omega
      have hlen_m₂ : 2 + 3 * k + 2 < (s₂.arrs a_src).length := by rw [hsrc₂]; exact hlen_m
      have hget_m₂ : (s₂.arrs a_src)[2 + 3 * k + 2]'hlen_m₂ = m := by
        simpa [hsrc₂, m] using hget_m
      let s₃ := s₂.setReg (r_base + 9) m
      have hex₃ : Exec w (.assign (r_base + 9)
          (.read a_src (.op .add (.reg (r_base + 6)) (.const 2)))) s₂ s₃ 5 :=
        .assign (by simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hr6_2,
          hidx_w, hw2, hidx2_w, hlen_m₂, hget_m₂, hm_w])
      have hbuf₃ : s₃.arrs a_buf = pfx ++ List.replicate ((3 * ps.length + extra_buf) + 3) 0 := by
        have hlen_eq : 3 * ((u, v) :: ps).length + extra_buf = (3 * ps.length + extra_buf) + 3 := by
          simp; omega
        rw [← hlen_eq]
        simpa [s₃, s₂, harr₁] using hbuf
      have hr5_3 : s₃.regs (r_base + 5) = pfx.length := by
        simp [s₃, s₂, hreg₁ (r_base + 5) (by omega) (by omega) (by omega), hr5]
      have hr7_3 : s₃.regs (r_base + 7) = u.1 := by
        simp [s₃, s₂, hr7_1]
      have hr8_3 : s₃.regs (r_base + 8) = v.1 := by
        simp [s₃, s₂, hr8_1]
      have hr9_3 : s₃.regs (r_base + 9) = m := by simp [s₃]
      have hflt_uv :
          (List.filter (fun p => decide (step8Pred V X p.1 p.2)) ((u, v) :: ps)).length =
            (List.filter (fun p => decide (step8Pred V X p.1 p.2)) ps).length + 1 := by
        simp [hkeep]
      have hdel_uv :
          G.restrictTriplesAux (step8Pred V X) ((u, v) :: ps) =
            u.1 :: v.1 :: m :: G.restrictTriplesAux (step8Pred V X) ps := by
        simp [MultiDigraph.restrictTriplesAux, hkeep, m]
      have hm_acc_lt : m_acc + 1 ≤ G.numActivePairs := by
        rw [hflt_uv] at hm_bound; omega
      have hpos_w : pfx.length + 3 < 2 ^ w := by omega
      rcases bufPush3_exec a_buf (r_base + 5) (r_base + 7) (r_base + 8) (r_base + 9)
          pfx (3 * ps.length + extra_buf) u.1 v.1 m
          hw3 hpos_w hu_w hv_w hm_w hbuf₃ hr5_3 hr7_3 hr8_3 hr9_3 with
        ⟨s₄, t₄, hex₄, ht₄, hbuf₄, hr5_4, harr₄, hreg₄⟩
      have hr1_4 : s₄.regs (r_base + 1) = m_acc := by
        rw [hreg₄ _ (by omega)]
        simp [s₃, s₂, hreg₁ (r_base + 1) (by omega) (by omega) (by omega), hr1]
      have hm_acc_w : m_acc < 2 ^ w := by omega
      have hm_acc1_w : m_acc + 1 < 2 ^ w := by omega
      let s₅ := s₄.setReg (r_base + 1) (m_acc + 1)
      have hex₅ : Exec w (.assign (r_base + 1) (.op .add (.reg (r_base + 1)) (.const 1))) s₄ s₅ 4 :=
        .assign (by simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hr1_4, hm_acc_w, hw, hm_acc1_w])
      have hex_ite : Exec w
          (.ite (.reg (r_base + 9))
            (.seq (.assign (r_base + 9) (.read a_src (.op .add (.reg (r_base + 6)) (.const 2))))
              (.seq (bufPush3 a_buf (r_base + 5) (r_base + 7) (r_base + 8) (r_base + 9))
                (.assign (r_base + 1) (.op .add (.reg (r_base + 1)) (.const 1)))))
            .skip)
          s₂ s₅ (1 + (5 + (t₄ + 4))) :=
        .ite_true hcond_z (by omega) (.seq hex₃ (.seq hex₄ hex₅))
      have hex_body : Exec w (step8RestrictBody a_src a_V a_U a_buf r_base) s s₅
          (t₁ + (12 + (1 + (5 + (t₄ + 4))))) :=
        .seq hex₁ (.seq hex₂ hex_ite)
      have hr4_5 : s₅.regs (r_base + 4) = k := by
        simp only [s₅, State.setReg_regs_ne _ _ (by omega : (r_base + 4 : Reg) ≠ r_base + 1)]
        rw [hreg₄ _ (by omega)]
        simp [s₃, s₂, hreg₁ (r_base + 4) (by omega) (by omega) (by omega), hr4, k]
      let s₆ := s₅.setReg (r_base + 4) (k + 1)
      have hex_inc : Exec w (.assign (r_base + 4) (.op .add (.reg (r_base + 4)) (.const 1)))
          s₅ s₆ 4 :=
        .assign (by simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hr4_5, hk_w, hw,
          show k + 1 < 2 ^ w by omega])
      have hm_bound' :
          (m_acc + 1) + (ps.filter (fun p => decide (step8Pred V X p.1 p.2))).length ≤
            G.numActivePairs := by
        rw [hflt_uv] at hm_bound; omega
      rcases ih (pref ++ [(u, v)]) hsplit' (pfx ++ [u.1, v.1, m]) extra_buf (m_acc + 1)
          (by simp [hpfx_len]; omega) hm_bound' (s := s₆)
          (by simp only [s₆, s₅, State.setReg_arrs]; rw [harr₄ a_src hne_sb]; simp [s₃, s₂, harr₁, hsrc])
          (by simp only [s₆, s₅, State.setReg_arrs]; rw [harr₄ a_V hne_vb]; simp [s₃, s₂, harr₁, hV])
          (by simp only [s₆, s₅, State.setReg_arrs]; rw [harr₄ a_U hne_ub]; simp [s₃, s₂, harr₁, hU])
          (by simpa [s₆, s₅] using hbuf₄)
          (by simp only [s₆, s₅,
              State.setReg_regs_ne _ _ (by omega : (r_base : Reg) ≠ r_base + 4),
              State.setReg_regs_ne _ _ (by omega : (r_base : Reg) ≠ r_base + 1)];
              rw [hreg₄ _ (by omega)];
              simp [s₃, s₂, hreg₁ r_base (by omega) (by omega) (by omega), hr0])
          (by simp [s₆, s₅])
          (by simp only [s₆, s₅,
              State.setReg_regs_ne _ _ (by omega : (r_base + 3 : Reg) ≠ r_base + 4),
              State.setReg_regs_ne _ _ (by omega : (r_base + 3 : Reg) ≠ r_base + 1)];
              rw [hreg₄ _ (by omega)];
              simp [s₃, s₂, hreg₁ (r_base + 3) (by omega) (by omega) (by omega), hr3])
          (by simp [s₆, k])
          (by simp [s₆, s₅, hr5_4]) with
        ⟨s₇, t₇, extra_buf', hex₇, ht₇, hbuf₇, hr0_7, hr1_7, hr5_7, harr₇, hreg₇⟩
      refine ⟨s₇, 3 + ((t₁ + (12 + (1 + (5 + (t₄ + 4))))) + 4) + t₇, extra_buf',
        .while_true hcond (by omega) (.seq hex_body hex_inc) hex₇,
        by simp only [List.length_cons]; omega,
        by rw [hdel_uv]; simpa [List.append_assoc] using hbuf₇,
        hr0_7,
        by rw [hflt_uv]; omega,
        by rw [hdel_uv]; simpa [List.append_assoc] using hr5_7,
        fun a ha => by
          rw [harr₇ a ha]
          simp only [s₆, s₅, State.setReg_arrs]
          rw [harr₄ a ha]
          simp [s₃, s₂, harr₁],
        fun r hr => by
          rw [hreg₇ r hr]
          simp only [s₆, s₅,
            State.setReg_regs_ne _ _ (by omega : (r : Reg) ≠ r_base + 4),
            State.setReg_regs_ne _ _ (by omega : (r : Reg) ≠ r_base + 1)]
          rw [hreg₄ r (by omega)]
          simp [s₃, s₂,
            State.setReg_regs_ne _ _ (by omega : (r : Reg) ≠ r_base + 9),
            hreg₁ r (by omega) (by omega) (by omega)]⟩
    · have hzuv_ne : zu * yv + zv * yu = 0 := by
        by_contra hne
        exact hkeep (hword.mpr hne)
      have hcond_z : (Expr.reg (r_base + 9)).eval w s₂ = some 0 := by
        simp [s₂, Expr.eval, checkWord, hzuv_ne, h0_w]
      have hex_ite : Exec w
          (.ite (.reg (r_base + 9))
            (.seq (.assign (r_base + 9) (.read a_src (.op .add (.reg (r_base + 6)) (.const 2))))
              (.seq (bufPush3 a_buf (r_base + 5) (r_base + 7) (r_base + 8) (r_base + 9))
                (.assign (r_base + 1) (.op .add (.reg (r_base + 1)) (.const 1)))))
            .skip)
          s₂ s₂ (1 + 1) :=
        .ite_false hcond_z (.skip s₂)
      have hex_body : Exec w (step8RestrictBody a_src a_V a_U a_buf r_base) s s₂
          (t₁ + (12 + (1 + 1))) :=
        .seq hex₁ (.seq hex₂ hex_ite)
      have hr4_2 : s₂.regs (r_base + 4) = k := by
        simp [s₂, hreg₁ (r_base + 4) (by omega) (by omega) (by omega), hr4, k]
      let s₃ := s₂.setReg (r_base + 4) (k + 1)
      have hex_inc : Exec w (.assign (r_base + 4) (.op .add (.reg (r_base + 4)) (.const 1)))
          s₂ s₃ 4 :=
        .assign (by simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hr4_2, hk_w, hw,
          show k + 1 < 2 ^ w by omega])
      have hbuf₃ : s₃.arrs a_buf = pfx ++ List.replicate (3 * ps.length + (extra_buf + 3)) 0 := by
        have hlen_eq : 3 * ((u, v) :: ps).length + extra_buf = 3 * ps.length + (extra_buf + 3) := by
          simp; omega
        rw [← hlen_eq]
        simpa [s₃, s₂, harr₁] using hbuf
      have hm_bound' :
          m_acc + (ps.filter (fun p => decide (step8Pred V X p.1 p.2))).length ≤ G.numActivePairs := by
        simpa [hkeep] using hm_bound
      rcases ih (pref ++ [(u, v)]) hsplit' pfx (extra_buf + 3) m_acc
          hpfx_len hm_bound' (s := s₃)
          (by simp [s₃, s₂, harr₁, hsrc])
          (by simp [s₃, s₂, harr₁, hV])
          (by simp [s₃, s₂, harr₁, hU])
          hbuf₃
          (by simp [s₃, s₂, hreg₁ r_base (by omega) (by omega) (by omega), hr0])
          (by simp [s₃, s₂, hreg₁ (r_base + 1) (by omega) (by omega) (by omega), hr1])
          (by simp [s₃, s₂, hreg₁ (r_base + 3) (by omega) (by omega) (by omega), hr3])
          (by simp [s₃, k])
          (by simp [s₃, s₂, hreg₁ (r_base + 5) (by omega) (by omega) (by omega), hr5]) with
        ⟨s₄, t₄, extra_buf', hex₄, ht₄, hbuf₄, hr0_4, hr1_4, hr5_4, harr₄, hreg₄⟩
      refine ⟨s₄, 3 + ((t₁ + (12 + (1 + 1))) + 4) + t₄, extra_buf',
        .while_true hcond (by omega) (.seq hex_body hex_inc) hex₄,
        by simp only [List.length_cons]; omega,
        by simpa [MultiDigraph.restrictTriplesAux, hkeep] using hbuf₄,
        hr0_4,
        by simpa [hkeep] using hr1_4,
        by simpa [MultiDigraph.restrictTriplesAux, hkeep] using hr5_4,
        fun a ha => by rw [harr₄ a ha]; simp [s₃, s₂, harr₁],
        fun r hr => by
          rw [hreg₄ r hr]
          simp [s₃, s₂,
            State.setReg_regs_ne _ _ (by omega : (r : Reg) ≠ r_base + 4),
            State.setReg_regs_ne _ _ (by omega : (r : Reg) ≠ r_base + 9),
            hreg₁ r (by omega) (by omega) (by omega)]⟩

/-- **The kept edges of step (8)** (Graph Minors XIII, page 105). From `G.enc` in `a_src` and
the bit sets of `V` and `V ∪ X` in `a_V` and `a_U`, the program writes
`(G.restrictMult (step8Pred V X)).enc` into `a_dst`, in time `O(|active pairs of G|)`. It changes
only the arrays `a_buf`, `a_dst` and the registers from `r_base` on. -/
theorem step8RestrictProg_exec {w n : ℕ} (G : MultiDigraph n) (V X : Finset (Fin n))
    (a_src a_V a_U a_buf a_dst : ℕ) (r_base : ℕ)
    (hne_sb : a_src ≠ a_buf) (hne_vb : a_V ≠ a_buf) (hne_ub : a_U ≠ a_buf)
    (hne_bd : a_buf ≠ a_dst)
    (hw3 : 3 < 2 ^ w) (hn_w : n < 2 ^ w)
    (hm3_w : 2 + 3 * G.numActivePairs < 2 ^ w)
    (hedges_w : G.numEdges < 2 ^ w)
    {s : State}
    (hsrc : s.arrs a_src = G.enc)
    (hV : s.arrs a_V = bitSetList V) (hU : s.arrs a_U = bitSetList (V ∪ X)) :
    ∃ s' t,
      Exec w (step8RestrictProg a_src a_V a_U a_buf a_dst r_base) s s' t ∧
      t ≤ 130 * G.numActivePairs + 80 ∧
      s'.arrs a_dst = (G.restrictMult (step8Pred V X)).enc ∧
      (∀ a : ℕ, a ≠ a_buf → a ≠ a_dst → s'.arrs a = s.arrs a) ∧
      (∀ r < r_base, s'.regs r = s.regs r) := by
  have hw : 1 < 2 ^ w := by omega
  have hw2 : 2 < 2 ^ w := by omega
  have h0_w : 0 < 2 ^ w := by omega
  have hm'_w : G.numActivePairs < 2 ^ w := by omega
  have h3m'_w : 3 * G.numActivePairs < 2 ^ w := by omega
  have hsrc' : s.arrs a_src = G.enc ++ [] := by simp [hsrc]
  obtain ⟨h0_len, h0_val⟩ := enc_getElem_zero G [] hsrc'
  obtain ⟨h1_len, h1_val⟩ := enc_getElem_one G [] hsrc'
  -- 1. r_base := a_src[0]
  let s₁ := s.setReg r_base n
  have hex₁ : Exec w (.assign r_base (.read a_src (.const 0))) s s₁ 3 :=
    .assign (by simp [Expr.eval, checkWord, h0_w, h0_len, h0_val, hn_w])
  -- 2. r_base + 3 := a_src[1]
  let s₂ := s₁.setReg (r_base + 3) G.numActivePairs
  have hex₂ : Exec w (.assign (r_base + 3) (.read a_src (.const 1))) s₁ s₂ 3 :=
    .assign (by simp [s₁, Expr.eval, checkWord, hw, h1_len, h1_val, hm'_w])
  -- 3. r_base + 1 := 0
  let s₃ := s₂.setReg (r_base + 1) 0
  have hex₃ : Exec w (.assign (r_base + 1) (.const 0)) s₂ s₃ 2 :=
    .assign (by simp [Expr.eval, checkWord, h0_w])
  -- 4. r_base + 5 := 2 + 3 * (r_base + 3)
  let s₄ := s₃.setReg (r_base + 5) (2 + 3 * G.numActivePairs)
  have hex₄ : Exec w (.assign (r_base + 5)
      (.op .add (.const 2) (.op .mul (.const 3) (.reg (r_base + 3))))) s₃ s₄ 6 :=
    .assign (by simp [s₃, s₂, State.setReg, Expr.eval, BinOp.eval, BinOp.raw, checkWord,
      hw2, hw3, hm'_w, h3m'_w, hm3_w])
  -- 5. alloc a_buf (.reg (r_base + 5))
  let s₅ := s₄.setArr a_buf (List.replicate (2 + 3 * G.numActivePairs) 0)
  have hex₅ : Exec w (.alloc a_buf (.reg (r_base + 5))) s₄ s₅ (1 + (2 + 3 * G.numActivePairs)) :=
    .alloc (by simp [s₄, Expr.eval, checkWord, hm3_w])
  -- 6. write a_buf 0 (.reg r_base)
  let s₆ := s₅.writeArr a_buf 0 n
  have hex₆ : Exec w (.write a_buf (.const 0) (.reg r_base)) s₅ s₆ 3 :=
    .write (by simp [Expr.eval, checkWord, h0_w])
      (by simp [s₅, s₄, s₃, s₂, s₁, State.setReg, Expr.eval, checkWord, hn_w])
      (by simp [s₅])
  -- 7. r_base + 5 := 2, r_base + 4 := 0
  let s₇ := s₆.setReg (r_base + 5) 2
  have hex₇ : Exec w (.assign (r_base + 5) (.const 2)) s₆ s₇ 2 :=
    .assign (by simp [Expr.eval, checkWord, hw2])
  let s₈ := s₇.setReg (r_base + 4) 0
  have hex₈ : Exec w (.assign (r_base + 4) (.const 0)) s₇ s₈ 2 :=
    .assign (by simp [Expr.eval, checkWord, h0_w])
  -- 8. Run `step8RestrictLoop_exec`
  have hbuf₈ : s₈.arrs a_buf = [n, 0] ++ List.replicate (3 * G.activePairsList.length + 0) 0 := by
    simp only [s₈, s₇, s₆, s₅, State.setReg_arrs, State.writeArr_arrs_self,
      State.setArr_arrs_self, MultiDigraph.numActivePairs]
    rw [show 2 + 3 * G.activePairsList.length = 2 + (3 * G.activePairsList.length + 0) by omega,
      List.replicate_add]
    rfl
  have hm_bound₀ :
      0 + (G.activePairsList.filter (fun p => decide (step8Pred V X p.1 p.2))).length ≤
        G.numActivePairs := by
    simp only [Nat.zero_add, MultiDigraph.numActivePairs]
    exact List.length_filter_le _ _
  rcases step8RestrictLoop_exec G V X a_src a_V a_U a_buf r_base hne_sb hne_vb hne_ub hw3 hn_w hm3_w hedges_w
      G.activePairsList [] (by simp) [n, 0] 0 0 (by simp) hm_bound₀ (s := s₈)
      (by simp [s₈, s₇, s₆, s₅, s₄, s₃, s₂, s₁, show (a_src : Arr) ≠ a_buf from hne_sb, hsrc])
      (by simp [s₈, s₇, s₆, s₅, s₄, s₃, s₂, s₁, show (a_V : Arr) ≠ a_buf from hne_vb, hV])
      (by simp [s₈, s₇, s₆, s₅, s₄, s₃, s₂, s₁, show (a_U : Arr) ≠ a_buf from hne_ub, hU])
      hbuf₈
      (by simp [s₈, s₇, s₆, s₅, s₄, s₃, s₂, s₁, State.setReg])
      (by simp [s₈, s₇, s₆, s₅, s₄, s₃, State.setReg])
      (by simp [s₈, s₇, s₆, s₅, s₄, s₃, s₂, State.setReg])
      (by simp [s₈])
      (by simp [s₈, s₇, State.setReg]) with
    ⟨s₉, t₉, extra_buf', hex₉, ht₉, hbuf₉, _, hr1_9, hr5_9, harr₉, hreg₉⟩
  simp only [Nat.zero_add] at hr1_9
  let m_del := (G.activePairsList.filter (fun p => decide (step8Pred V X p.1 p.2))).length
  have hr1_9' : s₉.regs (r_base + 1) = m_del := hr1_9
  have hm_del_le : m_del ≤ G.numActivePairs := List.length_filter_le _ _
  have hm_del_w : m_del < 2 ^ w := by omega
  have hlen_enc_del : ([n, m_del] ++ G.restrictTriplesAux (step8Pred V X) G.activePairsList).length =
      2 + 3 * m_del := by
    simp [MultiDigraph.length_restrictTriplesAux, m_del]; omega
  have hr5_9' : s₉.regs (r_base + 5) = 2 + 3 * m_del := by
    rw [hr5_9]
    simp [MultiDigraph.length_restrictTriplesAux, m_del]
    omega
  -- 9. write a_buf 1 (.reg (r_base + 1))
  let s₁₀ := s₉.writeArr a_buf 1 m_del
  have hex₁₀ : Exec w (.write a_buf (.const 1) (.reg (r_base + 1))) s₉ s₁₀ 3 :=
    .write (by simp [Expr.eval, checkWord, hw])
      (by simp only [Expr.eval, hr1_9', checkWord_eq_some, and_true]; exact hm_del_w)
      (by rw [hbuf₉]; simp)
  have hbuf₁₀ : s₁₀.arrs a_buf =
      [] ++ (G.restrictMult (step8Pred V X)).enc ++ List.replicate extra_buf' 0 := by
    simp only [s₁₀, State.writeArr_arrs_self, hbuf₉, List.nil_append,
      MultiDigraph.enc_restrictMult_eq, m_del]
    rfl
  -- 10. readSliceProg a_buf 0 a_dst (.reg (r_base + 5)) (r_base + 6)
  have hall_del_w : ∀ x ∈ (G.restrictMult (step8Pred V X)).enc, x < 2 ^ w := by
    intro x hx
    simp only [MultiDigraph.enc, List.cons_append, List.nil_append, List.mem_cons] at hx
    rcases hx with rfl | rfl | hx
    · exact hn_w
    · exact Nat.lt_of_le_of_lt (G.numActivePairs_restrictMult_le (step8Pred V X)) hm'_w
    · exact all_lt_flatTriples (G.restrictMult (step8Pred V X)) (G.restrictMult (step8Pred V X)).activePairsList hn_w
        (fun q _ => Nat.lt_of_le_of_lt
          (le_trans ((G.restrictMult (step8Pred V X)).edgeMult_le_numEdges q.1 q.2)
            (G.numEdges_restrictMult_le (step8Pred V X)))
          hedges_w) x hx
  have hlen_del_eq : (G.restrictMult (step8Pred V X)).enc.length = 2 + 3 * m_del := by
    rw [MultiDigraph.enc_restrictMult_eq]
    exact hlen_enc_del
  have hoff_w : 0 + (2 + 3 * m_del) < 2 ^ w := by omega
  rcases readSliceProg_exec a_buf a_dst (.const 0) (r_base + 5) (r_base + 6)
      hne_bd (by omega)
      [] (G.restrictMult (step8Pred V X)).enc (List.replicate extra_buf' 0)
      rfl hlen_del_eq hall_del_w hw hoff_w (s := s₁₀)
      (by simp [Expr.eval, checkWord, h0_w])
      hbuf₁₀
      (by simp [s₁₀, hr5_9']) with
    ⟨s₁₁, t₁₁, hex₁₁, ht₁₁, hdst₁₁, harr₁₁, hreg₁₁⟩
  dsimp [Expr.cost] at ht₁₁
  have hlen_ap : G.activePairsList.length = G.numActivePairs := rfl
  rw [hlen_ap] at ht₉
  refine ⟨s₁₁, _,
    .seq hex₁ (.seq hex₂ (.seq hex₃ (.seq hex₄ (.seq hex₅ (.seq hex₆
      (.seq hex₇ (.seq hex₈ (.seq hex₉ (.seq hex₁₀ hex₁₁))))))))),
    by omega,
    hdst₁₁,
    fun a hab had => by
      rw [harr₁₁ a had]
      dsimp only [s₁₀]
      rw [State.writeArr_arrs_ne _ _ _ hab, harr₉ a hab]
      simp [s₈, s₇, s₆, s₅, s₄, s₃, s₂, s₁, show (a : Arr) ≠ a_buf from hab],
    fun r hr => by
      rw [hreg₁₁ r (by omega)]
      simp only [s₁₀, State.writeArr_regs]
      rw [hreg₉ r hr]
      simp [s₈, s₇, s₆, s₅, s₄, s₃, s₂, s₁,
        State.setReg_regs_ne _ _ (by omega : (r : Reg) ≠ r_base + 4),
        State.setReg_regs_ne _ _ (by omega : (r : Reg) ≠ r_base + 5),
        State.setReg_regs_ne _ _ (by omega : (r : Reg) ≠ r_base + 1),
        State.setReg_regs_ne _ _ (by omega : (r : Reg) ≠ r_base + 3),
        State.setReg_regs_ne _ _ (by omega : (r : Reg) ≠ r_base)]⟩


end GraphMinor.Compute
