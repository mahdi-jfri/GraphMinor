module

public import GraphMinor.Compute.GM13PairCapValue

/-!
# The Word RAM program for Step (1) of Graph Minors XIII, (4.3)

`capPairProg` reads the encoding of a multigraph `G` and writes the encoding of `G.capPair δ`:
at most `δ` loops at each vertex, and at most `δ + 1` edges between two distinct vertices,
counting both directions (Step (1) of (4.3), page 77, with the corrected cutoff; see the
correction to (4.3), Step (1), in `corrections/GM13.md`). It makes one pass over the triples of the
encoding, and each triple costs a bounded
number of steps (`capPairValue_exec`). The proof follows that of `capMultiDigraphProg_exec`.
-/

@[expose] public section

namespace GraphMinor.Compute

open MultiDigraph

/-- Loop body of `capPairProg`: reads the `k`-th triple `(u, v, m)`, computes the kept number
`(G.capPair δ).edgeMult u v` with `capPairValue`, and appends `(u, v, kept)` to `a_buf` when it is
positive, counting the triples in `r_base + 1` and the edges in `r_base + 2`. -/
def capPairBody (δ : ℕ) (a_src a_buf : Arr) (r_base : Reg) : Cmd :=
  .seq (readTripleEndpoints a_src (r_base + 4) (r_base + 6) (r_base + 7) (r_base + 8))
    (.seq (capPairValue δ a_src r_base)
      (.ite (.op .lt (.const 0) (.reg (r_base + 9)))
        (.seq (bufPush3 a_buf (r_base + 5) (r_base + 7) (r_base + 8) (r_base + 9))
          (.seq (.assign (r_base + 1) (.op .add (.reg (r_base + 1)) (.const 1)))
            (.assign (r_base + 2) (.op .add (.reg (r_base + 2)) (.reg (r_base + 9))))))
        .skip))

/-- Step (1) of Graph Minors XIII, (4.3), page 77, with the corrected cutoff (see the correction
to (4.3), Step (1), in `corrections/GM13.md`): write `(G.capPair δ).enc` into `a_dst`, using the
scratch array `a_buf` and the registers
`r_base .. r_base + 10`. -/
def capPairProg (δ : ℕ) (a_src a_buf a_dst : Arr) (r_base : Reg) : Cmd :=
  .seq (.assign r_base (.read a_src (.const 0)))
    (.seq (.assign (r_base + 3) (.read a_src (.const 1)))
      (.seq (.assign (r_base + 1) (.const 0))
        (.seq (.assign (r_base + 2) (.const 0))
          (.seq (.assign (r_base + 5)
              (.op .add (.const 2) (.op .mul (.const 3) (.reg (r_base + 3)))))
            (.seq (.alloc a_buf (.reg (r_base + 5)))
              (.seq (.write a_buf (.const 0) (.reg r_base))
                (.seq (.assign (r_base + 5) (.const 2))
                  (.seq (.assign (r_base + 4) (.const 0))
                    (.seq (forUp (r_base + 4) (.reg (r_base + 3))
                        (capPairBody δ a_src a_buf r_base))
                      (.seq (.write a_buf (.const 1) (.reg (r_base + 1)))
                        (readSliceProg a_buf (.const 0) a_dst
                          (.reg (r_base + 5)) (r_base + 6))))))))))))

/-- The loop of `capPairProg`, by induction on the triples still to be read. -/
theorem capPairLoop_exec {w n : ℕ} (G : MultiDigraph n) (δ : ℕ) (extra : List ℕ)
    (a_src a_buf : ℕ) (r_base : ℕ)
    (hne_sb : a_src ≠ a_buf)
    (hw3 : 3 < 2 ^ w) (hn_w : n < 2 ^ w) (hδ_w : δ + 1 < 2 ^ w)
    (hm3_w : 2 + 3 * G.numActivePairs < 2 ^ w)
    (suff pref : List (Fin n × Fin n))
    (hsplit : G.activePairsList = pref ++ suff)
    (pfx : List ℕ) (extra_buf m_acc e_acc : ℕ)
    (hpfx_len : pfx.length = 2 + 3 * m_acc)
    (hm_bound :
      m_acc + (suff.filter (fun p => decide (0 < (G.capPair δ).edgeMult p.1 p.2))).length ≤
        G.numActivePairs)
    (he_bound : e_acc + MultiDigraph.sumEdgeMult (G.capPair δ) suff < 2 ^ w)
    {s : State}
    (hsrc : s.arrs a_src = G.enc ++ extra)
    (hbuf : s.arrs a_buf = pfx ++ List.replicate (3 * suff.length + extra_buf) 0)
    (hr0 : s.regs r_base = n)
    (hr1 : s.regs (r_base + 1) = m_acc)
    (hr2 : s.regs (r_base + 2) = e_acc)
    (hr3 : s.regs (r_base + 3) = G.numActivePairs)
    (hr4 : s.regs (r_base + 4) = pref.length)
    (hr5 : s.regs (r_base + 5) = pfx.length) :
    ∃ s' t extra_buf',
      Exec w (forUp (r_base + 4) (.reg (r_base + 3)) (capPairBody δ a_src a_buf r_base))
        s s' t ∧
      t ≤ 3 + 92 * suff.length ∧
      s'.arrs a_buf = (pfx ++ MultiDigraph.capPairTriplesAux G δ suff) ++ List.replicate extra_buf' 0 ∧
      s'.regs r_base = n ∧
      s'.regs (r_base + 1) =
        m_acc + (suff.filter (fun p => decide (0 < (G.capPair δ).edgeMult p.1 p.2))).length ∧
      s'.regs (r_base + 2) = e_acc + MultiDigraph.sumEdgeMult (G.capPair δ) suff ∧
      s'.regs (r_base + 5) = (pfx ++ MultiDigraph.capPairTriplesAux G δ suff).length ∧
      (∀ a : ℕ, a ≠ a_buf → s'.arrs a = s.arrs a) ∧
      (∀ r < r_base, s'.regs r = s.regs r) := by
  have hw : 1 < 2 ^ w := by omega
  have hw2 : 2 < 2 ^ w := by omega
  have h0_w : 0 < 2 ^ w := by omega
  have hδ0_w : δ < 2 ^ w := by omega
  have hm'_w : G.numActivePairs < 2 ^ w := by omega
  induction suff generalizing pref pfx extra_buf m_acc e_acc s with
  | nil =>
    have hk_eq : pref.length = G.numActivePairs := by
      have := congrArg List.length hsplit
      simp [MultiDigraph.numActivePairs] at this ⊢
      omega
    have hcond : (Expr.op .lt (.reg (r_base + 4)) (.reg (r_base + 3))).eval w s = some 0 := by
      simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hr4, hr3, hk_eq, hm'_w, h0_w]
    refine ⟨s, 3, extra_buf, .while_false hcond, by omega,
      by simpa [MultiDigraph.capPairTriplesAux] using hbuf,
      hr0, by simpa using hr1, by simpa [MultiDigraph.sumEdgeMult] using hr2,
      by simpa [MultiDigraph.capPairTriplesAux] using hr5,
      fun _ _ => rfl, fun _ _ => rfl⟩
  | cons p ps ih =>
    rcases p with ⟨u, v⟩
    let k := pref.length
    obtain ⟨hk_lt, hget_k⟩ := getElem_of_eq_append_cons hsplit
    have hk_m' : k < G.numActivePairs := hk_lt
    have hk_w : k < 2 ^ w := by omega
    have hcond : (Expr.op .lt (.reg (r_base + 4)) (.reg (r_base + 3))).eval w s = some 1 := by
      simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hr4, hr3, k, hk_m', hk_w, hm'_w, hw]
    -- 1. readTripleEndpoints
    rcases readTripleEndpoints_exec G extra a_src (r_base + 4) (r_base + 6) (r_base + 7) (r_base + 8)
        k s (by omega) (by omega) (by omega) hw3 hn_w hm3_w hk_m' hsrc hr4 with
      ⟨s₁, t₁, hex₁, ht₁, hr6_1, hr7_1, hr8_1, harr₁, hreg₁⟩
    have hget_u : (G.activePairsList[k]'hk_m').1 = u := congrArg Prod.fst hget_k
    have hget_v : (G.activePairsList[k]'hk_m').2 = v := congrArg Prod.snd hget_k
    rw [hget_u] at hr7_1
    rw [hget_v] at hr8_1
    have hu_w : u.1 < 2 ^ w := Nat.lt_trans u.2 hn_w
    have hv_w : v.1 < 2 ^ w := Nat.lt_trans v.2 hn_w
    -- 2. the kept multiplicity, into r_base + 9
    let m := (G.capPair δ).edgeMult u v
    have hm_w : m < 2 ^ w := by
      have := G.capPair_edgeMult_le_succ δ u v; omega
    obtain ⟨x₁₀, t₂, hex₂, ht₂⟩ := capPairValue_exec G δ extra a_src r_base k hk_m' hget_k
      hw3 hn_w hδ_w hm3_w (by rw [harr₁]; exact hsrc) hr6_1 hr7_1 hr8_1
    let s₂ := (s₁.setReg (r_base + 10) x₁₀).setReg (r_base + 9) m
    have hsplit' : G.activePairsList = (pref ++ [(u, v)]) ++ ps := by
      simp [hsplit, List.append_assoc]
    -- 3. ite on 0 < (G.capPair δ).edgeMult u v
    by_cases hm_pos : 0 < (G.capPair δ).edgeMult u v
    · have hm_pos' : 0 < m := hm_pos
      have hcond_m : (Expr.op .lt (.const 0) (.reg (r_base + 9))).eval w s₂ = some 1 := by
        simp [s₂, Expr.eval, BinOp.eval, BinOp.raw, checkWord, h0_w, hm_w, hm_pos', hw]
      have hbuf₂ : s₂.arrs a_buf = pfx ++ List.replicate ((3 * ps.length + extra_buf) + 3) 0 := by
        have hlen_eq : 3 * ((u, v) :: ps).length + extra_buf = (3 * ps.length + extra_buf) + 3 := by
          simp; omega
        rw [← hlen_eq]
        simpa [s₂, harr₁] using hbuf
      have hr5_2 : s₂.regs (r_base + 5) = pfx.length := by
        simp [s₂, hreg₁ (r_base + 5) (by omega) (by omega) (by omega), hr5]
      have hr7_2 : s₂.regs (r_base + 7) = u.1 := by simp [s₂, hr7_1]
      have hr8_2 : s₂.regs (r_base + 8) = v.1 := by simp [s₂, hr8_1]
      have hr9_2 : s₂.regs (r_base + 9) = m := by simp [s₂]
      have hm_acc_lt : m_acc + 1 ≤ G.numActivePairs := by
        have hflt :
            (List.filter (fun p => decide (0 < (G.capPair δ).edgeMult p.1 p.2)) ((u, v) :: ps)).length =
              (List.filter (fun p => decide (0 < (G.capPair δ).edgeMult p.1 p.2)) ps).length + 1 := by
          simp only [List.filter_cons, hm_pos, decide_true, ↓reduceIte, List.length_cons]
        omega
      have hpos_w : pfx.length + 3 < 2 ^ w := by omega
      rcases bufPush3_exec a_buf (r_base + 5) (r_base + 7) (r_base + 8) (r_base + 9)
          pfx (3 * ps.length + extra_buf) u.1 v.1 m hw3 hpos_w hu_w hv_w hm_w
          hbuf₂ hr5_2 hr7_2 hr8_2 hr9_2 with
        ⟨s₃, t₃, hex₃, ht₃, hbuf₃, hr5_3, harr₃, hreg₃⟩
      have hr1_3 : s₃.regs (r_base + 1) = m_acc := by
        rw [hreg₃ _ (by omega)]
        simp [s₂, hreg₁ (r_base + 1) (by omega) (by omega) (by omega), hr1]
      have hm_acc_w : m_acc < 2 ^ w := by omega
      have hm_acc1_w : m_acc + 1 < 2 ^ w := by omega
      let s₄ := s₃.setReg (r_base + 1) (m_acc + 1)
      have hex₄ : Exec w (.assign (r_base + 1) (.op .add (.reg (r_base + 1)) (.const 1))) s₃ s₄ 4 :=
        .assign (by simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hr1_3, hm_acc_w, hw, hm_acc1_w])
      have hr2_4 : s₄.regs (r_base + 2) = e_acc := by
        simp only [s₄, State.setReg_regs_ne _ _ (show (r_base + 2 : Reg) ≠ r_base + 1 by omega)]
        rw [hreg₃ _ (by omega)]
        simp [s₂, hreg₁ (r_base + 2) (by omega) (by omega) (by omega), hr2]
      have hr9_4 : s₄.regs (r_base + 9) = m := by
        simp only [s₄, State.setReg_regs_ne _ _ (show (r_base + 9 : Reg) ≠ r_base + 1 by omega)]
        rw [hreg₃ _ (by omega)]
        exact hr9_2
      have he_acc_w : e_acc < 2 ^ w := by
        simp only [MultiDigraph.sumEdgeMult] at he_bound; omega
      have he_accm_w : e_acc + m < 2 ^ w := by
        change e_acc + ((G.capPair δ).edgeMult u v + MultiDigraph.sumEdgeMult (G.capPair δ) ps) < 2 ^ w at he_bound
        omega
      let s₅ := s₄.setReg (r_base + 2) (e_acc + m)
      have hex₅ : Exec w (.assign (r_base + 2) (.op .add (.reg (r_base + 2)) (.reg (r_base + 9))))
          s₄ s₅ 4 :=
        .assign (by simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hr2_4, hr9_4,
          he_acc_w, hm_w, he_accm_w])
      have hex_ite_m : Exec w
          (.ite (.op .lt (.const 0) (.reg (r_base + 9)))
            (.seq (bufPush3 a_buf (r_base + 5) (r_base + 7) (r_base + 8) (r_base + 9))
              (.seq (.assign (r_base + 1) (.op .add (.reg (r_base + 1)) (.const 1)))
                (.assign (r_base + 2) (.op .add (.reg (r_base + 2)) (.reg (r_base + 9))))))
            .skip)
          s₂ s₅ (3 + (t₃ + (4 + 4))) :=
        .ite_true hcond_m (by omega) (.seq hex₃ (.seq hex₄ hex₅))
      have hex_body : Exec w (capPairBody δ a_src a_buf r_base) s s₅
          (t₁ + (t₂ + (3 + (t₃ + (4 + 4))))) :=
        .seq hex₁ (.seq hex₂ hex_ite_m)
      have hr4_5 : s₅.regs (r_base + 4) = k := by
        simp only [s₅, s₄, State.setReg_regs_ne _ _ (show (r_base + 4 : Reg) ≠ r_base + 2 by omega),
          State.setReg_regs_ne _ _ (show (r_base + 4 : Reg) ≠ r_base + 1 by omega)]
        rw [hreg₃ _ (by omega)]
        simp [s₂, hreg₁ (r_base + 4) (by omega) (by omega) (by omega), hr4, k]
      let s₆ := s₅.setReg (r_base + 4) (k + 1)
      have hex_inc : Exec w (.assign (r_base + 4) (.op .add (.reg (r_base + 4)) (.const 1)))
          s₅ s₆ 4 :=
        .assign (by simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hr4_5, hk_w, hw,
          show k + 1 < 2 ^ w by omega])
      have hsrc₆ : s₆.arrs a_src = G.enc ++ extra := by
        simp only [s₆, s₅, s₄, State.setReg_arrs]
        rw [harr₃ a_src hne_sb]
        simp [s₂, harr₁, hsrc]
      have hbuf₆ : s₆.arrs a_buf = (pfx ++ [u.1, v.1, m]) ++ List.replicate (3 * ps.length + extra_buf) 0 := by
        simpa [s₆, s₅, s₄] using hbuf₃
      have hm_bound' :
          (m_acc + 1) + (ps.filter (fun p => decide (0 < (G.capPair δ).edgeMult p.1 p.2))).length ≤
            G.numActivePairs := by
        have hflt :
            (List.filter (fun p => decide (0 < (G.capPair δ).edgeMult p.1 p.2)) ((u, v) :: ps)).length =
              (List.filter (fun p => decide (0 < (G.capPair δ).edgeMult p.1 p.2)) ps).length + 1 := by
          simp only [List.filter_cons, hm_pos, decide_true, ↓reduceIte, List.length_cons]
        omega
      have he_bound' : (e_acc + m) + MultiDigraph.sumEdgeMult (G.capPair δ) ps < 2 ^ w := by
        change e_acc + ((G.capPair δ).edgeMult u v + MultiDigraph.sumEdgeMult (G.capPair δ) ps) < 2 ^ w at he_bound
        omega
      rcases ih (pref ++ [(u, v)]) hsplit' (pfx ++ [u.1, v.1, m]) extra_buf (m_acc + 1) (e_acc + m)
          (by simp [hpfx_len]; omega) hm_bound' he_bound' hsrc₆ hbuf₆
          (by simp only [s₆, s₅, s₄, State.setReg_regs_ne _ _ (by omega : (r_base : Reg) ≠ r_base + 4),
              State.setReg_regs_ne _ _ (by omega : (r_base : Reg) ≠ r_base + 2),
              State.setReg_regs_ne _ _ (by omega : (r_base : Reg) ≠ r_base + 1)];
              rw [hreg₃ _ (by omega)];
              simp [s₂, hreg₁ r_base (by omega) (by omega) (by omega), hr0])
          (by simp [s₆, s₅, s₄])
          (by simp [s₆, s₅])
          (by simp only [s₆, s₅, s₄,
              State.setReg_regs_ne _ _ (by omega : (r_base + 3 : Reg) ≠ r_base + 4),
              State.setReg_regs_ne _ _ (by omega : (r_base + 3 : Reg) ≠ r_base + 2),
              State.setReg_regs_ne _ _ (by omega : (r_base + 3 : Reg) ≠ r_base + 1)];
              rw [hreg₃ _ (by omega)];
              simp [s₂, hreg₁ (r_base + 3) (by omega) (by omega) (by omega), hr3])
          (by simp [s₆, k])
          (by simp [s₆, s₅, s₄, hr5_3]) with
        ⟨s₇, t₇, extra_buf', hex₇, ht₇, hbuf₇, hr0_7, hr1_7, hr2_7, hr5_7, harr₇, hreg₇⟩
      refine ⟨s₇, 3 + ((t₁ + (t₂ + (3 + (t₃ + (4 + 4))))) + 4) + t₇, extra_buf',
        .while_true hcond (by omega) (.seq hex_body hex_inc) hex₇,
        by simp only [List.length_cons]; omega,
        by simp only [MultiDigraph.capPairTriplesAux, hm_pos, ↓reduceIte]; simpa [m, List.append_assoc] using hbuf₇,
        hr0_7,
        by rw [hr1_7]
           have hflt :
               (List.filter (fun p => decide (0 < (G.capPair δ).edgeMult p.1 p.2)) ((u, v) :: ps)).length =
                 (List.filter (fun p => decide (0 < (G.capPair δ).edgeMult p.1 p.2)) ps).length + 1 := by
             simp only [List.filter_cons, hm_pos, decide_true, ↓reduceIte, List.length_cons]
           omega,
        by rw [hr2_7]; change e_acc + m + MultiDigraph.sumEdgeMult (G.capPair δ) ps =
             e_acc + (m + MultiDigraph.sumEdgeMult (G.capPair δ) ps); omega,
        by simp only [MultiDigraph.capPairTriplesAux, hm_pos, ↓reduceIte]; simpa [m, List.append_assoc] using hr5_7,
        fun a ha => by
          rw [harr₇ a ha]
          simp only [s₆, s₅, s₄, State.setReg_arrs]
          rw [harr₃ a ha]
          simp [s₂, harr₁],
        fun r hr => by
          rw [hreg₇ r hr]
          simp only [s₆, s₅, s₄,
            State.setReg_regs_ne _ _ (by omega : (r : Reg) ≠ r_base + 4),
            State.setReg_regs_ne _ _ (by omega : (r : Reg) ≠ r_base + 2),
            State.setReg_regs_ne _ _ (by omega : (r : Reg) ≠ r_base + 1)]
          rw [hreg₃ r (by omega)]
          simp [s₂, State.setReg_regs_ne _ _ (by omega : (r : Reg) ≠ r_base + 9),
            State.setReg_regs_ne _ _ (by omega : (r : Reg) ≠ r_base + 10),
            hreg₁ r (by omega) (by omega) (by omega)]⟩
    · have hm_pos' : ¬(0 < m) := hm_pos
      have hcond_m : (Expr.op .lt (.const 0) (.reg (r_base + 9))).eval w s₂ = some 0 := by
        simp [s₂, Expr.eval, BinOp.eval, BinOp.raw, checkWord, h0_w, hm_w, hm_pos']
      have hex_ite_m : Exec w
          (.ite (.op .lt (.const 0) (.reg (r_base + 9)))
            (.seq (bufPush3 a_buf (r_base + 5) (r_base + 7) (r_base + 8) (r_base + 9))
              (.seq (.assign (r_base + 1) (.op .add (.reg (r_base + 1)) (.const 1)))
                (.assign (r_base + 2) (.op .add (.reg (r_base + 2)) (.reg (r_base + 9))))))
            .skip)
          s₂ s₂ (3 + 1) :=
        .ite_false hcond_m (.skip s₂)
      have hex_body : Exec w (capPairBody δ a_src a_buf r_base) s s₂
          (t₁ + (t₂ + (3 + 1))) :=
        .seq hex₁ (.seq hex₂ hex_ite_m)
      have hr4_2 : s₂.regs (r_base + 4) = k := by
        simp [s₂, hreg₁ (r_base + 4) (by omega) (by omega) (by omega), hr4, k]
      let s₃ := s₂.setReg (r_base + 4) (k + 1)
      have hex_inc : Exec w (.assign (r_base + 4) (.op .add (.reg (r_base + 4)) (.const 1)))
          s₂ s₃ 4 :=
        .assign (by simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hr4_2, hk_w, hw,
          show k + 1 < 2 ^ w by omega])
      have hsrc₃ : s₃.arrs a_src = G.enc ++ extra := by
        simp [s₃, s₂, harr₁, hsrc]
      have hbuf₃ : s₃.arrs a_buf = pfx ++ List.replicate (3 * ps.length + (extra_buf + 3)) 0 := by
        have hlen_eq : 3 * ((u, v) :: ps).length + extra_buf = 3 * ps.length + (extra_buf + 3) := by
          simp; omega
        rw [← hlen_eq]
        simpa [s₃, s₂, harr₁] using hbuf
      have hm_bound' :
          m_acc + (ps.filter (fun p => decide (0 < (G.capPair δ).edgeMult p.1 p.2))).length ≤
            G.numActivePairs := by
        have hflt :
            (List.filter (fun p => decide (0 < (G.capPair δ).edgeMult p.1 p.2)) ((u, v) :: ps)).length =
              (List.filter (fun p => decide (0 < (G.capPair δ).edgeMult p.1 p.2)) ps).length := by
          simp only [List.filter_cons, hm_pos, decide_false, Bool.false_eq_true, ↓reduceIte]
        omega
      have hm_zero : (G.capPair δ).edgeMult u v = 0 := by omega
      have he_bound' : e_acc + MultiDigraph.sumEdgeMult (G.capPair δ) ps < 2 ^ w := by
        simp only [MultiDigraph.sumEdgeMult] at he_bound; omega
      rcases ih (pref ++ [(u, v)]) hsplit' pfx (extra_buf + 3) m_acc e_acc
          hpfx_len hm_bound' he_bound' hsrc₃ hbuf₃
          (by simp [s₃, s₂, hreg₁ r_base (by omega) (by omega) (by omega), hr0])
          (by simp [s₃, s₂, hreg₁ (r_base + 1) (by omega) (by omega) (by omega), hr1])
          (by simp [s₃, s₂, hreg₁ (r_base + 2) (by omega) (by omega) (by omega), hr2])
          (by simp [s₃, s₂, hreg₁ (r_base + 3) (by omega) (by omega) (by omega), hr3])
          (by simp [s₃, k])
          (by simp [s₃, s₂, hreg₁ (r_base + 5) (by omega) (by omega) (by omega), hr5]) with
        ⟨s₄, t₄, extra_buf', hex₄, ht₄, hbuf₄, hr0_4, hr1_4, hr2_4, hr5_4, harr₄, hreg₄⟩
      refine ⟨s₄, 3 + ((t₁ + (t₂ + (3 + 1))) + 4) + t₄, extra_buf',
        .while_true hcond (by omega) (.seq hex_body hex_inc) hex₄,
        by simp only [List.length_cons]; omega,
        by simp only [MultiDigraph.capPairTriplesAux, hm_pos, ↓reduceIte]; exact hbuf₄,
        hr0_4,
        by rw [hr1_4]
           have hflt :
               (List.filter (fun p => decide (0 < (G.capPair δ).edgeMult p.1 p.2)) ((u, v) :: ps)).length =
                 (List.filter (fun p => decide (0 < (G.capPair δ).edgeMult p.1 p.2)) ps).length := by
             simp only [List.filter_cons, hm_pos, decide_false, Bool.false_eq_true, ↓reduceIte]
           omega,
        by rw [hr2_4]; change e_acc + MultiDigraph.sumEdgeMult (G.capPair δ) ps =
             e_acc + ((G.capPair δ).edgeMult u v + MultiDigraph.sumEdgeMult (G.capPair δ) ps); omega,
        by simp only [MultiDigraph.capPairTriplesAux, hm_pos, ↓reduceIte]; exact hr5_4,
        fun a ha => by rw [harr₄ a ha]; simp [s₃, s₂, harr₁],
        fun r hr => by
          rw [hreg₄ r hr]
          simp [s₃, s₂,
            State.setReg_regs_ne _ _ (by omega : (r : Reg) ≠ r_base + 4),
            State.setReg_regs_ne _ _ (by omega : (r : Reg) ≠ r_base + 9),
            State.setReg_regs_ne _ _ (by omega : (r : Reg) ≠ r_base + 10),
            hreg₁ r (by omega) (by omega) (by omega)]⟩

/-- Specification for `capPairProg`: keeps at most `δ` loops at each vertex and at most `δ + 1`
edges between two distinct vertices, in `O(G.numActivePairs + 1)` steps, writing `(G.capPair δ).enc` into `a_dst` and setting
`r_base = n`, `r_base + 1 = (G.capPair δ).numActivePairs`, and `r_base + 2 = (G.capPair δ).numEdges`.
Works even when `G` has unbounded multiplicities `≥ 2 ^ w` in `a_src`. -/
theorem capPairProg_exec {w n : ℕ} (G : MultiDigraph n) (δ : ℕ) (extra : List ℕ)
    (a_src a_buf a_dst : ℕ) (r_base : ℕ)
    (hne_sb : a_src ≠ a_buf) (hne_bd : a_buf ≠ a_dst)
    (hw3 : 3 < 2 ^ w) (hn_w : n < 2 ^ w) (hδ_w : δ + 1 < 2 ^ w)
    (hm3_w : 2 + 3 * G.numActivePairs < 2 ^ w)
    (hedges_w : (G.capPair δ).numEdges < 2 ^ w)
    {s : State}
    (hsrc : s.arrs a_src = G.enc ++ extra) :
    ∃ s' t,
      Exec w (capPairProg δ a_src a_buf a_dst r_base) s s' t ∧
      t ≤ 150 * G.numActivePairs + 80 ∧
      s'.arrs a_dst = (G.capPair δ).enc ∧
      s'.regs r_base = n ∧
      s'.regs (r_base + 1) = (G.capPair δ).numActivePairs ∧
      s'.regs (r_base + 2) = (G.capPair δ).numEdges ∧
      (∀ a : ℕ, a ≠ a_buf → a ≠ a_dst → s'.arrs a = s.arrs a) ∧
      (∀ r < r_base, s'.regs r = s.regs r) := by
  have hw : 1 < 2 ^ w := by omega
  have hw2 : 2 < 2 ^ w := by omega
  have h0_w : 0 < 2 ^ w := by omega
  have hm'_w : G.numActivePairs < 2 ^ w := by omega
  have h3m'_w : 3 * G.numActivePairs < 2 ^ w := by omega
  -- 1. r_base := a_src[0]
  obtain ⟨h0_len, h0_val⟩ := enc_getElem_zero G extra hsrc
  let s₁ := s.setReg r_base n
  have hex₁ : Exec w (.assign r_base (.read a_src (.const 0))) s s₁ 3 :=
    .assign (by simp [Expr.eval, checkWord, h0_w, h0_len, h0_val, hn_w])
  -- 2. r_base + 3 := a_src[1]
  obtain ⟨h1_len, h1_val⟩ := enc_getElem_one G extra hsrc
  let s₂ := s₁.setReg (r_base + 3) G.numActivePairs
  have hex₂ : Exec w (.assign (r_base + 3) (.read a_src (.const 1))) s₁ s₂ 3 :=
    .assign (by simp [s₁, Expr.eval, checkWord, hw, h1_len, h1_val, hm'_w])
  -- 3. r_base + 1 := 0
  let s₃ := s₂.setReg (r_base + 1) 0
  have hex₃ : Exec w (.assign (r_base + 1) (.const 0)) s₂ s₃ 2 :=
    .assign (by simp [Expr.eval, checkWord, h0_w])
  -- 4. r_base + 2 := 0
  let s₄ := s₃.setReg (r_base + 2) 0
  have hex₄ : Exec w (.assign (r_base + 2) (.const 0)) s₃ s₄ 2 :=
    .assign (by simp [Expr.eval, checkWord, h0_w])
  -- 5. r_base + 5 := 2 + 3 * (r_base + 3)
  let s₅ := s₄.setReg (r_base + 5) (2 + 3 * G.numActivePairs)
  have hex₅ : Exec w (.assign (r_base + 5)
      (.op .add (.const 2) (.op .mul (.const 3) (.reg (r_base + 3))))) s₄ s₅ 6 :=
    .assign (by simp [s₄, s₃, s₂, Expr.eval, BinOp.eval, BinOp.raw, checkWord,
      hw2, hw3, hm'_w, h3m'_w, hm3_w])
  -- 6. alloc a_buf (r_base + 5)
  let s₆ := s₅.setArr a_buf (List.replicate (2 + 3 * G.numActivePairs) 0)
  have hex₆ : Exec w (.alloc a_buf (.reg (r_base + 5))) s₅ s₆ (1 + (2 + 3 * G.numActivePairs)) :=
    .alloc (by simp [s₅, Expr.eval, checkWord, hm3_w])
  -- 7. write a_buf 0 r_base
  let s₇ := s₆.writeArr a_buf 0 n
  have hex₇ : Exec w (.write a_buf (.const 0) (.reg r_base)) s₆ s₇ 3 :=
    .write (by simp [Expr.eval, checkWord, h0_w])
      (by simp [s₆, s₅, s₄, s₃, s₂, s₁, Expr.eval, checkWord, hn_w])
      (by simp [s₆])
  -- 8. r_base + 5 := 2
  let s₈ := s₇.setReg (r_base + 5) 2
  have hex₈ : Exec w (.assign (r_base + 5) (.const 2)) s₇ s₈ 2 :=
    .assign (by simp [Expr.eval, checkWord, hw2])
  -- 9. r_base + 4 := 0
  let s₉ := s₈.setReg (r_base + 4) 0
  have hex₉ : Exec w (.assign (r_base + 4) (.const 0)) s₈ s₉ 2 :=
    .assign (by simp [Expr.eval, checkWord, h0_w])
  -- 10. capPairLoop_exec
  have hbuf₉ : s₉.arrs a_buf = [n, 0] ++ List.replicate (3 * G.activePairsList.length + 0) 0 := by
    simp only [s₉, s₈, s₇, s₆, State.setReg_arrs, State.writeArr_arrs_self,
      State.setArr_arrs_self]
    have hrep : 2 + 3 * G.numActivePairs = 1 + (1 + 3 * G.activePairsList.length) := by
      simp [MultiDigraph.numActivePairs]; omega
    rw [hrep, List.replicate_add, List.replicate_add]
    rfl
  have hm_bound₉ :
      0 + (G.activePairsList.filter (fun p => decide (0 < (G.capPair δ).edgeMult p.1 p.2))).length ≤
        G.numActivePairs := by
    simp only [Nat.zero_add, MultiDigraph.numActivePairs]
    exact List.length_filter_le _ _
  have he_bound₉ : 0 + MultiDigraph.sumEdgeMult (G.capPair δ) G.activePairsList < 2 ^ w := by
    simpa [MultiDigraph.sumEdgeMult_capPair_activePairsList] using hedges_w
  rcases capPairLoop_exec G δ extra a_src a_buf r_base hne_sb hw3 hn_w hδ_w hm3_w
      G.activePairsList [] rfl [n, 0] 0 0 0 rfl hm_bound₉ he_bound₉
      (by simp [s₉, s₈, s₇, s₆, s₅, s₄, s₃, s₂, s₁, hne_sb, hsrc])
      hbuf₉
      (by simp [s₉, s₈, s₇, s₆, s₅, s₄, s₃, s₂, s₁])
      (by simp [s₉, s₈, s₇, s₆, s₅, s₄, s₃])
      (by simp [s₉, s₈, s₇, s₆, s₅, s₄])
      (by simp [s₉, s₈, s₇, s₆, s₅, s₄, s₃, s₂])
      (by simp [s₉])
      (by simp [s₉, s₈]) with
    ⟨s₁₀, t₁₀, extra_buf', hex₁₀, ht₁₀, hbuf₁₀, hr0_10, hr1_10, hr2_10, hr5_10, harr₁₀, hreg₁₀⟩
  rw [← MultiDigraph.flatTriples_capPair] at hbuf₁₀ hr5_10
  rw [Nat.zero_add, ← MultiDigraph.activePairsList_capPair] at hr1_10
  change s₁₀.regs (r_base + 1) = (G.capPair δ).numActivePairs at hr1_10
  rw [Nat.zero_add, MultiDigraph.sumEdgeMult_capPair_activePairsList] at hr2_10
  -- 11. write a_buf 1 (r_base + 1)
  have hcap_le : (G.capPair δ).numActivePairs ≤ G.numActivePairs := by
    simp only [MultiDigraph.numActivePairs, MultiDigraph.activePairsList_capPair]
    exact List.length_filter_le _ _
  have hcap_m'_w : (G.capPair δ).numActivePairs < 2 ^ w := by omega
  let s₁₁ := s₁₀.writeArr a_buf 1 (G.capPair δ).numActivePairs
  have hex₁₁ : Exec w (.write a_buf (.const 1) (.reg (r_base + 1))) s₁₀ s₁₁ 3 :=
    .write (by simp [Expr.eval, checkWord, hw])
      (by simp [Expr.eval, checkWord, hr1_10, hcap_m'_w])
      (by simp [hbuf₁₀])
  have hbuf₁₁ : s₁₁.arrs a_buf = [] ++ (G.capPair δ).enc ++ List.replicate extra_buf' 0 := by
    simp only [s₁₁, State.writeArr_arrs_self, hbuf₁₀, MultiDigraph.enc]
    rfl
  -- 12. readSliceProg a_buf (.const 0) a_dst (.reg (r_base + 5)) (r_base + 6)
  have hlen_enc_cap : (G.capPair δ).enc.length = 2 + 3 * (G.capPair δ).numActivePairs :=
    (G.capPair δ).length_enc
  have hr5_11 : s₁₁.regs (r_base + 5) = (G.capPair δ).enc.length := by
    simpa [s₁₁, MultiDigraph.enc] using hr5_10
  have henc_w : ∀ x ∈ (G.capPair δ).enc, x < 2 ^ w := by
    intro x hx
    simp only [MultiDigraph.enc, List.cons_append, List.nil_append, List.mem_cons] at hx
    rcases hx with rfl | rfl | hx
    · exact hn_w
    · exact hcap_m'_w
    · exact all_lt_flatTriples (G.capPair δ) (G.capPair δ).activePairsList hn_w
        (fun p _ => Nat.lt_of_le_of_lt (G.capPair_edgeMult_le_succ δ p.1 p.2) hδ_w) x hx
  have hoff_len_w : 0 + (G.capPair δ).enc.length < 2 ^ w := by omega
  rcases readSliceProg_exec a_buf a_dst (.const 0) (r_base + 5) (r_base + 6)
      hne_bd (by omega) [] (G.capPair δ).enc (List.replicate extra_buf' 0)
      rfl rfl henc_w hw hoff_len_w
      (by simp [Expr.eval, checkWord, h0_w])
      hbuf₁₁ hr5_11 with
    ⟨s₁₂, t₁₂, hex₁₂, ht₁₂, hdst₁₂, harr₁₂, hreg₁₂⟩
  have hlen_apl : G.activePairsList.length = G.numActivePairs := rfl
  rw [hlen_apl] at ht₁₀
  rw [hlen_enc_cap] at ht₁₂
  dsimp only [Expr.cost] at ht₁₂
  refine ⟨s₁₂, _,
    .seq hex₁ (.seq hex₂ (.seq hex₃ (.seq hex₄ (.seq hex₅ (.seq hex₆
      (.seq hex₇ (.seq hex₈ (.seq hex₉ (.seq hex₁₀ (.seq hex₁₁ hex₁₂)))))))))),
    by omega,
    hdst₁₂,
    by rw [hreg₁₂ r_base (by omega)]; exact hr0_10,
    by rw [hreg₁₂ (r_base + 1) (by omega)]; exact hr1_10,
    by rw [hreg₁₂ (r_base + 2) (by omega)]; exact hr2_10,
    fun a hab had => by
      rw [harr₁₂ a had]
      simp only [s₁₁, State.writeArr_arrs_ne _ _ _ hab]
      rw [harr₁₀ a hab]
      simp [s₉, s₈, s₇, s₆, s₅, s₄, s₃, s₂, s₁, show (a : Arr) ≠ a_buf from hab],
    fun r hr => by
      rw [hreg₁₂ r (by omega)]
      simp only [s₁₁, State.writeArr_regs]
      rw [hreg₁₀ r hr]
      simp [s₉, s₈, s₇, s₆, s₅, s₄, s₃, s₂, s₁,
        State.setReg_regs_ne _ _ (by omega : (r : Reg) ≠ r_base + 4),
        State.setReg_regs_ne _ _ (by omega : (r : Reg) ≠ r_base + 5),
        State.setReg_regs_ne _ _ (by omega : (r : Reg) ≠ r_base + 2),
        State.setReg_regs_ne _ _ (by omega : (r : Reg) ≠ r_base + 1),
        State.setReg_regs_ne _ _ (by omega : (r : Reg) ≠ r_base + 3),
        State.setReg_regs_ne _ _ (by omega : (r : Reg) ≠ r_base)]⟩


end GraphMinor.Compute
