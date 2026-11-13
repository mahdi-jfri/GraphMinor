module

public import GraphMinor.Compute.CrossingLoopCand

/-!
# Five-Vertex Trial Search (`docs/crossing/crossing_extractor.tex`, Section 10)

This file formalizes the trial search over the candidate edges of the first five low-degree
vertices in one iteration of the contraction loop (Section 10, steps 3–5 of
`docs/crossing/crossing_extractor.tex`). The search stops at the first trial that does not answer
`NO`.
* `isCycleList_of_isHistory`: any valid history with `ContractionsLong` preserves `HP25.IsCycleList`.
* `AcceptedTrialAt`: state predicate packaging an accepted trial (`r_state = 1` for `YES`, or
  `r_state = 2` for `WITNESS`) produced by `P_tr`.
* `tryCandLoopProg` and `tryFiveProg`: runs the trial program `P_tr` over all candidates for the
  first five low-degree vertices while the outcome register `r_state` is `0` (`NO`). By
  `sec102_proved` and Lemma 4 (`not_isCrossed_of_planar_of_no_distinctBridges`), at least one trial
  cannot return `0`, so `tryFiveProg` finishes with `AcceptedTrialAt` (`r_state ∈ {1, 2}`).
-/

@[expose] public section

namespace GraphMinor.Compute.Crossing

open SimpleGraph GraphMinor.Crossing

/-- If `IsHistory I recs I'` holds from a valid starting instance `(K, S, D)` with
`ContractionsLong recs`, then the final instance `(H, S', D')` also has `HP25.IsCycleList H D'`. -/
theorem isCycleList_of_isHistory {N : ℕ}
    {I I' : SimpleGraph (Fin N) × Set (Fin N) × List (Fin N)}
    {recs : List (CrossRecord (Fin N))}
    (hD : HP25.IsCycleList I.1 I.2.2) (hcl : ContractionsLong recs) (hH : IsHistory I recs I') :
    HP25.IsCycleList I'.1 I'.2.2 := by
  induction recs generalizing I with
  | nil =>
    subst hH
    exact hD
  | cons rec rs ih =>
    rcases rec with r | r | ⟨G', S'⟩
    · obtain ⟨hG, _, hval, hrs⟩ := hH
      have hD_r : HP25.IsCycleList r.graph I.2.2 := hG.symm ▸ hD
      exact ih (isCycleList_newGraph hD_r hval)
        (fun r' hr' => hcl r' (List.mem_cons_of_mem _ hr')) hrs
    · obtain ⟨_, _, _, ⟨_, hD_r, htr_r⟩, hrs⟩ := hH
      exact ih (isCycleList_contractGraph hD_r htr_r (fun hu => hcl r List.mem_cons_self hu))
        (fun r' hr' => hcl r' (List.mem_cons_of_mem _ hr')) hrs
    · obtain ⟨_, _, _, _, hce, hrs⟩ := hH
      have hD_new : HP25.IsCycleList G' I.2.2 :=
        ⟨hD.1, hD.2.1, fun p hp => hce p.1 p.2 ⟨p, hp, Or.inl rfl⟩⟩
      exact ih hD_new (fun r' hr' => hcl r' (List.mem_cons_of_mem _ hr')) hrs

/-- State predicate holding when an accepted trial (`r_state = 1` for `YES`, or `r_state = 2` for
`WITNESS`) has been produced in `(b, a_trec, r_trec, a_Q, a_R)` from `(K, S, D)` at some vertex
`u ∈ S` of degree at most `64`. -/
def AcceptedTrialAt {N : ℕ} (b : InstArrs) (a_trec r_trec r_state a_Q a_R C_tr : ℕ)
    (K : SimpleGraph (Fin N)) (S : Finset (Fin N)) (D : List (Fin N)) (s : State) : Prop :=
  ∃ (u : Fin N) (H : SimpleGraph (Fin N)) (S' : Finset (Fin N))
    (recs_t : List (CrossRecord (Fin N))) (k_t : ℕ),
    u ∈ S ∧ (K.neighborSet u).ncard ≤ 64 ∧
    IsInstanceAt b H S' (contractCycle D u) s ∧
    HP25.IsCycleList H (contractCycle D u) ∧
    IsHistoryFin K S D recs_t H S' (contractCycle D u) ∧
    ContractionsLong recs_t ∧
    IsRecBufAt a_trec r_trec recs_t k_t s ∧
    IsClean H (S' : Set (Fin N)) (contractCycle D u) ∧
    S' ⊆ S.erase u ∧
    (s.arrs a_trec).length ≤ 65 * C_tr * instSize N K ∧
    H.edgeSet.ncard ≤ K.edgeSet.ncard + 192 ∧
    ((s.regs r_state = 2 ∧ IsCrossingPairAt H (contractCycle D u) a_Q a_R s) ∨
      (s.regs r_state = 1 ∧ IsEmpty (HP25.PlaneEmbedding H (S' : Set (Fin N))) ∧
        HP25.IsCrossed H (contractCycle D u)))

theorem AcceptedTrialAt.of_eq {N : ℕ} {b : InstArrs} {a_trec r_trec r_state a_Q a_R C_tr : ℕ}
    {K : SimpleGraph (Fin N)} {S : Finset (Fin N)} {D : List (Fin N)} {s s' : State}
    (h : AcceptedTrialAt b a_trec r_trec r_state a_Q a_R C_tr K S D s)
    (ha : ∀ x ∈ b.list ++ [a_trec, a_Q, a_R], s'.arrs x = s.arrs x)
    (hrt : s'.regs r_trec = s.regs r_trec)
    (hrs : s'.regs r_state = s.regs r_state) :
    AcceptedTrialAt b a_trec r_trec r_state a_Q a_R C_tr K S D s' := by
  obtain ⟨u, H, S', recs_t, k_t, huS, hdeg, hinst_b, hcyc_H, hhist, hcl, hbuf, hclean, hsub,
    hlen_trec, hedge, hout⟩ := h
  have hinst_b' : IsInstanceAt b H S' (contractCycle D u) s' :=
    hinst_b.of_arrs_eq (fun x hx => ha x (List.mem_append_left _ hx))
  have htrec_eq : s'.arrs a_trec = s.arrs a_trec := ha a_trec (by simp)
  have hQ_eq : s'.arrs a_Q = s.arrs a_Q := ha a_Q (by simp)
  have hR_eq : s'.arrs a_R = s.arrs a_R := ha a_R (by simp)
  have hbuf' : IsRecBufAt a_trec r_trec recs_t k_t s' := by
    obtain ⟨ls, hls, he, hr⟩ := hbuf
    exact ⟨ls, hls, htrec_eq.trans he, hrt.trans hr⟩
  refine ⟨u, H, S', recs_t, k_t, huS, hdeg, hinst_b', hcyc_H, hhist, hcl, hbuf', hclean, hsub,
    htrec_eq.symm ▸ hlen_trec, hedge, ?_⟩
  rcases hout with ⟨hs2, L₁, L₂, hpair, hQ, hR⟩ | ⟨hs1, hemp, hcross⟩
  · exact Or.inl ⟨hrs.trans hs2, L₁, L₂, hpair, hQ_eq.trans hQ, hR_eq.trans hR⟩
  · exact Or.inr ⟨hrs.trans hs1, hemp, hcross⟩

theorem AcceptedTrialAt.state_pos {N : ℕ} {b : InstArrs} {a_trec r_trec r_state a_Q a_R C_tr : ℕ}
    {K : SimpleGraph (Fin N)} {S : Finset (Fin N)} {D : List (Fin N)} {s : State}
    (h : AcceptedTrialAt b a_trec r_trec r_state a_Q a_R C_tr K S D s) :
    s.regs r_state = 1 ∨ s.regs r_state = 2 := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hout⟩ := h
  rcases hout with ⟨h2, _⟩ | ⟨h1, _⟩
  · exact Or.inr h2
  · exact Or.inl h1

/-- Loop over the candidates in `(a_cv, r_ncand)` for the vertex `u` in `r_u`: while `r_state = 0`,
load `R_tr := r_u` and `R_tr + 1 := a_cv[r_idx]`, run `P_tr`, and copy `R_tr` into `r_state`. -/
def tryCandLoopProg (a_cv r_state r_u r_ncand r_idx R_tr : ℕ) (P_tr : Cmd) : Cmd :=
  forRangeProg r_idx (.reg r_ncand)
    (.ite (.op .eq (.reg r_state) (.const 0))
      (.seq (.assign R_tr (.reg r_u))
        (.seq (.assign (R_tr + 1) (.read a_cv (.reg r_idx)))
          (.seq P_tr
            (.assign r_state (.reg R_tr)))))
      .skip)

/-- Execution of `tryCandLoopProg` for a fixed vertex `u ∈ S` of degree at most `64`. -/
theorem tryCandLoopProg_exec {w N : ℕ} (a b : InstArrs) (a_trec a_Q a_R a_cv : ℕ)
    (r_trec r_state r_u r_ncand r_idx A_tr R_tr : ℕ)
    (P_tr : Cmd) (C_tr c_tr : ℕ)
    (hP_tr : ∀ (K : SimpleGraph (Fin N)) (S : Finset (Fin N)) (D : List (Fin N))
      (u v : Fin N) (s : State),
      wordSize c_tr ((N + 1) * instSize N K) ≤ w → IsInstanceAt a K S D s →
      HP25.IsCycleList K D → IsClean K (S : Set (Fin N)) D → IsTrialEdge K D u v →
      (u ∈ D → 4 < D.length) → s.regs R_tr = u.val → s.regs (R_tr + 1) = v.val →
      ∃ s' t, Exec w P_tr s s' t ∧ t ≤ C_tr * ((K.neighborSet u).ncard + 1) * instSize N K ∧
        KeepsBelow R_tr A_tr [r_trec] (b.list ++ [a_trec, a_Q, a_R]) s s' ∧
        ∃ (H : SimpleGraph (Fin N)) (S' : Finset (Fin N)) (recs : List (CrossRecord (Fin N)))
          (k' : ℕ),
          IsInstanceAt b H S' (contractCycle D u) s' ∧
          IsHistoryFin K S D recs H S' (contractCycle D u) ∧ ContractionsLong recs ∧
          IsRecBufAt a_trec r_trec recs k' s' ∧ IsClean H (S' : Set (Fin N)) (contractCycle D u) ∧
          S' ⊆ S.erase u ∧
          (HP25.IsCrossed (contractGraph K u v) (contractCycle D u) ↔
            HP25.IsCrossed H (contractCycle D u)) ∧
          (s'.arrs a_trec).length ≤ C_tr * ((K.neighborSet u).ncard + 1) * instSize N K ∧
          H.edgeSet.ncard ≤ K.edgeSet.ncard + 3 * (K.neighborSet u).ncard ∧
          ((s'.regs R_tr = 2 ∧ IsCrossingPairAt H (contractCycle D u) a_Q a_R s') ∨
            (s'.regs R_tr = 0 ∧ Nonempty (HP25.PlaneEmbedding H (S' : Set (Fin N))) ∧
              ∀ L₁ L₂, IsCrossingPair H (contractCycle D u) L₁ L₂ →
                ¬ InDistinctBridges H (contractCycle D u) L₁ L₂) ∨
            (s'.regs R_tr = 1 ∧ IsEmpty (HP25.PlaneEmbedding H (S' : Set (Fin N))) ∧
              ∀ L₁ L₂, IsCrossingPair H (contractCycle D u) L₁ L₂ →
                ¬ InDistinctBridges H (contractCycle D u) L₁ L₂)))
    {K : SimpleGraph (Fin N)} {S : Finset (Fin N)} {D : List (Fin N)}
    {lists : Fin N → List ℕ} {u : Fin N} {k_cv : ℕ} {s : State}
    (hw_tr : wordSize c_tr ((N + 1) * instSize N K) ≤ w)
    (hw : 4 * instSize N K + 70 < 2 ^ w)
    (hinst : IsInstanceAt a K S D s)
    (hadj : IsAdjList K a.st a.en a.ent lists s)
    (hD : HP25.IsCycleList K D)
    (hclean : IsClean K (S : Set (Fin N)) D)
    (huS : u ∈ S)
    (hdeg : (K.neighborSet u).ncard ≤ 64)
    (hu : s.regs r_u = u.val)
    (hbuf_cv : IsBuf a_cv r_ncand (candVals D lists u) k_cv s)
    (hstate0 : s.regs r_state = 0 ∨ AcceptedTrialAt b a_trec r_trec r_state a_Q a_R C_tr K S D s)
    (ha_Sub : ∀ x ∈ a.list, x < A_tr ∧ x ∉ b.list ++ [a_trec, a_Q, a_R])
    (hcv_Sub : a_cv < A_tr ∧ a_cv ∉ b.list ++ [a_trec, a_Q, a_R])
    (hregs_lt : r_trec < R_tr ∧ r_state < R_tr ∧ r_u < R_tr ∧ r_ncand < R_tr ∧ r_idx < R_tr)
    (hregs_nd : [r_trec, r_state, r_u, r_ncand, r_idx].Nodup) :
    ∃ s' t, Exec w (tryCandLoopProg a_cv r_state r_u r_ncand r_idx R_tr P_tr) s s' t ∧
      t ≤ 65 * (65 * C_tr + 20) * instSize N K ∧
      KeepsBelow R_tr A_tr [r_trec, r_state, r_idx] (b.list ++ [a_trec, a_Q, a_R]) s s' ∧
      ((s'.regs r_state = 0 ∧ ∀ v : Fin N, IsTrialEdge K D u v → (u ∈ D → 4 < D.length) →
          ¬ HP25.IsCrossed (contractGraph K u v) (contractCycle D u)) ∨
        AcceptedTrialAt b a_trec r_trec r_state a_Q a_R C_tr K S D s') := by
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or,
    not_false_eq_true, List.nodup_nil, and_true, ← ne_eq] at hregs_nd
  obtain ⟨⟨hrt_st, hrt_u, hrt_nc, hrt_idx⟩,
    ⟨hst_u, hst_nc, hst_idx⟩,
    ⟨hu_nc, hu_idx⟩, hnc_idx⟩ := hregs_nd
  obtain ⟨hrt_lt, hst_lt, hu_lt, hnc_lt, hidx_lt⟩ := hregs_lt
  set vs := candVals D lists u
  have hvs_len : vs.length ≤ 64 := length_candVals_le hadj.2 hdeg
  have hsz_pos : 1 ≤ instSize N K := by unfold instSize; omega
  have hN_le : N ≤ instSize N K := by unfold instSize; omega
  have hw0 : 0 < 2 ^ w := by omega
  have hw1 : 1 < 2 ^ w := by omega
  have hvs_w : vs.length < 2 ^ w := by omega
  have hB_ge : 12 * instSize N K ≤ (65 * C_tr + 12) * instSize N K :=
    Nat.mul_le_mul_right _ (by omega)
  let I' : ℕ → State → Prop := fun j st =>
    KeepsBelow R_tr A_tr [r_trec, r_state, r_idx] (b.list ++ [a_trec, a_Q, a_R]) s st ∧
    ((st.regs r_state = 0 ∧ ∀ (i : ℕ) (hi : i < vs.length), i < j → ∀ hv : vs[i]'hi < N,
        ¬ HP25.IsCrossed (contractGraph K u ⟨vs[i]'hi, hv⟩) (contractCycle D u)) ∨
      AcceptedTrialAt b a_trec r_trec r_state a_Q a_R C_tr K S D st)
  have hI0 : I' 0 s := by
    refine ⟨⟨fun _ _ _ => rfl, fun _ _ _ => rfl⟩, ?_⟩
    rcases hstate0 with hs0 | hacc
    · exact Or.inl ⟨hs0, fun i _ hi => absurd hi (Nat.not_lt_zero i)⟩
    · exact Or.inr hacc
  obtain ⟨s', t', hex', ht', hI_end, _⟩ :=
    forRangeProg_exec (w := w) r_idx (.reg r_ncand)
      (.ite (.op .eq (.reg r_state) (.const 0))
        (.seq (.assign R_tr (.reg r_u))
          (.seq (.assign (R_tr + 1) (.read a_cv (.reg r_idx)))
            (.seq P_tr
              (.assign r_state (.reg R_tr)))))
        .skip)
      vs.length ((65 * C_tr + 12) * instSize N K) I' hvs_w
      (fun j hj st v ⟨hk, hst_or⟩ => by
        refine ⟨⟨fun r hr hnr => ?_, hk.2⟩, ?_⟩
        · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hnr
          rw [State.setReg_regs_ne _ _ hnr.2.2]
          exact hk.1 r hr (by simp [hnr])
        · rcases hst_or with ⟨hs0, hno⟩ | hacc
          · exact Or.inl ⟨by simp [State.setReg_regs_ne _ _ hst_idx, hs0], hno⟩
          · exact Or.inr (hacc.of_eq (fun _ _ => rfl)
              (State.setReg_regs_ne _ _ hrt_idx) (State.setReg_regs_ne _ _ hst_idx)))
      (fun j hj st ⟨hk, _⟩ _ => by
        have hrnc : st.regs r_ncand = vs.length := by
          rw [hk.1 r_ncand hnc_lt (by simp [hrt_nc.symm, hst_nc.symm, hnc_idx])]
          exact hbuf_cv.2
        exact eval_reg hrnc hvs_w)
      (fun st ⟨hk, _⟩ _ => by
        have hrnc : st.regs r_ncand = vs.length := by
          rw [hk.1 r_ncand hnc_lt (by simp [hrt_nc.symm, hst_nc.symm, hnc_idx])]
          exact hbuf_cv.2
        exact eval_reg hrnc hvs_w)
      (fun j hj st ⟨hk, hst_or⟩ hridx => by
        have hru_st : st.regs r_u = u.val := by
          rw [hk.1 r_u hu_lt (by simp [hrt_u.symm, hst_u.symm, hu_idx])]
          exact hu
        have hcv_st : st.arrs a_cv = vs ++ List.replicate k_cv 0 := by
          rw [hk.2 a_cv hcv_Sub.1 hcv_Sub.2]
          exact hbuf_cv.1
        rcases hst_or with ⟨hs0, hno⟩ | hacc
        · -- `st.regs r_state = 0`: execute the trial on `vs[j]`
          have heq_eval : (Expr.op .eq (.reg r_state) (.const 0)).eval w st = some 1 :=
            eval_eq (eval_reg hs0 hw0) (eval_const hw0) hw1
          obtain ⟨hv_lt, htrial_v, hlong_v⟩ :=
            (mem_candVals_iff hD hadj.2 (vs[j]'hj)).mp (List.getElem_mem hj)
          let v : Fin N := ⟨vs[j]'hj, hv_lt⟩
          have hvw : v.val < 2 ^ w := by omega
          have huw : u.val < 2 ^ w := by omega
          set st₁ := st.setReg R_tr u.val
          have hex₁ : Exec w (.assign R_tr (.reg r_u)) st st₁ 2 :=
            .assign (eval_reg hru_st huw)
          have hcv_j : (st₁.arrs a_cv)[j]'(by rw [State.setReg_arrs, hcv_st]; simp; omega) = v.val := by
            simp only [st₁, State.setReg_arrs, hcv_st, List.getElem_append_left hj, v]
          have hread_v : (Expr.read a_cv (.reg r_idx)).eval w st₁ = some v.val := by
            rw [← hcv_j]
            exact eval_read (w := w) (eval_reg (w := w) (by
                simp only [st₁, State.setReg_regs_ne _ _ (show r_idx ≠ R_tr by omega), hridx])
              (by omega)) (by rw [State.setReg_arrs, hcv_st]; simp; omega)
              (by rw [hcv_j]; exact hvw)
          set st₂ := st₁.setReg (R_tr + 1) v.val
          have hex₂ : Exec w (.assign (R_tr + 1) (.read a_cv (.reg r_idx))) st₁ st₂ 3 :=
            .assign hread_v
          have hinst_st₂ : IsInstanceAt a K S D st₂ :=
            hinst.of_arrs_eq (fun x hxa => hk.2 x (ha_Sub x hxa).1 (ha_Sub x hxa).2)
          obtain ⟨st₃, t₃, hex₃, ht₃, hk₃, H, S', recs_t, k_t, hinst_b₃, hhist₃, hcl₃,
            hbuf₃, hclean₃, hsub₃, hcross_iff, hlen_trec₃, hedge₃, hout₃⟩ :=
            hP_tr K S D u v st₂ hw_tr hinst_st₂ hD hclean htrial_v hlong_v
              (by simp [st₂, st₁]) (by simp [st₂])
          have hcyc_H : HP25.IsCycleList H (contractCycle D u) :=
            isCycleList_of_isHistory hD hcl₃ hhist₃
          have ht₃_bound : t₃ ≤ 65 * C_tr * instSize N K := by
            calc t₃ ≤ C_tr * ((K.neighborSet u).ncard + 1) * instSize N K := ht₃
              _ ≤ C_tr * 65 * instSize N K :=
                  Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ (by omega))
              _ = 65 * C_tr * instSize N K := by ring
          have hlen_trec₃' : (st₃.arrs a_trec).length ≤ 65 * C_tr * instSize N K := by
            calc (st₃.arrs a_trec).length
              _ ≤ C_tr * ((K.neighborSet u).ncard + 1) * instSize N K := hlen_trec₃
              _ ≤ C_tr * 65 * instSize N K :=
                  Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ (by omega))
              _ = 65 * C_tr * instSize N K := by ring
          have hedge₃' : H.edgeSet.ncard ≤ K.edgeSet.ncard + 192 := by omega
          have hR_tr_val : st₃.regs R_tr < 2 ^ w := by
            rcases hout₃ with ⟨h2, _⟩ | ⟨h0, _⟩ | ⟨h1, _⟩ <;> omega
          set st₄ := st₃.setReg r_state (st₃.regs R_tr)
          have hex₄ : Exec w (.assign r_state (.reg R_tr)) st₃ st₄ 2 :=
            .assign (eval_reg rfl hR_tr_val)
          have hbuf₄ : IsRecBufAt a_trec r_trec recs_t k_t st₄ := by
            obtain ⟨ls, hls, he, hr⟩ := hbuf₃
            exact ⟨ls, hls, he, (State.setReg_regs_ne _ _ hrt_st).trans hr⟩
          have hk_st₄ : KeepsBelow R_tr A_tr [r_trec, r_state, r_idx]
              (b.list ++ [a_trec, a_Q, a_R]) s st₄ := by
            refine ⟨fun r hr hnr => ?_, fun x hx hnx => ?_⟩
            · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hnr
              rw [State.setReg_regs_ne _ _ hnr.2.1, hk₃.1 r hr (by simp [hnr.1])]
              simp only [st₂, st₁, State.setReg_regs_ne _ _ (show r ≠ R_tr + 1 by omega),
                State.setReg_regs_ne _ _ (show r ≠ R_tr by omega), hk.1 r hr (by simp [hnr])]
            · rw [State.setReg_arrs, hk₃.2 x hx hnx]
              exact hk.2 x hx hnx
          have hridx₄ : st₄.regs r_idx = j := by
            rw [State.setReg_regs_ne _ _ hst_idx.symm, hk₃.1 r_idx hidx_lt (by simp [hrt_idx.symm])]
            simp only [st₂, st₁, State.setReg_regs_ne _ _ (show r_idx ≠ R_tr + 1 by omega),
              State.setReg_regs_ne _ _ (show r_idx ≠ R_tr by omega), hridx]
          refine ⟨st₄, 3 + (2 + (3 + (t₃ + 2))),
            .ite_true heq_eval (show 1 ≠ 0 by decide) (.seq hex₁ (.seq hex₂ (.seq hex₃ hex₄))),
            by rw [Nat.add_mul]; omega, ⟨hk_st₄, ?_⟩, hridx₄⟩
          rcases hout₃ with ⟨h2, hpair⟩ | ⟨h0, hplan, hno_br⟩ | ⟨h1, hemp, _⟩
          · -- WITNESS (`R_tr = 2`)
            right
            exact ⟨u, H, S', recs_t, k_t, huS, hdeg, hinst_b₃, hcyc_H, hhist₃, hcl₃,
              hbuf₄, hclean₃, hsub₃, hlen_trec₃', hedge₃', Or.inl ⟨by simp [st₄, h2], hpair⟩⟩
          · -- NO (`R_tr = 0`)
            left
            refine ⟨by simp [st₄, h0], fun i hi hij hv_i => ?_⟩
            rcases Nat.lt_succ_iff_lt_or_eq.mp hij with hij_lt | rfl
            · exact hno i hi hij_lt hv_i
            · have hnc_H : ¬ HP25.IsCrossed H (contractCycle D u) :=
                not_isCrossed_of_planar_of_no_distinctBridges hplan hinst_b₃.1 hcyc_H hno_br
              exact fun hcr => hnc_H (hcross_iff.mp hcr)
          · -- YES (`R_tr = 1`)
            right
            have hnp_H : ¬ Nonempty (HP25.PlaneEmbedding H (S' : Set (Fin N))) :=
              fun ⟨φ⟩ => hemp.false φ
            have hcross_H : HP25.IsCrossed H (contractCycle D u) :=
              isCrossed_of_clean_of_not_planar (Finset.finite_toSet S') hinst_b₃.1 hcyc_H
                hclean₃ hnp_H
            exact ⟨u, H, S', recs_t, k_t, huS, hdeg, hinst_b₃, hcyc_H, hhist₃, hcl₃,
              hbuf₄, hclean₃, hsub₃, hlen_trec₃', hedge₃', Or.inr ⟨by simp [st₄, h1], hemp, hcross_H⟩⟩
        · -- `AcceptedTrialAt` already holds (`st.regs r_state ∈ {1, 2}`): skip
          have hpos_st := hacc.state_pos
          have hne0 : st.regs r_state ≠ 0 := by rcases hpos_st with h | h <;> omega
          have hst_w : st.regs r_state < 2 ^ w := by rcases hpos_st with h | h <;> omega
          have heq_eval : (Expr.op .eq (.reg r_state) (.const 0)).eval w st = some 0 := by
            have := eval_eq (eval_reg rfl hst_w) (eval_const hw0) hw1
            simpa [hne0] using this
          refine ⟨st, 3 + 1, .ite_false heq_eval (.skip _), by omega,
            ⟨hk, Or.inr hacc⟩, hridx⟩)
      hI0
  obtain ⟨hk_end, h_or_end⟩ := hI_end
  refine ⟨s', t', hex', ?_, hk_end, ?_⟩
  · simp only [Expr.cost] at ht'
    calc t'
      _ ≤ (vs.length + 1) * (1 + (65 * C_tr + 12) * instSize N K + 6) := ht'
      _ ≤ 65 * ((65 * C_tr + 20) * instSize N K) :=
          Nat.mul_le_mul (by omega) (by
            have : (65 * C_tr + 20) * instSize N K =
                (65 * C_tr + 12) * instSize N K + 8 * instSize N K := by ring
            omega)
      _ = 65 * (65 * C_tr + 20) * instSize N K := (Nat.mul_assoc _ _ _).symm
  · rcases h_or_end with ⟨hs0, hno⟩ | hacc
    · left
      refine ⟨hs0, fun v htrial hlong => ?_⟩
      have hv_mem : v.val ∈ vs := (mem_candVals_iff hD hadj.2 v.val).mpr ⟨v.2, htrial, hlong⟩
      obtain ⟨i, hi, hget⟩ := List.getElem_of_mem hv_mem
      have hv_eq : (⟨vs[i]'hi, hget ▸ v.2⟩ : Fin N) = v := Fin.ext hget
      exact hv_eq ▸ hno i hi hi (hget ▸ v.2)
    · exact Or.inr hacc

/-- Search over the first five low-degree vertices for an accepted trial:
1. Run `emitLowDegProg` to populate `a_low` with active vertices of degree at most `64`.
2. Set `r_state := 0`.
3. Loop `r_j` from `0` to `4`: if `r_state = 0`, read `r_u := a_low[r_j]`, build candidates in
   `a_cv` via `buildCandProg`, and run `tryCandLoopProg`. -/
def tryFiveProg (a : InstArrs) (a_low a_cv : ℕ)
    (r_state r_low_cnt r_j r_u r_ncand r_idx r_onD r_pos r_clen r_k r_hi r_y R_tr : ℕ)
    (P_tr : Cmd) : Cmd :=
  .seq (emitLowDegProg a a_low r_low_cnt r_clen r_k r_hi)
    (.seq (.assign r_state (.const 0))
      (forRangeProg r_j (.const 5)
        (.ite (.op .eq (.reg r_state) (.const 0))
          (.seq (.assign r_u (.read a_low (.reg r_j)))
            (.seq (buildCandProg a a_cv r_u r_ncand r_onD r_pos r_clen r_k r_hi r_y)
              (tryCandLoopProg a_cv r_state r_u r_ncand r_idx R_tr P_tr)))
          .skip)))

/-- Execution of `tryFiveProg`: when `(K, S, D)` is clean, nonplanar, crossed, and has
`|E(K)| ≤ 16 |S|`, `tryFiveProg` always terminates with `AcceptedTrialAt` (`r_state ∈ {1, 2}`). -/
theorem tryFiveProg_exec {w N : ℕ} (a b : InstArrs) (a_trec a_Q a_R a_low a_cv : ℕ)
    (r_trec r_state r_low_cnt r_j r_u r_ncand r_idx r_onD r_pos r_clen r_k r_hi r_y A_tr R_tr : ℕ)
    (P_tr : Cmd) (C_tr c_tr : ℕ)
    (hP_tr : ∀ (K : SimpleGraph (Fin N)) (S : Finset (Fin N)) (D : List (Fin N))
      (u v : Fin N) (s : State),
      wordSize c_tr ((N + 1) * instSize N K) ≤ w → IsInstanceAt a K S D s →
      HP25.IsCycleList K D → IsClean K (S : Set (Fin N)) D → IsTrialEdge K D u v →
      (u ∈ D → 4 < D.length) → s.regs R_tr = u.val → s.regs (R_tr + 1) = v.val →
      ∃ s' t, Exec w P_tr s s' t ∧ t ≤ C_tr * ((K.neighborSet u).ncard + 1) * instSize N K ∧
        KeepsBelow R_tr A_tr [r_trec] (b.list ++ [a_trec, a_Q, a_R]) s s' ∧
        ∃ (H : SimpleGraph (Fin N)) (S' : Finset (Fin N)) (recs : List (CrossRecord (Fin N)))
          (k' : ℕ),
          IsInstanceAt b H S' (contractCycle D u) s' ∧
          IsHistoryFin K S D recs H S' (contractCycle D u) ∧ ContractionsLong recs ∧
          IsRecBufAt a_trec r_trec recs k' s' ∧ IsClean H (S' : Set (Fin N)) (contractCycle D u) ∧
          S' ⊆ S.erase u ∧
          (HP25.IsCrossed (contractGraph K u v) (contractCycle D u) ↔
            HP25.IsCrossed H (contractCycle D u)) ∧
          (s'.arrs a_trec).length ≤ C_tr * ((K.neighborSet u).ncard + 1) * instSize N K ∧
          H.edgeSet.ncard ≤ K.edgeSet.ncard + 3 * (K.neighborSet u).ncard ∧
          ((s'.regs R_tr = 2 ∧ IsCrossingPairAt H (contractCycle D u) a_Q a_R s') ∨
            (s'.regs R_tr = 0 ∧ Nonempty (HP25.PlaneEmbedding H (S' : Set (Fin N))) ∧
              ∀ L₁ L₂, IsCrossingPair H (contractCycle D u) L₁ L₂ →
                ¬ InDistinctBridges H (contractCycle D u) L₁ L₂) ∨
            (s'.regs R_tr = 1 ∧ IsEmpty (HP25.PlaneEmbedding H (S' : Set (Fin N))) ∧
              ∀ L₁ L₂, IsCrossingPair H (contractCycle D u) L₁ L₂ →
                ¬ InDistinctBridges H (contractCycle D u) L₁ L₂)))
    {K : SimpleGraph (Fin N)} [DecidableRel K.Adj] {S : Finset (Fin N)} {D : List (Fin N)}
    {s : State}
    (hw_tr : wordSize c_tr ((N + 1) * instSize N K) ≤ w)
    (hw : 4 * instSize N K + 70 < 2 ^ w)
    (hinst : IsInstanceAt a K S D s)
    (hD : HP25.IsCycleList K D)
    (hclean : IsClean K (S : Set (Fin N)) D)
    (hnp : IsEmpty (HP25.PlaneEmbedding K (S : Set (Fin N))))
    (hcross : HP25.IsCrossed K D)
    (hedge : K.edgeSet.ncard ≤ 16 * S.card)
    (ha_Sub : ∀ x ∈ a.list, x < A_tr ∧ x ∉ b.list ++ [a_trec, a_Q, a_R, a_low, a_cv])
    (hlow_Sub : a_low < A_tr ∧ a_low ∉ b.list ++ [a_trec, a_Q, a_R] ∧ a_low ≠ a_cv)
    (hcv_Sub : a_cv < A_tr ∧ a_cv ∉ b.list ++ [a_trec, a_Q, a_R])
    (hregs_eq : r_trec = R_tr - 13 ∧ r_state = R_tr - 12 ∧ r_low_cnt = R_tr - 11 ∧
      r_j = R_tr - 10 ∧ r_u = R_tr - 9 ∧ r_ncand = R_tr - 8 ∧ r_idx = R_tr - 7 ∧
      r_onD = R_tr - 6 ∧ r_pos = R_tr - 5 ∧ r_clen = R_tr - 4 ∧ r_k = R_tr - 3 ∧
      r_hi = R_tr - 2 ∧ r_y = R_tr - 1 ∧ 13 ≤ R_tr) :
    ∃ s' t, Exec w (tryFiveProg a a_low a_cv r_state r_low_cnt r_j r_u r_ncand r_idx
        r_onD r_pos r_clen r_k r_hi r_y R_tr P_tr) s s' t ∧
      t ≤ (390 * (65 * C_tr + 20) + 8000) * instSize N K ∧
      KeepsBelow (R_tr - 12) A_tr [r_trec] (b.list ++ [a_trec, a_Q, a_R, a_low, a_cv]) s s' ∧
      AcceptedTrialAt b a_trec r_trec r_state a_Q a_R C_tr K S D s' := by
  rcases hregs_eq with
    ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, hR_tr_13⟩
  obtain ⟨lists, hadj⟩ := hinst.2.2.1
  have hsz_pos : 1 ≤ instSize N K := by unfold instSize; omega
  have hN_le : N + 1 ≤ instSize N K := by unfold instSize; omega
  have hw0 : 0 < 2 ^ w := by omega
  have hw1 : 1 < 2 ^ w := by omega
  have hB5_ge : 1250 * instSize N K ≤ (65 * (65 * C_tr + 20) + 1250) * instSize N K :=
    Nat.mul_le_mul_right _ (by omega)
  have ha_low : ∀ x ∈ a.list, x ≠ a_low := fun x hx => by
    have := (ha_Sub x hx).2
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false, not_or] at this
    exact this.2.2.2.2.1
  have ha_cv : ∀ x ∈ a.list, x ≠ a_cv := fun x hx => by
    have := (ha_Sub x hx).2
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false, not_or] at this
    exact this.2.2.2.2.2
  have ha_Sub' : ∀ x ∈ a.list, x < A_tr ∧ x ∉ b.list ++ [a_trec, a_Q, a_R] := fun x hx => by
    obtain ⟨h1, h2⟩ := ha_Sub x hx
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false, not_or] at h2 ⊢
    exact ⟨h1, h2.1, h2.2.1, h2.2.2.1, h2.2.2.2.1⟩
  -- Phase 1: emitLowDegProg
  obtain ⟨s₁, t₁, hex₁, ht₁, hbuf_low, harr₁, hreg₁⟩ :=
    emitLowDegProg_exec (w := w) a a_low (R_tr - 11) (R_tr - 4) (R_tr - 3) (R_tr - 2) hinst ha_low
      (by
        unfold Reg
        simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, List.nodup_nil]
        exact ⟨by omega, by omega, by omega, not_false, trivial⟩)
      (by omega)
  set s₂ := s₁.setReg (R_tr - 12) 0
  have hex₂ : Exec w (.assign (R_tr - 12) (.const 0)) s₁ s₂ 2 := .assign (eval_const hw0)
  set L_low := lowDegUpTo K S N
  obtain ⟨hlen5, U, hU_card, hU_sub, hU_deg, hU_mem⟩ :=
    five_le_length_lowDegUpTo hinst.1 hnp hedge
  -- Phase 2: forRangeProg (R_tr - 10) (.const 5)
  let I : ℕ → State → Prop := fun m st =>
    KeepsBelow (R_tr - 10) A_tr [R_tr - 13, R_tr - 12, R_tr - 11]
      (b.list ++ [a_trec, a_Q, a_R, a_low, a_cv]) s st ∧
    st.arrs a_low = L_low ++ List.replicate (N - L_low.length) 0 ∧
    ((st.regs (R_tr - 12) = 0 ∧ ∀ (j : ℕ), j < m → ∀ (hj : j < L_low.length) (hu : L_low[j]'hj < N),
        ∀ v : Fin N, IsTrialEdge K D ⟨L_low[j]'hj, hu⟩ v → (⟨L_low[j]'hj, hu⟩ ∈ D → 4 < D.length) →
          ¬ HP25.IsCrossed (contractGraph K ⟨L_low[j]'hj, hu⟩ v)
              (contractCycle D ⟨L_low[j]'hj, hu⟩)) ∨
      AcceptedTrialAt b a_trec (R_tr - 13) (R_tr - 12) a_Q a_R C_tr K S D st)
  have hI0 : I 0 s₂ := by
    refine ⟨⟨fun r hr hnr => ?_, fun x hx hnx => ?_⟩, hbuf_low.1,
      Or.inl ⟨by simp [s₂], fun j hj => absurd hj (Nat.not_lt_zero j)⟩⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hnr
      simp only [s₂, State.setReg_regs_ne _ _ hnr.2.1]
      exact hreg₁ r (fun h => by
        unfold Reg at h
        simp only [List.mem_cons, List.not_mem_nil, or_false] at h
        omega)
    · simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false, not_or] at hnx
      exact harr₁ x hnx.2.2.2.2.1
  obtain ⟨s₃, t₃, hex₃, ht₃, hI5, _⟩ :=
    forRangeProg_exec (w := w) (R_tr - 10) (.const 5)
      (.ite (.op .eq (.reg (R_tr - 12)) (.const 0))
        (.seq (.assign (R_tr - 9) (.read a_low (.reg (R_tr - 10))))
          (.seq (buildCandProg a a_cv (R_tr - 9) (R_tr - 8) (R_tr - 6) (R_tr - 5)
              (R_tr - 4) (R_tr - 3) (R_tr - 2) (R_tr - 1))
            (tryCandLoopProg a_cv (R_tr - 12) (R_tr - 9) (R_tr - 8) (R_tr - 7) R_tr P_tr)))
        .skip)
      5 ((65 * (65 * C_tr + 20) + 1250) * instSize N K) I (by omega)
      (fun j hj st v ⟨hk, hlow_st, hst_or⟩ => by
        refine ⟨⟨fun r hr hnr => ?_, hk.2⟩, hlow_st, ?_⟩
        · rw [State.setReg_regs_ne _ _ (show r ≠ R_tr - 10 by omega)]
          exact hk.1 r hr hnr
        · rcases hst_or with ⟨hs0, hno⟩ | hacc
          · exact Or.inl ⟨by simp only [State.setReg_regs_ne _ _ (show R_tr - 12 ≠ R_tr - 10 by omega), hs0], hno⟩
          · exact Or.inr (hacc.of_eq (fun _ _ => rfl)
              (State.setReg_regs_ne _ _ (show R_tr - 13 ≠ R_tr - 10 by omega))
              (State.setReg_regs_ne _ _ (show R_tr - 12 ≠ R_tr - 10 by omega))))
      (fun _ _ _ _ _ => eval_const (by omega))
      (fun _ _ _ => eval_const (by omega))
      (fun j hj st ⟨hk, hlow_st, hst_or⟩ hrj => by
        rcases hst_or with ⟨hs0, hno⟩ | hacc
        · -- `st.regs (R_tr - 12) = 0`: test vertex `L_low[j]`
          have heq_eval : (Expr.op .eq (.reg (R_tr - 12)) (.const 0)).eval w st = some 1 :=
            eval_eq (eval_reg hs0 hw0) (eval_const hw0) hw1
          have hj_low : j < L_low.length := show j < (lowDegUpTo K S N).length by omega
          obtain ⟨hu_lt, huS, hudeg⟩ := mem_lowDegUpTo_iff.mp (List.getElem_mem hj_low)
          let u : Fin N := ⟨L_low[j]'hj_low, hu_lt⟩
          have huw : u.val < 2 ^ w := by omega
          have hlow_j : (st.arrs a_low)[j]'(by rw [hlow_st]; simp; omega) = u.val := by
            simp only [hlow_st, List.getElem_append_left hj_low, u]
          have hread_u : (Expr.read a_low (.reg (R_tr - 10))).eval w st = some u.val := by
            rw [← hlow_j]
            exact eval_read (w := w) (eval_reg (w := w) hrj (by omega))
              (by rw [hlow_st]; simp; omega) (by rw [hlow_j]; exact huw)
          set st₁ := st.setReg (R_tr - 9) u.val
          have hex_u : Exec w (.assign (R_tr - 9) (.read a_low (.reg (R_tr - 10)))) st st₁ 3 :=
            .assign hread_u
          have hinst_st₁ : IsInstanceAt a K S D st₁ :=
            hinst.of_arrs_eq (fun x hxa => hk.2 x (ha_Sub x hxa).1 (ha_Sub x hxa).2)
          have hadj_st₁ : IsAdjList K a.st a.en a.ent lists st₁ :=
            hadj.of_arrs_eq
              (hk.2 a.st (ha_Sub a.st (by simp [InstArrs.list])).1
                (ha_Sub a.st (by simp [InstArrs.list])).2)
              (hk.2 a.en (ha_Sub a.en (by simp [InstArrs.list])).1
                (ha_Sub a.en (by simp [InstArrs.list])).2)
              (hk.2 a.ent (ha_Sub a.ent (by simp [InstArrs.list])).1
                (ha_Sub a.ent (by simp [InstArrs.list])).2)
          obtain ⟨st₂, t_bc, hex_bc, ht_bc, hbuf_cv, harr_bc, hreg_bc⟩ :=
            buildCandProg_exec (w := w) (u := u) a a_cv (R_tr - 9) (R_tr - 8) (R_tr - 6) (R_tr - 5)
              (R_tr - 4) (R_tr - 3) (R_tr - 2) (R_tr - 1)
              hinst_st₁ hadj_st₁ hD (by simp [st₁]) hudeg ha_cv
              (by
                unfold Reg
                simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, List.nodup_nil]
                exact ⟨by omega, by omega, by omega, by omega, by omega, by omega, by omega, not_false, trivial⟩)
              hw
          have hinst_st₂ : IsInstanceAt a K S D st₂ :=
            hinst_st₁.of_arrs_eq (fun x hxa => harr_bc x (ha_cv x hxa))
          have hadj_st₂ : IsAdjList K a.st a.en a.ent lists st₂ :=
            hadj_st₁.of_arrs_eq
              (harr_bc a.st (ha_cv a.st (by simp [InstArrs.list])))
              (harr_bc a.en (ha_cv a.en (by simp [InstArrs.list])))
              (harr_bc a.ent (ha_cv a.ent (by simp [InstArrs.list])))
          have hru_st₂ : st₂.regs (R_tr - 9) = u.val := by
            rw [hreg_bc (R_tr - 9) (fun h => by
              unfold Reg at h
              simp only [List.mem_cons, List.not_mem_nil, or_false] at h
              omega)]
            simp [st₁]
          have hs0_st₂ : st₂.regs (R_tr - 12) = 0 := by
            rw [hreg_bc (R_tr - 12) (fun h => by
              unfold Reg at h
              simp only [List.mem_cons, List.not_mem_nil, or_false] at h
              omega)]
            simp only [st₁, State.setReg_regs_ne _ _ (show R_tr - 12 ≠ R_tr - 9 by omega), hs0]
          obtain ⟨st₃, t_tc, hex_tc, ht_tc, hk_tc, h_or_tc⟩ :=
            tryCandLoopProg_exec (w := w) (u := u) a b a_trec a_Q a_R a_cv (R_tr - 13) (R_tr - 12)
              (R_tr - 9) (R_tr - 8) (R_tr - 7)
              A_tr R_tr P_tr C_tr c_tr hP_tr hw_tr hw hinst_st₂ hadj_st₂ hD hclean huS hudeg
              hru_st₂ hbuf_cv (Or.inl hs0_st₂) ha_Sub' hcv_Sub
              (by omega)
              (by
                simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, List.nodup_nil]
                exact ⟨by omega, by omega, by omega, by omega, not_false, trivial⟩)
          have hk_st₃ : KeepsBelow (R_tr - 10) A_tr [R_tr - 13, R_tr - 12, R_tr - 11]
              (b.list ++ [a_trec, a_Q, a_R, a_low, a_cv]) s st₃ := by
            refine ⟨fun r hr hnr => ?_, fun x hx hnx => ?_⟩
            · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hnr
              rw [hk_tc.1 r (by omega) (fun h => by
                  simp only [List.mem_cons, List.not_mem_nil, or_false] at h
                  omega),
                hreg_bc r (fun h => by
                  unfold Reg at h
                  simp only [List.mem_cons, List.not_mem_nil, or_false] at h
                  omega)]
              simp only [st₁, State.setReg_regs_ne _ _ (show r ≠ R_tr - 9 by omega), hk.1 r hr (by simp [hnr])]
            · simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false, not_or] at hnx
              rw [hk_tc.2 x hx (by simp [hnx.1, hnx.2.1, hnx.2.2.1, hnx.2.2.2.1]),
                harr_bc x hnx.2.2.2.2.2]
              exact hk.2 x hx (by simp [hnx])
          have hlow_st₃ : st₃.arrs a_low = L_low ++ List.replicate (N - L_low.length) 0 := by
            rw [hk_tc.2 a_low hlow_Sub.1 hlow_Sub.2.1, harr_bc a_low hlow_Sub.2.2]
            exact hlow_st
          have hrj_st₃ : st₃.regs (R_tr - 10) = j := by
            rw [hk_tc.1 (R_tr - 10) (by omega) (fun h => by
                simp only [List.mem_cons, List.not_mem_nil, or_false] at h
                omega),
              hreg_bc (R_tr - 10) (fun h => by
                unfold Reg at h
                simp only [List.mem_cons, List.not_mem_nil, or_false] at h
                omega)]
            simp only [st₁, State.setReg_regs_ne _ _ (show R_tr - 10 ≠ R_tr - 9 by omega), hrj]
          have ht_step : 3 + (3 + (t_bc + t_tc)) ≤
              (65 * (65 * C_tr + 20) + 1250) * instSize N K := by
            have hbc_sz : t_bc ≤ 1225 * instSize N K := by omega
            calc 3 + (3 + (t_bc + t_tc))
              _ ≤ 6 * instSize N K + 1225 * instSize N K +
                  65 * (65 * C_tr + 20) * instSize N K := by omega
              _ ≤ (65 * (65 * C_tr + 20) + 1250) * instSize N K := by ring_nf; omega
          refine ⟨st₃, 3 + (3 + (t_bc + t_tc)),
            .ite_true heq_eval (show 1 ≠ 0 by decide) (.seq hex_u (.seq hex_bc hex_tc)),
            ht_step, ⟨hk_st₃, hlow_st₃, ?_⟩, hrj_st₃⟩
          rcases h_or_tc with ⟨hs0_tc, hno_u⟩ | hacc_tc
          · left
            refine ⟨hs0_tc, fun i hi hij hu_i v htr_v hlong_v => ?_⟩
            rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi_lt | rfl
            · exact hno i hi_lt hij hu_i v htr_v hlong_v
            · exact hno_u v htr_v hlong_v
          · exact Or.inr hacc_tc
        · -- `AcceptedTrialAt` already holds: skip
          have hpos_st := hacc.state_pos
          have hne0 : st.regs (R_tr - 12) ≠ 0 := by rcases hpos_st with h | h <;> omega
          have hst_w : st.regs (R_tr - 12) < 2 ^ w := by rcases hpos_st with h | h <;> omega
          have heq_eval : (Expr.op .eq (.reg (R_tr - 12)) (.const 0)).eval w st = some 0 := by
            have := eval_eq (eval_reg rfl hst_w) (eval_const hw0) hw1
            simpa [hne0] using this
          refine ⟨st, 3 + 1, .ite_false heq_eval (.skip _), by omega,
            ⟨hk, hlow_st, Or.inr hacc⟩, hrj⟩)
      hI0
  obtain ⟨hk5, _, h_or5⟩ := hI5
  -- Show that `s₃.regs (R_tr - 12) = 0` is impossible at `m = 5` by `sec102_proved`:
  have hacc_final : AcceptedTrialAt b a_trec (R_tr - 13) (R_tr - 12) a_Q a_R C_tr K S D s₃ := by
    rcases h_or5 with ⟨_, hno5⟩ | hacc
    · exfalso
      obtain ⟨u, huU, v, htrial_uv, hne4, hcross_uv⟩ :=
        sec102_proved K (S : Set (Fin N)) D U (Finset.finite_toSet S) hinst.1 hD hclean
          hcross hU_card hU_sub
      have hlong_uv : u ∈ D → 4 < D.length :=
        fun huD => four_lt_length_of_isCrossed_of_ne_four hcross (hne4 huD)
      obtain ⟨j, hj5, hget_j⟩ := hU_mem u huU
      obtain ⟨hj_len, hget_eq⟩ := List.getElem?_eq_some_iff.mp hget_j
      have hu_eq : (⟨L_low[j]'hj_len, hget_eq ▸ u.2⟩ : Fin N) = u := Fin.ext hget_eq
      exact hno5 j hj5 hj_len (hget_eq ▸ u.2) v (hu_eq.symm ▸ htrial_uv)
        (hu_eq.symm ▸ hlong_uv) (hu_eq.symm ▸ hcross_uv)
    · exact hacc
  refine ⟨s₃, t₁ + (2 + t₃), .seq hex₁ (.seq hex₂ hex₃), ?_, ?_, hacc_final⟩
  · simp only [Expr.cost] at ht₃
    calc t₁ + (2 + t₃)
      _ ≤ 30 * (N + 1) + 2 * instSize N K +
          6 * (1 + ((65 * (65 * C_tr + 20) + 1250) * instSize N K + 6)) := by omega
      _ ≤ (390 * (65 * C_tr + 20) + 8000) * instSize N K := by ring_nf; omega
  · refine ⟨fun r hr hnr => ?_, hk5.2⟩
    exact hk5.1 r (by omega)
      (by simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hnr ⊢; omega)

end GraphMinor.Compute.Crossing
