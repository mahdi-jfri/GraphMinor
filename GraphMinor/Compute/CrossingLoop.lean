module

import GraphMinor.Compute.CrossingOpsSparsify

public import GraphMinor.Compute.CrossingLoopStep
public import GraphMinor.Crossing.Sparse72

/-!
# The Contraction Loop of the Crossing Extractor (Section 10)

Section 10 of `docs/crossing/crossing_extractor.tex` repeats one iteration while the current
instance is clean, nonplanar and crossed, that is, while `Classify` answers `YES`. One iteration
has seven steps:
1. sparsify as in Section 7.2, so that $M \le 16N$;
2. choose five distinct vertices of degree at most $64$;
3. for each chosen vertex $u$, try every edge $uv$ at $u$ if $u \notin D$, and the two cycle edges
   at $u$ if $u \in D$, except that cycle edges are not contracted when $|D| = 4$;
4. for each trial, copy the current instance, contract $uv$, restore cleanliness as in Section 9
   with the markers $N_K(u) \setminus \{v\}$, and call `Classify` on the restored instance;
5. on `NO`, discard the trial;
6. on `WITNESS`, lift the crossing through the trial and all earlier accepted operations, and
   return it;
7. on `YES`, accept the trial and begin the next iteration.

The program takes the first five vertices of degree at most $64$ in the order of their numbers,
and it keeps the records of the accepted operations in a buffer. At `WITNESS` it stops the loop,
with the records of this trial appended, and the lift of Section 11 is done afterwards.

This file implements `loopProg` and proves:
* `loopRecProgClaim_of_full (hSp : SparsifyRecProgClaim) (hTr : TrialRecFullProgClaim) : LoopRecProgClaim`
* `loopRecProgClaim_of (hSp : SparsifyRecProgClaim) (hRs : RestoreRecNeProgClaim) (hCl : ClassifyProgClaim) : LoopRecProgClaim`
-/

@[expose] public section

namespace GraphMinor.Compute.Crossing

open Classical SimpleGraph GraphMinor.Crossing

/-! ### Appending a trial record buffer into the main record buffer -/

/-- Copy the active prefix of length `r_trec` from `a_trec` into `a_rec` starting at offset
`r_rec`, then advance `r_rec` by `r_trec`. Uses scratch loop counter `r_i`. -/
def appendRecBufProg (a_trec a_rec r_trec r_rec r_i : ℕ) : Cmd :=
  .seq
    (forRangeProg r_i (.reg r_trec)
      (.write a_rec (.op .add (.reg r_rec) (.reg r_i)) (.read a_trec (.reg r_i))))
    (.assign r_rec (.op .add (.reg r_rec) (.reg r_trec)))

/-- Execution of `appendRecBufProg`: appends `recs_t` from `(a_trec, r_trec)` into `(a_rec, r_rec)`
without reallocating `a_rec`. -/
theorem appendRecBufProg_exec {w N : ℕ} (a_trec a_rec r_trec r_rec r_i : ℕ)
    (htrec_ne : a_trec ≠ a_rec)
    (hregs : [r_trec, r_rec, r_i].Nodup)
    {recs recs_t : List (CrossRecord (Fin N))} {k k_t : ℕ} {s : State}
    (hbuf : IsRecBufAt a_rec r_rec recs k s)
    (hbuf_t : IsRecBufAt a_trec r_trec recs_t k_t s)
    (hcap : (s.arrs a_trec).length ≤ k)
    (hw : (s.arrs a_rec).length + N + 2 < 2 ^ w) :
    ∃ (s' : State) (t k' : ℕ),
      Exec w (appendRecBufProg a_trec a_rec r_trec r_rec r_i) s s' t ∧
      t ≤ 14 * (s.arrs a_trec).length + 19 ∧
      IsRecBufAt a_rec r_rec (recs ++ recs_t) k' s' ∧
      (s'.arrs a_rec).length = (s.arrs a_rec).length ∧
      k ≤ k' + (s.arrs a_trec).length ∧
      (∀ x, x ≠ a_rec → s'.arrs x = s.arrs x) ∧
      (∀ r, r ≠ r_rec → r ≠ r_i → s'.regs r = s.regs r) := by
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or,
    List.nodup_nil, and_true, not_false_eq_true] at hregs
  obtain ⟨⟨htr_rec, htr_i⟩, hrec_i⟩ := hregs
  obtain ⟨ls, hF, harr_rec, hreg_rec⟩ := hbuf
  obtain ⟨ls_t, hF_t, harr_trec, hreg_trec⟩ := hbuf_t
  set A := ls.flatten
  set L := ls_t.flatten
  set n := L.length
  have hlen_L : ls_t.flatten.length = n := rfl
  have hlen_rec : (s.arrs a_rec).length = A.length + k := by
    rw [harr_rec, List.length_append, List.length_replicate]
  have hlen_trec : (s.arrs a_trec).length = n + k_t := by
    rw [harr_trec, List.length_append, List.length_replicate]
  have hn_le_k : n ≤ k := by omega
  have hw1 : 1 < 2 ^ w := by omega
  have hn_w : n < 2 ^ w := by omega
  have hL_bound : ∀ y ∈ L, y < 2 ^ w := by
    intro y hy
    have hle := le_of_forall₂ hF_t y hy
    omega
  let I : ℕ → State → Prop := fun j st =>
    (∀ r, r ≠ r_i → st.regs r = s.regs r) ∧
    (∀ x, x ≠ a_rec → st.arrs x = s.arrs x) ∧
    st.arrs a_rec = A ++ L.take j ++ List.replicate (k - j) 0
  have hI0 : I 0 s := ⟨fun _ _ => rfl, fun _ _ => rfl, by simp [harr_rec, A]⟩
  obtain ⟨s₁, t₁, hex₁, ht₁, hIn, _⟩ :=
    forRangeProg_exec (w := w) r_i (.reg r_trec)
      (.write a_rec (.op .add (.reg r_rec) (.reg r_i)) (.read a_trec (.reg r_i)))
      n 6 I hn_w
      (fun j _ st v ⟨hreg, harr, hrec_st⟩ =>
        ⟨fun r hr => (State.setReg_regs_ne _ _ hr).trans (hreg r hr), harr, hrec_st⟩)
      (fun j _ st ⟨hreg, _, _⟩ _ =>
        eval_reg (w := w) (by rw [hreg r_trec htr_i]; exact hreg_trec) hn_w)
      (fun st ⟨hreg, _, _⟩ _ =>
        eval_reg (w := w) (by rw [hreg r_trec htr_i]; exact hreg_trec) hn_w)
      (fun j hj st ⟨hreg, harr, hrec_st⟩ hri => by
        have htrec_st : st.arrs a_trec = L ++ List.replicate k_t 0 := by
          rw [harr a_trec htrec_ne, harr_trec]
        have hj_trec : j < (st.arrs a_trec).length := by rw [htrec_st]; simp; omega
        have hval_j : (st.arrs a_trec)[j]'hj_trec = L[j]'hj := by
          simp [htrec_st, List.getElem_append_left hj]
        have hLw : L[j]'hj < 2 ^ w := hL_bound _ (List.getElem_mem hj)
        have hpos : (Expr.op .add (.reg r_rec) (.reg r_i)).eval w st = some (A.length + j) :=
          eval_add (eval_reg (w := w) (by rw [hreg r_rec hrec_i]; exact hreg_rec) (by omega))
            (eval_reg (w := w) hri (by omega)) (by omega)
        have hrd : (Expr.read a_trec (.reg r_i)).eval w st = some (L[j]'hj) := by
          rw [← hval_j]
          exact eval_read (w := w) (eval_reg (w := w) hri (by omega)) hj_trec
            (by rw [hval_j]; exact hLw)
        have hj_rec : A.length + j < (st.arrs a_rec).length := by
          rw [hrec_st]; simp; omega
        refine ⟨st.writeArr a_rec (A.length + j) (L[j]'hj), 6,
          .write hpos hrd hj_rec, le_rfl, ⟨hreg, fun x hx => ?_, ?_⟩, hri⟩
        · rw [State.writeArr_arrs_ne _ _ _ hx]
          exact harr x hx
        · rw [State.writeArr_arrs_self, hrec_st]
          have hkj : k - j = (k - (j + 1)) + 1 := by omega
          rw [hkj, List.replicate_succ,
            set_after (by rw [List.length_append, List.length_take_of_le (show j ≤ L.length by omega)]),
            List.take_succ_eq_append_getElem hj]
          simp only [List.append_assoc, List.singleton_append])
      hI0
  obtain ⟨hreg₁, harr₁, hrec₁⟩ := hIn
  rw [List.take_of_length_le le_rfl] at hrec₁
  have hadd_end : (Expr.op .add (.reg r_rec) (.reg r_trec)).eval w s₁ = some (A.length + n) :=
    eval_add (eval_reg (w := w) (by rw [hreg₁ r_rec hrec_i]; exact hreg_rec) (by omega))
      (eval_reg (w := w) (by rw [hreg₁ r_trec htr_i]; exact hreg_trec) hn_w) (by omega)
  set s₂ := s₁.setReg r_rec (A.length + n)
  have hex₂ : Exec w (.assign r_rec (.op .add (.reg r_rec) (.reg r_trec))) s₁ s₂ 4 :=
    .assign hadd_end
  refine ⟨s₂, t₁ + 4, k - n, .seq hex₁ hex₂, ?_, ?_, ?_, by omega, ?_, ?_⟩
  · simp only [Expr.cost] at ht₁
    omega
  · refine ⟨ls ++ ls_t, List.rel_append hF hF_t, ?_, ?_⟩
    · simp only [s₂, State.setReg_arrs, hrec₁, List.flatten_append, A, L]
    · simp only [s₂, State.setReg_regs_self, List.flatten_append, List.length_append, A, L, n]
  · simp only [s₂, State.setReg_arrs, hrec₁, List.length_append, List.length_replicate, hlen_rec]
    omega
  · intro x hx
    exact harr₁ x hx
  · intro r h1 h2
    simp only [s₂, State.setReg_regs_ne _ _ h1]
    exact hreg₁ r h2

/-! ### Sparsification step wrapper -/

/-- Every clean cycle instance has at least `1` active vertex in `S`. -/
theorem card_pos_of_isCycleList {N : ℕ} {K : SimpleGraph (Fin N)} {S : Finset (Fin N)}
    {D : List (Fin N)} (hsupp : HP25.IsSupportedOn K (S : Set (Fin N)))
    (hD : HP25.IsCycleList K D) : 1 ≤ S.card := by
  have hne : D ≠ [] := by
    rintro rfl
    have := hD.1
    simp at this
  have hd : D.head hne ∈ (S : Set (Fin N)) :=
    isCycleList_mem_supported hsupp hD _ (List.head_mem hne)
  exact Finset.card_pos.mpr ⟨D.head hne, hd⟩

/-- Valid history and cycle properties for the deletion record emitted by sparsification. -/
theorem isHistoryFin_and_cycle_sparsifyGraph {N : ℕ} {K : SimpleGraph (Fin N)}
    {S : Finset (Fin N)} {D : List (Fin N)}
    {Fs : List (SimpleGraph (Option (Fin N)))} {E₀ : Set (Sym2 (Fin N))}
    (hsupp : HP25.IsSupportedOn K (S : Set (Fin N))) (hD : HP25.IsCycleList K D) :
    let K₁ := sparsifyGraph K D Fs E₀
    HP25.IsCycleList K₁ D ∧
      IsHistoryFin K S D [CrossRecord.del K₁ (S : Set (Fin N))] K₁ S D ∧
      ContractionsLong [CrossRecord.del K₁ (S : Set (Fin N))] := by
  intro K₁
  have hle : K₁ ≤ K := fun _ _ h => h.1
  have hsupp₁ : HP25.IsSupportedOn K₁ (S : Set (Fin N)) := fun _ _ h => hsupp h.1
  have hDS : ∀ d ∈ D, d ∈ (S : Set (Fin N)) := isCycleList_mem_supported hsupp hD
  have hce : ∀ a b, IsCycleEdge D a b → K₁.Adj a b := by
    intro a b h
    have h' := h
    rcases h with ⟨p, hp, ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩⟩
    · exact ⟨hD.2.2 (a, b) hp, Or.inr (Or.inl h')⟩
    · exact ⟨(hD.2.2 (b, a) hp).symm, Or.inr (Or.inl h')⟩
  have hD₁ : HP25.IsCycleList K₁ D :=
    ⟨hD.1, hD.2.1, fun p hp => hce p.1 p.2 ⟨p, hp, Or.inl rfl⟩⟩
  refine ⟨hD₁, ⟨hle, Set.Subset.rfl, hsupp₁, hDS, hce, rfl⟩, fun r hr => ?_⟩
  simp only [List.mem_singleton] at hr
  nomatch hr

/-! ### One iteration of the contraction loop -/

/-- Scratch instance array bundle starting at `A`. -/
def loopScratchInst (A : ℕ) : InstArrs := ⟨A, A + 1, A + 2, A + 3, A + 4⟩

/-- Constant factor for one iteration of the Section 10 contraction loop. -/
def loopIterConst (C_sp C_tr C_cp : ℕ) : ℕ :=
  210 * C_sp + 17 * (390 * (65 * C_tr + 20) + 8000) + 210 * C_cp + 15470 * C_tr + 25

/-- One iteration of the Section 10 contraction loop:
1. Run `P_sp` on `(a, a_rec, r_rec)` so that the current graph has at most `16 * |S|` edges.
2. Run `tryFiveProg` on `a` into scratch instance `b = loopScratchInst A`, scratch trial buffer
   `(A + 5, R)`, status register `R + 1`, and crossing-pair arrays `(a_Q, a_R)`.
3. Copy `b` back into `a` via `P_cp`.
4. Append the trial record buffer `(A + 5, R)` into `(a_rec, r_rec)` using scratch register `R + 2`. -/
def loopIterProg (a : InstArrs) (a_rec r_rec _a_Q _a_R A R : ℕ)
    (P_sp P_tr P_cp : Cmd) : Cmd :=
  let a_trec := A + 5
  let a_low := A + 6
  let a_cv := A + 7
  .seq P_sp
    (.seq (tryFiveProg a a_low a_cv
        (R + 1) (R + 2) (R + 3) (R + 4) (R + 5) (R + 6)
        (R + 7) (R + 8) (R + 9) (R + 10) (R + 11) (R + 12) (R + 13) P_tr)
      (.seq P_cp
        (appendRecBufProg a_trec a_rec R r_rec (R + 2))))

set_option maxHeartbeats 800000 in
/-- Execution of one iteration of `loopIterProg`. Starting from a clean, nonplanar, crossed
instance `(K, S, D)` at `a`, produces a smaller instance `(K', S', D')` at `a` with `S'.card < S.card`
and `K'.edgeSet.ncard ≤ 16 * N + 192`, and sets `R + 1` to either `2` (`WITNESS`, with a crossing
pair in `a_Q, a_R`) or `1` (`YES`, where `(K', S', D')` is again clean, nonplanar, and crossed). -/
theorem loopIterProg_exec {w N : ℕ} (a : InstArrs) (a_rec r_rec a_Q a_R A R : ℕ)
    (hok : ArrsOk (a.list ++ [a_rec, a_Q, a_R]) A) (hr_rec : r_rec < R)
    {P_sp P_tr P_cp : Cmd} {C_sp c_sp C_tr c_tr C_cp c_cp : ℕ}
    (hP_sp : ∀ (w N : ℕ) (G : SimpleGraph (Fin N)) (S : Finset (Fin N))
      (D : List (Fin N)) (recs : List (CrossRecord (Fin N))) (k : ℕ) (s : State),
      wordSize c_sp (instSize N G + (s.arrs a_rec).length) ≤ w → IsInstanceAt a G S D s →
      HP25.IsCycleList G D → IsRecBufAt a_rec r_rec recs k s → C_sp * instSize N G ≤ k →
      ∃ s' t, Exec w P_sp s s' t ∧ t ≤ C_sp * instSize N G ∧
        KeepsBelow (R + 2) (A + 8) [r_rec] (a.list ++ [a_rec]) s s' ∧
        (s'.arrs a_rec).length = (s.arrs a_rec).length ∧
        ((G.edgeSet.ncard ≤ 16 * S.card ∧ IsInstanceAt a G S D s' ∧
            IsRecBufAt a_rec r_rec recs k s') ∨
          (16 * S.card < G.edgeSet.ncard ∧
            ∃ (Fs : List (SimpleGraph (Option (Fin N)))) (E₀ : Set (Sym2 (Fin N))) (k' : ℕ),
              IsSparsifyData G (S : Set (Fin N)) D Fs E₀ ∧
              IsInstanceAt a (sparsifyGraph G D Fs E₀) S D s' ∧
              IsRecBufAt a_rec r_rec (recs ++ [CrossRecord.del (sparsifyGraph G D Fs E₀) S]) k'
                s' ∧ k ≤ k' + C_sp * instSize N G)))
    (hP_tr : ∀ (K : SimpleGraph (Fin N)) (S : Finset (Fin N)) (D : List (Fin N))
      (u v : Fin N) (s : State),
      wordSize c_tr ((N + 1) * instSize N K) ≤ w → IsInstanceAt a K S D s →
      HP25.IsCycleList K D → IsClean K (S : Set (Fin N)) D → IsTrialEdge K D u v →
      (u ∈ D → 4 < D.length) → s.regs (R + 13) = u.val → s.regs (R + 13 + 1) = v.val →
      ∃ s' t, Exec w P_tr s s' t ∧ t ≤ C_tr * ((K.neighborSet u).ncard + 1) * instSize N K ∧
        KeepsBelow (R + 13) (A + 8) [R] ((loopScratchInst A).list ++ [A + 5, a_Q, a_R]) s s' ∧
        ∃ (H : SimpleGraph (Fin N)) (S' : Finset (Fin N)) (recs : List (CrossRecord (Fin N)))
          (k' : ℕ),
          IsInstanceAt (loopScratchInst A) H S' (contractCycle D u) s' ∧
          IsHistoryFin K S D recs H S' (contractCycle D u) ∧ ContractionsLong recs ∧
          IsRecBufAt (A + 5) R recs k' s' ∧ IsClean H (S' : Set (Fin N)) (contractCycle D u) ∧
          S' ⊆ S.erase u ∧
          (HP25.IsCrossed (contractGraph K u v) (contractCycle D u) ↔
            HP25.IsCrossed H (contractCycle D u)) ∧
          (s'.arrs (A + 5)).length ≤ C_tr * ((K.neighborSet u).ncard + 1) * instSize N K ∧
          H.edgeSet.ncard ≤ K.edgeSet.ncard + 3 * (K.neighborSet u).ncard ∧
          ((s'.regs (R + 13) = 2 ∧ IsCrossingPairAt H (contractCycle D u) a_Q a_R s') ∨
            (s'.regs (R + 13) = 0 ∧ Nonempty (HP25.PlaneEmbedding H (S' : Set (Fin N))) ∧
              ∀ L₁ L₂, IsCrossingPair H (contractCycle D u) L₁ L₂ →
                ¬ InDistinctBridges H (contractCycle D u) L₁ L₂) ∨
            (s'.regs (R + 13) = 1 ∧ IsEmpty (HP25.PlaneEmbedding H (S' : Set (Fin N))) ∧
              ∀ L₁ L₂, IsCrossingPair H (contractCycle D u) L₁ L₂ →
                ¬ InDistinctBridges H (contractCycle D u) L₁ L₂)))
    (hP_cp : ∀ (w N : ℕ) (G : SimpleGraph (Fin N)) (S : Finset (Fin N))
      (D : List (Fin N)) (s : State),
      wordSize c_cp (instSize N G) ≤ w → IsInstanceAt (loopScratchInst A) G S D s →
      HP25.IsCycleList G D →
      ∃ s' t, Exec w P_cp s s' t ∧ t ≤ C_cp * instSize N G ∧
        KeepsBelow (R + 2) (A + 8) [] a.list s s' ∧ IsInstanceAt a G S D s')
    {K : SimpleGraph (Fin N)} {S : Finset (Fin N)} {D : List (Fin N)}
    {recs : List (CrossRecord (Fin N))} {k Z : ℕ} {s : State}
    (hZ_pos : N + 1 ≤ Z)
    (hsz_K : instSize N K ≤ 210 * Z)
    (hw_sp : wordSize c_sp (instSize N K + (s.arrs a_rec).length) ≤ w)
    (hw_tr : ∀ K₁ : SimpleGraph (Fin N), instSize N K₁ ≤ 17 * Z →
      wordSize c_tr ((N + 1) * instSize N K₁) ≤ w ∧ 4 * instSize N K₁ + 70 < 2 ^ w)
    (hw_cp : ∀ H : SimpleGraph (Fin N), instSize N H ≤ 210 * Z →
      wordSize c_cp (instSize N H) ≤ w)
    (hw_app : (s.arrs a_rec).length + N + 2 < 2 ^ w)
    (hinst : IsInstanceAt a K S D s) (hD : HP25.IsCycleList K D)
    (hclean : IsClean K (S : Set (Fin N)) D)
    (hemp : IsEmpty (HP25.PlaneEmbedding K (S : Set (Fin N))))
    (hcrossed : HP25.IsCrossed K D)
    (hbuf : IsRecBufAt a_rec r_rec recs k s)
    (hk_cap : (210 * C_sp + 1105 * C_tr) * Z ≤ k) :
    ∃ (s' : State) (t : ℕ) (K' : SimpleGraph (Fin N)) (S' : Finset (Fin N)) (D' : List (Fin N))
      (recs_step : List (CrossRecord (Fin N))) (k' : ℕ),
      Exec w (loopIterProg a a_rec r_rec a_Q a_R A R P_sp P_tr P_cp) s s' t ∧
      t ≤ loopIterConst C_sp C_tr C_cp * Z ∧
      KeepsBelow R A [r_rec] (a.list ++ [a_rec, a_Q, a_R]) s s' ∧
      IsInstanceAt a K' S' D' s' ∧
      HP25.IsCycleList K' D' ∧
      IsClean K' (S' : Set (Fin N)) D' ∧
      IsHistoryFin K S D recs_step K' S' D' ∧
      ContractionsLong recs_step ∧
      IsRecBufAt a_rec r_rec (recs ++ recs_step) k' s' ∧
      (s'.arrs a_rec).length = (s.arrs a_rec).length ∧
      k ≤ k' + loopIterConst C_sp C_tr C_cp * Z ∧
      1 ≤ S.card ∧ S'.card < S.card ∧
      instSize N K' ≤ 210 * Z ∧
      ((s'.regs (R + 1) = 2 ∧ IsCrossingPairAt K' D' a_Q a_R s') ∨
        (s'.regs (R + 1) = 1 ∧ IsEmpty (HP25.PlaneEmbedding K' (S' : Set (Fin N))) ∧
          HP25.IsCrossed K' D')) := by
  set b := loopScratchInst A
  have ha_lt : ∀ x ∈ a.list, x < A := fun x hx =>
    hok.2 x (List.mem_append_left _ hx)
  have hrec_lt : a_rec < A := hok.2 a_rec (by simp)
  have hQ_lt : a_Q < A := hok.2 a_Q (by simp)
  have hR_lt : a_R < A := hok.2 a_R (by simp)
  have hnd_aQR := hok.1
  have hrec_not_a : a_rec ∉ a.list := by
    rw [List.nodup_append] at hnd_aQR
    exact fun hx => hnd_aQR.2.2 a_rec hx a_rec (by simp) rfl
  have hQ_not_a : a_Q ∉ a.list := by
    rw [List.nodup_append] at hnd_aQR
    exact fun hx => hnd_aQR.2.2 a_Q hx a_Q (by simp) rfl
  have hR_not_a : a_R ∉ a.list := by
    rw [List.nodup_append] at hnd_aQR
    exact fun hx => hnd_aQR.2.2 a_R hx a_R (by simp) rfl
  have hrec_not_QR : a_rec ∉ [a_Q, a_R] := by
    have htail := hnd_aQR.sublist (List.sublist_append_right _ _)
    simp only [List.nodup_cons] at htail
    exact htail.1
  have h1_S : 1 ≤ S.card := card_pos_of_isCycleList hinst.1 hD
  -- Step 1: Run `P_sp`
  have hk_sp : C_sp * instSize N K ≤ k := by
    have : C_sp * instSize N K ≤ 210 * C_sp * Z := by
      calc C_sp * instSize N K ≤ C_sp * (210 * Z) := Nat.mul_le_mul_left _ hsz_K
        _ = 210 * C_sp * Z := by ring
    have : 210 * C_sp * Z ≤ (210 * C_sp + 1105 * C_tr) * Z := by
      rw [Nat.add_mul]; omega
    omega
  obtain ⟨s₁, t₁, hex₁, ht₁, hk₁, hlen_rec₁, hsp_out⟩ :=
    hP_sp w N K S D recs k s hw_sp hinst hD hbuf hk_sp
  -- Unify the two cases of sparsification into a common post-sparsification state `(K₁, recs₁, k₁)`
  have hpost_sp : ∃ (K₁ : SimpleGraph (Fin N)) (recs₁ : List (CrossRecord (Fin N))) (k₁ : ℕ),
      K₁.edgeSet.ncard ≤ 16 * S.card ∧
      IsInstanceAt a K₁ S D s₁ ∧
      HP25.IsCycleList K₁ D ∧
      IsClean K₁ (S : Set (Fin N)) D ∧
      IsEmpty (HP25.PlaneEmbedding K₁ (S : Set (Fin N))) ∧
      HP25.IsCrossed K₁ D ∧
      IsHistoryFin K S D recs₁ K₁ S D ∧
      ContractionsLong recs₁ ∧
      IsRecBufAt a_rec r_rec (recs ++ recs₁) k₁ s₁ ∧
      k ≤ k₁ + 210 * C_sp * Z := by
    rcases hsp_out with ⟨hedge_le, hinst₁, hbuf₁⟩ | ⟨_, Fs, E₀, k₁, hsp_data, hinst₁, hbuf₁, hk₁_le⟩
    · exact ⟨K, [], k, hedge_le, hinst₁, hD, hclean, hemp, hcrossed,
        IsHistoryFin.refl K S D, ContractionsLong.nil,
        by simpa using hbuf₁, by omega⟩
    · have hS_fin : (S : Set (Fin N)).Finite := Finset.finite_toSet S
      have hcnt := sec72Count_proved K (S : Set (Fin N)) D Fs E₀ hS_fin hinst.1 hD hsp_data
      have hScard_eq : (S : Set (Fin N)).ncard = S.card := Set.ncard_coe_finset S
      have hedge_K₁ : (sparsifyGraph K D Fs E₀).edgeSet.ncard ≤ 16 * S.card := by omega
      obtain ⟨hclean₁, hnp₁, hcrossed₁⟩ :=
        sec72_proved K (S : Set (Fin N)) D Fs E₀ hS_fin hinst.1 hD hclean hsp_data
      obtain ⟨hD₁, hhist₁, hcl₁⟩ := isHistoryFin_and_cycle_sparsifyGraph hinst.1 hD (Fs := Fs) (E₀ := E₀)
      have hsp_mul : C_sp * instSize N K ≤ 210 * C_sp * Z := by
        calc C_sp * instSize N K ≤ C_sp * (210 * Z) := Nat.mul_le_mul_left _ hsz_K
          _ = 210 * C_sp * Z := by ring
      exact ⟨sparsifyGraph K D Fs E₀,
        [CrossRecord.del (sparsifyGraph K D Fs E₀) (S : Set (Fin N))], k₁,
        hedge_K₁, hinst₁, hD₁, hclean₁, not_nonempty_iff.mp hnp₁, hcrossed₁,
        hhist₁, hcl₁, hbuf₁, by omega⟩
  obtain ⟨K₁, recs₁, k₁, hedge_K₁, hinst₁, hD₁, hclean₁, hemp₁, hcrossed₁,
    hhist₁, hcl₁, hbuf₁, hk₁_le⟩ := hpost_sp
  have hS_le_N : S.card ≤ N := by
    have := Finset.card_le_univ S
    simpa using this
  have hsz_K₁ : instSize N K₁ ≤ 17 * Z := by
    unfold instSize
    omega
  -- Step 2: Run `tryFiveProg` on `(K₁, S, D)`
  have ha_Sub : ∀ x ∈ a.list, x < A + 8 ∧ x ∉ b.list ++ [A + 5, a_Q, a_R, A + 6, A + 7] := by
    intro x hxa
    have hxA : x < A := ha_lt x hxa
    have hxQ : x ≠ a_Q := fun e => hQ_not_a (e ▸ hxa)
    have hxR : x ≠ a_R := fun e => hR_not_a (e ▸ hxa)
    refine ⟨by omega, ?_⟩
    simp only [b, loopScratchInst, InstArrs.list, List.cons_append, List.nil_append,
      List.mem_cons, List.not_mem_nil, or_false, not_or]
    exact ⟨by omega, by omega, by omega, by omega, by omega, by omega,
      hxQ, hxR, by omega, by omega⟩
  have hlow_Sub : A + 6 < A + 8 ∧ A + 6 ∉ b.list ++ [A + 5, a_Q, a_R] ∧ A + 6 ≠ A + 7 := by
    refine ⟨by omega, ?_, by omega⟩
    simp only [b, loopScratchInst, InstArrs.list, List.cons_append, List.nil_append,
      List.mem_cons, List.not_mem_nil, or_false, not_or]
    exact ⟨by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega⟩
  have hcv_Sub : A + 7 < A + 8 ∧ A + 7 ∉ b.list ++ [A + 5, a_Q, a_R] := by
    refine ⟨by omega, ?_⟩
    simp only [b, loopScratchInst, InstArrs.list, List.cons_append, List.nil_append,
      List.mem_cons, List.not_mem_nil, or_false, not_or]
    exact ⟨by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega⟩
  obtain ⟨hw_tr_K₁, hw_70_K₁⟩ := hw_tr K₁ hsz_K₁
  obtain ⟨s₂, t₂, hex₂, ht₂, hk₂, hacc₂⟩ :=
    tryFiveProg_exec (w := w) a b (A + 5) a_Q a_R (A + 6) (A + 7)
      R (R + 1) (R + 2) (R + 3) (R + 4) (R + 5) (R + 6)
      (R + 7) (R + 8) (R + 9) (R + 10) (R + 11) (R + 12) (A + 8) (R + 13)
      P_tr C_tr c_tr hP_tr hw_tr_K₁ hw_70_K₁ hinst₁ hD₁ hclean₁ hemp₁ hcrossed₁ hedge_K₁
      ha_Sub hlow_Sub hcv_Sub
      ⟨by omega, by omega, by omega, by omega, by omega, by omega, by omega,
        by omega, by omega, by omega, by omega, by omega, by omega, by omega⟩
  obtain ⟨u, H, S', recs_t, k_t, huS, hdeg_u, hinst_b₂, hcyc_H, hhist_t, hcl_t,
    hbuf_t₂, hclean_H, hS'_sub, hlen_trec₂, hedge_H, hout_H⟩ := hacc₂
  have hS'_lt : S'.card < S.card := by
    have h1 : S'.card ≤ (S.erase u).card := Finset.card_le_card hS'_sub
    have h2 : (S.erase u).card < S.card := Finset.card_erase_lt_of_mem huS
    omega
  have hsz_H : instSize N H ≤ 210 * Z := by
    unfold instSize
    omega
  -- Step 3: Copy `b` back into `a` via `P_cp`
  obtain ⟨s₃, t₃, hex₃, ht₃, hk₃, hinst_a₃⟩ :=
    hP_cp w N H S' (contractCycle D u) s₂ (hw_cp H hsz_H) hinst_b₂ hcyc_H
  -- Step 4: Append `(A + 5, R)` into `(a_rec, r_rec)` via `appendRecBufProg`
  have hrec_not_five : a_rec ∉ b.list ++ [A + 5, a_Q, a_R, A + 6, A + 7] := by
    simp only [b, loopScratchInst, InstArrs.list, List.cons_append, List.nil_append,
      List.mem_cons, List.not_mem_nil, or_false, not_or]
    have hne_Q : a_rec ≠ a_Q := fun e => hrec_not_QR (by simp [e])
    have hne_R : a_rec ≠ a_R := fun e => hrec_not_QR (by simp [e])
    exact ⟨by omega, by omega, by omega, by omega, by omega, by omega,
      hne_Q, hne_R, by omega, by omega⟩
  have hbuf_rec₃ : IsRecBufAt a_rec r_rec (recs ++ recs₁) k₁ s₃ := by
    have harr_eq : s₃.arrs a_rec = s₁.arrs a_rec := by
      rw [hk₃.2 a_rec (by omega) hrec_not_a,
        hk₂.2 a_rec (by omega) hrec_not_five]
    have hreg_eq : s₃.regs r_rec = s₁.regs r_rec := by
      rw [hk₃.1 r_rec (by omega) (by simp),
        hk₂.1 r_rec (by omega) (fun h => by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at h
          omega)]
    exact hbuf₁.of_arrs_regs_eq harr_eq hreg_eq
  have htrec_not_a : A + 5 ∉ a.list := fun h => by have := ha_lt (A + 5) h; omega
  have hbuf_trec₃ : IsRecBufAt (A + 5) R recs_t k_t s₃ :=
    hbuf_t₂.of_arrs_regs_eq
      (hk₃.2 (A + 5) (by omega) htrec_not_a)
      (hk₃.1 R (by omega) (by simp))
  have hlen_trec₃ : (s₃.arrs (A + 5)).length ≤ 1105 * C_tr * Z := by
    rw [hk₃.2 (A + 5) (by omega) htrec_not_a]
    calc (s₂.arrs (A + 5)).length ≤ 65 * C_tr * instSize N K₁ := hlen_trec₂
      _ ≤ 65 * C_tr * (17 * Z) := Nat.mul_le_mul_left _ hsz_K₁
      _ = 1105 * C_tr * Z := by ring
  have hk₁_cap : (s₃.arrs (A + 5)).length ≤ k₁ := by
    have : (210 * C_sp + 1105 * C_tr) * Z = 210 * C_sp * Z + 1105 * C_tr * Z := by ring
    omega
  have hlen_rec₃ : (s₃.arrs a_rec).length = (s.arrs a_rec).length := by
    rw [hk₃.2 a_rec (by omega) hrec_not_a,
      hk₂.2 a_rec (by omega) hrec_not_five, hlen_rec₁]
  obtain ⟨s₄, t₄, k', hex₄, ht₄, hbuf₄, hlen_rec₄, hk'_le, harr₄, hreg₄⟩ :=
    appendRecBufProg_exec (w := w) (N := N) (A + 5) a_rec R r_rec (R + 2)
      (by omega)
      (by
        simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or, List.nodup_nil]
        exact ⟨⟨by omega, by omega⟩, by omega, not_false, trivial⟩)
      hbuf_rec₃ hbuf_trec₃ hk₁_cap (by rw [hlen_rec₃]; exact hw_app)
  -- Combine executions and establish all postconditions
  have hex_iter : Exec w (loopIterProg a a_rec r_rec a_Q a_R A R P_sp P_tr P_cp)
      s s₄ (t₁ + (t₂ + (t₃ + t₄))) :=
    .seq hex₁ (.seq hex₂ (.seq hex₃ hex₄))
  have hinst_a₄ : IsInstanceAt a H S' (contractCycle D u) s₄ :=
    hinst_a₃.of_arrs_eq (fun x hxa => harr₄ x (fun e => hrec_not_a (e ▸ hxa)))
  have hstate₄ : s₄.regs (R + 1) = s₂.regs (R + 1) := by
    rw [hreg₄ (R + 1) (by omega) (by omega),
      hk₃.1 (R + 1) (by omega) (by simp)]
  refine ⟨s₄, t₁ + (t₂ + (t₃ + t₄)), H, S', contractCycle D u, recs₁ ++ recs_t, k',
    hex_iter, ?_, ?_, hinst_a₄, hcyc_H, hclean_H, hhist₁.trans hhist_t,
    hcl₁.append hcl_t, by simpa [List.append_assoc] using hbuf₄,
    hlen_rec₄.trans hlen_rec₃, ?_, h1_S, hS'_lt, hsz_H, ?_⟩
  · -- Time bound
    have ht₁' : t₁ ≤ 210 * C_sp * Z := by
      calc t₁ ≤ C_sp * instSize N K := ht₁
        _ ≤ C_sp * (210 * Z) := Nat.mul_le_mul_left _ hsz_K
        _ = 210 * C_sp * Z := by ring
    have ht₂' : t₂ ≤ 17 * (390 * (65 * C_tr + 20) + 8000) * Z := by
      calc t₂ ≤ (390 * (65 * C_tr + 20) + 8000) * instSize N K₁ := ht₂
        _ ≤ (390 * (65 * C_tr + 20) + 8000) * (17 * Z) := Nat.mul_le_mul_left _ hsz_K₁
        _ = 17 * (390 * (65 * C_tr + 20) + 8000) * Z := by ring
    have ht₃' : t₃ ≤ 210 * C_cp * Z := by
      calc t₃ ≤ C_cp * instSize N H := ht₃
        _ ≤ C_cp * (210 * Z) := Nat.mul_le_mul_left _ hsz_H
        _ = 210 * C_cp * Z := by ring
    have ht₄' : t₄ ≤ 15470 * C_tr * Z + 19 * Z := by
      have : 14 * (s₃.arrs (A + 5)).length ≤ 14 * (1105 * C_tr * Z) :=
        Nat.mul_le_mul_left 14 hlen_trec₃
      have h14 : 14 * (1105 * C_tr * Z) = 15470 * C_tr * Z := by ring
      omega
    have hC_eq : loopIterConst C_sp C_tr C_cp * Z =
        210 * C_sp * Z + 17 * (390 * (65 * C_tr + 20) + 8000) * Z + 210 * C_cp * Z +
          15470 * C_tr * Z + 25 * Z := by
      unfold loopIterConst; ring
    omega
  · -- KeepsBelow R A [r_rec] (a.list ++ [a_rec, a_Q, a_R]) s s₄
    refine ⟨fun r hr hnr => ?_, fun x hx hnx => ?_⟩
    · simp only [List.mem_singleton] at hnr
      rw [hreg₄ r hnr (by omega),
        hk₃.1 r (by omega) (by simp),
        hk₂.1 r (by omega) (fun h => by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at h
          omega),
        hk₁.1 r (by omega) (by simp [hnr])]
    · simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false, not_or] at hnx
      obtain ⟨hxa, hxrec, hxQ, hxR⟩ := hnx
      rw [harr₄ x hxrec,
        hk₃.2 x (by omega) hxa,
        hk₂.2 x (by omega) (by
          simp only [b, loopScratchInst, InstArrs.list, List.cons_append, List.nil_append,
            List.mem_cons, List.not_mem_nil, or_false, not_or]
          exact ⟨by omega, by omega, by omega, by omega, by omega, by omega,
            hxQ, hxR, by omega, by omega⟩),
        hk₁.2 x (by omega) (by simp [hxa, hxrec])]
  · -- Buffer consumption bound `k ≤ k' + loopIterConst C_sp C_tr C_cp * Z`
    have hC_ge : 210 * C_sp * Z + 1105 * C_tr * Z ≤ loopIterConst C_sp C_tr C_cp * Z := by
      have : 210 * C_sp + 1105 * C_tr ≤ loopIterConst C_sp C_tr C_cp := by
        unfold loopIterConst; omega
      rw [← Nat.add_mul]
      exact Nat.mul_le_mul_right Z this
    omega
  · -- Output status in `R + 1`
    rcases hout_H with ⟨h2, L₁, L₂, hpair, harr_Q, harr_R⟩ | ⟨h0, hemp_H, hcross_H⟩
    · left
      have hQ_rec : a_Q ≠ a_rec := fun e => hrec_not_QR (by simp [e.symm])
      have hR_rec : a_R ≠ a_rec := fun e => hrec_not_QR (by simp [e.symm])
      refine ⟨hstate₄.trans h2, L₁, L₂, hpair, ?_, ?_⟩
      · rw [harr₄ a_Q hQ_rec, hk₃.2 a_Q (by omega) hQ_not_a, harr_Q]
      · rw [harr₄ a_R hR_rec, hk₃.2 a_R (by omega) hR_not_a, harr_R]
    · right
      exact ⟨hstate₄.trans h0, hemp_H, hcross_H⟩

/-! ### The `.while` loop by induction on `S.card` -/

/-- The full Section 10 contraction loop program: initialize `r_state = R + 1` to `1`, then repeat
`loopIterProg` while `r_state = 1`. -/
def loopProg (a : InstArrs) (a_rec r_rec a_Q a_R A R : ℕ)
    (P_sp P_tr P_cp : Cmd) : Cmd :=
  .seq (.assign (R + 1) (.const 1))
    (.while (.op .eq (.reg (R + 1)) (.const 1))
      (loopIterProg a a_rec r_rec a_Q a_R A R P_sp P_tr P_cp))

set_option maxHeartbeats 800000 in
/-- Induction on `n ≥ S.card` for the `.while` loop of `loopProg`. -/
theorem loopWhile_exec {w N : ℕ} (a : InstArrs) (a_rec r_rec a_Q a_R A R : ℕ)
    (hok : ArrsOk (a.list ++ [a_rec, a_Q, a_R]) A) (hr_rec : r_rec < R)
    {P_sp P_tr P_cp : Cmd} {C_sp c_sp C_tr c_tr C_cp c_cp Z len_rec : ℕ}
    (hZ_pos : N + 1 ≤ Z)
    (hw1 : 1 < 2 ^ w) (hw2 : 2 < 2 ^ w)
    (hP_sp : ∀ (w N : ℕ) (G : SimpleGraph (Fin N)) (S : Finset (Fin N))
      (D : List (Fin N)) (recs : List (CrossRecord (Fin N))) (k : ℕ) (s : State),
      wordSize c_sp (instSize N G + (s.arrs a_rec).length) ≤ w → IsInstanceAt a G S D s →
      HP25.IsCycleList G D → IsRecBufAt a_rec r_rec recs k s → C_sp * instSize N G ≤ k →
      ∃ s' t, Exec w P_sp s s' t ∧ t ≤ C_sp * instSize N G ∧
        KeepsBelow (R + 2) (A + 8) [r_rec] (a.list ++ [a_rec]) s s' ∧
        (s'.arrs a_rec).length = (s.arrs a_rec).length ∧
        ((G.edgeSet.ncard ≤ 16 * S.card ∧ IsInstanceAt a G S D s' ∧
            IsRecBufAt a_rec r_rec recs k s') ∨
          (16 * S.card < G.edgeSet.ncard ∧
            ∃ (Fs : List (SimpleGraph (Option (Fin N)))) (E₀ : Set (Sym2 (Fin N))) (k' : ℕ),
              IsSparsifyData G (S : Set (Fin N)) D Fs E₀ ∧
              IsInstanceAt a (sparsifyGraph G D Fs E₀) S D s' ∧
              IsRecBufAt a_rec r_rec (recs ++ [CrossRecord.del (sparsifyGraph G D Fs E₀) S]) k'
                s' ∧ k ≤ k' + C_sp * instSize N G)))
    (hP_tr : ∀ (K : SimpleGraph (Fin N)) (S : Finset (Fin N)) (D : List (Fin N))
      (u v : Fin N) (s : State),
      wordSize c_tr ((N + 1) * instSize N K) ≤ w → IsInstanceAt a K S D s →
      HP25.IsCycleList K D → IsClean K (S : Set (Fin N)) D → IsTrialEdge K D u v →
      (u ∈ D → 4 < D.length) → s.regs (R + 13) = u.val → s.regs (R + 13 + 1) = v.val →
      ∃ s' t, Exec w P_tr s s' t ∧ t ≤ C_tr * ((K.neighborSet u).ncard + 1) * instSize N K ∧
        KeepsBelow (R + 13) (A + 8) [R] ((loopScratchInst A).list ++ [A + 5, a_Q, a_R]) s s' ∧
        ∃ (H : SimpleGraph (Fin N)) (S' : Finset (Fin N)) (recs : List (CrossRecord (Fin N)))
          (k' : ℕ),
          IsInstanceAt (loopScratchInst A) H S' (contractCycle D u) s' ∧
          IsHistoryFin K S D recs H S' (contractCycle D u) ∧ ContractionsLong recs ∧
          IsRecBufAt (A + 5) R recs k' s' ∧ IsClean H (S' : Set (Fin N)) (contractCycle D u) ∧
          S' ⊆ S.erase u ∧
          (HP25.IsCrossed (contractGraph K u v) (contractCycle D u) ↔
            HP25.IsCrossed H (contractCycle D u)) ∧
          (s'.arrs (A + 5)).length ≤ C_tr * ((K.neighborSet u).ncard + 1) * instSize N K ∧
          H.edgeSet.ncard ≤ K.edgeSet.ncard + 3 * (K.neighborSet u).ncard ∧
          ((s'.regs (R + 13) = 2 ∧ IsCrossingPairAt H (contractCycle D u) a_Q a_R s') ∨
            (s'.regs (R + 13) = 0 ∧ Nonempty (HP25.PlaneEmbedding H (S' : Set (Fin N))) ∧
              ∀ L₁ L₂, IsCrossingPair H (contractCycle D u) L₁ L₂ →
                ¬ InDistinctBridges H (contractCycle D u) L₁ L₂) ∨
            (s'.regs (R + 13) = 1 ∧ IsEmpty (HP25.PlaneEmbedding H (S' : Set (Fin N))) ∧
              ∀ L₁ L₂, IsCrossingPair H (contractCycle D u) L₁ L₂ →
                ¬ InDistinctBridges H (contractCycle D u) L₁ L₂)))
    (hP_cp : ∀ (w N : ℕ) (G : SimpleGraph (Fin N)) (S : Finset (Fin N))
      (D : List (Fin N)) (s : State),
      wordSize c_cp (instSize N G) ≤ w → IsInstanceAt (loopScratchInst A) G S D s →
      HP25.IsCycleList G D →
      ∃ s' t, Exec w P_cp s s' t ∧ t ≤ C_cp * instSize N G ∧
        KeepsBelow (R + 2) (A + 8) [] a.list s s' ∧ IsInstanceAt a G S D s')
    (hw_sp_all : ∀ G : SimpleGraph (Fin N),
      instSize N G ≤ 210 * Z → wordSize c_sp (instSize N G + len_rec) ≤ w)
    (hw_tr : ∀ K₁ : SimpleGraph (Fin N), instSize N K₁ ≤ 17 * Z →
      wordSize c_tr ((N + 1) * instSize N K₁) ≤ w ∧ 4 * instSize N K₁ + 70 < 2 ^ w)
    (hw_cp : ∀ H : SimpleGraph (Fin N), instSize N H ≤ 210 * Z →
      wordSize c_cp (instSize N H) ≤ w)
    (hw_app : len_rec + N + 2 < 2 ^ w) :
    ∀ (n : ℕ) {K : SimpleGraph (Fin N)} {S : Finset (Fin N)} {D : List (Fin N)}
      {recs : List (CrossRecord (Fin N))} {k : ℕ} {s : State},
      S.card ≤ n →
      instSize N K ≤ 210 * Z →
      (s.arrs a_rec).length = len_rec →
      IsInstanceAt a K S D s →
      HP25.IsCycleList K D →
      IsClean K (S : Set (Fin N)) D →
      IsEmpty (HP25.PlaneEmbedding K (S : Set (Fin N))) →
      HP25.IsCrossed K D →
      IsRecBufAt a_rec r_rec recs k s →
      s.regs (R + 1) = 1 →
      (loopIterConst C_sp C_tr C_cp + 10) * S.card * Z ≤ k →
      ∃ (s' : State) (t : ℕ) (K' : SimpleGraph (Fin N)) (S' : Finset (Fin N)) (D' : List (Fin N))
        (recs_out : List (CrossRecord (Fin N))) (k' : ℕ),
        Exec w (.while (.op .eq (.reg (R + 1)) (.const 1))
          (loopIterProg a a_rec r_rec a_Q a_R A R P_sp P_tr P_cp)) s s' t ∧
        t ≤ (loopIterConst C_sp C_tr C_cp + 10) * S.card * Z + 3 ∧
        KeepsBelow R A [r_rec] (a.list ++ [a_rec, a_Q, a_R]) s s' ∧
        IsHistoryFin K S D recs_out K' S' D' ∧
        ContractionsLong recs_out ∧
        IsRecBufAt a_rec r_rec (recs ++ recs_out) k' s' ∧
        IsCrossingPairAt K' D' a_Q a_R s' ∧
        (s'.arrs a_rec).length = len_rec ∧
        k ≤ k' + (loopIterConst C_sp C_tr C_cp + 10) * S.card * Z := by
  intro n
  induction n with
  | zero =>
    intro K S D recs k s hcard _ _ hinst hD _ _ _ _ _ _
    have h1 := card_pos_of_isCycleList hinst.1 hD
    omega
  | succ n ih =>
    intro K S D recs k s hcard hsz_K hlen_s hinst hD hclean hemp hcrossed hbuf hs1 hk_cap
    have h1_S : 1 ≤ S.card := card_pos_of_isCycleList hinst.1 hD
    have hk_iter : (210 * C_sp + 1105 * C_tr) * Z ≤ k := by
      have h1 : 210 * C_sp + 1105 * C_tr ≤ loopIterConst C_sp C_tr C_cp + 10 := by
        unfold loopIterConst; omega
      have h2 : (210 * C_sp + 1105 * C_tr) * Z ≤ (loopIterConst C_sp C_tr C_cp + 10) * Z :=
        Nat.mul_le_mul_right Z h1
      have h3 : (loopIterConst C_sp C_tr C_cp + 10) * Z ≤
          (loopIterConst C_sp C_tr C_cp + 10) * S.card * Z := by
        rw [Nat.mul_assoc]
        exact Nat.mul_le_mul_left _ (Nat.le_mul_of_pos_left Z h1_S)
      omega
    have hcond_true : (Expr.op .eq (.reg (R + 1)) (.const 1)).eval w s = some 1 :=
      eval_eq (eval_reg hs1 hw1) (eval_const hw1) hw1
    obtain ⟨s₁, t₁, K₁, S₁, D₁, recs₁, k₁, hex₁, ht₁, hk₁, hinst₁, hD₁, hclean₁,
      hhist₁, hcl₁, hbuf₁, hlen₁, hk₁_le, _, hS₁_lt, hsz_K₁, hout₁⟩ :=
      loopIterProg_exec a a_rec r_rec a_Q a_R A R hok hr_rec hP_sp hP_tr hP_cp
        hZ_pos hsz_K (by rw [hlen_s]; exact hw_sp_all K hsz_K) hw_tr hw_cp
        (by rw [hlen_s]; exact hw_app) hinst hD hclean hemp hcrossed hbuf hk_iter
    have hlen_s₁ : (s₁.arrs a_rec).length = len_rec := hlen₁.trans hlen_s
    have hS₁_le_S : S₁.card + 1 ≤ S.card := hS₁_lt
    have hstep_split :
        (loopIterConst C_sp C_tr C_cp + 10) * S₁.card * Z +
          loopIterConst C_sp C_tr C_cp * Z + 10 * Z ≤
        (loopIterConst C_sp C_tr C_cp + 10) * S.card * Z := by
      have hmul :
          (loopIterConst C_sp C_tr C_cp + 10) * (S₁.card + 1) * Z ≤
          (loopIterConst C_sp C_tr C_cp + 10) * S.card * Z :=
        Nat.mul_le_mul_right Z (Nat.mul_le_mul_left _ hS₁_le_S)
      have hring :
          (loopIterConst C_sp C_tr C_cp + 10) * (S₁.card + 1) * Z =
          (loopIterConst C_sp C_tr C_cp + 10) * S₁.card * Z +
            loopIterConst C_sp C_tr C_cp * Z + 10 * Z := by ring
      omega
    rcases hout₁ with ⟨hs2, hpair₁⟩ | ⟨hs1', hemp₁, hcrossed₁⟩
    · -- Witness found (`s₁.regs (R + 1) = 2`): `.while_false` terminates
      have hcond_false : (Expr.op .eq (.reg (R + 1)) (.const 1)).eval w s₁ = some 0 := by
        have := eval_eq (eval_reg hs2 hw2) (eval_const hw1) hw1
        simpa using this
      have hex_end : Exec w (.while (.op .eq (.reg (R + 1)) (.const 1))
          (loopIterProg a a_rec r_rec a_Q a_R A R P_sp P_tr P_cp)) s₁ s₁ 3 :=
        .while_false hcond_false
      have hex_while : Exec w (.while (.op .eq (.reg (R + 1)) (.const 1))
          (loopIterProg a a_rec r_rec a_Q a_R A R P_sp P_tr P_cp)) s s₁ (3 + t₁ + 3) :=
        .while_true hcond_true (show 1 ≠ 0 by decide) hex₁ hex_end
      refine ⟨s₁, 3 + t₁ + 3, K₁, S₁, D₁, recs₁, k₁, hex_while, ?_, hk₁,
        hhist₁, hcl₁, hbuf₁, hpair₁, hlen_s₁, ?_⟩
      · omega
      · omega
    · -- Yes trial (`s₁.regs (R + 1) = 1`): recurse by induction hypothesis
      have hS₁_n : S₁.card ≤ n := by omega
      have hk₁_cap : (loopIterConst C_sp C_tr C_cp + 10) * S₁.card * Z ≤ k₁ := by omega
      obtain ⟨s', t₂, K', S', D', recs₂, k', hex₂, ht₂, hk₂, hhist₂, hcl₂,
        hbuf₂, hpair', hlen', hk'_le⟩ :=
        ih hS₁_n hsz_K₁ hlen_s₁ hinst₁ hD₁ hclean₁ hemp₁ hcrossed₁ hbuf₁ hs1' hk₁_cap
      have hex_while : Exec w (.while (.op .eq (.reg (R + 1)) (.const 1))
          (loopIterProg a a_rec r_rec a_Q a_R A R P_sp P_tr P_cp)) s s' (3 + t₁ + t₂) :=
        .while_true hcond_true (show 1 ≠ 0 by decide) hex₁ hex₂
      refine ⟨s', 3 + t₁ + t₂, K', S', D', recs₁ ++ recs₂, k', hex_while, ?_,
        hk₁.trans hk₂ (fun _ h _ => h) (fun _ h _ => h),
        hhist₁.trans hhist₂, hcl₁.append hcl₂,
        by simpa [List.append_assoc] using hbuf₂, hpair', hlen', ?_⟩
      · omega
      · omega

set_option maxHeartbeats 800000 in
/-- **The loop** (Section 10) from `SparsifyRecProgClaim` and `TrialRecFullProgClaim`. -/
theorem loopRecProgClaim_of_full :
    LoopRecProgClaim := by
  intro prog Cp cp_w hprog a a_rec r_rec a_Q a_R A R hok hrr
  set b := loopScratchInst A
  have ha_lt : ∀ x ∈ a.list, x < A := fun x hx =>
    hok.2 x (List.mem_append_left _ hx)
  have hrec_lt : a_rec < A := hok.2 a_rec (by simp)
  have hQ_lt : a_Q < A := hok.2 a_Q (by simp)
  have hR_lt : a_R < A := hok.2 a_R (by simp)
  have hnd_aQR := hok.1
  have hQ_not_a : a_Q ∉ a.list := by
    rw [List.nodup_append] at hnd_aQR
    exact fun hx => hnd_aQR.2.2 a_Q hx a_Q (by simp) rfl
  have hR_not_a : a_R ∉ a.list := by
    rw [List.nodup_append] at hnd_aQR
    exact fun hx => hnd_aQR.2.2 a_R hx a_R (by simp) rfl
  have hQR_ne : a_Q ≠ a_R := by
    have htail := hnd_aQR.sublist (List.sublist_append_right _ _)
    simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false] at htail
    exact htail.2.1
  have hok_sp : ArrsOk (a.list ++ [a_rec]) (A + 8) := by
    have hsub : List.Sublist (a.list ++ [a_rec]) (a.list ++ [a_rec, a_Q, a_R]) :=
      List.Sublist.append (List.Sublist.refl a.list) (by simp)
    exact ⟨hnd_aQR.sublist hsub, fun x hx => by have := hok.2 x (hsub.subset hx); omega⟩
  have hok_tr : ArrsOk (a.list ++ b.list ++ [A + 5, a_Q, a_R]) (A + 8) := by
    refine ⟨?_, fun x hx => ?_⟩
    · rw [List.append_assoc, List.nodup_append]
      refine ⟨hnd_aQR.sublist (List.sublist_append_left _ _), ?_, fun x hxa y hy e => ?_⟩
      · simp only [b, loopScratchInst, InstArrs.list, List.cons_append, List.nil_append,
          List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or, List.nodup_nil]
        exact ⟨⟨by omega, by omega, by omega, by omega, by omega, by omega, by omega⟩,
          ⟨by omega, by omega, by omega, by omega, by omega, by omega⟩,
          ⟨by omega, by omega, by omega, by omega, by omega⟩,
          ⟨by omega, by omega, by omega, by omega⟩,
          ⟨by omega, by omega, by omega⟩,
          ⟨by omega, by omega⟩,
          hQR_ne, not_false, trivial⟩
      · have hxA : x < A := ha_lt x hxa
        simp only [b, loopScratchInst, InstArrs.list, List.cons_append, List.nil_append,
          List.mem_cons, List.not_mem_nil, or_false] at hy
        rcases hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
        · omega
        · omega
        · omega
        · omega
        · omega
        · omega
        · exact hQ_not_a (e ▸ hxa)
        · exact hR_not_a (e ▸ hxa)
    · rw [List.append_assoc] at hx
      rcases List.mem_append.mp hx with hxa | hx_rest
      · have := ha_lt x hxa; omega
      · simp only [b, loopScratchInst, InstArrs.list, List.cons_append, List.nil_append,
          List.mem_cons, List.not_mem_nil, or_false] at hx_rest
        rcases hx_rest with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> omega
  have hok_cp : ArrsOk (b.list ++ a.list) (A + 8) := by
    refine ⟨?_, fun x hx => ?_⟩
    · rw [List.nodup_append]
      refine ⟨?_, hnd_aQR.sublist (List.sublist_append_left _ _), fun x hxb y hya e => ?_⟩
      · simp only [b, loopScratchInst, InstArrs.list, List.nodup_cons, List.mem_cons,
          List.not_mem_nil, or_false, List.nodup_nil]
        exact ⟨by omega, by omega, by omega, by omega, not_false, trivial⟩
      · have hyA : y < A := ha_lt y hya
        simp only [b, loopScratchInst, InstArrs.list, List.mem_cons, List.not_mem_nil, or_false] at hxb
        rcases hxb with rfl | rfl | rfl | rfl | rfl <;> omega
    · rcases List.mem_append.mp hx with hxb | hxa
      · simp only [b, loopScratchInst, InstArrs.list, List.mem_cons, List.not_mem_nil, or_false] at hxb
        rcases hxb with rfl | rfl | rfl | rfl | rfl <;> omega
      · have := ha_lt x hxa; omega
  obtain ⟨P_sp, C_sp, c_sp, hP_sp⟩ := sparsifyRecProgClaim_proved a a_rec r_rec (A + 8) (R + 2) hok_sp (by omega)
  obtain ⟨P_tr, C_tr, c_tr, hP_tr⟩ :=
    trialRecFullProgClaim_of prog Cp cp_w hprog a b (A + 5) R a_Q a_R (A + 8) (R + 13) hok_tr (by omega)
  obtain ⟨P_cp, C_cp, c_cp, hP_cp⟩ :=
    copyInstanceRecProgClaim_proved b a (A + 8) (R + 2) hok_cp
  set C_step := loopIterConst C_sp C_tr C_cp + 10
  set C_total := C_step + 10
  set c_total := c_sp * 213 + c_tr * 20 + c_cp * 213 + 155
  refine ⟨loopProg a a_rec r_rec a_Q a_R A R P_sp P_tr P_cp, C_total, c_total, ?_⟩
  intro w N inst K S D recs₀ k s hw hinst hD hclean hemp hcrossed hbuf hk_cap
  obtain rfl : inst = instDecidableEqFin N := Subsingleton.elim _ _
  set Z := instSize N K
  set len_rec := (s.arrs a_rec).length
  set M := (N + 1) * Z + len_rec
  have hM_def : M = (N + 1) * Z + len_rec := rfl
  have hc_def : c_total = c_sp * 213 + c_tr * 20 + c_cp * 213 + 155 := rfl
  have hZ_pos : N + 1 ≤ Z := by unfold Z instSize; omega
  have hZ_le_NZ : Z ≤ (N + 1) * Z := Nat.le_mul_of_pos_left Z (by omega)
  have hZ_le_M : Z ≤ M := by omega
  have hw150 : 150 * M < 2 ^ w := by
    apply lt_two_pow_of_le_mul (K := 150) (n := M)
    · omega
    · exact (wordSize_mono_left (by dsimp [c_total]; omega) M).trans hw
  have hw1 : 1 < 2 ^ w := by omega
  have hw2 : 2 < 2 ^ w := by omega
  have hw_app : len_rec + N + 2 < 2 ^ w := by omega
  have hw_sp_all : ∀ G : SimpleGraph (Fin N),
      instSize N G ≤ 210 * Z → wordSize c_sp (instSize N G + len_rec) ≤ w := by
    intro G hG
    have hle : instSize N G + len_rec ≤ 210 * M := by omega
    exact (wordSize_le_of_le_mul_self (K := 210) hle).trans
      ((wordSize_mono_left (by dsimp [c_total]; omega) M).trans hw)
  have hw_tr : ∀ K₁ : SimpleGraph (Fin N), instSize N K₁ ≤ 17 * Z →
      wordSize c_tr ((N + 1) * instSize N K₁) ≤ w ∧ 4 * instSize N K₁ + 70 < 2 ^ w := by
    intro K₁ hK₁
    refine ⟨?_, by omega⟩
    have hle : (N + 1) * instSize N K₁ ≤ 17 * M := by
      have h1 : (N + 1) * instSize N K₁ ≤ (N + 1) * (17 * Z) := Nat.mul_le_mul_left _ hK₁
      have h2 : (N + 1) * (17 * Z) = 17 * ((N + 1) * Z) := by ring
      omega
    exact (wordSize_le_of_le_mul_self (K := 17) hle).trans
      ((wordSize_mono_left (by dsimp [c_total]; omega) M).trans hw)
  have hw_cp : ∀ H : SimpleGraph (Fin N), instSize N H ≤ 210 * Z →
      wordSize c_cp (instSize N H) ≤ w := by
    intro H hH
    have hle : instSize N H ≤ 210 * M := by omega
    exact (wordSize_le_of_le_mul_self (K := 210) hle).trans
      ((wordSize_mono_left (by dsimp [c_total]; omega) M).trans hw)
  -- Step 1: `.assign (R + 1) (.const 1)`
  set s₀ := s.setReg (R + 1) 1
  have hex₀ : Exec w (.assign (R + 1) (.const 1)) s s₀ 2 := .assign (eval_const hw1)
  have hinst₀ : IsInstanceAt a K S D s₀ := hinst.of_arrs_eq (fun _ _ => rfl)
  have hbuf₀ : IsRecBufAt a_rec r_rec recs₀ k s₀ :=
    hbuf.of_arrs_regs_eq rfl (State.setReg_regs_ne _ _ (show r_rec ≠ R + 1 by omega))
  have hlen₀ : (s₀.arrs a_rec).length = len_rec := rfl
  have hs₀_1 : s₀.regs (R + 1) = 1 := State.setReg_regs_self _ _ _
  have hS_le_N : S.card ≤ N := by
    have := Finset.card_le_univ S
    simpa using this
  have hstep_eq : (loopIterConst C_sp C_tr C_cp + 10) * S.card * Z = C_step * S.card * Z := rfl
  have hk_while : (loopIterConst C_sp C_tr C_cp + 10) * S.card * Z ≤ k := by
    have h1 : C_step * S.card * Z ≤ C_step * (N + 1) * Z :=
      Nat.mul_le_mul_right Z (Nat.mul_le_mul_left C_step (by omega))
    have h2 : C_step * (N + 1) * Z ≤ C_total * (N + 1) * Z :=
      Nat.mul_le_mul_right Z (Nat.mul_le_mul_right (N + 1) (by dsimp [C_total]; omega))
    omega
  -- Step 2: Run `loopWhile_exec`
  obtain ⟨s', t_w, K', S', D', recs_out, k', hex_w, ht_w, hk_w, hhist, hcl,
    hbuf', hpair', hlen', hk'_le⟩ :=
    loopWhile_exec a a_rec r_rec a_Q a_R A R hok hrr hZ_pos hw1 hw2
      hP_sp (fun K' S' D' u v st => hP_tr w N K' S' D' u v st) hP_cp
      hw_sp_all hw_tr hw_cp hw_app
      S.card (s := s₀) le_rfl (by omega) hlen₀ hinst₀ hD hclean hemp hcrossed hbuf₀ hs₀_1 hk_while
  have hstep_le_total : (loopIterConst C_sp C_tr C_cp + 10) * S.card * Z + 5 ≤
      C_total * (N + 1) * Z := by
    have h1 : C_step * S.card * Z ≤ C_step * (N + 1) * Z :=
      Nat.mul_le_mul_right Z (Nat.mul_le_mul_left C_step (by omega))
    have h2 : 5 ≤ 10 * ((N + 1) * Z) := by omega
    have h3 : C_step * (N + 1) * Z + 10 * ((N + 1) * Z) = C_total * (N + 1) * Z := by
      dsimp [C_total]; ring
    omega
  refine ⟨s', 2 + t_w, .seq hex₀ hex_w, by omega, ?_, K', S', D', recs_out, k',
    hhist, hcl, hbuf', hpair', hlen', by omega⟩
  refine ⟨fun r hr hnr => ?_, fun x hx hnx => hk_w.2 x hx hnx⟩
  rw [hk_w.1 r hr hnr]
  exact State.setReg_regs_ne _ _ (show r ≠ R + 1 by omega)

/-- **The loop** (Section 10) from `SparsifyRecProgClaim`, `RestoreRecNeProgClaim`, and
`ClassifyProgClaim`. -/
theorem loopRecProgClaim_of
    : LoopRecProgClaim :=
  loopRecProgClaim_of_full

end GraphMinor.Compute.Crossing

