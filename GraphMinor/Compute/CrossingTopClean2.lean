module

import GraphMinor.Compute.CrossingOpsReplace

public import GraphMinor.Compute.CrossingTopClean1
public import GraphMinor.Compute.CrossingFlow
public import GraphMinor.Crossing.CutSec4

/-!
# Strengthened Initial Cleaning (Part 2: Phase 2 and `InitialCleaningRecFullProgClaim`)

This file completes the strengthened initial cleaning specification `InitialCleaningRecFullProgClaim`,
which adds `HP25.IsCycleList G' D` and `(HP25.IsCrossed G D ↔ HP25.IsCrossed G' D)` to
`InitialCleaningRecProgClaim`, and proves `initialCleaningRecFullProgClaim_of` from
`ReplaceRecProgClaim`.
-/

@[expose] public section

namespace GraphMinor.Compute.Crossing

open Classical SimpleGraph GraphMinor.Crossing

/-- Strengthened version of `InitialCleaningRecProgClaim` (Section 4 of
`docs/crossing/crossing_extractor.tex`):
adds `HP25.IsCycleList G' D` and `(HP25.IsCrossed G D ↔ HP25.IsCrossed G' D)` to the postconditions
of `InitialCleaningRecProgClaim`. -/
def InitialCleaningRecFullProgClaim : Prop :=
  ∀ (a : InstArrs) (a_rec r_rec a_base r_base : ℕ),
    ArrsOk (a.list ++ [a_rec]) a_base → r_rec < r_base →
    ∃ (P : Cmd) (C c : ℕ),
      ∀ (w N : ℕ) (G : SimpleGraph (Fin N)) (S : Finset (Fin N))
        (D : List (Fin N)) (recs₀ : List (CrossRecord (Fin N))) (k : ℕ) (s : State),
        wordSize c ((N + 1) * instSize N G + (s.arrs a_rec).length) ≤ w →
        IsInstanceAt a G S D s →
        HP25.IsCycleList G D →
        IsRecBufAt a_rec r_rec recs₀ k s →
        C * (N + 1) * instSize N G ≤ k →
        ∃ s' t, Exec w P s s' t ∧
          t ≤ C * (N + 1) * instSize N G ∧
          KeepsBelow r_base a_base [r_rec] (a.list ++ [a_rec]) s s' ∧
          ∃ (G' : SimpleGraph (Fin N)) (S' : Finset (Fin N))
            (recs : List (CrossRecord (Fin N))) (k' : ℕ),
            IsInstanceAt a G' S' D s' ∧
            HP25.IsCycleList G' D ∧
            IsClean G' (S' : Set (Fin N)) D ∧
            IsHistoryFin G S D recs G' S' D ∧
            ContractionsLong recs ∧
            (HP25.IsCrossed G D ↔ HP25.IsCrossed G' D) ∧
            IsRecBufAt a_rec r_rec (recs₀ ++ recs) k' s' ∧
            G'.edgeSet.ncard ≤ G.edgeSet.ncard + 3 * N ∧
            (s'.arrs a_rec).length = (s.arrs a_rec).length ∧
            k ≤ k' + C * (N + 1) * instSize N G

/-- Execution of `phase2BodyProg` at vertex `v = ⟨j, hj⟩`, tracking `AllRepl recs'`. -/
theorem phase2BodyProg_exec_full {w N : ℕ} (a : InstArrs) (a_rec r_rec a_base r_base : ℕ)
    (harrs : ArrsOk (a.list ++ [a_rec]) a_base) (hr_rec : r_rec < r_base)
    {P_flow P_repl : Cmd} {C_F c_F C_R c_R : ℕ}
    (hP_flow : ∀ (w N : ℕ) (G : SimpleGraph (Fin N)) (S : Finset (Fin N))
      (D : List (Fin N)) (z : Fin N) (k ow : ℕ) (s : State),
      wordSize c_F (instSize N G) ≤ w → IsInstanceAt a G S D s → HP25.IsCycleList G D →
      z ∈ S → z ∉ D → 1 ≤ k → k ≤ 4 → ow ≠ z.val → ow ≤ N →
      s.regs (r_base + 3) = z.val → s.regs (r_base + 3 + 1) = k →
      s.regs (r_base + 3 + 2) = ow →
      ∃ s' t, Exec w P_flow s s' t ∧ t ≤ C_F * instSize N G ∧
        KeepsBelow (r_base + 3) (a_base + 10) [] [a_base, a_base + 1] s s' ∧
        ((s'.regs (r_base + 3) = 1 ∧
            IsUnseparable (apex G D) (flowVerts S ow) (some z) none (k - 1)) ∨
          (s'.regs (r_base + 3) = 0 ∧ ∃ X : Finset (Option (Fin N)),
            IsMaxSourceSeparator (apex G D) (flowVerts S ow) (some z) none X ∧ X.card < k ∧
            IsSetListAt a_base {y | some y ∈ X} s' ∧
            IsSetListAt (a_base + 1) {y | some y ∈ sourceSide (apex G D) (flowVerts S ow) none X} s')))
    (hP_repl : ∀ (w N : ℕ) (G : SimpleGraph (Fin N)) (S : Finset (Fin N))
      (D : List (Fin N)) (r : ReplRecord (Fin N)) (recs : List (CrossRecord (Fin N)))
      (S' : Finset (Fin N)) (k : ℕ) (s : State),
      wordSize c_R (instSize N G + (s.arrs a_rec).length) ≤ w → IsInstanceAt a G S D s →
      HP25.IsCycleList G D → r.graph = G → r.verts = S → r.IsValid D →
      (S' : Set (Fin N)) = r.newVerts →
      IsSetListAt (a_base + 2) r.deleted s → IsSetListAt (a_base + 3) (r.boundary : Set (Fin N)) s →
      IsSetListAt (a_base + 4) r.rep s →
      IsRecBufAt a_rec r_rec recs k s → C_R * instSize N G ≤ k →
      ∃ s' t, Exec w P_repl s s' t ∧ t ≤ C_R * instSize N G ∧
        KeepsBelow (r_base + 3) (a_base + 10) [r_rec] (a.list ++ [a_rec]) s s' ∧
        IsInstanceAt a r.newGraph S' D s' ∧
        ∃ k', IsRecBufAt a_rec r_rec (recs ++ [CrossRecord.repl r]) k' s' ∧
          (s'.arrs a_rec).length = (s.arrs a_rec).length ∧ k ≤ k' + C_R * instSize N G)
    {G K : SimpleGraph (Fin N)} {S S_cur : Finset (Fin N)} {D : List (Fin N)}
    {recs₀ recs : List (CrossRecord (Fin N))} {k j : ℕ} (hj : j < N) {s₀ s : State}
    (hinst : IsInstanceAt a K S_cur D s) (hD : HP25.IsCycleList K D)
    (hhist : IsHistoryFin G S D recs K S_cur D) (hlong : ContractionsLong recs)
    (hrepl : AllRepl recs)
    (hbuf : IsRecBufAt a_rec r_rec (recs₀ ++ recs) k s)
    (hpot : K.edgeSet.ncard + 3 * S_cur.card ≤ G.edgeSet.ncard + 3 * S.card)
    (hlen_rec : (s.arrs a_rec).length = (s₀.arrs a_rec).length)
    (hk_cap : 4 * C_R * instSize N G ≤ k)
    (hkeep : KeepsBelow r_base a_base [r_rec] (a.list ++ [a_rec]) s₀ s)
    (hrN : s.regs r_base = N) (hrv : s.regs (r_base + 1) = j)
    (hrch_cyc : s.arrs (a_base + 5) = List.ofFn (fun x : Fin N => if x ∈ D then 1 else 0))
    (hunsep_prev : ∀ u : Fin N, u.1 < j → u ∈ S_cur → u ∉ D →
      IsUnseparable (apex K D) (apexVerts (S_cur : Set (Fin N))) (some u) none 3)
    (hw_F : wordSize c_F (instSize N K) ≤ w)
    (hw_R : wordSize c_R (instSize N K + (s₀.arrs a_rec).length) ≤ w)
    (hw_4K : 4 * instSize N K + 4 < 2 ^ w) :
    ∃ (s' : State) (t : ℕ) (K' : SimpleGraph (Fin N)) (S' : Finset (Fin N))
      (recs' : List (CrossRecord (Fin N))) (k' : ℕ),
      Exec w (phase2BodyProg a a_base (a_base + 2) (a_base + 3) (a_base + 4) (a_base + 5)
        (a_base + 6) (a_base + 7) (a_base + 8) (a_base + 9) P_flow P_repl
        r_base (r_base + 1) (r_base + 2) (r_base + 3)) s s' t ∧
      t ≤ (4 * C_F + 4 * C_R + 2000) * instSize N G ∧
      IsInstanceAt a K' S' D s' ∧ HP25.IsCycleList K' D ∧
      IsHistoryFin G S D recs' K' S' D ∧ ContractionsLong recs' ∧ AllRepl recs' ∧
      IsRecBufAt a_rec r_rec (recs₀ ++ recs') k' s' ∧
      K'.edgeSet.ncard + 3 * S'.card ≤ G.edgeSet.ncard + 3 * S.card ∧
      (s'.arrs a_rec).length = (s₀.arrs a_rec).length ∧
      k ≤ k' + 4 * C_R * instSize N G ∧
      KeepsBelow r_base a_base [r_rec] (a.list ++ [a_rec]) s₀ s' ∧
      s'.regs r_base = N ∧ s'.regs (r_base + 1) = j ∧
      s'.arrs (a_base + 5) = List.ofFn (fun x : Fin N => if x ∈ D then 1 else 0) ∧
      (∀ u : Fin N, u.1 < j + 1 → u ∈ S' → u ∉ D →
        IsUnseparable (apex K' D) (apexVerts (S' : Set (Fin N))) (some u) none 3) := by
  have hK_sz : instSize N K ≤ 4 * instSize N G := (instSize_le_four_mul_of_edge_pot hpot).2
  have hw1 : 1 < 2 ^ w := by omega
  have h0w : 0 < 2 ^ w := by omega
  have h4w : 4 < 2 ^ w := by omega
  have hNw : N < 2 ^ w := by have := le_instSize_self N K; omega
  have hjw : j < 2 ^ w := by omega
  set v : Fin N := ⟨j, hj⟩
  set av : ℕ := if v ∈ S_cur then 1 else 0
  have hav_w : av < 2 ^ w := by simp only [av]; split_ifs <;> omega
  have hal_len : j < (s.arrs a.alive).length := by rw [hinst.length_alive]; exact hj
  have hal_val : (s.arrs a.alive)[j]'hal_len = av := by simp [hinst.2.1, av, v]
  have hrd_al : (Expr.read a.alive (.reg (r_base + 1))).eval w s = some av := by
    have := eval_read (a := a.alive) (eval_reg hrv hjw) hal_len (by rw [hal_val]; exact hav_w)
    rwa [hal_val] at this
  set s₁ := s.setReg (r_base + 2) av
  have hex₁ : Exec w (.assign (r_base + 2) (.read a.alive (.reg (r_base + 1)))) s s₁ 3 :=
    .assign hrd_al
  by_cases hvS : v ∈ S_cur
  · have hav1 : av = 1 := by simp [av, hvS]
    have hcond1 : (Expr.op .eq (.reg (r_base + 2)) (.const 1)).eval w s₁ = some 1 := by
      have := eval_eq (s := s₁) (eval_reg (r := r_base + 2) (by simp [s₁, hav1]) hw1)
        (eval_const hw1) hw1
      simpa using this
    set dv : ℕ := if v ∈ D then 1 else 0
    have hdv_w : dv < 2 ^ w := by simp only [dv]; split_ifs <;> omega
    have hrc_len : j < (s₁.arrs (a_base + 5)).length := by simp [s₁, hrch_cyc, hj]
    have hrc_val : (s₁.arrs (a_base + 5))[j]'hrc_len = dv := by simp [s₁, hrch_cyc, dv, v]
    have hrd_rc : (Expr.read (a_base + 5) (.reg (r_base + 1))).eval w s₁ = some dv := by
      have hrv₁ : s₁.regs (r_base + 1) = j := by simp [s₁, hrv]
      have := eval_read (a := a_base + 5) (eval_reg hrv₁ hjw) hrc_len (by rw [hrc_val]; exact hdv_w)
      rwa [hrc_val] at this
    set s₂ := s₁.setReg (r_base + 2) dv
    have hex₂ : Exec w (.assign (r_base + 2) (.read (a_base + 5) (.reg (r_base + 1)))) s₁ s₂ 3 :=
      .assign hrd_rc
    by_cases hvD : v ∈ D
    · have hdv1 : dv = 1 := by simp [dv, hvD]
      have hcond2 : (Expr.op .eq (.reg (r_base + 2)) (.const 0)).eval w s₂ = some 0 := by
        have := eval_eq (s := s₂) (eval_reg (r := r_base + 2) (by simp [s₂, hdv1]) hw1)
          (eval_const h0w) hw1
        simpa using this
      have hex_ite2 : Exec w (.ite (.op .eq (.reg (r_base + 2)) (.const 0))
          (phase2FlowAndReplaceProg a a_base (a_base + 2) (a_base + 3) (a_base + 4)
            (a_base + 6) (a_base + 7) (a_base + 8) (a_base + 9) P_flow P_repl
            r_base (r_base + 1) (r_base + 3)) .skip) s₂ s₂ 4 :=
        .ite_false hcond2 (.skip s₂)
      have hex_ite1 : Exec w (.ite (.op .eq (.reg (r_base + 2)) (.const 1))
          (.seq (.assign (r_base + 2) (.read (a_base + 5) (.reg (r_base + 1))))
            (.ite (.op .eq (.reg (r_base + 2)) (.const 0))
              (phase2FlowAndReplaceProg a a_base (a_base + 2) (a_base + 3) (a_base + 4)
                (a_base + 6) (a_base + 7) (a_base + 8) (a_base + 9) P_flow P_repl
                r_base (r_base + 1) (r_base + 3)) .skip)) .skip)
          s₁ s₂ 10 := .ite_true hcond1 one_ne_zero (.seq hex₂ hex_ite2)
      have hsz_pos : 1 ≤ instSize N G := instSize_pos N G
      have h_mul : (4 * C_F + 4 * C_R + 2000) * instSize N G =
          4 * C_F * instSize N G + 4 * C_R * instSize N G + 2000 * instSize N G := by ring
      refine ⟨s₂, 13, K, S_cur, recs, k, .seq hex₁ hex_ite1, by omega,
        hinst.of_keeps_disjoint (fun _ _ => rfl), hD, hhist, hlong, hrepl,
        hbuf.of_arrs_regs_eq rfl (by simp [s₂, s₁, show r_rec ≠ r_base + 2 by omega]),
        hpot, hlen_rec, by omega,
        (hkeep.setReg_ge (by omega) _).setReg_ge (by omega) _,
        by simp [s₂, s₁, hrN], by simp [s₂, s₁, hrv], hrch_cyc, ?_⟩
      intro u hu_lt huS huD
      rcases Nat.lt_succ_iff_lt_or_eq.mp hu_lt with hlt | heq
      · exact hunsep_prev u hlt huS huD
      · have huv : u = v := Fin.ext heq
        exact (huD (huv ▸ hvD)).elim
    · have hdv0 : dv = 0 := by simp [dv, hvD]
      have hcond2 : (Expr.op .eq (.reg (r_base + 2)) (.const 0)).eval w s₂ = some 1 := by
        have := eval_eq (s := s₂) (eval_reg (r := r_base + 2) (by simp [s₂, hdv0]) h0w)
          (eval_const h0w) hw1
        simpa using this
      set s₃ := s₂.setReg (r_base + 3) j
      have hex_a1 : Exec w (.assign (r_base + 3) (.reg (r_base + 1))) s₂ s₃ 2 :=
        .assign (eval_reg (by simp [s₂, s₁, hrv]) hjw)
      set s₄ := s₃.setReg (r_base + 3 + 1) 4
      have hex_a2 : Exec w (.assign (r_base + 3 + 1) (.const 4)) s₃ s₄ 2 :=
        .assign (eval_const h4w)
      set s₅ := s₄.setReg (r_base + 3 + 2) N
      have hex_a3 : Exec w (.assign (r_base + 3 + 2) (.reg r_base)) s₄ s₅ 2 :=
        .assign (eval_reg (by
          simp [s₄, s₃, s₂, s₁, show r_base ≠ r_base + 3 + 1 by omega, hrN]) hNw)
      have hinst₅ : IsInstanceAt a K S_cur D s₅ := hinst.of_keeps_disjoint (fun _ _ => rfl)
      obtain ⟨s₆, t_fl, hex_fl, ht_fl, hkeep_fl, hres_fl⟩ :=
        hP_flow w N K S_cur D v 4 N s₅ hw_F hinst₅ hD hvS hvD (by omega) (by omega)
          (by simp [v]; omega) le_rfl
          (by simp [s₅, s₄, s₃, v]) (by simp [s₅, s₄]) (by simp [s₅])
      have hno_a : ∀ d, a_base + d ∉ a.list := fun d => add_not_mem_instArrs_of_arrsOk harrs
      have hinst₆ : IsInstanceAt a K S_cur D s₆ :=
        hinst₅.of_keeps_disjoint (fun x hx =>
          hkeep_fl.2 x (lt_trans (mem_instArrs_lt_of_arrsOk harrs hx) (by omega))
            (by simp only [List.mem_cons, List.not_mem_nil, or_false, not_or];
                exact ⟨fun e => hno_a 0 (by simpa [← e] using hx), fun e => hno_a 1 (e ▸ hx)⟩))
      have hrec_lt : a_rec < a_base := harrs.2 a_rec (by simp)
      have ha₆_rec : s₆.arrs a_rec = s.arrs a_rec :=
        hkeep_fl.2 a_rec (by omega) (by simp; omega)
      have hr₆_below : ∀ r₀ < r_base + 2, s₆.regs r₀ = s.regs r₀ := by
        intro r₀ hr₀
        rw [hkeep_fl.1 r₀ (by omega) (by simp)]
        simp [s₅, s₄, s₃, s₂, s₁,
          show r₀ ≠ r_base + 3 + 2 by omega, show r₀ ≠ r_base + 3 + 1 by omega,
          show r₀ ≠ r_base + 3 by omega, show r₀ ≠ r_base + 2 by omega]
      have hkeep_s₆ : KeepsBelow r_base a_base [r_rec] (a.list ++ [a_rec]) s₀ s₆ := by
        refine ⟨fun r₀ hr₀ hnr₀ => by rw [hr₆_below r₀ (by omega)]; exact hkeep.1 r₀ hr₀ hnr₀,
                fun x hx hnx => by
                  rw [hkeep_fl.2 x (by omega) (by simp; omega)]
                  exact hkeep.2 x hx hnx⟩
      have hrch_cyc₆ : s₆.arrs (a_base + 5) =
          List.ofFn (fun x : Fin N => if x ∈ D then 1 else 0) := by
        rw [hkeep_fl.2 (a_base + 5) (by omega) (by simp)]
        exact hrch_cyc
      rcases hres_fl with ⟨hr_fl1, hunsep_v⟩ | ⟨hr_fl0, X, hmax_X, hX_lt, hsep_X, _⟩
      · rw [flowVerts_self] at hunsep_v
        have hcond3 : (Expr.op .eq (.reg (r_base + 3)) (.const 0)).eval w s₆ = some 0 := by
          have := eval_eq (s := s₆) (eval_reg hr_fl1 hw1) (eval_const h0w) hw1
          simpa using this
        have hex_ite3 : Exec w (.ite (.op .eq (.reg (r_base + 3)) (.const 0))
            (phase2ReplaceProg a a_base (a_base + 2) (a_base + 3) (a_base + 4)
              (a_base + 6) (a_base + 7) (a_base + 8) (a_base + 9) P_repl
              (r_base + 1) (r_base + 3)) .skip) s₆ s₆ 4 :=
          .ite_false hcond3 (.skip s₆)
        have hex_fl_all : Exec w
            (phase2FlowAndReplaceProg a a_base (a_base + 2) (a_base + 3) (a_base + 4)
              (a_base + 6) (a_base + 7) (a_base + 8) (a_base + 9) P_flow P_repl
              r_base (r_base + 1) (r_base + 3))
            s₂ s₆ (2 + (2 + (2 + (t_fl + 4)))) :=
          .seq hex_a1 (.seq hex_a2 (.seq hex_a3 (.seq hex_fl hex_ite3)))
        have hex_ite2 : Exec w (.ite (.op .eq (.reg (r_base + 2)) (.const 0))
            (phase2FlowAndReplaceProg a a_base (a_base + 2) (a_base + 3) (a_base + 4)
              (a_base + 6) (a_base + 7) (a_base + 8) (a_base + 9) P_flow P_repl
              r_base (r_base + 1) (r_base + 3)) .skip)
            s₂ s₆ (3 + (2 + (2 + (2 + (t_fl + 4))))) :=
          .ite_true hcond2 one_ne_zero hex_fl_all
        have hex_ite1 : Exec w (.ite (.op .eq (.reg (r_base + 2)) (.const 1))
            (.seq (.assign (r_base + 2) (.read (a_base + 5) (.reg (r_base + 1))))
              (.ite (.op .eq (.reg (r_base + 2)) (.const 0))
                (phase2FlowAndReplaceProg a a_base (a_base + 2) (a_base + 3) (a_base + 4)
                  (a_base + 6) (a_base + 7) (a_base + 8) (a_base + 9) P_flow P_repl
                  r_base (r_base + 1) (r_base + 3)) .skip)) .skip)
            s₁ s₆ (3 + (3 + (3 + (2 + (2 + (2 + (t_fl + 4))))))) :=
          .ite_true hcond1 one_ne_zero (.seq hex₂ hex_ite2)
        have ht_bound : 3 + (3 + (3 + (3 + (2 + (2 + (2 + (t_fl + 4))))))) ≤
            (4 * C_F + 4 * C_R + 2000) * instSize N G := by
          have h1 : C_F * instSize N K ≤ 4 * C_F * instSize N G := by
            calc C_F * instSize N K ≤ C_F * (4 * instSize N G) := Nat.mul_le_mul_left _ hK_sz
              _ = 4 * C_F * instSize N G := by ring
          have h2 : (4 * C_F + 4 * C_R + 2000) * instSize N G =
              4 * C_F * instSize N G + 4 * C_R * instSize N G + 2000 * instSize N G := by ring
          have hsz_pos : 1 ≤ instSize N G := instSize_pos N G
          omega
        refine ⟨s₆, _, K, S_cur, recs, k, .seq hex₁ hex_ite1, ht_bound,
          hinst₆, hD, hhist, hlong, hrepl,
          hbuf.of_arrs_regs_eq ha₆_rec (hr₆_below r_rec (by omega)),
          hpot, by rw [ha₆_rec, hlen_rec], by omega, hkeep_s₆,
          by rw [hr₆_below r_base (by omega), hrN],
          by rw [hr₆_below (r_base + 1) (by omega), hrv],
          hrch_cyc₆, ?_⟩
        intro u hu_lt huS huD
        rcases Nat.lt_succ_iff_lt_or_eq.mp hu_lt with hlt | heq
        · exact hunsep_prev u hlt huS huD
        · have huv : u = v := Fin.ext heq
          subst huv
          exact hunsep_v
      · rw [flowVerts_self] at hmax_X
        have hcond3 : (Expr.op .eq (.reg (r_base + 3)) (.const 0)).eval w s₆ = some 1 := by
          have := eval_eq (s := s₆) (eval_reg hr_fl0 h0w) (eval_const h0w) hw1
          simpa using this
        have hal_ne : ∀ d, a_base + d ≠ a.alive :=
          fun d e => hno_a d (e ▸ by simp [InstArrs.list])
        obtain ⟨s₇, t₇, hex₇, ht₇, hr₇, ha₇, hallow₇⟩ :=
          allowMinusSepProg_exec a a_base (a_base + 6) (r_base + 3)
            hinst₆ hsep_X ⟨hal_ne 6, by omega⟩ hw_4K
        have hinst₇ : IsInstanceAt a K S_cur D s₇ :=
          hinst₆.of_keeps_disjoint (fun x hx => ha₇ x (fun e => hno_a 6 (e ▸ hx)))
        have hrv₇ : s₇.regs (r_base + 1) = v.1 := by
          rw [hr₇ (r_base + 1) (by omega), hr₆_below (r_base + 1) (by omega), hrv]
        obtain ⟨s₈, t₈, hex₈, ht₈, hsrc₈, ha₈, hr₈⟩ :=
          singleSrcProg_exec_nat (w := w) (a_base + 7) (r_base + 1) v (s := s₇) hrv₇ hw1 hNw
        have hinst₈ : IsInstanceAt a K S_cur D s₈ :=
          hinst₇.of_keeps_disjoint (fun x hx => ha₈ x (fun e => hno_a 7 (e ▸ hx)))
        have hallow₈ : s₈.arrs (a_base + 6) =
            List.ofFn (fun x : Fin N =>
              @ite ℕ (x ∈ (S_cur : Set (Fin N)) \ {y | some y ∈ X}) (propDecidable _) 1 0) := by
          rw [ha₈ (a_base + 6) (by omega)]; convert hallow₇
        obtain ⟨s₉, t₉, hex₉, ht₉, hr₉, ha₉, _, hdel₉⟩ :=
          reachSearchProg_exec a (a_base + 6) (a_base + 7) (a_base + 8) (a_base + 2) (a_base + 9)
            (r_base + 3) hinst₈ hallow₈ hsrc₈ (by simp)
            ⟨hno_a 8, by omega, by omega, by omega, by omega⟩
            ⟨hno_a 9, by omega, by omega, by omega⟩
            ⟨hno_a 2, by omega, by omega, by omega⟩ hw_4K
        have hinst₉ : IsInstanceAt a K S_cur D s₉ :=
          hinst₈.of_keeps_disjoint (fun x hx => ha₉ x
            (fun e => hno_a 8 (e ▸ hx)) (fun e => hno_a 2 (e ▸ hx)) (fun e => hno_a 9 (e ▸ hx)))
        have hallow₉ : s₉.arrs (a_base + 6) =
            List.ofFn (fun x : Fin N =>
              @ite ℕ (x ∈ (S_cur : Set (Fin N)) \ {y | some y ∈ X}) (propDecidable _) 1 0) := by
          rw [ha₉ (a_base + 6) (by omega) (by omega) (by omega)]; exact hallow₈
        have hsrc₉ : s₉.arrs (a_base + 7) = [v].map Fin.val := by
          rw [ha₉ (a_base + 7) (by omega) (by omega) (by omega)]; exact hsrc₈
        obtain ⟨s₁₀, t₁₀, hex₁₀, ht₁₀, hr₁₀, ha₁₀, hrch₁₀, hrep₁₀⟩ :=
          reachSearchProg_exec a (a_base + 6) (a_base + 7) (a_base + 8) (a_base + 4) (a_base + 9)
            (r_base + 3) hinst₉ hallow₉ hsrc₉ (by simp)
            ⟨hno_a 8, by omega, by omega, by omega, by omega⟩
            ⟨hno_a 9, by omega, by omega, by omega⟩
            ⟨hno_a 4, by omega, by omega, by omega⟩ hw_4K
        have hinst₁₀ : IsInstanceAt a K S_cur D s₁₀ :=
          hinst₉.of_keeps_disjoint (fun x hx => ha₁₀ x
            (fun e => hno_a 8 (e ▸ hx)) (fun e => hno_a 4 (e ▸ hx)) (fun e => hno_a 9 (e ▸ hx)))
        have hsep₁₀ : IsSetListAt a_base {y | some y ∈ X} s₁₀ := by
          apply hsep_X.of_arrs_eq
          rw [ha₁₀ a_base (by omega) (by omega) (by omega),
              ha₉ a_base (by omega) (by omega) (by omega),
              ha₈ a_base (by omega), ha₇ a_base (by omega)]
        let A : Set (Fin N) := {y | ReachIn K ((S_cur : Set (Fin N)) \ {y | some y ∈ X}) v y}
        have hA_eq : ReachSet K ((S_cur : Set (Fin N)) \ {y | some y ∈ X}) [v] = A :=
          reachSet_singleton K ((S_cur : Set (Fin N)) \ {y | some y ∈ X})
        rw [hA_eq] at hrch₁₀
        obtain ⟨s₁₁, t₁₁, hex₁₁, ht₁₁, hr₁₁, ha₁₁, hbd₁₁⟩ :=
          filterSepToBdProg_exec a a_base (a_base + 8) (a_base + 3) (a_base + 9) (r_base + 3)
            hinst₁₀ hsep₁₀ hrch₁₀
            ⟨hno_a 9, by omega, by omega, by omega⟩
            ⟨hno_a 3, by omega, by omega⟩ hw_4K
        obtain ⟨hvA, N_bd, hN_bd_eq, hval⟩ :=
          sec4Component_proved K (S_cur : Set (Fin N)) D v X (Set.toFinite _)
            hinst.1 hD hvS hvD hmax_X.1.1 (by omega)
        let r : ReplRecord (Fin N) :=
          { graph := K, verts := (S_cur : Set (Fin N)), deleted := A, boundary := N_bd, rep := A }
        let S' : Finset (Fin N) := r.newVerts.toFinset
        have hS'_coe : (S' : Set (Fin N)) = r.newVerts := Set.coe_toFinset r.newVerts
        have ha₁₁_below : ∀ x < a_base, s₁₁.arrs x = s.arrs x := by
          intro x hx
          rw [ha₁₁ x (by omega) (by omega),
              ha₁₀ x (by omega) (by omega) (by omega),
              ha₉ x (by omega) (by omega) (by omega),
              ha₈ x (by omega), ha₇ x (by omega),
              hkeep_fl.2 x (by omega) (by simp; omega)]
          rfl
        have hr₁₁_below : ∀ r₀ < r_base + 2, s₁₁.regs r₀ = s.regs r₀ := by
          intro r₀ hr₀
          rw [hr₁₁ r₀ (by omega), hr₁₀ r₀ (by omega), hr₉ r₀ (by omega),
              hr₈, hr₇ r₀ (by omega), hr₆_below r₀ hr₀]
        have hinst₁₁ : IsInstanceAt a K S_cur D s₁₁ :=
          hinst.of_keeps_disjoint (fun x hx => ha₁₁_below x (mem_instArrs_lt_of_arrsOk harrs hx))
        have hdel₁₁ : IsSetListAt (a_base + 2) r.deleted s₁₁ := by
          change IsSetListAt (a_base + 2) A s₁₁
          rw [← hA_eq]
          apply hdel₉.of_arrs_eq
          rw [ha₁₁ (a_base + 2) (by omega) (by omega),
              ha₁₀ (a_base + 2) (by omega) (by omega) (by omega)]
        have hbd₁₁' : IsSetListAt (a_base + 3) (r.boundary : Set (Fin N)) s₁₁ := by
          change IsSetListAt (a_base + 3) (N_bd : Set (Fin N)) s₁₁
          rwa [hN_bd_eq]
        have hrep₁₁ : IsSetListAt (a_base + 4) r.rep s₁₁ := by
          change IsSetListAt (a_base + 4) A s₁₁
          rw [← hA_eq]
          apply hrep₁₀.of_arrs_eq
          exact ha₁₁ (a_base + 4) (by omega) (by omega)
        have hbuf₁₁ : IsRecBufAt a_rec r_rec (recs₀ ++ recs) k s₁₁ :=
          hbuf.of_arrs_regs_eq (ha₁₁_below a_rec hrec_lt) (hr₁₁_below r_rec (by omega))
        have hlen_rec₁₁ : (s₁₁.arrs a_rec).length = (s₀.arrs a_rec).length := by
          rw [ha₁₁_below a_rec hrec_lt, hlen_rec]
        have hk_R : C_R * instSize N K ≤ k := by
          calc C_R * instSize N K ≤ C_R * (4 * instSize N G) := Nat.mul_le_mul_left _ hK_sz
            _ = 4 * C_R * instSize N G := by ring
            _ ≤ k := hk_cap
        obtain ⟨s₁₂, t₁₂, hex₁₂, ht₁₂, hkeep₁₂, hinst₁₂, k', hbuf₁₂, hlen₁₂, hk₁₂⟩ :=
          hP_repl w N K S_cur D r (recs₀ ++ recs) S' k s₁₁
            (by rwa [hlen_rec₁₁]) hinst₁₁ hD rfl rfl hval hS'_coe
            hdel₁₁ hbd₁₁' hrep₁₁ hbuf₁₁ hk_R
        have hex_repl_all : Exec w
            (phase2ReplaceProg a a_base (a_base + 2) (a_base + 3) (a_base + 4)
              (a_base + 6) (a_base + 7) (a_base + 8) (a_base + 9) P_repl
              (r_base + 1) (r_base + 3))
            s₆ s₁₂ (t₇ + (t₈ + (t₉ + (t₁₀ + (t₁₁ + t₁₂))))) :=
          .seq hex₇ (.seq hex₈ (.seq hex₉ (.seq hex₁₀ (.seq hex₁₁ hex₁₂))))
        have hex_ite3 : Exec w (.ite (.op .eq (.reg (r_base + 3)) (.const 0))
            (phase2ReplaceProg a a_base (a_base + 2) (a_base + 3) (a_base + 4)
              (a_base + 6) (a_base + 7) (a_base + 8) (a_base + 9) P_repl
              (r_base + 1) (r_base + 3)) .skip)
            s₆ s₁₂ (3 + (t₇ + (t₈ + (t₉ + (t₁₀ + (t₁₁ + t₁₂)))))) :=
          .ite_true hcond3 one_ne_zero hex_repl_all
        have hex_fl_all : Exec w
            (phase2FlowAndReplaceProg a a_base (a_base + 2) (a_base + 3) (a_base + 4)
              (a_base + 6) (a_base + 7) (a_base + 8) (a_base + 9) P_flow P_repl
              r_base (r_base + 1) (r_base + 3))
            s₂ s₁₂ (2 + (2 + (2 + (t_fl + (3 + (t₇ + (t₈ + (t₉ + (t₁₀ + (t₁₁ + t₁₂)))))))))) :=
          .seq hex_a1 (.seq hex_a2 (.seq hex_a3 (.seq hex_fl hex_ite3)))
        have hex_ite2 : Exec w (.ite (.op .eq (.reg (r_base + 2)) (.const 0))
            (phase2FlowAndReplaceProg a a_base (a_base + 2) (a_base + 3) (a_base + 4)
              (a_base + 6) (a_base + 7) (a_base + 8) (a_base + 9) P_flow P_repl
              r_base (r_base + 1) (r_base + 3)) .skip)
            s₂ s₁₂ (3 + (2 + (2 + (2 + (t_fl + (3 + (t₇ + (t₈ + (t₉ + (t₁₀ + (t₁₁ + t₁₂))))))))))) :=
          .ite_true hcond2 one_ne_zero hex_fl_all
        have hex_ite1 : Exec w (.ite (.op .eq (.reg (r_base + 2)) (.const 1))
            (.seq (.assign (r_base + 2) (.read (a_base + 5) (.reg (r_base + 1))))
              (.ite (.op .eq (.reg (r_base + 2)) (.const 0))
                (phase2FlowAndReplaceProg a a_base (a_base + 2) (a_base + 3) (a_base + 4)
                  (a_base + 6) (a_base + 7) (a_base + 8) (a_base + 9) P_flow P_repl
                  r_base (r_base + 1) (r_base + 3)) .skip)) .skip)
            s₁ s₁₂
            (3 + (3 + (3 + (2 + (2 + (2 + (t_fl + (3 + (t₇ + (t₈ + (t₉ + (t₁₀ + (t₁₁ + t₁₂))))))))))))) :=
          .ite_true hcond1 one_ne_zero (.seq hex₂ hex_ite2)
        have hkeep_s₁₁ : KeepsBelow r_base a_base [r_rec] (a.list ++ [a_rec]) s₀ s₁₁ :=
          ⟨fun r₀ hr₀ hnr₀ => by rw [hr₁₁_below r₀ (by omega)]; exact hkeep.1 r₀ hr₀ hnr₀,
           fun x hx hnx => by rw [ha₁₁_below x hx]; exact hkeep.2 x hx hnx⟩
        have hkeep_s₁₂ : KeepsBelow r_base a_base [r_rec] (a.list ++ [a_rec]) s₀ s₁₂ :=
          hkeep_s₁₁.trans (hkeep₁₂.le (by omega) (by omega))
            (fun _ hm _ => hm) (fun _ hm _ => hm)
        have hrN₁₂ : s₁₂.regs r_base = N := by
          rw [hkeep₁₂.1 r_base (by omega) (by simp; omega), hr₁₁_below r_base (by omega), hrN]
        have hrv₁₂ : s₁₂.regs (r_base + 1) = j := by
          rw [hkeep₁₂.1 (r_base + 1) (by omega) (by simp; omega),
              hr₁₁_below (r_base + 1) (by omega), hrv]
        have hrch_cyc₁₂ : s₁₂.arrs (a_base + 5) =
            List.ofFn (fun x : Fin N => if x ∈ D then 1 else 0) := by
          rw [hkeep₁₂.2 (a_base + 5) (by omega) (by
            simp only [List.mem_append, List.mem_singleton, not_or]
            exact ⟨hno_a 5, by omega⟩)]
          rw [ha₁₁ (a_base + 5) (by omega) (by omega),
              ha₁₀ (a_base + 5) (by omega) (by omega) (by omega),
              ha₉ (a_base + 5) (by omega) (by omega) (by omega),
              ha₈ (a_base + 5) (by omega), ha₇ (a_base + 5) (by omega)]
          exact hrch_cyc₆
        have ht_bound :
            3 + (3 + (3 + (3 + (2 + (2 + (2 + (t_fl + (3 + (t₇ + (t₈ + (t₉ + (t₁₀ + (t₁₁ + t₁₂))))))))))))) ≤
            (4 * C_F + 4 * C_R + 2000) * instSize N G := by
          have h1 : C_F * instSize N K ≤ 4 * C_F * instSize N G := by
            calc C_F * instSize N K ≤ C_F * (4 * instSize N G) := Nat.mul_le_mul_left _ hK_sz
              _ = 4 * C_F * instSize N G := by ring
          have h2 : C_R * instSize N K ≤ 4 * C_R * instSize N G := by
            calc C_R * instSize N K ≤ C_R * (4 * instSize N G) := Nat.mul_le_mul_left _ hK_sz
              _ = 4 * C_R * instSize N G := by ring
          have h3 : (4 * C_F + 4 * C_R + 2000) * instSize N G =
              4 * C_F * instSize N G + 4 * C_R * instSize N G + 2000 * instSize N G := by ring
          have hsz_pos : 1 ≤ instSize N G := instSize_pos N G
          omega
        have hk_bound : k ≤ k' + 4 * C_R * instSize N G := by
          have h1 : C_R * instSize N K ≤ 4 * C_R * instSize N G := by
            calc C_R * instSize N K ≤ C_R * (4 * instSize N G) := Nat.mul_le_mul_left _ hK_sz
              _ = 4 * C_R * instSize N G := by ring
          omega
        refine ⟨s₁₂, _, r.newGraph, S', recs ++ [CrossRecord.repl r], k',
          .seq hex₁ hex_ite1, ht_bound, hinst₁₂, ReplRecord.isCycleList_newGraph hD hval,
          hhist.snoc_repl rfl rfl hval hS'_coe, hlong.append_repl, hrepl.append_repl,
          by rwa [← List.append_assoc],
          le_trans (edge_pot_step rfl rfl hval hS'_coe).2.2 hpot,
          hlen₁₂.trans hlen_rec₁₁, hk_bound, hkeep_s₁₂, hrN₁₂, hrv₁₂, hrch_cyc₁₂, ?_⟩
        intro u hu_lt huS' huD
        have hu_new : u ∈ r.newVerts := by rwa [← hS'_coe]
        rcases Nat.lt_succ_iff_lt_or_eq.mp hu_lt with hlt | heq
        · have hu_old : u ∈ S_cur := hu_new.1
          have hunsep_old := hunsep_prev u hlt hu_old huD
          rw [hS'_coe]
          exact lemma2Apex_proved r D u 3 hinst.1 hD hval hu_new hunsep_old
        · have huv : u = v := Fin.ext heq
          subst huv
          exact (hu_new.2 hvA).elim
  · have hav0 : av = 0 := by simp [av, hvS]
    have hcond1 : (Expr.op .eq (.reg (r_base + 2)) (.const 1)).eval w s₁ = some 0 := by
      have := eval_eq (s := s₁) (eval_reg (r := r_base + 2) (by simp [s₁, hav0]) h0w)
        (eval_const hw1) hw1
      simpa using this
    have hex_ite1 : Exec w (.ite (.op .eq (.reg (r_base + 2)) (.const 1))
        (.seq (.assign (r_base + 2) (.read (a_base + 5) (.reg (r_base + 1))))
          (.ite (.op .eq (.reg (r_base + 2)) (.const 0))
            (phase2FlowAndReplaceProg a a_base (a_base + 2) (a_base + 3) (a_base + 4)
              (a_base + 6) (a_base + 7) (a_base + 8) (a_base + 9) P_flow P_repl
              r_base (r_base + 1) (r_base + 3)) .skip)) .skip)
        s₁ s₁ 4 := .ite_false hcond1 (.skip s₁)
    have hsz_pos : 1 ≤ instSize N G := instSize_pos N G
    have h_mul : (4 * C_F + 4 * C_R + 2000) * instSize N G =
        4 * C_F * instSize N G + 4 * C_R * instSize N G + 2000 * instSize N G := by ring
    refine ⟨s₁, 7, K, S_cur, recs, k, .seq hex₁ hex_ite1, by omega,
      hinst.of_keeps_disjoint (fun _ _ => rfl), hD, hhist, hlong, hrepl,
      hbuf.of_arrs_regs_eq rfl (by simp [s₁, show r_rec ≠ r_base + 2 by omega]),
      hpot, hlen_rec, by omega, hkeep.setReg_ge (by omega) _,
      by simp [s₁, hrN], by simp [s₁, hrv], hrch_cyc, ?_⟩
    intro u hu_lt huS huD
    rcases Nat.lt_succ_iff_lt_or_eq.mp hu_lt with hlt | heq
    · exact hunsep_prev u hlt huS huD
    · have huv : u = v := Fin.ext heq
      exact (hvS (huv ▸ huS)).elim

/-- **Strengthened initial cleaning** (`InitialCleaningRecFullProgClaim`) proved from
`ReplaceRecProgClaim` and `boundedFlowProgLeClaim_proved`. -/
theorem initialCleaningRecFullProgClaim_of :
    InitialCleaningRecFullProgClaim := by
  intro a a_rec r_rec a_base r_base harrs hr_rec
  obtain ⟨P_flow, C_F, c_F, hP_flow⟩ :=
    boundedFlowProgLeClaim_proved a a_base (a_base + 1) (a_base + 10) (r_base + 3)
      (arrsOk_flow_of_arrsOk harrs)
  obtain ⟨P_repl, C_R, c_R, hP_repl⟩ :=
    replaceRecProgClaim_proved a (a_base + 2) (a_base + 3) (a_base + 4) a_rec r_rec (a_base + 10) (r_base + 3)
      (arrsOk_repl_of_arrsOk harrs) (by omega)
  let C_total := 4 * C_F + 8 * C_R + 4000
  let c_total := 3 * c_F + 3 * c_R + 5
  refine ⟨initialCleaningProg a a_base P_flow P_repl r_base, C_total, c_total, ?_⟩
  intro w N G S D recs₀ k s hw hinst hD hbuf hk
  have h1_cap : N * (4 * C_R * instSize N G) ≤ k := by
    have : N * (4 * C_R * instSize N G) + N * (4 * C_R * instSize N G) ≤
        C_total * (N + 1) * instSize N G := by
      dsimp only [C_total]
      have : (4 * C_F + 8 * C_R + 4000) * (N + 1) * instSize N G =
          N * (4 * C_R * instSize N G) + N * (4 * C_R * instSize N G) +
          (4 * C_F + 4000) * (N + 1) * instSize N G + 8 * C_R * instSize N G := by ring
      omega
    omega
  obtain ⟨s₁, t₁, G₁, S₁, recs₁, k₁, hex₁, ht₁, hinst₁, hD₁, hhist₁, hlong₁, hrepl₁,
    hbuf₁, hpot₁, hlen₁, hk₁, hkeep₁⟩ :=
    phase1Prog_exec_full a a_rec r_rec a_base r_base harrs hr_rec hP_repl (c_F := c_F)
      hw hinst hD hbuf h1_cap
  have hG₁_sz := (instSize_le_four_mul_of_edge_pot hpot₁).2
  have hb1 := wordSize_subprog_bounds hG₁_sz hw
  have hw1 : 1 < 2 ^ w := hb1.2.2.2.2.1
  have h0w : 0 < 2 ^ w := by omega
  have hNw : N < 2 ^ w := hb1.2.2.2.2.2
  have hno_a : ∀ d, a_base + d ∉ a.list := fun d => add_not_mem_instArrs_of_arrsOk harrs
  have hcyc_ne : ∀ d, a_base + d ≠ a.cyc :=
    fun d e => hno_a d (e ▸ by simp [InstArrs.list])
  have hD_len : D.length ≤ N := isCycleList_length_le_fin hD₁
  obtain ⟨s₂, t₂, hex₂, ht₂, hr₂, ha₂, hrch_cyc₂⟩ :=
    allowFromListProg_exec a a.cyc (a_base + 5) (r_base + 3)
      hinst₁ hinst₁.2.2.2.2 hD_len (hcyc_ne 5) hb1.2.2.1
  have hinst₂ : IsInstanceAt a G₁ S₁ D s₂ :=
    hinst₁.of_keeps_disjoint (fun x hx => ha₂ x (fun e => hno_a 5 (e ▸ hx)))
  have hal_len₂ : (s₂.arrs a.alive).length = N := hinst₂.length_alive
  set s₃ := s₂.setReg r_base N
  have hex₃ : Exec w (.assign r_base (.len a.alive)) s₂ s₃ 2 :=
    .assign (by rw [← hal_len₂]; exact eval_len rfl (by rw [hal_len₂]; exact hNw))
  set s₄ := s₃.setReg (r_base + 1) 0
  have hex₄ : Exec w (.assign (r_base + 1) (.const 0)) s₃ s₄ 2 := .assign (eval_const h0w)
  let I₂ : ℕ → State → Prop := fun j st =>
    st.regs r_base = N ∧ st.regs (r_base + 1) = j ∧
    st.arrs (a_base + 5) = List.ofFn (fun x : Fin N => if x ∈ D then 1 else 0) ∧
    (st.arrs a_rec).length = (s.arrs a_rec).length ∧
    KeepsBelow r_base a_base [r_rec] (a.list ++ [a_rec]) s st ∧
    ∃ (K : SimpleGraph (Fin N)) (S_cur : Finset (Fin N)) (recs : List (CrossRecord (Fin N)))
      (k_cur : ℕ),
      IsInstanceAt a K S_cur D st ∧ HP25.IsCycleList K D ∧
      IsHistoryFin G S D recs K S_cur D ∧ ContractionsLong recs ∧ AllRepl recs ∧
      IsRecBufAt a_rec r_rec (recs₀ ++ recs) k_cur st ∧
      K.edgeSet.ncard + 3 * S_cur.card ≤ G.edgeSet.ncard + 3 * S.card ∧
      k₁ ≤ k_cur + j * (4 * C_R * instSize N G) ∧
      (∀ u : Fin N, u.1 < j → u ∈ S_cur → u ∉ D →
        IsUnseparable (apex K D) (apexVerts (S_cur : Set (Fin N))) (some u) none 3)
  have hrec_lt : a_rec < a_base := harrs.2 a_rec (by simp)
  have hkeep₄ : KeepsBelow r_base a_base [r_rec] (a.list ++ [a_rec]) s s₄ := by
    refine ⟨fun r₀ hr₀ hnr₀ => ?_, fun x hx hnx => ?_⟩
    · simp only [s₄, s₃, State.setReg_regs_ne _ _ (show r₀ ≠ r_base + 1 by omega),
        State.setReg_regs_ne _ _ (show r₀ ≠ r_base by omega)]
      rw [hr₂ r₀ (by omega)]
      exact hkeep₁.1 r₀ hr₀ hnr₀
    · simp only [s₄, s₃, State.setReg_arrs]
      rw [ha₂ x (by omega)]
      exact hkeep₁.2 x hx hnx
  have hI₂0 : I₂ 0 s₄ := by
    refine ⟨by simp [s₄, s₃], by simp [s₄], hrch_cyc₂,
      by simp [s₄, s₃, ha₂ a_rec (by omega), hlen₁], hkeep₄,
      G₁, S₁, recs₁, k₁, hinst₂, hD₁, hhist₁, hlong₁, hrepl₁, ?_, hpot₁, by omega,
      fun _ h => (Nat.not_lt_zero _ h).elim⟩
    exact hbuf₁.of_arrs_regs_eq (ha₂ a_rec (by omega))
      (by simp [s₄, s₃, show r_rec ≠ r_base + 1 by omega, show r_rec ≠ r_base by omega,
        hr₂ r_rec (by omega)])
  let B₂ := (4 * C_F + 4 * C_R + 2000) * instSize N G
  have h2_cap : N * (4 * C_R * instSize N G) ≤ k₁ := by
    have : N * (4 * C_R * instSize N G) + N * (4 * C_R * instSize N G) ≤
        C_total * (N + 1) * instSize N G := by
      dsimp only [C_total]
      have : (4 * C_F + 8 * C_R + 4000) * (N + 1) * instSize N G =
          N * (4 * C_R * instSize N G) + N * (4 * C_R * instSize N G) +
          (4 * C_F + 4000) * (N + 1) * instSize N G + 8 * C_R * instSize N G := by ring
      omega
    omega
  obtain ⟨s₅, t₅, hex₅, ht₅, hI₂N⟩ := forUp_exec' I₂ N B₂
    (r_i := r_base + 1) (hi := .reg r_base)
    (body := phase2BodyProg a a_base (a_base + 2) (a_base + 3) (a_base + 4) (a_base + 5)
      (a_base + 6) (a_base + 7) (a_base + 8) (a_base + 9) P_flow P_repl
      r_base (r_base + 1) (r_base + 2) (r_base + 3))
    hw1 hNw
    (fun j _ st hI => ⟨hI.2.1, eval_reg hI.1 hNw⟩)
    (fun j hj st hI => by
      obtain ⟨hrN, hrv, hrch, hlen, hkeep, K, S_cur, recs, k_cur,
        hinst_K, hD_K, hhist, hlong, hrepl, hbuf_K, hpot, hk_j, hunsep_prev⟩ := hI
      have hK_sz := (instSize_le_four_mul_of_edge_pot hpot).2
      have hwb := wordSize_subprog_bounds hK_sz hw
      have hk_rem : 4 * C_R * instSize N G ≤ k_cur := by
        have : (j + 1) * (4 * C_R * instSize N G) ≤ N * (4 * C_R * instSize N G) :=
          Nat.mul_le_mul_right _ (by omega)
        rw [Nat.add_mul, Nat.one_mul] at this
        omega
      obtain ⟨st', t', K', S', recs', k', hex_b, ht_b, hinst', hD', hhist', hlong', hrepl',
        hbuf', hpot', hlen', hk', hkeep', hrN', hrv', hrch', hunsep'⟩ :=
        phase2BodyProg_exec_full a a_rec r_rec a_base r_base harrs hr_rec hP_flow hP_repl hj
          hinst_K hD_K hhist hlong hrepl hbuf_K hpot hlen hk_rem hkeep hrN hrv hrch hunsep_prev
          hwb.1 hwb.2.1 hwb.2.2.1
      refine ⟨st', t', hex_b, ht_b, ?_, hrv'⟩
      refine ⟨by simp [hrN'], by simp, hrch', hlen', hkeep'.setReg_ge (by omega) _,
        K', S', recs', k', hinst'.of_keeps_disjoint (fun _ _ => rfl), hD', hhist', hlong', hrepl',
        hbuf'.of_arrs_regs_eq rfl (by simp [show r_rec ≠ r_base + 1 by omega]),
        hpot', ?_, hunsep'⟩
      rw [Nat.add_mul, Nat.one_mul]
      omega)
    s₄ hI₂0
  obtain ⟨_, _, _, hlen₅, hkeep₅, G', S', recs, k',
    hinst₅, hD₅, hhist₅, hlong₅, hrepl₅, hbuf₅, hpot₅, hk₅, hunsep₅⟩ := hI₂N
  have hclean : IsClean G' (S' : Set (Fin N)) D :=
    sec4Clean_proved G' (S' : Set (Fin N)) D hinst₅.1 hD₅
      (fun u huS huD => hunsep₅ u u.isLt huS huD)
  have hedge_le : G'.edgeSet.ncard ≤ G.edgeSet.ncard + 3 * N :=
    (instSize_le_four_mul_of_edge_pot hpot₅).1
  have hcross_iff : HP25.IsCrossed G D ↔ HP25.IsCrossed G' D :=
    isCrossed_iff_of_allRepl hinst.1 hD hD₅ hhist₅ hlong₅ hrepl₅
  have hex_p2 : Exec w (phase2Prog a a_base P_flow P_repl r_base) s₁ s₅
      (t₂ + (2 + (2 + t₅))) :=
    .seq hex₂ (.seq hex₃ (.seq hex₄ hex₅))
  have ht_total : t₁ + (t₂ + (2 + (2 + t₅))) ≤ C_total * (N + 1) * instSize N G := by
    simp only [Expr.cost, B₂] at ht₅
    have h1 : 20 * instSize N G₁ ≤ 80 * instSize N G := by omega
    have hsz_pos : 1 ≤ instSize N G := instSize_pos N G
    have hN_le : N ≤ N * instSize N G := by
      simpa using Nat.mul_le_mul_left N hsz_pos
    have hring : C_total * (N + 1) * instSize N G + 7 * N =
        (4 * C_R + 1800) * (N + 1) * instSize N G +
        N * (1 + 6 + (4 * C_F + 4 * C_R + 2000) * instSize N G) +
        (4 * C_F + 4 * C_R) * instSize N G + 200 * (N * instSize N G) +
        2200 * instSize N G := by
      dsimp only [C_total]; ring
    omega
  have hk_total : k ≤ k' + C_total * (N + 1) * instSize N G := by
    have : N * (4 * C_R * instSize N G) + N * (4 * C_R * instSize N G) ≤
        C_total * (N + 1) * instSize N G := by
      dsimp only [C_total]
      have : (4 * C_F + 8 * C_R + 4000) * (N + 1) * instSize N G =
          N * (4 * C_R * instSize N G) + N * (4 * C_R * instSize N G) +
          (4 * C_F + 4000) * (N + 1) * instSize N G + 8 * C_R * instSize N G := by ring
      omega
    omega
  exact ⟨s₅, _, .seq hex₁ hex_p2, ht_total, hkeep₅,
    G', S', recs, k', hinst₅, hD₅, hclean, hhist₅, hlong₅, hcross_iff,
    hbuf₅, hedge_le, hlen₅, hk_total⟩

end GraphMinor.Compute.Crossing
