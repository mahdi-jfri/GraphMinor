module

public import GraphMinor.Compute.Algorithm41Aux7

/-!
# Execution of `combineStepProg` for GM XIII (4.1)

This file completes the verification of the constant-time table combination step `combineStepProg`
for Algorithm (4.1) of Robertson and Seymour,
*Graph Minors. XIII. The Disjoint Paths Problem* (pages 75–76):

1. **Section 1 (`tabsSlotProg_exec`, `tabsCombineBodyProg_exec`, `combineDispatchProg_exec`):**
   Verifies the slot-fill program `tabsSlotProg`, the combination body `tabsCombineBodyProg`, and
   the three-level `branchOnBound` dispatch `combineDispatchProg`.
2. **Section 2 (`copyOutToAccProg_exec`, `combineStepProg_exec`, `combineStepProg_exec_pieceTables`):**
   Proves that `combineStepProg` combines `bufA` and `bufB` into `bufA` in $O(1)$ time, producing a
   `ValidPieceBuffer` for `rawCombineTables` (and hence for `combinePieceTables`).
-/

@[expose] public section

namespace GraphMinor.Compute

open SimpleGraph

/-! ### Section 1: Execution of `tabsSlotProg`, `tabsCombineBodyProg`, and `combineDispatchProg` -/

private theorem biUnion_range_succ {α : Type*} [DecidableEq α] (f : ℕ → Finset α) (k : ℕ) :
    (Finset.range (k + 1)).biUnion f = (Finset.range k).biUnion f ∪ f k := by
  rw [Finset.range_add_one, Finset.biUnion_insert, Finset.union_comm]

theorem tabsSlotProg_exec {w δ ξ ω q_U kv₀ ke₀ kv ke pos : ℕ}
    {G : ComputeDigraph} {ZA ZB : Finset (Fin G.numVerts)}
    {EA EB : Finset (Fin G.numEdges)}
    {es_A : List (RawCertEntry G ZA.card)}
    {es_B : List (RawCertEntry G ZB.card)}
    {S_A S_B S_Z : Finset (Fin q_U)} {s₀ s : State}
    (hbufA : ValidPieceBuffer δ ξ ω G ZA EA es_A bufA s₀)
    (hbufB : ValidPieceBuffer δ ξ ω G ZB EB es_B bufB s₀)
    (hw2 : 2 < 2 ^ w) (hm_w : G.numEdges < 2 ^ w) (hS_w : S_tab δ ξ ω < 2 ^ w)
    (hkv_w : kv + 2 * V_max δ ξ ω < 2 ^ w) (hke_w : ke + 2 * V_max δ ξ ω < 2 ^ w)
    (hkv0_le : kv₀ ≤ kv) (hke0_le : ke₀ ≤ ke)
    (hr_kv0 : s₀.regs r_kv = kv₀) (hr_ke0 : s₀.regs r_ke = ke₀)
    (hwfV : ArenaWF G.numVerts kv (s.arrs a_vkd) (s.arrs a_vv1) (s.arrs a_vv2))
    (hwfE : ArenaWF G.numEdges ke (s.arrs a_ekd) (s.arrs a_ev1) (s.arrs a_ev2))
    (hkv_cap : kv + 2 * V_max δ ξ ω ≤ (s.arrs a_vkd).length)
    (hke_cap : ke + 2 * V_max δ ξ ω ≤ (s.arrs a_ekd).length)
    (hevalV0 : ∀ p < kv₀,
      evalArena G.numVerts (s.arrs a_vkd) (s.arrs a_vv1) (s.arrs a_vv2) p =
        evalArena G.numVerts (s₀.arrs a_vkd) (s₀.arrs a_vv1) (s₀.arrs a_vv2) p)
    (hevalE0 : ∀ p < ke₀,
      evalArena G.numEdges (s.arrs a_ekd) (s.arrs a_ev1) (s.arrs a_ev2) p =
        evalArena G.numEdges (s₀.arrs a_ekd) (s₀.arrs a_ev1) (s₀.arrs a_ev2) p)
    (hacc_vv : s.arrs a_acc_vv = s₀.arrs a_acc_vv)
    (hacc_ve : s.arrs a_acc_ve = s₀.arrs a_acc_ve)
    (hacc_em : s.arrs a_acc_em = s₀.arrs a_acc_em)
    (hrhs_vv : s.arrs a_rhs_vv = s₀.arrs a_rhs_vv)
    (hrhs_ve : s.arrs a_rhs_ve = s₀.arrs a_rhs_ve)
    (hrhs_em : s.arrs a_rhs_em = s₀.arrs a_rhs_em)
    (hr_kv : s.regs r_kv = kv) (hr_ke : s.regs r_ke = ke)
    (hpos : pos < S_tab δ ξ ω)
    (hout_vv_len : (s.arrs a_out_vv).length = S_tab δ ξ ω)
    (hout_ve_len : (s.arrs a_out_ve).length = S_tab δ ξ ω)
    (hout_em_len : (s.arrs a_out_em).length = S_tab δ ξ ω) :
    let tab_A : AbstractTable := ⟨ZA.card, es_A.map RawCertEntry.H⟩
    let tab_B : AbstractTable := ⟨ZB.card, es_B.map RawCertEntry.H⟩
    let kv' := kv + 2 * V_max δ ξ ω
    let ke' := ke + 2 * V_max δ ξ ω
    ∃ s' t,
      Exec w (tabsSlotProg δ ξ ω tab_A tab_B q_U S_A S_B S_Z pos) s s' t ∧
      t ≤ 20 + 90 * V_max δ ξ ω ∧
      s'.regs r_kv = kv' ∧ s'.regs r_ke = ke' ∧
      ArenaWF G.numVerts kv' (s'.arrs a_vkd) (s'.arrs a_vv1) (s'.arrs a_vv2) ∧
      ArenaWF G.numEdges ke' (s'.arrs a_ekd) (s'.arrs a_ev1) (s'.arrs a_ev2) ∧
      (s'.arrs a_vkd).length = (s.arrs a_vkd).length ∧
      (s'.arrs a_ekd).length = (s.arrs a_ekd).length ∧
      (∀ p < kv,
        evalArena G.numVerts (s'.arrs a_vkd) (s'.arrs a_vv1) (s'.arrs a_vv2) p =
          evalArena G.numVerts (s.arrs a_vkd) (s.arrs a_vv1) (s.arrs a_vv2) p) ∧
      (∀ p < ke,
        evalArena G.numEdges (s'.arrs a_ekd) (s'.arrs a_ev1) (s'.arrs a_ev2) p =
          evalArena G.numEdges (s.arrs a_ekd) (s.arrs a_ev1) (s.arrs a_ev2) p) ∧
      (s'.arrs a_out_vv).length = S_tab δ ξ ω ∧
      (s'.arrs a_out_ve).length = S_tab δ ξ ω ∧
      (s'.arrs a_out_em).length = S_tab δ ξ ω ∧
      (s'.arrs a_out_vv).getD pos 0 < kv' ∧
      evalArena G.numVerts (s'.arrs a_vkd) (s'.arrs a_vv1) (s'.arrs a_vv2)
        ((s'.arrs a_out_vv).getD pos 0) =
        slotTargetVV (δ := δ) (ξ := ξ) (ω := ω) es_A es_B S_A S_B S_Z pos ∧
      (s'.arrs a_out_ve).getD pos 0 < ke' ∧
      evalArena G.numEdges (s'.arrs a_ekd) (s'.arrs a_ev1) (s'.arrs a_ev2)
        ((s'.arrs a_out_ve).getD pos 0) =
        slotTargetVE (δ := δ) (ξ := ξ) (ω := ω) es_A es_B S_A S_B S_Z pos ∧
      (s'.arrs a_out_em).getD pos 0 =
        slotTargetEM (δ := δ) (ξ := ξ) (ω := ω) es_A es_B S_A S_B S_Z pos ∧
      (s'.arrs a_out_em).getD pos 0 ≤ G.numEdges ∧
      (∀ i < pos,
        (s'.arrs a_out_vv).getD i 0 = (s.arrs a_out_vv).getD i 0 ∧
        (s'.arrs a_out_ve).getD i 0 = (s.arrs a_out_ve).getD i 0 ∧
        (s'.arrs a_out_em).getD i 0 = (s.arrs a_out_em).getD i 0) ∧
      (∀ r < 10, r ≠ r_kv → r ≠ r_ke → s'.regs r = s.regs r) ∧
      (∀ a, a ≠ a_vkd → a ≠ a_vv1 → a ≠ a_vv2 → a ≠ a_ekd → a ≠ a_ev1 → a ≠ a_ev2 →
        a ≠ a_out_vv → a ≠ a_out_ve → a ≠ a_out_em → s'.arrs a = s.arrs a) := by
  intro tab_A tab_B kv' ke'
  have h0_w : 0 < 2 ^ w := by omega
  have hpos_w : pos < 2 ^ w := by omega
  let s₁ := (s.setReg 10 0).setReg 11 0
  have hex₁ : Exec w (.assign 10 (.const 0)) s (s.setReg 10 0) 2 :=
    .assign (by simp [Expr.eval, checkWord, h0_w])
  have hex₂ : Exec w (.assign 11 (.const 0)) (s.setReg 10 0) s₁ 2 :=
    .assign (by simp [Expr.eval, checkWord, h0_w])
  -- Fold A over `u_A < V_max δ ξ ω`
  let P_A : ℕ → State → Prop := fun k s_k =>
    s_k.regs r_kv = kv + k ∧ s_k.regs r_ke = ke + k ∧
    ArenaWF G.numVerts (kv + k) (s_k.arrs a_vkd) (s_k.arrs a_vv1) (s_k.arrs a_vv2) ∧
    ArenaWF G.numEdges (ke + k) (s_k.arrs a_ekd) (s_k.arrs a_ev1) (s_k.arrs a_ev2) ∧
    (s_k.arrs a_vkd).length = (s.arrs a_vkd).length ∧
    (s_k.arrs a_ekd).length = (s.arrs a_ekd).length ∧
    (∀ p < kv,
      evalArena G.numVerts (s_k.arrs a_vkd) (s_k.arrs a_vv1) (s_k.arrs a_vv2) p =
        evalArena G.numVerts (s.arrs a_vkd) (s.arrs a_vv1) (s.arrs a_vv2) p) ∧
    (∀ p < ke,
      evalArena G.numEdges (s_k.arrs a_ekd) (s_k.arrs a_ev1) (s_k.arrs a_ev2) p =
        evalArena G.numEdges (s.arrs a_ekd) (s.arrs a_ev1) (s.arrs a_ev2) p) ∧
    s_k.regs 10 < kv + k ∧ s_k.regs 11 < ke + k ∧
    evalArena G.numVerts (s_k.arrs a_vkd) (s_k.arrs a_vv1) (s_k.arrs a_vv2) (s_k.regs 10) =
      (Finset.range k).biUnion (slotVertSetA (δ := δ) (ξ := ξ) (ω := ω) es_A es_B S_A S_B S_Z pos) ∧
    evalArena G.numEdges (s_k.arrs a_ekd) (s_k.arrs a_ev1) (s_k.arrs a_ev2) (s_k.regs 11) =
      (Finset.range k).biUnion (slotEdgeSetA (δ := δ) (ξ := ξ) (ω := ω) es_A es_B S_A S_B S_Z pos) ∧
    (∀ r < 10, r ≠ r_kv → r ≠ r_ke → s_k.regs r = s.regs r) ∧
    (∀ a, a ≠ a_vkd → a ≠ a_vv1 → a ≠ a_vv2 → a ≠ a_ekd → a ≠ a_ev1 → a ≠ a_ev2 →
      s_k.arrs a = s.arrs a)
  have hP_A0 : P_A 0 s₁ := by
    refine ⟨by simp [s₁, hr_kv], by simp [s₁, hr_ke],
      by simpa [s₁] using hwfV, by simpa [s₁] using hwfE,
      by simp [s₁], by simp [s₁], fun _ _ => rfl, fun _ _ => rfl,
      by simp [s₁]; exact hwfV.1, by simp [s₁]; exact hwfE.1,
      by simp [s₁, evalArena_zero], by simp [s₁, evalArena_zero],
      fun r hr _ _ => by simp [s₁, Nat.ne_of_lt hr, Nat.ne_of_lt (Nat.lt_trans hr (by decide : 10 < 11))],
      fun _ _ _ _ _ _ _ => rfl⟩
  rcases Exec.seqRange (w := w) (K := V_max δ ξ ω) (c := 45) P_A hP_A0
      (fun k hk s_k hs_k => by
        rcases hs_k with ⟨hkv_k, hke_k, hwfV_k, hwfE_k, hlenV_k, hlenE_k, hevV_k, hevE_k,
          hr10_k, hr11_k, hsetV_k, hsetE_k, hreg_k, harr_k⟩
        rcases tabsFoldACmd_exec (_EB := EB) (es_B := es_B) hbufA hw2 hS_w (by omega) (by omega)
            (by omega) (by omega) hr_kv0 hr_ke0 hwfV_k hwfE_k
            (by rw [hlenV_k]; omega) (by rw [hlenE_k]; omega)
            (fun p hp => (hevV_k p (Nat.lt_of_lt_of_le hp hkv0_le)).trans (hevalV0 p hp))
            (fun p hp => (hevE_k p (Nat.lt_of_lt_of_le hp hke0_le)).trans (hevalE0 p hp))
            ((harr_k a_acc_vv (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hacc_vv)
            ((harr_k a_acc_ve (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hacc_ve)
            hkv_k hke_k rfl rfl hr10_k hr11_k hsetV_k hsetE_k hk with
          ⟨s_next, t_step, hex_step, ht_step, hkv_n, hke_n, hr10_n, hr11_n,
           hwfV_n, hwfE_n, hlenV_n, hlenE_n, hevV_n, hevE_n, hsetV_n, hsetE_n, hreg_n, harr_n⟩
        refine ⟨s_next, t_step, hex_step, ht_step,
          by omega, by omega,
          by simpa [Nat.add_assoc] using hwfV_n,
          by simpa [Nat.add_assoc] using hwfE_n,
          hlenV_n.trans hlenV_k, hlenE_n.trans hlenE_k,
          fun p hp => (hevV_n p (by omega)).trans (hevV_k p hp),
          fun p hp => (hevE_n p (by omega)).trans (hevE_k p hp),
          by omega, by omega,
          by rw [hr10_n, hsetV_n, biUnion_range_succ],
          by rw [hr11_n, hsetE_n, biUnion_range_succ],
          fun r hr h1 h2 => (hreg_n r hr h1 h2).trans (hreg_k r hr h1 h2),
          fun a h1 h2 h3 h4 h5 h6 => (harr_n a h1 h2 h3 h4 h5 h6).trans (harr_k a h1 h2 h3 h4 h5 h6)⟩) with
    ⟨s₂, t_A, hex_A, ht_A, hP_A⟩
  -- Fold B over `u_B < V_max δ ξ ω`
  let SV_A := (Finset.range (V_max δ ξ ω)).biUnion
    (slotVertSetA (δ := δ) (ξ := ξ) (ω := ω) es_A es_B S_A S_B S_Z pos)
  let SE_A := (Finset.range (V_max δ ξ ω)).biUnion
    (slotEdgeSetA (δ := δ) (ξ := ξ) (ω := ω) es_A es_B S_A S_B S_Z pos)
  let P_B : ℕ → State → Prop := fun k s_k =>
    s_k.regs r_kv = kv + V_max δ ξ ω + k ∧ s_k.regs r_ke = ke + V_max δ ξ ω + k ∧
    ArenaWF G.numVerts (kv + V_max δ ξ ω + k) (s_k.arrs a_vkd) (s_k.arrs a_vv1) (s_k.arrs a_vv2) ∧
    ArenaWF G.numEdges (ke + V_max δ ξ ω + k) (s_k.arrs a_ekd) (s_k.arrs a_ev1) (s_k.arrs a_ev2) ∧
    (s_k.arrs a_vkd).length = (s.arrs a_vkd).length ∧
    (s_k.arrs a_ekd).length = (s.arrs a_ekd).length ∧
    (∀ p < kv,
      evalArena G.numVerts (s_k.arrs a_vkd) (s_k.arrs a_vv1) (s_k.arrs a_vv2) p =
        evalArena G.numVerts (s.arrs a_vkd) (s.arrs a_vv1) (s.arrs a_vv2) p) ∧
    (∀ p < ke,
      evalArena G.numEdges (s_k.arrs a_ekd) (s_k.arrs a_ev1) (s_k.arrs a_ev2) p =
        evalArena G.numEdges (s.arrs a_ekd) (s.arrs a_ev1) (s.arrs a_ev2) p) ∧
    s_k.regs 10 < kv + V_max δ ξ ω + k ∧ s_k.regs 11 < ke + V_max δ ξ ω + k ∧
    evalArena G.numVerts (s_k.arrs a_vkd) (s_k.arrs a_vv1) (s_k.arrs a_vv2) (s_k.regs 10) =
      SV_A ∪ (Finset.range k).biUnion (slotVertSetB (δ := δ) (ξ := ξ) (ω := ω) es_A es_B S_A S_B S_Z pos) ∧
    evalArena G.numEdges (s_k.arrs a_ekd) (s_k.arrs a_ev1) (s_k.arrs a_ev2) (s_k.regs 11) =
      SE_A ∪ (Finset.range k).biUnion (slotEdgeSetB (δ := δ) (ξ := ξ) (ω := ω) es_A es_B S_A S_B S_Z pos) ∧
    (∀ r < 10, r ≠ r_kv → r ≠ r_ke → s_k.regs r = s.regs r) ∧
    (∀ a, a ≠ a_vkd → a ≠ a_vv1 → a ≠ a_vv2 → a ≠ a_ekd → a ≠ a_ev1 → a ≠ a_ev2 →
      s_k.arrs a = s.arrs a)
  rcases hP_A with ⟨hkv_2, hke_2, hwfV_2, hwfE_2, hlenV_2, hlenE_2, hevV_2, hevE_2,
    hr10_2, hr11_2, hsetV_2, hsetE_2, hreg_2, harr_2⟩
  have hP_B0 : P_B 0 s₂ :=
    ⟨by omega, by omega, hwfV_2, hwfE_2, hlenV_2, hlenE_2, hevV_2, hevE_2,
     by omega, by omega,
     by simp [SV_A, hsetV_2], by simp [SE_A, hsetE_2], hreg_2, harr_2⟩
  rcases Exec.seqRange (w := w) (K := V_max δ ξ ω) (c := 45) P_B hP_B0
      (fun k hk s_k hs_k => by
        rcases hs_k with ⟨hkv_k, hke_k, hwfV_k, hwfE_k, hlenV_k, hlenE_k, hevV_k, hevE_k,
          hr10_k, hr11_k, hsetV_k, hsetE_k, hreg_k, harr_k⟩
        rcases tabsFoldBCmd_exec (_EA := EA) (es_A := es_A) hbufB hw2 hS_w (by omega) (by omega)
            (by omega) (by omega) hr_kv0 hr_ke0 hwfV_k hwfE_k
            (by rw [hlenV_k]; omega) (by rw [hlenE_k]; omega)
            (fun p hp => (hevV_k p (Nat.lt_of_lt_of_le hp hkv0_le)).trans (hevalV0 p hp))
            (fun p hp => (hevE_k p (Nat.lt_of_lt_of_le hp hke0_le)).trans (hevalE0 p hp))
            ((harr_k a_rhs_vv (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hrhs_vv)
            ((harr_k a_rhs_ve (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hrhs_ve)
            hkv_k hke_k rfl rfl hr10_k hr11_k hsetV_k hsetE_k hk with
          ⟨s_next, t_step, hex_step, ht_step, hkv_n, hke_n, hr10_n, hr11_n,
           hwfV_n, hwfE_n, hlenV_n, hlenE_n, hevV_n, hevE_n, hsetV_n, hsetE_n, hreg_n, harr_n⟩
        refine ⟨s_next, t_step, hex_step, ht_step,
          by omega, by omega,
          by simpa [Nat.add_assoc] using hwfV_n,
          by simpa [Nat.add_assoc] using hwfE_n,
          hlenV_n.trans hlenV_k, hlenE_n.trans hlenE_k,
          fun p hp => (hevV_n p (by omega)).trans (hevV_k p hp),
          fun p hp => (hevE_n p (by omega)).trans (hevE_k p hp),
          by omega, by omega,
          by rw [hr10_n, hsetV_n, biUnion_range_succ, Finset.union_assoc],
          by rw [hr11_n, hsetE_n, biUnion_range_succ, Finset.union_assoc],
          fun r hr h1 h2 => (hreg_n r hr h1 h2).trans (hreg_k r hr h1 h2),
          fun a h1 h2 h3 h4 h5 h6 => (harr_n a h1 h2 h3 h4 h5 h6).trans (harr_k a h1 h2 h3 h4 h5 h6)⟩) with
    ⟨s₃, t_B, hex_B, ht_B, hP_B⟩
  rcases hP_B with ⟨hkv_3, hke_3, hwfV_3, hwfE_3, hlenV_3, hlenE_3, hevV_3, hevE_3,
    hr10_3, hr11_3, hsetV_3, hsetE_3, hreg_3, harr_3⟩
  have hkv_eq : kv + V_max δ ξ ω + V_max δ ξ ω = kv' := by dsimp [kv']; omega
  have hke_eq : ke + V_max δ ξ ω + V_max δ ξ ω = ke' := by dsimp [ke']; omega
  rw [hkv_eq] at hkv_3 hwfV_3 hr10_3
  rw [hke_eq] at hke_3 hwfE_3 hr11_3
  have hout_vv_3 : s₃.arrs a_out_vv = s.arrs a_out_vv :=
    harr_3 a_out_vv (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  have hout_ve_3 : s₃.arrs a_out_ve = s.arrs a_out_ve :=
    harr_3 a_out_ve (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  have hout_em_3 : s₃.arrs a_out_em = s.arrs a_out_em :=
    harr_3 a_out_em (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  let s₄ := s₃.writeArr a_out_vv pos (s₃.regs 10)
  have hex_w1 : Exec w (.write a_out_vv (.const pos) (.reg 10)) s₃ s₄ 3 :=
    .write (by simp [Expr.eval, checkWord, hpos_w])
           (by simp [Expr.eval, checkWord, show s₃.regs 10 < 2 ^ w by omega])
           (by rw [hout_vv_3, hout_vv_len]; exact hpos)
  let s₅ := s₄.writeArr a_out_ve pos (s₃.regs 11)
  have hex_w2 : Exec w (.write a_out_ve (.const pos) (.reg 11)) s₄ s₅ 3 :=
    .write (by simp [Expr.eval, checkWord, hpos_w])
           (by simp [s₄, Expr.eval, checkWord, show s₃.regs 11 < 2 ^ w by omega])
           (by simp [s₄, hout_ve_3, hout_ve_len, hpos])
  rcases eval_tabsSlotEMExpr (w := w) (δ := δ) (ξ := ξ) (ω := ω) (pos := pos)
      (S_A := S_A) (S_B := S_B) (S_Z := S_Z) (s₀ := s₀) (s := s₅)
      hbufA hbufB h0_w hm_w hS_w
      (by simp [s₅, s₄, harr_3 a_acc_em (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), hacc_em])
      (by simp [s₅, s₄, harr_3 a_rhs_em (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), hrhs_em]) with
    ⟨he_em, hcost_em, hval_em_le⟩
  let e_em := tabsSlotEMExpr δ ξ ω tab_A tab_B q_U S_A S_B S_Z pos
  let val_em := slotTargetEM (δ := δ) (ξ := ξ) (ω := ω) es_A es_B S_A S_B S_Z pos
  let s' := s₅.writeArr a_out_em pos val_em
  have hex_w3 : Exec w (.write a_out_em (.const pos) e_em) s₅ s' (1 + e_em.cost + 1) :=
    .write (by simp [Expr.eval, checkWord, hpos_w]) he_em
           (by simp [s₅, s₄, hout_em_3, hout_em_len, hpos])
  have hget_vv : (s'.arrs a_out_vv).getD pos 0 = s₃.regs 10 := by
    simp only [s', s₅, s₄, State.writeArr_arrs_ne _ _ _ (by decide : a_out_vv ≠ a_out_em),
      State.writeArr_arrs_ne _ _ _ (by decide : a_out_vv ≠ a_out_ve),
      State.writeArr_arrs_self, hout_vv_3]
    rw [List.getD_eq_getElem?_getD, List.getElem?_set_self (by rw [hout_vv_len]; exact hpos),
        Option.getD_some]
  have hget_ve : (s'.arrs a_out_ve).getD pos 0 = s₃.regs 11 := by
    simp only [s', s₅, s₄, State.writeArr_arrs_ne _ _ _ (by decide : a_out_ve ≠ a_out_em),
      State.writeArr_arrs_self, State.writeArr_arrs_ne _ _ _ (by decide : a_out_ve ≠ a_out_vv),
      hout_ve_3]
    rw [List.getD_eq_getElem?_getD, List.getElem?_set_self (by rw [hout_ve_len]; exact hpos),
        Option.getD_some]
  have hget_em : (s'.arrs a_out_em).getD pos 0 = val_em := by
    simp only [s', s₅, s₄, State.writeArr_arrs_self,
      State.writeArr_arrs_ne _ _ _ (by decide : a_out_em ≠ a_out_ve),
      State.writeArr_arrs_ne _ _ _ (by decide : a_out_em ≠ a_out_vv), hout_em_3]
    rw [List.getD_eq_getElem?_getD, List.getElem?_set_self (by rw [hout_em_len]; exact hpos),
        Option.getD_some]
  refine ⟨s', 2 + (2 + (t_A + (t_B + (3 + (3 + (1 + e_em.cost + 1)))))),
    .seq hex₁ (.seq hex₂ (.seq hex_A (.seq hex_B (.seq hex_w1 (.seq hex_w2 hex_w3))))),
    by dsimp [e_em, tab_A, tab_B]; omega,
    by simp [s', s₅, s₄, hkv_3], by simp [s', s₅, s₄, hke_3],
    by simpa [s', s₅, s₄] using hwfV_3, by simpa [s', s₅, s₄] using hwfE_3,
    by simp [s', s₅, s₄, hlenV_3], by simp [s', s₅, s₄, hlenE_3],
    fun p hp => by
      have : evalArena G.numVerts (s'.arrs a_vkd) (s'.arrs a_vv1) (s'.arrs a_vv2) p =
          evalArena G.numVerts (s₃.arrs a_vkd) (s₃.arrs a_vv1) (s₃.arrs a_vv2) p := by
        simp [s', s₅, s₄]
      exact this.trans (hevV_3 p hp),
    fun p hp => by
      have : evalArena G.numEdges (s'.arrs a_ekd) (s'.arrs a_ev1) (s'.arrs a_ev2) p =
          evalArena G.numEdges (s₃.arrs a_ekd) (s₃.arrs a_ev1) (s₃.arrs a_ev2) p := by
        simp [s', s₅, s₄]
      exact this.trans (hevE_3 p hp),
    by simp [s', s₅, s₄, hout_vv_3, hout_vv_len],
    by simp [s', s₅, s₄, hout_ve_3, hout_ve_len],
    by simp [s', s₅, s₄, hout_em_3, hout_em_len],
    by rw [hget_vv]; exact hr10_3,
    by rw [hget_vv]; simpa [s', s₅, s₄, slotTargetVV, SV_A] using hsetV_3,
    by rw [hget_ve]; exact hr11_3,
    by rw [hget_ve]; simpa [s', s₅, s₄, slotTargetVE, SE_A] using hsetE_3,
    hget_em,
    by rw [hget_em]; exact hval_em_le,
    fun i hi => by
      have hne : pos ≠ i := by omega
      refine ⟨?_, ?_, ?_⟩
      · simp only [s', s₅, s₄, State.writeArr_arrs_ne _ _ _ (by decide : a_out_vv ≠ a_out_em),
          State.writeArr_arrs_ne _ _ _ (by decide : a_out_vv ≠ a_out_ve),
          State.writeArr_arrs_self, hout_vv_3]
        rw [List.getD_eq_getElem?_getD, List.getElem?_set_ne hne, ← List.getD_eq_getElem?_getD]
      · simp only [s', s₅, s₄, State.writeArr_arrs_ne _ _ _ (by decide : a_out_ve ≠ a_out_em),
          State.writeArr_arrs_self, State.writeArr_arrs_ne _ _ _ (by decide : a_out_ve ≠ a_out_vv),
          hout_ve_3]
        rw [List.getD_eq_getElem?_getD, List.getElem?_set_ne hne, ← List.getD_eq_getElem?_getD]
      · simp only [s', s₅, s₄, State.writeArr_arrs_self,
          State.writeArr_arrs_ne _ _ _ (by decide : a_out_em ≠ a_out_ve),
          State.writeArr_arrs_ne _ _ _ (by decide : a_out_em ≠ a_out_vv), hout_em_3]
        rw [List.getD_eq_getElem?_getD, List.getElem?_set_ne hne, ← List.getD_eq_getElem?_getD],
    fun r hr h1 h2 => by simp [s', s₅, s₄, hreg_3 r hr h1 h2],
    fun a h1 h2 h3 h4 h5 h6 h7 h8 h9 => by
      simp [s', s₅, s₄, h7, h8, h9, harr_3 a h1 h2 h3 h4 h5 h6]⟩

theorem tabsCombineBodyProg_exec {w δ ξ ω q_U kv₀ ke₀ : ℕ}
    {G : ComputeDigraph} {ZA ZB : Finset (Fin G.numVerts)}
    {EA EB : Finset (Fin G.numEdges)}
    {es_A : List (RawCertEntry G ZA.card)}
    {es_B : List (RawCertEntry G ZB.card)}
    {S_A S_B S_Z : Finset (Fin q_U)} (hSZ_le : S_Z.card ≤ Q_max ξ ω) {s₀ s_in : State}
    (hbufA : ValidPieceBuffer δ ξ ω G ZA EA es_A bufA s₀)
    (hbufB : ValidPieceBuffer δ ξ ω G ZB EB es_B bufB s₀)
    (hw2 : 2 < 2 ^ w) (hm_w : G.numEdges < 2 ^ w)
    (hS_w : S_tab δ ξ ω < 2 ^ w) (hT_w : T_max δ ξ ω < 2 ^ w)
    (hkv_w : kv₀ + K_comb δ ξ ω < 2 ^ w) (hke_w : ke₀ + K_comb δ ξ ω < 2 ^ w)
    (hr_kv0 : s₀.regs r_kv = kv₀) (hr_ke0 : s₀.regs r_ke = ke₀)
    (hr_kv : s_in.regs r_kv = kv₀) (hr_ke : s_in.regs r_ke = ke₀)
    (harr0 : ∀ a, a ≠ a_out_zV → a ≠ a_out_zI → s_in.arrs a = s₀.arrs a)
    (hwfV0 : ArenaWF G.numVerts kv₀ (s₀.arrs a_vkd) (s₀.arrs a_vv1) (s₀.arrs a_vv2))
    (hwfE0 : ArenaWF G.numEdges ke₀ (s₀.arrs a_ekd) (s₀.arrs a_ev1) (s₀.arrs a_ev2))
    (hkv_cap : kv₀ + K_comb δ ξ ω ≤ (s₀.arrs a_vkd).length)
    (hke_cap : ke₀ + K_comb δ ξ ω ≤ (s₀.arrs a_ekd).length)
    (hout_vv_len : (s₀.arrs a_out_vv).length = S_tab δ ξ ω)
    (hout_ve_len : (s₀.arrs a_out_ve).length = S_tab δ ξ ω)
    (hout_em_len : (s₀.arrs a_out_em).length = S_tab δ ξ ω) :
    let tab_A : AbstractTable := ⟨ZA.card, es_A.map RawCertEntry.H⟩
    let tab_B : AbstractTable := ⟨ZB.card, es_B.map RawCertEntry.H⟩
    let kv_f := kv₀ + K_comb δ ξ ω
    let ke_f := ke₀ + K_comb δ ξ ω
    ∃ s' t,
      Exec w (tabsCombineBodyProg δ ξ ω tab_A tab_B q_U S_A S_B S_Z) s_in s' t ∧
      t ≤ 3 + (20 + 90 * V_max δ ξ ω) * S_tab δ ξ ω ∧
      s'.regs r_tidA = tabsNewTid δ ξ ω tab_A tab_B q_U S_A S_B S_Z ∧
      s'.regs r_kv = kv_f ∧ s'.regs r_ke = ke_f ∧
      ArenaWF G.numVerts kv_f (s'.arrs a_vkd) (s'.arrs a_vv1) (s'.arrs a_vv2) ∧
      ArenaWF G.numEdges ke_f (s'.arrs a_ekd) (s'.arrs a_ev1) (s'.arrs a_ev2) ∧
      (s'.arrs a_vkd).length = (s₀.arrs a_vkd).length ∧
      (s'.arrs a_ekd).length = (s₀.arrs a_ekd).length ∧
      (∀ p < kv₀,
        evalArena G.numVerts (s'.arrs a_vkd) (s'.arrs a_vv1) (s'.arrs a_vv2) p =
          evalArena G.numVerts (s₀.arrs a_vkd) (s₀.arrs a_vv1) (s₀.arrs a_vv2) p) ∧
      (∀ p < ke₀,
        evalArena G.numEdges (s'.arrs a_ekd) (s'.arrs a_ev1) (s'.arrs a_ev2) p =
          evalArena G.numEdges (s₀.arrs a_ekd) (s₀.arrs a_ev1) (s₀.arrs a_ev2) p) ∧
      (s'.arrs a_out_vv).length = S_tab δ ξ ω ∧
      (s'.arrs a_out_ve).length = S_tab δ ξ ω ∧
      (s'.arrs a_out_em).length = S_tab δ ξ ω ∧
      (∀ pos < S_tab δ ξ ω,
        (s'.arrs a_out_vv).getD pos 0 < kv_f ∧
        evalArena G.numVerts (s'.arrs a_vkd) (s'.arrs a_vv1) (s'.arrs a_vv2)
          ((s'.arrs a_out_vv).getD pos 0) =
          slotTargetVV (δ := δ) (ξ := ξ) (ω := ω) es_A es_B S_A S_B S_Z pos ∧
        (s'.arrs a_out_ve).getD pos 0 < ke_f ∧
        evalArena G.numEdges (s'.arrs a_ekd) (s'.arrs a_ev1) (s'.arrs a_ev2)
          ((s'.arrs a_out_ve).getD pos 0) =
          slotTargetVE (δ := δ) (ξ := ξ) (ω := ω) es_A es_B S_A S_B S_Z pos ∧
        (s'.arrs a_out_em).getD pos 0 =
          slotTargetEM (δ := δ) (ξ := ξ) (ω := ω) es_A es_B S_A S_B S_Z pos ∧
        (s'.arrs a_out_em).getD pos 0 ≤ G.numEdges) ∧
      (∀ r < 10, r ≠ r_tidA → r ≠ r_kv → r ≠ r_ke → s'.regs r = s_in.regs r) ∧
      (∀ a, a ≠ a_vkd → a ≠ a_vv1 → a ≠ a_vv2 → a ≠ a_ekd → a ≠ a_ev1 → a ≠ a_ev2 →
        a ≠ a_out_vv → a ≠ a_out_ve → a ≠ a_out_em → s'.arrs a = s_in.arrs a) := by
  intro tab_A tab_B kv_f ke_f
  let tid_new := tabsNewTid δ ξ ω tab_A tab_B q_U S_A S_B S_Z
  have htid_lt : tid_new < T_max δ ξ ω := by
    refine encAbstractTable_lt δ ξ ω _ hSZ_le ?_
    simp only [List.length_map]
    exact length_combineRecipesOfTabs_le tab_A tab_B q_U S_A S_B S_Z
  have htid_w : tid_new < 2 ^ w := by omega
  let s₁ := s_in.setReg r_tidA tid_new
  have hex₁ : Exec w (.assign r_tidA (.const tid_new)) s_in s₁ 2 :=
    .assign (by simp [Expr.eval, checkWord, htid_w])
  have hvkd_in : s_in.arrs a_vkd = s₀.arrs a_vkd := harr0 a_vkd (by decide) (by decide)
  have hvv1_in : s_in.arrs a_vv1 = s₀.arrs a_vv1 := harr0 a_vv1 (by decide) (by decide)
  have hvv2_in : s_in.arrs a_vv2 = s₀.arrs a_vv2 := harr0 a_vv2 (by decide) (by decide)
  have hekd_in : s_in.arrs a_ekd = s₀.arrs a_ekd := harr0 a_ekd (by decide) (by decide)
  have hev1_in : s_in.arrs a_ev1 = s₀.arrs a_ev1 := harr0 a_ev1 (by decide) (by decide)
  have hev2_in : s_in.arrs a_ev2 = s₀.arrs a_ev2 := harr0 a_ev2 (by decide) (by decide)
  let P : ℕ → State → Prop := fun pos s =>
    let kv := kv₀ + 2 * V_max δ ξ ω * pos
    let ke := ke₀ + 2 * V_max δ ξ ω * pos
    s.regs r_tidA = tid_new ∧
    s.regs r_kv = kv ∧ s.regs r_ke = ke ∧
    ArenaWF G.numVerts kv (s.arrs a_vkd) (s.arrs a_vv1) (s.arrs a_vv2) ∧
    ArenaWF G.numEdges ke (s.arrs a_ekd) (s.arrs a_ev1) (s.arrs a_ev2) ∧
    (s.arrs a_vkd).length = (s₀.arrs a_vkd).length ∧
    (s.arrs a_ekd).length = (s₀.arrs a_ekd).length ∧
    (∀ p < kv₀,
      evalArena G.numVerts (s.arrs a_vkd) (s.arrs a_vv1) (s.arrs a_vv2) p =
        evalArena G.numVerts (s₀.arrs a_vkd) (s₀.arrs a_vv1) (s₀.arrs a_vv2) p) ∧
    (∀ p < ke₀,
      evalArena G.numEdges (s.arrs a_ekd) (s.arrs a_ev1) (s.arrs a_ev2) p =
        evalArena G.numEdges (s₀.arrs a_ekd) (s₀.arrs a_ev1) (s₀.arrs a_ev2) p) ∧
    (s.arrs a_out_vv).length = S_tab δ ξ ω ∧
    (s.arrs a_out_ve).length = S_tab δ ξ ω ∧
    (s.arrs a_out_em).length = S_tab δ ξ ω ∧
    (∀ i < pos,
      (s.arrs a_out_vv).getD i 0 < kv ∧
      evalArena G.numVerts (s.arrs a_vkd) (s.arrs a_vv1) (s.arrs a_vv2)
        ((s.arrs a_out_vv).getD i 0) =
        slotTargetVV (δ := δ) (ξ := ξ) (ω := ω) es_A es_B S_A S_B S_Z i ∧
      (s.arrs a_out_ve).getD i 0 < ke ∧
      evalArena G.numEdges (s.arrs a_ekd) (s.arrs a_ev1) (s.arrs a_ev2)
        ((s.arrs a_out_ve).getD i 0) =
        slotTargetVE (δ := δ) (ξ := ξ) (ω := ω) es_A es_B S_A S_B S_Z i ∧
      (s.arrs a_out_em).getD i 0 =
        slotTargetEM (δ := δ) (ξ := ξ) (ω := ω) es_A es_B S_A S_B S_Z i ∧
      (s.arrs a_out_em).getD i 0 ≤ G.numEdges) ∧
    (∀ r < 10, r ≠ r_tidA → r ≠ r_kv → r ≠ r_ke → s.regs r = s_in.regs r) ∧
    (∀ a, a ≠ a_vkd → a ≠ a_vv1 → a ≠ a_vv2 → a ≠ a_ekd → a ≠ a_ev1 → a ≠ a_ev2 →
      a ≠ a_out_vv → a ≠ a_out_ve → a ≠ a_out_em → s.arrs a = s_in.arrs a)
  have hP0 : P 0 s₁ := by
    refine ⟨by simp [s₁], by simp [s₁, hr_kv], by simp [s₁, hr_ke],
      by simpa [s₁, hvkd_in, hvv1_in, hvv2_in] using hwfV0,
      by simpa [s₁, hekd_in, hev1_in, hev2_in] using hwfE0,
      by simp [s₁, hvkd_in], by simp [s₁, hekd_in],
      fun p _ => by simp [s₁, hvkd_in, hvv1_in, hvv2_in],
      fun p _ => by simp [s₁, hekd_in, hev1_in, hev2_in],
      by simp [s₁, harr0 a_out_vv (by decide) (by decide), hout_vv_len],
      by simp [s₁, harr0 a_out_ve (by decide) (by decide), hout_ve_len],
      by simp [s₁, harr0 a_out_em (by decide) (by decide), hout_em_len],
      fun _ h => by omega,
      fun r _ h1 _ _ => by simp [s₁, h1],
      fun _ _ _ _ _ _ _ _ _ _ => rfl⟩
  rcases Exec.seqRange (w := w) (K := S_tab δ ξ ω) (c := 20 + 90 * V_max δ ξ ω) P hP0
      (fun pos hpos s hs => by
        rcases hs with ⟨htid_s, hkv_s, hke_s, hwfV_s, hwfE_s, hlenV_s, hlenE_s,
          hevV_s, hevE_s, hout_vv_s, hout_ve_s, hout_em_s, hprev_s, hreg_s, harr_s⟩
        have hmul_le : 2 * V_max δ ξ ω * (pos + 1) ≤ K_comb δ ξ ω := by
          unfold K_comb
          exact Nat.mul_le_mul_left (2 * V_max δ ξ ω) hpos
        have hstep_eq :
            kv₀ + 2 * V_max δ ξ ω * pos + 2 * V_max δ ξ ω =
              kv₀ + 2 * V_max δ ξ ω * (pos + 1) := by
          rw [Nat.mul_succ, Nat.add_assoc]
        have hstepE_eq :
            ke₀ + 2 * V_max δ ξ ω * pos + 2 * V_max δ ξ ω =
              ke₀ + 2 * V_max δ ξ ω * (pos + 1) := by
          rw [Nat.mul_succ, Nat.add_assoc]
        rcases tabsSlotProg_exec (S_A := S_A) (S_B := S_B) (S_Z := S_Z) (pos := pos)
            hbufA hbufB hw2 hm_w hS_w (by omega) (by omega)
            (Nat.le_add_right _ _) (Nat.le_add_right _ _) hr_kv0 hr_ke0
            hwfV_s hwfE_s (by rw [hlenV_s]; omega) (by rw [hlenE_s]; omega)
            hevV_s hevE_s
            ((harr_s a_acc_vv (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans
              (harr0 a_acc_vv (by decide) (by decide)))
            ((harr_s a_acc_ve (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans
              (harr0 a_acc_ve (by decide) (by decide)))
            ((harr_s a_acc_em (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans
              (harr0 a_acc_em (by decide) (by decide)))
            ((harr_s a_rhs_vv (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans
              (harr0 a_rhs_vv (by decide) (by decide)))
            ((harr_s a_rhs_ve (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans
              (harr0 a_rhs_ve (by decide) (by decide)))
            ((harr_s a_rhs_em (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans
              (harr0 a_rhs_em (by decide) (by decide)))
            hkv_s hke_s hpos hout_vv_s hout_ve_s hout_em_s with
          ⟨s_next, t_slot, hex_slot, ht_slot, hkv_n, hke_n, hwfV_n, hwfE_n,
           hlenV_n, hlenE_n, hevV_n, hevE_n, hout_vv_n, hout_ve_n, hout_em_n,
           hvv_pos_lt, hvv_pos_ev, hve_pos_lt, hve_pos_ev, hem_pos_eq, hem_pos_le,
           hprev_n, hreg_n, harr_n⟩
        refine ⟨s_next, t_slot, hex_slot, ht_slot,
          (hreg_n r_tidA (by decide) (by decide) (by decide)).trans htid_s,
          by omega, by omega,
          by simpa [hstep_eq] using hwfV_n,
          by simpa [hstepE_eq] using hwfE_n,
          hlenV_n.trans hlenV_s, hlenE_n.trans hlenE_s,
          fun p hp => (hevV_n p (Nat.lt_of_lt_of_le hp (Nat.le_add_right _ _))).trans (hevV_s p hp),
          fun p hp => (hevE_n p (Nat.lt_of_lt_of_le hp (Nat.le_add_right _ _))).trans (hevE_s p hp),
          hout_vv_n, hout_ve_n, hout_em_n,
          fun i hi => by
            by_cases hip : i = pos
            · subst hip
              exact ⟨by omega, hvv_pos_ev, by omega, hve_pos_ev, hem_pos_eq, hem_pos_le⟩
            · have hi_lt : i < pos := by omega
              rcases hprev_n i hi_lt with ⟨h1, h2, h3⟩
              rcases hprev_s i hi_lt with ⟨hp1, hp2, hp3, hp4, hp5, hp6⟩
              exact ⟨by rw [h1]; omega,
                by rw [h1, hevV_n _ hp1, hp2],
                by rw [h2]; omega,
                by rw [h2, hevE_n _ hp3, hp4],
                by rw [h3, hp5],
                by rw [h3]; exact hp6⟩,
          fun r hr h1 h2 h3 => (hreg_n r hr h2 h3).trans (hreg_s r hr h1 h2 h3),
          fun a h1 h2 h3 h4 h5 h6 h7 h8 h9 =>
            (harr_n a h1 h2 h3 h4 h5 h6 h7 h8 h9).trans (harr_s a h1 h2 h3 h4 h5 h6 h7 h8 h9)⟩) with
    ⟨s', t_loop, hex_loop, ht_loop, hP_f⟩
  rcases hP_f with ⟨htid_f, hkv_f, hke_f, hwfV_f, hwfE_f, hlenV_f, hlenE_f,
    hevV_f, hevE_f, hout_vv_f, hout_ve_f, hout_em_f, hslots_f, hreg_f, harr_f⟩
  exact ⟨s', 2 + t_loop, .seq hex₁ hex_loop, by omega,
    htid_f, hkv_f, hke_f, hwfV_f, hwfE_f, hlenV_f, hlenE_f, hevV_f, hevE_f,
    hout_vv_f, hout_ve_f, hout_em_f, hslots_f, hreg_f, harr_f⟩

theorem canonCombineBodyProg_eq_tabsCombineBodyProg {δ ξ ω : ℕ} {G : ComputeDigraph}
    {ZA ZB Z' : Finset (Fin G.numVerts)}
    {EA EB : Finset (Fin G.numEdges)}
    {es_A : List (RawCertEntry G ZA.card)}
    {es_B : List (RawCertEntry G ZB.card)}
    {s₀ : State}
    (hbufA : ValidPieceBuffer δ ξ ω G ZA EA es_A bufA s₀)
    (hbufB : ValidPieceBuffer δ ξ ω G ZB EB es_B bufB s₀)
    (hqU : (ZA ∪ ZB).card ≤ Q_max ξ ω)
    {tid_A tid_B mcode : ℕ}
    (htidA : tid_A = encAbstractTable δ ξ ω ⟨ZA.card, es_A.map RawCertEntry.H⟩)
    (htidB : tid_B = encAbstractTable δ ξ ω ⟨ZB.card, es_B.map RawCertEntry.H⟩)
    (hmcode : mcode = encBoundaryMask ZA ZB Z') :
    canonCombineBodyProg δ ξ ω tid_A tid_B mcode =
      tabsCombineBodyProg δ ξ ω
        ⟨ZA.card, es_A.map RawCertEntry.H⟩
        ⟨ZB.card, es_B.map RawCertEntry.H⟩
        (ZA ∪ ZB).card
        (subMaskFinset (ZA ∪ ZB) ZA)
        (subMaskFinset (ZA ∪ ZB) ZB)
        (subMaskFinset (ZA ∪ ZB) Z') := by
  subst htidA htidB hmcode
  have hdecA := decAbstractTable_encAbstractTable δ ξ ω ⟨ZA.card, es_A.map RawCertEntry.H⟩
    hbufA.hq_le (by simp [hbufA.hlen_le])
    (by intro H hH; rcases List.mem_map.mp hH with ⟨e, he, rfl⟩; exact hbufA.hdet e he)
  have hdecB := decAbstractTable_encAbstractTable δ ξ ω ⟨ZB.card, es_B.map RawCertEntry.H⟩
    hbufB.hq_le (by simp [hbufB.hlen_le])
    (by intro H hH; rcases List.mem_map.mp hH with ⟨e, he, rfl⟩; exact hbufB.hdet e he)
  rcases mem_canonMaskSub_encBoundaryMask ZA ZB Z' hqU with ⟨hSA, hSB, hSZ⟩
  exact tabsFn_congr (tabsCombineBodyProg δ ξ ω) hdecA hdecB
    (canonMaskCardU_encBoundaryMask ZA ZB Z' hqU) hSA hSB hSZ

theorem combineDispatchProg_exec {w δ ξ ω kv₀ ke₀ : ℕ}
    {G : ComputeDigraph} {ZA ZB Z' : Finset (Fin G.numVerts)}
    {EA EB : Finset (Fin G.numEdges)}
    {es_A : List (RawCertEntry G ZA.card)}
    {es_B : List (RawCertEntry G ZB.card)}
    (hqU : (ZA ∪ ZB).card ≤ Q_max ξ ω)
    (hZ'_sub : Z' ⊆ ZA ∪ ZB)
    {s₀ s_in : State}
    (hbufA : ValidPieceBuffer δ ξ ω G ZA EA es_A bufA s₀)
    (hbufB : ValidPieceBuffer δ ξ ω G ZB EB es_B bufB s₀)
    (hw2 : 2 < 2 ^ w) (hm_w : G.numEdges < 2 ^ w)
    (hS_w : S_tab δ ξ ω < 2 ^ w) (hT_w : T_max δ ξ ω < 2 ^ w) (hM_w : M_max ξ ω < 2 ^ w)
    (hkv_w : kv₀ + K_comb δ ξ ω < 2 ^ w) (hke_w : ke₀ + K_comb δ ξ ω < 2 ^ w)
    (hr_kv0 : s₀.regs r_kv = kv₀) (hr_ke0 : s₀.regs r_ke = ke₀)
    (hr_kv : s_in.regs r_kv = kv₀) (hr_ke : s_in.regs r_ke = ke₀)
    (hr_tidA_in : s_in.regs r_tidA = s₀.regs r_tidA)
    (hr_tidB_in : s_in.regs r_tidB = s₀.regs r_tidB)
    (hr13_in : s_in.regs 13 = encBoundaryMask ZA ZB Z')
    (harr0 : ∀ a, a ≠ a_out_zV → a ≠ a_out_zI → s_in.arrs a = s₀.arrs a)
    (hwfV0 : ArenaWF G.numVerts kv₀ (s₀.arrs a_vkd) (s₀.arrs a_vv1) (s₀.arrs a_vv2))
    (hwfE0 : ArenaWF G.numEdges ke₀ (s₀.arrs a_ekd) (s₀.arrs a_ev1) (s₀.arrs a_ev2))
    (hkv_cap : kv₀ + K_comb δ ξ ω ≤ (s₀.arrs a_vkd).length)
    (hke_cap : ke₀ + K_comb δ ξ ω ≤ (s₀.arrs a_ekd).length)
    (hout_vv_len : (s₀.arrs a_out_vv).length = S_tab δ ξ ω)
    (hout_ve_len : (s₀.arrs a_out_ve).length = S_tab δ ξ ω)
    (hout_em_len : (s₀.arrs a_out_em).length = S_tab δ ξ ω) :
    let U := ZA ∪ ZB
    let S_A := subMaskFinset U ZA
    let S_B := subMaskFinset U ZB
    let S_Z := subMaskFinset U Z'
    let tab_A : AbstractTable := ⟨ZA.card, es_A.map RawCertEntry.H⟩
    let tab_B : AbstractTable := ⟨ZB.card, es_B.map RawCertEntry.H⟩
    let kv_f := kv₀ + K_comb δ ξ ω
    let ke_f := ke₀ + K_comb δ ξ ω
    ∃ s' t,
      Exec w (combineDispatchProg δ ξ ω) s_in s' t ∧
      t ≤ 6 * T_max δ ξ ω + 3 * M_max ξ ω + 3 + (20 + 90 * V_max δ ξ ω) * S_tab δ ξ ω ∧
      s'.regs r_tidA = tabsNewTid δ ξ ω tab_A tab_B U.card S_A S_B S_Z ∧
      s'.regs r_kv = kv_f ∧ s'.regs r_ke = ke_f ∧
      ArenaWF G.numVerts kv_f (s'.arrs a_vkd) (s'.arrs a_vv1) (s'.arrs a_vv2) ∧
      ArenaWF G.numEdges ke_f (s'.arrs a_ekd) (s'.arrs a_ev1) (s'.arrs a_ev2) ∧
      (s'.arrs a_vkd).length = (s₀.arrs a_vkd).length ∧
      (s'.arrs a_ekd).length = (s₀.arrs a_ekd).length ∧
      (∀ p < kv₀,
        evalArena G.numVerts (s'.arrs a_vkd) (s'.arrs a_vv1) (s'.arrs a_vv2) p =
          evalArena G.numVerts (s₀.arrs a_vkd) (s₀.arrs a_vv1) (s₀.arrs a_vv2) p) ∧
      (∀ p < ke₀,
        evalArena G.numEdges (s'.arrs a_ekd) (s'.arrs a_ev1) (s'.arrs a_ev2) p =
          evalArena G.numEdges (s₀.arrs a_ekd) (s₀.arrs a_ev1) (s₀.arrs a_ev2) p) ∧
      (s'.arrs a_out_vv).length = S_tab δ ξ ω ∧
      (s'.arrs a_out_ve).length = S_tab δ ξ ω ∧
      (s'.arrs a_out_em).length = S_tab δ ξ ω ∧
      (∀ pos < S_tab δ ξ ω,
        (s'.arrs a_out_vv).getD pos 0 < kv_f ∧
        evalArena G.numVerts (s'.arrs a_vkd) (s'.arrs a_vv1) (s'.arrs a_vv2)
          ((s'.arrs a_out_vv).getD pos 0) =
          slotTargetVV (δ := δ) (ξ := ξ) (ω := ω) es_A es_B S_A S_B S_Z pos ∧
        (s'.arrs a_out_ve).getD pos 0 < ke_f ∧
        evalArena G.numEdges (s'.arrs a_ekd) (s'.arrs a_ev1) (s'.arrs a_ev2)
          ((s'.arrs a_out_ve).getD pos 0) =
          slotTargetVE (δ := δ) (ξ := ξ) (ω := ω) es_A es_B S_A S_B S_Z pos ∧
        (s'.arrs a_out_em).getD pos 0 =
          slotTargetEM (δ := δ) (ξ := ξ) (ω := ω) es_A es_B S_A S_B S_Z pos ∧
        (s'.arrs a_out_em).getD pos 0 ≤ G.numEdges) ∧
      (∀ r < 10, r ≠ r_tidA → r ≠ r_kv → r ≠ r_ke → s'.regs r = s_in.regs r) ∧
      (∀ a, a ≠ a_vkd → a ≠ a_vv1 → a ≠ a_vv2 → a ≠ a_ekd → a ≠ a_ev1 → a ≠ a_ev2 →
        a ≠ a_out_vv → a ≠ a_out_ve → a ≠ a_out_em → s'.arrs a = s_in.arrs a) := by
  intro U S_A S_B S_Z tab_A tab_B kv_f ke_f
  have hw_pos : 0 < w := by by_contra h0; obtain rfl : w = 0 := (by omega); simp at hw2
  have hSZ_le : S_Z.card ≤ Q_max ξ ω := by
    rw [card_subMaskFinset hZ'_sub]
    exact le_trans (Finset.card_le_card hZ'_sub) hqU
  rcases tabsCombineBodyProg_exec (S_A := S_A) (S_B := S_B) (S_Z := S_Z) hSZ_le
      hbufA hbufB hw2 hm_w hS_w hT_w hkv_w hke_w hr_kv0 hr_ke0 hr_kv hr_ke harr0
      hwfV0 hwfE0 hkv_cap hke_cap hout_vv_len hout_ve_len hout_em_len with
    ⟨s', t_body, hex_body, ht_body, htid_f, hkv_f, hke_f, hwfV_f, hwfE_f,
     hlenV_f, hlenE_f, hevV_f, hevE_f, hout_vv_f, hout_ve_f, hout_em_f,
     hslots_f, hreg_f, harr_f⟩
  let tid_A := s₀.regs r_tidA
  let tid_B := s₀.regs r_tidB
  let mcode := encBoundaryMask ZA ZB Z'
  have htidA_eq : tid_A = encAbstractTable δ ξ ω tab_A := hbufA.htid
  have htidB_eq : tid_B = encAbstractTable δ ξ ω tab_B := hbufB.htid
  have htidA_lt : tid_A < T_max δ ξ ω := by
    rw [htidA_eq]; exact encAbstractTable_lt δ ξ ω tab_A hbufA.hq_le (by simp [tab_A, hbufA.hlen_le])
  have htidB_lt : tid_B < T_max δ ξ ω := by
    rw [htidB_eq]; exact encAbstractTable_lt δ ξ ω tab_B hbufB.hq_le (by simp [tab_B, hbufB.hlen_le])
  have hmcode_lt : mcode < M_max ξ ω := encBoundaryMask_lt ZA ZB Z' hqU
  have hcmd_eq : canonCombineBodyProg δ ξ ω tid_A tid_B mcode =
      tabsCombineBodyProg δ ξ ω tab_A tab_B U.card S_A S_B S_Z :=
    canonCombineBodyProg_eq_tabsCombineBodyProg hbufA hbufB hqU htidA_eq htidB_eq rfl
  rw [← hcmd_eq] at hex_body
  rcases Exec.branchOnBound (body := canonCombineBodyProg δ ξ ω tid_A tid_B) (r_in := 13)
      hw_pos hM_w hr13_in hmcode_lt hex_body with
    ⟨t₁, ht₁, hex₁⟩
  rcases Exec.branchOnBound
      (body := fun b => branchOnBound (M_max ξ ω) 13 (canonCombineBodyProg δ ξ ω tid_A b))
      (r_in := r_tidB) hw_pos hT_w hr_tidB_in htidB_lt hex₁ with
    ⟨t₂, ht₂, hex₂⟩
  rcases Exec.branchOnBound
      (body := fun a => branchOnBound (T_max δ ξ ω) r_tidB
        (fun b => branchOnBound (M_max ξ ω) 13 (canonCombineBodyProg δ ξ ω a b)))
      (r_in := r_tidA) hw_pos hT_w hr_tidA_in htidA_lt hex₂ with
    ⟨t₃, ht₃, hex₃⟩
  exact ⟨s', t₃, hex₃, by omega,
    htid_f, hkv_f, hke_f, hwfV_f, hwfE_f, hlenV_f, hlenE_f, hevV_f, hevE_f,
    hout_vv_f, hout_ve_f, hout_em_f, hslots_f, hreg_f, harr_f⟩

/-! ### Section 2: Execution of `copyOutToAccProg` and `combineStepProg` -/

theorem subInc_le_numEdges (G : ComputeDigraph) (E : Finset (Fin G.numEdges))
    (v : Fin G.numVerts) : subInc G E v ≤ G.numEdges := by
  calc subInc G E v
      ≤ (Finset.univ : Finset (Fin G.numEdges)).card :=
        Finset.card_le_card (Finset.subset_univ _)
    _ = G.numEdges := Finset.card_fin G.numEdges

theorem copyOutToAccProg_exec {w δ ξ ω kv ke : ℕ} {G : ComputeDigraph} {s₀ : State}
    (hQ_w : Q_max ξ ω < 2 ^ w) (hS_w : S_tab δ ξ ω < 2 ^ w)
    (hn_w : G.numVerts < 2 ^ w) (hm_w : G.numEdges < 2 ^ w)
    (hkv_w : kv < 2 ^ w) (hke_w : ke < 2 ^ w)
    (hr0 : s₀.regs 0 = G.numVerts) (hr1 : s₀.regs 1 = G.numEdges)
    (hr_kv : s₀.regs r_kv = kv) (hr_ke : s₀.regs r_ke = ke)
    (hout_zV : (s₀.arrs a_out_zV).length = Q_max ξ ω)
    (hout_zI : (s₀.arrs a_out_zI).length = Q_max ξ ω)
    (hout_vv : (s₀.arrs a_out_vv).length = S_tab δ ξ ω)
    (hout_ve : (s₀.arrs a_out_ve).length = S_tab δ ξ ω)
    (hout_em : (s₀.arrs a_out_em).length = S_tab δ ξ ω)
    (hacc_zV : (s₀.arrs a_acc_zV).length = Q_max ξ ω)
    (hacc_zI : (s₀.arrs a_acc_zI).length = Q_max ξ ω)
    (hacc_vv : (s₀.arrs a_acc_vv).length = S_tab δ ξ ω)
    (hacc_ve : (s₀.arrs a_acc_ve).length = S_tab δ ξ ω)
    (hacc_em : (s₀.arrs a_acc_em).length = S_tab δ ξ ω) :
    ∃ s' t,
      Exec w (copyOutToAccProg δ ξ ω) s₀ s' t ∧
      t ≤ 5 + 12 * Q_max ξ ω + 18 * S_tab δ ξ ω ∧
      (s'.arrs a_acc_zV).length = Q_max ξ ω ∧
      (s'.arrs a_acc_zI).length = Q_max ξ ω ∧
      (s'.arrs a_acc_vv).length = S_tab δ ξ ω ∧
      (s'.arrs a_acc_ve).length = S_tab δ ξ ω ∧
      (s'.arrs a_acc_em).length = S_tab δ ξ ω ∧
      (∀ i < Q_max ξ ω,
        (s'.arrs a_acc_zV).getD i 0 = Nat.min ((s₀.arrs a_out_zV).getD i 0) G.numVerts ∧
        (s'.arrs a_acc_zI).getD i 0 = Nat.min ((s₀.arrs a_out_zI).getD i 0) G.numEdges) ∧
      (∀ pos < S_tab δ ξ ω,
        (s'.arrs a_acc_vv).getD pos 0 = Nat.min ((s₀.arrs a_out_vv).getD pos 0) kv ∧
        (s'.arrs a_acc_ve).getD pos 0 = Nat.min ((s₀.arrs a_out_ve).getD pos 0) ke ∧
        (s'.arrs a_acc_em).getD pos 0 = Nat.min ((s₀.arrs a_out_em).getD pos 0) G.numEdges) ∧
      (∀ r, s'.regs r = s₀.regs r) ∧
      (∀ a, a ≠ a_acc_zV → a ≠ a_acc_zI → a ≠ a_acc_vv → a ≠ a_acc_ve → a ≠ a_acc_em →
        s'.arrs a = s₀.arrs a) := by
  rcases copyFixedArrMinProg_exec (a_src := a_out_zV) (a_dst := a_acc_zV) (r_cap := 0)
      (by decide) hQ_w hn_w hr0 hout_zV hacc_zV with
    ⟨s₁, t₁, hex₁, ht₁, hlen₁, hget₁, harr₁, hreg₁⟩
  rcases copyFixedArrMinProg_exec (a_src := a_out_zI) (a_dst := a_acc_zI) (r_cap := 1) (s₀ := s₁)
      (by decide) hQ_w hm_w ((hreg₁ 1).trans hr1)
      ((congrArg List.length (harr₁ a_out_zI (by decide))).trans hout_zI)
      ((congrArg List.length (harr₁ a_acc_zI (by decide))).trans hacc_zI) with
    ⟨s₂, t₂, hex₂, ht₂, hlen₂, hget₂, harr₂, hreg₂⟩
  rcases copyFixedArrMinProg_exec (a_src := a_out_vv) (a_dst := a_acc_vv) (r_cap := r_kv) (s₀ := s₂)
      (by decide) hS_w hkv_w ((hreg₂ r_kv).trans ((hreg₁ r_kv).trans hr_kv))
      ((congrArg List.length ((harr₂ a_out_vv (by decide)).trans (harr₁ a_out_vv (by decide)))).trans hout_vv)
      ((congrArg List.length ((harr₂ a_acc_vv (by decide)).trans (harr₁ a_acc_vv (by decide)))).trans hacc_vv) with
    ⟨s₃, t₃, hex₃, ht₃, hlen₃, hget₃, harr₃, hreg₃⟩
  rcases copyFixedArrMinProg_exec (a_src := a_out_ve) (a_dst := a_acc_ve) (r_cap := r_ke) (s₀ := s₃)
      (by decide) hS_w hke_w ((hreg₃ r_ke).trans ((hreg₂ r_ke).trans ((hreg₁ r_ke).trans hr_ke)))
      ((congrArg List.length ((harr₃ a_out_ve (by decide)).trans
        ((harr₂ a_out_ve (by decide)).trans (harr₁ a_out_ve (by decide))))).trans hout_ve)
      ((congrArg List.length ((harr₃ a_acc_ve (by decide)).trans
        ((harr₂ a_acc_ve (by decide)).trans (harr₁ a_acc_ve (by decide))))).trans hacc_ve) with
    ⟨s₄, t₄, hex₄, ht₄, hlen₄, hget₄, harr₄, hreg₄⟩
  rcases copyFixedArrMinProg_exec (a_src := a_out_em) (a_dst := a_acc_em) (r_cap := 1) (s₀ := s₄)
      (by decide) hS_w hm_w
      ((hreg₄ 1).trans ((hreg₃ 1).trans ((hreg₂ 1).trans ((hreg₁ 1).trans hr1))))
      ((congrArg List.length ((harr₄ a_out_em (by decide)).trans ((harr₃ a_out_em (by decide)).trans
        ((harr₂ a_out_em (by decide)).trans (harr₁ a_out_em (by decide)))))).trans hout_em)
      ((congrArg List.length ((harr₄ a_acc_em (by decide)).trans ((harr₃ a_acc_em (by decide)).trans
        ((harr₂ a_acc_em (by decide)).trans (harr₁ a_acc_em (by decide)))))).trans hacc_em) with
    ⟨s₅, t₅, hex₅, ht₅, hlen₅, hget₅, harr₅, hreg₅⟩
  have hzV_5 : s₅.arrs a_acc_zV = s₁.arrs a_acc_zV :=
    (harr₅ a_acc_zV (by decide)).trans ((harr₄ a_acc_zV (by decide)).trans
      ((harr₃ a_acc_zV (by decide)).trans (harr₂ a_acc_zV (by decide))))
  have hzI_5 : s₅.arrs a_acc_zI = s₂.arrs a_acc_zI :=
    (harr₅ a_acc_zI (by decide)).trans ((harr₄ a_acc_zI (by decide)).trans
      (harr₃ a_acc_zI (by decide)))
  have hvv_5 : s₅.arrs a_acc_vv = s₃.arrs a_acc_vv :=
    (harr₅ a_acc_vv (by decide)).trans (harr₄ a_acc_vv (by decide))
  have hve_5 : s₅.arrs a_acc_ve = s₄.arrs a_acc_ve := harr₅ a_acc_ve (by decide)
  refine ⟨s₅, t₁ + (t₂ + (t₃ + (t₄ + t₅))),
    .seq hex₁ (.seq hex₂ (.seq hex₃ (.seq hex₄ hex₅))),
    by omega,
    by rw [hzV_5, hlen₁], by rw [hzI_5, hlen₂],
    by rw [hvv_5, hlen₃], by rw [hve_5, hlen₄], hlen₅,
    fun i hi => ⟨by rw [hzV_5, hget₁ i hi],
      by rw [hzI_5, hget₂ i hi, harr₁ a_out_zI (by decide)]⟩,
    fun pos hpos => ⟨by rw [hvv_5, hget₃ pos hpos, harr₂ a_out_vv (by decide), harr₁ a_out_vv (by decide)],
      by rw [hve_5, hget₄ pos hpos, harr₃ a_out_ve (by decide), harr₂ a_out_ve (by decide), harr₁ a_out_ve (by decide)],
      by rw [hget₅ pos hpos, harr₄ a_out_em (by decide), harr₃ a_out_em (by decide),
             harr₂ a_out_em (by decide), harr₁ a_out_em (by decide)]⟩,
    fun r => (hreg₅ r).trans ((hreg₄ r).trans ((hreg₃ r).trans ((hreg₂ r).trans (hreg₁ r)))),
    fun a h1 h2 h3 h4 h5 =>
      (harr₅ a h5).trans ((harr₄ a h4).trans ((harr₃ a h3).trans ((harr₂ a h2).trans (harr₁ a h1))))⟩

/-- Time bound for one execution of `combineStepProg δ ξ ω`. -/
def C_combineStep (δ ξ ω : ℕ) : ℕ :=
  30 + 107 * Q_max ξ ω + 6 * T_max δ ξ ω + 3 * M_max ξ ω + 18 * S_tab δ ξ ω +
    (20 + 90 * V_max δ ξ ω) * S_tab δ ξ ω

theorem combineStepProg_exec {w δ ξ ω kv₀ ke₀ : ℕ}
    {G : ComputeDigraph} {Z ZA ZB Z' : Finset (Fin G.numVerts)}
    {EA EB : Finset (Fin G.numEdges)}
    {es_A : List (RawCertEntry G ZA.card)}
    {es_B : List (RawCertEntry G ZB.card)}
    (hqU : (ZA ∪ ZB).card ≤ Q_max ξ ω)
    (hinc_union : ∀ u ∈ ZA ∪ ZB,
      subInc G (EA ∪ EB) u =
        (if u ∈ ZA then subInc G EA u else 0) + (if u ∈ ZB then subInc G EB u else 0))
    (hZ'_iff : ∀ u : Fin G.numVerts,
      u ∈ Z' ↔ u ∈ ZA ∪ ZB ∧ subInc G (EA ∪ EB) u < capVal G Z u)
    {s₀ : State}
    (hbufA : ValidPieceBuffer δ ξ ω G ZA EA es_A bufA s₀)
    (hbufB : ValidPieceBuffer δ ξ ω G ZB EB es_B bufB s₀)
    (hw8 : 8 < 2 ^ w) (hn_w : G.numVerts < 2 ^ w) (hm1_w : G.numEdges + 1 < 2 ^ w)
    (hQ_w : Q_max ξ ω < 2 ^ w) (hS_w : S_tab δ ξ ω < 2 ^ w)
    (hT_w : T_max δ ξ ω < 2 ^ w) (hM_w : M_max ξ ω < 2 ^ w)
    (hkv_w : kv₀ + K_comb δ ξ ω < 2 ^ w) (hke_w : ke₀ + K_comb δ ξ ω < 2 ^ w)
    (hr0 : s₀.regs 0 = G.numVerts) (hr1 : s₀.regs 1 = G.numEdges)
    (hr_kv0 : s₀.regs r_kv = kv₀) (hr_ke0 : s₀.regs r_ke = ke₀)
    (hcap : s₀.arrs a_cap = List.ofFn (capVal G Z))
    (hwfV0 : ArenaWF G.numVerts kv₀ (s₀.arrs a_vkd) (s₀.arrs a_vv1) (s₀.arrs a_vv2))
    (hwfE0 : ArenaWF G.numEdges ke₀ (s₀.arrs a_ekd) (s₀.arrs a_ev1) (s₀.arrs a_ev2))
    (hkv_cap : kv₀ + K_comb δ ξ ω ≤ (s₀.arrs a_vkd).length)
    (hke_cap : ke₀ + K_comb δ ξ ω ≤ (s₀.arrs a_ekd).length)
    (hout_zV : (s₀.arrs a_out_zV).length = Q_max ξ ω)
    (hout_zI : (s₀.arrs a_out_zI).length = Q_max ξ ω)
    (hout_vv : (s₀.arrs a_out_vv).length = S_tab δ ξ ω)
    (hout_ve : (s₀.arrs a_out_ve).length = S_tab δ ξ ω)
    (hout_em : (s₀.arrs a_out_em).length = S_tab δ ξ ω) :
    have hZ'_sub : Z' ⊆ ZA ∪ ZB := fun u hu => (hZ'_iff u).mp hu |>.1
    let α_A := finsetSubIdx (Finset.subset_union_left : ZA ⊆ ZA ∪ ZB)
    let α_B := finsetSubIdx (Finset.subset_union_right : ZB ⊆ ZA ∪ ZB)
    let β := finsetSubIdx hZ'_sub
    have hcov : ∀ k : Fin (ZA ∪ ZB).card, (∃ i_A, α_A i_A = k) ∨ (∃ i_B, α_B i_B = k) := by
      intro k
      rcases Finset.mem_union.mp (finsetRootFn_mem (ZA ∪ ZB) k) with hkA | hkB
      · rcases exists_finsetRootFn_eq hkA with ⟨i_A, hi_A⟩
        exact Or.inl ⟨i_A, finsetRootFn_injective (ZA ∪ ZB) (by simpa [α_A] using hi_A)⟩
      · rcases exists_finsetRootFn_eq hkB with ⟨i_B, hi_B⟩
        exact Or.inr ⟨i_B, finsetRootFn_injective (ZA ∪ ZB) (by simpa [α_B] using hi_B)⟩
    let kv_f := kv₀ + K_comb δ ξ ω
    let ke_f := ke₀ + K_comb δ ξ ω
    ∃ s' t,
      Exec w (combineStepProg δ ξ ω) s₀ s' t ∧
      t ≤ C_combineStep δ ξ ω ∧
      s'.regs r_kv = kv_f ∧ s'.regs r_ke = ke_f ∧
      ArenaWF G.numVerts kv_f (s'.arrs a_vkd) (s'.arrs a_vv1) (s'.arrs a_vv2) ∧
      ArenaWF G.numEdges ke_f (s'.arrs a_ekd) (s'.arrs a_ev1) (s'.arrs a_ev2) ∧
      (s'.arrs a_vkd).length = (s₀.arrs a_vkd).length ∧
      (s'.arrs a_ekd).length = (s₀.arrs a_ekd).length ∧
      (∀ p < kv₀,
        evalArena G.numVerts (s'.arrs a_vkd) (s'.arrs a_vv1) (s'.arrs a_vv2) p =
          evalArena G.numVerts (s₀.arrs a_vkd) (s₀.arrs a_vv1) (s₀.arrs a_vv2) p) ∧
      (∀ p < ke₀,
        evalArena G.numEdges (s'.arrs a_ekd) (s'.arrs a_ev1) (s'.arrs a_ev2) p =
          evalArena G.numEdges (s₀.arrs a_ekd) (s₀.arrs a_ev1) (s₀.arrs a_ev2) p) ∧
      ValidPieceBuffer δ ξ ω G Z' (EA ∪ EB) (rawCombineTables δ α_A α_B hcov β es_A es_B) bufA s' ∧
      ValidPieceBuffer δ ξ ω G ZB EB es_B bufB s' ∧
      (s'.arrs a_out_zV).length = Q_max ξ ω ∧
      (s'.arrs a_out_zI).length = Q_max ξ ω ∧
      (s'.arrs a_out_vv).length = S_tab δ ξ ω ∧
      (s'.arrs a_out_ve).length = S_tab δ ξ ω ∧
      (s'.arrs a_out_em).length = S_tab δ ξ ω ∧
      (∀ r < 10, r ≠ r_tidA → r ≠ r_qA → r ≠ r_kv → r ≠ r_ke → s'.regs r = s₀.regs r) ∧
      (∀ a, a ≠ a_vkd → a ≠ a_vv1 → a ≠ a_vv2 → a ≠ a_ekd → a ≠ a_ev1 → a ≠ a_ev2 →
        a ≠ a_out_zV → a ≠ a_out_zI → a ≠ a_out_vv → a ≠ a_out_ve → a ≠ a_out_em →
        a ≠ a_acc_zV → a ≠ a_acc_zI → a ≠ a_acc_vv → a ≠ a_acc_ve → a ≠ a_acc_em →
        s'.arrs a = s₀.arrs a) := by
  intro hZ'_sub α_A α_B β hcov kv_f ke_f
  have hw2 : 2 < 2 ^ w := by omega
  have hm_w : G.numEdges < 2 ^ w := by omega
  have hq'_le : Z'.card ≤ Q_max ξ ω := le_trans (Finset.card_le_card hZ'_sub) hqU
  have hq'_w : Z'.card < 2 ^ w := by omega
  -- 1. `mergeBoundaryProg`
  rcases mergeBoundaryProg_exec hqU hinc_union hZ'_iff hw8 hn_w hm1_w hM_w
      hr0 hbufA.hq hbufB.hq hcap
      hbufA.hzV_len hbufA.hzI_len hbufB.hzV_len hbufB.hzI_len
      hbufA.hzV hbufA.hzI hbufB.hzV hbufB.hzI hout_zV hout_zI with
    ⟨s₁, t₁, hex₁, ht₁, hr12_1, hr13_1, houtV_len₁, houtI_len₁, houtV₁, houtI₁, hreg₁, harr₁⟩
  -- 2. `.assign r_qA (.reg 12)`
  let s₂ := s₁.setReg r_qA Z'.card
  have hex₂ : Exec w (.assign r_qA (.reg 12)) s₁ s₂ 2 :=
    .assign (by simp [Expr.eval, checkWord, hr12_1, hq'_w])
  -- 3. `combineDispatchProg δ ξ ω`
  rcases combineDispatchProg_exec (s₀ := s₀) (s_in := s₂) hqU hZ'_sub hbufA hbufB
      hw2 hm_w hS_w hT_w hM_w hkv_w hke_w hr_kv0 hr_ke0
      (by simp [s₂, hreg₁ r_kv (by decide), hr_kv0])
      (by simp [s₂, hreg₁ r_ke (by decide), hr_ke0])
      (by simp [s₂, hreg₁ r_tidA (by decide)])
      (by simp [s₂, hreg₁ r_tidB (by decide)])
      (by simp [s₂, hr13_1])
      (fun a ha1 ha2 => by simp [s₂, harr₁ a ha1 ha2])
      hwfV0 hwfE0 hkv_cap hke_cap hout_vv hout_ve hout_em with
    ⟨s₃, t₃, hex₃, ht₃, htid_3, hkv_3, hke_3, hwfV_3, hwfE_3,
     hlenV_3, hlenE_3, hevV_3, hevE_3, hout_vv_3, hout_ve_3, hout_em_3,
     hslots_3, hreg₃, harr₃⟩
  -- 4. `copyOutToAccProg δ ξ ω`
  have hr0_3 : s₃.regs 0 = G.numVerts :=
    (hreg₃ 0 (by decide) (by decide) (by decide) (by decide)).trans
      (by simp [s₂, hreg₁ 0 (by decide), hr0])
  have hr1_3 : s₃.regs 1 = G.numEdges :=
    (hreg₃ 1 (by decide) (by decide) (by decide) (by decide)).trans
      (by simp [s₂, hreg₁ 1 (by decide), hr1])
  have hout_zV_3 : s₃.arrs a_out_zV = s₁.arrs a_out_zV :=
    harr₃ a_out_zV (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide)
  have hout_zI_3 : s₃.arrs a_out_zI = s₁.arrs a_out_zI :=
    harr₃ a_out_zI (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide)
  have hacc_zV_3 : s₃.arrs a_acc_zV = s₀.arrs a_acc_zV :=
    (harr₃ a_acc_zV (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide)).trans (harr₁ a_acc_zV (by decide) (by decide))
  have hacc_zI_3 : s₃.arrs a_acc_zI = s₀.arrs a_acc_zI :=
    (harr₃ a_acc_zI (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide)).trans (harr₁ a_acc_zI (by decide) (by decide))
  have hacc_vv_3 : s₃.arrs a_acc_vv = s₀.arrs a_acc_vv :=
    (harr₃ a_acc_vv (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide)).trans (harr₁ a_acc_vv (by decide) (by decide))
  have hacc_ve_3 : s₃.arrs a_acc_ve = s₀.arrs a_acc_ve :=
    (harr₃ a_acc_ve (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide)).trans (harr₁ a_acc_ve (by decide) (by decide))
  have hacc_em_3 : s₃.arrs a_acc_em = s₀.arrs a_acc_em :=
    (harr₃ a_acc_em (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide)).trans (harr₁ a_acc_em (by decide) (by decide))
  have hzV_len0 : (s₀.arrs a_acc_zV).length = Q_max ξ ω := hbufA.hzV_len
  have hzI_len0 : (s₀.arrs a_acc_zI).length = Q_max ξ ω := hbufA.hzI_len
  have hvv_len0 : (s₀.arrs a_acc_vv).length = S_tab δ ξ ω := hbufA.hvv_len
  have hve_len0 : (s₀.arrs a_acc_ve).length = S_tab δ ξ ω := hbufA.hve_len
  have hem_len0 : (s₀.arrs a_acc_em).length = S_tab δ ξ ω := hbufA.hem_len
  rcases copyOutToAccProg_exec (G := G) hQ_w hS_w hn_w hm_w hkv_w hke_w
      hr0_3 hr1_3 hkv_3 hke_3
      (by rw [hout_zV_3, houtV_len₁]) (by rw [hout_zI_3, houtI_len₁])
      hout_vv_3 hout_ve_3 hout_em_3
      (by rw [hacc_zV_3, hzV_len0]) (by rw [hacc_zI_3, hzI_len0])
      (by rw [hacc_vv_3, hvv_len0]) (by rw [hacc_ve_3, hve_len0])
      (by rw [hacc_em_3, hem_len0]) with
    ⟨s', t₄, hex₄, ht₄, hacc_zV', hacc_zI', hacc_vv', hacc_ve', hacc_em',
     hget_z', hget_pos', hreg₄, harr₄⟩
  have hvkd' : s'.arrs a_vkd = s₃.arrs a_vkd :=
    harr₄ a_vkd (by decide) (by decide) (by decide) (by decide) (by decide)
  have hvv1' : s'.arrs a_vv1 = s₃.arrs a_vv1 :=
    harr₄ a_vv1 (by decide) (by decide) (by decide) (by decide) (by decide)
  have hvv2' : s'.arrs a_vv2 = s₃.arrs a_vv2 :=
    harr₄ a_vv2 (by decide) (by decide) (by decide) (by decide) (by decide)
  have hekd' : s'.arrs a_ekd = s₃.arrs a_ekd :=
    harr₄ a_ekd (by decide) (by decide) (by decide) (by decide) (by decide)
  have hev1' : s'.arrs a_ev1 = s₃.arrs a_ev1 :=
    harr₄ a_ev1 (by decide) (by decide) (by decide) (by decide) (by decide)
  have hev2' : s'.arrs a_ev2 = s₃.arrs a_ev2 :=
    harr₄ a_ev2 (by decide) (by decide) (by decide) (by decide) (by decide)
  have hkv' : s'.regs r_kv = kv_f := (hreg₄ r_kv).trans hkv_3
  have hke' : s'.regs r_ke = ke_f := (hreg₄ r_ke).trans hke_3
  have htidA' : s'.regs r_tidA =
      tabsNewTid δ ξ ω ⟨ZA.card, es_A.map RawCertEntry.H⟩ ⟨ZB.card, es_B.map RawCertEntry.H⟩
        (ZA ∪ ZB).card (subMaskFinset (ZA ∪ ZB) ZA) (subMaskFinset (ZA ∪ ZB) ZB)
        (subMaskFinset (ZA ∪ ZB) Z') :=
    (hreg₄ r_tidA).trans htid_3
  have hqA' : s'.regs r_qA = Z'.card := by
    rw [hreg₄ r_qA, hreg₃ r_qA (by decide) (by decide) (by decide) (by decide)]
    simp [s₂]
  have harr_other : ∀ a, a ≠ a_vkd → a ≠ a_vv1 → a ≠ a_vv2 → a ≠ a_ekd → a ≠ a_ev1 → a ≠ a_ev2 →
      a ≠ a_out_zV → a ≠ a_out_zI → a ≠ a_out_vv → a ≠ a_out_ve → a ≠ a_out_em →
      a ≠ a_acc_zV → a ≠ a_acc_zI → a ≠ a_acc_vv → a ≠ a_acc_ve → a ≠ a_acc_em →
      s'.arrs a = s₀.arrs a :=
    fun a h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16 =>
      (harr₄ a h12 h13 h14 h15 h16).trans
        ((harr₃ a h1 h2 h3 h4 h5 h6 h9 h10 h11).trans (harr₁ a h7 h8))
  have hreg_other : ∀ r < 10, r ≠ r_tidA → r ≠ r_qA → r ≠ r_kv → r ≠ r_ke → s'.regs r = s₀.regs r :=
    fun r hr h1 h2 h3 h4 => by
      rw [hreg₄ r, hreg₃ r hr h1 h3 h4]
      simp [s₂, h2, hreg₁ r hr]
  -- Construct `ValidPieceBuffer` for `bufA` in `s'`
  let U := ZA ∪ ZB
  let S_A := subMaskFinset U ZA
  let S_B := subMaskFinset U ZB
  let S_Z := subMaskFinset U Z'
  let tab_A : AbstractTable := ⟨ZA.card, es_A.map RawCertEntry.H⟩
  let tab_B : AbstractTable := ⟨ZB.card, es_B.map RawCertEntry.H⟩
  let rs := combineRecipesOfTabs δ tab_A tab_B U.card S_A S_B S_Z
  let es_comb := rs.map (fun r => r.eval es_A es_B rfl rfl)
  have hSZ : S_Z.card = Z'.card := card_subMaskFinset hZ'_sub
  have hraw_eq : rawCombineTables δ α_A α_B hcov β es_A es_B = hSZ ▸ es_comb :=
    (map_eval_combineRecipesOfTabs_subMask (δ := δ) hZ'_sub es_A es_B).symm
  have hbufA' : ValidPieceBuffer δ ξ ω G Z' (EA ∪ EB)
      (rawCombineTables δ α_A α_B hcov β es_A es_B) bufA s' := by
    rw [hraw_eq]
    have hSZ_le : S_Z.card ≤ Q_max ξ ω := hSZ.symm ▸ hq'_le
    have hmap_H : es_comb.map RawCertEntry.H = rs.map (·.H) := by
      rw [List.map_map]; rfl
    refine validPieceBuffer_cast_q hSZ es_comb bufA s' hSZ_le
      (by simp only [es_comb, List.length_map]; exact length_combineRecipesOfTabs_le tab_A tab_B U.card S_A S_B S_Z)
      (fun e he => by
        rcases List.mem_map.mp he with ⟨r, hr, rfl⟩
        exact hasDetailLe_of_mem_combineRecipesOfTabs tab_A tab_B U.card S_A S_B S_Z hr)
      (by dsimp [bufA]; rw [htidA', tabsNewTid, hmap_H])
      hqA' hacc_zV' hacc_zI'
      (fun idx => by
        have hidx_Q : idx.1 < Q_max ξ ω := Nat.lt_of_lt_of_le idx.2 hq'_le
        dsimp [bufA]
        rw [(hget_z' idx.1 hidx_Q).1, hout_zV_3, houtV₁ idx]
        exact Nat.min_eq_left (le_of_lt (finsetRootFn Z' idx).2))
      (fun idx => by
        have hidx_Q : idx.1 < Q_max ξ ω := Nat.lt_of_lt_of_le idx.2 hq'_le
        dsimp [bufA]
        rw [(hget_z' idx.1 hidx_Q).2, hout_zI_3, houtI₁ idx]
        exact Nat.min_eq_left (subInc_le_numEdges G (EA ∪ EB) (finsetRootFn Z' idx)))
      hacc_vv' hacc_ve' hacc_em' ?_
    intro idx
    have hidx : idx.1 < rs.length := by simpa [es_comb] using idx.2
    let r := rs[idx.1]'hidx
    have hr_mem : r ∈ rs := List.getElem_mem hidx
    have hdet_r : r.H.HasDetailLe δ :=
      hasDetailLe_of_mem_combineRecipesOfTabs tab_A tab_B U.card S_A S_B S_Z hr_mem
    have hidx_C : idx.1 < C_max δ ξ ω :=
      Nat.lt_of_lt_of_le hidx (Nat.le_trans
        (length_combineRecipesOfTabs_le tab_A tab_B U.card S_A S_B S_Z)
        (Nat.le_of_lt (length_allDetailLeCodes_lt_C_max δ ξ ω hSZ_le)))
    have hget_comb : es_comb[idx.1] = r.eval es_A es_B rfl rfl := List.getElem_map _
    dsimp only [bufA]
    rw [hget_comb]
    refine ⟨fun v => ?_, fun d => ?_⟩
    · have hv_V : v.1 < V_max δ ξ ω := Nat.lt_trans v.2 (numVerts_lt_V_max hSZ_le hdet_r)
      let pos := idx.1 * V_max δ ξ ω + v.1
      have hpos_S : pos < S_tab δ ξ ω := by
        unfold S_tab; have := Nat.mul_le_mul_right (V_max δ ξ ω) hidx_C
        rw [Nat.succ_mul] at this; omega
      have hdiv_pos : pos / V_max δ ξ ω = idx.1 := by
        dsimp [pos]; rw [Nat.mul_comm idx.1 (V_max δ ξ ω),
          Nat.mul_add_div (V_max_pos δ ξ ω), Nat.div_eq_of_lt hv_V, Nat.add_zero]
      have hmod_pos : pos % V_max δ ξ ω = v.1 := by
        dsimp [pos]; rw [Nat.mul_comm idx.1 (V_max δ ξ ω), Nat.mul_add_mod, Nat.mod_eq_of_lt hv_V]
      rcases hslots_3 pos hpos_S with ⟨hvv_lt, hvv_ev, hve_lt, hve_ev, _⟩
      rcases hget_pos' pos hpos_S with ⟨hvv_min, hve_min, _⟩
      have hp_vv_eq : (s'.arrs a_acc_vv).getD pos 0 = (s₃.arrs a_out_vv).getD pos 0 := by
        rw [hvv_min]; exact Nat.min_eq_left (le_of_lt hvv_lt)
      have hp_ve_eq : (s'.arrs a_acc_ve).getD pos 0 = (s₃.arrs a_out_ve).getD pos 0 := by
        rw [hve_min]; exact Nat.min_eq_left (le_of_lt hve_lt)
      refine ⟨by rw [hp_vv_eq, hkv']; exact hvv_lt, ?_, by rw [hp_ve_eq, hke']; exact hve_lt, ?_⟩
      · rw [hvkd', hvv1', hvv2', hp_vv_eq, hvv_ev]
        exact slotTargetVV_eq_eval es_A es_B hbufA.hq_le hbufB.hq_le hbufA.hdet hbufB.hdet
          S_A S_B S_Z pos hdiv_pos hidx (v := ⟨v.1, v.2⟩) hmod_pos
      · rw [hekd', hev1', hev2', hp_ve_eq, hve_ev]
        exact slotTargetVE_eq_eval es_A es_B hbufA.hq_le hbufB.hq_le hbufA.hdet hbufB.hdet
          S_A S_B S_Z pos hdiv_pos hidx (v := ⟨v.1, v.2⟩) hmod_pos
    · have hd_V : d.1 < V_max δ ξ ω := Nat.lt_trans d.2 (numEdges_lt_V_max hdet_r)
      let pos := idx.1 * V_max δ ξ ω + d.1
      have hpos_S : pos < S_tab δ ξ ω := by
        unfold S_tab; have := Nat.mul_le_mul_right (V_max δ ξ ω) hidx_C
        rw [Nat.succ_mul] at this; omega
      have hdiv_pos : pos / V_max δ ξ ω = idx.1 := by
        dsimp [pos]; rw [Nat.mul_comm idx.1 (V_max δ ξ ω),
          Nat.mul_add_div (V_max_pos δ ξ ω), Nat.div_eq_of_lt hd_V, Nat.add_zero]
      have hmod_pos : pos % V_max δ ξ ω = d.1 := by
        dsimp [pos]; rw [Nat.mul_comm idx.1 (V_max δ ξ ω), Nat.mul_add_mod, Nat.mod_eq_of_lt hd_V]
      rcases hslots_3 pos hpos_S with ⟨_, _, _, _, hem_eq, hem_le⟩
      rcases hget_pos' pos hpos_S with ⟨_, _, hem_min⟩
      rw [hem_min, hem_eq]
      exact (Nat.min_eq_left (hem_eq ▸ hem_le)).trans
        (slotTargetEM_eq_eval es_A es_B S_A S_B S_Z pos hdiv_pos hidx (d := ⟨d.1, d.2⟩) hmod_pos)
  have hbufB' : ValidPieceBuffer δ ξ ω G ZB EB es_B bufB s' :=
    hbufB.mono_arena
      (hreg_other r_tidB (by decide) (by decide) (by decide) (by decide) (by decide))
      (hreg_other r_qB (by decide) (by decide) (by decide) (by decide) (by decide))
      (harr_other a_rhs_zV (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))
      (harr_other a_rhs_zI (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))
      (harr_other a_rhs_vv (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))
      (harr_other a_rhs_ve (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))
      (harr_other a_rhs_em (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))
      (by rw [hr_kv0, hkv']; exact Nat.le_add_right _ _)
      (by rw [hr_ke0, hke']; exact Nat.le_add_right _ _)
      (fun p hp => by rw [hr_kv0] at hp; rw [hvkd', hvv1', hvv2']; exact hevV_3 p hp)
      (fun p hp => by rw [hr_ke0] at hp; rw [hekd', hev1', hev2']; exact hevE_3 p hp)
  refine ⟨s', t₁ + (2 + (t₃ + t₄)),
    .seq hex₁ (.seq hex₂ (.seq hex₃ hex₄)),
    by unfold C_combineStep; omega,
    hkv', hke',
    by rw [hvkd', hvv1', hvv2']; exact hwfV_3,
    by rw [hekd', hev1', hev2']; exact hwfE_3,
    by rw [hvkd', hlenV_3], by rw [hekd', hlenE_3],
    fun p hp => by rw [hvkd', hvv1', hvv2']; exact hevV_3 p hp,
    fun p hp => by rw [hekd', hev1', hev2']; exact hevE_3 p hp,
    hbufA', hbufB',
    by rw [harr₄ a_out_zV (by decide) (by decide) (by decide) (by decide) (by decide), hout_zV_3, houtV_len₁],
    by rw [harr₄ a_out_zI (by decide) (by decide) (by decide) (by decide) (by decide), hout_zI_3, houtI_len₁],
    by rw [harr₄ a_out_vv (by decide) (by decide) (by decide) (by decide) (by decide), hout_vv_3],
    by rw [harr₄ a_out_ve (by decide) (by decide) (by decide) (by decide) (by decide), hout_ve_3],
    by rw [harr₄ a_out_em (by decide) (by decide) (by decide) (by decide) (by decide), hout_em_3],
    hreg_other, harr_other⟩

theorem combineStepProg_exec_pieceTables {w δ ξ ω kv₀ ke₀ : ℕ}
    {G : ComputeDigraph} {Z VA VB ZA ZB Z' : Finset (Fin G.numVerts)}
    {EA EB : Finset (Fin G.numEdges)}
    (hZA : ZA ⊆ VA) (hZB : ZB ⊆ VB)
    (hE_disj : Disjoint EA EB)
    (hEA : ∀ e ∈ EA, G.head e ∈ VA ∧ G.tail e ∈ VA)
    (hEB : ∀ e ∈ EB, G.head e ∈ VB ∧ G.tail e ∈ VB)
    (hinter : VA ∩ VB ⊆ ZA ∩ ZB)
    (hqU : (ZA ∪ ZB).card ≤ Q_max ξ ω)
    (hZ'_iff : ∀ u : Fin G.numVerts,
      u ∈ Z' ↔ u ∈ ZA ∪ ZB ∧ subInc G (EA ∪ EB) u < capVal G Z u)
    (T_A : CertFolioTable G VA EA (finsetRootFn ZA) δ)
    (T_B : CertFolioTable G VB EB (finsetRootFn ZB) δ)
    {s₀ : State}
    (hbufA : ValidPieceBuffer δ ξ ω G ZA EA T_A.toRawList bufA s₀)
    (hbufB : ValidPieceBuffer δ ξ ω G ZB EB T_B.toRawList bufB s₀)
    (hw8 : 8 < 2 ^ w) (hn_w : G.numVerts < 2 ^ w) (hm1_w : G.numEdges + 1 < 2 ^ w)
    (hQ_w : Q_max ξ ω < 2 ^ w) (hS_w : S_tab δ ξ ω < 2 ^ w)
    (hT_w : T_max δ ξ ω < 2 ^ w) (hM_w : M_max ξ ω < 2 ^ w)
    (hkv_w : kv₀ + K_comb δ ξ ω < 2 ^ w) (hke_w : ke₀ + K_comb δ ξ ω < 2 ^ w)
    (hr0 : s₀.regs 0 = G.numVerts) (hr1 : s₀.regs 1 = G.numEdges)
    (hr_kv0 : s₀.regs r_kv = kv₀) (hr_ke0 : s₀.regs r_ke = ke₀)
    (hcap : s₀.arrs a_cap = List.ofFn (capVal G Z))
    (hwfV0 : ArenaWF G.numVerts kv₀ (s₀.arrs a_vkd) (s₀.arrs a_vv1) (s₀.arrs a_vv2))
    (hwfE0 : ArenaWF G.numEdges ke₀ (s₀.arrs a_ekd) (s₀.arrs a_ev1) (s₀.arrs a_ev2))
    (hkv_cap : kv₀ + K_comb δ ξ ω ≤ (s₀.arrs a_vkd).length)
    (hke_cap : ke₀ + K_comb δ ξ ω ≤ (s₀.arrs a_ekd).length)
    (hout_zV : (s₀.arrs a_out_zV).length = Q_max ξ ω)
    (hout_zI : (s₀.arrs a_out_zI).length = Q_max ξ ω)
    (hout_vv : (s₀.arrs a_out_vv).length = S_tab δ ξ ω)
    (hout_ve : (s₀.arrs a_out_ve).length = S_tab δ ξ ω)
    (hout_em : (s₀.arrs a_out_em).length = S_tab δ ξ ω) :
    have hZ'_sub : Z' ⊆ ZA ∪ ZB := fun u hu => (hZ'_iff u).mp hu |>.1
    let kv_f := kv₀ + K_comb δ ξ ω
    let ke_f := ke₀ + K_comb δ ξ ω
    ∃ s' t,
      Exec w (combineStepProg δ ξ ω) s₀ s' t ∧
      t ≤ C_combineStep δ ξ ω ∧
      s'.regs r_kv = kv_f ∧ s'.regs r_ke = ke_f ∧
      ArenaWF G.numVerts kv_f (s'.arrs a_vkd) (s'.arrs a_vv1) (s'.arrs a_vv2) ∧
      ArenaWF G.numEdges ke_f (s'.arrs a_ekd) (s'.arrs a_ev1) (s'.arrs a_ev2) ∧
      (s'.arrs a_vkd).length = (s₀.arrs a_vkd).length ∧
      (s'.arrs a_ekd).length = (s₀.arrs a_ekd).length ∧
      (∀ p < kv₀,
        evalArena G.numVerts (s'.arrs a_vkd) (s'.arrs a_vv1) (s'.arrs a_vv2) p =
          evalArena G.numVerts (s₀.arrs a_vkd) (s₀.arrs a_vv1) (s₀.arrs a_vv2) p) ∧
      (∀ p < ke₀,
        evalArena G.numEdges (s'.arrs a_ekd) (s'.arrs a_ev1) (s'.arrs a_ev2) p =
          evalArena G.numEdges (s₀.arrs a_ekd) (s₀.arrs a_ev1) (s₀.arrs a_ev2) p) ∧
      ValidPieceBuffer δ ξ ω G Z' (EA ∪ EB)
        (combinePieceTables hZA hZB hZ'_sub hE_disj hEA hEB hinter T_A T_B).toRawList bufA s' ∧
      ValidPieceBuffer δ ξ ω G ZB EB T_B.toRawList bufB s' ∧
      (s'.arrs a_out_zV).length = Q_max ξ ω ∧
      (s'.arrs a_out_zI).length = Q_max ξ ω ∧
      (s'.arrs a_out_vv).length = S_tab δ ξ ω ∧
      (s'.arrs a_out_ve).length = S_tab δ ξ ω ∧
      (s'.arrs a_out_em).length = S_tab δ ξ ω ∧
      (∀ r < 10, r ≠ r_tidA → r ≠ r_qA → r ≠ r_kv → r ≠ r_ke → s'.regs r = s₀.regs r) ∧
      (∀ a, a ≠ a_vkd → a ≠ a_vv1 → a ≠ a_vv2 → a ≠ a_ekd → a ≠ a_ev1 → a ≠ a_ev2 →
        a ≠ a_out_zV → a ≠ a_out_zI → a ≠ a_out_vv → a ≠ a_out_ve → a ≠ a_out_em →
        a ≠ a_acc_zV → a ≠ a_acc_zI → a ≠ a_acc_vv → a ≠ a_acc_ve → a ≠ a_acc_em →
        s'.arrs a = s₀.arrs a) := by
  intro hZ'_sub kv_f ke_f
  have hinc_union : ∀ u ∈ ZA ∪ ZB,
      subInc G (EA ∪ EB) u =
        (if u ∈ ZA then subInc G EA u else 0) + (if u ∈ ZB then subInc G EB u else 0) := by
    intro u hu
    rw [subInc_union G hE_disj u]
    have hnotA : u ∉ ZA → subInc G EA u = 0 := by
      intro huA
      have huB : u ∈ ZB := by
        rcases Finset.mem_union.mp hu with h | h
        · exact False.elim (huA h)
        · exact h
      have huVB : u ∈ VB := hZB huB
      have huVA : u ∉ VA := fun huV =>
        huA (Finset.mem_inter.mp (hinter (Finset.mem_inter.mpr ⟨huV, huVB⟩))).1
      unfold subInc incEdges
      rw [Finset.card_eq_zero, Finset.eq_empty_iff_forall_notMem]
      intro e he
      simp only [Finset.mem_inter, Finset.mem_filter, Finset.mem_univ, true_and] at he
      rcases he with ⟨rfl | rfl, heA⟩
      · exact huVA (hEA e heA).1
      · exact huVA (hEA e heA).2
    have hnotB : u ∉ ZB → subInc G EB u = 0 := by
      intro huB
      have huA : u ∈ ZA := by
        rcases Finset.mem_union.mp hu with h | h
        · exact h
        · exact False.elim (huB h)
      have huVA : u ∈ VA := hZA huA
      have huVB : u ∉ VB := fun huV =>
        huB (Finset.mem_inter.mp (hinter (Finset.mem_inter.mpr ⟨huVA, huV⟩))).2
      unfold subInc incEdges
      rw [Finset.card_eq_zero, Finset.eq_empty_iff_forall_notMem]
      intro e he
      simp only [Finset.mem_inter, Finset.mem_filter, Finset.mem_univ, true_and] at he
      rcases he with ⟨rfl | rfl, heB⟩
      · exact huVB (hEB e heB).1
      · exact huVB (hEB e heB).2
    by_cases hA : u ∈ ZA <;> by_cases hB : u ∈ ZB <;>
      simp [hA, hB, hnotA, hnotB]
  rcases combineStepProg_exec hqU hinc_union hZ'_iff hbufA hbufB hw8 hn_w hm1_w
      hQ_w hS_w hT_w hM_w hkv_w hke_w hr0 hr1 hr_kv0 hr_ke0 hcap
      hwfV0 hwfE0 hkv_cap hke_cap hout_zV hout_zI hout_vv hout_ve hout_em with
    ⟨s', t, hex, ht, hkv', hke', hwfV', hwfE', hlenV', hlenE', hevV', hevE',
     hbufA', hbufB', hout_zV', hout_zI', hout_vv', hout_ve', hout_em', hreg', harr'⟩
  have hraw_eq := toRawList_combinePieceTables (δ := δ) hZA hZB hZ'_sub hE_disj hEA hEB hinter T_A T_B
  refine ⟨s', t, hex, ht, hkv', hke', hwfV', hwfE', hlenV', hlenE', hevV', hevE',
    hraw_eq.symm ▸ hbufA', hbufB',
    hout_zV', hout_zI', hout_vv', hout_ve', hout_em', hreg', harr'⟩

end GraphMinor.Compute
