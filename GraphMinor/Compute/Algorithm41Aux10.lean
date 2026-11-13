module

public import GraphMinor.Compute.Algorithm41Aux9

/-!
# Isolated-Vertex Completion for GM XIII (4.1)

This file implements and verifies the isolated-vertex pass of GM XIII (4.1)
(Robertson and Seymour, *Graph Minors. XIII. The Disjoint Paths Problem*, pages 75–76).
After the bottom-up tree computation, `isoVertLoopProg` adds each isolated vertex
using a single-vertex base table and the constant-time combination program.
The execution theorem identifies the resulting buffer with `computeFolioDP`
and bounds the running time and arena space by a constant times the vertex count.
-/

@[expose] public section

namespace GraphMinor.Compute

open SimpleGraph

/-! ### Section 1: Isolated-Vertex Completion Pass (`isoVertStepProg`, `isoVertLoopProg`) -/

theorem mem_dpVertPrefix_self_iff (G : ComputeDigraph) (v : Fin G.numVerts) :
    v ∈ dpVertPrefix G v.1 ↔ v ∈ pieceVB G Finset.univ := by
  simp [dpVertPrefix]

theorem subInc_univ_eq_totalInc (G : ComputeDigraph) (v : Fin G.numVerts) :
    subInc G Finset.univ v = totalInc G v := by
  simp [subInc, totalInc]

theorem mem_dpVertPrefix_self_iff_totalInc_pos (G : ComputeDigraph) (v : Fin G.numVerts) :
    v ∈ dpVertPrefix G v.1 ↔ 0 < totalInc G v := by
  rw [mem_dpVertPrefix_self_iff, mem_pieceVB_iff_subInc_pos, subInc_univ_eq_totalInc]

theorem not_mem_dpVertPrefix_self_iff_totalInc_eq_zero (G : ComputeDigraph) (v : Fin G.numVerts) :
    v ∉ dpVertPrefix G v.1 ↔ totalInc G v = 0 := by
  rw [mem_dpVertPrefix_self_iff_totalInc_pos]
  omega

theorem ValidPieceBuffer.setReg_ne {δ ξ ω : ℕ} {G : ComputeDigraph}
    {Z_P : Finset (Fin G.numVerts)} {E_P : Finset (Fin G.numEdges)}
    {es : List (RawCertEntry G Z_P.card)} {buf : PieceBufLayout} {s : State}
    (h : ValidPieceBuffer δ ξ ω G Z_P E_P es buf s)
    (r : ℕ) (h1 : r ≠ buf.r_tid) (h2 : r ≠ buf.r_q) (h3 : r ≠ r_kv) (h4 : r ≠ r_ke) (v : ℕ) :
    ValidPieceBuffer δ ξ ω G Z_P E_P es buf (s.setReg r v) :=
  h.mono_arena
    (State.setReg_regs_ne s v h1.symm)
    (State.setReg_regs_ne s v h2.symm)
    rfl rfl rfl rfl rfl
    (by rw [State.setReg_regs_ne s v h3.symm])
    (by rw [State.setReg_regs_ne s v h4.symm])
    (fun _ _ => rfl) (fun _ _ => rfl)

/-- Next accumulator table in `addIsolatedVertsTable.loop` at vertex index `k < G.numVerts`. -/
def isoNextAcc (G : ComputeDigraph) (Z : Finset (Fin G.numVerts)) (δ : ℕ)
    {k : ℕ} (hlt : k < G.numVerts)
    (acc : CertFolioTable G (dpVertPrefix G k) Finset.univ
      (finsetRootFn (Z ∩ dpVertPrefix G k)) δ) :
    CertFolioTable G (dpVertPrefix G (k + 1)) Finset.univ
      (finsetRootFn (Z ∩ dpVertPrefix G (k + 1))) δ :=
  let v : Fin G.numVerts := ⟨k, hlt⟩
  if hv : v ∈ dpVertPrefix G k then
    acc.castSets
      (dpVertPrefix_step_mem G hv).symm rfl
      (by rw [dpVertPrefix_step_mem G hv])
  else
    let singleT : CertFolioTable G {v} ∅ (finsetRootFn (Z ∩ {v})) δ :=
      baseCertFolioTable G {v} ∅ (finsetRootFn (Z ∩ {v})) δ
    have hVB_sub : ∀ e ∈ (Finset.univ : Finset (Fin G.numEdges)),
        G.head e ∈ dpVertPrefix G k ∧ G.tail e ∈ dpVertPrefix G k :=
      fun _ he =>
        ⟨Finset.mem_union_left _ (head_mem_edgeEnds he),
         Finset.mem_union_left _ (tail_mem_edgeEnds he)⟩
    have hinter : dpVertPrefix G k ∩ {v} ⊆ (Z ∩ dpVertPrefix G k) ∩ (Z ∩ {v}) := by
      intro u hu
      rcases Finset.mem_inter.mp hu with ⟨hu_pre, hu_v⟩
      rw [Finset.mem_singleton] at hu_v
      subst hu_v
      exact False.elim (hv hu_pre)
    have hZ_sub : Z ∩ (dpVertPrefix G k ∪ {v}) ⊆
        (Z ∩ dpVertPrefix G k) ∪ (Z ∩ {v}) := by
      intro u hu
      rw [Finset.inter_union_distrib_left] at hu
      exact hu
    (combinePieceTables
      Finset.inter_subset_right
      Finset.inter_subset_right
      hZ_sub
      (Finset.disjoint_empty_right _)
      hVB_sub
      (fun _ he => by simp at he)
      hinter
      acc singleT).castSets
      (dpVertPrefix_step_not_mem G v).symm
      (Finset.union_empty _)
      (by rw [dpVertPrefix_step_not_mem G v])

theorem addIsolatedVertsTable_loop_step (G : ComputeDigraph) (Z : Finset (Fin G.numVerts))
    (δ : ℕ) {k : ℕ} (hlt : k < G.numVerts)
    (acc : CertFolioTable G (dpVertPrefix G k) Finset.univ
      (finsetRootFn (Z ∩ dpVertPrefix G k)) δ) :
    addIsolatedVertsTable.loop G Z δ k (by omega) acc =
      addIsolatedVertsTable.loop G Z δ (k + 1) (by omega) (isoNextAcc G Z δ hlt acc) := by
  rw [addIsolatedVertsTable.loop]
  simp only [hlt, ↓reduceDIte, isoNextAcc]

theorem addIsolatedVertsTable_loop_done (G : ComputeDigraph) (Z : Finset (Fin G.numVerts))
    (δ : ℕ)
    (acc : CertFolioTable G (dpVertPrefix G G.numVerts) Finset.univ
      (finsetRootFn (Z ∩ dpVertPrefix G G.numVerts)) δ) :
    addIsolatedVertsTable.loop G Z δ G.numVerts (le_refl _) acc = acc := by
  rw [addIsolatedVertsTable.loop]
  simp

/-- Arena allocation bound per vertex in the isolated-vertex completion pass. -/
abbrev K_iso (δ ξ ω : ℕ) : ℕ :=
  3 + K_comb δ ξ ω

/-- Running time bound per vertex in the isolated-vertex completion pass. -/
abbrev C_isoStep (δ ξ ω : ℕ) : ℕ :=
  360 + 15 * S_tab δ ξ ω + C_combineStep δ ξ ω

/-- Word RAM command processing vertex `r_9 = k` during the isolated-vertex completion pass:
if `a_tot[r_9] == 0`, builds the single-vertex base table in `bufB` and combines `bufA` with `bufB`. -/
def isoVertStepProg (δ ξ ω : ℕ) : Cmd :=
  .ite (.op .eq (.read a_tot (.reg 9)) (.const 0))
    (.seq (isoBaseStepProg δ ξ ω 9)
      (combineStepProg δ ξ ω))
    .skip

theorem isoVertStepProg_exec {w δ ξ ω : ℕ} (inp : Alg41CoreInput ξ ω)
    (hw : Alg41WordBounds w δ ξ ω inp)
    {k kv₀ ke₀ : ℕ} (hk_lt : k < inp.G.numVerts)
    (acc : CertFolioTable inp.G (dpVertPrefix inp.G k) Finset.univ
      (finsetRootFn (inp.Z ∩ dpVertPrefix inp.G k)) δ)
    {s₀ : State}
    (hinv : TreeDPStateInv δ ξ ω inp s₀)
    (har : ArenaStateInv inp.G kv₀ ke₀ s₀)
    (hr9 : s₀.regs 9 = k)
    (hkv_w : kv₀ + K_iso δ ξ ω < 2 ^ w)
    (hke_w : ke₀ + K_iso δ ξ ω < 2 ^ w)
    (hkv_cap : kv₀ + K_iso δ ξ ω ≤ (s₀.arrs a_vkd).length)
    (hke_cap : ke₀ + K_iso δ ξ ω ≤ (s₀.arrs a_ekd).length)
    (hbufA : ValidPieceBuffer δ ξ ω inp.G (inp.Z ∩ dpVertPrefix inp.G k) Finset.univ
      acc.toRawList bufA s₀) :
    ∃ s' t_step kv' ke',
      Exec w (isoVertStepProg δ ξ ω) s₀ s' t_step ∧
      t_step ≤ C_isoStep δ ξ ω ∧
      kv₀ ≤ kv' ∧ kv' ≤ kv₀ + K_iso δ ξ ω ∧
      ke₀ ≤ ke' ∧ ke' ≤ ke₀ + K_iso δ ξ ω ∧
      TreeDPStateInv δ ξ ω inp s' ∧
      ArenaStateInv inp.G kv' ke' s' ∧
      s'.regs 9 = k ∧
      (s'.arrs a_vkd).length = (s₀.arrs a_vkd).length ∧
      (s'.arrs a_ekd).length = (s₀.arrs a_ekd).length ∧
      ValidPieceBuffer δ ξ ω inp.G (inp.Z ∩ dpVertPrefix inp.G (k + 1)) Finset.univ
        (isoNextAcc inp.G inp.Z δ hk_lt acc).toRawList bufA s' := by
  let v : Fin inp.G.numVerts := ⟨k, hk_lt⟩
  let tot_v := totalInc inp.G v
  have hw8 := hw.hw8
  have hn_w := hw.hn_w
  have hm_w := hw.hm_w
  have hm1_w := hw.hm1_w
  have hk_w : k < 2 ^ w := by omega
  have h0_w : 0 < 2 ^ w := by omega
  have h1_w : 1 < 2 ^ w := by omega
  have htot_le : tot_v ≤ inp.G.numEdges := totalInc_le_numEdges inp.G v
  have htot_w : tot_v < 2 ^ w := by omega
  have hread_tot : (Expr.read a_tot (.reg 9)).eval w s₀ = some tot_v := by
    simp [Expr.eval, checkWord, hr9, hk_w, hinv.htot, hk_lt, v, tot_v, htot_w]
  by_cases htot0 : tot_v = 0
  · have hcond : (Expr.op .eq (.read a_tot (.reg 9)) (.const 0)).eval w s₀ = some 1 := by
      rw [Expr.eval, hread_tot]
      simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, h0_w, htot0, h1_w]
    have hv_not_mem : v ∉ dpVertPrefix inp.G k :=
      (not_mem_dpVertPrefix_self_iff_totalInc_eq_zero inp.G v).mpr htot0
    -- 1. Execute `isoBaseStepProg δ ξ ω 9`
    rcases isoBaseStepProg_exec (w := w) (δ := δ) (ξ := ξ) (ω := ω) (G := inp.G) (Z := inp.Z)
        v (r_v := 9) (by decide) (by decide) (by decide) (by decide) (by decide)
        (kv₀ := kv₀) (ke₀ := ke₀) (s := s₀)
        hw.hw72 hn_w hm_w hw.hS_w hw.hT_w
        (by dsimp [K_iso] at hkv_w; omega) (by dsimp [K_iso] at hke_w; omega)
        har.hwfV har.hwfE
        (by dsimp [K_iso] at hkv_cap; omega) (by dsimp [K_iso] at hke_cap; omega)
        har.hr_kv har.hr_ke hr9 hinv.hZ
        hinv.hrhs_zV hinv.hrhs_zI hinv.hrhs_vv hinv.hrhs_ve hinv.hrhs_em with
      ⟨s₁, t₁, hex₁, ht₁, hkv₁, hke₁, hwfV₁, hwfE₁, hlenV₁, hlenE₁,
       hevV₁, hevE₁, hbufB₁, hreg₁, harr₁⟩
    have hbufA₁ : ValidPieceBuffer δ ξ ω inp.G (inp.Z ∩ dpVertPrefix inp.G k) Finset.univ
        acc.toRawList bufA s₁ := by
      refine hbufA.mono_arena
        (hreg₁ r_tidA (by decide) (by decide) (by decide) (by decide) (by decide))
        (hreg₁ r_qA (by decide) (by decide) (by decide) (by decide) (by decide))
        (harr₁ bufA.a_zV (by decide) (by decide) (by decide) (by decide) (by decide)
          (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))
        (harr₁ bufA.a_zI (by decide) (by decide) (by decide) (by decide) (by decide)
          (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))
        (harr₁ bufA.a_vv (by decide) (by decide) (by decide) (by decide) (by decide)
          (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))
        (harr₁ bufA.a_ve (by decide) (by decide) (by decide) (by decide) (by decide)
          (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))
        (harr₁ bufA.a_em (by decide) (by decide) (by decide) (by decide) (by decide)
          (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))
        (by rw [har.hr_kv, hkv₁]; omega)
        (by rw [har.hr_ke, hke₁]; omega)
        (fun p hp => hevV₁ p (by rw [← har.hr_kv]; exact hp))
        (fun p hp => hevE₁ p (by rw [← har.hr_ke]; exact hp))
    -- 2. Execute `combineStepProg δ ξ ω`
    let ZA := inp.Z ∩ dpVertPrefix inp.G k
    let ZB := inp.Z ∩ {v}
    let singleT := baseCertFolioTable inp.G {v} ∅ (finsetRootFn ZB) δ
    have hVB_sub : ∀ e ∈ (Finset.univ : Finset (Fin inp.G.numEdges)),
        inp.G.head e ∈ dpVertPrefix inp.G k ∧ inp.G.tail e ∈ dpVertPrefix inp.G k :=
      fun _ he =>
        ⟨Finset.mem_union_left _ (head_mem_edgeEnds he),
         Finset.mem_union_left _ (tail_mem_edgeEnds he)⟩
    have hEB_sub : ∀ e ∈ (∅ : Finset (Fin inp.G.numEdges)),
        inp.G.head e ∈ ({v} : Finset _) ∧ inp.G.tail e ∈ ({v} : Finset _) :=
      fun _ he => by simp at he
    have hinter : dpVertPrefix inp.G k ∩ {v} ⊆ ZA ∩ ZB := by
      intro u hu
      rcases Finset.mem_inter.mp hu with ⟨hu_pre, hu_v⟩
      rw [Finset.mem_singleton] at hu_v
      subst hu_v
      exact False.elim (hv_not_mem hu_pre)
    have hqU : (ZA ∪ ZB).card ≤ Q_max ξ ω := by
      have hsub : ZA ∪ ZB ⊆ inp.Z :=
        Finset.union_subset Finset.inter_subset_left Finset.inter_subset_left
      have hle1 : (ZA ∪ ZB).card ≤ inp.Z.card := Finset.card_le_card hsub
      have hle2 := inp.hZ
      unfold Q_max
      omega
    have hZ'_eq : inp.Z ∩ (dpVertPrefix inp.G k ∪ {v}) = ZA ∪ ZB :=
      Finset.inter_union_distrib_left inp.Z (dpVertPrefix inp.G k) {v}
    have hZ'_iff : ∀ u : Fin inp.G.numVerts,
        u ∈ inp.Z ∩ (dpVertPrefix inp.G k ∪ {v}) ↔
          u ∈ ZA ∪ ZB ∧ subInc inp.G (Finset.univ ∪ ∅) u < capVal inp.G inp.Z u := by
      intro u
      rw [hZ'_eq]
      refine ⟨fun hu => ⟨hu, ?_⟩, fun h => h.1⟩
      have huZ : u ∈ inp.Z :=
        Finset.union_subset Finset.inter_subset_left Finset.inter_subset_left hu
      have hcap_u : capVal inp.G inp.Z u = inp.G.numEdges + 1 := by simp [capVal, huZ]
      have hle_tot : subInc inp.G (Finset.univ ∪ ∅) u ≤ inp.G.numEdges :=
        (subInc_le_totalInc inp.G (Finset.univ ∪ ∅) u).trans (totalInc_le_numEdges inp.G u)
      omega
    rcases combineStepProg_exec_pieceTables (w := w) (δ := δ) (ξ := ξ) (ω := ω)
        (kv₀ := kv₀ + 3) (ke₀ := ke₀ + 1) (G := inp.G) (Z := inp.Z)
        (VA := dpVertPrefix inp.G k) (VB := {v}) (ZA := ZA) (ZB := ZB)
        (Z' := inp.Z ∩ (dpVertPrefix inp.G k ∪ {v}))
        (EA := Finset.univ) (EB := ∅)
        Finset.inter_subset_right Finset.inter_subset_right
        (Finset.disjoint_empty_right _) hVB_sub hEB_sub hinter hqU hZ'_iff
        acc singleT hbufA₁ hbufB₁
        hw8 hn_w hm1_w hw.hQ_w hw.hS_w hw.hT_w hw.hM_w
        (by dsimp [K_iso] at hkv_w; omega) (by dsimp [K_iso] at hke_w; omega)
        (by rw [hreg₁ 0 (by decide) (by decide) (by decide) (by decide) (by decide), hinv.hr0])
        (by rw [hreg₁ 1 (by decide) (by decide) (by decide) (by decide) (by decide), hinv.hr1])
        hkv₁ hke₁
        (by rw [harr₁ a_cap (by decide) (by decide) (by decide) (by decide) (by decide)
                  (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), hinv.hcap])
        hwfV₁ hwfE₁
        (by rw [hlenV₁]; dsimp [K_iso] at hkv_cap; omega)
        (by rw [hlenE₁]; dsimp [K_iso] at hke_cap; omega)
        (by rw [harr₁ a_out_zV (by decide) (by decide) (by decide) (by decide) (by decide)
                  (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), hinv.hout_zV])
        (by rw [harr₁ a_out_zI (by decide) (by decide) (by decide) (by decide) (by decide)
                  (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), hinv.hout_zI])
        (by rw [harr₁ a_out_vv (by decide) (by decide) (by decide) (by decide) (by decide)
                  (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), hinv.hout_vv])
        (by rw [harr₁ a_out_ve (by decide) (by decide) (by decide) (by decide) (by decide)
                  (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), hinv.hout_ve])
        (by rw [harr₁ a_out_em (by decide) (by decide) (by decide) (by decide) (by decide)
                  (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), hinv.hout_em]) with
      ⟨s₂, t₂, hex₂, ht₂, hkv₂, hke₂, hwfV₂, hwfE₂, hlenV₂, hlenE₂,
       _, _, hbufA₂, hbufB₂, hout_zV₂, hout_zI₂, hout_vv₂, hout_ve₂, hout_em₂, hreg₂, harr₂⟩
    have hex_ite : Exec w (isoVertStepProg δ ξ ω) s₀ s₂ (4 + (t₁ + t₂)) :=
      .ite_true hcond (by decide) (.seq hex₁ hex₂)
    have hinv₂ : TreeDPStateInv δ ξ ω inp s₂ := by
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
        hbufA₂.hzV_len, hbufA₂.hzI_len, hbufA₂.hvv_len, hbufA₂.hve_len, hbufA₂.hem_len,
        hbufB₂.hzV_len, hbufB₂.hzI_len, hbufB₂.hvv_len, hbufB₂.hve_len, hbufB₂.hem_len,
        hout_zV₂, hout_zI₂, hout_vv₂, hout_ve₂, hout_em₂,
        ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · rw [hreg₂ 0 (by decide) (by decide) (by decide) (by decide) (by decide),
            hreg₁ 0 (by decide) (by decide) (by decide) (by decide) (by decide), hinv.hr0]
      · rw [hreg₂ 1 (by decide) (by decide) (by decide) (by decide) (by decide),
            hreg₁ 1 (by decide) (by decide) (by decide) (by decide) (by decide), hinv.hr1]
      · rw [hreg₂ 2 (by decide) (by decide) (by decide) (by decide) (by decide),
            hreg₁ 2 (by decide) (by decide) (by decide) (by decide) (by decide), hinv.hr2]
      · rw [harr₂ a_head (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
              (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
              (by decide) (by decide) (by decide),
            harr₁ a_head (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
              (by decide) (by decide) (by decide) (by decide) (by decide), hinv.hhead]
      · rw [harr₂ a_tail (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
              (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
              (by decide) (by decide) (by decide),
            harr₁ a_tail (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
              (by decide) (by decide) (by decide) (by decide) (by decide), hinv.htail]
      · rw [harr₂ a_Z (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
              (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
              (by decide) (by decide) (by decide),
            harr₁ a_Z (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
              (by decide) (by decide) (by decide) (by decide) (by decide), hinv.hZ]
      · rw [harr₂ a_tot (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
              (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
              (by decide) (by decide) (by decide),
            harr₁ a_tot (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
              (by decide) (by decide) (by decide) (by decide) (by decide), hinv.htot]
      · rw [harr₂ a_edge (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
              (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
              (by decide) (by decide) (by decide),
            harr₁ a_edge (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
              (by decide) (by decide) (by decide) (by decide) (by decide), hinv.hedge]
      · rw [harr₂ a_cap (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
              (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
              (by decide) (by decide) (by decide),
            harr₁ a_cap (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
              (by decide) (by decide) (by decide) (by decide) (by decide), hinv.hcap]
      · rw [harr₂ a_degC (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
              (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
              (by decide) (by decide) (by decide),
            harr₁ a_degC (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
              (by decide) (by decide) (by decide) (by decide) (by decide), hinv.hdegC]
      · rw [harr₂ a_ch (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
              (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
              (by decide) (by decide) (by decide),
            harr₁ a_ch (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
              (by decide) (by decide) (by decide) (by decide) (by decide), hinv.hch]
      · rw [harr₂ a_sub_tid (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
              (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
              (by decide) (by decide) (by decide),
            harr₁ a_sub_tid (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
              (by decide) (by decide) (by decide) (by decide) (by decide), hinv.hsub_tid]
      · rw [harr₂ a_sub_q (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
              (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
              (by decide) (by decide) (by decide),
            harr₁ a_sub_q (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
              (by decide) (by decide) (by decide) (by decide) (by decide), hinv.hsub_q]
      · rw [harr₂ a_sub_zV (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
              (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
              (by decide) (by decide) (by decide),
            harr₁ a_sub_zV (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
              (by decide) (by decide) (by decide) (by decide) (by decide), hinv.hsub_zV]
      · rw [harr₂ a_sub_zI (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
              (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
              (by decide) (by decide) (by decide),
            harr₁ a_sub_zI (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
              (by decide) (by decide) (by decide) (by decide) (by decide), hinv.hsub_zI]
      · rw [harr₂ a_sub_vv (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
              (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
              (by decide) (by decide) (by decide),
            harr₁ a_sub_vv (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
              (by decide) (by decide) (by decide) (by decide) (by decide), hinv.hsub_vv]
      · rw [harr₂ a_sub_ve (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
              (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
              (by decide) (by decide) (by decide),
            harr₁ a_sub_ve (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
              (by decide) (by decide) (by decide) (by decide) (by decide), hinv.hsub_ve]
      · rw [harr₂ a_sub_em (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
              (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
              (by decide) (by decide) (by decide),
            harr₁ a_sub_em (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
              (by decide) (by decide) (by decide) (by decide) (by decide), hinv.hsub_em]
    have hZ_next_eq : inp.Z ∩ (dpVertPrefix inp.G k ∪ {v}) = inp.Z ∩ dpVertPrefix inp.G (k + 1) := by
      rw [dpVertPrefix_step_not_mem inp.G v]
    have hbufA_next : ValidPieceBuffer δ ξ ω inp.G (inp.Z ∩ dpVertPrefix inp.G (k + 1)) Finset.univ
        (isoNextAcc inp.G inp.Z δ hk_lt acc).toRawList bufA s₂ := by
      refine ValidPieceBuffer.of_toSigmaRaw_eq (Finset.union_empty _) hZ_next_eq ?_ hbufA₂
      unfold isoNextAcc
      simp only [v, hv_not_mem, ↓reduceDIte, CertFolioTable.toSigmaRaw_castSets]
      rfl
    refine ⟨s₂, 4 + (t₁ + t₂), kv₀ + 3 + K_comb δ ξ ω, ke₀ + 1 + K_comb δ ξ ω,
      hex_ite, by dsimp [C_isoStep]; omega,
      by omega, by dsimp [K_iso]; omega, by omega, by dsimp [K_iso]; omega,
      hinv₂, ⟨hkv₂, hke₂, hwfV₂, hwfE₂⟩,
      by rw [hreg₂ 9 (by decide) (by decide) (by decide) (by decide) (by decide),
             hreg₁ 9 (by decide) (by decide) (by decide) (by decide) (by decide), hr9],
      hlenV₂.trans hlenV₁, hlenE₂.trans hlenE₁, hbufA_next⟩
  · have hcond : (Expr.op .eq (.read a_tot (.reg 9)) (.const 0)).eval w s₀ = some 0 := by
      rw [Expr.eval, hread_tot]
      simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, h0_w, htot0]
    have hv_mem : v ∈ dpVertPrefix inp.G k := by
      rw [show k = v.1 from rfl, mem_dpVertPrefix_self_iff_totalInc_pos]
      omega
    have hex_ite : Exec w (isoVertStepProg δ ξ ω) s₀ s₀ (4 + 1) :=
      .ite_false hcond (.skip s₀)
    have hbufA_next : ValidPieceBuffer δ ξ ω inp.G (inp.Z ∩ dpVertPrefix inp.G (k + 1)) Finset.univ
        (isoNextAcc inp.G inp.Z δ hk_lt acc).toRawList bufA s₀ := by
      refine ValidPieceBuffer.of_toSigmaRaw_eq rfl (by rw [dpVertPrefix_step_mem inp.G hv_mem]) ?_ hbufA
      unfold isoNextAcc
      simp only [v, hv_mem, ↓reduceDIte, CertFolioTable.toSigmaRaw_castSets]
    refine ⟨s₀, 4 + 1, kv₀, ke₀, hex_ite, by dsimp [C_isoStep]; omega,
      le_refl _, by omega, le_refl _, by omega,
      hinv, har, hr9, rfl, rfl, hbufA_next⟩

/-- Body of the isolated-vertex completion loop: processes vertex `r_9` and increments `r_9`. -/
def isoVertLoopBody (δ ξ ω : ℕ) : Cmd :=
  .seq (isoVertStepProg δ ξ ω)
    (.assign 9 (.op .add (.reg 9) (.const 1)))

/-- Complete isolated-vertex completion pass (`r_9` from `0` up to `r_0 = G.numVerts`). -/
def isoVertLoopProg (δ ξ ω : ℕ) : Cmd :=
  .seq (.assign 9 (.const 0))
    (.while (.op .lt (.reg 9) (.reg 0))
      (isoVertLoopBody δ ξ ω))

theorem isoVertLoop_exec {w δ ξ ω : ℕ} (inp : Alg41CoreInput ξ ω)
    (hw : Alg41WordBounds w δ ξ ω inp)
    {k kv₀ ke₀ : ℕ} (hk_le : k ≤ inp.G.numVerts)
    (acc : CertFolioTable inp.G (dpVertPrefix inp.G k) Finset.univ
      (finsetRootFn (inp.Z ∩ dpVertPrefix inp.G k)) δ)
    {s : State}
    (hinv : TreeDPStateInv δ ξ ω inp s)
    (har : ArenaStateInv inp.G kv₀ ke₀ s)
    (hr9 : s.regs 9 = k)
    (hkv_w : kv₀ + (inp.G.numVerts - k) * K_iso δ ξ ω < 2 ^ w)
    (hke_w : ke₀ + (inp.G.numVerts - k) * K_iso δ ξ ω < 2 ^ w)
    (hkv_cap : kv₀ + (inp.G.numVerts - k) * K_iso δ ξ ω ≤ (s.arrs a_vkd).length)
    (hke_cap : ke₀ + (inp.G.numVerts - k) * K_iso δ ξ ω ≤ (s.arrs a_ekd).length)
    (hbufA : ValidPieceBuffer δ ξ ω inp.G (inp.Z ∩ dpVertPrefix inp.G k) Finset.univ
      acc.toRawList bufA s) :
    ∃ s' t_loop kv' ke',
      Exec w (.while (.op .lt (.reg 9) (.reg 0)) (isoVertLoopBody δ ξ ω)) s s' t_loop ∧
      t_loop ≤ 3 + (inp.G.numVerts - k) * (C_isoStep δ ξ ω + 9) ∧
      kv₀ ≤ kv' ∧ kv' ≤ kv₀ + (inp.G.numVerts - k) * K_iso δ ξ ω ∧
      ke₀ ≤ ke' ∧ ke' ≤ ke₀ + (inp.G.numVerts - k) * K_iso δ ξ ω ∧
      TreeDPStateInv δ ξ ω inp s' ∧
      ArenaStateInv inp.G kv' ke' s' ∧
      (s'.arrs a_vkd).length = (s.arrs a_vkd).length ∧
      (s'.arrs a_ekd).length = (s.arrs a_ekd).length ∧
      ValidPieceBuffer δ ξ ω inp.G
        (inp.Z ∩ dpVertPrefix inp.G inp.G.numVerts) Finset.univ
        (addIsolatedVertsTable.loop inp.G inp.Z δ k hk_le acc).toRawList bufA s' := by
  generalize hrem : inp.G.numVerts - k = rem
  induction rem generalizing k kv₀ ke₀ s with
  | zero =>
    have hkeq : k = inp.G.numVerts := by omega
    subst hkeq
    have hw8 := hw.hw8
    have hn_w := hw.hn_w
    have h0_w : 0 < 2 ^ w := by omega
    have hcond : (Expr.op .lt (.reg 9) (.reg 0)).eval w s = some 0 := by
      simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hr9, hinv.hr0, hn_w, h0_w]
    rw [addIsolatedVertsTable_loop_done]
    exact ⟨s, 3, kv₀, ke₀, .while_false hcond, by omega,
      le_refl _, by omega, le_refl _, by omega, hinv, har, rfl, rfl, hbufA⟩
  | succ rem ih =>
    have hk_lt : k < inp.G.numVerts := by omega
    have hw8 := hw.hw8
    have hn_w := hw.hn_w
    have hk_w : k < 2 ^ w := by omega
    have h1_w : 1 < 2 ^ w := by omega
    have hcond : (Expr.op .lt (.reg 9) (.reg 0)).eval w s = some 1 := by
      simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hr9, hinv.hr0, hk_w, hn_w, hk_lt, h1_w]
    have hmul_split : (rem + 1) * K_iso δ ξ ω = K_iso δ ξ ω + rem * K_iso δ ξ ω := by
      rw [Nat.add_mul, Nat.one_mul, Nat.add_comm]
    rw [hrem, hmul_split] at hkv_w hke_w hkv_cap hke_cap
    rcases isoVertStepProg_exec inp hw hk_lt acc hinv har hr9
        (by omega) (by omega) (by omega) (by omega) hbufA with
      ⟨s₁, t₁, kv₁, ke₁, hex₁, ht₁, hkv₁_ge, hkv₁_le, hke₁_ge, hke₁_le,
       hinv₁, har₁, hr9_1, hlenV₁, hlenE₁, hbufA₁⟩
    let s₂ := s₁.setReg 9 (k + 1)
    have hk1_w : k + 1 < 2 ^ w := by omega
    have hex₂ : Exec w (.assign 9 (.op .add (.reg 9) (.const 1))) s₁ s₂ 4 := by
      refine .assign ?_
      simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hr9_1, hk_w, h1_w, hk1_w]
    have hinv₂ : TreeDPStateInv δ ξ ω inp s₂ := hinv₁.setReg_ge3 9 (by decide) (k + 1)
    have har₂ : ArenaStateInv inp.G kv₁ ke₁ s₂ :=
      har₁.setReg_ne 9 (by decide) (by decide) (k + 1)
    have hbufA₂ : ValidPieceBuffer δ ξ ω inp.G (inp.Z ∩ dpVertPrefix inp.G (k + 1)) Finset.univ
        (isoNextAcc inp.G inp.Z δ hk_lt acc).toRawList bufA s₂ :=
      hbufA₁.setReg_ne 9 (by decide) (by decide) (by decide) (by decide) (k + 1)
    have hrem' : inp.G.numVerts - (k + 1) = rem := by omega
    rcases ih (k := k + 1) (kv₀ := kv₁) (ke₀ := ke₁) (s := s₂) (by omega)
        (isoNextAcc inp.G inp.Z δ hk_lt acc) hinv₂ har₂
        (State.setReg_regs_self s₁ 9 (k + 1))
        (by rw [hrem']; omega)
        (by rw [hrem']; omega)
        (by rw [hrem', State.setReg_arrs, hlenV₁]; omega)
        (by rw [hrem', State.setReg_arrs, hlenE₁]; omega)
        hbufA₂ hrem' with
      ⟨s₃, t_rem, kv', ke', hex_rem, ht_rem, hkv'_ge, hkv'_le, hke'_ge, hke'_le,
       hinv₃, har₃, hlenV₃, hlenE₃, hbufA₃⟩
    rw [← addIsolatedVertsTable_loop_step inp.G inp.Z δ hk_lt acc] at hbufA₃
    have htime_split :
        3 + (rem + 1) * (C_isoStep δ ξ ω + 9) =
          (3 + (C_isoStep δ ξ ω + 4)) + (3 + rem * (C_isoStep δ ξ ω + 9)) + 2 := by
      rw [Nat.add_mul, Nat.one_mul]; omega
    refine ⟨s₃, 3 + (t₁ + 4) + t_rem, kv', ke',
      .while_true hcond (by decide) (.seq hex₁ hex₂) hex_rem,
      by rw [htime_split]; omega,
      hkv₁_ge.trans hkv'_ge,
      by rw [hmul_split]; omega,
      hke₁_ge.trans hke'_ge,
      by rw [hmul_split]; omega,
      hinv₃, har₃,
      hlenV₃.trans hlenV₁, hlenE₃.trans hlenE₁,
      hbufA₃⟩

theorem isoVertLoopProg_exec {w δ ξ ω : ℕ} (inp : Alg41CoreInput ξ ω)
    (hw : Alg41WordBounds w δ ξ ω inp)
    {kv₀ ke₀ : ℕ} {s₀ : State}
    (hinv : TreeDPStateInv δ ξ ω inp s₀)
    (har : ArenaStateInv inp.G kv₀ ke₀ s₀)
    (hkv_w : kv₀ + inp.G.numVerts * K_iso δ ξ ω < 2 ^ w)
    (hke_w : ke₀ + inp.G.numVerts * K_iso δ ξ ω < 2 ^ w)
    (hkv_cap : kv₀ + inp.G.numVerts * K_iso δ ξ ω ≤ (s₀.arrs a_vkd).length)
    (hke_cap : ke₀ + inp.G.numVerts * K_iso δ ξ ω ≤ (s₀.arrs a_ekd).length)
    (hbufA : ValidPieceBuffer δ ξ ω inp.G
      (pieceZ inp.G inp.Z (dpEB inp.G inp.p inp.τ 0))
      (dpEB inp.G inp.p inp.τ 0)
      (dpSubtreeTable inp.G inp.Z δ inp.p inp.hp inp.τ 0 inp.ht).toRawList bufA s₀) :
    ∃ s' t_total kv' ke',
      Exec w (isoVertLoopProg δ ξ ω) s₀ s' t_total ∧
      t_total ≤ 5 + inp.G.numVerts * (C_isoStep δ ξ ω + 9) ∧
      kv₀ ≤ kv' ∧ kv' ≤ kv₀ + inp.G.numVerts * K_iso δ ξ ω ∧
      ke₀ ≤ ke' ∧ ke' ≤ ke₀ + inp.G.numVerts * K_iso δ ξ ω ∧
      TreeDPStateInv δ ξ ω inp s' ∧
      ArenaStateInv inp.G kv' ke' s' ∧
      ValidPieceBuffer δ ξ ω inp.G inp.Z Finset.univ
        (computeFolioDP inp.G inp.Z δ inp.ht inp.p inp.hp inp.τ).toRawList bufA s' := by
  have hw8 := hw.hw8
  have h0_w : 0 < 2 ^ w := by omega
  let s₁ := s₀.setReg 9 0
  have hex₁ : Exec w (.assign 9 (.const 0)) s₀ s₁ 2 :=
    .assign (by simp [Expr.eval, checkWord, h0_w])
  have hinv₁ : TreeDPStateInv δ ξ ω inp s₁ := hinv.setReg_ge3 9 (by decide) 0
  have har₁ : ArenaStateInv inp.G kv₀ ke₀ s₁ :=
    har.setReg_ne 9 (by decide) (by decide) 0
  let rootPiece : PieceFolioTable inp.G inp.Z δ Finset.univ :=
    (dpSubtreeTable inp.G inp.Z δ inp.p inp.hp inp.τ 0 inp.ht).castSets
      (by rw [dpEB_zero_eq_univ inp.G inp.hp inp.τ])
      (dpEB_zero_eq_univ inp.G inp.hp inp.τ)
      (by rw [dpEB_zero_eq_univ inp.G inp.hp inp.τ])
  let edgesTable : CertFolioTable inp.G (pieceVB inp.G Finset.univ) Finset.univ
      (finsetRootFn (inp.Z ∩ pieceVB inp.G Finset.univ)) δ :=
    rootPiece.castSets rfl rfl (pieceZ_univ_eq inp.G inp.Z)
  let initAcc : CertFolioTable inp.G (dpVertPrefix inp.G 0) Finset.univ
      (finsetRootFn (inp.Z ∩ dpVertPrefix inp.G 0)) δ :=
    edgesTable.castSets (dpVertPrefix_zero inp.G).symm rfl (by rw [dpVertPrefix_zero])
  have hbufA_init : ValidPieceBuffer δ ξ ω inp.G (inp.Z ∩ dpVertPrefix inp.G 0) Finset.univ
      initAcc.toRawList bufA s₁ := by
    have hbufA₁ : ValidPieceBuffer δ ξ ω inp.G
        (pieceZ inp.G inp.Z (dpEB inp.G inp.p inp.τ 0))
        (dpEB inp.G inp.p inp.τ 0)
        (dpSubtreeTable inp.G inp.Z δ inp.p inp.hp inp.τ 0 inp.ht).toRawList bufA s₁ :=
      hbufA.setReg_ne 9 (by decide) (by decide) (by decide) (by decide) 0
    refine ValidPieceBuffer.of_toSigmaRaw_eq
      (dpEB_zero_eq_univ inp.G inp.hp inp.τ)
      (by rw [dpEB_zero_eq_univ inp.G inp.hp inp.τ, pieceZ_univ_eq, dpVertPrefix_zero])
      ?_ hbufA₁
    simp only [initAcc, edgesTable, rootPiece, CertFolioTable.toSigmaRaw_castSets]
  rcases isoVertLoop_exec inp hw (k := 0) (Nat.zero_le _) initAcc hinv₁ har₁
      (State.setReg_regs_self s₀ 9 0)
      (by simpa using hkv_w) (by simpa using hke_w)
      (by simpa [s₁] using hkv_cap) (by simpa [s₁] using hke_cap)
      hbufA_init with
    ⟨s₂, t_loop, kv', ke', hex_loop, ht_loop, hkv'_ge, hkv'_le, hke'_ge, hke'_le,
     hinv₂, har₂, _, _, hbufA₂⟩
  rw [Nat.sub_zero] at ht_loop hkv'_le hke'_le
  have hbufA_final : ValidPieceBuffer δ ξ ω inp.G inp.Z Finset.univ
      (computeFolioDP inp.G inp.Z δ inp.ht inp.p inp.hp inp.τ).toRawList bufA s₂ := by
    refine ValidPieceBuffer.of_toSigmaRaw_eq rfl
      (by rw [dpVertPrefix_full, Finset.inter_univ])
      ?_ hbufA₂
    simp only [computeFolioDP, addIsolatedVertsTable, initAcc, edgesTable, rootPiece,
      CertFolioTable.toSigmaRaw_castSets]
  exact ⟨s₂, 2 + t_loop, kv', ke', .seq hex₁ hex_loop, by omega,
    hkv'_ge, hkv'_le, hke'_ge, hke'_le,
    hinv₂, har₂, hbufA_final⟩

end GraphMinor.Compute
