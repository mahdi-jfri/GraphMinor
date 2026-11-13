module

public import GraphMinor.Compute.Algorithm41Aux4

/-!
# Base-Step and Boundary-Merge Gadgets for GM XIII Algorithm (4.1)

This file continues the Word RAM implementation of Algorithm (4.1) of Robertson and Seymour,
*Graph Minors. XIII. The Disjoint Paths Problem* (pages 75–76):

1. `toRawList_baseCertFolioTable_eq_canon` and `baseTableFillProg_exec`: execution and correctness
   of `baseTableFillProg`, proving that it populates a `ValidPieceBuffer` for
   `baseCertFolioTable G VA EA (finsetRootFn ZA) δ`.
2. `isoBaseStepProg` and `treeBaseStepProg`: Word RAM programs initializing `bufB` for an isolated
   vertex `v` (`VA = {v}, EA = ∅, ZA = Z ∩ {v}`) and `bufA` for a branch-decomposition tree node `x`
   (`EA = {e | (τ e).1 = x}, VA = pieceVB G EA, ZA = pieceZ G Z EA`), together with their execution
   proofs `isoBaseStepProg_exec` and `treeBaseStepProg_exec`.
-/

@[expose] public section

namespace GraphMinor.Compute

open SimpleGraph

/-! ### Section 1: Correctness and Execution of `baseTableFillProg` -/

theorem State.writeArr_arrs (s : State) (a a' : Arr) (i v : ℕ) :
    (s.writeArr a i v).arrs a' = if a' = a then (s.arrs a).set i v else s.arrs a' := by
  simp [State.writeArr, State.setArr, Function.update_apply]

private theorem sigma_snd_eq_rec {α : Type*} {β : α → Type*} {a₁ a₂ : α} {b₁ : β a₁} {b₂ : β a₂}
    (h : (⟨a₁, b₁⟩ : Sigma β) = ⟨a₂, b₂⟩) :
    ∃ ha : a₂ = a₁, b₁ = ha ▸ b₂ := by
  cases h; exact ⟨rfl, rfl⟩

private theorem evalArena_congr {n : ℕ} {k₁ k₂ v1₁ v1₂ v2₁ v2₂ : List ℕ}
    {p₁ p₂ : ℕ} (hk : k₁ = k₂) (h1 : v1₁ = v1₂) (h2 : v2₁ = v2₂) (hp : p₁ = p₂) :
    evalArena n k₁ v1₁ v2₁ p₁ = evalArena n k₂ v1₂ v2₂ p₂ := by
  subst hk h1 h2 hp; rfl

theorem validPieceBuffer_cast_q {δ ξ ω : ℕ} {G : ComputeDigraph}
    {Z_P : Finset (Fin G.numVerts)} {E_P : Finset (Fin G.numEdges)}
    {q' : ℕ} (hq : q' = Z_P.card) (es : List (RawCertEntry G q'))
    (buf : PieceBufLayout) (s : State) (hq_le : q' ≤ Q_max ξ ω)
    (hlen_le : es.length ≤ (allDetailLeCodes q' δ).length) (hdet : ∀ e ∈ es, e.H.HasDetailLe δ)
    (htid : s.regs buf.r_tid = encAbstractTable δ ξ ω ⟨q', es.map (·.H)⟩)
    (hr_q : s.regs buf.r_q = Z_P.card)
    (hzV_len : (s.arrs buf.a_zV).length = Q_max ξ ω) (hzI_len : (s.arrs buf.a_zI).length = Q_max ξ ω)
    (hzV : ∀ i : Fin Z_P.card, (s.arrs buf.a_zV).getD i.1 0 = (finsetRootFn Z_P i).1)
    (hzI : ∀ i : Fin Z_P.card, (s.arrs buf.a_zI).getD i.1 0 = subInc G E_P (finsetRootFn Z_P i))
    (hvv_len : (s.arrs buf.a_vv).length = S_tab δ ξ ω)
    (hve_len : (s.arrs buf.a_ve).length = S_tab δ ξ ω)
    (hem_len : (s.arrs buf.a_em).length = S_tab δ ξ ω)
    (hentries : ∀ idx : Fin es.length,
      let e := es[idx.1]
      let base := idx.1 * V_max δ ξ ω
      (∀ u : Fin e.H.digraph.numVerts,
        let p_vv := (s.arrs buf.a_vv).getD (base + u.1) 0
        let p_ve := (s.arrs buf.a_ve).getD (base + u.1) 0
        p_vv < s.regs r_kv ∧
        evalArena G.numVerts (s.arrs a_vkd) (s.arrs a_vv1) (s.arrs a_vv2) p_vv = e.vertVerts u ∧
        p_ve < s.regs r_ke ∧
        evalArena G.numEdges (s.arrs a_ekd) (s.arrs a_ev1) (s.arrs a_ev2) p_ve = e.vertEdges u) ∧
      (∀ d : Fin e.H.digraph.numEdges,
        (s.arrs buf.a_em).getD (base + d.1) 0 = (e.edgeMap d).1)) :
    ValidPieceBuffer δ ξ ω G Z_P E_P (hq ▸ es) buf s := by
  subst hq; exact ⟨hq_le, hlen_le, hdet, htid, hr_q, hzV_len, hzI_len, hzV, hzI,
    hvv_len, hve_len, hem_len, hentries⟩

theorem toRawList_baseCertFolioTable_eq_canon {δ : ℕ} (G : ComputeDigraph)
    (VA : Finset (Fin G.numVerts)) (EA : Finset (Fin G.numEdges))
    (ZA : Finset (Fin G.numVerts)) (hZA : ZA ⊆ VA)
    (hEA : ∀ e ∈ EA, G.head e ∈ VA ∧ G.tail e ∈ VA) (bcfg : ℕ)
    (hG_loc : pieceLocDigraph G VA EA hEA = canonLocDigraph bcfg)
    (hZ_loc : ∀ i : Fin VA.card,
      (i ∈ subMaskFinset VA ZA ↔
        (⟨i.1, Nat.lt_of_lt_of_eq i.2 (congrArg ComputeDigraph.numVerts hG_loc)⟩ :
          Fin (canonLocDigraph bcfg).numVerts) ∈ canonLocRoots bcfg)) :
    ∃ hq : (canonLocRoots bcfg).card = ZA.card,
      (baseCertFolioTable G VA EA (finsetRootFn ZA) δ).toRawList =
        hq ▸ ((canonBaseRawList δ bcfg).map
          (RawCertEntry.mapEmb
            (fun i => finsetRootFn VA
              ⟨i.1, Nat.lt_of_lt_of_eq i.2 (congrArg ComputeDigraph.numVerts hG_loc).symm⟩)
            (fun d => finsetRootFn EA
              ⟨d.1, Nat.lt_of_lt_of_eq d.2 (congrArg ComputeDigraph.numEdges hG_loc).symm⟩))) := by
  have h1 := toSigmaRaw_baseCertFolioTable (δ := δ) G VA EA ZA hZA hEA
  dsimp only [CertFolioTable.toSigmaRaw] at h1
  have hn_loc : VA.card = (canonLocDigraph bcfg).numVerts :=
    congrArg ComputeDigraph.numVerts hG_loc
  have hm_loc : EA.card = (canonLocDigraph bcfg).numEdges :=
    congrArg ComputeDigraph.numEdges hG_loc
  have h2 := baseRawList_congr (δ := δ) (Z₁ := subMaskFinset VA ZA) (Z₂ := canonLocRoots bcfg)
    (fV₁ := finsetRootFn VA)
    (fV₂ := fun i => finsetRootFn VA ⟨i.1, Nat.lt_of_lt_of_eq i.2 hn_loc.symm⟩)
    (fE₁ := finsetRootFn EA)
    (fE₂ := fun d => finsetRootFn EA ⟨d.1, Nat.lt_of_lt_of_eq d.2 hm_loc.symm⟩)
    hG_loc hZ_loc (fun _ => rfl) (fun _ => rfl)
  exact sigma_snd_eq_rec (h1.trans h2)

private theorem baseVVCode_eq (δ ξ ω bcfg pos i u : ℕ)
    (hd : pos / V_max δ ξ ω = i) (hm : pos % V_max δ ξ ω = u)
    (hi : i < (canonBaseRawList δ bcfg).length)
    (hu : u < (canonBaseRawList δ bcfg)[i].H.digraph.numVerts) :
    baseVVCode δ ξ ω bcfg pos =
      (if decide (∃ x ∈ (canonBaseRawList δ bcfg)[i].vertVerts ⟨u, hu⟩, x.1 = 0) then 1 else 0) +
      (if decide (∃ x ∈ (canonBaseRawList δ bcfg)[i].vertVerts ⟨u, hu⟩, x.1 = 1) then 2 else 0) := by
  unfold baseVVCode; revert hd hm
  generalize pos / V_max δ ξ ω = i', pos % V_max δ ξ ω = u'
  rintro rfl rfl; simp [hi, hu]

private theorem baseVECode_eq (δ ξ ω bcfg pos i u : ℕ)
    (hd : pos / V_max δ ξ ω = i) (hm : pos % V_max δ ξ ω = u)
    (hi : i < (canonBaseRawList δ bcfg).length)
    (hu : u < (canonBaseRawList δ bcfg)[i].H.digraph.numVerts) :
    baseVECode δ ξ ω bcfg pos =
      if decide (∃ d ∈ (canonBaseRawList δ bcfg)[i].vertEdges ⟨u, hu⟩, d.1 = 0) then 1 else 0 := by
  unfold baseVECode; revert hd hm
  generalize pos / V_max δ ξ ω = i', pos % V_max δ ξ ω = u'
  rintro rfl rfl; simp [hi, hu]

theorem validPieceBuffer_of_baseTableFill {δ ξ ω : ℕ} {G : ComputeDigraph}
    {VA : Finset (Fin G.numVerts)} {EA : Finset (Fin G.numEdges)}
    {ZA : Finset (Fin G.numVerts)} (hZA : ZA ⊆ VA)
    (hEA : ∀ e ∈ EA, G.head e ∈ VA ∧ G.tail e ∈ VA)
    {bcfg kv₀ ke₀ : ℕ} {buf : PieceBufLayout} {s s' : State}
    (hG_loc : pieceLocDigraph G VA EA hEA = canonLocDigraph bcfg)
    (hZ_loc : ∀ i : Fin VA.card,
      (i ∈ subMaskFinset VA ZA ↔
        (⟨i.1, Nat.lt_of_lt_of_eq i.2 (congrArg ComputeDigraph.numVerts hG_loc)⟩ :
          Fin (canonLocDigraph bcfg).numVerts) ∈ canonLocRoots bcfg))
    (hkv0_pos : 1 ≤ kv₀) (hke0_pos : 1 ≤ ke₀)
    (hkv_cap : kv₀ + 3 ≤ (s.arrs a_vkd).length) (hke_cap : ke₀ + 1 ≤ (s.arrs a_ekd).length)
    (hlen_vv1 : (s.arrs a_vv1).length = (s.arrs a_vkd).length)
    (hlen_vv2 : (s.arrs a_vv2).length = (s.arrs a_vkd).length)
    (hlen_ev1 : (s.arrs a_ev1).length = (s.arrs a_ekd).length)
    (htid' : s'.regs buf.r_tid =
      encAbstractTable δ ξ ω ⟨(canonLocRoots bcfg).card, (canonBaseRawList δ bcfg).map (·.H)⟩)
    (hr_q' : s'.regs buf.r_q = ZA.card)
    (hr_kv' : s'.regs r_kv = kv₀ + 3) (hr_ke' : s'.regs r_ke = ke₀ + 1)
    (hzV_len' : (s'.arrs buf.a_zV).length = Q_max ξ ω)
    (hzI_len' : (s'.arrs buf.a_zI).length = Q_max ξ ω)
    (hzV' : ∀ i : Fin ZA.card, (s'.arrs buf.a_zV).getD i.1 0 = (finsetRootFn ZA i).1)
    (hzI' : ∀ i : Fin ZA.card, (s'.arrs buf.a_zI).getD i.1 0 = subInc G EA (finsetRootFn ZA i))
    (hvv_len' : (s'.arrs buf.a_vv).length = S_tab δ ξ ω)
    (hve_len' : (s'.arrs buf.a_ve).length = S_tab δ ξ ω)
    (hem_len' : (s'.arrs buf.a_em).length = S_tab δ ξ ω)
    (hs'_vkd : s'.arrs a_vkd =
      (((s.arrs a_vkd).set kv₀ (if 0 < VA.card then 1 else 0)).set
        (kv₀ + 1) (if 1 < VA.card then 1 else 0)).set (kv₀ + 2) 2)
    (hs'_vv1 : s'.arrs a_vv1 =
      (((s.arrs a_vv1).set kv₀ (if h0 : 0 < VA.card then (finsetRootFn VA ⟨0, h0⟩).1 else 0)).set
        (kv₀ + 1) (if h1 : 1 < VA.card then (finsetRootFn VA ⟨1, h1⟩).1 else 0)).set (kv₀ + 2) kv₀)
    (hs'_vv2 : s'.arrs a_vv2 =
      (((s.arrs a_vv2).set kv₀ 0).set (kv₀ + 1) 0).set (kv₀ + 2) (kv₀ + 1))
    (hs'_ekd : s'.arrs a_ekd = (s.arrs a_ekd).set ke₀ (if 0 < EA.card then 1 else 0))
    (hs'_ev1 : s'.arrs a_ev1 =
      (s.arrs a_ev1).set ke₀ (if he : 0 < EA.card then (finsetRootFn EA ⟨0, he⟩).1 else 0))
    (hs'_ev2 : s'.arrs a_ev2 = (s.arrs a_ev2).set ke₀ 0)
    (hpos' : ∀ pos < S_tab δ ξ ω,
      (s'.arrs buf.a_vv).getD pos 0 = baseVVVal kv₀ (baseVVCode δ ξ ω bcfg pos) ∧
      (s'.arrs buf.a_ve).getD pos 0 = baseVEVal ke₀ (baseVECode δ ξ ω bcfg pos) ∧
      (s'.arrs buf.a_em).getD pos 0 =
        if he : 0 < EA.card then (finsetRootFn EA ⟨0, he⟩).1 else 0) :
    ValidPieceBuffer δ ξ ω G ZA EA
      (baseCertFolioTable G VA EA (finsetRootFn ZA) δ).toRawList buf s' := by
  rcases toRawList_baseCertFolioTable_eq_canon (δ := δ) G VA EA ZA hZA hEA bcfg hG_loc hZ_loc
    with ⟨hq_eq, hraw_eq⟩
  rw [hraw_eq]
  have hn_loc : VA.card = (canonLocDigraph bcfg).numVerts := congrArg ComputeDigraph.numVerts hG_loc
  have hm_loc : EA.card = (canonLocDigraph bcfg).numEdges := congrArg ComputeDigraph.numEdges hG_loc
  let fV : Fin (canonLocDigraph bcfg).numVerts → Fin G.numVerts :=
    fun i => finsetRootFn VA ⟨i.1, Nat.lt_of_lt_of_eq i.2 hn_loc.symm⟩
  let fE : Fin (canonLocDigraph bcfg).numEdges → Fin G.numEdges :=
    fun d => finsetRootFn EA ⟨d.1, Nat.lt_of_lt_of_eq d.2 hm_loc.symm⟩
  let es_canon := canonBaseRawList δ bcfg
  have hmap_H : (es_canon.map (RawCertEntry.mapEmb fV fE)).map (·.H) = es_canon.map (·.H) := by
    rw [List.map_map]; rfl
  refine validPieceBuffer_cast_q hq_eq (es_canon.map (RawCertEntry.mapEmb fV fE)) buf s'
    (card_canonLocRoots_le_two ξ ω bcfg).2
    (by simp only [List.length_map]; exact length_canonBaseRawList_le δ bcfg)
    (fun e he => by
      rcases List.mem_map.mp he with ⟨e₀, he₀, rfl⟩; exact hasDetailLe_of_mem_canonBaseRawList he₀)
    (by rw [htid', hmap_H])
    hr_q' hzV_len' hzI_len' hzV' hzI' hvv_len' hve_len' hem_len' ?_
  intro idx
  have hidx : idx.1 < es_canon.length := by simpa using idx.2
  let e₀ := es_canon[idx.1]'hidx
  have he₀_mem : e₀ ∈ es_canon := List.getElem_mem hidx
  have hdet₀ : e₀.H.HasDetailLe δ := hasDetailLe_of_mem_canonBaseRawList he₀_mem
  have hidx_C : idx.1 < C_max δ ξ ω :=
    Nat.lt_of_lt_of_le hidx (Nat.le_trans (length_canonBaseRawList_le δ bcfg)
      (Nat.le_of_lt (length_allDetailLeCodes_lt_C_max δ ξ ω (card_canonLocRoots_le_two ξ ω bcfg).2)))
  have hget_map : (es_canon.map (RawCertEntry.mapEmb fV fE))[idx.1] =
      RawCertEntry.mapEmb fV fE e₀ := List.getElem_map _
  dsimp only; rw [hget_map]; dsimp only [RawCertEntry.mapEmb]
  refine ⟨fun u => ?_, fun d => ?_⟩
  · have hu_V : u.1 < V_max δ ξ ω :=
      Nat.lt_trans u.2 (numVerts_lt_V_max (card_canonLocRoots_le_two ξ ω bcfg).2 hdet₀)
    let pos := idx.1 * V_max δ ξ ω + u.1
    have hpos_S : pos < S_tab δ ξ ω := by
      unfold S_tab; have := Nat.mul_le_mul_right (V_max δ ξ ω) hidx_C
      rw [Nat.succ_mul] at this; omega
    rcases hpos' pos hpos_S with ⟨hvv_pos, hve_pos, _⟩
    have hdiv_pos : pos / V_max δ ξ ω = idx.1 := by
      dsimp [pos]; rw [Nat.mul_comm idx.1 (V_max δ ξ ω),
        Nat.mul_add_div (V_max_pos δ ξ ω), Nat.div_eq_of_lt hu_V, Nat.add_zero]
    have hmod_pos : pos % V_max δ ξ ω = u.1 := by
      dsimp [pos]; rw [Nat.mul_comm idx.1 (V_max δ ξ ω), Nat.mul_add_mod, Nat.mod_eq_of_lt hu_V]
    have hcode_vv := baseVVCode_eq δ ξ ω bcfg pos idx.1 u.1 hdiv_pos hmod_pos hidx u.2
    have hcode_ve := baseVECode_eq δ ξ ω bcfg pos idx.1 u.1 hdiv_pos hmod_pos hidx u.2
    have hev_vv := evalArena_baseVVVal (n := G.numVerts) (kv₀ := kv₀) (bcfg := bcfg)
      hkv0_pos (L_vkd := s.arrs a_vkd) (L_vv1 := s.arrs a_vv1) (L_vv2 := s.arrs a_vv2)
      (by omega) (by omega) (by omega) VA hn_loc (e₀.vertVerts u)
    have hev_ve := evalArena_baseVEVal (m := G.numEdges) (ke₀ := ke₀) (bcfg := bcfg)
      hke0_pos (L_ekd := s.arrs a_ekd) (L_ev1 := s.arrs a_ev1) (L_ev2 := s.arrs a_ev2)
      (by omega) (by omega) EA hm_loc (e₀.vertEdges u)
    have hp_vv : (s'.arrs buf.a_vv).getD pos 0 =
        baseVVVal kv₀ ((if decide (∃ i ∈ e₀.vertVerts u, i.1 = 0) then 1 else 0) +
          (if decide (∃ i ∈ e₀.vertVerts u, i.1 = 1) then 2 else 0)) := by rw [hvv_pos, hcode_vv]
    have hp_ve : (s'.arrs buf.a_ve).getD pos 0 =
        baseVEVal ke₀ (if decide (∃ d ∈ e₀.vertEdges u, d.1 = 0) then 1 else 0) := by
      rw [hve_pos, hcode_ve]
    refine ⟨by rw [hp_vv, hr_kv']; exact hev_vv.1,
      (evalArena_congr hs'_vkd hs'_vv1 hs'_vv2 hp_vv).trans hev_vv.2,
      by rw [hp_ve, hr_ke']; exact hev_ve.1,
      (evalArena_congr hs'_ekd hs'_ev1 hs'_ev2 hp_ve).trans hev_ve.2⟩
  · have hd_V : d.1 < V_max δ ξ ω := Nat.lt_trans d.2 (numEdges_lt_V_max hdet₀)
    let pos := idx.1 * V_max δ ξ ω + d.1
    have hpos_S : pos < S_tab δ ξ ω := by
      unfold S_tab; have := Nat.mul_le_mul_right (V_max δ ξ ω) hidx_C
      rw [Nat.succ_mul] at this; omega
    rcases hpos' pos hpos_S with ⟨_, _, hem_pos⟩
    rw [hem_pos]
    have hm_le1 : (canonLocDigraph bcfg).numEdges ≤ 1 := by
      change (if bcfg % 3 = 0 then 0 else (bcfg / 3) % 2) ≤ 1; split_ifs <;> omega
    have hd0 : (e₀.edgeMap d).1 = 0 := by have := (e₀.edgeMap d).2; omega
    have he_pos : 0 < EA.card := by have := (e₀.edgeMap d).2; omega
    dsimp [fE]; simp only [he_pos, ↓reduceDIte]; congr 2; exact Fin.ext hd0.symm

theorem arenaWF_after_basePush {G : ComputeDigraph}
    {VA : Finset (Fin G.numVerts)} {EA : Finset (Fin G.numEdges)}
    {kv₀ ke₀ : ℕ} {s s' : State}
    (hwfV : ArenaWF G.numVerts kv₀ (s.arrs a_vkd) (s.arrs a_vv1) (s.arrs a_vv2))
    (hwfE : ArenaWF G.numEdges ke₀ (s.arrs a_ekd) (s.arrs a_ev1) (s.arrs a_ev2))
    (hkv_cap : kv₀ + 3 ≤ (s.arrs a_vkd).length) (hke_cap : ke₀ + 1 ≤ (s.arrs a_ekd).length)
    (hs'_vkd : s'.arrs a_vkd =
      (((s.arrs a_vkd).set kv₀ (if 0 < VA.card then 1 else 0)).set
        (kv₀ + 1) (if 1 < VA.card then 1 else 0)).set (kv₀ + 2) 2)
    (hs'_vv1 : s'.arrs a_vv1 =
      (((s.arrs a_vv1).set kv₀ (if h0 : 0 < VA.card then (finsetRootFn VA ⟨0, h0⟩).1 else 0)).set
        (kv₀ + 1) (if h1 : 1 < VA.card then (finsetRootFn VA ⟨1, h1⟩).1 else 0)).set (kv₀ + 2) kv₀)
    (hs'_vv2 : s'.arrs a_vv2 =
      (((s.arrs a_vv2).set kv₀ 0).set (kv₀ + 1) 0).set (kv₀ + 2) (kv₀ + 1))
    (hs'_ekd : s'.arrs a_ekd = (s.arrs a_ekd).set ke₀ (if 0 < EA.card then 1 else 0))
    (hs'_ev1 : s'.arrs a_ev1 =
      (s.arrs a_ev1).set ke₀ (if he : 0 < EA.card then (finsetRootFn EA ⟨0, he⟩).1 else 0))
    (hs'_ev2 : s'.arrs a_ev2 = (s.arrs a_ev2).set ke₀ 0) :
    ArenaWF G.numVerts (kv₀ + 3) (s'.arrs a_vkd) (s'.arrs a_vv1) (s'.arrs a_vv2) ∧
    ArenaWF G.numEdges (ke₀ + 1) (s'.arrs a_ekd) (s'.arrs a_ev1) (s'.arrs a_ev2) ∧
    (∀ p < kv₀,
      evalArena G.numVerts (s'.arrs a_vkd) (s'.arrs a_vv1) (s'.arrs a_vv2) p =
        evalArena G.numVerts (s.arrs a_vkd) (s.arrs a_vv1) (s.arrs a_vv2) p) ∧
    (∀ p < ke₀,
      evalArena G.numEdges (s'.arrs a_ekd) (s'.arrs a_ev1) (s'.arrs a_ev2) p =
        evalArena G.numEdges (s.arrs a_ekd) (s.arrs a_ev1) (s.arrs a_ev2) p) := by
  let kd_v0 := if 0 < VA.card then 1 else 0
  let v0 := if h0 : 0 < VA.card then (finsetRootFn VA ⟨0, h0⟩).1 else 0
  let kd_v1 := if 1 < VA.card then 1 else 0
  let v1 := if h1 : 1 < VA.card then (finsetRootFn VA ⟨1, h1⟩).1 else 0
  have hwfV1 : ArenaWF G.numVerts (kv₀ + 1)
      ((s.arrs a_vkd).set kv₀ kd_v0) ((s.arrs a_vv1).set kv₀ v0) ((s.arrs a_vv2).set kv₀ 0) := by
    dsimp [kd_v0, v0]; split_ifs with h0
    · exact arenaWF_step_singleton hwfV (by omega) (finsetRootFn VA ⟨0, h0⟩).2
    · exact arenaWF_step_empty hwfV (by omega)
  have hwfV2 : ArenaWF G.numVerts (kv₀ + 2)
      (((s.arrs a_vkd).set kv₀ kd_v0).set (kv₀ + 1) kd_v1)
      (((s.arrs a_vv1).set kv₀ v0).set (kv₀ + 1) v1)
      (((s.arrs a_vv2).set kv₀ 0).set (kv₀ + 1) 0) := by
    dsimp [kd_v1, v1]; split_ifs with h1
    · exact arenaWF_step_singleton hwfV1 (by simp; omega) (finsetRootFn VA ⟨1, h1⟩).2
    · exact arenaWF_step_empty hwfV1 (by simp; omega)
  have hwfV3 : ArenaWF G.numVerts (kv₀ + 3) (s'.arrs a_vkd) (s'.arrs a_vv1) (s'.arrs a_vv2) := by
    rw [hs'_vkd, hs'_vv1, hs'_vv2]
    exact arenaWF_step_union hwfV2 (by simp; omega) (by omega) (by omega)
  have hwfE1 : ArenaWF G.numEdges (ke₀ + 1) (s'.arrs a_ekd) (s'.arrs a_ev1) (s'.arrs a_ev2) := by
    rw [hs'_ekd, hs'_ev1, hs'_ev2]; split_ifs with he
    · exact arenaWF_step_singleton hwfE (by omega) (finsetRootFn EA ⟨0, he⟩).2
    · exact arenaWF_step_empty hwfE (by omega)
  refine ⟨hwfV3, hwfE1, fun p hp => ?_, fun p hp => ?_⟩
  · exact (evalArena_congr hs'_vkd hs'_vv1 hs'_vv2 rfl).trans
      ((evalArena_set_gt _ _ _ _ (kv₀ + 2) 2 kv₀ (kv₀ + 1) p (by omega)).trans
        ((evalArena_set_gt _ _ _ _ (kv₀ + 1) _ _ 0 p (by omega)).trans
          (evalArena_set_gt _ _ _ _ kv₀ _ _ 0 p hp)))
  · exact (evalArena_congr hs'_ekd hs'_ev1 hs'_ev2 rfl).trans
      (evalArena_set_gt _ _ _ _ ke₀ _ _ 0 p hp)

theorem baseTableFillProg_exec {w δ ξ ω : ℕ} {G : ComputeDigraph}
    {VA : Finset (Fin G.numVerts)} {EA : Finset (Fin G.numEdges)}
    {ZA : Finset (Fin G.numVerts)} (hZA : ZA ⊆ VA)
    (hEA : ∀ e ∈ EA, G.head e ∈ VA ∧ G.tail e ∈ VA)
    {bcfg kv₀ ke₀ : ℕ} {buf : PieceBufLayout} {s : State} (hbcfg_lt : bcfg < 72)
    (hG_loc : pieceLocDigraph G VA EA hEA = canonLocDigraph bcfg)
    (hZ_loc : ∀ i : Fin VA.card,
      (i ∈ subMaskFinset VA ZA ↔
        (⟨i.1, Nat.lt_of_lt_of_eq i.2 (congrArg ComputeDigraph.numVerts hG_loc)⟩ :
          Fin (canonLocDigraph bcfg).numVerts) ∈ canonLocRoots bcfg))
    (hvv_ve : buf.a_vv ≠ buf.a_ve) (hvv_em : buf.a_vv ≠ buf.a_em) (hve_em : buf.a_ve ≠ buf.a_em)
    (hzV_vv : buf.a_zV ≠ buf.a_vv) (hzV_ve : buf.a_zV ≠ buf.a_ve) (hzV_em : buf.a_zV ≠ buf.a_em)
    (hzI_vv : buf.a_zI ≠ buf.a_vv) (hzI_ve : buf.a_zI ≠ buf.a_ve) (hzI_em : buf.a_zI ≠ buf.a_em)
    (hbuf_arena :
      ∀ a ∈ [a_vkd, a_vv1, a_vv2, a_ekd, a_ev1, a_ev2],
        a ≠ buf.a_zV ∧ a ≠ buf.a_zI ∧ a ≠ buf.a_vv ∧ a ≠ buf.a_ve ∧ a ≠ buf.a_em)
    (hrt_lt : buf.r_tid < 10) (_hrq_lt : buf.r_q < 10) (hrt_ne_rq : buf.r_tid ≠ buf.r_q)
    (hrt_ne_kv : buf.r_tid ≠ r_kv) (hrt_ne_ke : buf.r_tid ≠ r_ke)
    (hrq_ne_kv : buf.r_q ≠ r_kv) (hrq_ne_ke : buf.r_q ≠ r_ke)
    (hw72 : 72 < 2 ^ w) (hn_w : G.numVerts < 2 ^ w) (hm_w : G.numEdges < 2 ^ w)
    (hS_w : S_tab δ ξ ω < 2 ^ w) (hT_w : T_max δ ξ ω < 2 ^ w)
    (hkv_w : kv₀ + 3 < 2 ^ w) (hke_w : ke₀ + 1 < 2 ^ w)
    (hwfV : ArenaWF G.numVerts kv₀ (s.arrs a_vkd) (s.arrs a_vv1) (s.arrs a_vv2))
    (hwfE : ArenaWF G.numEdges ke₀ (s.arrs a_ekd) (s.arrs a_ev1) (s.arrs a_ev2))
    (hkv_cap : kv₀ + 3 ≤ (s.arrs a_vkd).length) (hke_cap : ke₀ + 1 ≤ (s.arrs a_ekd).length)
    (hr_kv : s.regs r_kv = kv₀) (hr_ke : s.regs r_ke = ke₀)
    (hr10 : s.regs 10 = if h0 : 0 < VA.card then (finsetRootFn VA ⟨0, h0⟩).1 else 0)
    (hr11 : s.regs 11 = if h1 : 1 < VA.card then (finsetRootFn VA ⟨1, h1⟩).1 else 0)
    (hr12 : s.regs 12 = if he : 0 < EA.card then (finsetRootFn EA ⟨0, he⟩).1 else 0)
    (hr13 : s.regs 13 = bcfg)
    (hr16 : s.regs 16 = if 0 < VA.card then 1 else 0)
    (hr17 : s.regs 17 = if 1 < VA.card then 1 else 0)
    (hr18 : s.regs 18 = if 0 < EA.card then 1 else 0)
    (hr_q : s.regs buf.r_q = ZA.card)
    (hzV_len : (s.arrs buf.a_zV).length = Q_max ξ ω)
    (hzI_len : (s.arrs buf.a_zI).length = Q_max ξ ω)
    (hzV : ∀ i : Fin ZA.card, (s.arrs buf.a_zV).getD i.1 0 = (finsetRootFn ZA i).1)
    (hzI : ∀ i : Fin ZA.card, (s.arrs buf.a_zI).getD i.1 0 = subInc G EA (finsetRootFn ZA i))
    (hvv_len : (s.arrs buf.a_vv).length = S_tab δ ξ ω)
    (hve_len : (s.arrs buf.a_ve).length = S_tab δ ξ ω)
    (hem_len : (s.arrs buf.a_em).length = S_tab δ ξ ω) :
    ∃ s' t_step,
      Exec w (baseTableFillProg δ ξ ω buf) s s' t_step ∧
      t_step ≤ 300 + 15 * S_tab δ ξ ω ∧
      s'.regs r_kv = kv₀ + 3 ∧ s'.regs r_ke = ke₀ + 1 ∧
      ArenaWF G.numVerts (kv₀ + 3) (s'.arrs a_vkd) (s'.arrs a_vv1) (s'.arrs a_vv2) ∧
      ArenaWF G.numEdges (ke₀ + 1) (s'.arrs a_ekd) (s'.arrs a_ev1) (s'.arrs a_ev2) ∧
      (s'.arrs a_vkd).length = (s.arrs a_vkd).length ∧
      (s'.arrs a_ekd).length = (s.arrs a_ekd).length ∧
      (∀ p < kv₀,
        evalArena G.numVerts (s'.arrs a_vkd) (s'.arrs a_vv1) (s'.arrs a_vv2) p =
          evalArena G.numVerts (s.arrs a_vkd) (s.arrs a_vv1) (s.arrs a_vv2) p) ∧
      (∀ p < ke₀,
        evalArena G.numEdges (s'.arrs a_ekd) (s'.arrs a_ev1) (s'.arrs a_ev2) p =
          evalArena G.numEdges (s.arrs a_ekd) (s.arrs a_ev1) (s.arrs a_ev2) p) ∧
      ValidPieceBuffer δ ξ ω G ZA EA
        (baseCertFolioTable G VA EA (finsetRootFn ZA) δ).toRawList buf s' ∧
      (∀ r < 10, r ≠ r_kv → r ≠ r_ke → r ≠ buf.r_tid → s'.regs r = s.regs r) ∧
      (∀ a, a ≠ a_vkd → a ≠ a_vv1 → a ≠ a_vv2 → a ≠ a_ekd → a ≠ a_ev1 → a ≠ a_ev2 →
        a ≠ buf.a_vv → a ≠ buf.a_ve → a ≠ buf.a_em → s'.arrs a = s.arrs a) := by
  have hw_pos : 0 < w := by by_contra h0; obtain rfl : w = 0 := (by omega); simp at hw72
  have h0_w : 0 < 2 ^ w := by omega
  have hw1 : 1 < 2 ^ w := by omega
  have hw2 : 2 < 2 ^ w := by omega
  have hkv0_pos : 1 ≤ kv₀ := hwfV.1
  have hke0_pos : 1 ≤ ke₀ := hwfE.1
  have hlen_vv1 : (s.arrs a_vv1).length = (s.arrs a_vkd).length := hwfV.2.2.1
  have hlen_vv2 : (s.arrs a_vv2).length = (s.arrs a_vkd).length := hwfV.2.2.2.1
  have hlen_ev1 : (s.arrs a_ev1).length = (s.arrs a_ekd).length := hwfE.2.2.1
  have hlen_ev2 : (s.arrs a_ev2).length = (s.arrs a_ekd).length := hwfE.2.2.2.1
  let v0 := if h0 : 0 < VA.card then (finsetRootFn VA ⟨0, h0⟩).1 else 0
  let v1 := if h1 : 1 < VA.card then (finsetRootFn VA ⟨1, h1⟩).1 else 0
  let e0 := if he : 0 < EA.card then (finsetRootFn EA ⟨0, he⟩).1 else 0
  let kd_v0 := if 0 < VA.card then 1 else 0
  let kd_v1 := if 1 < VA.card then 1 else 0
  let kd_e0 := if 0 < EA.card then 1 else 0
  have hv0_w : v0 < 2 ^ w := by
    dsimp [v0]; split_ifs with h0 <;> [exact Nat.lt_trans (finsetRootFn VA ⟨0, h0⟩).2 hn_w; exact h0_w]
  have hv1_w : v1 < 2 ^ w := by
    dsimp [v1]; split_ifs with h1 <;> [exact Nat.lt_trans (finsetRootFn VA ⟨1, h1⟩).2 hn_w; exact h0_w]
  have he0_w : e0 < 2 ^ w := by
    dsimp [e0]; split_ifs with he <;> [exact Nat.lt_trans (finsetRootFn EA ⟨0, he⟩).2 hm_w; exact h0_w]
  have hkd_v0_w : kd_v0 < 2 ^ w := by dsimp [kd_v0]; split_ifs <;> omega
  have hkd_v1_w : kd_v1 < 2 ^ w := by dsimp [kd_v1]; split_ifs <;> omega
  have hkd_e0_w : kd_e0 < 2 ^ w := by dsimp [kd_e0]; split_ifs <;> omega
  have hr10' : s.regs 10 = v0 := hr10
  have hr11' : s.regs 11 = v1 := hr11
  have hr12' : s.regs 12 = e0 := hr12
  have hr16' : s.regs 16 = kd_v0 := hr16
  have hr17' : s.regs 17 = kd_v1 := hr17
  have hr18' : s.regs 18 = kd_e0 := hr18
  -- 1. `r_14 := r_kv`, `r_15 := r_ke`
  let s₁ := (s.setReg 14 kv₀).setReg 15 ke₀
  have hex₁ : Exec w (.assign 14 (.reg r_kv)) s (s.setReg 14 kv₀) 2 :=
    .assign (by simp [Expr.eval, checkWord, hr_kv, show kv₀ < 2 ^ w by omega])
  have hex₂ : Exec w (.assign 15 (.reg r_ke)) (s.setReg 14 kv₀) s₁ 2 :=
    .assign (by simp [Expr.eval, checkWord, hr_ke, show ke₀ < 2 ^ w by omega])
  -- 2. Push node `kv₀`: `(kd_v0, v0, 0)`
  rcases pushArenaNodeProg_exec (w := w) (a_kd := a_vkd) (a_v1 := a_vv1) (a_v2 := a_vv2)
      (r_k := r_kv) (e_kd := .reg 16) (e_v1 := .reg 10) (e_v2 := .const 0)
      (s := s₁) (K := kv₀) (kd := kd_v0) (v1 := v0) (v2 := 0)
      (by decide) (by decide) (by decide) hw1 (by omega)
      (by simp -zeta [s₁, hr_kv])
      (by simp -zeta [s₁]; omega) (by simp -zeta [s₁]; omega) (by simp -zeta [s₁]; omega)
      (by simp -zeta [s₁, Expr.eval, checkWord, hr16', hkd_v0_w])
      (by simp -zeta [s₁, Expr.eval, checkWord, hr10', hv0_w])
      (by simp -zeta [Expr.eval, checkWord, h0_w]) with ⟨t₃, ht₃, hex₃⟩
  let s₂ := (((s₁.writeArr a_vkd kv₀ kd_v0).writeArr a_vv1 kv₀ v0).writeArr a_vv2 kv₀ 0).setReg
    r_kv (kv₀ + 1)
  -- 3. Push node `kv₀ + 1`: `(kd_v1, v1, 0)`
  rcases pushArenaNodeProg_exec (w := w) (a_kd := a_vkd) (a_v1 := a_vv1) (a_v2 := a_vv2)
      (r_k := r_kv) (e_kd := .reg 17) (e_v1 := .reg 11) (e_v2 := .const 0)
      (s := s₂) (K := kv₀ + 1) (kd := kd_v1) (v1 := v1) (v2 := 0)
      (by decide) (by decide) (by decide) hw1 (by omega) (by simp -zeta [s₂])
      (by simp -zeta [s₂, s₁]; omega) (by simp -zeta [s₂, s₁]; omega) (by simp -zeta [s₂, s₁]; omega)
      (by simp -zeta [s₂, s₁, Expr.eval, checkWord, hr17', hkd_v1_w])
      (by simp -zeta [s₂, s₁, Expr.eval, checkWord, hr11', hv1_w])
      (by simp -zeta [Expr.eval, checkWord, h0_w]) with ⟨t₄, ht₄, hex₄⟩
  let s₃ := (((s₂.writeArr a_vkd (kv₀ + 1) kd_v1).writeArr
    a_vv1 (kv₀ + 1) v1).writeArr a_vv2 (kv₀ + 1) 0).setReg r_kv (kv₀ + 2)
  -- 4. Push node `kv₀ + 2`: `(2, kv₀, kv₀ + 1)`
  rcases pushArenaNodeProg_exec (w := w) (a_kd := a_vkd) (a_v1 := a_vv1) (a_v2 := a_vv2)
      (r_k := r_kv) (e_kd := .const 2) (e_v1 := .reg 14) (e_v2 := .op .add (.reg 14) (.const 1))
      (s := s₃) (K := kv₀ + 2) (kd := 2) (v1 := kv₀) (v2 := kv₀ + 1)
      (by decide) (by decide) (by decide) hw1 (by omega) (by simp -zeta [s₃])
      (by simp -zeta [s₃, s₂, s₁]; omega) (by simp -zeta [s₃, s₂, s₁]; omega)
      (by simp -zeta [s₃, s₂, s₁]; omega) (by simp -zeta [Expr.eval, checkWord, hw2])
      (by simp -zeta [s₃, s₂, s₁, Expr.eval, checkWord, show kv₀ < 2 ^ w by omega])
      (by simp -zeta [s₃, s₂, s₁, Expr.eval, BinOp.eval, BinOp.raw, checkWord,
            hw1, show kv₀ < 2 ^ w by omega, show kv₀ + 1 < 2 ^ w by omega]) with ⟨t₅, ht₅, hex₅⟩
  let s₄ := (((s₃.writeArr a_vkd (kv₀ + 2) 2).writeArr
    a_vv1 (kv₀ + 2) kv₀).writeArr a_vv2 (kv₀ + 2) (kv₀ + 1)).setReg r_kv (kv₀ + 3)
  -- 5. Push node `ke₀`: `(kd_e0, e0, 0)`
  rcases pushArenaNodeProg_exec (w := w) (a_kd := a_ekd) (a_v1 := a_ev1) (a_v2 := a_ev2)
      (r_k := r_ke) (e_kd := .reg 18) (e_v1 := .reg 12) (e_v2 := .const 0)
      (s := s₄) (K := ke₀) (kd := kd_e0) (v1 := e0) (v2 := 0)
      (by decide) (by decide) (by decide) hw1 (by omega)
      (by simp -zeta [s₄, s₃, s₂, s₁, hr_ke])
      (by simp -zeta [s₄, s₃, s₂, s₁]; omega) (by simp -zeta [s₄, s₃, s₂, s₁]; omega)
      (by simp -zeta [s₄, s₃, s₂, s₁]; omega)
      (by simp -zeta [s₄, s₃, s₂, s₁, Expr.eval, checkWord, hr18', hkd_e0_w])
      (by simp -zeta [s₄, s₃, s₂, s₁, Expr.eval, checkWord, hr12', he0_w])
      (by simp -zeta [Expr.eval, checkWord, h0_w]) with ⟨t₆, ht₆, hex₆⟩
  let s₅ := (((s₄.writeArr a_ekd ke₀ kd_e0).writeArr
    a_ev1 ke₀ e0).writeArr a_ev2 ke₀ 0).setReg r_ke (ke₀ + 1)
  -- 6. Execute `branchOnBound 72 13 (baseTableBodyProg δ ξ ω buf)` from `s₅`
  have h1 : a_vkd ≠ buf.a_vv ∧ a_vkd ≠ buf.a_ve ∧ a_vkd ≠ buf.a_em ∧ a_vkd ≠ buf.a_zV ∧ a_vkd ≠ buf.a_zI := by
    have := hbuf_arena a_vkd (by simp); tauto
  have h2 : a_vv1 ≠ buf.a_vv ∧ a_vv1 ≠ buf.a_ve ∧ a_vv1 ≠ buf.a_em ∧ a_vv1 ≠ buf.a_zV ∧ a_vv1 ≠ buf.a_zI := by
    have := hbuf_arena a_vv1 (by simp); tauto
  have h3 : a_vv2 ≠ buf.a_vv ∧ a_vv2 ≠ buf.a_ve ∧ a_vv2 ≠ buf.a_em ∧ a_vv2 ≠ buf.a_zV ∧ a_vv2 ≠ buf.a_zI := by
    have := hbuf_arena a_vv2 (by simp); tauto
  have h4 : a_ekd ≠ buf.a_vv ∧ a_ekd ≠ buf.a_ve ∧ a_ekd ≠ buf.a_em ∧ a_ekd ≠ buf.a_zV ∧ a_ekd ≠ buf.a_zI := by
    have := hbuf_arena a_ekd (by simp); tauto
  have h5 : a_ev1 ≠ buf.a_vv ∧ a_ev1 ≠ buf.a_ve ∧ a_ev1 ≠ buf.a_em ∧ a_ev1 ≠ buf.a_zV ∧ a_ev1 ≠ buf.a_zI := by
    have := hbuf_arena a_ev1 (by simp); tauto
  have h6 : a_ev2 ≠ buf.a_vv ∧ a_ev2 ≠ buf.a_ve ∧ a_ev2 ≠ buf.a_em ∧ a_ev2 ≠ buf.a_zV ∧ a_ev2 ≠ buf.a_zI := by
    have := hbuf_arena a_ev2 (by simp); tauto
  have hs5_arr : ∀ a, a ≠ a_vkd → a ≠ a_vv1 → a ≠ a_vv2 → a ≠ a_ekd → a ≠ a_ev1 → a ≠ a_ev2 →
      s₅.arrs a = s.arrs a := fun a ha1 ha2 ha3 ha4 ha5 ha6 => by
    simp -zeta only [s₅, s₄, s₃, s₂, s₁, State.setReg_arrs,
      State.writeArr_arrs_ne _ _ _ ha1, State.writeArr_arrs_ne _ _ _ ha2,
      State.writeArr_arrs_ne _ _ _ ha3, State.writeArr_arrs_ne _ _ _ ha4,
      State.writeArr_arrs_ne _ _ _ ha5, State.writeArr_arrs_ne _ _ _ ha6]
  have hs5_reg : ∀ r, r ≠ r_kv → r ≠ r_ke → r ≠ 14 → r ≠ 15 → s₅.regs r = s.regs r :=
    fun r hr1 hr2 hr3 hr4 => by
      simp -zeta only [s₅, s₄, s₃, s₂, s₁, State.writeArr_regs,
        State.setReg_regs_ne _ _ hr1, State.setReg_regs_ne _ _ hr2,
        State.setReg_regs_ne _ _ hr3, State.setReg_regs_ne _ _ hr4]
  have hs5_vv := hs5_arr buf.a_vv h1.1.symm h2.1.symm h3.1.symm h4.1.symm h5.1.symm h6.1.symm
  have hs5_ve := hs5_arr buf.a_ve h1.2.1.symm h2.2.1.symm h3.2.1.symm h4.2.1.symm h5.2.1.symm h6.2.1.symm
  have hs5_em := hs5_arr buf.a_em h1.2.2.1.symm h2.2.2.1.symm h3.2.2.1.symm h4.2.2.1.symm h5.2.2.1.symm h6.2.2.1.symm
  rcases baseTableBodyProg_exec (w := w) (δ := δ) (ξ := ξ) (ω := ω) (bcfg := bcfg)
      (kv₀ := kv₀) (ke₀ := ke₀) (e0 := e0) (buf := buf) (s₀ := s₅) hvv_ve hvv_em hve_em
      (Nat.ne_of_lt (Nat.lt_trans hrt_lt (by decide)))
      (Nat.ne_of_lt (Nat.lt_trans hrt_lt (by decide)))
      (Nat.ne_of_lt (Nat.lt_trans hrt_lt (by decide)))
      hw2 hS_w hT_w (by omega) (by omega) he0_w
      ((hs5_reg 12 (by decide) (by decide) (by decide) (by decide)).trans hr12')
      (by simp -zeta [s₅, s₄, s₃, s₂, s₁]) (by simp -zeta [s₅, s₄, s₃, s₂, s₁])
      (by rw [hs5_vv, hvv_len]) (by rw [hs5_ve, hve_len]) (by rw [hs5_em, hem_len]) with
    ⟨s', t_body, hex_body, ht_body, htid', hreg', harr', hvv_len', hve_len', hem_len', hpos'⟩
  rcases Exec.branchOnBound (r_in := 13) hw_pos hw72
      ((hs5_reg 13 (by decide) (by decide) (by decide) (by decide)).trans hr13)
      hbcfg_lt hex_body with ⟨t_br, ht_br, hex_br⟩
  dsimp [Expr.cost] at ht₃ ht₄ ht₅ ht₆
  have hex_all : Exec w (baseTableFillProg δ ξ ω buf) s s'
      (2 + (2 + (t₃ + (t₄ + (t₅ + (t₆ + t_br)))))) :=
    .seq hex₁ (.seq hex₂ (.seq hex₃ (.seq hex₄ (.seq hex₅ (.seq hex₆ hex_br)))))
  have hs'_vkd : s'.arrs a_vkd = (((s.arrs a_vkd).set kv₀ kd_v0).set (kv₀ + 1) kd_v1).set (kv₀ + 2) 2 := by
    rw [harr' a_vkd h1.1 h1.2.1 h1.2.2.1]; simp -zeta [s₅, s₄, s₃, s₂, s₁]
  have hs'_vv1 : s'.arrs a_vv1 = (((s.arrs a_vv1).set kv₀ v0).set (kv₀ + 1) v1).set (kv₀ + 2) kv₀ := by
    rw [harr' a_vv1 h2.1 h2.2.1 h2.2.2.1]; simp -zeta [s₅, s₄, s₃, s₂, s₁]
  have hs'_vv2 : s'.arrs a_vv2 = (((s.arrs a_vv2).set kv₀ 0).set (kv₀ + 1) 0).set (kv₀ + 2) (kv₀ + 1) := by
    rw [harr' a_vv2 h3.1 h3.2.1 h3.2.2.1]; simp -zeta [s₅, s₄, s₃, s₂, s₁]
  have hs'_ekd : s'.arrs a_ekd = (s.arrs a_ekd).set ke₀ kd_e0 := by
    rw [harr' a_ekd h4.1 h4.2.1 h4.2.2.1]; simp -zeta [s₅, s₄, s₃, s₂, s₁]
  have hs'_ev1 : s'.arrs a_ev1 = (s.arrs a_ev1).set ke₀ e0 := by
    rw [harr' a_ev1 h5.1 h5.2.1 h5.2.2.1]; simp -zeta [s₅, s₄, s₃, s₂, s₁]
  have hs'_ev2 : s'.arrs a_ev2 = (s.arrs a_ev2).set ke₀ 0 := by
    rw [harr' a_ev2 h6.1 h6.2.1 h6.2.2.1]; simp -zeta [s₅, s₄, s₃, s₂, s₁]
  rcases arenaWF_after_basePush hwfV hwfE hkv_cap hke_cap
      hs'_vkd hs'_vv1 hs'_vv2 hs'_ekd hs'_ev1 hs'_ev2 with
    ⟨hwfV3, hwfE1, hevalV_prev, hevalE_prev⟩
  have hr_kv' : s'.regs r_kv = kv₀ + 3 := by rw [hreg' r_kv hrt_ne_kv.symm]; simp -zeta [s₅, s₄]
  have hr_ke' : s'.regs r_ke = ke₀ + 1 := by rw [hreg' r_ke hrt_ne_ke.symm]; simp -zeta [s₅]
  have hr_q' : s'.regs buf.r_q = ZA.card :=
    (hreg' buf.r_q hrt_ne_rq.symm).trans
      ((hs5_reg buf.r_q hrq_ne_kv hrq_ne_ke
        (Nat.ne_of_lt (Nat.lt_trans _hrq_lt (by decide : 10 < 14)))
        (Nat.ne_of_lt (Nat.lt_trans _hrq_lt (by decide : 10 < 15)))).trans hr_q)
  have hzV' : s'.arrs buf.a_zV = s.arrs buf.a_zV :=
    (harr' buf.a_zV hzV_vv hzV_ve hzV_em).trans
      (hs5_arr buf.a_zV h1.2.2.2.1.symm h2.2.2.2.1.symm h3.2.2.2.1.symm
        h4.2.2.2.1.symm h5.2.2.2.1.symm h6.2.2.2.1.symm)
  have hzI' : s'.arrs buf.a_zI = s.arrs buf.a_zI :=
    (harr' buf.a_zI hzI_vv hzI_ve hzI_em).trans
      (hs5_arr buf.a_zI h1.2.2.2.2.symm h2.2.2.2.2.symm h3.2.2.2.2.symm
        h4.2.2.2.2.symm h5.2.2.2.2.symm h6.2.2.2.2.symm)
  have hvalid : ValidPieceBuffer δ ξ ω G ZA EA
      (baseCertFolioTable G VA EA (finsetRootFn ZA) δ).toRawList buf s' :=
    validPieceBuffer_of_baseTableFill hZA hEA hG_loc hZ_loc hkv0_pos hke0_pos hkv_cap hke_cap
      hlen_vv1 hlen_vv2 hlen_ev1 htid' hr_q' hr_kv' hr_ke'
      (by rw [hzV']; exact hzV_len) (by rw [hzI']; exact hzI_len)
      (fun i => by rw [hzV']; exact hzV i) (fun i => by rw [hzI']; exact hzI i)
      hvv_len' hve_len' hem_len' hs'_vkd hs'_vv1 hs'_vv2 hs'_ekd hs'_ev1 hs'_ev2 hpos'
  refine ⟨s', 2 + (2 + (t₃ + (t₄ + (t₅ + (t₆ + t_br))))), hex_all, by omega,
    hr_kv', hr_ke', hwfV3, hwfE1,
    by rw [hs'_vkd]; simp, by rw [hs'_ekd]; simp,
    hevalV_prev, fun p hp => hevalE_prev p hp, hvalid,
    fun r hr h1' h2' h3' =>
      (hreg' r h3').trans
        (hs5_reg r h1' h2'
          (Nat.ne_of_lt (Nat.lt_trans hr (by decide : 10 < 14)))
          (Nat.ne_of_lt (Nat.lt_trans hr (by decide : 10 < 15)))),
    fun a ha1 ha2 ha3 ha4 ha5 ha6 ha7 ha8 ha9 =>
      (harr' a ha7 ha8 ha9).trans (hs5_arr a ha1 ha2 ha3 ha4 ha5 ha6)⟩

/-! ### Section 2: Base Step Programs (`isoBaseStepProg`, `treeBaseStepProg`) -/

private theorem getD_set_ne (L : List ℕ) (k v p : ℕ) (hne : p ≠ k) :
    (L.set k v).getD p 0 = L.getD p 0 := by
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_set_ne hne.symm]

private theorem getD_set_eq (L : List ℕ) (k v : ℕ) (hk : k < L.length) :
    (L.set k v).getD k 0 = v := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_set_self hk, Option.getD_some]

theorem pairwise_lt_finRange (n : ℕ) : (List.finRange n).Pairwise (· < ·) := by
  rw [List.pairwise_iff_getElem]; intro i j hi hj hij; simpa using hij

theorem finsetRootFn_strictMono {n : ℕ} (S : Finset (Fin n)) :
    StrictMono (finsetRootFn S) := by
  intro i j hij
  have hp : (finsetToFinList S).Pairwise (· < ·) := (pairwise_lt_finRange n).filter _
  exact List.pairwise_iff_getElem.mp hp i.1 j.1
    (by rw [length_finsetToFinList]; exact i.2)
    (by rw [length_finsetToFinList]; exact j.2) hij

theorem finsetRootFn_congr {n : ℕ} {S₁ S₂ : Finset (Fin n)} (h : S₁ = S₂)
    (k : ℕ) (hk₁ : k < S₁.card) (hk₂ : k < S₂.card) :
    finsetRootFn S₁ ⟨k, hk₁⟩ = finsetRootFn S₂ ⟨k, hk₂⟩ := by subst h; rfl

theorem finsetRootFn_singleton {n : ℕ} (v : Fin n) (i : Fin ({v} : Finset (Fin n)).card) :
    finsetRootFn {v} i = v := Finset.mem_singleton.mp (finsetRootFn_mem {v} i)

theorem card_pair_of_lt {n : ℕ} {a b : Fin n} (hab : a < b) :
    ({a, b} : Finset (Fin n)).card = 2 := Finset.card_pair (ne_of_lt hab)

theorem finsetRootFn_pair_zero {n : ℕ} {a b : Fin n} (hab : a < b) :
    finsetRootFn {a, b} ⟨0, by rw [card_pair_of_lt hab]; decide⟩ = a := by
  let S : Finset (Fin n) := {a, b}
  have hcard : S.card = 2 := card_pair_of_lt hab
  let i0 : Fin S.card := ⟨0, by omega⟩
  let i1 : Fin S.card := ⟨1, by omega⟩
  have hlt : finsetRootFn S i0 < finsetRootFn S i1 :=
    finsetRootFn_strictMono S (Fin.lt_def.mpr (by decide : (0 : ℕ) < 1))
  have hm0 : finsetRootFn S i0 = a ∨ finsetRootFn S i0 = b := by simpa [S] using finsetRootFn_mem S i0
  have hm1 : finsetRootFn S i1 = a ∨ finsetRootFn S i1 = b := by simpa [S] using finsetRootFn_mem S i1
  rcases hm0 with h0 | h0 <;> rcases hm1 with h1 | h1
  · exact h0
  · exact h0
  · rw [h0, h1] at hlt; exact False.elim (lt_asymm hab hlt)
  · rw [h0, h1] at hlt; exact False.elim (lt_irrefl b hlt)

theorem finsetRootFn_pair_one {n : ℕ} {a b : Fin n} (hab : a < b) :
    finsetRootFn {a, b} ⟨1, by rw [card_pair_of_lt hab]; decide⟩ = b := by
  let S : Finset (Fin n) := {a, b}
  have hcard : S.card = 2 := card_pair_of_lt hab
  let i0 : Fin S.card := ⟨0, by omega⟩
  let i1 : Fin S.card := ⟨1, by omega⟩
  have hlt : finsetRootFn S i0 < finsetRootFn S i1 :=
    finsetRootFn_strictMono S (Fin.lt_def.mpr (by decide : (0 : ℕ) < 1))
  have hm0 : finsetRootFn S i0 = a ∨ finsetRootFn S i0 = b := by simpa [S] using finsetRootFn_mem S i0
  have hm1 : finsetRootFn S i1 = a ∨ finsetRootFn S i1 = b := by simpa [S] using finsetRootFn_mem S i1
  rcases hm0 with h0 | h0 <;> rcases hm1 with h1 | h1
  · rw [h0, h1] at hlt; exact False.elim (lt_irrefl a hlt)
  · exact h1
  · rw [h0, h1] at hlt; exact False.elim (lt_asymm hab hlt)
  · exact h1

theorem ComputeDigraph.ext_of_numEdges_zero {G₁ G₂ : ComputeDigraph}
    (hn : G₁.numVerts = G₂.numVerts) (hm1 : G₁.numEdges = 0) (hm2 : G₂.numEdges = 0) :
    G₁ = G₂ := by
  cases G₁ with
  | mk nv₁ ne₁ hd₁ tl₁ =>
    cases G₂ with
    | mk nv₂ ne₂ hd₂ tl₂ =>
      dsimp at hn hm1 hm2; subst hn hm1 hm2
      have h1 : hd₁ = hd₂ := funext fun e => Fin.elim0 e
      have h2 : tl₁ = tl₂ := funext fun e => Fin.elim0 e
      subst h1 h2; rfl

theorem ComputeDigraph.ext_of_numEdges_one {G₁ G₂ : ComputeDigraph}
    (hn : G₁.numVerts = G₂.numVerts) (hm1 : G₁.numEdges = 1) (hm2 : G₂.numEdges = 1)
    (hhd : (G₁.head ⟨0, by omega⟩).1 = (G₂.head ⟨0, by omega⟩).1)
    (htl : (G₁.tail ⟨0, by omega⟩).1 = (G₂.tail ⟨0, by omega⟩).1) :
    G₁ = G₂ := by
  cases G₁ with
  | mk nv₁ ne₁ hd₁ tl₁ =>
    cases G₂ with
    | mk nv₂ ne₂ hd₂ tl₂ =>
      dsimp at hn hm1 hm2 hhd htl; subst hn hm1 hm2
      have h1 : hd₁ = hd₂ := funext fun e => by
        rw [show e = ⟨0, by omega⟩ from Fin.ext (by omega)]; exact Fin.ext hhd
      have h2 : tl₁ = tl₂ := funext fun e => by
        rw [show e = ⟨0, by omega⟩ from Fin.ext (by omega)]; exact Fin.ext htl
      subst h1 h2; rfl

/-- Word RAM program initializing `bufB` with the base table for an isolated vertex `v = r_v`:
`VA = {v}, EA = ∅, ZA = Z ∩ {v}` (`bcfg = 1 + 18 * a_Z[v]`). -/
def isoBaseStepProg (δ ξ ω : ℕ) (r_v : Reg) : Cmd :=
  .seq (.assign 10 (.reg r_v))
  (.seq (.assign r_qB (.read a_Z (.reg 10)))
  (.seq (.write a_rhs_zV (.const 0) (.reg 10))
  (.seq (.write a_rhs_zI (.const 0) (.const 0))
  (.seq (.assign 11 (.const 0))
  (.seq (.assign 12 (.const 0))
  (.seq (.assign 13 (.op .add (.const 1) (.op .mul (.const 18) (.reg r_qB))))
  (.seq (.assign 16 (.const 1))
  (.seq (.assign 17 (.const 0))
  (.seq (.assign 18 (.const 0))
        (baseTableFillProg δ ξ ω bufB))))))))))

theorem isoBaseStepProg_exec {w δ ξ ω : ℕ} {G : ComputeDigraph}
    {Z : Finset (Fin G.numVerts)} (v : Fin G.numVerts)
    {r_v : Reg} (_hrv_lt : r_v < 10) (_hrv_kv : r_v ≠ r_kv) (_hrv_ke : r_v ≠ r_ke)
    (_hrv_tidB : r_v ≠ r_tidB) (_hrv_qB : r_v ≠ r_qB)
    {kv₀ ke₀ : ℕ} {s : State} (hw72 : 72 < 2 ^ w)
    (hn_w : G.numVerts < 2 ^ w) (hm_w : G.numEdges < 2 ^ w)
    (hS_w : S_tab δ ξ ω < 2 ^ w) (hT_w : T_max δ ξ ω < 2 ^ w)
    (hkv_w : kv₀ + 3 < 2 ^ w) (hke_w : ke₀ + 1 < 2 ^ w)
    (hwfV : ArenaWF G.numVerts kv₀ (s.arrs a_vkd) (s.arrs a_vv1) (s.arrs a_vv2))
    (hwfE : ArenaWF G.numEdges ke₀ (s.arrs a_ekd) (s.arrs a_ev1) (s.arrs a_ev2))
    (hkv_cap : kv₀ + 3 ≤ (s.arrs a_vkd).length) (hke_cap : ke₀ + 1 ≤ (s.arrs a_ekd).length)
    (hr_kv : s.regs r_kv = kv₀) (hr_ke : s.regs r_ke = ke₀)
    (hr_v : s.regs r_v = v.1) (hZ_arr : s.arrs a_Z = bitSetList Z)
    (hzV_len : (s.arrs a_rhs_zV).length = Q_max ξ ω)
    (hzI_len : (s.arrs a_rhs_zI).length = Q_max ξ ω)
    (hvv_len : (s.arrs a_rhs_vv).length = S_tab δ ξ ω)
    (hve_len : (s.arrs a_rhs_ve).length = S_tab δ ξ ω)
    (hem_len : (s.arrs a_rhs_em).length = S_tab δ ξ ω) :
    ∃ s' t_step,
      Exec w (isoBaseStepProg δ ξ ω r_v) s s' t_step ∧
      t_step ≤ 340 + 15 * S_tab δ ξ ω ∧
      s'.regs r_kv = kv₀ + 3 ∧ s'.regs r_ke = ke₀ + 1 ∧
      ArenaWF G.numVerts (kv₀ + 3) (s'.arrs a_vkd) (s'.arrs a_vv1) (s'.arrs a_vv2) ∧
      ArenaWF G.numEdges (ke₀ + 1) (s'.arrs a_ekd) (s'.arrs a_ev1) (s'.arrs a_ev2) ∧
      (s'.arrs a_vkd).length = (s.arrs a_vkd).length ∧
      (s'.arrs a_ekd).length = (s.arrs a_ekd).length ∧
      (∀ p < kv₀,
        evalArena G.numVerts (s'.arrs a_vkd) (s'.arrs a_vv1) (s'.arrs a_vv2) p =
          evalArena G.numVerts (s.arrs a_vkd) (s.arrs a_vv1) (s.arrs a_vv2) p) ∧
      (∀ p < ke₀,
        evalArena G.numEdges (s'.arrs a_ekd) (s'.arrs a_ev1) (s'.arrs a_ev2) p =
          evalArena G.numEdges (s.arrs a_ekd) (s.arrs a_ev1) (s.arrs a_ev2) p) ∧
      ValidPieceBuffer δ ξ ω G (Z ∩ {v}) ∅
        (baseCertFolioTable G {v} ∅ (finsetRootFn (Z ∩ {v})) δ).toRawList bufB s' ∧
      (∀ r < 10, r ≠ r_kv → r ≠ r_ke → r ≠ r_tidB → r ≠ r_qB → s'.regs r = s.regs r) ∧
      (∀ a, a ≠ a_vkd → a ≠ a_vv1 → a ≠ a_vv2 → a ≠ a_ekd → a ≠ a_ev1 → a ≠ a_ev2 →
        a ≠ a_rhs_zV → a ≠ a_rhs_zI → a ≠ a_rhs_vv → a ≠ a_rhs_ve → a ≠ a_rhs_em →
        s'.arrs a = s.arrs a) := by
  have h0_w : 0 < 2 ^ w := by omega
  have hw1 : 1 < 2 ^ w := by omega
  have hv_w : v.1 < 2 ^ w := Nat.lt_trans v.2 hn_w
  let b₀ : ℕ := if v ∈ Z then 1 else 0
  have hb0_w : b₀ < 2 ^ w := by dsimp [b₀]; split_ifs <;> omega
  let bcfg := 1 + 18 * b₀
  have hbcfg_lt : bcfg < 72 := by dsimp [bcfg, b₀]; split_ifs <;> omega
  have hQ_pos : 0 < Q_max ξ ω := by unfold Q_max; omega
  let s₁ := s.setReg 10 v.1
  have hex₁ : Exec w (.assign 10 (.reg r_v)) s s₁ 2 :=
    .assign (by simp [Expr.eval, checkWord, hr_v, hv_w])
  let s₂ := s₁.setReg r_qB b₀
  have hex₂ : Exec w (.assign r_qB (.read a_Z (.reg 10))) s₁ s₂ 3 :=
    .assign (by simp [s₁, Expr.eval, checkWord, hv_w, hZ_arr, v.2, bitSetList, b₀, hb0_w])
  let s₃ := s₂.writeArr a_rhs_zV 0 v.1
  have hex₃ : Exec w (.write a_rhs_zV (.const 0) (.reg 10)) s₂ s₃ 3 :=
    .write (by simp [Expr.eval, checkWord, h0_w])
           (by simp [s₂, s₁, Expr.eval, checkWord, hv_w]) (by simp [s₂, s₁, hzV_len, hQ_pos])
  let s₄ := s₃.writeArr a_rhs_zI 0 0
  have hex₄ : Exec w (.write a_rhs_zI (.const 0) (.const 0)) s₃ s₄ 3 :=
    .write (by simp [Expr.eval, checkWord, h0_w])
           (by simp [Expr.eval, checkWord, h0_w]) (by simp [s₃, s₂, s₁, hzI_len, hQ_pos])
  let s₅ := s₄.setReg 11 0
  have hex₅ : Exec w (.assign 11 (.const 0)) s₄ s₅ 2 := .assign (by simp [Expr.eval, checkWord, h0_w])
  let s₆ := s₅.setReg 12 0
  have hex₆ : Exec w (.assign 12 (.const 0)) s₅ s₆ 2 := .assign (by simp [Expr.eval, checkWord, h0_w])
  let s₇ := s₆.setReg 13 bcfg
  have hex₇ : Exec w (.assign 13 (.op .add (.const 1) (.op .mul (.const 18) (.reg r_qB)))) s₆ s₇ 6 :=
    .assign (by
      have h18_w : 18 < 2 ^ w := by omega
      have h18b_w : 18 * b₀ < 2 ^ w := by dsimp [b₀]; split_ifs <;> omega
      have hbcfg_w : bcfg < 2 ^ w := by omega
      simp [s₆, s₅, s₄, s₃, s₂, Expr.eval, BinOp.eval, BinOp.raw, checkWord,
        hw1, h18_w, hb0_w, h18b_w, bcfg, hbcfg_w])
  let s₈ := s₇.setReg 16 1
  have hex₈ : Exec w (.assign 16 (.const 1)) s₇ s₈ 2 := .assign (by simp [Expr.eval, checkWord, hw1])
  let s₉ := s₈.setReg 17 0
  have hex₉ : Exec w (.assign 17 (.const 0)) s₈ s₉ 2 := .assign (by simp [Expr.eval, checkWord, h0_w])
  let s₁₀ := s₉.setReg 18 0
  have hex₁₀ : Exec w (.assign 18 (.const 0)) s₉ s₁₀ 2 := .assign (by simp [Expr.eval, checkWord, h0_w])
  have hVA_card : ({v} : Finset (Fin G.numVerts)).card = 1 := Finset.card_singleton v
  have hEA_card : (∅ : Finset (Fin G.numEdges)).card = 0 := rfl
  have hZA_sub : Z ∩ {v} ⊆ {v} := Finset.inter_subset_right
  have hEA_sub : ∀ e ∈ (∅ : Finset (Fin G.numEdges)), G.head e ∈ ({v} : Finset _) ∧ G.tail e ∈ ({v} : Finset _) :=
    fun _ he => by simp at he
  have hZA_card : (Z ∩ {v}).card = b₀ := by
    dsimp [b₀]; split_ifs with hvZ
    · rw [Finset.inter_singleton_of_mem hvZ, Finset.card_singleton]
    · rw [Finset.inter_singleton_of_notMem hvZ, Finset.card_empty]
  have hG_loc : pieceLocDigraph G {v} ∅ hEA_sub = canonLocDigraph bcfg := by
    apply ComputeDigraph.ext_of_numEdges_zero
    · change ({v} : Finset _).card = bcfg % 3; rw [hVA_card]; dsimp [bcfg, b₀]; split_ifs <;> rfl
    · rfl
    · change (if bcfg % 3 = 0 then 0 else (bcfg / 3) % 2) = 0; dsimp [bcfg, b₀]; split_ifs <;> rfl
  have hZ_loc : ∀ i : Fin ({v} : Finset (Fin G.numVerts)).card,
      (i ∈ subMaskFinset {v} (Z ∩ {v}) ↔
        (⟨i.1, Nat.lt_of_lt_of_eq i.2 (congrArg ComputeDigraph.numVerts hG_loc)⟩ :
          Fin (canonLocDigraph bcfg).numVerts) ∈ canonLocRoots bcfg) := by
    intro i; have hi_lt := Nat.lt_of_lt_of_eq i.2 hVA_card; have hi0 : i.1 = 0 := by omega
    simp only [subMaskFinset, canonLocRoots, Finset.mem_filter, Finset.mem_univ, true_and,
      finsetRootFn_singleton v i, Finset.mem_inter, Finset.mem_singleton, and_true, hi0]
    dsimp [bcfg, b₀]; by_cases hvZ : v ∈ Z <;> simp [hvZ]
  rcases baseTableFillProg_exec (w := w) (δ := δ) (ξ := ξ) (ω := ω) (G := G)
      (VA := {v}) (EA := ∅) (ZA := Z ∩ {v}) hZA_sub hEA_sub
      (bcfg := bcfg) (kv₀ := kv₀) (ke₀ := ke₀) (buf := bufB) (s := s₁₀) hbcfg_lt hG_loc hZ_loc
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide)
      hw72 hn_w hm_w hS_w hT_w hkv_w hke_w
      (by simpa [s₁₀, s₉, s₈, s₇, s₆, s₅, s₄, s₃, s₂, s₁] using hwfV)
      (by simpa [s₁₀, s₉, s₈, s₇, s₆, s₅, s₄, s₃, s₂, s₁] using hwfE)
      (by simpa [s₁₀, s₉, s₈, s₇, s₆, s₅, s₄, s₃, s₂, s₁] using hkv_cap)
      (by simpa [s₁₀, s₉, s₈, s₇, s₆, s₅, s₄, s₃, s₂, s₁] using hke_cap)
      (by simp [s₁₀, s₉, s₈, s₇, s₆, s₅, s₄, s₃, s₂, s₁, hr_kv])
      (by simp [s₁₀, s₉, s₈, s₇, s₆, s₅, s₄, s₃, s₂, s₁, hr_ke])
      (by simp [s₁₀, s₉, s₈, s₇, s₆, s₅, s₄, s₃, s₂, s₁, hVA_card, finsetRootFn_singleton])
      (by simp [s₁₀, s₉, s₈, s₇, s₆, s₅, s₄, s₃, s₂, s₁, hVA_card])
      (by simp [s₁₀, s₉, s₈, s₇, s₆, s₅, s₄, s₃, s₂, s₁, hEA_card])
      (by simp [s₁₀, s₉, s₈, s₇]) (by simp [s₁₀, s₉, s₈, hVA_card])
      (by simp [s₁₀, s₉, hVA_card]) (by simp [s₁₀, hEA_card])
      (by simp [s₁₀, s₉, s₈, s₇, s₆, s₅, s₄, s₃, s₂, bufB, hZA_card])
      (by simp [s₁₀, s₉, s₈, s₇, s₆, s₅, s₄, s₃, s₂, s₁, bufB, hzV_len])
      (by simp [s₁₀, s₉, s₈, s₇, s₆, s₅, s₄, s₃, s₂, s₁, bufB, hzI_len])
      (by intro i
          have hi_lt := Nat.lt_of_lt_of_eq i.2 hZA_card
          have hb0_le : b₀ ≤ 1 := by dsimp [b₀]; split_ifs <;> omega
          have hi0 : i.1 = 0 := by omega
          have hroot : finsetRootFn (Z ∩ {v}) i = v :=
            Finset.mem_singleton.mp (hZA_sub (finsetRootFn_mem (Z ∩ {v}) i))
          have hs10_zV : s₁₀.arrs bufB.a_zV = (s.arrs a_rhs_zV).set 0 v.1 := by
            simp [s₁₀, s₉, s₈, s₇, s₆, s₅, s₄, s₃, s₂, s₁, bufB]
          rw [hi0, hroot, hs10_zV, getD_set_eq _ 0 v.1 (by omega)])
      (by intro i
          have hi_lt := Nat.lt_of_lt_of_eq i.2 hZA_card
          have hb0_le : b₀ ≤ 1 := by dsimp [b₀]; split_ifs <;> omega
          have hi0 : i.1 = 0 := by omega
          have hs10_zI : s₁₀.arrs bufB.a_zI = (s.arrs a_rhs_zI).set 0 0 := by
            simp [s₁₀, s₉, s₈, s₇, s₆, s₅, s₄, s₃, s₂, s₁, bufB]
          rw [hi0, hs10_zI, getD_set_eq _ 0 0 (by omega)]; simp [subInc])
      (by simp [s₁₀, s₉, s₈, s₇, s₆, s₅, s₄, s₃, s₂, s₁, bufB, hvv_len])
      (by simp [s₁₀, s₉, s₈, s₇, s₆, s₅, s₄, s₃, s₂, s₁, bufB, hve_len])
      (by simp [s₁₀, s₉, s₈, s₇, s₆, s₅, s₄, s₃, s₂, s₁, bufB, hem_len]) with
    ⟨s', t_fill, hex_fill, ht_fill, hkv', hke', hwfV', hwfE', hlen_vkd', hlen_ekd',
     hevalV', hevalE', hvalid', hreg', harr'⟩
  refine ⟨s', 2 + (3 + (3 + (3 + (2 + (2 + (6 + (2 + (2 + (2 + t_fill))))))))),
    .seq hex₁ (.seq hex₂ (.seq hex₃ (.seq hex₄ (.seq hex₅ (.seq hex₆
      (.seq hex₇ (.seq hex₈ (.seq hex₉ (.seq hex₁₀ hex_fill))))))))),
    by omega, hkv', hke', hwfV', hwfE',
    by simpa [s₁₀, s₉, s₈, s₇, s₆, s₅, s₄, s₃, s₂, s₁] using hlen_vkd',
    by simpa [s₁₀, s₉, s₈, s₇, s₆, s₅, s₄, s₃, s₂, s₁] using hlen_ekd',
    fun p hp => by simpa [s₁₀, s₉, s₈, s₇, s₆, s₅, s₄, s₃, s₂, s₁] using hevalV' p hp,
    fun p hp => by simpa [s₁₀, s₉, s₈, s₇, s₆, s₅, s₄, s₃, s₂, s₁] using hevalE' p hp,
    hvalid',
    fun r hr h1 h2 h3 h4 => by
      rw [hreg' r hr h1 h2 h3]
      simp [s₁₀, s₉, s₈, s₇, s₆, s₅, s₄, s₃, s₂, s₁, h4,
        Nat.ne_of_lt (Nat.lt_of_lt_of_le hr (by decide : 10 ≤ 10)),
        Nat.ne_of_lt (Nat.lt_trans hr (by decide : 10 < 11)),
        Nat.ne_of_lt (Nat.lt_trans hr (by decide : 10 < 12)),
        Nat.ne_of_lt (Nat.lt_trans hr (by decide : 10 < 13)),
        Nat.ne_of_lt (Nat.lt_trans hr (by decide : 10 < 16)),
        Nat.ne_of_lt (Nat.lt_trans hr (by decide : 10 < 17)),
        Nat.ne_of_lt (Nat.lt_trans hr (by decide : 10 < 18))],
    fun a ha1 ha2 ha3 ha4 ha5 ha6 ha7 ha8 ha9 ha10 ha11 => by
      rw [harr' a ha1 ha2 ha3 ha4 ha5 ha6 ha9 ha10 ha11]
      simp [s₁₀, s₉, s₈, s₇, s₆, s₅, s₄, s₃, s₂, s₁, ha7, ha8]⟩

theorem pieceVB_singleton (G : ComputeDigraph) (e : Fin G.numEdges) :
    pieceVB G {e} = {G.head e, G.tail e} := by
  ext v; simp only [pieceVB, mem_edgeEnds, Finset.mem_singleton, exists_eq_left,
    Finset.mem_insert, digraphIncident]; tauto

theorem subInc_singleton_of_mem {G : ComputeDigraph} (e : Fin G.numEdges)
    {v : Fin G.numVerts} (hv : v = G.head e ∨ v = G.tail e) :
    subInc G {e} v = 1 := by
  have hmem : e ∈ incEdges G v := by
    rw [incEdges, Finset.mem_filter]; refine ⟨Finset.mem_univ e, ?_⟩
    rcases hv with rfl | rfl <;> [exact Or.inl rfl; exact Or.inr rfl]
  have hinter : incEdges G v ∩ {e} = {e} := Finset.inter_singleton_of_mem hmem
  unfold subInc; rw [hinter, Finset.card_singleton]

theorem subset_pair_spec {n : ℕ} {a b : Fin n} (hab : a < b)
    {ZA : Finset (Fin n)} (hZA : ZA ⊆ {a, b}) :
    let b₀ := if a ∈ ZA then 1 else 0
    let b₁ := if b ∈ ZA then 1 else 0
    ZA.card = b₀ + b₁ ∧
    (∀ (L : List ℕ), 2 ≤ L.length → ∀ i : Fin ZA.card,
      ((L.set 0 a.1).set b₀ b.1).getD i.1 0 = (finsetRootFn ZA i).1) ∧
    (∀ (L : List ℕ), 2 ≤ L.length → ∀ i : Fin ZA.card,
      ((L.set 0 1).set b₀ 1).getD i.1 0 = 1) := by
  dsimp only; by_cases ha : a ∈ ZA <;> by_cases hb : b ∈ ZA <;> simp only [ha, hb, ↓reduceIte]
  · have hZA_eq : ZA = {a, b} := by
      ext x; simp only [Finset.mem_insert, Finset.mem_singleton]
      exact ⟨fun hx => by simpa using hZA hx, by rintro (rfl | rfl) <;> assumption⟩
    subst hZA_eq; have hcard : ({a, b} : Finset (Fin n)).card = 2 := card_pair_of_lt hab
    refine ⟨hcard, fun L hL i => ?_, fun L hL i => ?_⟩
    · have hi2 : i.1 < 2 := Nat.lt_of_lt_of_eq i.2 hcard
      rcases (by omega : i.1 = 0 ∨ i.1 = 1) with hi0 | hi1
      · rw [hi0, getD_set_ne _ 1 b.1 0 (by decide), getD_set_eq L 0 a.1 (by omega),
            show i = ⟨0, by rw [hcard]; decide⟩ from Fin.ext hi0, finsetRootFn_pair_zero hab]
      · rw [hi1, getD_set_eq (L.set 0 a.1) 1 b.1 (by simp; omega),
            show i = ⟨1, by rw [hcard]; decide⟩ from Fin.ext hi1, finsetRootFn_pair_one hab]
    · have hi2 : i.1 < 2 := Nat.lt_of_lt_of_eq i.2 hcard
      rcases (by omega : i.1 = 0 ∨ i.1 = 1) with hi0 | hi1
      · rw [hi0, getD_set_ne _ 1 1 0 (by decide), getD_set_eq L 0 1 (by omega)]
      · rw [hi1, getD_set_eq (L.set 0 1) 1 1 (by simp; omega)]
  · have hZA_eq : ZA = {a} := by
      ext x; simp only [Finset.mem_singleton]; refine ⟨fun hx => ?_, fun h => h ▸ ha⟩
      rcases Finset.mem_insert.mp (hZA hx) with rfl | hxb
      · rfl
      · exact False.elim (hb (Finset.mem_singleton.mp hxb ▸ hx))
    subst hZA_eq; refine ⟨Finset.card_singleton a, fun L hL i => ?_, fun L hL i => ?_⟩
    · have hi0 : i.1 = 0 := by have := Nat.lt_of_lt_of_eq i.2 (Finset.card_singleton a); omega
      rw [hi0, getD_set_ne _ 1 b.1 0 (by decide), getD_set_eq L 0 a.1 (by omega), finsetRootFn_singleton a i]
    · have hi0 : i.1 = 0 := by have := Nat.lt_of_lt_of_eq i.2 (Finset.card_singleton a); omega
      rw [hi0, getD_set_ne _ 1 1 0 (by decide), getD_set_eq L 0 1 (by omega)]
  · have hZA_eq : ZA = {b} := by
      ext x; simp only [Finset.mem_singleton]; refine ⟨fun hx => ?_, fun h => h ▸ hb⟩
      rcases Finset.mem_insert.mp (hZA hx) with rfl | hxb <;>
        [exact False.elim (ha hx); exact Finset.mem_singleton.mp hxb]
    subst hZA_eq; refine ⟨Finset.card_singleton b, fun L hL i => ?_, fun L hL i => ?_⟩
    · have hi0 : i.1 = 0 := by have := Nat.lt_of_lt_of_eq i.2 (Finset.card_singleton b); omega
      rw [hi0, getD_set_eq (L.set 0 a.1) 0 b.1 (by simp; omega), finsetRootFn_singleton b i]
    · have hi0 : i.1 = 0 := by have := Nat.lt_of_lt_of_eq i.2 (Finset.card_singleton b); omega
      rw [hi0, getD_set_eq (L.set 0 1) 0 1 (by simp; omega)]
  · have hZA_eq : ZA = ∅ := by
      ext x; simp only [Finset.notMem_empty, iff_false]; intro hx
      rcases Finset.mem_insert.mp (hZA hx) with rfl | hxb <;>
        [exact ha hx; exact hb (Finset.mem_singleton.mp hxb ▸ hx)]
    subst hZA_eq; exact ⟨rfl, fun _ _ i => Fin.elim0 i, fun _ _ i => Fin.elim0 i⟩

/-- Empty-edge branch of `treeBaseSetupProg` (`a_edge[r_x] == 0`). -/
def treeBaseEmptyProg : Cmd :=
  .seq (.assign r_qA (.const 0)) (.seq (.assign 10 (.const 0))
  (.seq (.assign 11 (.const 0)) (.seq (.assign 12 (.const 0))
  (.seq (.assign 13 (.const 0)) (.seq (.assign 16 (.const 0))
  (.seq (.assign 17 (.const 0)) (.assign 18 (.const 0))))))))

/-- Self-loop branch of `treeBaseSetupProg` (`a_edge[r_x] = e0 + 1` and `u_h = u_t`). -/
def treeBaseLoopProg : Cmd :=
  .seq (.assign 10 (.reg 14)) (.seq (.assign 11 (.const 0))
  (.seq (.assign 16 (.const 1)) (.seq (.assign 17 (.const 0))
  (.seq (.assign 19 (.read a_cap (.reg 10)))
  (.seq (.assign r_qA (.op .lt (.const 1) (.reg 19)))
  (.seq (.write a_acc_zV (.const 0) (.reg 10))
  (.seq (.write a_acc_zI (.const 0) (.const 1))
        (.assign 13 (.op .add (.const 4) (.op .mul (.const 18) (.reg r_qA)))))))))))

/-- Non-loop single-edge branch of `treeBaseSetupProg` (`a_edge[r_x] = e0 + 1` and `u_h ≠ u_t`). -/
def treeBaseNonLoopProg : Cmd :=
  .seq (.assign 16 (.const 1)) (.seq (.assign 17 (.const 1))
  (.seq (.ite (.op .lt (.reg 14) (.reg 15))
      (.seq (.assign 10 (.reg 14)) (.seq (.assign 11 (.reg 15)) (.assign 13 (.const 11))))
      (.seq (.assign 10 (.reg 15)) (.seq (.assign 11 (.reg 14)) (.assign 13 (.const 17)))))
  (.seq (.assign 14 (.read a_cap (.reg 10))) (.seq (.assign 14 (.op .lt (.const 1) (.reg 14)))
  (.seq (.assign 15 (.read a_cap (.reg 11))) (.seq (.assign 15 (.op .lt (.const 1) (.reg 15)))
  (.seq (.write a_acc_zV (.const 0) (.reg 10)) (.seq (.write a_acc_zI (.const 0) (.const 1))
  (.seq (.write a_acc_zV (.reg 14) (.reg 11)) (.seq (.write a_acc_zI (.reg 14) (.const 1))
  (.seq (.assign r_qA (.op .add (.reg 14) (.reg 15)))
  (.seq (.assign 19 (.op .add (.op .mul (.const 18) (.reg 14)) (.op .mul (.const 36) (.reg 15))))
        (.assign 13 (.op .add (.reg 13) (.reg 19)))))))))))))))

/-- Setup gadget for `treeBaseStepProg`: inspects `a_edge[r_x]` and configures registers
`10, 11, 12, 13, 16, 17, 18, r_qA` and arrays `a_acc_zV, a_acc_zI` for `baseTableFillProg`. -/
def treeBaseSetupProg (r_x : Reg) : Cmd :=
  .seq (.assign 19 (.read a_edge (.reg r_x)))
  (.ite (.op .eq (.reg 19) (.const 0)) treeBaseEmptyProg
    (.seq (.assign 12 (.op .sub (.reg 19) (.const 1))) (.seq (.assign 18 (.const 1))
    (.seq (.assign 14 (.read a_head (.reg 12))) (.seq (.assign 15 (.read a_tail (.reg 12)))
    (.ite (.op .eq (.reg 14) (.reg 15)) treeBaseLoopProg treeBaseNonLoopProg))))))

/-- Word RAM program initializing `bufA` with the base table at tree node `r_x`:
`EA = {e | (τ e).1 = x}, VA = pieceVB G EA, ZA = pieceZ G Z EA`. -/
def treeBaseStepProg (δ ξ ω : ℕ) (r_x : Reg) : Cmd :=
  .seq (treeBaseSetupProg r_x) (baseTableFillProg δ ξ ω bufA)

theorem treeBaseSetupProg_exec {w ξ ω : ℕ} (inp : Alg41CoreInput ξ ω)
    (node : Fin inp.t) {r_x : Reg} (_hrx_lt : r_x < 10) (_hrx_qA : r_x ≠ r_qA) {s : State}
    (hw72 : 72 < 2 ^ w) (hn_w : inp.G.numVerts < 2 ^ w)
    (hm1_w : inp.G.numEdges + 1 < 2 ^ w) (ht_w : inp.t < 2 ^ w)
    (hr_x : s.regs r_x = node.1)
    (hhead : s.arrs a_head = List.ofFn (fun e => (inp.G.head e).1))
    (htail : s.arrs a_tail = List.ofFn (fun e => (inp.G.tail e).1))
    (hedge : s.arrs a_edge = List.ofFn (leafEdgeAt inp.τ inp.G.numEdges))
    (hcap : s.arrs a_cap = List.ofFn (capVal inp.G inp.Z))
    (hzV_len : (s.arrs a_acc_zV).length = Q_max ξ ω)
    (hzI_len : (s.arrs a_acc_zI).length = Q_max ξ ω) :
    let EA := Finset.univ.filter (fun e : Fin inp.G.numEdges => (inp.τ e).1 = node.1)
    let VA := pieceVB inp.G EA
    let ZA := pieceZ inp.G inp.Z EA
    have hEA_sub : ∀ e ∈ EA, inp.G.head e ∈ VA ∧ inp.G.tail e ∈ VA :=
      fun _ he => ⟨head_mem_edgeEnds he, tail_mem_edgeEnds he⟩
    ∃ s₁ t_setup bcfg,
      Exec w (treeBaseSetupProg r_x) s s₁ t_setup ∧ t_setup ≤ 80 ∧ bcfg < 72 ∧
      ∃ (hG_loc : pieceLocDigraph inp.G VA EA hEA_sub = canonLocDigraph bcfg),
      (∀ i : Fin VA.card,
        (i ∈ subMaskFinset VA ZA ↔
          (⟨i.1, Nat.lt_of_lt_of_eq i.2 (congrArg ComputeDigraph.numVerts hG_loc)⟩ :
            Fin (canonLocDigraph bcfg).numVerts) ∈ canonLocRoots bcfg)) ∧
      s₁.regs 10 = (if h0 : 0 < VA.card then (finsetRootFn VA ⟨0, h0⟩).1 else 0) ∧
      s₁.regs 11 = (if h1 : 1 < VA.card then (finsetRootFn VA ⟨1, h1⟩).1 else 0) ∧
      s₁.regs 12 = (if he : 0 < EA.card then (finsetRootFn EA ⟨0, he⟩).1 else 0) ∧
      s₁.regs 13 = bcfg ∧
      s₁.regs 16 = (if 0 < VA.card then 1 else 0) ∧
      s₁.regs 17 = (if 1 < VA.card then 1 else 0) ∧
      s₁.regs 18 = (if 0 < EA.card then 1 else 0) ∧
      s₁.regs r_qA = ZA.card ∧
      (s₁.arrs a_acc_zV).length = Q_max ξ ω ∧ (s₁.arrs a_acc_zI).length = Q_max ξ ω ∧
      (∀ i : Fin ZA.card, (s₁.arrs a_acc_zV).getD i.1 0 = (finsetRootFn ZA i).1) ∧
      (∀ i : Fin ZA.card, (s₁.arrs a_acc_zI).getD i.1 0 = subInc inp.G EA (finsetRootFn ZA i)) ∧
      (∀ r < 10, r ≠ r_qA → s₁.regs r = s.regs r) ∧
      (∀ a, a ≠ a_acc_zV → a ≠ a_acc_zI → s₁.arrs a = s.arrs a) := by
  intro EA VA ZA hEA_sub
  have h0_w : 0 < 2 ^ w := by omega
  have hw1 : 1 < 2 ^ w := by omega
  have hnode_w : node.1 < 2 ^ w := Nat.lt_trans node.2 ht_w
  have hQ2 : 2 ≤ Q_max ξ ω := by unfold Q_max; omega
  let ev := leafEdgeAt inp.τ inp.G.numEdges node
  have hev_le : ev ≤ inp.G.numEdges := leafEdgeAt_le inp.τ inp.G.numEdges node
  have hev_w : ev < 2 ^ w := by omega
  let s_a := s.setReg 19 ev
  have hex_a : Exec w (.assign 19 (.read a_edge (.reg r_x))) s s_a 3 :=
    .assign (by simp [Expr.eval, checkWord, hr_x, hnode_w, hedge, node.2, ev, hev_w])
  rcases Nat.eq_zero_or_pos ev with hev0 | hev_pos
  · -- Branch 1: `ev = 0` (`EA = ∅`)
    have hcond0 : (Expr.op .eq (.reg 19) (.const 0)).eval w s_a = some 1 := by
      simp [s_a, hev0, Expr.eval, BinOp.eval, BinOp.raw, checkWord, h0_w, hw1]
    have hEA_emp : EA = ∅ := filter_tau_eq_empty_of_leafEdgeAt_zero inp.τ node hev0
    have hVA_emp : VA = ∅ := by simp [VA, hEA_emp, edgeEnds]
    have hZA_emp : ZA = ∅ :=
      Finset.subset_empty.mp (hVA_emp ▸ pieceZ_subset_pieceVB inp.G inp.Z EA)
    let s₁ := (((((((s_a.setReg r_qA 0).setReg 10 0).setReg 11 0).setReg 12 0).setReg 13 0).setReg
      16 0).setReg 17 0).setReg 18 0
    have hex_emp : Exec w treeBaseEmptyProg s_a s₁ 16 :=
      .seq (.assign (by simp [Expr.eval, checkWord, h0_w]))
      (.seq (.assign (by simp [Expr.eval, checkWord, h0_w]))
      (.seq (.assign (by simp [Expr.eval, checkWord, h0_w]))
      (.seq (.assign (by simp [Expr.eval, checkWord, h0_w]))
      (.seq (.assign (by simp [Expr.eval, checkWord, h0_w]))
      (.seq (.assign (by simp [Expr.eval, checkWord, h0_w]))
      (.seq (.assign (by simp [Expr.eval, checkWord, h0_w]))
            (.assign (by simp [Expr.eval, checkWord, h0_w]))))))))
    have hG_loc : pieceLocDigraph inp.G VA EA hEA_sub = canonLocDigraph 0 :=
      ComputeDigraph.ext_of_numEdges_zero (by simp [hVA_emp, canonLocDigraph])
        (by simp [hEA_emp]) (by rfl)
    refine ⟨s₁, 3 + (3 + 16), 0, .seq hex_a (.ite_true hcond0 (by decide) hex_emp),
      by omega, by decide, hG_loc,
      fun i => by have := Nat.lt_of_lt_of_eq i.2 (by simp [hVA_emp] : VA.card = 0); omega,
      by simp [s₁, hVA_emp], by simp [s₁, hVA_emp], by simp [s₁, hEA_emp],
      by simp [s₁], by simp [s₁, hVA_emp], by simp [s₁, hVA_emp], by simp [s₁, hEA_emp],
      by simp [s₁, hZA_emp], by simp [s₁, s_a, hzV_len], by simp [s₁, s_a, hzI_len],
      fun i => by have := Nat.lt_of_lt_of_eq i.2 (by simp [hZA_emp] : ZA.card = 0); omega,
      fun i => by have := Nat.lt_of_lt_of_eq i.2 (by simp [hZA_emp] : ZA.card = 0); omega,
      fun r hr hrq => by
        simp [s₁, s_a, hrq,
          Nat.ne_of_lt (Nat.lt_of_lt_of_le hr (by decide : 10 ≤ 10)),
          Nat.ne_of_lt (Nat.lt_trans hr (by decide : 10 < 11)),
          Nat.ne_of_lt (Nat.lt_trans hr (by decide : 10 < 12)),
          Nat.ne_of_lt (Nat.lt_trans hr (by decide : 10 < 13)),
          Nat.ne_of_lt (Nat.lt_trans hr (by decide : 10 < 16)),
          Nat.ne_of_lt (Nat.lt_trans hr (by decide : 10 < 17)),
          Nat.ne_of_lt (Nat.lt_trans hr (by decide : 10 < 18)),
          Nat.ne_of_lt (Nat.lt_trans hr (by decide : 10 < 19))],
      fun a _ _ => by simp [s₁, s_a]⟩
  · -- Branch 2: `ev = e0 + 1` (`EA = {e}`)
    obtain ⟨e0, hev_eq⟩ : ∃ e0, ev = e0 + 1 := ⟨ev - 1, by omega⟩
    have he01_w : e0 + 1 < 2 ^ w := by omega
    have hcond0 : (Expr.op .eq (.reg 19) (.const 0)).eval w s_a = some 0 := by
      simp [s_a, hev_eq, Expr.eval, BinOp.eval, BinOp.raw, checkWord, h0_w, he01_w]
    rcases filter_tau_eq_singleton_of_leafEdgeAt_succ inp.τ node (inp.hleaf node.1) hev_eq with
      ⟨he0_lt, _hτ_e0, hEA_eq'⟩
    let e : Fin inp.G.numEdges := ⟨e0, he0_lt⟩
    have hEA_eq : EA = {e} := hEA_eq'
    have he0_w : e0 < 2 ^ w := by omega
    have hEA_card : EA.card = 1 := by rw [hEA_eq, Finset.card_singleton]
    have hEA_root : ∀ i : Fin EA.card, finsetRootFn EA i = e :=
      fun i => Finset.mem_singleton.mp (hEA_eq ▸ finsetRootFn_mem EA i)
    let u_h := inp.G.head e
    let u_t := inp.G.tail e
    have huh_w : u_h.1 < 2 ^ w := Nat.lt_trans u_h.2 hn_w
    have hut_w : u_t.1 < 2 ^ w := Nat.lt_trans u_t.2 hn_w
    have hVA_eq : VA = {u_h, u_t} := by dsimp [VA]; rw [hEA_eq, pieceVB_singleton]
    let s_b := (((s_a.setReg 12 e0).setReg 18 1).setReg 14 u_h.1).setReg 15 u_t.1
    have hex_b1 : Exec w (.assign 12 (.op .sub (.reg 19) (.const 1))) s_a (s_a.setReg 12 e0) 4 :=
      .assign (by simp [s_a, hev_eq, Expr.eval, BinOp.eval, BinOp.raw, checkWord, hw1, he0_w, he01_w])
    have hex_b2 : Exec w (.assign 18 (.const 1)) (s_a.setReg 12 e0)
        ((s_a.setReg 12 e0).setReg 18 1) 2 := .assign (by simp [Expr.eval, checkWord, hw1])
    have hex_b3 : Exec w (.assign 14 (.read a_head (.reg 12)))
        ((s_a.setReg 12 e0).setReg 18 1) (((s_a.setReg 12 e0).setReg 18 1).setReg 14 u_h.1) 3 :=
      .assign (by simp [s_a, Expr.eval, checkWord, he0_w, hhead, he0_lt, e, u_h, huh_w])
    have hex_b4 : Exec w (.assign 15 (.read a_tail (.reg 12)))
        (((s_a.setReg 12 e0).setReg 18 1).setReg 14 u_h.1) s_b 3 :=
      .assign (by simp [s_a, Expr.eval, checkWord, he0_w, htail, he0_lt, e, u_t, hut_w])
    by_cases hloop : u_h.1 = u_t.1
    · -- Subcase 2a: Self-loop (`u_h = u_t`)
      have huh_eq_ut : u_h = u_t := Fin.ext hloop
      have hcond_loop : (Expr.op .eq (.reg 14) (.reg 15)).eval w s_b = some 1 := by
        simp [s_b, hloop, Expr.eval, BinOp.eval, BinOp.raw, checkWord, hut_w, hw1]
      have hVA_single : VA = {u_h} := by rw [hVA_eq, huh_eq_ut, Finset.pair_eq_singleton]
      have hVA_card : VA.card = 1 := by rw [hVA_single, Finset.card_singleton]
      have hVA_root : ∀ i : Fin VA.card, finsetRootFn VA i = u_h :=
        fun i => Finset.mem_singleton.mp (hVA_single ▸ finsetRootFn_mem VA i)
      let cap_h := capVal inp.G inp.Z u_h
      have hcap_h_le : cap_h ≤ inp.G.numEdges + 1 := by
        dsimp [cap_h, capVal]; split_ifs with hZ
        · omega
        · have := totalInc_le_numEdges inp.G u_h; omega
      have hcap_h_w : cap_h < 2 ^ w := by omega
      let b₀ : ℕ := if 1 < cap_h then 1 else 0
      have hb0_w : b₀ < 2 ^ w := by dsimp [b₀]; split_ifs <;> omega
      let bcfg := 4 + 18 * b₀
      have hbcfg_lt : bcfg < 72 := by dsimp [bcfg, b₀]; split_ifs <;> omega
      have hsub_uh : subInc inp.G EA u_h = 1 := by
        rw [hEA_eq]; exact subInc_singleton_of_mem e (Or.inl rfl)
      have huh_ZA_iff : u_h ∈ ZA ↔ 1 < cap_h := by
        dsimp [ZA]; rw [mem_pieceZ_iff_subInc_lt_capVal, hsub_uh]; simp [cap_h]
      have hZA_sub : ZA ⊆ {u_h} := hVA_single ▸ pieceZ_subset_pieceVB inp.G inp.Z EA
      have hZA_card : ZA.card = b₀ := by
        dsimp [b₀]; split_ifs with h1
        · have hZA_eq : ZA = {u_h} :=
            Finset.Subset.antisymm hZA_sub (Finset.singleton_subset_iff.mpr (huh_ZA_iff.mpr h1))
          rw [hZA_eq, Finset.card_singleton]
        · have huh_not : u_h ∉ ZA := fun h => h1 (huh_ZA_iff.mp h)
          have hZA_eq : ZA = ∅ := by
            ext x; simp only [Finset.notMem_empty, iff_false]
            intro hx; exact huh_not (Finset.mem_singleton.mp (hZA_sub hx) ▸ hx)
          rw [hZA_eq, Finset.card_empty]
      let s_l1 := (((s_b.setReg 10 u_h.1).setReg 11 0).setReg 16 1).setReg 17 0
      have hex_l1 : Exec w (.assign 10 (.reg 14)) s_b (s_b.setReg 10 u_h.1) 2 :=
        .assign (by simp [s_b, Expr.eval, checkWord, huh_w])
      have hex_l2 : Exec w (.assign 11 (.const 0)) (s_b.setReg 10 u_h.1)
          ((s_b.setReg 10 u_h.1).setReg 11 0) 2 := .assign (by simp [Expr.eval, checkWord, h0_w])
      have hex_l3 : Exec w (.assign 16 (.const 1)) ((s_b.setReg 10 u_h.1).setReg 11 0)
          (((s_b.setReg 10 u_h.1).setReg 11 0).setReg 16 1) 2 :=
        .assign (by simp [Expr.eval, checkWord, hw1])
      have hex_l4 : Exec w (.assign 17 (.const 0)) (((s_b.setReg 10 u_h.1).setReg 11 0).setReg 16 1) s_l1 2 :=
        .assign (by simp [Expr.eval, checkWord, h0_w])
      let s_l5 := s_l1.setReg 19 cap_h
      have hex_l5 : Exec w (.assign 19 (.read a_cap (.reg 10))) s_l1 s_l5 3 :=
        .assign (by simp [s_l1, s_b, s_a, Expr.eval, checkWord, huh_w, hcap, u_h.2, cap_h, hcap_h_w])
      let s_l6 := s_l5.setReg r_qA b₀
      have hex_l6 : Exec w (.assign r_qA (.op .lt (.const 1) (.reg 19))) s_l5 s_l6 4 :=
        .assign (by simp [s_l5, Expr.eval, BinOp.eval, BinOp.raw, checkWord, hw1, hcap_h_w, b₀, hb0_w])
      let s_l7 := s_l6.writeArr a_acc_zV 0 u_h.1
      have hex_l7 : Exec w (.write a_acc_zV (.const 0) (.reg 10)) s_l6 s_l7 3 :=
        .write (by simp [Expr.eval, checkWord, h0_w])
               (by simp [s_l6, s_l5, s_l1, Expr.eval, checkWord, huh_w])
               (by simp [s_l6, s_l5, s_l1, s_b, s_a, hzV_len]; omega)
      let s_l8 := s_l7.writeArr a_acc_zI 0 1
      have hex_l8 : Exec w (.write a_acc_zI (.const 0) (.const 1)) s_l7 s_l8 3 :=
        .write (by simp [Expr.eval, checkWord, h0_w]) (by simp [Expr.eval, checkWord, hw1])
               (by simp [s_l7, s_l6, s_l5, s_l1, s_b, s_a, hzI_len]; omega)
      let s₁ := s_l8.setReg 13 bcfg
      have hex_l9 : Exec w (.assign 13 (.op .add (.const 4) (.op .mul (.const 18) (.reg r_qA)))) s_l8 s₁ 6 :=
        .assign (by
          have h4_w : 4 < 2 ^ w := by omega
          have h18_w : 18 < 2 ^ w := by omega
          have h18b_w : 18 * b₀ < 2 ^ w := by dsimp [b₀]; split_ifs <;> omega
          have hbcfg_w : bcfg < 2 ^ w := by omega
          simp [s_l8, s_l7, s_l6, Expr.eval, BinOp.eval, BinOp.raw, checkWord,
            h4_w, h18_w, hb0_w, h18b_w, bcfg, hbcfg_w])
      have hex_loop : Exec w treeBaseLoopProg s_b s₁
          (2 + (2 + (2 + (2 + (3 + (4 + (3 + (3 + 6)))))))) :=
        .seq hex_l1 (.seq hex_l2 (.seq hex_l3 (.seq hex_l4
          (.seq hex_l5 (.seq hex_l6 (.seq hex_l7 (.seq hex_l8 hex_l9)))))))
      have hm1_loc : (pieceLocDigraph inp.G VA EA hEA_sub).numEdges = 1 := hEA_card
      have hm2_loc : (canonLocDigraph bcfg).numEdges = 1 := by
        change (if bcfg % 3 = 0 then 0 else (bcfg / 3) % 2) = 1
        by_cases h1 : 1 < cap_h <;> simp [bcfg, b₀, h1]
      have hG_loc : pieceLocDigraph inp.G VA EA hEA_sub = canonLocDigraph bcfg := by
        refine ComputeDigraph.ext_of_numEdges_one ?_ hm1_loc hm2_loc ?_ ?_
        · change VA.card = bcfg % 3; rw [hVA_card]; by_cases h1 : 1 < cap_h <;> simp [bcfg, b₀, h1]
        · have hlt_v : ((pieceLocDigraph inp.G VA EA hEA_sub).head ⟨0, by omega⟩).1 < 1 := by
            have := ((pieceLocDigraph inp.G VA EA hEA_sub).head ⟨0, by omega⟩).2
            change _ < VA.card at this; omega
          have h0 : ((pieceLocDigraph inp.G VA EA hEA_sub).head ⟨0, by omega⟩).1 = 0 := by omega
          rw [h0]; change 0 = ((canonLocDigraph bcfg).head ⟨0, _⟩).1
          by_cases h1 : 1 < cap_h <;> simp [canonLocDigraph, bcfg, b₀, h1]
        · have hlt_v : ((pieceLocDigraph inp.G VA EA hEA_sub).tail ⟨0, by omega⟩).1 < 1 := by
            have := ((pieceLocDigraph inp.G VA EA hEA_sub).tail ⟨0, by omega⟩).2
            change _ < VA.card at this; omega
          have h0 : ((pieceLocDigraph inp.G VA EA hEA_sub).tail ⟨0, by omega⟩).1 = 0 := by omega
          rw [h0]; change 0 = ((canonLocDigraph bcfg).tail ⟨0, _⟩).1
          by_cases h1 : 1 < cap_h <;> simp [canonLocDigraph, bcfg, b₀, h1]
      have hZ_loc : ∀ i : Fin VA.card,
          (i ∈ subMaskFinset VA ZA ↔
            (⟨i.1, Nat.lt_of_lt_of_eq i.2 (congrArg ComputeDigraph.numVerts hG_loc)⟩ :
              Fin (canonLocDigraph bcfg).numVerts) ∈ canonLocRoots bcfg) := by
        intro i; have hi0 : i.1 = 0 := by have := i.2; omega
        simp only [subMaskFinset, canonLocRoots, Finset.mem_filter, Finset.mem_univ, true_and,
          hVA_root i, huh_ZA_iff, hi0]
        dsimp [bcfg, b₀]; by_cases h1 : 1 < cap_h <;> simp [h1]
      refine ⟨s₁, 3 + (3 + (4 + (2 + (3 + (3 + (3 + (2 + (2 + (2 + (2 + (3 + (4 + (3 + (3 + 6)))))))))))))),
        bcfg, .seq hex_a (.ite_false hcond0 (.seq hex_b1 (.seq hex_b2 (.seq hex_b3 (.seq hex_b4
          (.ite_true hcond_loop (by decide) hex_loop)))))),
        by omega, hbcfg_lt, hG_loc, hZ_loc,
        by simp [s₁, s_l8, s_l7, s_l6, s_l5, s_l1, hVA_card, hVA_root ⟨0, by omega⟩],
        by simp [s₁, s_l8, s_l7, s_l6, s_l5, s_l1, hVA_card],
        by simp [s₁, s_l8, s_l7, s_l6, s_l5, s_l1, s_b, hEA_card, hEA_root ⟨0, by omega⟩, e],
        by simp [s₁], by simp [s₁, s_l8, s_l7, s_l6, s_l5, s_l1, hVA_card],
        by simp [s₁, s_l8, s_l7, s_l6, s_l5, s_l1, hVA_card],
        by simp [s₁, s_l8, s_l7, s_l6, s_l5, s_l1, s_b, hEA_card],
        by simp [s₁, s_l8, s_l7, s_l6, hZA_card],
        by simp [s₁, s_l8, s_l7, s_l6, s_l5, s_l1, s_b, s_a, hzV_len],
        by simp [s₁, s_l8, s_l7, s_l6, s_l5, s_l1, s_b, s_a, hzI_len],
        fun i => by
          have hi_lt := Nat.lt_of_lt_of_eq i.2 hZA_card
          have hb0_le : b₀ ≤ 1 := by dsimp [b₀]; split_ifs <;> omega
          have hi0 : i.1 = 0 := by omega
          have hroot := Finset.mem_singleton.mp (hZA_sub (finsetRootFn_mem ZA i))
          have hs1_zV : s₁.arrs a_acc_zV = (s.arrs a_acc_zV).set 0 u_h.1 := by
            simp [s₁, s_l8, s_l7, s_l6, s_l5, s_l1, s_b, s_a]
          rw [hi0, hroot, hs1_zV, getD_set_eq _ 0 u_h.1 (by omega)],
        fun i => by
          have hi_lt := Nat.lt_of_lt_of_eq i.2 hZA_card
          have hb0_le : b₀ ≤ 1 := by dsimp [b₀]; split_ifs <;> omega
          have hi0 : i.1 = 0 := by omega
          have hroot := Finset.mem_singleton.mp (hZA_sub (finsetRootFn_mem ZA i))
          have hs1_zI : s₁.arrs a_acc_zI = (s.arrs a_acc_zI).set 0 1 := by
            simp [s₁, s_l8, s_l7, s_l6, s_l5, s_l1, s_b, s_a]
          rw [hi0, hroot, hsub_uh, hs1_zI, getD_set_eq _ 0 1 (by omega)],
        fun r hr hrq => by
          simp [s₁, s_l8, s_l7, s_l6, s_l5, s_l1, s_b, s_a, hrq,
            Nat.ne_of_lt (Nat.lt_of_lt_of_le hr (by decide : 10 ≤ 10)),
            Nat.ne_of_lt (Nat.lt_trans hr (by decide : 10 < 11)),
            Nat.ne_of_lt (Nat.lt_trans hr (by decide : 10 < 12)),
            Nat.ne_of_lt (Nat.lt_trans hr (by decide : 10 < 13)),
            Nat.ne_of_lt (Nat.lt_trans hr (by decide : 10 < 14)),
            Nat.ne_of_lt (Nat.lt_trans hr (by decide : 10 < 15)),
            Nat.ne_of_lt (Nat.lt_trans hr (by decide : 10 < 16)),
            Nat.ne_of_lt (Nat.lt_trans hr (by decide : 10 < 17)),
            Nat.ne_of_lt (Nat.lt_trans hr (by decide : 10 < 18)),
            Nat.ne_of_lt (Nat.lt_trans hr (by decide : 10 < 19))],
        fun a ha1 ha2 => by simp [s₁, s_l8, s_l7, s_l6, s_l5, s_l1, s_b, s_a, ha1, ha2]⟩
    · -- Subcase 2b: Non-loop edge (`u_h ≠ u_t`)
      have hcond_loop : (Expr.op .eq (.reg 14) (.reg 15)).eval w s_b = some 0 := by
        simp [s_b, hloop, Expr.eval, BinOp.eval, BinOp.raw, checkWord, huh_w, hut_w, h0_w]
      let v_min : Fin inp.G.numVerts := if u_h.1 < u_t.1 then u_h else u_t
      let v_max : Fin inp.G.numVerts := if u_h.1 < u_t.1 then u_t else u_h
      let dir : ℕ := if u_h.1 < u_t.1 then 1 else 2
      have hv_lt : v_min < v_max := by
        dsimp [v_min, v_max]; split_ifs with hlt
        · exact hlt
        · exact Nat.lt_of_le_of_ne (Nat.not_lt.mp hlt) (Ne.symm hloop)
      have hVA_pair : VA = {v_min, v_max} := by
        rw [hVA_eq]; dsimp [v_min, v_max]; split_ifs with hlt <;> [rfl; exact Finset.pair_comm u_h u_t]
      have hVA_card : VA.card = 2 := by rw [hVA_pair]; exact card_pair_of_lt hv_lt
      have hVA_root0 : finsetRootFn VA ⟨0, by omega⟩ = v_min :=
        (finsetRootFn_congr hVA_pair 0 (by omega) (by rw [card_pair_of_lt hv_lt]; decide)).trans
          (finsetRootFn_pair_zero hv_lt)
      have hVA_root1 : finsetRootFn VA ⟨1, by omega⟩ = v_max :=
        (finsetRootFn_congr hVA_pair 1 (by omega) (by rw [card_pair_of_lt hv_lt]; decide)).trans
          (finsetRootFn_pair_one hv_lt)
      have hvmin_w : v_min.1 < 2 ^ w := Nat.lt_trans v_min.2 hn_w
      have hvmax_w : v_max.1 < 2 ^ w := Nat.lt_trans v_max.2 hn_w
      let s_c0 := (s_b.setReg 16 1).setReg 17 1
      have hex_c1 : Exec w (.assign 16 (.const 1)) s_b (s_b.setReg 16 1) 2 :=
        .assign (by simp [Expr.eval, checkWord, hw1])
      have hex_c2 : Exec w (.assign 17 (.const 1)) (s_b.setReg 16 1) s_c0 2 :=
        .assign (by simp [Expr.eval, checkWord, hw1])
      let s_c := ((s_c0.setReg 10 v_min.1).setReg 11 v_max.1).setReg 13 (5 + 6 * dir)
      have hex_c3_ex : ∃ tc3 ≤ 10,
          Exec w (.ite (.op .lt (.reg 14) (.reg 15))
            (.seq (.assign 10 (.reg 14)) (.seq (.assign 11 (.reg 15)) (.assign 13 (.const 11))))
            (.seq (.assign 10 (.reg 15)) (.seq (.assign 11 (.reg 14)) (.assign 13 (.const 17)))))
            s_c0 s_c tc3 := by
        by_cases hlt : u_h.1 < u_t.1
        · have hcond_lt : (Expr.op .lt (.reg 14) (.reg 15)).eval w s_c0 = some 1 := by
            simp [s_c0, s_b, hlt, Expr.eval, BinOp.eval, BinOp.raw, checkWord, huh_w, hut_w, hw1]
          have hsc_eq : s_c = ((s_c0.setReg 10 u_h.1).setReg 11 u_t.1).setReg 13 11 := by
            simp [s_c, v_min, v_max, dir, hlt]
          rw [hsc_eq]; refine ⟨3 + (2 + (2 + 2)), by omega, .ite_true hcond_lt (by decide) ?_⟩
          exact .seq (.assign (by simp [s_c0, s_b, Expr.eval, checkWord, huh_w]))
            (.seq (.assign (by simp [s_c0, s_b, Expr.eval, checkWord, hut_w]))
                  (.assign (by simp [Expr.eval, checkWord, show 11 < 2 ^ w by omega])))
        · have hcond_lt : (Expr.op .lt (.reg 14) (.reg 15)).eval w s_c0 = some 0 := by
            simp [s_c0, s_b, hlt, Expr.eval, BinOp.eval, BinOp.raw, checkWord, huh_w, hut_w, h0_w]
          have hsc_eq : s_c = ((s_c0.setReg 10 u_t.1).setReg 11 u_h.1).setReg 13 17 := by
            simp [s_c, v_min, v_max, dir, hlt]
          rw [hsc_eq]; refine ⟨3 + (2 + (2 + 2)), by omega, .ite_false hcond_lt ?_⟩
          exact .seq (.assign (by simp [s_c0, s_b, Expr.eval, checkWord, hut_w]))
            (.seq (.assign (by simp [s_c0, s_b, Expr.eval, checkWord, huh_w]))
                  (.assign (by simp [Expr.eval, checkWord, show 17 < 2 ^ w by omega])))
      rcases hex_c3_ex with ⟨tc3, htc3, hex_c3⟩
      let cap0 := capVal inp.G inp.Z v_min
      let cap1 := capVal inp.G inp.Z v_max
      have hcap0_le : cap0 ≤ inp.G.numEdges + 1 := by
        dsimp [cap0, capVal]; split_ifs with hZ <;> [omega; (have := totalInc_le_numEdges inp.G v_min; omega)]
      have hcap1_le : cap1 ≤ inp.G.numEdges + 1 := by
        dsimp [cap1, capVal]; split_ifs with hZ <;> [omega; (have := totalInc_le_numEdges inp.G v_max; omega)]
      have hcap0_w : cap0 < 2 ^ w := by omega
      have hcap1_w : cap1 < 2 ^ w := by omega
      let b₀ : ℕ := if 1 < cap0 then 1 else 0
      let b₁ : ℕ := if 1 < cap1 then 1 else 0
      have hb0_w : b₀ < 2 ^ w := by dsimp [b₀]; split_ifs <;> omega
      have hb1_w : b₁ < 2 ^ w := by dsimp [b₁]; split_ifs <;> omega
      let bcfg := (5 + 6 * dir) + (18 * b₀ + 36 * b₁)
      have hdir_cases : dir = 1 ∨ dir = 2 := by dsimp [dir]; split_ifs <;> omega
      have hb0_cases : b₀ = 0 ∨ b₀ = 1 := by dsimp [b₀]; split_ifs <;> omega
      have hb1_cases : b₁ = 0 ∨ b₁ = 1 := by dsimp [b₁]; split_ifs <;> omega
      have hbcfg_lt : bcfg < 72 := by
        rcases hdir_cases with hd | hd <;> rcases hb0_cases with h0 | h0 <;>
          rcases hb1_cases with h1 | h1 <;> omega
      let s_d1 := s_c.setReg 14 cap0
      have hex_d1 : Exec w (.assign 14 (.read a_cap (.reg 10))) s_c s_d1 3 :=
        .assign (by simp [s_c, s_c0, s_b, s_a, Expr.eval, checkWord, hvmin_w, hcap, v_min.2, cap0, hcap0_w])
      let s_d2 := s_d1.setReg 14 b₀
      have hex_d2 : Exec w (.assign 14 (.op .lt (.const 1) (.reg 14))) s_d1 s_d2 4 :=
        .assign (by simp [s_d1, Expr.eval, BinOp.eval, BinOp.raw, checkWord, hw1, hcap0_w, b₀, hb0_w])
      let s_d3 := s_d2.setReg 15 cap1
      have hex_d3 : Exec w (.assign 15 (.read a_cap (.reg 11))) s_d2 s_d3 3 :=
        .assign (by simp [s_d2, s_d1, s_c, s_c0, s_b, s_a, Expr.eval, checkWord, hvmax_w, hcap, v_max.2, cap1, hcap1_w])
      let s_d4 := s_d3.setReg 15 b₁
      have hex_d4 : Exec w (.assign 15 (.op .lt (.const 1) (.reg 15))) s_d3 s_d4 4 :=
        .assign (by simp [s_d3, Expr.eval, BinOp.eval, BinOp.raw, checkWord, hw1, hcap1_w, b₁, hb1_w])
      let s_d5 := s_d4.writeArr a_acc_zV 0 v_min.1
      have hex_d5 : Exec w (.write a_acc_zV (.const 0) (.reg 10)) s_d4 s_d5 3 :=
        .write (by simp [Expr.eval, checkWord, h0_w])
               (by simp [s_d4, s_d3, s_d2, s_d1, s_c, Expr.eval, checkWord, hvmin_w])
               (by simp [s_d4, s_d3, s_d2, s_d1, s_c, s_c0, s_b, s_a, hzV_len]; omega)
      let s_d6 := s_d5.writeArr a_acc_zI 0 1
      have hex_d6 : Exec w (.write a_acc_zI (.const 0) (.const 1)) s_d5 s_d6 3 :=
        .write (by simp [Expr.eval, checkWord, h0_w]) (by simp [Expr.eval, checkWord, hw1])
               (by simp [s_d5, s_d4, s_d3, s_d2, s_d1, s_c, s_c0, s_b, s_a, hzI_len]; omega)
      let s_d7 := s_d6.writeArr a_acc_zV b₀ v_max.1
      have hex_d7 : Exec w (.write a_acc_zV (.reg 14) (.reg 11)) s_d6 s_d7 3 :=
        .write (by simp [s_d6, s_d5, s_d4, s_d3, s_d2, Expr.eval, checkWord, hb0_w])
               (by simp [s_d6, s_d5, s_d4, s_d3, s_d2, s_d1, s_c, Expr.eval, checkWord, hvmax_w])
               (by simp [s_d6, s_d5, s_d4, s_d3, s_d2, s_d1, s_c, s_c0, s_b, s_a, hzV_len]
                   rcases hb0_cases with h0 | h0 <;> omega)
      let s_d8 := s_d7.writeArr a_acc_zI b₀ 1
      have hex_d8 : Exec w (.write a_acc_zI (.reg 14) (.const 1)) s_d7 s_d8 3 :=
        .write (by simp [s_d7, s_d6, s_d5, s_d4, s_d3, s_d2, Expr.eval, checkWord, hb0_w])
               (by simp [Expr.eval, checkWord, hw1])
               (by simp [s_d7, s_d6, s_d5, s_d4, s_d3, s_d2, s_d1, s_c, s_c0, s_b, s_a, hzI_len]
                   rcases hb0_cases with h0 | h0 <;> omega)
      let s_d9 := s_d8.setReg r_qA (b₀ + b₁)
      have hex_d9 : Exec w (.assign r_qA (.op .add (.reg 14) (.reg 15))) s_d8 s_d9 4 :=
        .assign (by
          have hsum_w : b₀ + b₁ < 2 ^ w := by rcases hb0_cases with h0 | h0 <;> rcases hb1_cases with h1 | h1 <;> omega
          simp [s_d8, s_d7, s_d6, s_d5, s_d4, s_d3, s_d2, Expr.eval, BinOp.eval, BinOp.raw,
            checkWord, hb0_w, hb1_w, hsum_w])
      let s_d10 := s_d9.setReg 19 (18 * b₀ + 36 * b₁)
      have hex_d10 : Exec w (.assign 19 (.op .add (.op .mul (.const 18) (.reg 14))
          (.op .mul (.const 36) (.reg 15)))) s_d9 s_d10 8 :=
        .assign (by
          have h18_w : 18 < 2 ^ w := by omega
          have h36_w : 36 < 2 ^ w := by omega
          have h18b_w : 18 * b₀ < 2 ^ w := by rcases hb0_cases with h0 | h0 <;> omega
          have h36b_w : 36 * b₁ < 2 ^ w := by rcases hb1_cases with h1 | h1 <;> omega
          have h19_w : 18 * b₀ + 36 * b₁ < 2 ^ w := by rcases hb0_cases with h0 | h0 <;> rcases hb1_cases with h1 | h1 <;> omega
          simp [s_d9, s_d8, s_d7, s_d6, s_d5, s_d4, s_d3, s_d2, Expr.eval, BinOp.eval, BinOp.raw,
            checkWord, h18_w, h36_w, hb0_w, hb1_w, h18b_w, h36b_w, h19_w])
      let s₁ := s_d10.setReg 13 bcfg
      have hex_d11 : Exec w (.assign 13 (.op .add (.reg 13) (.reg 19))) s_d10 s₁ 4 :=
        .assign (by
          have h13_w : 5 + 6 * dir < 2 ^ w := by rcases hdir_cases with hd | hd <;> omega
          have h19_w : 18 * b₀ + 36 * b₁ < 2 ^ w := by rcases hb0_cases with h0 | h0 <;> rcases hb1_cases with h1 | h1 <;> omega
          have hbcfg_w : bcfg < 2 ^ w := by omega
          simp [s_d10, s_d9, s_d8, s_d7, s_d6, s_d5, s_d4, s_d3, s_d2, s_d1, s_c,
            Expr.eval, BinOp.eval, BinOp.raw, checkWord, h13_w, h19_w, bcfg, hbcfg_w])
      have hex_nonloop : Exec w treeBaseNonLoopProg s_b s₁
          (2 + (2 + (tc3 + (3 + (4 + (3 + (4 + (3 + (3 + (3 + (3 + (4 + (8 + 4))))))))))))) :=
        .seq hex_c1 (.seq hex_c2 (.seq hex_c3 (.seq hex_d1 (.seq hex_d2 (.seq hex_d3
          (.seq hex_d4 (.seq hex_d5 (.seq hex_d6 (.seq hex_d7 (.seq hex_d8 (.seq hex_d9
            (.seq hex_d10 hex_d11))))))))))))
      have hsub_vmin : subInc inp.G EA v_min = 1 := by
        rw [hEA_eq]; refine subInc_singleton_of_mem e ?_
        dsimp [v_min]; split_ifs <;> [exact Or.inl rfl; exact Or.inr rfl]
      have hsub_vmax : subInc inp.G EA v_max = 1 := by
        rw [hEA_eq]; refine subInc_singleton_of_mem e ?_
        dsimp [v_max]; split_ifs <;> [exact Or.inr rfl; exact Or.inl rfl]
      have hvmin_ZA_iff : v_min ∈ ZA ↔ 1 < cap0 := by
        dsimp [ZA]; rw [mem_pieceZ_iff_subInc_lt_capVal, hsub_vmin]; simp [cap0]
      have hvmax_ZA_iff : v_max ∈ ZA ↔ 1 < cap1 := by
        dsimp [ZA]; rw [mem_pieceZ_iff_subInc_lt_capVal, hsub_vmax]; simp [cap1]
      have hb0_eq : b₀ = (if v_min ∈ ZA then 1 else 0) := by dsimp [b₀]; simp [hvmin_ZA_iff]
      have hb1_eq : b₁ = (if v_max ∈ ZA then 1 else 0) := by dsimp [b₁]; simp [hvmax_ZA_iff]
      have hZA_sub : ZA ⊆ {v_min, v_max} := hVA_pair ▸ pieceZ_subset_pieceVB inp.G inp.Z EA
      rcases subset_pair_spec hv_lt hZA_sub with ⟨hZA_card, hzV_pair, hzI_pair⟩
      rw [← hb0_eq, ← hb1_eq] at hZA_card; rw [← hb0_eq] at hzV_pair hzI_pair
      have hm1_loc : (pieceLocDigraph inp.G VA EA hEA_sub).numEdges = 1 := hEA_card
      have hm2_loc : (canonLocDigraph bcfg).numEdges = 1 := by
        change (if bcfg % 3 = 0 then 0 else (bcfg / 3) % 2) = 1
        rcases hdir_cases with hd | hd <;> rcases hb0_cases with h0 | h0 <;>
          rcases hb1_cases with h1 | h1 <;> simp [bcfg, hd, h0, h1]
      have hG_loc : pieceLocDigraph inp.G VA EA hEA_sub = canonLocDigraph bcfg := by
        refine ComputeDigraph.ext_of_numEdges_one ?_ hm1_loc hm2_loc ?_ ?_
        · change VA.card = bcfg % 3; rw [hVA_card]
          rcases hdir_cases with hd | hd <;> rcases hb0_cases with h0 | h0 <;>
            rcases hb1_cases with h1 | h1 <;> simp [bcfg, hd, h0, h1]
        · have hhd := pieceLocDigraph_head_eq inp.G VA EA hEA_sub ⟨0, by omega⟩
          rw [hEA_root ⟨0, by omega⟩] at hhd
          by_cases hlt : u_h.1 < u_t.1
          · have hvh : inp.G.head e = finsetRootFn VA ⟨0, by omega⟩ := by rw [hVA_root0]; simp [v_min, u_h, hlt]
            have h0 := congrArg Fin.val (finsetRootFn_injective VA (hhd.trans hvh))
            have hd : dir = 1 := by simp [dir, hlt]
            rw [h0]; change 0 = ((canonLocDigraph bcfg).head ⟨0, _⟩).1
            rcases hb0_cases with h0' | h0' <;> rcases hb1_cases with h1' | h1' <;>
              (dsimp [canonLocDigraph, bcfg]; simp [hd, h0', h1'])
          · have hvh : inp.G.head e = finsetRootFn VA ⟨1, by omega⟩ := by rw [hVA_root1]; simp [v_max, u_h, hlt]
            have h1 := congrArg Fin.val (finsetRootFn_injective VA (hhd.trans hvh))
            have hd : dir = 2 := by simp [dir, hlt]
            rw [h1]; change 1 = ((canonLocDigraph bcfg).head ⟨0, _⟩).1
            rcases hb0_cases with h0' | h0' <;> rcases hb1_cases with h1' | h1' <;>
              (dsimp [canonLocDigraph, bcfg]; simp [hd, h0', h1'])
        · have htl := pieceLocDigraph_tail_eq inp.G VA EA hEA_sub ⟨0, by omega⟩
          rw [hEA_root ⟨0, by omega⟩] at htl
          by_cases hlt : u_h.1 < u_t.1
          · have hvt : inp.G.tail e = finsetRootFn VA ⟨1, by omega⟩ := by rw [hVA_root1]; simp [v_max, u_t, hlt]
            have h1 := congrArg Fin.val (finsetRootFn_injective VA (htl.trans hvt))
            have hd : dir = 1 := by simp [dir, hlt]
            rw [h1]; change 1 = ((canonLocDigraph bcfg).tail ⟨0, _⟩).1
            rcases hb0_cases with h0' | h0' <;> rcases hb1_cases with h1' | h1' <;>
              (dsimp [canonLocDigraph, bcfg]; simp [hd, h0', h1'])
          · have hvt : inp.G.tail e = finsetRootFn VA ⟨0, by omega⟩ := by rw [hVA_root0]; simp [v_min, u_t, hlt]
            have h0 := congrArg Fin.val (finsetRootFn_injective VA (htl.trans hvt))
            have hd : dir = 2 := by simp [dir, hlt]
            rw [h0]; change 0 = ((canonLocDigraph bcfg).tail ⟨0, _⟩).1
            rcases hb0_cases with h0' | h0' <;> rcases hb1_cases with h1' | h1' <;>
              (dsimp [canonLocDigraph, bcfg]; simp [hd, h0', h1'])
      have hZ_loc : ∀ i : Fin VA.card,
          (i ∈ subMaskFinset VA ZA ↔
            (⟨i.1, Nat.lt_of_lt_of_eq i.2 (congrArg ComputeDigraph.numVerts hG_loc)⟩ :
              Fin (canonLocDigraph bcfg).numVerts) ∈ canonLocRoots bcfg) := by
        intro i; have hi2 : i.1 < 2 := Nat.lt_of_lt_of_eq i.2 hVA_card
        have hbcfg_18 : (bcfg / 18) % 2 = b₀ := by
          rcases hdir_cases with hd | hd <;> rcases hb0_cases with h0 | h0 <;>
            rcases hb1_cases with h1 | h1 <;> (dsimp [bcfg]; rw [hd, h0, h1])
        have hbcfg_36 : (bcfg / 36) % 2 = b₁ := by
          rcases hdir_cases with hd | hd <;> rcases hb0_cases with h0 | h0 <;>
            rcases hb1_cases with h1 | h1 <;> (dsimp [bcfg]; rw [hd, h0, h1])
        simp only [subMaskFinset, canonLocRoots, Finset.mem_filter, Finset.mem_univ, true_and,
          hbcfg_18, hbcfg_36]
        rcases (by omega : i.1 = 0 ∨ i.1 = 1) with hi0 | hi1
        · rw [hi0, show i = ⟨0, by omega⟩ from Fin.ext hi0, hVA_root0, hb0_eq]; by_cases h0 : v_min ∈ ZA <;> simp [h0]
        · rw [hi1, show i = ⟨1, by omega⟩ from Fin.ext hi1, hVA_root1, hb1_eq]; by_cases h1 : v_max ∈ ZA <;> simp [h1]
      refine ⟨s₁, 3 + (3 + (4 + (2 + (3 + (3 + (3 +
        (2 + (2 + (tc3 + (3 + (4 + (3 + (4 + (3 + (3 + (3 + (3 + (4 + (8 + 4))))))))))))))))))),
        bcfg, .seq hex_a (.ite_false hcond0 (.seq hex_b1 (.seq hex_b2 (.seq hex_b3 (.seq hex_b4
          (.ite_false hcond_loop hex_nonloop)))))),
        by omega, hbcfg_lt, hG_loc, hZ_loc,
        by simp [s₁, s_d10, s_d9, s_d8, s_d7, s_d6, s_d5, s_d4, s_d3, s_d2, s_d1, s_c, hVA_card, hVA_root0],
        by simp [s₁, s_d10, s_d9, s_d8, s_d7, s_d6, s_d5, s_d4, s_d3, s_d2, s_d1, s_c, hVA_card, hVA_root1],
        by simp [s₁, s_d10, s_d9, s_d8, s_d7, s_d6, s_d5, s_d4, s_d3, s_d2, s_d1, s_c, s_c0, s_b, hEA_card, hEA_root ⟨0, by omega⟩, e],
        by simp [s₁],
        by simp [s₁, s_d10, s_d9, s_d8, s_d7, s_d6, s_d5, s_d4, s_d3, s_d2, s_d1, s_c, s_c0, hVA_card],
        by simp [s₁, s_d10, s_d9, s_d8, s_d7, s_d6, s_d5, s_d4, s_d3, s_d2, s_d1, s_c, s_c0, hVA_card],
        by simp [s₁, s_d10, s_d9, s_d8, s_d7, s_d6, s_d5, s_d4, s_d3, s_d2, s_d1, s_c, s_c0, s_b, hEA_card],
        by simp [s₁, s_d10, s_d9, hZA_card],
        by simp [s₁, s_d10, s_d9, s_d8, s_d7, s_d6, s_d5, s_d4, s_d3, s_d2, s_d1, s_c, s_c0, s_b, s_a, hzV_len],
        by simp [s₁, s_d10, s_d9, s_d8, s_d7, s_d6, s_d5, s_d4, s_d3, s_d2, s_d1, s_c, s_c0, s_b, s_a, hzI_len],
        fun i => by
          have h_arr : s₁.arrs a_acc_zV = ((s.arrs a_acc_zV).set 0 v_min.1).set b₀ v_max.1 := by
            simp [s₁, s_d10, s_d9, s_d8, s_d7, s_d6, s_d5, s_d4, s_d3, s_d2, s_d1, s_c, s_c0, s_b, s_a]
          rw [h_arr]; exact hzV_pair (s.arrs a_acc_zV) (by omega) i,
        fun i => by
          have h_arr : s₁.arrs a_acc_zI = ((s.arrs a_acc_zI).set 0 1).set b₀ 1 := by
            simp [s₁, s_d10, s_d9, s_d8, s_d7, s_d6, s_d5, s_d4, s_d3, s_d2, s_d1, s_c, s_c0, s_b, s_a]
          have hroot_mem : finsetRootFn ZA i = v_min ∨ finsetRootFn ZA i = v_max := by
            simpa using hZA_sub (finsetRootFn_mem ZA i)
          have hsub_i : subInc inp.G EA (finsetRootFn ZA i) = 1 := by
            rcases hroot_mem with h | h <;> [rw [h, hsub_vmin]; rw [h, hsub_vmax]]
          rw [h_arr, hsub_i]; exact hzI_pair (s.arrs a_acc_zI) (by omega) i,
        fun r hr hrq => by
          simp [s₁, s_d10, s_d9, s_d8, s_d7, s_d6, s_d5, s_d4, s_d3, s_d2, s_d1, s_c, s_c0, s_b, s_a, hrq,
            Nat.ne_of_lt (Nat.lt_of_lt_of_le hr (by decide : 10 ≤ 10)),
            Nat.ne_of_lt (Nat.lt_trans hr (by decide : 10 < 11)),
            Nat.ne_of_lt (Nat.lt_trans hr (by decide : 10 < 12)),
            Nat.ne_of_lt (Nat.lt_trans hr (by decide : 10 < 13)),
            Nat.ne_of_lt (Nat.lt_trans hr (by decide : 10 < 14)),
            Nat.ne_of_lt (Nat.lt_trans hr (by decide : 10 < 15)),
            Nat.ne_of_lt (Nat.lt_trans hr (by decide : 10 < 16)),
            Nat.ne_of_lt (Nat.lt_trans hr (by decide : 10 < 17)),
            Nat.ne_of_lt (Nat.lt_trans hr (by decide : 10 < 18)),
            Nat.ne_of_lt (Nat.lt_trans hr (by decide : 10 < 19))],
        fun a ha1 ha2 => by
          simp [s₁, s_d10, s_d9, s_d8, s_d7, s_d6, s_d5, s_d4, s_d3, s_d2, s_d1, s_c, s_c0, s_b, s_a, ha1, ha2]⟩

theorem treeBaseStepProg_exec {w δ ξ ω : ℕ} (inp : Alg41CoreInput ξ ω) (node : Fin inp.t)
    {r_x : Reg} (hrx_lt : r_x < 10) (_hrx_kv : r_x ≠ r_kv) (_hrx_ke : r_x ≠ r_ke)
    (_hrx_tidA : r_x ≠ r_tidA) (hrx_qA : r_x ≠ r_qA) {kv₀ ke₀ : ℕ} {s : State}
    (hw72 : 72 < 2 ^ w) (hn_w : inp.G.numVerts < 2 ^ w)
    (hm1_w : inp.G.numEdges + 1 < 2 ^ w) (ht_w : inp.t < 2 ^ w)
    (hS_w : S_tab δ ξ ω < 2 ^ w) (hT_w : T_max δ ξ ω < 2 ^ w)
    (hkv_w : kv₀ + 3 < 2 ^ w) (hke_w : ke₀ + 1 < 2 ^ w)
    (hwfV : ArenaWF inp.G.numVerts kv₀ (s.arrs a_vkd) (s.arrs a_vv1) (s.arrs a_vv2))
    (hwfE : ArenaWF inp.G.numEdges ke₀ (s.arrs a_ekd) (s.arrs a_ev1) (s.arrs a_ev2))
    (hkv_cap : kv₀ + 3 ≤ (s.arrs a_vkd).length) (hke_cap : ke₀ + 1 ≤ (s.arrs a_ekd).length)
    (hr_kv : s.regs r_kv = kv₀) (hr_ke : s.regs r_ke = ke₀) (hr_x : s.regs r_x = node.1)
    (hhead : s.arrs a_head = List.ofFn (fun e => (inp.G.head e).1))
    (htail : s.arrs a_tail = List.ofFn (fun e => (inp.G.tail e).1))
    (hedge : s.arrs a_edge = List.ofFn (leafEdgeAt inp.τ inp.G.numEdges))
    (hcap : s.arrs a_cap = List.ofFn (capVal inp.G inp.Z))
    (hzV_len : (s.arrs a_acc_zV).length = Q_max ξ ω) (hzI_len : (s.arrs a_acc_zI).length = Q_max ξ ω)
    (hvv_len : (s.arrs a_acc_vv).length = S_tab δ ξ ω)
    (hve_len : (s.arrs a_acc_ve).length = S_tab δ ξ ω)
    (hem_len : (s.arrs a_acc_em).length = S_tab δ ξ ω) :
    let EA := Finset.univ.filter (fun e : Fin inp.G.numEdges => (inp.τ e).1 = node.1)
    let ZA := pieceZ inp.G inp.Z EA
    ∃ s' t_step,
      Exec w (treeBaseStepProg δ ξ ω r_x) s s' t_step ∧ t_step ≤ 380 + 15 * S_tab δ ξ ω ∧
      s'.regs r_kv = kv₀ + 3 ∧ s'.regs r_ke = ke₀ + 1 ∧
      ArenaWF inp.G.numVerts (kv₀ + 3) (s'.arrs a_vkd) (s'.arrs a_vv1) (s'.arrs a_vv2) ∧
      ArenaWF inp.G.numEdges (ke₀ + 1) (s'.arrs a_ekd) (s'.arrs a_ev1) (s'.arrs a_ev2) ∧
      (s'.arrs a_vkd).length = (s.arrs a_vkd).length ∧ (s'.arrs a_ekd).length = (s.arrs a_ekd).length ∧
      (∀ p < kv₀,
        evalArena inp.G.numVerts (s'.arrs a_vkd) (s'.arrs a_vv1) (s'.arrs a_vv2) p =
          evalArena inp.G.numVerts (s.arrs a_vkd) (s.arrs a_vv1) (s.arrs a_vv2) p) ∧
      (∀ p < ke₀,
        evalArena inp.G.numEdges (s'.arrs a_ekd) (s'.arrs a_ev1) (s'.arrs a_ev2) p =
          evalArena inp.G.numEdges (s.arrs a_ekd) (s.arrs a_ev1) (s.arrs a_ev2) p) ∧
      ValidPieceBuffer δ ξ ω inp.G ZA EA
        (baseEdgePieceTable inp.G inp.Z δ EA).toRawList bufA s' ∧
      (∀ r < 10, r ≠ r_kv → r ≠ r_ke → r ≠ r_tidA → r ≠ r_qA → s'.regs r = s.regs r) ∧
      (∀ a, a ≠ a_vkd → a ≠ a_vv1 → a ≠ a_vv2 → a ≠ a_ekd → a ≠ a_ev1 → a ≠ a_ev2 →
        a ≠ a_acc_zV → a ≠ a_acc_zI → a ≠ a_acc_vv → a ≠ a_acc_ve → a ≠ a_acc_em →
        s'.arrs a = s.arrs a) := by
  intro EA ZA; let VA := pieceVB inp.G EA
  have hEA_sub : ∀ e ∈ EA, inp.G.head e ∈ VA ∧ inp.G.tail e ∈ VA :=
    fun _ he => ⟨head_mem_edgeEnds he, tail_mem_edgeEnds he⟩
  have hZA_sub : ZA ⊆ VA := pieceZ_subset_pieceVB inp.G inp.Z EA
  rcases treeBaseSetupProg_exec inp node hrx_lt hrx_qA hw72 hn_w hm1_w ht_w
      hr_x hhead htail hedge hcap hzV_len hzI_len with
    ⟨s₁, t_setup, bcfg, hex_setup, ht_setup, hbcfg_lt, hG_loc, hZ_loc,
     hr10, hr11, hr12, hr13, hr16, hr17, hr18, hr_q, hzV_len1, hzI_len1,
     hzV1, hzI1, hreg1, harr1⟩
  rcases baseTableFillProg_exec (w := w) (δ := δ) (ξ := ξ) (ω := ω) (G := inp.G)
      (VA := VA) (EA := EA) (ZA := ZA) hZA_sub hEA_sub
      (bcfg := bcfg) (kv₀ := kv₀) (ke₀ := ke₀) (buf := bufA) (s := s₁) hbcfg_lt hG_loc hZ_loc
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide)
      hw72 hn_w (by omega) hS_w hT_w hkv_w hke_w
      (by rw [harr1 a_vkd (by decide) (by decide), harr1 a_vv1 (by decide) (by decide),
              harr1 a_vv2 (by decide) (by decide)]; exact hwfV)
      (by rw [harr1 a_ekd (by decide) (by decide), harr1 a_ev1 (by decide) (by decide),
              harr1 a_ev2 (by decide) (by decide)]; exact hwfE)
      (by rw [harr1 a_vkd (by decide) (by decide)]; exact hkv_cap)
      (by rw [harr1 a_ekd (by decide) (by decide)]; exact hke_cap)
      (by rw [hreg1 r_kv (by decide) (by decide)]; exact hr_kv)
      (by rw [hreg1 r_ke (by decide) (by decide)]; exact hr_ke)
      hr10 hr11 hr12 hr13 hr16 hr17 hr18 hr_q hzV_len1 hzI_len1 hzV1 hzI1
      (by change (s₁.arrs a_acc_vv).length = _; rw [harr1 a_acc_vv (by decide) (by decide)]; exact hvv_len)
      (by change (s₁.arrs a_acc_ve).length = _; rw [harr1 a_acc_ve (by decide) (by decide)]; exact hve_len)
      (by change (s₁.arrs a_acc_em).length = _; rw [harr1 a_acc_em (by decide) (by decide)]; exact hem_len) with
    ⟨s', t_fill, hex_fill, ht_fill, hkv', hke', hwfV', hwfE', hlen_vkd', hlen_ekd',
     hevalV', hevalE', hvalid', hreg', harr'⟩
  refine ⟨s', t_setup + t_fill, .seq hex_setup hex_fill, by omega,
    hkv', hke', hwfV', hwfE',
    by rw [hlen_vkd', harr1 a_vkd (by decide) (by decide)],
    by rw [hlen_ekd', harr1 a_ekd (by decide) (by decide)],
    fun p hp => (hevalV' p hp).trans (evalArena_congr (harr1 a_vkd (by decide) (by decide))
      (harr1 a_vv1 (by decide) (by decide)) (harr1 a_vv2 (by decide) (by decide)) rfl),
    fun p hp => (hevalE' p hp).trans (evalArena_congr (harr1 a_ekd (by decide) (by decide))
      (harr1 a_ev1 (by decide) (by decide)) (harr1 a_ev2 (by decide) (by decide)) rfl),
    hvalid',
    fun r hr h1 h2 h3 h4 => (hreg' r hr h1 h2 h3).trans (hreg1 r hr h4),
    fun a ha1 ha2 ha3 ha4 ha5 ha6 ha7 ha8 ha9 ha10 ha11 =>
      (harr' a ha1 ha2 ha3 ha4 ha5 ha6 ha9 ha10 ha11).trans (harr1 a ha7 ha8)⟩

end GraphMinor.Compute
