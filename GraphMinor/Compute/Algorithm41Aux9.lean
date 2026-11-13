module

public import GraphMinor.Compute.Algorithm41Aux8

/-!
# Subtree Table Storage and Bottom-Up Tree DP Loop for GM XIII (4.1)

This file continues the Word RAM implementation of Algorithm (4.1) of Robertson and Seymour,
*Graph Minors. XIII. The Disjoint Paths Problem* (pages 75–76):

1. **Subtree Table Storage (`ValidSubtreeSlot`, `storeSubtreeProg`, `loadSubtreeProg`):**
   Stores and loads computed subtree tables between the working buffers (`bufA`, `bufB`) and the
   subtree storage arrays (`a_sub_tid`, `a_sub_q`, `a_sub_zV`, `a_sub_zI`, `a_sub_vv`, `a_sub_ve`,
   `a_sub_em`).
2. **Bottom-Up Tree DP Loop (`treeChildStepProg`, `treeNodeProg`, `treeDPLoopProg`):**
   Executes the bottom-up dynamic program over `x = t - 1` down to `0`, proving that upon
   completion `bufA` holds `ValidPieceBuffer` for `(dpSubtreeTable G Z δ p hp τ 0 ht).toRawList`.
-/

@[expose] public section

namespace GraphMinor.Compute

open SimpleGraph

/-! ### Section 1: Subtree Table Storage (`ValidSubtreeSlot`, `storeSubtreeProg`, `loadSubtreeProg`) -/

theorem Q_max_pos (ξ ω : ℕ) : 0 < Q_max ξ ω := by
  unfold Q_max; omega

theorem C_max_pos (δ ξ ω : ℕ) : 0 < C_max δ ξ ω := by
  unfold C_max; omega

theorem S_tab_pos (δ ξ ω : ℕ) : 0 < S_tab δ ξ ω :=
  Nat.mul_pos (C_max_pos δ ξ ω) (V_max_pos δ ξ ω)

/-- Transport `ValidPieceBuffer` across two `CertFolioTable`s that have the same `toSigmaRaw`
(in particular across `CertFolioTable.castSets`). -/
theorem ValidPieceBuffer.of_toSigmaRaw_eq {δ ξ ω : ℕ} {G : ComputeDigraph}
    {VA₁ VA₂ : Finset (Fin G.numVerts)} {E₁ E₂ : Finset (Fin G.numEdges)}
    {Z₁ Z₂ : Finset (Fin G.numVerts)}
    {T₁ : CertFolioTable G VA₁ E₁ (finsetRootFn Z₁) δ}
    {T₂ : CertFolioTable G VA₂ E₂ (finsetRootFn Z₂) δ}
    (hE : E₁ = E₂) (hZ : Z₁ = Z₂) (hSigma : T₁.toSigmaRaw = T₂.toSigmaRaw)
    {buf : PieceBufLayout} {s : State}
    (h : ValidPieceBuffer δ ξ ω G Z₁ E₁ T₁.toRawList buf s) :
    ValidPieceBuffer δ ξ ω G Z₂ E₂ T₂.toRawList buf s := by
  subst hE hZ
  have hraw : T₁.toRawList = T₂.toRawList := eq_of_heq (Sigma.mk.inj hSigma).2
  exact hraw ▸ h

/-- Validity invariant stating that subtree slot `x` in the subtree storage arrays (`a_sub_*`)
of state `s` (together with `ArenaV` and `ArenaE`) represents the boundary `(Z_P, E_P)` and the
certified raw entry list `es : List (RawCertEntry G Z_P.card)`. -/
structure ValidSubtreeSlot (δ ξ ω : ℕ) (G : ComputeDigraph)
    (Z_P : Finset (Fin G.numVerts)) (E_P : Finset (Fin G.numEdges))
    (es : List (RawCertEntry G Z_P.card)) (x : ℕ) (s : State) : Prop where
  hq_le : Z_P.card ≤ Q_max ξ ω
  hlen_le : es.length ≤ (allDetailLeCodes Z_P.card δ).length
  hdet : ∀ e ∈ es, e.H.HasDetailLe δ
  htid : (s.arrs a_sub_tid).getD x 0 = encAbstractTable δ ξ ω ⟨Z_P.card, es.map (·.H)⟩
  hq : (s.arrs a_sub_q).getD x 0 = Z_P.card
  hzV : ∀ i : Fin Z_P.card,
    (s.arrs a_sub_zV).getD (x * Q_max ξ ω + i.1) 0 = (finsetRootFn Z_P i).1
  hzI : ∀ i : Fin Z_P.card,
    (s.arrs a_sub_zI).getD (x * Q_max ξ ω + i.1) 0 = subInc G E_P (finsetRootFn Z_P i)
  hentries : ∀ idx : Fin es.length,
    let e := es[idx.1]
    let base := x * S_tab δ ξ ω + idx.1 * V_max δ ξ ω
    (∀ u : Fin e.H.digraph.numVerts,
      let p_vv := (s.arrs a_sub_vv).getD (base + u.1) 0
      let p_ve := (s.arrs a_sub_ve).getD (base + u.1) 0
      p_vv < s.regs r_kv ∧
      evalArena G.numVerts (s.arrs a_vkd) (s.arrs a_vv1) (s.arrs a_vv2) p_vv = e.vertVerts u ∧
      p_ve < s.regs r_ke ∧
      evalArena G.numEdges (s.arrs a_ekd) (s.arrs a_ev1) (s.arrs a_ev2) p_ve = e.vertEdges u) ∧
    (∀ d : Fin e.H.digraph.numEdges,
      (s.arrs a_sub_em).getD (base + d.1) 0 = (e.edgeMap d).1)

/-- Monotonicity of `ValidSubtreeSlot` when another subtree slot (disjoint from `x`) is written
and the arenas only grow. -/
theorem ValidSubtreeSlot.mono_slice {δ ξ ω : ℕ} {G : ComputeDigraph}
    {Z_P : Finset (Fin G.numVerts)} {E_P : Finset (Fin G.numEdges)}
    {es : List (RawCertEntry G Z_P.card)} {x : ℕ} {s s' : State}
    (h : ValidSubtreeSlot δ ξ ω G Z_P E_P es x s)
    (htid : (s'.arrs a_sub_tid).getD x 0 = (s.arrs a_sub_tid).getD x 0)
    (hq : (s'.arrs a_sub_q).getD x 0 = (s.arrs a_sub_q).getD x 0)
    (hzV : ∀ k < Q_max ξ ω,
      (s'.arrs a_sub_zV).getD (x * Q_max ξ ω + k) 0 =
        (s.arrs a_sub_zV).getD (x * Q_max ξ ω + k) 0)
    (hzI : ∀ k < Q_max ξ ω,
      (s'.arrs a_sub_zI).getD (x * Q_max ξ ω + k) 0 =
        (s.arrs a_sub_zI).getD (x * Q_max ξ ω + k) 0)
    (hvv : ∀ k < S_tab δ ξ ω,
      (s'.arrs a_sub_vv).getD (x * S_tab δ ξ ω + k) 0 =
        (s.arrs a_sub_vv).getD (x * S_tab δ ξ ω + k) 0)
    (hve : ∀ k < S_tab δ ξ ω,
      (s'.arrs a_sub_ve).getD (x * S_tab δ ξ ω + k) 0 =
        (s.arrs a_sub_ve).getD (x * S_tab δ ξ ω + k) 0)
    (hem : ∀ k < S_tab δ ξ ω,
      (s'.arrs a_sub_em).getD (x * S_tab δ ξ ω + k) 0 =
        (s.arrs a_sub_em).getD (x * S_tab δ ξ ω + k) 0)
    (hkv_le : s.regs r_kv ≤ s'.regs r_kv)
    (hke_le : s.regs r_ke ≤ s'.regs r_ke)
    (hevalV : ∀ p < s.regs r_kv,
      evalArena G.numVerts (s'.arrs a_vkd) (s'.arrs a_vv1) (s'.arrs a_vv2) p =
        evalArena G.numVerts (s.arrs a_vkd) (s.arrs a_vv1) (s.arrs a_vv2) p)
    (hevalE : ∀ p < s.regs r_ke,
      evalArena G.numEdges (s'.arrs a_ekd) (s'.arrs a_ev1) (s'.arrs a_ev2) p =
        evalArena G.numEdges (s.arrs a_ekd) (s.arrs a_ev1) (s.arrs a_ev2) p) :
    ValidSubtreeSlot δ ξ ω G Z_P E_P es x s' where
  hq_le := h.hq_le
  hlen_le := h.hlen_le
  hdet := h.hdet
  htid := htid.trans h.htid
  hq := hq.trans h.hq
  hzV i := (hzV i.1 (Nat.lt_of_lt_of_le i.2 h.hq_le)).trans (h.hzV i)
  hzI i := (hzI i.1 (Nat.lt_of_lt_of_le i.2 h.hq_le)).trans (h.hzI i)
  hentries idx := by
    rcases h.hentries idx with ⟨hverts, hedges⟩
    have hdet_idx : es[idx.1].H.HasDetailLe δ := h.hdet es[idx.1] (List.getElem_mem idx.2)
    have hidx_C : idx.1 < C_max δ ξ ω :=
      Nat.lt_of_lt_of_le (Nat.lt_of_lt_of_le idx.2 h.hlen_le)
        (Nat.le_of_lt (length_allDetailLeCodes_lt_C_max δ ξ ω h.hq_le))
    refine ⟨fun u => ?_, fun d => ?_⟩
    · have hu_V : u.1 < V_max δ ξ ω := Nat.lt_trans u.2 (numVerts_lt_V_max h.hq_le hdet_idx)
      have hk_S : idx.1 * V_max δ ξ ω + u.1 < S_tab δ ξ ω := by
        unfold S_tab
        have := Nat.mul_le_mul_right (V_max δ ξ ω) hidx_C
        rw [Nat.succ_mul] at this
        omega
      rcases hverts u with ⟨hp_vv, hev_vv, hp_ve, hev_ve⟩
      have h_assoc : x * S_tab δ ξ ω + idx.1 * V_max δ ξ ω + u.1 =
          x * S_tab δ ξ ω + (idx.1 * V_max δ ξ ω + u.1) := by omega
      dsimp only
      rw [h_assoc, hvv _ hk_S, hve _ hk_S, ← h_assoc]
      exact ⟨Nat.lt_of_lt_of_le hp_vv hkv_le, (hevalV _ hp_vv).trans hev_vv,
             Nat.lt_of_lt_of_le hp_ve hke_le, (hevalE _ hp_ve).trans hev_ve⟩
    · have hd_V : d.1 < V_max δ ξ ω := Nat.lt_trans d.2 (numEdges_lt_V_max hdet_idx)
      have hk_S : idx.1 * V_max δ ξ ω + d.1 < S_tab δ ξ ω := by
        unfold S_tab
        have := Nat.mul_le_mul_right (V_max δ ξ ω) hidx_C
        rw [Nat.succ_mul] at this
        omega
      have h_assoc : x * S_tab δ ξ ω + idx.1 * V_max δ ξ ω + d.1 =
          x * S_tab δ ξ ω + (idx.1 * V_max δ ξ ω + d.1) := by omega
      rw [h_assoc, hem _ hk_S, ← h_assoc]
      exact hedges d

/-- Monotonicity of `ValidSubtreeSlot` when the subtree arrays `a_sub_*` are unchanged and the
arenas only grow. -/
theorem ValidSubtreeSlot.mono_arena {δ ξ ω : ℕ} {G : ComputeDigraph}
    {Z_P : Finset (Fin G.numVerts)} {E_P : Finset (Fin G.numEdges)}
    {es : List (RawCertEntry G Z_P.card)} {x : ℕ} {s s' : State}
    (h : ValidSubtreeSlot δ ξ ω G Z_P E_P es x s)
    (htid : s'.arrs a_sub_tid = s.arrs a_sub_tid)
    (hq : s'.arrs a_sub_q = s.arrs a_sub_q)
    (hzV : s'.arrs a_sub_zV = s.arrs a_sub_zV)
    (hzI : s'.arrs a_sub_zI = s.arrs a_sub_zI)
    (hvv : s'.arrs a_sub_vv = s.arrs a_sub_vv)
    (hve : s'.arrs a_sub_ve = s.arrs a_sub_ve)
    (hem : s'.arrs a_sub_em = s.arrs a_sub_em)
    (hkv_le : s.regs r_kv ≤ s'.regs r_kv)
    (hke_le : s.regs r_ke ≤ s'.regs r_ke)
    (hevalV : ∀ p < s.regs r_kv,
      evalArena G.numVerts (s'.arrs a_vkd) (s'.arrs a_vv1) (s'.arrs a_vv2) p =
        evalArena G.numVerts (s.arrs a_vkd) (s.arrs a_vv1) (s.arrs a_vv2) p)
    (hevalE : ∀ p < s.regs r_ke,
      evalArena G.numEdges (s'.arrs a_ekd) (s'.arrs a_ev1) (s'.arrs a_ev2) p =
        evalArena G.numEdges (s.arrs a_ekd) (s.arrs a_ev1) (s.arrs a_ev2) p) :
    ValidSubtreeSlot δ ξ ω G Z_P E_P es x s' :=
  h.mono_slice
    (by rw [htid]) (by rw [hq])
    (fun _ _ => by rw [hzV]) (fun _ _ => by rw [hzI])
    (fun _ _ => by rw [hvv]) (fun _ _ => by rw [hve]) (fun _ _ => by rw [hem])
    hkv_le hke_le hevalV hevalE

/-- Unrolled loop copying `len` words from `a_src[0 .. len)` into `a_dst[r_x * len .. (r_x + 1) * len)`,
clamping each word with `readMin a_src (.const k) (.reg r_cap)`. -/
def copyToSliceMinProg (len : ℕ) (r_x : Reg) (a_src a_dst : Arr) (r_cap : Reg) : Cmd :=
  seqRange len (fun k =>
    .write a_dst (.op .add (.op .mul (.reg r_x) (.const len)) (.const k))
      (.readMin a_src (.const k) (.reg r_cap)))

theorem copyToSliceMinProg_exec {w len x cap : ℕ} {r_x r_cap : Reg} {a_src a_dst : Arr}
    {s₀ : State}
    (hne : a_dst ≠ a_src)
    (hlen_pos : 0 < len)
    (hxlen_w : (x + 1) * len < 2 ^ w) (hcap_w : cap < 2 ^ w)
    (hr_x : s₀.regs r_x = x) (hr_cap : s₀.regs r_cap = cap)
    (hsrc_len : len ≤ (s₀.arrs a_src).length)
    (hdst_len : (x + 1) * len ≤ (s₀.arrs a_dst).length) :
    ∃ s' t,
      Exec w (copyToSliceMinProg len r_x a_src a_dst r_cap) s₀ s' t ∧
      t ≤ 1 + 10 * len ∧
      s'.regs = s₀.regs ∧
      (s'.arrs a_dst).length = (s₀.arrs a_dst).length ∧
      (∀ k < len,
        (s'.arrs a_dst).getD (x * len + k) 0 =
          Nat.min ((s₀.arrs a_src).getD k 0) cap) ∧
      (∀ idx, (idx < x * len ∨ (x + 1) * len ≤ idx) →
        (s'.arrs a_dst).getD idx 0 = (s₀.arrs a_dst).getD idx 0) ∧
      (∀ a, a ≠ a_dst → s'.arrs a = s₀.arrs a) := by
  have h1_len : 1 ≤ len := hlen_pos
  have hx_le : x * 1 ≤ x * len := Nat.mul_le_mul_left x h1_len
  have hlen_w : len < 2 ^ w := by rw [Nat.add_mul, Nat.one_mul] at hxlen_w; omega
  have hx_w : x < 2 ^ w := by rw [Nat.add_mul, Nat.one_mul] at hxlen_w; omega
  have hxmul_w : x * len < 2 ^ w := by rw [Nat.add_mul, Nat.one_mul] at hxlen_w; omega
  let P (k : ℕ) (s : State) : Prop :=
    s.regs = s₀.regs ∧
    (s.arrs a_dst).length = (s₀.arrs a_dst).length ∧
    (∀ i < k,
      (s.arrs a_dst).getD (x * len + i) 0 =
        Nat.min ((s₀.arrs a_src).getD i 0) cap) ∧
    (∀ idx, (idx < x * len ∨ x * len + k ≤ idx) →
      (s.arrs a_dst).getD idx 0 = (s₀.arrs a_dst).getD idx 0) ∧
    (∀ a, a ≠ a_dst → s.arrs a = s₀.arrs a)
  have hP0 : P 0 s₀ :=
    ⟨rfl, rfl, fun _ hi => by omega, fun _ _ => rfl, fun _ _ => rfl⟩
  have hstep : ∀ k < len, ∀ s, P k s →
      ∃ s' t,
        Exec w (.write a_dst (.op .add (.op .mul (.reg r_x) (.const len)) (.const k))
          (.readMin a_src (.const k) (.reg r_cap))) s s' t ∧
        t ≤ 10 ∧ P (k + 1) s' := by
    intro k hk_lt s ⟨hregs, hlen_dst, hprev, hout, harr_ne⟩
    have hk_w : k < 2 ^ w := by omega
    have hxk_w : x * len + k < 2 ^ w := by rw [Nat.add_mul, Nat.one_mul] at hxlen_w; omega
    have hxk_dst : x * len + k < (s.arrs a_dst).length := by
      rw [hlen_dst]; rw [Nat.add_mul, Nat.one_mul] at hdst_len; omega
    have hsrc_s : s.arrs a_src = s₀.arrs a_src := harr_ne a_src hne.symm
    have hk_src : k < (s.arrs a_src).length := by rw [hsrc_s]; omega
    have hr_x_s : s.regs r_x = x := by rw [hregs, hr_x]
    have hr_cap_s : s.regs r_cap = cap := by rw [hregs, hr_cap]
    have hdst_eval :
        (Expr.op .add (.op .mul (.reg r_x) (.const len)) (.const k)).eval w s =
          some (x * len + k) := by
      simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hr_x_s, hx_w, hlen_w, hxmul_w, hk_w, hxk_w]
    have hidx_eval : (Expr.const k).eval w s = some k := by
      simp [Expr.eval, checkWord, hk_w]
    have hcap_eval : (Expr.reg r_cap).eval w s = some cap := by
      simp [Expr.eval, checkWord, hr_cap_s, hcap_w]
    have hread_eval := eval_readMin_of_getD hidx_eval hcap_eval hk_src
    rw [hsrc_s] at hread_eval
    let v_min := Nat.min ((s₀.arrs a_src).getD k 0) cap
    let s₁ := s.writeArr a_dst (x * len + k) v_min
    have hex : Exec w (.write a_dst (.op .add (.op .mul (.reg r_x) (.const len)) (.const k))
        (.readMin a_src (.const k) (.reg r_cap))) s s₁ 10 :=
      .write hdst_eval hread_eval hxk_dst
    refine ⟨s₁, 10, hex, le_refl 10, hregs, by simp [s₁, hlen_dst], ?_, ?_, ?_⟩
    · intro i hi
      by_cases hik : i = k
      · subst hik
        simp only [s₁, State.writeArr_arrs_self]
        rw [List.getD_eq_getElem?_getD, List.getElem?_set_self hxk_dst, Option.getD_some]
      · simp only [s₁, State.writeArr_arrs_self]
        have hne_idx : x * len + k ≠ x * len + i := by omega
        rw [List.getD_eq_getElem?_getD, List.getElem?_set_ne hne_idx, ← List.getD_eq_getElem?_getD]
        exact hprev i (by omega)
    · intro idx hidx
      simp only [s₁, State.writeArr_arrs_self]
      have hne_idx : x * len + k ≠ idx := by omega
      rw [List.getD_eq_getElem?_getD, List.getElem?_set_ne hne_idx, ← List.getD_eq_getElem?_getD]
      exact hout idx (by omega)
    · intro a ha
      simp [s₁, ha, harr_ne a ha]
  rcases Exec.seqRange P hP0 hstep with ⟨s', t, hex, ht, hregs, hlen_dst, hprev, hout, harr_ne⟩
  refine ⟨s', t, hex, ht, hregs, hlen_dst, hprev, fun idx hidx => hout idx ?_, harr_ne⟩
  rw [Nat.add_mul, Nat.one_mul] at hidx
  exact hidx

/-- Unrolled loop copying `len` words from `a_src[r_x * len .. (r_x + 1) * len)` into `a_dst[0 .. len)`,
clamping each word with `readMin a_src ... (.reg r_cap)`. -/
def copyFromSliceMinProg (len : ℕ) (r_x : Reg) (a_src a_dst : Arr) (r_cap : Reg) : Cmd :=
  seqRange len (fun k =>
    .write a_dst (.const k)
      (.readMin a_src (.op .add (.op .mul (.reg r_x) (.const len)) (.const k)) (.reg r_cap)))

theorem copyFromSliceMinProg_exec {w len x cap : ℕ} {r_x r_cap : Reg} {a_src a_dst : Arr}
    {s₀ : State}
    (hne : a_dst ≠ a_src)
    (hlen_pos : 0 < len)
    (hxlen_w : (x + 1) * len < 2 ^ w) (hcap_w : cap < 2 ^ w)
    (hr_x : s₀.regs r_x = x) (hr_cap : s₀.regs r_cap = cap)
    (hsrc_len : (x + 1) * len ≤ (s₀.arrs a_src).length)
    (hdst_len : len ≤ (s₀.arrs a_dst).length) :
    ∃ s' t,
      Exec w (copyFromSliceMinProg len r_x a_src a_dst r_cap) s₀ s' t ∧
      t ≤ 1 + 10 * len ∧
      s'.regs = s₀.regs ∧
      (s'.arrs a_dst).length = (s₀.arrs a_dst).length ∧
      (∀ k < len,
        (s'.arrs a_dst).getD k 0 =
          Nat.min ((s₀.arrs a_src).getD (x * len + k) 0) cap) ∧
      (∀ a, a ≠ a_dst → s'.arrs a = s₀.arrs a) := by
  have h1_len : 1 ≤ len := hlen_pos
  have hx_le : x * 1 ≤ x * len := Nat.mul_le_mul_left x h1_len
  have hlen_w : len < 2 ^ w := by rw [Nat.add_mul, Nat.one_mul] at hxlen_w; omega
  have hx_w : x < 2 ^ w := by rw [Nat.add_mul, Nat.one_mul] at hxlen_w; omega
  have hxmul_w : x * len < 2 ^ w := by rw [Nat.add_mul, Nat.one_mul] at hxlen_w; omega
  let P (k : ℕ) (s : State) : Prop :=
    s.regs = s₀.regs ∧
    (s.arrs a_dst).length = (s₀.arrs a_dst).length ∧
    (∀ i < k,
      (s.arrs a_dst).getD i 0 =
        Nat.min ((s₀.arrs a_src).getD (x * len + i) 0) cap) ∧
    (∀ a, a ≠ a_dst → s.arrs a = s₀.arrs a)
  have hP0 : P 0 s₀ := ⟨rfl, rfl, fun _ hi => by omega, fun _ _ => rfl⟩
  have hstep : ∀ k < len, ∀ s, P k s →
      ∃ s' t,
        Exec w (.write a_dst (.const k)
          (.readMin a_src (.op .add (.op .mul (.reg r_x) (.const len)) (.const k)) (.reg r_cap))) s s' t ∧
        t ≤ 10 ∧ P (k + 1) s' := by
    intro k hk_lt s ⟨hregs, hlen_dst, hprev, harr_ne⟩
    have hk_w : k < 2 ^ w := by omega
    have hxk_w : x * len + k < 2 ^ w := by rw [Nat.add_mul, Nat.one_mul] at hxlen_w; omega
    have hk_dst : k < (s.arrs a_dst).length := by rw [hlen_dst]; omega
    have hsrc_s : s.arrs a_src = s₀.arrs a_src := harr_ne a_src hne.symm
    have hxk_src : x * len + k < (s.arrs a_src).length := by
      rw [hsrc_s]; rw [Nat.add_mul, Nat.one_mul] at hsrc_len; omega
    have hr_x_s : s.regs r_x = x := by rw [hregs, hr_x]
    have hr_cap_s : s.regs r_cap = cap := by rw [hregs, hr_cap]
    have hdst_eval : (Expr.const k).eval w s = some k := by
      simp [Expr.eval, checkWord, hk_w]
    have hidx_eval :
        (Expr.op .add (.op .mul (.reg r_x) (.const len)) (.const k)).eval w s =
          some (x * len + k) := by
      simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hr_x_s, hx_w, hlen_w, hxmul_w, hk_w, hxk_w]
    have hcap_eval : (Expr.reg r_cap).eval w s = some cap := by
      simp [Expr.eval, checkWord, hr_cap_s, hcap_w]
    have hread_eval := eval_readMin_of_getD hidx_eval hcap_eval hxk_src
    rw [hsrc_s] at hread_eval
    let v_min := Nat.min ((s₀.arrs a_src).getD (x * len + k) 0) cap
    let s₁ := s.writeArr a_dst k v_min
    have hex : Exec w (.write a_dst (.const k)
        (.readMin a_src (.op .add (.op .mul (.reg r_x) (.const len)) (.const k)) (.reg r_cap)))
        s s₁ 10 :=
      .write hdst_eval hread_eval hk_dst
    refine ⟨s₁, 10, hex, le_refl 10, hregs, by simp [s₁, hlen_dst], ?_, ?_⟩
    · intro i hi
      by_cases hik : i = k
      · subst hik
        simp only [s₁, State.writeArr_arrs_self]
        rw [List.getD_eq_getElem?_getD, List.getElem?_set_self hk_dst, Option.getD_some]
      · simp only [s₁, State.writeArr_arrs_self]
        have hne_idx : k ≠ i := Ne.symm hik
        rw [List.getD_eq_getElem?_getD, List.getElem?_set_ne hne_idx, ← List.getD_eq_getElem?_getD]
        exact hprev i (by omega)
    · intro a ha
      simp [s₁, ha, harr_ne a ha]
  rcases Exec.seqRange P hP0 hstep with ⟨s', t, hex, ht, hregs, hlen_dst, hprev, harr_ne⟩
  exact ⟨s', t, hex, ht, hregs, hlen_dst, hprev, harr_ne⟩

/-- Store the current accumulator buffer `bufA` into subtree slot `r_x` of `a_sub_*`. -/
def storeSubtreeProg (δ ξ ω : ℕ) (r_x : Reg) : Cmd :=
  .seq (.write a_sub_tid (.reg r_x) (.reg r_tidA))
  (.seq (.write a_sub_q (.reg r_x) (.reg r_qA))
  (.seq (copyToSliceMinProg (Q_max ξ ω) r_x a_acc_zV a_sub_zV 0)
  (.seq (copyToSliceMinProg (Q_max ξ ω) r_x a_acc_zI a_sub_zI 1)
  (.seq (copyToSliceMinProg (S_tab δ ξ ω) r_x a_acc_vv a_sub_vv r_kv)
  (.seq (copyToSliceMinProg (S_tab δ ξ ω) r_x a_acc_ve a_sub_ve r_ke)
        (copyToSliceMinProg (S_tab δ ξ ω) r_x a_acc_em a_sub_em 1))))))

/-- Cost upper bound for `storeSubtreeProg` and `loadSubtreeProg`. -/
def C_subtreeCopy (δ ξ ω : ℕ) : ℕ :=
  15 + 20 * Q_max ξ ω + 30 * S_tab δ ξ ω

theorem storeSubtreeProg_exec {w δ ξ ω t x kv₀ ke₀ : ℕ}
    {G : ComputeDigraph} {Z_P : Finset (Fin G.numVerts)} {E_P : Finset (Fin G.numEdges)}
    {es : List (RawCertEntry G Z_P.card)} {r_x : Reg} {s₀ : State}
    (hbuf : ValidPieceBuffer δ ξ ω G Z_P E_P es bufA s₀)
    (hx_lt : x < t)
    (hn_w : G.numVerts < 2 ^ w) (hm_w : G.numEdges < 2 ^ w)
    (hQ_w : t * Q_max ξ ω < 2 ^ w) (hS_w : t * S_tab δ ξ ω < 2 ^ w)
    (hT_w : T_max δ ξ ω < 2 ^ w) (hkv_w : kv₀ < 2 ^ w) (hke_w : ke₀ < 2 ^ w)
    (hr0 : s₀.regs 0 = G.numVerts) (hr1 : s₀.regs 1 = G.numEdges)
    (hr_kv : s₀.regs r_kv = kv₀) (hr_ke : s₀.regs r_ke = ke₀)
    (hr_x : s₀.regs r_x = x)
    (hlen_tid : (s₀.arrs a_sub_tid).length = t)
    (hlen_q : (s₀.arrs a_sub_q).length = t)
    (hlen_zV : (s₀.arrs a_sub_zV).length = t * Q_max ξ ω)
    (hlen_zI : (s₀.arrs a_sub_zI).length = t * Q_max ξ ω)
    (hlen_vv : (s₀.arrs a_sub_vv).length = t * S_tab δ ξ ω)
    (hlen_ve : (s₀.arrs a_sub_ve).length = t * S_tab δ ξ ω)
    (hlen_em : (s₀.arrs a_sub_em).length = t * S_tab δ ξ ω) :
    ∃ s' time,
      Exec w (storeSubtreeProg δ ξ ω r_x) s₀ s' time ∧
      time ≤ C_subtreeCopy δ ξ ω ∧
      s'.regs = s₀.regs ∧
      ValidPieceBuffer δ ξ ω G Z_P E_P es bufA s' ∧
      ValidSubtreeSlot δ ξ ω G Z_P E_P es x s' ∧
      (∀ y < t, y ≠ x → ∀ (Z_Y : Finset (Fin G.numVerts)) (E_Y : Finset (Fin G.numEdges))
        (es_Y : List (RawCertEntry G Z_Y.card)),
        ValidSubtreeSlot δ ξ ω G Z_Y E_Y es_Y y s₀ →
        ValidSubtreeSlot δ ξ ω G Z_Y E_Y es_Y y s') ∧
      (s'.arrs a_sub_tid).length = t ∧
      (s'.arrs a_sub_q).length = t ∧
      (s'.arrs a_sub_zV).length = t * Q_max ξ ω ∧
      (s'.arrs a_sub_zI).length = t * Q_max ξ ω ∧
      (s'.arrs a_sub_vv).length = t * S_tab δ ξ ω ∧
      (s'.arrs a_sub_ve).length = t * S_tab δ ξ ω ∧
      (s'.arrs a_sub_em).length = t * S_tab δ ξ ω ∧
      (∀ a, a ≠ a_sub_tid → a ≠ a_sub_q → a ≠ a_sub_zV → a ≠ a_sub_zI →
        a ≠ a_sub_vv → a ≠ a_sub_ve → a ≠ a_sub_em → s'.arrs a = s₀.arrs a) := by
  have h1Q : 1 ≤ Q_max ξ ω := Q_max_pos ξ ω
  have hx_le_tQ : x < t * Q_max ξ ω :=
    lt_of_lt_of_le hx_lt (by simpa using Nat.mul_le_mul_left t h1Q)
  have hx_w : x < 2 ^ w := by omega
  have hx1_Q : (x + 1) * Q_max ξ ω ≤ t * Q_max ξ ω := Nat.mul_le_mul_right _ hx_lt
  have hx1_S : (x + 1) * S_tab δ ξ ω ≤ t * S_tab δ ξ ω := Nat.mul_le_mul_right _ hx_lt
  have hlen_map : (es.map RawCertEntry.H).length ≤ (allDetailLeCodes Z_P.card δ).length := by
    rw [List.length_map]; exact hbuf.hlen_le
  have htid_lt : s₀.regs r_tidA < T_max δ ξ ω := by
    rw [show s₀.regs r_tidA = encAbstractTable δ ξ ω ⟨Z_P.card, es.map RawCertEntry.H⟩ from hbuf.htid]
    exact encAbstractTable_lt δ ξ ω ⟨Z_P.card, es.map RawCertEntry.H⟩ hbuf.hq_le hlen_map
  have htid_w : s₀.regs r_tidA < 2 ^ w := by omega
  have hq_le : s₀.regs r_qA ≤ Q_max ξ ω := by
    rw [show s₀.regs r_qA = Z_P.card from hbuf.hq]; exact hbuf.hq_le
  have hq_w : s₀.regs r_qA < 2 ^ w := by
    have : s₀.regs r_qA ≤ 1 * Q_max ξ ω := by simpa using hq_le
    have : 1 * Q_max ξ ω ≤ t * Q_max ξ ω := Nat.mul_le_mul_right _ (by omega : 1 ≤ t)
    omega
  let s₁ := s₀.writeArr a_sub_tid x (s₀.regs r_tidA)
  have hex₁ : Exec w (.write a_sub_tid (.reg r_x) (.reg r_tidA)) s₀ s₁ 3 :=
    .write (by simp [Expr.eval, checkWord, hr_x, hx_w])
      (by simp [Expr.eval, checkWord, htid_w])
      (by rw [hlen_tid]; exact hx_lt)
  let s₂ := s₁.writeArr a_sub_q x (s₀.regs r_qA)
  have hex₂ : Exec w (.write a_sub_q (.reg r_x) (.reg r_qA)) s₁ s₂ 3 :=
    .write (by simp [s₁, Expr.eval, checkWord, hr_x, hx_w])
      (by simp [s₁, Expr.eval, checkWord, hq_w])
      (by simp [s₁, hlen_q, hx_lt])
  rcases copyToSliceMinProg_exec (w := w) (len := Q_max ξ ω) (x := x) (cap := G.numVerts)
      (r_x := r_x) (r_cap := 0) (a_src := a_acc_zV) (a_dst := a_sub_zV) (s₀ := s₂)
      (by decide) (Q_max_pos ξ ω) (by omega) hn_w
      (by simp [s₂, s₁, hr_x]) (by simp [s₂, s₁, hr0])
      (by simp [s₂, s₁]; exact le_of_eq hbuf.hzV_len.symm)
      (by simp [s₂, s₁, hlen_zV]; exact hx1_Q) with
    ⟨s₃, t₃, hex₃, ht₃, hregs₃, hlen_zV₃, hget_zV₃, hout_zV₃, harr₃⟩
  rcases copyToSliceMinProg_exec (w := w) (len := Q_max ξ ω) (x := x) (cap := G.numEdges)
      (r_x := r_x) (r_cap := 1) (a_src := a_acc_zI) (a_dst := a_sub_zI) (s₀ := s₃)
      (by decide) (Q_max_pos ξ ω) (by omega) hm_w
      (by rw [hregs₃]; simp [s₂, s₁, hr_x]) (by rw [hregs₃]; simp [s₂, s₁, hr1])
      (by rw [harr₃ a_acc_zI (by decide)]; simp [s₂, s₁]; exact le_of_eq hbuf.hzI_len.symm)
      (by rw [harr₃ a_sub_zI (by decide)]; simp [s₂, s₁, hlen_zI]; exact hx1_Q) with
    ⟨s₄, t₄, hex₄, ht₄, hregs₄, hlen_zI₄, hget_zI₄, hout_zI₄, harr₄⟩
  rcases copyToSliceMinProg_exec (w := w) (len := S_tab δ ξ ω) (x := x) (cap := kv₀)
      (r_x := r_x) (r_cap := r_kv) (a_src := a_acc_vv) (a_dst := a_sub_vv) (s₀ := s₄)
      (by decide) (S_tab_pos δ ξ ω) (by omega) hkv_w
      (by rw [hregs₄, hregs₃]; simp [s₂, s₁, hr_x]) (by rw [hregs₄, hregs₃]; simp [s₂, s₁, hr_kv])
      (by rw [harr₄ a_acc_vv (by decide), harr₃ a_acc_vv (by decide)]; simp [s₂, s₁]; exact le_of_eq hbuf.hvv_len.symm)
      (by rw [harr₄ a_sub_vv (by decide), harr₃ a_sub_vv (by decide)]; simp [s₂, s₁, hlen_vv]; exact hx1_S) with
    ⟨s₅, t₅, hex₅, ht₅, hregs₅, hlen_vv₅, hget_vv₅, hout_vv₅, harr₅⟩
  rcases copyToSliceMinProg_exec (w := w) (len := S_tab δ ξ ω) (x := x) (cap := ke₀)
      (r_x := r_x) (r_cap := r_ke) (a_src := a_acc_ve) (a_dst := a_sub_ve) (s₀ := s₅)
      (by decide) (S_tab_pos δ ξ ω) (by omega) hke_w
      (by rw [hregs₅, hregs₄, hregs₃]; simp [s₂, s₁, hr_x]) (by rw [hregs₅, hregs₄, hregs₃]; simp [s₂, s₁, hr_ke])
      (by rw [harr₅ a_acc_ve (by decide), harr₄ a_acc_ve (by decide), harr₃ a_acc_ve (by decide)]; simp [s₂, s₁]; exact le_of_eq hbuf.hve_len.symm)
      (by rw [harr₅ a_sub_ve (by decide), harr₄ a_sub_ve (by decide), harr₃ a_sub_ve (by decide)]; simp [s₂, s₁, hlen_ve]; exact hx1_S) with
    ⟨s₆, t₆, hex₆, ht₆, hregs₆, hlen_ve₆, hget_ve₆, hout_ve₆, harr₆⟩
  rcases copyToSliceMinProg_exec (w := w) (len := S_tab δ ξ ω) (x := x) (cap := G.numEdges)
      (r_x := r_x) (r_cap := 1) (a_src := a_acc_em) (a_dst := a_sub_em) (s₀ := s₆)
      (by decide) (S_tab_pos δ ξ ω) (by omega) hm_w
      (by rw [hregs₆, hregs₅, hregs₄, hregs₃]; simp [s₂, s₁, hr_x])
      (by rw [hregs₆, hregs₅, hregs₄, hregs₃]; simp [s₂, s₁, hr1])
      (by rw [harr₆ a_acc_em (by decide), harr₅ a_acc_em (by decide), harr₄ a_acc_em (by decide), harr₃ a_acc_em (by decide)]; simp [s₂, s₁]; exact le_of_eq hbuf.hem_len.symm)
      (by rw [harr₆ a_sub_em (by decide), harr₅ a_sub_em (by decide), harr₄ a_sub_em (by decide), harr₃ a_sub_em (by decide)]; simp [s₂, s₁, hlen_em]; exact hx1_S) with
    ⟨s', t₇, hex₇, ht₇, hregs₇, hlen_em₇, hget_em₇, hout_em₇, harr₇⟩
  have hregs' : s'.regs = s₀.regs := by
    rw [hregs₇, hregs₆, hregs₅, hregs₄, hregs₃]; rfl
  have harr_other : ∀ a, a ≠ a_sub_tid → a ≠ a_sub_q → a ≠ a_sub_zV → a ≠ a_sub_zI →
      a ≠ a_sub_vv → a ≠ a_sub_ve → a ≠ a_sub_em → s'.arrs a = s₀.arrs a := by
    intro a h1 h2 h3 h4 h5 h6 h7
    rw [harr₇ a h7, harr₆ a h6, harr₅ a h5, harr₄ a h4, harr₃ a h3]
    simp [s₂, s₁, h1, h2]
  have hsub_tid' : s'.arrs a_sub_tid = (s₀.arrs a_sub_tid).set x (s₀.regs r_tidA) := by
    rw [harr₇ a_sub_tid (by decide), harr₆ a_sub_tid (by decide), harr₅ a_sub_tid (by decide),
        harr₄ a_sub_tid (by decide), harr₃ a_sub_tid (by decide)]
    simp [s₂, s₁]
  have hsub_q' : s'.arrs a_sub_q = (s₀.arrs a_sub_q).set x (s₀.regs r_qA) := by
    rw [harr₇ a_sub_q (by decide), harr₆ a_sub_q (by decide), harr₅ a_sub_q (by decide),
        harr₄ a_sub_q (by decide), harr₃ a_sub_q (by decide)]
    simp [s₂, s₁]
  have hsub_zV' : s'.arrs a_sub_zV = s₃.arrs a_sub_zV := by
    rw [harr₇ a_sub_zV (by decide), harr₆ a_sub_zV (by decide), harr₅ a_sub_zV (by decide),
        harr₄ a_sub_zV (by decide)]
  have hsub_zI' : s'.arrs a_sub_zI = s₄.arrs a_sub_zI := by
    rw [harr₇ a_sub_zI (by decide), harr₆ a_sub_zI (by decide), harr₅ a_sub_zI (by decide)]
  have hsub_vv' : s'.arrs a_sub_vv = s₅.arrs a_sub_vv := by
    rw [harr₇ a_sub_vv (by decide), harr₆ a_sub_vv (by decide)]
  have hsub_ve' : s'.arrs a_sub_ve = s₆.arrs a_sub_ve := by
    rw [harr₇ a_sub_ve (by decide)]
  have hbuf' : ValidPieceBuffer δ ξ ω G Z_P E_P es bufA s' :=
    hbuf.mono_arena
      (by rw [hregs']) (by rw [hregs'])
      (harr_other a_acc_zV (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))
      (harr_other a_acc_zI (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))
      (harr_other a_acc_vv (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))
      (harr_other a_acc_ve (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))
      (harr_other a_acc_em (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))
      (by rw [hregs']) (by rw [hregs'])
      (fun p _ => by
        rw [harr_other a_vkd (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
            harr_other a_vv1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
            harr_other a_vv2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)])
      (fun p _ => by
        rw [harr_other a_ekd (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
            harr_other a_ev1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
            harr_other a_ev2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)])
  have hslot_x : ValidSubtreeSlot δ ξ ω G Z_P E_P es x s' := by
    refine ⟨hbuf.hq_le, hbuf.hlen_le, hbuf.hdet, ?_, ?_, ?_, ?_, ?_⟩
    · rw [hsub_tid', List.getD_eq_getElem?_getD, List.getElem?_set_self (by rw [hlen_tid]; exact hx_lt), Option.getD_some]
      exact hbuf.htid
    · rw [hsub_q', List.getD_eq_getElem?_getD, List.getElem?_set_self (by rw [hlen_q]; exact hx_lt), Option.getD_some]
      exact hbuf.hq
    · intro i
      have hi_Q : i.1 < Q_max ξ ω := Nat.lt_of_lt_of_le i.2 hbuf.hq_le
      rw [hsub_zV', hget_zV₃ i.1 hi_Q]
      have hsrc : s₂.arrs a_acc_zV = s₀.arrs bufA.a_zV := rfl
      rw [hsrc, hbuf.hzV i]
      exact Nat.min_eq_left (le_of_lt (finsetRootFn Z_P i).2)
    · intro i
      have hi_Q : i.1 < Q_max ξ ω := Nat.lt_of_lt_of_le i.2 hbuf.hq_le
      rw [hsub_zI', hget_zI₄ i.1 hi_Q, harr₃ a_acc_zI (by decide)]
      have hsrc : s₂.arrs a_acc_zI = s₀.arrs bufA.a_zI := rfl
      rw [hsrc, hbuf.hzI i]
      exact Nat.min_eq_left (subInc_le_numEdges G E_P (finsetRootFn Z_P i))
    · intro idx
      rcases hbuf.hentries idx with ⟨hverts, hedges⟩
      have hdet_idx : es[idx.1].H.HasDetailLe δ := hbuf.hdet es[idx.1] (List.getElem_mem idx.2)
      have hidx_C : idx.1 < C_max δ ξ ω :=
        Nat.lt_of_lt_of_le (Nat.lt_of_lt_of_le idx.2 hbuf.hlen_le)
          (Nat.le_of_lt (length_allDetailLeCodes_lt_C_max δ ξ ω hbuf.hq_le))
      refine ⟨fun u => ?_, fun d => ?_⟩
      · have hu_V : u.1 < V_max δ ξ ω := Nat.lt_trans u.2 (numVerts_lt_V_max hbuf.hq_le hdet_idx)
        have hk_S : idx.1 * V_max δ ξ ω + u.1 < S_tab δ ξ ω := by
          unfold S_tab; have := Nat.mul_le_mul_right (V_max δ ξ ω) hidx_C
          rw [Nat.succ_mul] at this; omega
        rcases hverts u with ⟨hp_vv, hev_vv, hp_ve, hev_ve⟩
        have h_assoc : x * S_tab δ ξ ω + idx.1 * V_max δ ξ ω + u.1 =
            x * S_tab δ ξ ω + (idx.1 * V_max δ ξ ω + u.1) := by omega
        have hp_vv_eq : (s'.arrs a_sub_vv).getD (x * S_tab δ ξ ω + idx.1 * V_max δ ξ ω + u.1) 0 =
            (s₀.arrs a_acc_vv).getD (idx.1 * V_max δ ξ ω + u.1) 0 := by
          rw [h_assoc, hsub_vv', hget_vv₅ _ hk_S, harr₄ a_acc_vv (by decide), harr₃ a_acc_vv (by decide)]
          change Nat.min ((s₀.arrs a_acc_vv).getD _ 0) kv₀ = _
          exact Nat.min_eq_left (le_of_lt (hr_kv ▸ hp_vv))
        have hp_ve_eq : (s'.arrs a_sub_ve).getD (x * S_tab δ ξ ω + idx.1 * V_max δ ξ ω + u.1) 0 =
            (s₀.arrs a_acc_ve).getD (idx.1 * V_max δ ξ ω + u.1) 0 := by
          rw [h_assoc, hsub_ve', hget_ve₆ _ hk_S, harr₅ a_acc_ve (by decide),
              harr₄ a_acc_ve (by decide), harr₃ a_acc_ve (by decide)]
          change Nat.min ((s₀.arrs a_acc_ve).getD _ 0) ke₀ = _
          exact Nat.min_eq_left (le_of_lt (hr_ke ▸ hp_ve))
        dsimp only
        rw [hp_vv_eq, hp_ve_eq, hregs',
            harr_other a_vkd (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
            harr_other a_vv1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
            harr_other a_vv2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
            harr_other a_ekd (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
            harr_other a_ev1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
            harr_other a_ev2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]
        exact ⟨hp_vv, hev_vv, hp_ve, hev_ve⟩
      · have hd_V : d.1 < V_max δ ξ ω := Nat.lt_trans d.2 (numEdges_lt_V_max hdet_idx)
        have hk_S : idx.1 * V_max δ ξ ω + d.1 < S_tab δ ξ ω := by
          unfold S_tab; have := Nat.mul_le_mul_right (V_max δ ξ ω) hidx_C
          rw [Nat.succ_mul] at this; omega
        have h_assoc : x * S_tab δ ξ ω + idx.1 * V_max δ ξ ω + d.1 =
            x * S_tab δ ξ ω + (idx.1 * V_max δ ξ ω + d.1) := by omega
        rw [h_assoc, hget_em₇ _ hk_S,
            harr₆ a_acc_em (by decide), harr₅ a_acc_em (by decide),
            harr₄ a_acc_em (by decide), harr₃ a_acc_em (by decide)]
        change Nat.min ((s₀.arrs bufA.a_em).getD _ 0) G.numEdges = _
        rw [hedges d]
        exact Nat.min_eq_left (le_of_lt (es[idx.1].edgeMap d).2)
  have hslot_other : ∀ y < t, y ≠ x → ∀ (Z_Y : Finset (Fin G.numVerts)) (E_Y : Finset (Fin G.numEdges))
      (es_Y : List (RawCertEntry G Z_Y.card)),
      ValidSubtreeSlot δ ξ ω G Z_Y E_Y es_Y y s₀ →
      ValidSubtreeSlot δ ξ ω G Z_Y E_Y es_Y y s' := by
    intro y hy_lt hyx Z_Y E_Y es_Y hslot
    have hdisj_len : ∀ L : ℕ, ∀ k < L, y * L + k < x * L ∨ (x + 1) * L ≤ y * L + k := by
      intro L k hk
      rcases Nat.lt_or_gt_of_ne hyx with hy_lt_x | hx_lt_y
      · left
        have := Nat.mul_le_mul_right L hy_lt_x
        rw [Nat.succ_mul] at this; omega
      · right
        exact le_trans (Nat.mul_le_mul_right L hx_lt_y) (Nat.le_add_right _ k)
    refine hslot.mono_slice
      (by rw [hsub_tid', List.getD_eq_getElem?_getD, List.getElem?_set_ne hyx.symm, ← List.getD_eq_getElem?_getD])
      (by rw [hsub_q', List.getD_eq_getElem?_getD, List.getElem?_set_ne hyx.symm, ← List.getD_eq_getElem?_getD])
      (fun k hk => by rw [hsub_zV', hout_zV₃ _ (hdisj_len _ k hk)]; rfl)
      (fun k hk => by rw [hsub_zI', hout_zI₄ _ (hdisj_len _ k hk), harr₃ a_sub_zI (by decide)]; rfl)
      (fun k hk => by
        rw [hsub_vv', hout_vv₅ _ (hdisj_len _ k hk), harr₄ a_sub_vv (by decide), harr₃ a_sub_vv (by decide)]; rfl)
      (fun k hk => by
        rw [hsub_ve', hout_ve₆ _ (hdisj_len _ k hk), harr₅ a_sub_ve (by decide),
            harr₄ a_sub_ve (by decide), harr₃ a_sub_ve (by decide)]; rfl)
      (fun k hk => by
        rw [hout_em₇ _ (hdisj_len _ k hk), harr₆ a_sub_em (by decide), harr₅ a_sub_em (by decide),
            harr₄ a_sub_em (by decide), harr₃ a_sub_em (by decide)]; rfl)
      (by rw [hregs']) (by rw [hregs'])
      (fun p _ => by
        rw [harr_other a_vkd (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
            harr_other a_vv1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
            harr_other a_vv2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)])
      (fun p _ => by
        rw [harr_other a_ekd (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
            harr_other a_ev1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
            harr_other a_ev2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)])
  refine ⟨s', 3 + (3 + (t₃ + (t₄ + (t₅ + (t₆ + t₇))))),
    .seq hex₁ (.seq hex₂ (.seq hex₃ (.seq hex₄ (.seq hex₅ (.seq hex₆ hex₇))))),
    by unfold C_subtreeCopy; omega,
    hregs', hbuf', hslot_x, hslot_other,
    by rw [hsub_tid', List.length_set, hlen_tid],
    by rw [hsub_q', List.length_set, hlen_q],
    by rw [hsub_zV', hlen_zV₃]; exact hlen_zV,
    by rw [hsub_zI', hlen_zI₄, harr₃ a_sub_zI (by decide)]; exact hlen_zI,
    by rw [hsub_vv', hlen_vv₅, harr₄ a_sub_vv (by decide), harr₃ a_sub_vv (by decide)]; exact hlen_vv,
    by rw [hsub_ve', hlen_ve₆, harr₅ a_sub_ve (by decide), harr₄ a_sub_ve (by decide), harr₃ a_sub_ve (by decide)]; exact hlen_ve,
    by rw [hlen_em₇, harr₆ a_sub_em (by decide), harr₅ a_sub_em (by decide), harr₄ a_sub_em (by decide), harr₃ a_sub_em (by decide)]; exact hlen_em,
    harr_other⟩

/-- Load subtree slot `r_x` from `a_sub_*` into working buffer `bufB` (`a_rhs_*`). -/
def loadSubtreeProg (δ ξ ω : ℕ) (r_x : Reg) : Cmd :=
  .seq (.assign r_tidB (.readMin a_sub_tid (.reg r_x) (.const (T_max δ ξ ω))))
  (.seq (.assign r_qB (.readMin a_sub_q (.reg r_x) (.const (Q_max ξ ω))))
  (.seq (copyFromSliceMinProg (Q_max ξ ω) r_x a_sub_zV a_rhs_zV 0)
  (.seq (copyFromSliceMinProg (Q_max ξ ω) r_x a_sub_zI a_rhs_zI 1)
  (.seq (copyFromSliceMinProg (S_tab δ ξ ω) r_x a_sub_vv a_rhs_vv r_kv)
  (.seq (copyFromSliceMinProg (S_tab δ ξ ω) r_x a_sub_ve a_rhs_ve r_ke)
        (copyFromSliceMinProg (S_tab δ ξ ω) r_x a_sub_em a_rhs_em 1))))))

theorem loadSubtreeProg_exec {w δ ξ ω t x kv₀ ke₀ : ℕ}
    {G : ComputeDigraph} {Z_P : Finset (Fin G.numVerts)} {E_P : Finset (Fin G.numEdges)}
    {es : List (RawCertEntry G Z_P.card)} {r_x : Reg} {s₀ : State}
    (hslot : ValidSubtreeSlot δ ξ ω G Z_P E_P es x s₀)
    (hrx_tidB : r_x ≠ r_tidB) (hrx_qB : r_x ≠ r_qB)
    (hx_lt : x < t)
    (hn_w : G.numVerts < 2 ^ w) (hm_w : G.numEdges < 2 ^ w)
    (hQ_w : t * Q_max ξ ω < 2 ^ w) (hS_w : t * S_tab δ ξ ω < 2 ^ w)
    (hT_w : T_max δ ξ ω < 2 ^ w) (hkv_w : kv₀ < 2 ^ w) (hke_w : ke₀ < 2 ^ w)
    (hr0 : s₀.regs 0 = G.numVerts) (hr1 : s₀.regs 1 = G.numEdges)
    (hr_kv : s₀.regs r_kv = kv₀) (hr_ke : s₀.regs r_ke = ke₀)
    (hr_x : s₀.regs r_x = x)
    (hlen_tid : (s₀.arrs a_sub_tid).length = t)
    (hlen_q : (s₀.arrs a_sub_q).length = t)
    (hlen_zV : (s₀.arrs a_sub_zV).length = t * Q_max ξ ω)
    (hlen_zI : (s₀.arrs a_sub_zI).length = t * Q_max ξ ω)
    (hlen_vv : (s₀.arrs a_sub_vv).length = t * S_tab δ ξ ω)
    (hlen_ve : (s₀.arrs a_sub_ve).length = t * S_tab δ ξ ω)
    (hlen_em : (s₀.arrs a_sub_em).length = t * S_tab δ ξ ω)
    (hrhs_zV : (s₀.arrs a_rhs_zV).length = Q_max ξ ω)
    (hrhs_zI : (s₀.arrs a_rhs_zI).length = Q_max ξ ω)
    (hrhs_vv : (s₀.arrs a_rhs_vv).length = S_tab δ ξ ω)
    (hrhs_ve : (s₀.arrs a_rhs_ve).length = S_tab δ ξ ω)
    (hrhs_em : (s₀.arrs a_rhs_em).length = S_tab δ ξ ω) :
    ∃ s' time,
      Exec w (loadSubtreeProg δ ξ ω r_x) s₀ s' time ∧
      time ≤ C_subtreeCopy δ ξ ω ∧
      ValidPieceBuffer δ ξ ω G Z_P E_P es bufB s' ∧
      (∀ r, r ≠ r_tidB → r ≠ r_qB → s'.regs r = s₀.regs r) ∧
      (∀ a, a ≠ a_rhs_zV → a ≠ a_rhs_zI → a ≠ a_rhs_vv → a ≠ a_rhs_ve → a ≠ a_rhs_em →
        s'.arrs a = s₀.arrs a) := by
  have h1Q : 1 ≤ Q_max ξ ω := Q_max_pos ξ ω
  have hx_le_tQ : x < t * Q_max ξ ω :=
    lt_of_lt_of_le hx_lt (by simpa using Nat.mul_le_mul_left t h1Q)
  have hx_w : x < 2 ^ w := by omega
  have hQ0_w : Q_max ξ ω < 2 ^ w := by
    have : 1 * Q_max ξ ω ≤ t * Q_max ξ ω := Nat.mul_le_mul_right _ (by omega : 1 ≤ t)
    omega
  have hx1_Q : (x + 1) * Q_max ξ ω ≤ t * Q_max ξ ω := Nat.mul_le_mul_right _ hx_lt
  have hx1_S : (x + 1) * S_tab δ ξ ω ≤ t * S_tab δ ξ ω := Nat.mul_le_mul_right _ hx_lt
  have hlen_map : (es.map RawCertEntry.H).length ≤ (allDetailLeCodes Z_P.card δ).length := by
    rw [List.length_map]; exact hslot.hlen_le
  have htid_lt : (s₀.arrs a_sub_tid).getD x 0 < T_max δ ξ ω := by
    rw [hslot.htid]
    exact encAbstractTable_lt δ ξ ω ⟨Z_P.card, es.map RawCertEntry.H⟩ hslot.hq_le hlen_map
  have htid_eval :
      (Expr.readMin a_sub_tid (.reg r_x) (.const (T_max δ ξ ω))).eval w s₀ =
        some ((s₀.arrs a_sub_tid).getD x 0) :=
    eval_readMin_eq_of_le
      (by simp [Expr.eval, checkWord, hr_x, hx_w])
      (by simp [Expr.eval, checkWord, hT_w])
      (by rw [hlen_tid]; exact hx_lt)
      rfl (le_of_lt htid_lt)
  let s₁ := s₀.setReg r_tidB ((s₀.arrs a_sub_tid).getD x 0)
  have hex₁ : Exec w (.assign r_tidB (.readMin a_sub_tid (.reg r_x) (.const (T_max δ ξ ω)))) s₀ s₁ 5 :=
    .assign htid_eval
  have hq_eval :
      (Expr.readMin a_sub_q (.reg r_x) (.const (Q_max ξ ω))).eval w s₁ = some Z_P.card :=
    eval_readMin_eq_of_le
      (by simp [s₁, Expr.eval, checkWord, State.setReg_regs_ne _ _ hrx_tidB, hr_x, hx_w])
      (by simp [Expr.eval, checkWord, hQ0_w])
      (by simp [s₁, hlen_q, hx_lt])
      hslot.hq hslot.hq_le
  let s₂ := s₁.setReg r_qB Z_P.card
  have hex₂ : Exec w (.assign r_qB (.readMin a_sub_q (.reg r_x) (.const (Q_max ξ ω)))) s₁ s₂ 5 :=
    .assign hq_eval
  rcases copyFromSliceMinProg_exec (w := w) (len := Q_max ξ ω) (x := x) (cap := G.numVerts)
      (r_x := r_x) (r_cap := 0) (a_src := a_sub_zV) (a_dst := a_rhs_zV) (s₀ := s₂)
      (by decide) (Q_max_pos ξ ω) (by omega) hn_w
      (by simp [s₂, s₁, State.setReg_regs_ne _ _ hrx_qB, State.setReg_regs_ne _ _ hrx_tidB, hr_x])
      (by simp [s₂, s₁, hr0])
      (by simp [s₂, s₁, hlen_zV]; exact hx1_Q)
      (by simp [s₂, s₁]; exact le_of_eq hrhs_zV.symm) with
    ⟨s₃, t₃, hex₃, ht₃, hregs₃, hlen_zV₃, hget_zV₃, harr₃⟩
  rcases copyFromSliceMinProg_exec (w := w) (len := Q_max ξ ω) (x := x) (cap := G.numEdges)
      (r_x := r_x) (r_cap := 1) (a_src := a_sub_zI) (a_dst := a_rhs_zI) (s₀ := s₃)
      (by decide) (Q_max_pos ξ ω) (by omega) hm_w
      (by rw [hregs₃]; simp [s₂, s₁, State.setReg_regs_ne _ _ hrx_qB, State.setReg_regs_ne _ _ hrx_tidB, hr_x])
      (by rw [hregs₃]; simp [s₂, s₁, hr1])
      (by rw [harr₃ a_sub_zI (by decide)]; simp [s₂, s₁, hlen_zI]; exact hx1_Q)
      (by rw [harr₃ a_rhs_zI (by decide)]; simp [s₂, s₁]; exact le_of_eq hrhs_zI.symm) with
    ⟨s₄, t₄, hex₄, ht₄, hregs₄, hlen_zI₄, hget_zI₄, harr₄⟩
  rcases copyFromSliceMinProg_exec (w := w) (len := S_tab δ ξ ω) (x := x) (cap := kv₀)
      (r_x := r_x) (r_cap := r_kv) (a_src := a_sub_vv) (a_dst := a_rhs_vv) (s₀ := s₄)
      (by decide) (S_tab_pos δ ξ ω) (by omega) hkv_w
      (by rw [hregs₄, hregs₃]; simp [s₂, s₁, State.setReg_regs_ne _ _ hrx_qB, State.setReg_regs_ne _ _ hrx_tidB, hr_x])
      (by rw [hregs₄, hregs₃]; simp [s₂, s₁, hr_kv])
      (by rw [harr₄ a_sub_vv (by decide), harr₃ a_sub_vv (by decide)]; simp [s₂, s₁, hlen_vv]; exact hx1_S)
      (by rw [harr₄ a_rhs_vv (by decide), harr₃ a_rhs_vv (by decide)]; simp [s₂, s₁]; exact le_of_eq hrhs_vv.symm) with
    ⟨s₅, t₅, hex₅, ht₅, hregs₅, hlen_vv₅, hget_vv₅, harr₅⟩
  rcases copyFromSliceMinProg_exec (w := w) (len := S_tab δ ξ ω) (x := x) (cap := ke₀)
      (r_x := r_x) (r_cap := r_ke) (a_src := a_sub_ve) (a_dst := a_rhs_ve) (s₀ := s₅)
      (by decide) (S_tab_pos δ ξ ω) (by omega) hke_w
      (by rw [hregs₅, hregs₄, hregs₃]; simp [s₂, s₁, State.setReg_regs_ne _ _ hrx_qB, State.setReg_regs_ne _ _ hrx_tidB, hr_x])
      (by rw [hregs₅, hregs₄, hregs₃]; simp [s₂, s₁, hr_ke])
      (by rw [harr₅ a_sub_ve (by decide), harr₄ a_sub_ve (by decide), harr₃ a_sub_ve (by decide)]; simp [s₂, s₁, hlen_ve]; exact hx1_S)
      (by rw [harr₅ a_rhs_ve (by decide), harr₄ a_rhs_ve (by decide), harr₃ a_rhs_ve (by decide)]; simp [s₂, s₁]; exact le_of_eq hrhs_ve.symm) with
    ⟨s₆, t₆, hex₆, ht₆, hregs₆, hlen_ve₆, hget_ve₆, harr₆⟩
  rcases copyFromSliceMinProg_exec (w := w) (len := S_tab δ ξ ω) (x := x) (cap := G.numEdges)
      (r_x := r_x) (r_cap := 1) (a_src := a_sub_em) (a_dst := a_rhs_em) (s₀ := s₆)
      (by decide) (S_tab_pos δ ξ ω) (by omega) hm_w
      (by rw [hregs₆, hregs₅, hregs₄, hregs₃]; simp [s₂, s₁, State.setReg_regs_ne _ _ hrx_qB, State.setReg_regs_ne _ _ hrx_tidB, hr_x])
      (by rw [hregs₆, hregs₅, hregs₄, hregs₃]; simp [s₂, s₁, hr1])
      (by rw [harr₆ a_sub_em (by decide), harr₅ a_sub_em (by decide), harr₄ a_sub_em (by decide), harr₃ a_sub_em (by decide)]; simp [s₂, s₁, hlen_em]; exact hx1_S)
      (by rw [harr₆ a_rhs_em (by decide), harr₅ a_rhs_em (by decide), harr₄ a_rhs_em (by decide), harr₃ a_rhs_em (by decide)]; simp [s₂, s₁]; exact le_of_eq hrhs_em.symm) with
    ⟨s', t₇, hex₇, ht₇, hregs₇, hlen_em₇, hget_em₇, harr₇⟩
  have hregs' : s'.regs = s₂.regs := by
    rw [hregs₇, hregs₆, hregs₅, hregs₄, hregs₃]
  have harr_other : ∀ a, a ≠ a_rhs_zV → a ≠ a_rhs_zI → a ≠ a_rhs_vv → a ≠ a_rhs_ve → a ≠ a_rhs_em →
      s'.arrs a = s₀.arrs a := by
    intro a h1 h2 h3 h4 h5
    rw [harr₇ a h5, harr₆ a h4, harr₅ a h3, harr₄ a h2, harr₃ a h1]
    rfl
  have hrhs_zV' : s'.arrs a_rhs_zV = s₃.arrs a_rhs_zV := by
    rw [harr₇ a_rhs_zV (by decide), harr₆ a_rhs_zV (by decide), harr₅ a_rhs_zV (by decide), harr₄ a_rhs_zV (by decide)]
  have hrhs_zI' : s'.arrs a_rhs_zI = s₄.arrs a_rhs_zI := by
    rw [harr₇ a_rhs_zI (by decide), harr₆ a_rhs_zI (by decide), harr₅ a_rhs_zI (by decide)]
  have hrhs_vv' : s'.arrs a_rhs_vv = s₅.arrs a_rhs_vv := by
    rw [harr₇ a_rhs_vv (by decide), harr₆ a_rhs_vv (by decide)]
  have hrhs_ve' : s'.arrs a_rhs_ve = s₆.arrs a_rhs_ve := by
    rw [harr₇ a_rhs_ve (by decide)]
  have hbufB : ValidPieceBuffer δ ξ ω G Z_P E_P es bufB s' := by
    refine ⟨hslot.hq_le, hslot.hlen_le, hslot.hdet, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · change s'.regs r_tidB = _; rw [hregs']; simp [s₂, s₁]; exact hslot.htid
    · change s'.regs r_qB = Z_P.card; rw [hregs']; simp [s₂, s₁]
    · change (s'.arrs a_rhs_zV).length = Q_max ξ ω; rw [hrhs_zV', hlen_zV₃]; exact hrhs_zV
    · change (s'.arrs a_rhs_zI).length = Q_max ξ ω; rw [hrhs_zI', hlen_zI₄, harr₃ a_rhs_zI (by decide)]; exact hrhs_zI
    · intro i
      have hi_Q : i.1 < Q_max ξ ω := Nat.lt_of_lt_of_le i.2 hslot.hq_le
      change (s'.arrs a_rhs_zV).getD i.1 0 = (finsetRootFn Z_P i).1
      rw [hrhs_zV', hget_zV₃ i.1 hi_Q]
      change Nat.min ((s₀.arrs a_sub_zV).getD (x * Q_max ξ ω + i.1) 0) G.numVerts = _
      rw [hslot.hzV i]
      exact Nat.min_eq_left (le_of_lt (finsetRootFn Z_P i).2)
    · intro i
      have hi_Q : i.1 < Q_max ξ ω := Nat.lt_of_lt_of_le i.2 hslot.hq_le
      change (s'.arrs a_rhs_zI).getD i.1 0 = subInc G E_P (finsetRootFn Z_P i)
      rw [hrhs_zI', hget_zI₄ i.1 hi_Q, harr₃ a_sub_zI (by decide)]
      change Nat.min ((s₀.arrs a_sub_zI).getD (x * Q_max ξ ω + i.1) 0) G.numEdges = _
      rw [hslot.hzI i]
      exact Nat.min_eq_left (subInc_le_numEdges G E_P (finsetRootFn Z_P i))
    · change (s'.arrs a_rhs_vv).length = S_tab δ ξ ω
      rw [hrhs_vv', hlen_vv₅, harr₄ a_rhs_vv (by decide), harr₃ a_rhs_vv (by decide)]; exact hrhs_vv
    · change (s'.arrs a_rhs_ve).length = S_tab δ ξ ω
      rw [hrhs_ve', hlen_ve₆, harr₅ a_rhs_ve (by decide), harr₄ a_rhs_ve (by decide), harr₃ a_rhs_ve (by decide)]; exact hrhs_ve
    · change (s'.arrs a_rhs_em).length = S_tab δ ξ ω
      rw [hlen_em₇, harr₆ a_rhs_em (by decide), harr₅ a_rhs_em (by decide), harr₄ a_rhs_em (by decide), harr₃ a_rhs_em (by decide)]; exact hrhs_em
    · intro idx
      rcases hslot.hentries idx with ⟨hverts, hedges⟩
      have hdet_idx : es[idx.1].H.HasDetailLe δ := hslot.hdet es[idx.1] (List.getElem_mem idx.2)
      have hidx_C : idx.1 < C_max δ ξ ω :=
        Nat.lt_of_lt_of_le (Nat.lt_of_lt_of_le idx.2 hslot.hlen_le)
          (Nat.le_of_lt (length_allDetailLeCodes_lt_C_max δ ξ ω hslot.hq_le))
      refine ⟨fun u => ?_, fun d => ?_⟩
      · have hu_V : u.1 < V_max δ ξ ω := Nat.lt_trans u.2 (numVerts_lt_V_max hslot.hq_le hdet_idx)
        have hk_S : idx.1 * V_max δ ξ ω + u.1 < S_tab δ ξ ω := by
          unfold S_tab; have := Nat.mul_le_mul_right (V_max δ ξ ω) hidx_C
          rw [Nat.succ_mul] at this; omega
        rcases hverts u with ⟨hp_vv, hev_vv, hp_ve, hev_ve⟩
        have h_assoc : x * S_tab δ ξ ω + (idx.1 * V_max δ ξ ω + u.1) =
            x * S_tab δ ξ ω + idx.1 * V_max δ ξ ω + u.1 := by omega
        have hp_vv_eq : (s'.arrs a_rhs_vv).getD (idx.1 * V_max δ ξ ω + u.1) 0 =
            (s₀.arrs a_sub_vv).getD (x * S_tab δ ξ ω + idx.1 * V_max δ ξ ω + u.1) 0 := by
          rw [hrhs_vv', hget_vv₅ _ hk_S, harr₄ a_sub_vv (by decide), harr₃ a_sub_vv (by decide)]
          change Nat.min ((s₀.arrs a_sub_vv).getD _ 0) kv₀ = _
          rw [h_assoc]
          exact Nat.min_eq_left (le_of_lt (hr_kv ▸ hp_vv))
        have hp_ve_eq : (s'.arrs a_rhs_ve).getD (idx.1 * V_max δ ξ ω + u.1) 0 =
            (s₀.arrs a_sub_ve).getD (x * S_tab δ ξ ω + idx.1 * V_max δ ξ ω + u.1) 0 := by
          rw [hrhs_ve', hget_ve₆ _ hk_S, harr₅ a_sub_ve (by decide),
              harr₄ a_sub_ve (by decide), harr₃ a_sub_ve (by decide)]
          change Nat.min ((s₀.arrs a_sub_ve).getD _ 0) ke₀ = _
          rw [h_assoc]
          exact Nat.min_eq_left (le_of_lt (hr_ke ▸ hp_ve))
        dsimp only [bufB]
        rw [hp_vv_eq, hp_ve_eq, hregs',
            harr_other a_vkd (by decide) (by decide) (by decide) (by decide) (by decide),
            harr_other a_vv1 (by decide) (by decide) (by decide) (by decide) (by decide),
            harr_other a_vv2 (by decide) (by decide) (by decide) (by decide) (by decide),
            harr_other a_ekd (by decide) (by decide) (by decide) (by decide) (by decide),
            harr_other a_ev1 (by decide) (by decide) (by decide) (by decide) (by decide),
            harr_other a_ev2 (by decide) (by decide) (by decide) (by decide) (by decide)]
        exact ⟨hp_vv, hev_vv, hp_ve, hev_ve⟩
      · have hd_V : d.1 < V_max δ ξ ω := Nat.lt_trans d.2 (numEdges_lt_V_max hdet_idx)
        have hk_S : idx.1 * V_max δ ξ ω + d.1 < S_tab δ ξ ω := by
          unfold S_tab; have := Nat.mul_le_mul_right (V_max δ ξ ω) hidx_C
          rw [Nat.succ_mul] at this; omega
        have h_assoc : x * S_tab δ ξ ω + (idx.1 * V_max δ ξ ω + d.1) =
            x * S_tab δ ξ ω + idx.1 * V_max δ ξ ω + d.1 := by omega
        dsimp only [bufB]
        rw [hget_em₇ _ hk_S, harr₆ a_sub_em (by decide), harr₅ a_sub_em (by decide),
            harr₄ a_sub_em (by decide), harr₃ a_sub_em (by decide)]
        change Nat.min ((s₀.arrs a_sub_em).getD _ 0) G.numEdges = _
        rw [h_assoc, hedges d]
        exact Nat.min_eq_left (le_of_lt (es[idx.1].edgeMap d).2)
  refine ⟨s', 5 + (5 + (t₃ + (t₄ + (t₅ + (t₆ + t₇))))),
    .seq hex₁ (.seq hex₂ (.seq hex₃ (.seq hex₄ (.seq hex₅ (.seq hex₆ hex₇))))),
    by unfold C_subtreeCopy; omega,
    hbufB,
    fun r h1 h2 => by rw [hregs']; simp [s₂, s₁, h1, h2],
    harr_other⟩

/-! ### Section 2: Bottom-Up Tree DP (`treeChildStepProg`, `treeNodeProg`, `treeDPLoopProg`) -/

theorem mem_pieceZ_union_iff (G : ComputeDigraph) (Z : Finset (Fin G.numVerts))
    (EA EB : Finset (Fin G.numEdges)) (u : Fin G.numVerts) :
    u ∈ pieceZ G Z (EA ∪ EB) ↔
      u ∈ pieceZ G Z EA ∪ pieceZ G Z EB ∧ subInc G (EA ∪ EB) u < capVal G Z u := by
  constructor
  · intro hu
    exact ⟨pieceZ_union_subset Z EA EB hu,
      ((mem_pieceZ_iff_subInc_lt_capVal G Z (EA ∪ EB) u).mp hu).2⟩
  · rintro ⟨hu_ab, hcap⟩
    rw [mem_pieceZ_iff_subInc_lt_capVal]
    refine ⟨?_, hcap⟩
    rw [← mem_pieceVB_iff_subInc_pos, pieceVB, edgeEnds_union]
    rcases Finset.mem_union.mp hu_ab with hA | hB
    · exact Finset.mem_union_left _ (pieceZ_subset_pieceVB G Z EA hA)
    · exact Finset.mem_union_right _ (pieceZ_subset_pieceVB G Z EB hB)

theorem toSigmaRaw_combineEdgePieceTables {G : ComputeDigraph} {Z : Finset (Fin G.numVerts)}
    {δ : ℕ} {E₁ E₂ : Finset (Fin G.numEdges)} (hdisj : Disjoint E₁ E₂)
    (T₁ : PieceFolioTable G Z δ E₁) (T₂ : PieceFolioTable G Z δ E₂) :
    (combineEdgePieceTables hdisj T₁ T₂).toSigmaRaw =
      (combinePieceTables
        (pieceZ_subset_pieceVB G Z E₁)
        (pieceZ_subset_pieceVB G Z E₂)
        (pieceZ_union_subset Z E₁ E₂)
        hdisj
        (fun _ he => ⟨head_mem_edgeEnds he, tail_mem_edgeEnds he⟩)
        (fun _ he => ⟨head_mem_edgeEnds he, tail_mem_edgeEnds he⟩)
        (pieceVB_inter_subset_pieceZ Z hdisj)
        T₁ T₂).toSigmaRaw := by
  unfold combineEdgePieceTables
  exact CertFolioTable.toSigmaRaw_castSets _ _ _ _

theorem dpAccEB_eq_of_forall_ne {t : ℕ} (G : ComputeDigraph) (p : ℕ → ℕ)
    (τ : Fin G.numEdges → Fin t) (x k₁ k₂ : ℕ) (hle : k₁ ≤ k₂)
    (hne : ∀ k', k₁ ≤ k' → k' < k₂ → p k' ≠ x) :
    dpAccEB G p τ x k₂ = dpAccEB G p τ x k₁ := by
  induction k₂ with
  | zero =>
    have hk : k₁ = 0 := by omega
    subst hk; rfl
  | succ k₂ ih =>
    by_cases heq : k₁ = k₂ + 1
    · subst heq; rfl
    · have hle' : k₁ ≤ k₂ := by omega
      rw [dpAccEB_step_ne G p τ (hne k₂ hle' (Nat.lt_succ_self k₂)),
          ih hle' (fun k' hk1 hk2 => hne k' hk1 (by omega))]

theorem dpChildrenLoop_toSigmaRaw_of_forall_ne (G : ComputeDigraph) (Z : Finset (Fin G.numVerts))
    (δ : ℕ) {t : ℕ} (p : ℕ → ℕ) (hp : ∀ z, 0 < z → z < t → p z < z)
    (τ : Fin G.numEdges → Fin t) (x : ℕ)
    (childFn : ∀ k, x < k → k < t → PieceFolioTable G Z δ (dpEB G p τ k))
    (k : ℕ) (hk_ge : x + 1 ≤ k) (hk_le : k ≤ t)
    (acc : PieceFolioTable G Z δ (dpAccEB G p τ x k))
    (hne : ∀ k', k ≤ k' → k' < t → p k' ≠ x) :
    (dpChildrenLoop G Z δ p hp τ x childFn k hk_ge hk_le acc).toSigmaRaw = acc.toSigmaRaw := by
  generalize hrem : t - k = rem
  induction rem generalizing k with
  | zero =>
    have hkeq : k = t := by omega
    subst hkeq
    simp [dpChildrenLoop]
  | succ rem ih =>
    have hkt : k < t := by omega
    have hpk : p k ≠ x := hne k (le_refl k) hkt
    rw [dpChildrenLoop]
    simp only [hkt, ↓reduceDIte, hpk]
    rw [ih (k + 1) (by omega) (by omega) _ (fun k' hk1 hk2 => hne k' (by omega) hk2) (by omega)]
    exact CertFolioTable.toSigmaRaw_castSets _ _ _ acc

@[simp]
theorem CertFolioTable.castSets_castSets {G : ComputeDigraph}
    {VA₁ VA₂ VA₃ : Finset (Fin G.numVerts)} {EA₁ EA₂ EA₃ : Finset (Fin G.numEdges)}
    {Z₁ Z₂ Z₃ : Finset (Fin G.numVerts)} {δ : ℕ}
    (hV₁ : VA₁ = VA₂) (hE₁ : EA₁ = EA₂) (hZ₁ : Z₁ = Z₂)
    (hV₂ : VA₂ = VA₃) (hE₂ : EA₂ = EA₃) (hZ₂ : Z₂ = Z₃)
    (T : CertFolioTable G VA₁ EA₁ (finsetRootFn Z₁) δ) :
    (T.castSets hV₁ hE₁ hZ₁).castSets hV₂ hE₂ hZ₂ =
      T.castSets (hV₁.trans hV₂) (hE₁.trans hE₂) (hZ₁.trans hZ₂) := by
  subst hV₁ hE₁ hZ₁ hV₂ hE₂ hZ₂
  rfl

theorem dpChildrenLoop_toSigmaRaw_skip_to (G : ComputeDigraph) (Z : Finset (Fin G.numVerts))
    (δ : ℕ) {t : ℕ} (p : ℕ → ℕ) (hp : ∀ z, 0 < z → z < t → p z < z)
    (τ : Fin G.numEdges → Fin t) (x : ℕ)
    (childFn : ∀ k, x < k → k < t → PieceFolioTable G Z δ (dpEB G p τ k))
    {k₁ k₂ : ℕ} (hk₁_ge : x + 1 ≤ k₁) (hk₁_le : k₁ ≤ k₂) (hk₂_le : k₂ ≤ t)
    (hne : ∀ k', k₁ ≤ k' → k' < k₂ → p k' ≠ x)
    (acc : PieceFolioTable G Z δ (dpAccEB G p τ x k₁)) :
    let hE := dpAccEB_eq_of_forall_ne G p τ x k₁ k₂ hk₁_le hne
    let acc₂ : PieceFolioTable G Z δ (dpAccEB G p τ x k₂) :=
      acc.castSets (by rw [hE]) hE.symm (by rw [hE])
    (dpChildrenLoop G Z δ p hp τ x childFn k₂ (by omega) hk₂_le acc₂).toSigmaRaw =
      (dpChildrenLoop G Z δ p hp τ x childFn k₁ hk₁_ge (by omega) acc).toSigmaRaw := by
  dsimp only
  generalize hrem : k₂ - k₁ = rem
  induction rem generalizing k₁ with
  | zero =>
    have hkeq : k₁ = k₂ := by omega
    subst hkeq
    unfold CertFolioTable.castSets
    rfl
  | succ rem ih =>
    have hk₁_lt_k₂ : k₁ < k₂ := by omega
    have hk₁_lt_t : k₁ < t := by omega
    have hpk₁ : p k₁ ≠ x := hne k₁ (le_refl k₁) hk₁_lt_k₂
    conv_rhs =>
      rw [dpChildrenLoop]
      simp only [hk₁_lt_t, ↓reduceDIte, hpk₁]
    let nextAcc : PieceFolioTable G Z δ (dpAccEB G p τ x (k₁ + 1)) :=
      acc.castSets (by rw [dpAccEB_step_ne G p τ hpk₁])
        (dpAccEB_step_ne G p τ hpk₁).symm
        (by rw [dpAccEB_step_ne G p τ hpk₁])
    have hne' : ∀ k', k₁ + 1 ≤ k' → k' < k₂ → p k' ≠ x :=
      fun k' hk1 hk2 => hne k' (by omega) hk2
    have h_ih := ih (by omega) (by omega) hne' nextAcc (by omega)
    rw [← h_ih]
    apply congrArg CertFolioTable.toSigmaRaw
    apply congrArg (dpChildrenLoop G Z δ p hp τ x childFn k₂ (by omega) hk₂_le)
    exact (CertFolioTable.castSets_castSets _ _ _ _ _ _ acc).symm

theorem dpChildrenLoop_step_eq (G : ComputeDigraph) (Z : Finset (Fin G.numVerts))
    (δ : ℕ) {t : ℕ} (p : ℕ → ℕ) (hp : ∀ z, 0 < z → z < t → p z < z)
    (τ : Fin G.numEdges → Fin t) (x : ℕ)
    (childFn : ∀ k, x < k → k < t → PieceFolioTable G Z δ (dpEB G p τ k))
    (c : ℕ) (hc_ge : x + 1 ≤ c) (hc_lt : c < t) (hpc : p c = x)
    (acc : PieceFolioTable G Z δ (dpAccEB G p τ x c)) :
    have hxc : x < c := by omega
    have hdisj := disjoint_dpAccEB_dpEB G hp τ hxc hpc
    let nextAcc : PieceFolioTable G Z δ (dpAccEB G p τ x (c + 1)) :=
      (combineEdgePieceTables hdisj acc (childFn c hxc hc_lt)).castSets
        (by rw [dpAccEB_step_eq G p τ hc_lt hxc hpc])
        (dpAccEB_step_eq G p τ hc_lt hxc hpc).symm
        (by rw [dpAccEB_step_eq G p τ hc_lt hxc hpc])
    dpChildrenLoop G Z δ p hp τ x childFn c hc_ge (by omega) acc =
      dpChildrenLoop G Z δ p hp τ x childFn (c + 1) (by omega) (by omega) nextAcc := by
  rw [dpChildrenLoop]
  simp only [hc_lt, ↓reduceDIte, hpc]

/-- Word-size bounds required during the tree DP and isolated-vertex completion passes. -/
structure Alg41WordBounds (w δ ξ ω : ℕ) (inp : Alg41CoreInput ξ ω) : Prop where
  hw72 : 72 < 2 ^ w
  hn_w : inp.G.numVerts < 2 ^ w
  hm1_w : inp.G.numEdges + 1 < 2 ^ w
  ht3_w : 3 * inp.t < 2 ^ w
  htQ_w : inp.t * Q_max ξ ω < 2 ^ w
  htS_w : inp.t * S_tab δ ξ ω < 2 ^ w
  hT_w : T_max δ ξ ω < 2 ^ w
  hM_w : M_max ξ ω < 2 ^ w

theorem Alg41WordBounds.hw8 {w δ ξ ω : ℕ} {inp : Alg41CoreInput ξ ω}
    (h : Alg41WordBounds w δ ξ ω inp) : 8 < 2 ^ w := by
  have := h.hw72; omega

theorem Alg41WordBounds.hm_w {w δ ξ ω : ℕ} {inp : Alg41CoreInput ξ ω}
    (h : Alg41WordBounds w δ ξ ω inp) : inp.G.numEdges < 2 ^ w := by
  have := h.hm1_w; omega

theorem Alg41WordBounds.ht_w {w δ ξ ω : ℕ} {inp : Alg41CoreInput ξ ω}
    (h : Alg41WordBounds w δ ξ ω inp) : inp.t < 2 ^ w := by
  have := h.ht3_w; have := inp.ht; omega

theorem Alg41WordBounds.hQ_w {w δ ξ ω : ℕ} {inp : Alg41CoreInput ξ ω}
    (h : Alg41WordBounds w δ ξ ω inp) : Q_max ξ ω < 2 ^ w := by
  have h1 : 1 * Q_max ξ ω ≤ inp.t * Q_max ξ ω := Nat.mul_le_mul_right _ inp.ht
  have := h.htQ_w; omega

theorem Alg41WordBounds.hS_w {w δ ξ ω : ℕ} {inp : Alg41CoreInput ξ ω}
    (h : Alg41WordBounds w δ ξ ω inp) : S_tab δ ξ ω < 2 ^ w := by
  have h1 : 1 * S_tab δ ξ ω ≤ inp.t * S_tab δ ξ ω := Nat.mul_le_mul_right _ inp.ht
  have := h.htS_w; omega

/-- State invariant for the read-only preprocessing arrays and working/subtree array lengths. -/
structure TreeDPStateInv (δ ξ ω : ℕ) (inp : Alg41CoreInput ξ ω) (s : State) : Prop where
  hr0 : s.regs 0 = inp.G.numVerts
  hr1 : s.regs 1 = inp.G.numEdges
  hr2 : s.regs 2 = inp.t
  hhead : s.arrs a_head = List.ofFn (fun e => (inp.G.head e).1)
  htail : s.arrs a_tail = List.ofFn (fun e => (inp.G.tail e).1)
  hZ : s.arrs a_Z = bitSetList inp.Z
  htot : s.arrs a_tot = List.ofFn (totalInc inp.G)
  hedge : s.arrs a_edge = List.ofFn (leafEdgeAt inp.τ inp.G.numEdges)
  hcap : s.arrs a_cap = List.ofFn (capVal inp.G inp.Z)
  hdegC : s.arrs a_degC = List.ofFn (fun z : Fin inp.t => (childrenUpTo inp.p z.1 inp.t).length)
  hch : s.arrs a_ch = List.ofFn (fun idx : Fin (3 * inp.t) =>
    (childrenUpTo inp.p (idx.1 / 3) inp.t).getD (idx.1 % 3) 0)
  hacc_zV : (s.arrs a_acc_zV).length = Q_max ξ ω
  hacc_zI : (s.arrs a_acc_zI).length = Q_max ξ ω
  hacc_vv : (s.arrs a_acc_vv).length = S_tab δ ξ ω
  hacc_ve : (s.arrs a_acc_ve).length = S_tab δ ξ ω
  hacc_em : (s.arrs a_acc_em).length = S_tab δ ξ ω
  hrhs_zV : (s.arrs a_rhs_zV).length = Q_max ξ ω
  hrhs_zI : (s.arrs a_rhs_zI).length = Q_max ξ ω
  hrhs_vv : (s.arrs a_rhs_vv).length = S_tab δ ξ ω
  hrhs_ve : (s.arrs a_rhs_ve).length = S_tab δ ξ ω
  hrhs_em : (s.arrs a_rhs_em).length = S_tab δ ξ ω
  hout_zV : (s.arrs a_out_zV).length = Q_max ξ ω
  hout_zI : (s.arrs a_out_zI).length = Q_max ξ ω
  hout_vv : (s.arrs a_out_vv).length = S_tab δ ξ ω
  hout_ve : (s.arrs a_out_ve).length = S_tab δ ξ ω
  hout_em : (s.arrs a_out_em).length = S_tab δ ξ ω
  hsub_tid : (s.arrs a_sub_tid).length = inp.t
  hsub_q : (s.arrs a_sub_q).length = inp.t
  hsub_zV : (s.arrs a_sub_zV).length = inp.t * Q_max ξ ω
  hsub_zI : (s.arrs a_sub_zI).length = inp.t * Q_max ξ ω
  hsub_vv : (s.arrs a_sub_vv).length = inp.t * S_tab δ ξ ω
  hsub_ve : (s.arrs a_sub_ve).length = inp.t * S_tab δ ξ ω
  hsub_em : (s.arrs a_sub_em).length = inp.t * S_tab δ ξ ω

theorem TreeDPStateInv.setReg_ge3 {δ ξ ω : ℕ} {inp : Alg41CoreInput ξ ω} {s : State}
    (h : TreeDPStateInv δ ξ ω inp s) (r : ℕ) (hr : 3 ≤ r) (v : ℕ) :
    TreeDPStateInv δ ξ ω inp (s.setReg r v) := by
  have h0 : (0 : ℕ) ≠ r := by omega
  have h1 : (1 : ℕ) ≠ r := by omega
  have h2 : (2 : ℕ) ≠ r := by omega
  refine ⟨?_, ?_, ?_, h.hhead, h.htail, h.hZ, h.htot, h.hedge, h.hcap, h.hdegC, h.hch,
    h.hacc_zV, h.hacc_zI, h.hacc_vv, h.hacc_ve, h.hacc_em,
    h.hrhs_zV, h.hrhs_zI, h.hrhs_vv, h.hrhs_ve, h.hrhs_em,
    h.hout_zV, h.hout_zI, h.hout_vv, h.hout_ve, h.hout_em,
    h.hsub_tid, h.hsub_q, h.hsub_zV, h.hsub_zI, h.hsub_vv, h.hsub_ve, h.hsub_em⟩
  · rw [State.setReg_regs_ne s v h0]; exact h.hr0
  · rw [State.setReg_regs_ne s v h1]; exact h.hr1
  · rw [State.setReg_regs_ne s v h2]; exact h.hr2

/-- Arena pointer and well-formedness invariant. -/
structure ArenaStateInv (G : ComputeDigraph) (kv ke : ℕ) (s : State) : Prop where
  hr_kv : s.regs r_kv = kv
  hr_ke : s.regs r_ke = ke
  hwfV : ArenaWF G.numVerts kv (s.arrs a_vkd) (s.arrs a_vv1) (s.arrs a_vv2)
  hwfE : ArenaWF G.numEdges ke (s.arrs a_ekd) (s.arrs a_ev1) (s.arrs a_ev2)

theorem ArenaStateInv.setReg_ne {G : ComputeDigraph} {kv ke : ℕ} {s : State}
    (h : ArenaStateInv G kv ke s) (r : ℕ) (h1 : r ≠ r_kv) (h2 : r ≠ r_ke) (v : ℕ) :
    ArenaStateInv G kv ke (s.setReg r v) :=
  ⟨by rw [State.setReg_regs_ne _ _ h1.symm]; exact h.hr_kv,
   by rw [State.setReg_regs_ne _ _ h2.symm]; exact h.hr_ke,
   h.hwfV, h.hwfE⟩

theorem ValidSubtreeSlot.setReg_ne {δ ξ ω x : ℕ} {G : ComputeDigraph}
    {Z_P : Finset (Fin G.numVerts)} {E_P : Finset (Fin G.numEdges)}
    {es : List (RawCertEntry G Z_P.card)} {s : State}
    (h : ValidSubtreeSlot δ ξ ω G Z_P E_P es x s)
    (r : ℕ) (h1 : r ≠ r_kv) (h2 : r ≠ r_ke) (v : ℕ) :
    ValidSubtreeSlot δ ξ ω G Z_P E_P es x (s.setReg r v) :=
  h.mono_arena rfl rfl rfl rfl rfl rfl rfl
    (by rw [State.setReg_regs_ne _ _ h1.symm])
    (by rw [State.setReg_regs_ne _ _ h2.symm])
    (fun _ _ => rfl) (fun _ _ => rfl)

/-- Child-combination step `j` (`j < 3`) at tree node `r_9 = x`:
if `j < a_degC[x]`, load child `c = a_ch[3 * x + j]` into `bufB` and combine `bufA` with `bufB`. -/
def treeChildStepProg (δ ξ ω j : ℕ) : Cmd :=
  .ite (.op .lt (.const j) (.read a_degC (.reg 9)))
    (.seq (.assign 10 (.read a_ch (.op .add (.op .mul (.const 3) (.reg 9)) (.const j))))
      (.seq (loadSubtreeProg δ ξ ω 10)
        (combineStepProg δ ξ ω)))
    .skip

theorem treeChildStepProg_exec {w δ ξ ω : ℕ} (inp : Alg41CoreInput ξ ω)
    (hw : Alg41WordBounds w δ ξ ω inp)
    {x j kv₀ ke₀ k_j : ℕ} (hx_lt : x < inp.t) (hj : j < 3)
    (hk_ge : x + 1 ≤ k_j) (hk_le : k_j ≤ inp.t)
    (acc_j : PieceFolioTable inp.G inp.Z δ (dpAccEB inp.G inp.p inp.τ x k_j))
    (hfilter : ((List.range inp.t).drop k_j).filter (fun c => decide (inp.p c = x)) =
      (childrenUpTo inp.p x inp.t).drop j)
    {s₀ : State}
    (hinv : TreeDPStateInv δ ξ ω inp s₀)
    (har : ArenaStateInv inp.G kv₀ ke₀ s₀)
    (hr9 : s₀.regs 9 = x)
    (hkv_w : kv₀ + K_comb δ ξ ω < 2 ^ w) (hke_w : ke₀ + K_comb δ ξ ω < 2 ^ w)
    (hkv_cap : kv₀ + K_comb δ ξ ω ≤ (s₀.arrs a_vkd).length)
    (hke_cap : ke₀ + K_comb δ ξ ω ≤ (s₀.arrs a_ekd).length)
    (hbufA : ValidPieceBuffer δ ξ ω inp.G
      (pieceZ inp.G inp.Z (dpAccEB inp.G inp.p inp.τ x k_j))
      (dpAccEB inp.G inp.p inp.τ x k_j) acc_j.toRawList bufA s₀)
    (hslots : ∀ y, x < y → (hy : y < inp.t) →
      ValidSubtreeSlot δ ξ ω inp.G
        (pieceZ inp.G inp.Z (dpEB inp.G inp.p inp.τ y))
        (dpEB inp.G inp.p inp.τ y)
        (dpSubtreeTable inp.G inp.Z δ inp.p inp.hp inp.τ y hy).toRawList y s₀) :
    ∃ (s' : State) (t_step kv' ke' k' : ℕ) (hk'_ge : x + 1 ≤ k') (hk'_le : k' ≤ inp.t)
      (acc' : PieceFolioTable inp.G inp.Z δ (dpAccEB inp.G inp.p inp.τ x k')),
      Exec w (treeChildStepProg δ ξ ω j) s₀ s' t_step ∧
      t_step ≤ 30 + C_subtreeCopy δ ξ ω + C_combineStep δ ξ ω ∧
      kv₀ ≤ kv' ∧ kv' ≤ kv₀ + K_comb δ ξ ω ∧
      ke₀ ≤ ke' ∧ ke' ≤ ke₀ + K_comb δ ξ ω ∧
      TreeDPStateInv δ ξ ω inp s' ∧
      ArenaStateInv inp.G kv' ke' s' ∧
      s'.regs 9 = x ∧
      (s'.arrs a_vkd).length = (s₀.arrs a_vkd).length ∧
      (s'.arrs a_ekd).length = (s₀.arrs a_ekd).length ∧
      (∀ p < kv₀,
        evalArena inp.G.numVerts (s'.arrs a_vkd) (s'.arrs a_vv1) (s'.arrs a_vv2) p =
          evalArena inp.G.numVerts (s₀.arrs a_vkd) (s₀.arrs a_vv1) (s₀.arrs a_vv2) p) ∧
      (∀ p < ke₀,
        evalArena inp.G.numEdges (s'.arrs a_ekd) (s'.arrs a_ev1) (s'.arrs a_ev2) p =
          evalArena inp.G.numEdges (s₀.arrs a_ekd) (s₀.arrs a_ev1) (s₀.arrs a_ev2) p) ∧
      ((List.range inp.t).drop k').filter (fun c => decide (inp.p c = x)) =
        (childrenUpTo inp.p x inp.t).drop (j + 1) ∧
      (dpChildrenLoop inp.G inp.Z δ inp.p inp.hp inp.τ x
        (fun k _ hkt => dpSubtreeTable inp.G inp.Z δ inp.p inp.hp inp.τ k hkt)
        k' hk'_ge hk'_le acc').toSigmaRaw =
        (dpChildrenLoop inp.G inp.Z δ inp.p inp.hp inp.τ x
          (fun k _ hkt => dpSubtreeTable inp.G inp.Z δ inp.p inp.hp inp.τ k hkt)
          k_j hk_ge hk_le acc_j).toSigmaRaw ∧
      ValidPieceBuffer δ ξ ω inp.G
        (pieceZ inp.G inp.Z (dpAccEB inp.G inp.p inp.τ x k'))
        (dpAccEB inp.G inp.p inp.τ x k') acc'.toRawList bufA s' ∧
      (∀ y, x < y → (hy : y < inp.t) →
        ValidSubtreeSlot δ ξ ω inp.G
          (pieceZ inp.G inp.Z (dpEB inp.G inp.p inp.τ y))
          (dpEB inp.G inp.p inp.τ y)
          (dpSubtreeTable inp.G inp.Z δ inp.p inp.hp inp.τ y hy).toRawList y s') := by
  let cs := childrenUpTo inp.p x inp.t
  have hcs_le3 : cs.length ≤ 3 :=
    (length_childrenUpTo_le_card_childrenFinset inp.hp x (le_refl inp.t)).trans (inp.hch ⟨x, hx_lt⟩)
  have hw8 := hw.hw8
  have ht_w := hw.ht_w
  have hx_w : x < 2 ^ w := by omega
  have hj_w : j < 2 ^ w := by omega
  have hcslen_w : cs.length < 2 ^ w := by omega
  have h0_w : 0 < 2 ^ w := by omega
  have h1_w : 1 < 2 ^ w := by omega
  have hread_deg : (Expr.read a_degC (.reg 9)).eval w s₀ = some cs.length := by
    simp [Expr.eval, checkWord, hr9, hx_w, hinv.hdegC, hx_lt, cs, hcslen_w]
  by_cases hj_cs : j < cs.length
  · have hcond : (Expr.op .lt (.const j) (.read a_degC (.reg 9))).eval w s₀ = some 1 := by
      rw [Expr.eval, hread_deg]
      simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hj_w, hj_cs, h1_w]
    have hdrop_cons : cs.drop j = cs[j] :: cs.drop (j + 1) :=
      List.drop_eq_getElem_cons hj_cs
    let c := cs[j]
    have hfilter_cons :
        ((List.range inp.t).drop k_j).filter (fun c => decide (inp.p c = x)) =
          c :: cs.drop (j + 1) :=
      hfilter.trans hdrop_cons
    rcases drop_range_filter_eq_cons hfilter_cons with
      ⟨hk_c, hc_lt, hpc_bool, hne_before_bool, hfilter_next⟩
    have hpc : inp.p c = x := of_decide_eq_true hpc_bool
    have hne_before : ∀ k', k_j ≤ k' → k' < c → inp.p k' ≠ x :=
      fun k' hk1 hk2 => of_decide_eq_false (hne_before_bool k' hk1 hk2)
    have hxc : x < c := by omega
    have hc_w : c < 2 ^ w := by omega
    have h3_w : 3 < 2 ^ w := by omega
    have h3x_w : 3 * x < 2 ^ w := by have := hw.ht3_w; omega
    have h3xj_lt : 3 * x + j < 3 * inp.t := by omega
    have h3xj_w : 3 * x + j < 2 ^ w := by have := hw.ht3_w; omega
    have hch_idx : (s₀.arrs a_ch)[3 * x + j]'(by rw [hinv.hch]; simp [h3xj_lt]) = c := by
      rw [List.getElem_of_eq hinv.hch, List.getElem_ofFn]
      have hdiv : (3 * x + j) / 3 = x := by omega
      have hmod : (3 * x + j) % 3 = j := by omega
      rw [hdiv, hmod]
      change cs.getD j 0 = cs[j]
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj_cs, Option.getD_some]
    let s₁ := s₀.setReg 10 c
    have hex₁ : Exec w (.assign 10 (.read a_ch (.op .add (.op .mul (.const 3) (.reg 9)) (.const j)))) s₀ s₁ 7 := by
      refine .assign ?_
      simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hr9, h3_w, hx_w, h3x_w, hj_w, h3xj_w,
        show 3 * x + j < (s₀.arrs a_ch).length by rw [hinv.hch]; simp [h3xj_lt], hch_idx, hc_w]
    have hslot_c : ValidSubtreeSlot δ ξ ω inp.G
        (pieceZ inp.G inp.Z (dpEB inp.G inp.p inp.τ c))
        (dpEB inp.G inp.p inp.τ c)
        (dpSubtreeTable inp.G inp.Z δ inp.p inp.hp inp.τ c hc_lt).toRawList c s₁ :=
      (hslots c hxc hc_lt).mono_slice rfl rfl (fun _ _ => rfl) (fun _ _ => rfl)
        (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl)
        (le_refl _) (le_refl _) (fun _ _ => rfl) (fun _ _ => rfl)
    rcases loadSubtreeProg_exec (w := w) (δ := δ) (ξ := ξ) (ω := ω) (t := inp.t) (x := c)
        (kv₀ := kv₀) (ke₀ := ke₀) (r_x := 10) (s₀ := s₁)
        hslot_c (by decide) (by decide) hc_lt hw.hn_w hw.hm_w hw.htQ_w hw.htS_w hw.hT_w
        (by omega) (by omega)
        (by simp [s₁, hinv.hr0]) (by simp [s₁, hinv.hr1])
        (by simp [s₁, har.hr_kv]) (by simp [s₁, har.hr_ke]) (by simp [s₁])
        hinv.hsub_tid hinv.hsub_q hinv.hsub_zV hinv.hsub_zI hinv.hsub_vv hinv.hsub_ve hinv.hsub_em
        hinv.hrhs_zV hinv.hrhs_zI hinv.hrhs_vv hinv.hrhs_ve hinv.hrhs_em with
      ⟨s₂, t_load, hex_load, ht_load, hbufB₂, hreg₂, harr₂⟩
    have hE_skip := dpAccEB_eq_of_forall_ne inp.G inp.p inp.τ x k_j c hk_c hne_before
    let acc_c : PieceFolioTable inp.G inp.Z δ (dpAccEB inp.G inp.p inp.τ x c) :=
      acc_j.castSets (by rw [hE_skip]) hE_skip.symm (by rw [hE_skip])
    have hbufA_s₂_kj : ValidPieceBuffer δ ξ ω inp.G
        (pieceZ inp.G inp.Z (dpAccEB inp.G inp.p inp.τ x k_j))
        (dpAccEB inp.G inp.p inp.τ x k_j) acc_j.toRawList bufA s₂ :=
      hbufA.mono_arena
        (by rw [hreg₂ bufA.r_tid (by decide) (by decide)]; rfl)
        (by rw [hreg₂ bufA.r_q (by decide) (by decide)]; rfl)
        (harr₂ bufA.a_zV (by decide) (by decide) (by decide) (by decide) (by decide))
        (harr₂ bufA.a_zI (by decide) (by decide) (by decide) (by decide) (by decide))
        (harr₂ bufA.a_vv (by decide) (by decide) (by decide) (by decide) (by decide))
        (harr₂ bufA.a_ve (by decide) (by decide) (by decide) (by decide) (by decide))
        (harr₂ bufA.a_em (by decide) (by decide) (by decide) (by decide) (by decide))
        (by rw [hreg₂ r_kv (by decide) (by decide)]; exact le_refl _)
        (by rw [hreg₂ r_ke (by decide) (by decide)]; exact le_refl _)
        (fun p _ => by
          rw [harr₂ a_vkd (by decide) (by decide) (by decide) (by decide) (by decide),
              harr₂ a_vv1 (by decide) (by decide) (by decide) (by decide) (by decide),
              harr₂ a_vv2 (by decide) (by decide) (by decide) (by decide) (by decide)]; rfl)
        (fun p _ => by
          rw [harr₂ a_ekd (by decide) (by decide) (by decide) (by decide) (by decide),
              harr₂ a_ev1 (by decide) (by decide) (by decide) (by decide) (by decide),
              harr₂ a_ev2 (by decide) (by decide) (by decide) (by decide) (by decide)]; rfl)
    have hbufA_s₂_c : ValidPieceBuffer δ ξ ω inp.G
        (pieceZ inp.G inp.Z (dpAccEB inp.G inp.p inp.τ x c))
        (dpAccEB inp.G inp.p inp.τ x c) acc_c.toRawList bufA s₂ :=
      ValidPieceBuffer.of_toSigmaRaw_eq hE_skip.symm (by rw [hE_skip])
        (CertFolioTable.toSigmaRaw_castSets _ _ _ acc_j).symm hbufA_s₂_kj
    let EA := dpAccEB inp.G inp.p inp.τ x c
    let EB := dpEB inp.G inp.p inp.τ c
    let ZA := pieceZ inp.G inp.Z EA
    let ZB := pieceZ inp.G inp.Z EB
    let Z' := pieceZ inp.G inp.Z (EA ∪ EB)
    have hE_disj : Disjoint EA EB := disjoint_dpAccEB_dpEB inp.G inp.hp inp.τ hxc hpc
    have hq_ZA : ZA.card ≤ 2 + 3 * (ω + ξ) := inp.hQ_acc x hx_lt c (by omega) (by omega)
    have hq_ZB : ZB.card ≤ ω + ξ := inp.hQ_child c (by omega) hc_lt
    have hqU : (ZA ∪ ZB).card ≤ Q_max ξ ω := by
      have := Finset.card_union_le ZA ZB
      unfold Q_max; omega
    rcases combineStepProg_exec_pieceTables
        (w := w) (δ := δ) (ξ := ξ) (ω := ω) (kv₀ := kv₀) (ke₀ := ke₀)
        (G := inp.G) (Z := inp.Z)
        (VA := pieceVB inp.G EA) (VB := pieceVB inp.G EB)
        (ZA := ZA) (ZB := ZB) (Z' := Z') (EA := EA) (EB := EB)
        (pieceZ_subset_pieceVB inp.G inp.Z EA)
        (pieceZ_subset_pieceVB inp.G inp.Z EB)
        hE_disj
        (fun _ he => ⟨head_mem_edgeEnds he, tail_mem_edgeEnds he⟩)
        (fun _ he => ⟨head_mem_edgeEnds he, tail_mem_edgeEnds he⟩)
        (pieceVB_inter_subset_pieceZ inp.Z hE_disj)
        hqU (mem_pieceZ_union_iff inp.G inp.Z EA EB)
        acc_c (dpSubtreeTable inp.G inp.Z δ inp.p inp.hp inp.τ c hc_lt)
        (s₀ := s₂) hbufA_s₂_c hbufB₂
        hw8 hw.hn_w hw.hm1_w hw.hQ_w hw.hS_w hw.hT_w hw.hM_w hkv_w hke_w
        (by rw [hreg₂ 0 (by decide) (by decide)]; simp [s₁, hinv.hr0])
        (by rw [hreg₂ 1 (by decide) (by decide)]; simp [s₁, hinv.hr1])
        (by rw [hreg₂ r_kv (by decide) (by decide)]; simp [s₁, har.hr_kv])
        (by rw [hreg₂ r_ke (by decide) (by decide)]; simp [s₁, har.hr_ke])
        (by rw [harr₂ a_cap (by decide) (by decide) (by decide) (by decide) (by decide)]; exact hinv.hcap)
        (by rw [harr₂ a_vkd (by decide) (by decide) (by decide) (by decide) (by decide),
                harr₂ a_vv1 (by decide) (by decide) (by decide) (by decide) (by decide),
                harr₂ a_vv2 (by decide) (by decide) (by decide) (by decide) (by decide)]; exact har.hwfV)
        (by rw [harr₂ a_ekd (by decide) (by decide) (by decide) (by decide) (by decide),
                harr₂ a_ev1 (by decide) (by decide) (by decide) (by decide) (by decide),
                harr₂ a_ev2 (by decide) (by decide) (by decide) (by decide) (by decide)]; exact har.hwfE)
        (by rw [harr₂ a_vkd (by decide) (by decide) (by decide) (by decide) (by decide)]; exact hkv_cap)
        (by rw [harr₂ a_ekd (by decide) (by decide) (by decide) (by decide) (by decide)]; exact hke_cap)
        (by rw [harr₂ a_out_zV (by decide) (by decide) (by decide) (by decide) (by decide)]; exact hinv.hout_zV)
        (by rw [harr₂ a_out_zI (by decide) (by decide) (by decide) (by decide) (by decide)]; exact hinv.hout_zI)
        (by rw [harr₂ a_out_vv (by decide) (by decide) (by decide) (by decide) (by decide)]; exact hinv.hout_vv)
        (by rw [harr₂ a_out_ve (by decide) (by decide) (by decide) (by decide) (by decide)]; exact hinv.hout_ve)
        (by rw [harr₂ a_out_em (by decide) (by decide) (by decide) (by decide) (by decide)]; exact hinv.hout_em) with
      ⟨s', t_comb, hex_comb, ht_comb, hkv', hke', hwfV', hwfE', hlenV', hlenE', hevV', hevE',
       hbufA', hbufB', hout_zV', hout_zI', hout_vv', hout_ve', hout_em', hreg', harr'⟩
    have hE_step := dpAccEB_step_eq inp.G inp.p inp.τ hc_lt hxc hpc
    let acc' : PieceFolioTable inp.G inp.Z δ (dpAccEB inp.G inp.p inp.τ x (c + 1)) :=
      (combineEdgePieceTables hE_disj acc_c (dpSubtreeTable inp.G inp.Z δ inp.p inp.hp inp.τ c hc_lt)).castSets
        (by rw [hE_step]) hE_step.symm (by rw [hE_step])
    have hbufA_acc' : ValidPieceBuffer δ ξ ω inp.G
        (pieceZ inp.G inp.Z (dpAccEB inp.G inp.p inp.τ x (c + 1)))
        (dpAccEB inp.G inp.p inp.τ x (c + 1)) acc'.toRawList bufA s' := by
      refine ValidPieceBuffer.of_toSigmaRaw_eq hE_step.symm (by rw [hE_step]) ?_ hbufA'
      rw [CertFolioTable.toSigmaRaw_castSets, toSigmaRaw_combineEdgePieceTables]
    have hloop_eq :
        (dpChildrenLoop inp.G inp.Z δ inp.p inp.hp inp.τ x
          (fun k _ hkt => dpSubtreeTable inp.G inp.Z δ inp.p inp.hp inp.τ k hkt)
          (c + 1) (by omega) (by omega) acc').toSigmaRaw =
        (dpChildrenLoop inp.G inp.Z δ inp.p inp.hp inp.τ x
          (fun k _ hkt => dpSubtreeTable inp.G inp.Z δ inp.p inp.hp inp.τ k hkt)
          k_j hk_ge hk_le acc_j).toSigmaRaw := by
      have h1 := dpChildrenLoop_step_eq inp.G inp.Z δ inp.p inp.hp inp.τ x
        (fun k _ hkt => dpSubtreeTable inp.G inp.Z δ inp.p inp.hp inp.τ k hkt)
        c (by omega) hc_lt hpc acc_c
      have h2 := dpChildrenLoop_toSigmaRaw_skip_to inp.G inp.Z δ inp.p inp.hp inp.τ x
        (fun k _ hkt => dpSubtreeTable inp.G inp.Z δ inp.p inp.hp inp.τ k hkt)
        hk_ge hk_c (by omega) hne_before acc_j
      rw [← h1]
      exact h2
    have harr_ro : ∀ a,
        a ≠ a_vkd → a ≠ a_vv1 → a ≠ a_vv2 → a ≠ a_ekd → a ≠ a_ev1 → a ≠ a_ev2 →
        a ≠ a_out_zV → a ≠ a_out_zI → a ≠ a_out_vv → a ≠ a_out_ve → a ≠ a_out_em →
        a ≠ a_acc_zV → a ≠ a_acc_zI → a ≠ a_acc_vv → a ≠ a_acc_ve → a ≠ a_acc_em →
        a ≠ a_rhs_zV → a ≠ a_rhs_zI → a ≠ a_rhs_vv → a ≠ a_rhs_ve → a ≠ a_rhs_em →
        s'.arrs a = s₀.arrs a :=
      fun a h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16 h17 h18 h19 h20 h21 =>
        (harr' a h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16).trans
          (harr₂ a h17 h18 h19 h20 h21)
    have hevV_0 : ∀ p < kv₀,
        evalArena inp.G.numVerts (s'.arrs a_vkd) (s'.arrs a_vv1) (s'.arrs a_vv2) p =
          evalArena inp.G.numVerts (s₀.arrs a_vkd) (s₀.arrs a_vv1) (s₀.arrs a_vv2) p :=
      fun p hp => by
        rw [hevV' p hp,
            harr₂ a_vkd (by decide) (by decide) (by decide) (by decide) (by decide),
            harr₂ a_vv1 (by decide) (by decide) (by decide) (by decide) (by decide),
            harr₂ a_vv2 (by decide) (by decide) (by decide) (by decide) (by decide)]
        rfl
    have hevE_0 : ∀ p < ke₀,
        evalArena inp.G.numEdges (s'.arrs a_ekd) (s'.arrs a_ev1) (s'.arrs a_ev2) p =
          evalArena inp.G.numEdges (s₀.arrs a_ekd) (s₀.arrs a_ev1) (s₀.arrs a_ev2) p :=
      fun p hp => by
        rw [hevE' p hp,
            harr₂ a_ekd (by decide) (by decide) (by decide) (by decide) (by decide),
            harr₂ a_ev1 (by decide) (by decide) (by decide) (by decide) (by decide),
            harr₂ a_ev2 (by decide) (by decide) (by decide) (by decide) (by decide)]
        rfl
    have hinv' : TreeDPStateInv δ ξ ω inp s' := by
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
        hbufA'.hzV_len, hbufA'.hzI_len, hbufA'.hvv_len, hbufA'.hve_len, hbufA'.hem_len,
        hbufB'.hzV_len, hbufB'.hzI_len, hbufB'.hvv_len, hbufB'.hve_len, hbufB'.hem_len,
        hout_zV', hout_zI', hout_vv', hout_ve', hout_em',
        ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · rw [hreg' 0 (by decide) (by decide) (by decide) (by decide) (by decide),
            hreg₂ 0 (by decide) (by decide)]; simp [s₁, hinv.hr0]
      · rw [hreg' 1 (by decide) (by decide) (by decide) (by decide) (by decide),
            hreg₂ 1 (by decide) (by decide)]; simp [s₁, hinv.hr1]
      · rw [hreg' 2 (by decide) (by decide) (by decide) (by decide) (by decide),
            hreg₂ 2 (by decide) (by decide)]; simp [s₁, hinv.hr2]
      · rw [harr_ro a_head (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]; exact hinv.hhead
      · rw [harr_ro a_tail (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]; exact hinv.htail
      · rw [harr_ro a_Z (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]; exact hinv.hZ
      · rw [harr_ro a_tot (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]; exact hinv.htot
      · rw [harr_ro a_edge (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]; exact hinv.hedge
      · rw [harr_ro a_cap (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]; exact hinv.hcap
      · rw [harr_ro a_degC (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]; exact hinv.hdegC
      · rw [harr_ro a_ch (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]; exact hinv.hch
      · rw [harr_ro a_sub_tid (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]; exact hinv.hsub_tid
      · rw [harr_ro a_sub_q (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]; exact hinv.hsub_q
      · rw [harr_ro a_sub_zV (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]; exact hinv.hsub_zV
      · rw [harr_ro a_sub_zI (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]; exact hinv.hsub_zI
      · rw [harr_ro a_sub_vv (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]; exact hinv.hsub_vv
      · rw [harr_ro a_sub_ve (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]; exact hinv.hsub_ve
      · rw [harr_ro a_sub_em (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]; exact hinv.hsub_em
    refine ⟨s', 4 + (7 + (t_load + t_comb)), kv₀ + K_comb δ ξ ω, ke₀ + K_comb δ ξ ω,
      c + 1, by omega, by omega, acc',
      .ite_true hcond (by decide) (.seq hex₁ (.seq hex_load hex_comb)),
      by omega, Nat.le_add_right _ _, le_refl _, Nat.le_add_right _ _, le_refl _,
      hinv', ⟨hkv', hke', hwfV', hwfE'⟩,
      by rw [hreg' 9 (by decide) (by decide) (by decide) (by decide) (by decide),
             hreg₂ 9 (by decide) (by decide)]; simp [s₁, hr9],
      by rw [hlenV', harr₂ a_vkd (by decide) (by decide) (by decide) (by decide) (by decide)]; rfl,
      by rw [hlenE', harr₂ a_ekd (by decide) (by decide) (by decide) (by decide) (by decide)]; rfl,
      hevV_0, hevE_0, hfilter_next, hloop_eq, hbufA_acc',
      fun y hxy hy => (hslots y hxy hy).mono_arena
        (by rw [harr_ro a_sub_tid (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)])
        (by rw [harr_ro a_sub_q (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)])
        (by rw [harr_ro a_sub_zV (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)])
        (by rw [harr_ro a_sub_zI (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)])
        (by rw [harr_ro a_sub_vv (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)])
        (by rw [harr_ro a_sub_ve (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)])
        (by rw [harr_ro a_sub_em (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)])
        (by rw [hkv', har.hr_kv]; exact Nat.le_add_right _ _)
        (by rw [hke', har.hr_ke]; exact Nat.le_add_right _ _)
        (fun p hp => hevV_0 p (har.hr_kv ▸ hp))
        (fun p hp => hevE_0 p (har.hr_ke ▸ hp))⟩
  · have hcond : (Expr.op .lt (.const j) (.read a_degC (.reg 9))).eval w s₀ = some 0 := by
      rw [Expr.eval, hread_deg]
      simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hj_w, hj_cs, h0_w]
    have hdrop_eq : cs.drop j = cs.drop (j + 1) := by
      rw [List.drop_of_length_le (by omega), List.drop_of_length_le (by omega)]
    refine ⟨s₀, 4 + 1, kv₀, ke₀, k_j, hk_ge, hk_le, acc_j,
      .ite_false hcond (.skip s₀), by omega,
      le_refl _, Nat.le_add_right _ _, le_refl _, Nat.le_add_right _ _,
      hinv, har, hr9, rfl, rfl, fun _ _ => rfl, fun _ _ => rfl,
      hfilter.trans hdrop_eq, rfl, hbufA, hslots⟩

/-- Arena capacity budget per tree node in `treeDPLoopProg`. -/
def K_node (δ ξ ω : ℕ) : ℕ := 3 + 3 * K_comb δ ξ ω

/-- Time bound for processing one tree node in `treeDPLoopProg`. -/
def C_treeNode (δ ξ ω : ℕ) : ℕ :=
  (380 + 15 * S_tab δ ξ ω) + 3 * (30 + C_subtreeCopy δ ξ ω + C_combineStep δ ξ ω) + C_subtreeCopy δ ξ ω

/-- Process tree node `r_9 = x`:
1. Initialize `bufA` with the leaf base table for `{e | τ e = x}` (`treeBaseStepProg δ ξ ω 9`).
2. Run up to 3 child-combination steps (`treeChildStepProg δ ξ ω 0`, `1`, `2`).
3. Store the resulting subtree table from `bufA` into subtree slot `x` (`storeSubtreeProg δ ξ ω 9`). -/
def treeNodeProg (δ ξ ω : ℕ) : Cmd :=
  .seq (treeBaseStepProg δ ξ ω 9)
  (.seq (treeChildStepProg δ ξ ω 0)
  (.seq (treeChildStepProg δ ξ ω 1)
  (.seq (treeChildStepProg δ ξ ω 2)
        (storeSubtreeProg δ ξ ω 9))))

theorem treeNodeProg_exec {w δ ξ ω : ℕ} (inp : Alg41CoreInput ξ ω)
    (hw : Alg41WordBounds w δ ξ ω inp)
    {x kv₀ ke₀ : ℕ} (hx_lt : x < inp.t)
    {s₀ : State}
    (hinv : TreeDPStateInv δ ξ ω inp s₀)
    (har : ArenaStateInv inp.G kv₀ ke₀ s₀)
    (hr9 : s₀.regs 9 = x)
    (hkv_w : kv₀ + K_node δ ξ ω < 2 ^ w) (hke_w : ke₀ + K_node δ ξ ω < 2 ^ w)
    (hkv_cap : kv₀ + K_node δ ξ ω ≤ (s₀.arrs a_vkd).length)
    (hke_cap : ke₀ + K_node δ ξ ω ≤ (s₀.arrs a_ekd).length)
    (hslots : ∀ y, x < y → (hy : y < inp.t) →
      ValidSubtreeSlot δ ξ ω inp.G
        (pieceZ inp.G inp.Z (dpEB inp.G inp.p inp.τ y))
        (dpEB inp.G inp.p inp.τ y)
        (dpSubtreeTable inp.G inp.Z δ inp.p inp.hp inp.τ y hy).toRawList y s₀) :
    ∃ s' t_node kv' ke',
      Exec w (treeNodeProg δ ξ ω) s₀ s' t_node ∧
      t_node ≤ C_treeNode δ ξ ω ∧
      kv₀ ≤ kv' ∧ kv' ≤ kv₀ + K_node δ ξ ω ∧
      ke₀ ≤ ke' ∧ ke' ≤ ke₀ + K_node δ ξ ω ∧
      TreeDPStateInv δ ξ ω inp s' ∧
      ArenaStateInv inp.G kv' ke' s' ∧
      s'.regs 9 = x ∧
      (s'.arrs a_vkd).length = (s₀.arrs a_vkd).length ∧
      (s'.arrs a_ekd).length = (s₀.arrs a_ekd).length ∧
      (∀ p < kv₀,
        evalArena inp.G.numVerts (s'.arrs a_vkd) (s'.arrs a_vv1) (s'.arrs a_vv2) p =
          evalArena inp.G.numVerts (s₀.arrs a_vkd) (s₀.arrs a_vv1) (s₀.arrs a_vv2) p) ∧
      (∀ p < ke₀,
        evalArena inp.G.numEdges (s'.arrs a_ekd) (s'.arrs a_ev1) (s'.arrs a_ev2) p =
          evalArena inp.G.numEdges (s₀.arrs a_ekd) (s₀.arrs a_ev1) (s₀.arrs a_ev2) p) ∧
      ValidPieceBuffer δ ξ ω inp.G
        (pieceZ inp.G inp.Z (dpEB inp.G inp.p inp.τ x))
        (dpEB inp.G inp.p inp.τ x)
        (dpSubtreeTable inp.G inp.Z δ inp.p inp.hp inp.τ x hx_lt).toRawList bufA s' ∧
      (∀ y, x ≤ y → (hy : y < inp.t) →
        ValidSubtreeSlot δ ξ ω inp.G
          (pieceZ inp.G inp.Z (dpEB inp.G inp.p inp.τ y))
          (dpEB inp.G inp.p inp.τ y)
          (dpSubtreeTable inp.G inp.Z δ inp.p inp.hp inp.τ y hy).toRawList y s') := by
  have hK : K_node δ ξ ω = 3 + 3 * K_comb δ ξ ω := rfl
  rcases treeBaseStepProg_exec inp ⟨x, hx_lt⟩ (r_x := 9)
      (by decide) (by decide) (by decide) (by decide) (by decide)
      hw.hw72 hw.hn_w hw.hm1_w hw.ht_w hw.hS_w hw.hT_w
      (by omega) (by omega) har.hwfV har.hwfE (by omega) (by omega)
      har.hr_kv har.hr_ke hr9 hinv.hhead hinv.htail hinv.hedge hinv.hcap
      hinv.hacc_zV hinv.hacc_zI hinv.hacc_vv hinv.hacc_ve hinv.hacc_em with
    ⟨s₁, t₁, hex₁, ht₁, hkv₁, hke₁, hwfV₁, hwfE₁, hlenV₁, hlenE₁, hevV₁, hevE₁,
     hbuf₁_raw, hreg₁, harr₁⟩
  let initTable : PieceFolioTable inp.G inp.Z δ (dpAccEB inp.G inp.p inp.τ x (x + 1)) :=
    (baseEdgePieceTable inp.G inp.Z δ (Finset.univ.filter (fun e => (inp.τ e).1 = x))).castSets
      (by rw [dpAccEB_self]) (dpAccEB_self inp.G inp.p inp.τ x).symm (by rw [dpAccEB_self])
  have hbuf₁ : ValidPieceBuffer δ ξ ω inp.G
      (pieceZ inp.G inp.Z (dpAccEB inp.G inp.p inp.τ x (x + 1)))
      (dpAccEB inp.G inp.p inp.τ x (x + 1)) initTable.toRawList bufA s₁ :=
    ValidPieceBuffer.of_toSigmaRaw_eq (dpAccEB_self inp.G inp.p inp.τ x).symm
      (by rw [dpAccEB_self]) (CertFolioTable.toSigmaRaw_castSets _ _ _ _).symm hbuf₁_raw
  have hinv₁ : TreeDPStateInv δ ξ ω inp s₁ := by
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
      hbuf₁.hzV_len, hbuf₁.hzI_len, hbuf₁.hvv_len, hbuf₁.hve_len, hbuf₁.hem_len,
      ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [hreg₁ 0 (by decide) (by decide) (by decide) (by decide) (by decide)]; exact hinv.hr0
    · rw [hreg₁ 1 (by decide) (by decide) (by decide) (by decide) (by decide)]; exact hinv.hr1
    · rw [hreg₁ 2 (by decide) (by decide) (by decide) (by decide) (by decide)]; exact hinv.hr2
    · rw [harr₁ a_head (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]; exact hinv.hhead
    · rw [harr₁ a_tail (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]; exact hinv.htail
    · rw [harr₁ a_Z (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]; exact hinv.hZ
    · rw [harr₁ a_tot (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]; exact hinv.htot
    · rw [harr₁ a_edge (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]; exact hinv.hedge
    · rw [harr₁ a_cap (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]; exact hinv.hcap
    · rw [harr₁ a_degC (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]; exact hinv.hdegC
    · rw [harr₁ a_ch (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]; exact hinv.hch
    · rw [harr₁ a_rhs_zV (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]; exact hinv.hrhs_zV
    · rw [harr₁ a_rhs_zI (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]; exact hinv.hrhs_zI
    · rw [harr₁ a_rhs_vv (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]; exact hinv.hrhs_vv
    · rw [harr₁ a_rhs_ve (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]; exact hinv.hrhs_ve
    · rw [harr₁ a_rhs_em (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]; exact hinv.hrhs_em
    · rw [harr₁ a_out_zV (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]; exact hinv.hout_zV
    · rw [harr₁ a_out_zI (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]; exact hinv.hout_zI
    · rw [harr₁ a_out_vv (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]; exact hinv.hout_vv
    · rw [harr₁ a_out_ve (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]; exact hinv.hout_ve
    · rw [harr₁ a_out_em (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]; exact hinv.hout_em
    · rw [harr₁ a_sub_tid (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]; exact hinv.hsub_tid
    · rw [harr₁ a_sub_q (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]; exact hinv.hsub_q
    · rw [harr₁ a_sub_zV (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]; exact hinv.hsub_zV
    · rw [harr₁ a_sub_zI (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]; exact hinv.hsub_zI
    · rw [harr₁ a_sub_vv (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]; exact hinv.hsub_vv
    · rw [harr₁ a_sub_ve (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]; exact hinv.hsub_ve
    · rw [harr₁ a_sub_em (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]; exact hinv.hsub_em
  have hslots₁ : ∀ y, x < y → (hy : y < inp.t) →
      ValidSubtreeSlot δ ξ ω inp.G
        (pieceZ inp.G inp.Z (dpEB inp.G inp.p inp.τ y))
        (dpEB inp.G inp.p inp.τ y)
        (dpSubtreeTable inp.G inp.Z δ inp.p inp.hp inp.τ y hy).toRawList y s₁ :=
    fun y hxy hy => (hslots y hxy hy).mono_arena
      (harr₁ a_sub_tid (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))
      (harr₁ a_sub_q (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))
      (harr₁ a_sub_zV (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))
      (harr₁ a_sub_zI (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))
      (harr₁ a_sub_vv (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))
      (harr₁ a_sub_ve (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))
      (harr₁ a_sub_em (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))
      (by rw [hkv₁, har.hr_kv]; exact Nat.le_add_right _ _)
      (by rw [hke₁, har.hr_ke]; exact Nat.le_add_right _ _)
      (fun p hp => hevV₁ p (har.hr_kv ▸ hp))
      (fun p hp => hevE₁ p (har.hr_ke ▸ hp))
  have hr9_1 : s₁.regs 9 = x := by
    rw [hreg₁ 9 (by decide) (by decide) (by decide) (by decide) (by decide)]; exact hr9
  rcases treeChildStepProg_exec inp hw hx_lt (j := 0) (by decide)
      (le_refl (x + 1)) (by omega) initTable
      (childrenUpTo_eq_drop_filter inp.hp hx_lt).symm
      hinv₁ ⟨hkv₁, hke₁, hwfV₁, hwfE₁⟩ hr9_1
      (by omega) (by omega) (by rw [hlenV₁]; omega) (by rw [hlenE₁]; omega)
      hbuf₁ hslots₁ with
    ⟨s₂, t₂, kv₂, ke₂, k₁, hk₁_ge, hk₁_le, acc₁, hex₂, ht₂, hkv₂_lo, hkv₂_hi, hke₂_lo, hke₂_hi,
     hinv₂, har₂, hr9_2, hlenV₂, hlenE₂, hevV₂, hevE₂, hfilter₁, hloop₁, hbuf₂, hslots₂⟩
  rcases treeChildStepProg_exec inp hw hx_lt (j := 1) (by decide)
      hk₁_ge hk₁_le acc₁ hfilter₁
      hinv₂ har₂ hr9_2
      (by omega) (by omega) (by rw [hlenV₂, hlenV₁]; omega) (by rw [hlenE₂, hlenE₁]; omega)
      hbuf₂ hslots₂ with
    ⟨s₃, t₃, kv₃, ke₃, k₂, hk₂_ge, hk₂_le, acc₂, hex₃, ht₃, hkv₃_lo, hkv₃_hi, hke₃_lo, hke₃_hi,
     hinv₃, har₃, hr9_3, hlenV₃, hlenE₃, hevV₃, hevE₃, hfilter₂, hloop₂, hbuf₃, hslots₃⟩
  rcases treeChildStepProg_exec inp hw hx_lt (j := 2) (by decide)
      hk₂_ge hk₂_le acc₂ hfilter₂
      hinv₃ har₃ hr9_3
      (by omega) (by omega) (by rw [hlenV₃, hlenV₂, hlenV₁]; omega) (by rw [hlenE₃, hlenE₂, hlenE₁]; omega)
      hbuf₃ hslots₃ with
    ⟨s₄, t₄, kv₄, ke₄, k₃, hk₃_ge, hk₃_le, acc₃, hex₄, ht₄, hkv₄_lo, hkv₄_hi, hke₄_lo, hke₄_hi,
     hinv₄, har₄, hr9_4, hlenV₄, hlenE₄, hevV₄, hevE₄, hfilter₃, hloop₃, hbuf₄, hslots₄⟩
  have hcs_le3 : (childrenUpTo inp.p x inp.t).length ≤ 3 :=
    (length_childrenUpTo_le_card_childrenFinset inp.hp x (le_refl inp.t)).trans (inp.hch ⟨x, hx_lt⟩)
  have hfilter_nil : ((List.range inp.t).drop k₃).filter (fun c => decide (inp.p c = x)) = [] := by
    rw [hfilter₃, List.drop_of_length_le hcs_le3]
  have hne_end : ∀ k', k₃ ≤ k' → k' < inp.t → inp.p k' ≠ x :=
    fun k' hk1 hk2 => of_decide_eq_false (drop_range_filter_eq_nil hfilter_nil k' hk1 hk2)
  have hE_end : dpAccEB inp.G inp.p inp.τ x k₃ = dpEB inp.G inp.p inp.τ x :=
    (dpAccEB_eq_of_forall_ne inp.G inp.p inp.τ x k₃ inp.t hk₃_le hne_end).symm.trans
      (dpAccEB_full inp.G inp.hp inp.τ hx_lt)
  have hSigma_end : acc₃.toSigmaRaw =
      (dpSubtreeTable inp.G inp.Z δ inp.p inp.hp inp.τ x hx_lt).toSigmaRaw := by
    have h_end := dpChildrenLoop_toSigmaRaw_of_forall_ne inp.G inp.Z δ inp.p inp.hp inp.τ x
      (fun k _ hkt => dpSubtreeTable inp.G inp.Z δ inp.p inp.hp inp.τ k hkt)
      k₃ hk₃_ge hk₃_le acc₃ hne_end
    unfold dpSubtreeTable
    rw [CertFolioTable.toSigmaRaw_castSets]
    exact h_end.symm.trans (hloop₃.trans (hloop₂.trans hloop₁))
  have hbuf₄_sub : ValidPieceBuffer δ ξ ω inp.G
      (pieceZ inp.G inp.Z (dpEB inp.G inp.p inp.τ x))
      (dpEB inp.G inp.p inp.τ x)
      (dpSubtreeTable inp.G inp.Z δ inp.p inp.hp inp.τ x hx_lt).toRawList bufA s₄ :=
    ValidPieceBuffer.of_toSigmaRaw_eq hE_end (by rw [hE_end]) hSigma_end hbuf₄
  rcases storeSubtreeProg_exec (w := w) (δ := δ) (ξ := ξ) (ω := ω) (t := inp.t) (x := x)
      (kv₀ := kv₄) (ke₀ := ke₄) (r_x := 9) (s₀ := s₄)
      hbuf₄_sub hx_lt hw.hn_w hw.hm_w hw.htQ_w hw.htS_w hw.hT_w
      (by omega) (by omega)
      hinv₄.hr0 hinv₄.hr1 har₄.hr_kv har₄.hr_ke hr9_4
      hinv₄.hsub_tid hinv₄.hsub_q hinv₄.hsub_zV hinv₄.hsub_zI
      hinv₄.hsub_vv hinv₄.hsub_ve hinv₄.hsub_em with
    ⟨s', t₅, hex₅, ht₅, hregs₅, hbuf', hslot_x, hslot_other,
     hsub_tid', hsub_q', hsub_zV', hsub_zI', hsub_vv', hsub_ve', hsub_em', harr₅⟩
  have hinv' : TreeDPStateInv δ ξ ω inp s' := by
    refine ⟨by rw [hregs₅]; exact hinv₄.hr0,
      by rw [hregs₅]; exact hinv₄.hr1,
      by rw [hregs₅]; exact hinv₄.hr2,
      by rw [harr₅ a_head (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]; exact hinv₄.hhead,
      by rw [harr₅ a_tail (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]; exact hinv₄.htail,
      by rw [harr₅ a_Z (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]; exact hinv₄.hZ,
      by rw [harr₅ a_tot (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]; exact hinv₄.htot,
      by rw [harr₅ a_edge (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]; exact hinv₄.hedge,
      by rw [harr₅ a_cap (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]; exact hinv₄.hcap,
      by rw [harr₅ a_degC (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]; exact hinv₄.hdegC,
      by rw [harr₅ a_ch (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]; exact hinv₄.hch,
      hbuf'.hzV_len, hbuf'.hzI_len, hbuf'.hvv_len, hbuf'.hve_len, hbuf'.hem_len,
      by rw [harr₅ a_rhs_zV (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]; exact hinv₄.hrhs_zV,
      by rw [harr₅ a_rhs_zI (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]; exact hinv₄.hrhs_zI,
      by rw [harr₅ a_rhs_vv (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]; exact hinv₄.hrhs_vv,
      by rw [harr₅ a_rhs_ve (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]; exact hinv₄.hrhs_ve,
      by rw [harr₅ a_rhs_em (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]; exact hinv₄.hrhs_em,
      by rw [harr₅ a_out_zV (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]; exact hinv₄.hout_zV,
      by rw [harr₅ a_out_zI (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]; exact hinv₄.hout_zI,
      by rw [harr₅ a_out_vv (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]; exact hinv₄.hout_vv,
      by rw [harr₅ a_out_ve (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]; exact hinv₄.hout_ve,
      by rw [harr₅ a_out_em (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]; exact hinv₄.hout_em,
      hsub_tid', hsub_q', hsub_zV', hsub_zI', hsub_vv', hsub_ve', hsub_em'⟩
  have har' : ArenaStateInv inp.G kv₄ ke₄ s' :=
    ⟨by rw [hregs₅]; exact har₄.hr_kv,
     by rw [hregs₅]; exact har₄.hr_ke,
     by rw [harr₅ a_vkd (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
            harr₅ a_vv1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
            harr₅ a_vv2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]; exact har₄.hwfV,
     by rw [harr₅ a_ekd (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
            harr₅ a_ev1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
            harr₅ a_ev2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]; exact har₄.hwfE⟩
  refine ⟨s', t₁ + (t₂ + (t₃ + (t₄ + t₅))), kv₄, ke₄,
    .seq hex₁ (.seq hex₂ (.seq hex₃ (.seq hex₄ hex₅))),
    by unfold C_treeNode; omega,
    by omega, by omega, by omega, by omega,
    hinv', har',
    by rw [hregs₅]; exact hr9_4,
    by rw [harr₅ a_vkd (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), hlenV₄, hlenV₃, hlenV₂, hlenV₁],
    by rw [harr₅ a_ekd (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), hlenE₄, hlenE₃, hlenE₂, hlenE₁],
    fun p hp => by
      rw [harr₅ a_vkd (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
          harr₅ a_vv1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
          harr₅ a_vv2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]
      exact (hevV₄ p (by omega)).trans ((hevV₃ p (by omega)).trans ((hevV₂ p (by omega)).trans (hevV₁ p hp))),
    fun p hp => by
      rw [harr₅ a_ekd (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
          harr₅ a_ev1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
          harr₅ a_ev2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]
      exact (hevE₄ p (by omega)).trans ((hevE₃ p (by omega)).trans ((hevE₂ p (by omega)).trans (hevE₁ p hp))),
    hbuf',
    fun y hxy hy => by
      by_cases hyx : y = x
      · subst hyx; exact hslot_x
      · exact hslot_other y hy hyx _ _ _ (hslots₄ y (by omega) hy)⟩

/-- Body of the bottom-up tree DP loop: decrement `r_9` and process node `r_9`. -/
def treeDPLoopBody (δ ξ ω : ℕ) : Cmd :=
  .seq (.assign 9 (.op .sub (.reg 9) (.const 1)))
       (treeNodeProg δ ξ ω)

/-- Bottom-up tree DP loop from `x = t - 1` down to `x = 0`. -/
def treeDPLoopProg (δ ξ ω : ℕ) : Cmd :=
  .seq (.assign 9 (.reg 2))
       (.while (.op .lt (.const 0) (.reg 9))
         (treeDPLoopBody δ ξ ω))

theorem treeDPLoop_exec {w δ ξ ω : ℕ} (inp : Alg41CoreInput ξ ω)
    (hw : Alg41WordBounds w δ ξ ω inp) :
    ∀ (rem : ℕ), rem ≤ inp.t → ∀ {kv₀ ke₀ : ℕ} {s₀ : State},
      TreeDPStateInv δ ξ ω inp s₀ →
      ArenaStateInv inp.G kv₀ ke₀ s₀ →
      s₀.regs 9 = rem →
      kv₀ + rem * K_node δ ξ ω < 2 ^ w →
      ke₀ + rem * K_node δ ξ ω < 2 ^ w →
      kv₀ + rem * K_node δ ξ ω ≤ (s₀.arrs a_vkd).length →
      ke₀ + rem * K_node δ ξ ω ≤ (s₀.arrs a_ekd).length →
      (∀ y, rem ≤ y → (hy : y < inp.t) →
        ValidSubtreeSlot δ ξ ω inp.G
          (pieceZ inp.G inp.Z (dpEB inp.G inp.p inp.τ y))
          (dpEB inp.G inp.p inp.τ y)
          (dpSubtreeTable inp.G inp.Z δ inp.p inp.hp inp.τ y hy).toRawList y s₀) →
      (∀ (hrem_lt : rem < inp.t),
        ValidPieceBuffer δ ξ ω inp.G
          (pieceZ inp.G inp.Z (dpEB inp.G inp.p inp.τ rem))
          (dpEB inp.G inp.p inp.τ rem)
          (dpSubtreeTable inp.G inp.Z δ inp.p inp.hp inp.τ rem hrem_lt).toRawList bufA s₀) →
      ∃ s' t_loop kv' ke',
        Exec w (.while (.op .lt (.const 0) (.reg 9)) (treeDPLoopBody δ ξ ω)) s₀ s' t_loop ∧
        t_loop ≤ 4 + rem * (15 + C_treeNode δ ξ ω) ∧
        kv₀ ≤ kv' ∧ kv' ≤ kv₀ + rem * K_node δ ξ ω ∧
        ke₀ ≤ ke' ∧ ke' ≤ ke₀ + rem * K_node δ ξ ω ∧
        TreeDPStateInv δ ξ ω inp s' ∧
        ArenaStateInv inp.G kv' ke' s' ∧
        (s'.arrs a_vkd).length = (s₀.arrs a_vkd).length ∧
        (s'.arrs a_ekd).length = (s₀.arrs a_ekd).length ∧
        ValidPieceBuffer δ ξ ω inp.G
          (pieceZ inp.G inp.Z (dpEB inp.G inp.p inp.τ 0))
          (dpEB inp.G inp.p inp.τ 0)
          (dpSubtreeTable inp.G inp.Z δ inp.p inp.hp inp.τ 0 inp.ht).toRawList bufA s' := by
  intro rem
  induction rem with
  | zero =>
    intro _ kv₀ ke₀ s₀ hinv har hr9 _ _ _ _ _ hbuf_rem
    have h0_w : 0 < 2 ^ w := by have := hw.hw72; omega
    have hcond : (Expr.op .lt (.const 0) (.reg 9)).eval w s₀ = some 0 := by
      simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hr9, h0_w]
    refine ⟨s₀, 3, kv₀, ke₀, .while_false hcond, by omega,
      le_refl _, by omega, le_refl _, by omega,
      hinv, har, rfl, rfl, hbuf_rem inp.ht⟩
  | succ x ih =>
    intro hrem_le kv₀ ke₀ s₀ hinv har hr9 hkv_w hke_w hkv_cap hke_cap hslots _
    have hx_lt : x < inp.t := by omega
    have ht_w := hw.ht_w
    have hx1_w : x + 1 < 2 ^ w := by omega
    have hx_w : x < 2 ^ w := by omega
    have h0_w : 0 < 2 ^ w := by have := hw.hw72; omega
    have h1_w : 1 < 2 ^ w := by have := hw.hw72; omega
    have hcond : (Expr.op .lt (.const 0) (.reg 9)).eval w s₀ = some 1 := by
      simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hr9, h0_w, hx1_w, h1_w]
    let s₁ := s₀.setReg 9 x
    have hex_dec : Exec w (.assign 9 (.op .sub (.reg 9) (.const 1))) s₀ s₁ 4 :=
      .assign (by simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hr9, hx1_w, h1_w, hx_w])
    have hmul_x : (x + 1) * K_node δ ξ ω = x * K_node δ ξ ω + K_node δ ξ ω :=
      Nat.succ_mul x (K_node δ ξ ω)
    rcases treeNodeProg_exec inp hw hx_lt
        (hinv.setReg_ge3 9 (by decide) x)
        (har.setReg_ne 9 (by decide) (by decide) x)
        (by simp)
        (by omega) (by omega)
        (le_trans (by omega) hkv_cap) (le_trans (by omega) hke_cap)
        (fun y hxy hy => (hslots y (by omega) hy).setReg_ne 9 (by decide) (by decide) x) with
      ⟨s₂, t_node, kv₂, ke₂, hex_node, ht_node, hkv₂_lo, hkv₂_hi, hke₂_lo, hke₂_hi,
       hinv₂, har₂, hr9_2, hlenV₂, hlenE₂, _hevV₂, _hevE₂, hbuf₂, hslots₂⟩
    rcases ih (by omega) hinv₂ har₂ hr9_2
        (by omega) (by omega)
        (by rw [hlenV₂]; exact le_trans (by omega) hkv_cap)
        (by rw [hlenE₂]; exact le_trans (by omega) hke_cap)
        hslots₂ (fun _ => hbuf₂) with
      ⟨s', t_ih, kv', ke', hex_ih, ht_ih, hkv'_lo, hkv'_hi, hke'_lo, hke'_hi,
       hinv', har', hlenV', hlenE', hbuf'⟩
    have hmul_t : (x + 1) * (15 + C_treeNode δ ξ ω) =
        x * (15 + C_treeNode δ ξ ω) + (15 + C_treeNode δ ξ ω) :=
      Nat.succ_mul x (15 + C_treeNode δ ξ ω)
    refine ⟨s', 3 + (4 + t_node) + t_ih, kv', ke',
      .while_true hcond (by decide) (.seq hex_dec hex_node) hex_ih,
      by omega, by omega, by omega, by omega, by omega,
      hinv', har',
      by rw [hlenV', hlenV₂]; rfl, by rw [hlenE', hlenE₂]; rfl, hbuf'⟩

theorem treeDPLoopProg_exec {w δ ξ ω : ℕ} (inp : Alg41CoreInput ξ ω)
    (hw : Alg41WordBounds w δ ξ ω inp)
    {kv₀ ke₀ : ℕ} {s₀ : State}
    (hinv : TreeDPStateInv δ ξ ω inp s₀)
    (har : ArenaStateInv inp.G kv₀ ke₀ s₀)
    (hkv_w : kv₀ + inp.t * K_node δ ξ ω < 2 ^ w)
    (hke_w : ke₀ + inp.t * K_node δ ξ ω < 2 ^ w)
    (hkv_cap : kv₀ + inp.t * K_node δ ξ ω ≤ (s₀.arrs a_vkd).length)
    (hke_cap : ke₀ + inp.t * K_node δ ξ ω ≤ (s₀.arrs a_ekd).length) :
    ∃ s' t_dp kv' ke',
      Exec w (treeDPLoopProg δ ξ ω) s₀ s' t_dp ∧
      t_dp ≤ 10 + inp.t * (15 + C_treeNode δ ξ ω) ∧
      kv₀ ≤ kv' ∧ kv' ≤ kv₀ + inp.t * K_node δ ξ ω ∧
      ke₀ ≤ ke' ∧ ke' ≤ ke₀ + inp.t * K_node δ ξ ω ∧
      TreeDPStateInv δ ξ ω inp s' ∧
      ArenaStateInv inp.G kv' ke' s' ∧
      (s'.arrs a_vkd).length = (s₀.arrs a_vkd).length ∧
      (s'.arrs a_ekd).length = (s₀.arrs a_ekd).length ∧
      ValidPieceBuffer δ ξ ω inp.G
        (pieceZ inp.G inp.Z (dpEB inp.G inp.p inp.τ 0))
        (dpEB inp.G inp.p inp.τ 0)
        (dpSubtreeTable inp.G inp.Z δ inp.p inp.hp inp.τ 0 inp.ht).toRawList bufA s' := by
  have ht_w := hw.ht_w
  let s₁ := s₀.setReg 9 inp.t
  have hex₁ : Exec w (.assign 9 (.reg 2)) s₀ s₁ 2 :=
    .assign (by simp [Expr.eval, checkWord, hinv.hr2, ht_w])
  rcases treeDPLoop_exec inp hw inp.t (le_refl _)
      (hinv.setReg_ge3 9 (by decide) inp.t)
      (har.setReg_ne 9 (by decide) (by decide) inp.t)
      (by simp) hkv_w hke_w hkv_cap hke_cap
      (fun y hy1 hy2 => by omega)
      (fun hlt => by omega) with
    ⟨s', t_loop, kv', ke', hex_loop, ht_loop, hkv'_lo, hkv'_hi, hke'_lo, hke'_hi,
     hinv', har', hlenV', hlenE', hbuf'⟩
  refine ⟨s', 2 + t_loop, kv', ke', .seq hex₁ hex_loop,
    by omega, hkv'_lo, hkv'_hi, hke'_lo, hke'_hi,
    hinv', har', hlenV', hlenE', hbuf'⟩

end GraphMinor.Compute
