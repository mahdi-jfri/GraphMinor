module

public import GraphMinor.Compute.Algorithm83

/-!
# Auxiliary Word RAM Subroutines for GM XIII Algorithm (8.6)

This file implements the Word RAM subroutines used by `Algorithm86.lean` to compute and serialize
the raw family $\mathcal{A}'$ and the quotient division $\mathcal{A}$ of a 4-linked core $(Z, C)$
in time $O(v\varepsilon)$ (`alg81Size x`).
-/

@[expose] public section

namespace GraphMinor.Compute

open SimpleGraph

/-! ### Section 1: Flat Encoding of Subgraphs and Subgraph Lists -/

/-- Flat word-list encoding of a subgraph $(V, \text{edges})$ on `Fin n`:
`bitSetList V ++ ([n, edges.length] ++ flatEdges edges)`. -/
def encAlg86Subgraph {n : ℕ} (V : Finset (Fin n)) (edges : List (Fin n × Fin n)) : List ℕ :=
  bitSetList V ++ ([n, edges.length] ++ flatEdges edges)

lemma length_encAlg86Subgraph {n : ℕ} (V : Finset (Fin n)) (edges : List (Fin n × Fin n)) :
    (encAlg86Subgraph V edges).length = n + 2 + 2 * edges.length := by
  simp [encAlg86Subgraph, length_bitSetList, length_flatEdges]
  omega

lemma mem_encAlg86Subgraph_w {w n : ℕ} (V : Finset (Fin n)) (edges : List (Fin n × Fin n))
    (hw : 1 < 2 ^ w) (hn_w : n < 2 ^ w) (hm_w : edges.length < 2 ^ w) :
    ∀ v ∈ encAlg86Subgraph V edges, v < 2 ^ w := by
  intro v hv
  simp only [encAlg86Subgraph, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hv
  rcases hv with hv_bit | (rfl | rfl) | hv_flat
  · rcases List.mem_iff_getElem.mp hv_bit with ⟨idx, hidx, rfl⟩
    have hle1 := getElem_bitSetList_le_one V idx hidx
    omega
  · exact hn_w
  · exact hm_w
  · exact Nat.lt_trans (mem_flatEdges_lt edges v hv_flat) hn_w

/-- Flat word-list encoding of a list of `(V, edges)` pairs:
`[L.length] ++ L.flatMap (fun p => encAlg86Subgraph p.1 p.2)`. -/
def encAlg86PairList {n : ℕ} (L : List (Finset (Fin n) × List (Fin n × Fin n))) : List ℕ :=
  [L.length] ++ L.flatMap (fun p => encAlg86Subgraph p.1 p.2)

/-- Overwriting the placeholder `0` immediately after `pre` with `val` in
`pre ++ [0] ++ mid ++ suf`. -/
lemma set_zero_between (pre mid suf : List ℕ) (val : ℕ) :
    (pre ++ [0] ++ mid ++ suf).set pre.length val = pre ++ [val] ++ mid ++ suf := by
  simp only [List.append_assoc, List.singleton_append]
  rw [List.set_append_right _ _ le_rfl, Nat.sub_self]
  rfl

/-! ### Section 2: Appending Slices and Subgraphs to `outArr` -/

/-- Loop body of `appendSliceToOutProg`: reads `a_src[r_2]` into `r_3`, writes it to
`outArr[r_25]`, and increments `r_25`. -/
def appendSliceToOutBody (a_src : Arr) : Cmd :=
  .seq (.assign 3 (.read a_src (.reg 2)))
    (.seq (.write outArr (.reg 25) (.reg 3))
      (.assign 25 (.op .add (.reg 25) (.const 1))))

/-- Copies the first `r_len` words of `a_src` into `outArr` starting at `r_25`, advancing
`r_25` by `r_len`. -/
def appendSliceToOutProg (a_src : Arr) (r_len : Reg) : Cmd :=
  .seq (.assign 2 (.const 0))
    (forUp 2 (.reg r_len) (appendSliceToOutBody a_src))

theorem appendSliceToOutLoop_exec {w len cap : ℕ} (a_src : Arr) (r_len : Reg)
    (hne_src : a_src ≠ outArr)
    (hne_len2 : r_len ≠ 2) (hne_len3 : r_len ≠ 3) (hne_len25 : r_len ≠ 25)
    (pref mid extra : List ℕ)
    (hmid_len : mid.length = len)
    (hmid_w : ∀ v ∈ mid, v < 2 ^ w)
    (hcap_le : pref.length + len ≤ cap)
    (hw : 1 < 2 ^ w) (hcap_w : cap < 2 ^ w)
    (rem k : ℕ) (hrem : k + rem = len) {s : State}
    (hsrc : s.arrs a_src = mid ++ extra)
    (hout : s.arrs outArr =
      (pref ++ mid.take k) ++ List.replicate (cap - (pref.length + k)) 0)
    (hrlen : s.regs r_len = len)
    (hr2 : s.regs 2 = k)
    (hr25 : s.regs 25 = pref.length + k) :
    ∃ s' t,
      Exec w (forUp 2 (.reg r_len) (appendSliceToOutBody a_src)) s s' t ∧
      t ≤ 3 + 17 * rem ∧
      s'.arrs outArr = (pref ++ mid) ++ List.replicate (cap - (pref.length + len)) 0 ∧
      s'.regs 25 = pref.length + len ∧
      (∀ a : Arr, a ≠ outArr → s'.arrs a = s.arrs a) ∧
      (∀ r : Reg, r ≠ 2 → r ≠ 3 → r ≠ 25 → s'.regs r = s.regs r) := by
  have h0_w : 0 < 2 ^ w := by omega
  have hlen_w : len < 2 ^ w := by omega
  induction rem generalizing k s with
  | zero =>
    have hk_eq : k = len := by omega
    subst hk_eq
    have hcond : (Expr.op .lt (.reg 2) (.reg r_len)).eval w s = some 0 := by
      simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hr2, hrlen, hlen_w]
    have htake : mid.take mid.length = mid := List.take_length
    rw [← hmid_len] at hout hr25 ⊢
    rw [htake] at hout
    exact ⟨s, 3, .while_false hcond, by omega, hout, hr25,
      fun _ _ => rfl, fun _ _ _ _ => rfl⟩
  | succ rem ih =>
    have hk_lt : k < len := by omega
    have hk_w : k < 2 ^ w := by omega
    have hk_mid : k < mid.length := by omega
    let val := mid[k]'hk_mid
    have hval_w : val < 2 ^ w := hmid_w val (List.getElem_mem hk_mid)
    have hcond : (Expr.op .lt (.reg 2) (.reg r_len)).eval w s = some 1 := by
      simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hr2, hrlen, hk_w, hlen_w, hk_lt, hw]
    have hk_src : k < (s.arrs a_src).length := by rw [hsrc, List.length_append]; omega
    have hget_src : (s.arrs a_src)[k]'hk_src = val := by
      simp only [hsrc, List.getElem_append_left hk_mid, val]
    let s₁ := s.setReg 3 val
    have hex₁ : Exec w (.assign 3 (.read a_src (.reg 2))) s s₁ 3 :=
      .assign (by simp [Expr.eval, checkWord, hr2, hk_w, hk_src, hget_src, hval_w])
    have hr25_w : pref.length + k < 2 ^ w := by omega
    have hout_idx : pref.length + k < (s₁.arrs outArr).length := by
      simp only [s₁, State.setReg_arrs, hout, List.length_append, List.length_take,
        List.length_replicate]
      omega
    let s₂ := s₁.writeArr outArr (pref.length + k) val
    have hex₂ : Exec w (.write outArr (.reg 25) (.reg 3)) s₁ s₂ 3 :=
      .write (by simp [s₁, State.setReg, Expr.eval, checkWord, hr25, hr25_w])
        (by simp [s₁, State.setReg, Expr.eval, checkWord, hval_w])
        hout_idx
    have hr25_s₂ : s₂.regs 25 = pref.length + k := hr25
    let s₃ := s₂.setReg 25 (pref.length + k + 1)
    have hex₃ : Exec w (.assign 25 (.op .add (.reg 25) (.const 1))) s₂ s₃ 4 :=
      .assign (by
        simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hr25_s₂, hr25_w, hw,
          show pref.length + k + 1 < 2 ^ w by omega])
    have hr2_s₃ : s₃.regs 2 = k := hr2
    let s₄ := s₃.setReg 2 (k + 1)
    have hex_inc : Exec w (.assign 2 (.op .add (.reg 2) (.const 1))) s₃ s₄ 4 :=
      .assign (by
        simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hr2_s₃, hk_w, hw,
          show k + 1 < 2 ^ w by omega])
    have hout₄ : s₄.arrs outArr =
        (pref ++ mid.take (k + 1)) ++ List.replicate (cap - (pref.length + (k + 1))) 0 := by
      change (s.arrs outArr).set (pref.length + k) val = _
      rw [hout]
      have hlen_pt : (pref ++ mid.take k).length = pref.length + k := by
        rw [List.length_append, List.length_take]; omega
      rw [List.set_append_right _ _ (by omega)]
      have hsub0 : pref.length + k - (pref ++ mid.take k).length = 0 := by omega
      have hrep : cap - (pref.length + k) = (cap - (pref.length + (k + 1))) + 1 := by omega
      rw [hsub0, hrep, List.replicate_succ, List.set_cons_zero]
      dsimp [val]
      rw [take_add_one_eq_append_getElem mid k hk_mid]
      simp only [List.append_assoc, List.singleton_append]
    rcases ih (k + 1) (by omega)
        (by simp [s₄, s₃, s₂, s₁, hne_src, hsrc])
        hout₄
        (by simp [s₄, s₃, s₂, s₁, State.setReg, hne_len2, hne_len3, hne_len25, hrlen])
        (by simp [s₄])
        (by simp [s₄, s₃, State.setReg, Nat.add_assoc]) with
      ⟨s₅, t₅, hex₅, ht₅, hout₅, hr25₅, harr₅, hreg₅⟩
    refine ⟨s₅, 3 + ((3 + (3 + 4)) + 4) + t₅,
      .while_true hcond (by omega) (.seq (.seq hex₁ (.seq hex₂ hex₃)) hex_inc) hex₅,
      by omega, hout₅, hr25₅,
      fun a ha => by rw [harr₅ a ha]; simp [s₄, s₃, s₂, s₁, ha],
      fun r h2 h3 h25 => by
        rw [hreg₅ r h2 h3 h25]
        simp [s₄, s₃, s₂, s₁, State.setReg, h2, h3, h25]⟩

theorem appendSliceToOutProg_exec {w len cap : ℕ} (a_src : Arr) (r_len : Reg)
    (hne_src : a_src ≠ outArr)
    (hne_len2 : r_len ≠ 2) (hne_len3 : r_len ≠ 3) (hne_len25 : r_len ≠ 25)
    (pref mid extra : List ℕ)
    (hmid_len : mid.length = len)
    (hmid_w : ∀ v ∈ mid, v < 2 ^ w)
    (hcap_le : pref.length + len ≤ cap)
    (hw : 1 < 2 ^ w) (hcap_w : cap < 2 ^ w) {s : State}
    (hsrc : s.arrs a_src = mid ++ extra)
    (hout : s.arrs outArr = pref ++ List.replicate (cap - pref.length) 0)
    (hrlen : s.regs r_len = len)
    (hr25 : s.regs 25 = pref.length) :
    ∃ s' t,
      Exec w (appendSliceToOutProg a_src r_len) s s' t ∧
      t ≤ 17 * len + 5 ∧
      s'.arrs outArr = (pref ++ mid) ++ List.replicate (cap - (pref.length + len)) 0 ∧
      s'.regs 25 = pref.length + len ∧
      (∀ a : Arr, a ≠ outArr → s'.arrs a = s.arrs a) ∧
      (∀ r : Reg, r ≠ 2 → r ≠ 3 → r ≠ 25 → s'.regs r = s.regs r) := by
  have h0_w : 0 < 2 ^ w := by omega
  let s₁ := s.setReg 2 0
  have hex₁ : Exec w (.assign 2 (.const 0)) s s₁ 2 :=
    .assign (by simp [Expr.eval, checkWord, h0_w])
  rcases appendSliceToOutLoop_exec a_src r_len hne_src hne_len2 hne_len3 hne_len25
      pref mid extra hmid_len hmid_w hcap_le hw hcap_w len 0 (by omega) (s := s₁)
      hsrc
      (by simpa [s₁] using hout)
      (by simp [s₁, State.setReg, hne_len2, hrlen])
      (by simp [s₁])
      (by simp [s₁, State.setReg, hr25]) with
    ⟨s₂, t₂, hex₂, ht₂, hout₂, hr25₂, harr₂, hreg₂⟩
  refine ⟨s₂, 2 + t₂, .seq hex₁ hex₂, by omega, hout₂, hr25₂,
    fun a ha => by rw [harr₂ a ha]; rfl,
    fun r h2 h3 h25 => by
      rw [hreg₂ r h2 h3 h25]
      simp [s₁, State.setReg, h2]⟩

/-- Program that appends `encAlg86Subgraph V edges` to `outArr` at `r_25` and increments the
subgraph counter `r_26`, where `a_18` holds `bitSetList V` (`r_14 = n`) and `a_17` begins with
`[n, edges.length] ++ flatEdges edges` (`r_22 = edges.length`). -/
def appendSubgraphToOutProg : Cmd :=
  .seq (appendSliceToOutProg 18 14)
    (.seq (.assign 21 (.op .add (.const 2) (.op .mul (.const 2) (.reg 22))))
      (.seq (appendSliceToOutProg 17 21)
        (.assign 26 (.op .add (.reg 26) (.const 1)))))

theorem appendSubgraphToOutProg_exec {w n cap cnt : ℕ}
    (V : Finset (Fin n)) (edges : List (Fin n × Fin n))
    (pref extra17 : List ℕ)
    (hcap_le : pref.length + (n + 2 + 2 * edges.length) ≤ cap)
    (hw2 : 2 < 2 ^ w) (hcap_w : cap < 2 ^ w) (hcnt_w : cnt + 1 < 2 ^ w) {s : State}
    (hV : IsBitSet V 18 s)
    (h17 : s.arrs 17 = ([n, edges.length] ++ flatEdges edges) ++ extra17)
    (hout : s.arrs outArr = pref ++ List.replicate (cap - pref.length) 0)
    (hr14 : s.regs 14 = n)
    (hr22 : s.regs 22 = edges.length)
    (hr25 : s.regs 25 = pref.length)
    (hr26 : s.regs 26 = cnt) :
    ∃ s' t,
      Exec w appendSubgraphToOutProg s s' t ∧
      t ≤ 17 * n + 34 * edges.length + 55 ∧
      s'.arrs outArr =
        (pref ++ encAlg86Subgraph V edges) ++
          List.replicate (cap - (pref ++ encAlg86Subgraph V edges).length) 0 ∧
      s'.regs 25 = (pref ++ encAlg86Subgraph V edges).length ∧
      s'.regs 26 = cnt + 1 ∧
      (∀ a : Arr, a ≠ outArr → s'.arrs a = s.arrs a) ∧
      (∀ r : Reg, r ≠ 2 → r ≠ 3 → r ≠ 21 → r ≠ 25 → r ≠ 26 → s'.regs r = s.regs r) := by
  have hw : 1 < 2 ^ w := by omega
  have hn_w : n < 2 ^ w := by omega
  have hm_w : edges.length < 2 ^ w := by omega
  have h2m_w : 2 * edges.length < 2 ^ w := by omega
  have h22m_w : 2 + 2 * edges.length < 2 ^ w := by omega
  have hV_arr : s.arrs 18 = bitSetList V ++ [] := by
    rw [List.append_nil]
    exact hV.arr_eq_bitSetList
  have hV_w : ∀ v ∈ bitSetList V, v < 2 ^ w := by
    intro v hv
    rcases List.mem_iff_getElem.mp hv with ⟨idx, hidx, rfl⟩
    have hle1 := getElem_bitSetList_le_one V idx hidx
    omega
  -- 1. appendSliceToOutProg 18 14
  rcases appendSliceToOutProg_exec (w := w) (len := n) (cap := cap) 18 14
      (by decide) (by decide) (by decide) (by decide)
      pref (bitSetList V) [] (length_bitSetList V) hV_w (by omega) hw hcap_w
      hV_arr hout hr14 hr25 with
    ⟨s₁, t₁, hex₁, ht₁, hout₁, hr25₁, harr₁, hreg₁⟩
  -- 2. r_21 := 2 + 2 * r_22
  have hr22_₁ : s₁.regs 22 = edges.length := by
    rw [hreg₁ 22 (by decide) (by decide) (by decide), hr22]
  let s₂ := s₁.setReg 21 (2 + 2 * edges.length)
  have hex₂ : Exec w (.assign 21 (.op .add (.const 2) (.op .mul (.const 2) (.reg 22)))) s₁ s₂ 6 :=
    .assign (by simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hr22_₁, hw2, hm_w, h2m_w, h22m_w])
  -- 3. appendSliceToOutProg 17 21
  have h17_₂ : s₂.arrs 17 = ([n, edges.length] ++ flatEdges edges) ++ extra17 := by
    change s₁.arrs 17 = _
    rw [harr₁ 17 (by decide), h17]
  have hout₂ : s₂.arrs outArr =
      (pref ++ bitSetList V) ++ List.replicate (cap - (pref ++ bitSetList V).length) 0 := by
    have hlen_pv : (pref ++ bitSetList V).length = pref.length + n := by
      rw [List.length_append, length_bitSetList]
    simpa [s₂, hlen_pv] using hout₁
  have hr25_₂ : s₂.regs 25 = (pref ++ bitSetList V).length := by
    simp [s₂, State.setReg, hr25₁, length_bitSetList]
  have henc_w : ∀ v ∈ [n, edges.length] ++ flatEdges edges, v < 2 ^ w := by
    intro v hv
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hv
    rcases hv with (rfl | rfl) | hv_flat
    · exact hn_w
    · exact hm_w
    · exact Nat.lt_trans (mem_flatEdges_lt edges v hv_flat) hn_w
  rcases appendSliceToOutProg_exec (w := w) (len := 2 + 2 * edges.length) (cap := cap) 17 21
      (by decide) (by decide) (by decide) (by decide)
      (pref ++ bitSetList V) ([n, edges.length] ++ flatEdges edges) extra17
      (by simp [length_flatEdges]; omega) henc_w
      (by rw [List.length_append, length_bitSetList]; omega) hw hcap_w (s := s₂)
      h17_₂ hout₂ (by simp [s₂]) hr25_₂ with
    ⟨s₃, t₃, hex₃, ht₃, hout₃, hr25₃, harr₃, hreg₃⟩
  -- 4. r_26 := r_26 + 1
  have hr26_₃ : s₃.regs 26 = cnt := by
    rw [hreg₃ 26 (by decide) (by decide) (by decide)]
    simp [s₂, State.setReg, hreg₁ 26 (by decide) (by decide) (by decide), hr26]
  have hcnt0_w : cnt < 2 ^ w := by omega
  let s₄ := s₃.setReg 26 (cnt + 1)
  have hex₄ : Exec w (.assign 26 (.op .add (.reg 26) (.const 1))) s₃ s₄ 4 :=
    .assign (by simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hr26_₃, hcnt0_w, hw, hcnt_w])
  have henc_eq : (pref ++ bitSetList V) ++ ([n, edges.length] ++ flatEdges edges) =
      pref ++ encAlg86Subgraph V edges := by
    simp [encAlg86Subgraph, List.append_assoc]
  have hlen_enc : (pref ++ bitSetList V).length + (2 + 2 * edges.length) =
      (pref ++ encAlg86Subgraph V edges).length := by
    rw [List.length_append, List.length_append, length_bitSetList, length_encAlg86Subgraph]
    omega
  refine ⟨s₄, t₁ + (6 + (t₃ + 4)),
    .seq hex₁ (.seq hex₂ (.seq hex₃ hex₄)),
    by omega,
    by change s₃.arrs outArr = _; rw [hout₃, henc_eq, hlen_enc],
    by rw [← hlen_enc]; exact hr25₃,
    by simp [s₄],
    fun a ha => by
      change s₃.arrs a = s.arrs a
      rw [harr₃ a ha]
      exact harr₁ a ha,
    fun r h2 h3 h21 h25 h26 => by
      change (s₃.setReg 26 (cnt + 1)).regs r = s.regs r
      rw [State.setReg_regs_ne _ _ h26, hreg₃ r h2 h3 h25]
      change (s₁.setReg 21 (2 + 2 * edges.length)).regs r = s.regs r
      rw [State.setReg_regs_ne _ _ h21]
      exact hreg₁ r h2 h3 h25⟩

/-! ### Section 3: Union of Two BitSets (`alg86UnionBitSetProg`) -/

/-- Loop body of `alg86UnionBitSetProg`: reads `a_12[r_2]` and `a_13[r_2]`; if their sum is non-zero,
writes `1` to `a_18[r_2]`. -/
def alg86UnionBitSetBody : Cmd :=
  .seq (.assign 3 (.read 12 (.reg 2)))
    (.seq (.assign 4 (.read 13 (.reg 2)))
      (.ite (.op .add (.reg 3) (.reg 4))
        (.write 18 (.reg 2) (.const 1))
        .skip))

/-- Allocates `a_18` of size `r_14 = n` and computes `IsBitSet (U ∪ X) 18` from
`IsBitSet U 12` and `IsBitSet X 13`. -/
def alg86UnionBitSetProg : Cmd :=
  .seq (.alloc 18 (.reg 14))
    (.seq (.assign 2 (.const 0))
      (forUp 2 (.reg 14) alg86UnionBitSetBody))

theorem alg86UnionBitSetLoop_exec {w n : ℕ} (U X : Finset (Fin n))
    (hw2 : 2 < 2 ^ w) (hn_w : n < 2 ^ w)
    (rem k : ℕ) (hrem : k + rem = n) {s : State}
    (hU : IsBitSet U 12 s) (hX : IsBitSet X 13 s)
    (hr14 : s.regs 14 = n) (hr2 : s.regs 2 = k)
    (h18 : s.arrs 18 = (bitSetList (U ∪ X)).take k ++ List.replicate (n - k) 0) :
    ∃ s' t,
      Exec w (forUp 2 (.reg 14) alg86UnionBitSetBody) s s' t ∧
      t ≤ 3 + 21 * rem ∧
      IsBitSet (U ∪ X) 18 s' ∧
      (∀ a : Arr, a ≠ 18 → s'.arrs a = s.arrs a) ∧
      (∀ r : Reg, r ≠ 2 → r ≠ 3 → r ≠ 4 → s'.regs r = s.regs r) := by
  have h0_w : 0 < 2 ^ w := by omega
  have hw : 1 < 2 ^ w := by omega
  induction rem generalizing k s with
  | zero =>
    have hk_eq : k = n := by omega
    subst hk_eq
    have hcond : (Expr.op .lt (.reg 2) (.reg 14)).eval w s = some 0 := by
      simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hr2, hr14, hn_w]
    have htake : (bitSetList (U ∪ X)).take k = bitSetList (U ∪ X) :=
      List.take_of_length_le (by simp)
    rw [htake, Nat.sub_self, List.replicate_zero, List.append_nil] at h18
    exact ⟨s, 3, .while_false hcond, by omega,
      IsBitSet.of_bitSetList (U ∪ X) 18 s h18,
      fun _ _ => rfl, fun _ _ _ _ => rfl⟩
  | succ rem ih =>
    have hk_lt : k < n := by omega
    have hk_w : k < 2 ^ w := by omega
    let uk : Fin n := ⟨k, hk_lt⟩
    have hcond : (Expr.op .lt (.reg 2) (.reg 14)).eval w s = some 1 := by
      simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hr2, hr14, hk_w, hn_w, hk_lt, hw]
    have hk_U : k < (s.arrs 12).length := by rw [hU.1]; exact hk_lt
    let bU := (s.arrs 12)[k]'hk_U
    have hbU_eq : bU = if uk ∈ U then 1 else 0 := hU.getElem_eq_ite uk
    have hbU_w : bU < 2 ^ w := by rw [hbU_eq]; split_ifs <;> omega
    let s₁ := s.setReg 3 bU
    have hex₁ : Exec w (.assign 3 (.read 12 (.reg 2))) s s₁ 3 :=
      .assign (by simp [Expr.eval, checkWord, hr2, hk_w, hk_U, bU, hbU_w])
    have hk_X : k < (s.arrs 13).length := by rw [hX.1]; exact hk_lt
    let bX := (s.arrs 13)[k]'hk_X
    have hbX_eq : bX = if uk ∈ X then 1 else 0 := hX.getElem_eq_ite uk
    have hbX_w : bX < 2 ^ w := by rw [hbX_eq]; split_ifs <;> omega
    let s₂ := s₁.setReg 4 bX
    have hex₂ : Exec w (.assign 4 (.read 13 (.reg 2))) s₁ s₂ 3 :=
      .assign (by simp [s₁, State.setReg, Expr.eval, checkWord, hr2, hk_w, hk_X, bX, hbX_w])
    have hsum_w : bU + bX < 2 ^ w := by rw [hbU_eq, hbX_eq]; split_ifs <;> omega
    have hstep : ∃ s₃ t_b,
        Exec w (.ite (.op .add (.reg 3) (.reg 4)) (.write 18 (.reg 2) (.const 1)) .skip) s₂ s₃ t_b ∧
        t_b ≤ 6 ∧
        s₃.regs 2 = k ∧
        s₃.arrs 18 = (bitSetList (U ∪ X)).take (k + 1) ++ List.replicate (n - (k + 1)) 0 ∧
        (∀ a : Arr, a ≠ 18 → s₃.arrs a = s.arrs a) ∧
        (∀ r : Reg, r ≠ 3 → r ≠ 4 → s₃.regs r = s.regs r) := by
      by_cases huk_UX : uk ∈ U ∪ X
      · have hsum_pos : bU + bX ≠ 0 := by
          rw [hbU_eq, hbX_eq]
          rcases Finset.mem_union.mp huk_UX with hu | hx
          · simp [hu]
          · simp [hx]
        have hcond_add : (Expr.op .add (.reg 3) (.reg 4)).eval w s₂ = some (bU + bX) := by
          simp [s₂, s₁, State.setReg, Expr.eval, BinOp.eval, BinOp.raw, checkWord,
            hbU_w, hbX_w, hsum_w]
        have h18_len : k < (s₂.arrs 18).length := by
          simp [s₂, s₁, h18, length_bitSetList]; omega
        let s₃ := s₂.writeArr 18 k 1
        have hex_w : Exec w (.write 18 (.reg 2) (.const 1)) s₂ s₃ 3 :=
          .write (by simp [s₂, s₁, State.setReg, Expr.eval, checkWord, hr2, hk_w])
            (by simp [Expr.eval, checkWord, hw])
            h18_len
        have h18_s₃ : s₃.arrs 18 =
            (bitSetList (U ∪ X)).take (k + 1) ++ List.replicate (n - (k + 1)) 0 := by
          change (s.arrs 18).set k 1 = _
          rw [h18]
          have hlen_t : ((bitSetList (U ∪ X)).take k).length = k := by
            rw [List.length_take, length_bitSetList]; omega
          rw [List.set_append_right _ _ (by omega)]
          have hsub0 : k - ((bitSetList (U ∪ X)).take k).length = 0 := by omega
          have hrep : n - k = (n - (k + 1)) + 1 := by omega
          rw [hsub0, hrep, List.replicate_succ, List.set_cons_zero]
          have hbit1 : (bitSetList (U ∪ X))[k]'(by simp [hk_lt]) = 1 := by
            rw [getElem_bitSetList (U ∪ X) k hk_lt]
            simp [uk, huk_UX]
          rw [take_add_one_eq_append_getElem (bitSetList (U ∪ X)) k (by simp [hk_lt]), hbit1]
          simp [List.append_assoc]
        exact ⟨s₃, 3 + 3, .ite_true hcond_add hsum_pos hex_w, by omega, hr2, h18_s₃,
          fun a ha => by simp [s₃, s₂, s₁, ha],
          fun r h3 h4 => by simp [s₃, s₂, s₁, State.setReg, h3, h4]⟩
      · have hsum0 : bU + bX = 0 := by
          rw [hbU_eq, hbX_eq]
          rw [Finset.mem_union, not_or] at huk_UX
          simp [huk_UX.1, huk_UX.2]
        have hcond_add : (Expr.op .add (.reg 3) (.reg 4)).eval w s₂ = some 0 := by
          simp [s₂, s₁, State.setReg, Expr.eval, BinOp.eval, BinOp.raw, checkWord,
            hbU_w, hbX_w, hsum0, h0_w]
        have h18_s₂ : s₂.arrs 18 =
            (bitSetList (U ∪ X)).take (k + 1) ++ List.replicate (n - (k + 1)) 0 := by
          change s.arrs 18 = _
          rw [h18]
          have hrep : n - k = 1 + (n - (k + 1)) := by omega
          rw [hrep, List.replicate_add, List.replicate_one]
          have hbit0 : (bitSetList (U ∪ X))[k]'(by simp [hk_lt]) = 0 := by
            rw [getElem_bitSetList (U ∪ X) k hk_lt]
            simp [uk, huk_UX]
          rw [take_add_one_eq_append_getElem (bitSetList (U ∪ X)) k (by simp [hk_lt]), hbit0]
          simp [List.append_assoc]
        exact ⟨s₂, 3 + 1, .ite_false hcond_add (.skip s₂), by omega, hr2, h18_s₂,
          fun _ _ => rfl,
          fun r h3 h4 => by simp [s₂, s₁, State.setReg, h3, h4]⟩
    rcases hstep with ⟨s₃, t_b, hex_b, ht_b, hr2₃, h18₃, harr₃, hreg₃⟩
    let s₄ := s₃.setReg 2 (k + 1)
    have hex_inc : Exec w (.assign 2 (.op .add (.reg 2) (.const 1))) s₃ s₄ 4 :=
      .assign (by
        simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hr2₃, hk_w, hw,
          show k + 1 < 2 ^ w by omega])
    rcases ih (k + 1) (by omega) (s := s₄)
        (hU.of_arr_eq (harr₃ 12 (by decide)))
        (hX.of_arr_eq (harr₃ 13 (by decide)))
        (by
          change (s₃.setReg 2 (k + 1)).regs 14 = n
          rw [State.setReg_regs_ne _ _ (by decide), hreg₃ 14 (by decide) (by decide), hr14])
        rfl
        h18₃ with
      ⟨s₅, t₅, hex₅, ht₅, hUX₅, harr₅, hreg₅⟩
    refine ⟨s₅, 3 + ((3 + (3 + t_b)) + 4) + t₅,
      .while_true hcond (by omega) (.seq (.seq hex₁ (.seq hex₂ hex_b)) hex_inc) hex₅,
      by omega, hUX₅,
      fun a ha => by rw [harr₅ a ha]; exact harr₃ a ha,
      fun r h2 h3 h4 => by
        rw [hreg₅ r h2 h3 h4]
        change (s₃.setReg 2 (k + 1)).regs r = s.regs r
        rw [State.setReg_regs_ne _ _ h2]
        exact hreg₃ r h3 h4⟩

theorem alg86UnionBitSetProg_exec {w n : ℕ} (U X : Finset (Fin n))
    (hw2 : 2 < 2 ^ w) (hn_w : n < 2 ^ w) {s : State}
    (hU : IsBitSet U 12 s) (hX : IsBitSet X 13 s)
    (hr14 : s.regs 14 = n) :
    ∃ s' t,
      Exec w alg86UnionBitSetProg s s' t ∧
      t ≤ 22 * n + 8 ∧
      IsBitSet (U ∪ X) 18 s' ∧
      (∀ a : Arr, a ≠ 18 → s'.arrs a = s.arrs a) ∧
      (∀ r : Reg, r ≠ 2 → r ≠ 3 → r ≠ 4 → s'.regs r = s.regs r) := by
  have h0_w : 0 < 2 ^ w := by omega
  let s₁ := s.setArr 18 (List.replicate n 0)
  have hex₁ : Exec w (.alloc 18 (.reg 14)) s s₁ (1 + n) :=
    .alloc (by simp [Expr.eval, checkWord, hr14, hn_w])
  let s₂ := s₁.setReg 2 0
  have hex₂ : Exec w (.assign 2 (.const 0)) s₁ s₂ 2 :=
    .assign (by simp [Expr.eval, checkWord, h0_w])
  rcases alg86UnionBitSetLoop_exec U X hw2 hn_w n 0 (by omega) (s := s₂)
      (hU.of_arr_eq rfl) (hX.of_arr_eq rfl) hr14 rfl
      (by simp [s₂, s₁]) with
    ⟨s₃, t₃, hex₃, ht₃, hUX₃, harr₃, hreg₃⟩
  refine ⟨s₃, (1 + n) + (2 + t₃), .seq hex₁ (.seq hex₂ hex₃), by omega, hUX₃,
    fun a ha => by rw [harr₃ a ha]; simp [s₂, s₁, ha],
    fun r h2 h3 h4 => by
      rw [hreg₃ r h2 h3 h4]
      simp [s₂, s₁, State.setReg, h2]⟩

/-! ### Section 4: Filtering Subgraph Edges (`filterSubgraphEdgesProg`), `emitUXSubgraphProg`, and `markXEdgesProg` -/

/-- Predicate for whether an edge `e = (u, v)` is kept in the subgraph on `(U, X)` with flag `incX`:
either an endpoint lies in `U`, or `incX = true` and both endpoints lie in `X`. -/
def alg86KeepEdge {n : ℕ} (U X : Finset (Fin n)) (incX : Bool) (e : Fin n × Fin n) : Bool :=
  decide ((e.1 ∈ U ∨ e.2 ∈ U) ∨ (incX = true ∧ e.1 ∈ X ∧ e.2 ∈ X))

/-- Loop body of `filterSubgraphEdgesProg`: reads the `r_2`-th edge `(u, v)` from `inArr = 0`,
checks `alg86KeepEdge U X incX (u, v)` using `a_12` (`U`), `a_13` (`X`), and `r_28` (`incX`),
and if kept, appends `(u, v)` to `a_17` via `appendEdgeTo17Prog 3 4`. -/
def filterSubgraphEdgesBody : Cmd :=
  .seq (.assign 3 (.read 0 (.op .add (.const 2) (.op .mul (.const 2) (.reg 2)))))
    (.seq (.assign 4 (.read 0 (.op .add (.const 3) (.op .mul (.const 2) (.reg 2)))))
      (.seq (.assign 5 (.read 12 (.reg 3)))
        (.seq (.assign 6 (.read 12 (.reg 4)))
          (.seq (.assign 7 (.read 13 (.reg 3)))
            (.seq (.assign 8 (.read 13 (.reg 4)))
              (.seq (.assign 9 (.op .add (.op .add (.reg 5) (.reg 6))
                  (.op .mul (.reg 28) (.op .mul (.reg 7) (.reg 8)))))
                (.ite (.reg 9)
                  (appendEdgeTo17Prog 3 4)
                  .skip)))))))

/-- Filters `edges` from `inArr = 0` by `alg86KeepEdge U X incX` into `a_17` and writes the header
`[n, L₁.length]` at indices `0` and `1` of `a_17`. -/
def filterSubgraphEdgesProg : Cmd :=
  .seq (.alloc 17 (.op .add (.const 8) (.op .mul (.const 2) (.reg 1))))
    (.seq (.assign 22 (.const 0))
      (.seq (.assign 2 (.const 0))
        (.seq (forUp 2 (.reg 1) filterSubgraphEdgesBody)
          (.seq (.write 17 (.const 0) (.reg 14))
            (.write 17 (.const 1) (.reg 22))))))

theorem filterSubgraphEdgesLoop_exec {w n : ℕ} (U X : Finset (Fin n)) (incX : Bool)
    (edges : List (Fin n × Fin n))
    (hw3 : 3 < 2 ^ w) (hn_w : n < 2 ^ w) (hm8_w : 8 + 2 * edges.length < 2 ^ w)
    (rem k : ℕ) (hrem : k + rem = edges.length) {s : State}
    (hin : s.arrs 0 = [n, edges.length] ++ flatEdges edges)
    (hU : IsBitSet U 12 s) (hX : IsBitSet X 13 s)
    (hrm : s.regs 1 = edges.length) (hrk : s.regs 2 = k)
    (hr28 : s.regs 28 = if incX then 1 else 0)
    (hr22 : s.regs 22 = ((edges.take k).filter (alg86KeepEdge U X incX)).length)
    (hnew : s.arrs 17 =
      ([0, 0] ++ flatEdges ((edges.take k).filter (alg86KeepEdge U X incX))) ++
        List.replicate (6 + 2 * (edges.length - ((edges.take k).filter (alg86KeepEdge U X incX)).length)) 0) :
    let L₁ := edges.filter (alg86KeepEdge U X incX)
    ∃ s' t,
      Exec w (forUp 2 (.reg 1) filterSubgraphEdgesBody) s s' t ∧
      t ≤ 3 + 62 * rem ∧
      s'.regs 22 = L₁.length ∧
      s'.arrs 17 = ([0, 0] ++ flatEdges L₁) ++
        List.replicate (6 + 2 * (edges.length - L₁.length)) 0 ∧
      (∀ a : Arr, a ≠ 17 → s'.arrs a = s.arrs a) ∧
      (∀ r : Reg, r ≠ 2 → r ≠ 3 → r ≠ 4 → r ≠ 5 → r ≠ 6 → r ≠ 7 → r ≠ 8 → r ≠ 9 → r ≠ 22 →
        s'.regs r = s.regs r) := by
  intro L₁
  have h0_w : 0 < 2 ^ w := by omega
  have hw : 1 < 2 ^ w := by omega
  have hw2 : 2 < 2 ^ w := by omega
  have hm_w : edges.length < 2 ^ w := by omega
  induction rem generalizing k s with
  | zero =>
    have hk_eq : k = edges.length := by omega
    subst hk_eq
    have hcond : (Expr.op .lt (.reg 2) (.reg 1)).eval w s = some 0 := by
      simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hrk, hrm, hm_w]
    have htake : edges.take edges.length = edges := List.take_of_length_le (by simp)
    rw [htake] at hr22 hnew
    exact ⟨s, 3, .while_false hcond, by omega, hr22, hnew,
      fun _ _ => rfl, fun _ _ _ _ _ _ _ _ _ _ => rfl⟩
  | succ rem ih =>
    have hk_lt : k < edges.length := by omega
    have hk_w : k < 2 ^ w := by omega
    have h2k_w : 2 * k < 2 ^ w := by omega
    have h2k2_w : 2 + 2 * k < 2 ^ w := by omega
    have h2k3_w : 3 + 2 * k < 2 ^ w := by omega
    let e := edges[k]'hk_lt
    let u := e.1
    let v := e.2
    let L_k := (edges.take k).filter (alg86KeepEdge U X incX)
    let L_next := (edges.take (k + 1)).filter (alg86KeepEdge U X incX)
    have hL_k_le : L_k.length ≤ k := by
      calc
        L_k.length ≤ (edges.take k).length := List.length_filter_le _ _
        _ = k := by rw [List.length_take]; omega
    have htake_succ : edges.take (k + 1) = edges.take k ++ [e] :=
      take_add_one_eq_append_getElem edges k hk_lt
    have hcond : (Expr.op .lt (.reg 2) (.reg 1)).eval w s = some 1 := by
      simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hrk, hrm, hk_w, hm_w, hk_lt, hw]
    have hin_u_lt : 2 + 2 * k < (s.arrs 0).length := by
      rw [hin]; simp [length_flatEdges]; omega
    have hin_u_get : (s.arrs 0)[2 + 2 * k]'hin_u_lt = u.1 := by
      have hidx : 2 + 2 * k = (2 * k) + 1 + 1 := by omega
      simp only [hin, hidx, List.cons_append, List.nil_append, List.getElem_cons_succ]
      exact getElem_flatEdges_even edges hk_lt
    have hin_v_lt : 3 + 2 * k < (s.arrs 0).length := by
      rw [hin]; simp [length_flatEdges]; omega
    have hin_v_get : (s.arrs 0)[3 + 2 * k]'hin_v_lt = v.1 := by
      have hidx : 3 + 2 * k = (2 * k + 1) + 1 + 1 := by omega
      simp only [hin, hidx, List.cons_append, List.nil_append, List.getElem_cons_succ]
      exact getElem_flatEdges_odd edges hk_lt
    have hu_w : u.1 < 2 ^ w := Nat.lt_trans u.2 hn_w
    have hv_w : v.1 < 2 ^ w := Nat.lt_trans v.2 hn_w
    let s₁ := s.setReg 3 u.1
    have hex₁ : Exec w (.assign 3 (.read 0 (.op .add (.const 2) (.op .mul (.const 2) (.reg 2))))) s s₁ 7 :=
      .assign (by
        simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hrk, hw2, hk_w, h2k_w, h2k2_w,
          hin_u_lt, hin_u_get, hu_w])
    let s₂ := s₁.setReg 4 v.1
    have hex₂ : Exec w (.assign 4 (.read 0 (.op .add (.const 3) (.op .mul (.const 2) (.reg 2))))) s₁ s₂ 7 :=
      .assign (by
        simp [s₁, State.setReg, Expr.eval, BinOp.eval, BinOp.raw, checkWord, hrk, hw2, hw3,
          hk_w, h2k_w, h2k3_w, hin_v_lt, hin_v_get, hv_w])
    have hu_U_lt : u.1 < (s.arrs 12).length := by rw [hU.1]; exact u.2
    let b_u := (s.arrs 12)[u.1]'hu_U_lt
    have hbu_eq : b_u = if u ∈ U then 1 else 0 := hU.getElem_eq_ite u
    have hbu_w : b_u < 2 ^ w := by rw [hbu_eq]; split_ifs <;> omega
    let s₃ := s₂.setReg 5 b_u
    have hex₃ : Exec w (.assign 5 (.read 12 (.reg 3))) s₂ s₃ 3 :=
      .assign (by simp [s₂, s₁, State.setReg, Expr.eval, checkWord, hu_w, hu_U_lt, b_u, hbu_w])
    have hv_U_lt : v.1 < (s.arrs 12).length := by rw [hU.1]; exact v.2
    let b_v := (s.arrs 12)[v.1]'hv_U_lt
    have hbv_eq : b_v = if v ∈ U then 1 else 0 := hU.getElem_eq_ite v
    have hbv_w : b_v < 2 ^ w := by rw [hbv_eq]; split_ifs <;> omega
    let s₄ := s₃.setReg 6 b_v
    have hex₄ : Exec w (.assign 6 (.read 12 (.reg 4))) s₃ s₄ 3 :=
      .assign (by simp [s₃, s₂, s₁, State.setReg, Expr.eval, checkWord, hv_w, hv_U_lt, b_v, hbv_w])
    have hu_X_lt : u.1 < (s.arrs 13).length := by rw [hX.1]; exact u.2
    let xb_u := (s.arrs 13)[u.1]'hu_X_lt
    have hxbu_eq : xb_u = if u ∈ X then 1 else 0 := hX.getElem_eq_ite u
    have hxbu_w : xb_u < 2 ^ w := by rw [hxbu_eq]; split_ifs <;> omega
    let s₅ := s₄.setReg 7 xb_u
    have hex₅ : Exec w (.assign 7 (.read 13 (.reg 3))) s₄ s₅ 3 :=
      .assign (by simp [s₄, s₃, s₂, s₁, State.setReg, Expr.eval, checkWord, hu_w, hu_X_lt, xb_u, hxbu_w])
    have hv_X_lt : v.1 < (s.arrs 13).length := by rw [hX.1]; exact v.2
    let xb_v := (s.arrs 13)[v.1]'hv_X_lt
    have hxbv_eq : xb_v = if v ∈ X then 1 else 0 := hX.getElem_eq_ite v
    have hxbv_w : xb_v < 2 ^ w := by rw [hxbv_eq]; split_ifs <;> omega
    let s₆ := s₅.setReg 8 xb_v
    have hex₆ : Exec w (.assign 8 (.read 13 (.reg 4))) s₅ s₆ 3 :=
      .assign (by simp [s₅, s₄, s₃, s₂, s₁, State.setReg, Expr.eval, checkWord, hv_w, hv_X_lt, xb_v, hxbv_w])
    let b_inc := s.regs 28
    let flag := (b_u + b_v) + b_inc * (xb_u * xb_v)
    have hflag_iff : flag ≠ 0 ↔ alg86KeepEdge U X incX e = true := by
      dsimp [flag, b_inc, alg86KeepEdge]
      rw [hr28, hbu_eq, hbv_eq, hxbu_eq, hxbv_eq]
      cases incX <;>
        by_cases h1 : u ∈ U <;> by_cases h2 : v ∈ U <;>
        by_cases h3 : u ∈ X <;> by_cases h4 : v ∈ X <;>
        simp [e, u, v, h1, h2, h3, h4]
    have hbu_bv_w : b_u + b_v < 2 ^ w := by rw [hbu_eq, hbv_eq]; split_ifs <;> omega
    have hxb_w : xb_u * xb_v < 2 ^ w := by rw [hxbu_eq, hxbv_eq]; split_ifs <;> omega
    have hbinc_w : b_inc < 2 ^ w := by dsimp [b_inc]; rw [hr28]; split_ifs <;> omega
    have hmul_w : b_inc * (xb_u * xb_v) < 2 ^ w := by
      dsimp [b_inc]; rw [hr28, hxbu_eq, hxbv_eq]; split_ifs <;> omega
    have hflag_w : flag < 2 ^ w := by
      dsimp [flag, b_inc]; rw [hr28, hbu_eq, hbv_eq, hxbu_eq, hxbv_eq]; split_ifs <;> omega
    let s₇ := s₆.setReg 9 flag
    have hex₇ : Exec w (.assign 9 (.op .add (.op .add (.reg 5) (.reg 6))
        (.op .mul (.reg 28) (.op .mul (.reg 7) (.reg 8))))) s₆ s₇ 10 :=
      .assign (by
        simp [s₆, s₅, s₄, s₃, s₂, s₁, State.setReg, Expr.eval, BinOp.eval, BinOp.raw, checkWord,
          b_inc, hbu_w, hbv_w, hxbu_w, hxbv_w, hbu_bv_w, hxb_w, hbinc_w, hmul_w, flag, hflag_w])
    have hstep : ∃ s₈ t_b,
        Exec w (.ite (.reg 9) (appendEdgeTo17Prog 3 4) .skip) s₇ s₈ t_b ∧
        t_b ≤ 19 ∧
        s₈.regs 2 = k ∧
        s₈.regs 22 = L_next.length ∧
        s₈.arrs 17 = ([0, 0] ++ flatEdges L_next) ++
          List.replicate (6 + 2 * (edges.length - L_next.length)) 0 ∧
        (∀ a : Arr, a ≠ 17 → s₈.arrs a = s.arrs a) ∧
        (∀ r : Reg, r ≠ 2 → r ≠ 3 → r ≠ 4 → r ≠ 5 → r ≠ 6 → r ≠ 7 → r ≠ 8 → r ≠ 9 → r ≠ 22 →
          s₈.regs r = s.regs r) := by
      by_cases hkeep : alg86KeepEdge U X incX e = true
      · have hflag_ne : flag ≠ 0 := hflag_iff.mpr hkeep
        have hcond9 : (Expr.reg 9).eval w s₇ = some flag := by
          simp [s₇, State.setReg, Expr.eval, checkWord, hflag_w]
        have hL_next_eq : L_next = L_k ++ [e] := by
          dsimp [L_next, L_k]
          rw [htake_succ, List.filter_append, List.filter_cons_of_pos hkeep, List.filter_nil]
        have hrem_rep : 6 + 2 * (edges.length - L_k.length) =
            2 + (6 + 2 * (edges.length - (L_k.length + 1))) := by omega
        have hnew₇ : s₇.arrs 17 = ([0, 0] ++ flatEdges L_k) ++
            List.replicate (2 + (6 + 2 * (edges.length - (L_k.length + 1)))) 0 := by
          change s.arrs 17 = _
          rw [hnew, hrem_rep]
        rcases appendEdgeTo17Prog_exec L_k u v 3 4 (by decide) (by decide)
            (6 + 2 * (edges.length - (L_k.length + 1))) hw3 hn_w (by omega) (s := s₇)
            (by simp [s₇, s₆, s₅, s₄, s₃, s₂, s₁, State.setReg])
            (by simp [s₇, s₆, s₅, s₄, s₃, s₂, State.setReg])
            hr22 hnew₇ with
          ⟨s₈, t₈, hex₈, ht₈, hr22₈, hnew₈, harr₈, hreg₈⟩
        have hr2_₈ : s₈.regs 2 = k := by
          rw [hreg₈ 2 (by decide)]
          exact hrk
        refine ⟨s₈, 1 + t₈, .ite_true hcond9 hflag_ne hex₈, by omega, hr2_₈,
          by simpa [hL_next_eq, e, u, v] using hr22₈,
          by simpa [hL_next_eq, e, u, v] using hnew₈,
          fun a ha => by rw [harr₈ a ha]; rfl,
          fun r _ h3 h4 h5 h6 h7 h8 h9 h22 => by
            rw [hreg₈ r h22]
            simp [s₇, s₆, s₅, s₄, s₃, s₂, s₁, State.setReg, h3, h4, h5, h6, h7, h8, h9]⟩
      · have hflag0 : flag = 0 := Classical.not_not.mp (mt hflag_iff.mp hkeep)
        have hcond9 : (Expr.reg 9).eval w s₇ = some 0 := by
          simp [s₇, State.setReg, Expr.eval, checkWord, hflag0, h0_w]
        have hL_next_eq : L_next = L_k := by
          dsimp [L_next, L_k]
          rw [htake_succ, List.filter_append, List.filter_cons_of_neg hkeep,
            List.filter_nil, List.append_nil]
        refine ⟨s₇, 1 + 1, .ite_false hcond9 (.skip s₇), by omega, hrk,
          by simp [s₇, s₆, s₅, s₄, s₃, s₂, s₁, State.setReg, hL_next_eq, hr22, L_k],
          by simp [s₇, s₆, s₅, s₄, s₃, s₂, s₁, hL_next_eq, hnew, L_k],
          fun _ _ => rfl,
          fun r _ h3 h4 h5 h6 h7 h8 h9 _ => by
            simp [s₇, s₆, s₅, s₄, s₃, s₂, s₁, State.setReg, h3, h4, h5, h6, h7, h8, h9]⟩
    rcases hstep with ⟨s₈, t_b, hex_b, ht_b, hr2_s₈, hr22₈, hnew₈, harr₈, hreg₈⟩
    let s₉ := s₈.setReg 2 (k + 1)
    have hex_inc : Exec w (.assign 2 (.op .add (.reg 2) (.const 1))) s₈ s₉ 4 :=
      .assign (by
        simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hr2_s₈, hk_w, hw,
          show k + 1 < 2 ^ w by omega])
    have hin₉ : s₉.arrs 0 = [n, edges.length] ++ flatEdges edges := by
      change s₈.arrs 0 = _
      rw [harr₈ 0 (by decide), hin]
    have hU₉ : IsBitSet U 12 s₉ := hU.of_arr_eq (harr₈ 12 (by decide))
    have hX₉ : IsBitSet X 13 s₉ := hX.of_arr_eq (harr₈ 13 (by decide))
    have hrm₉ : s₉.regs 1 = edges.length := by
      change s₈.regs 1 = _
      rw [hreg₈ 1 (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide), hrm]
    have hrk₉ : s₉.regs 2 = k + 1 := rfl
    have hr28₉ : s₉.regs 28 = if incX then 1 else 0 := by
      change (s₈.setReg 2 (k + 1)).regs 28 = _
      rw [State.setReg_regs_ne _ _ (by decide),
          hreg₈ 28 (by decide) (by decide) (by decide) (by decide) (by decide)
            (by decide) (by decide) (by decide) (by decide), hr28]
    rcases ih (k + 1) (by omega) (s := s₉) hin₉ hU₉ hX₉ hrm₉ hrk₉ hr28₉ hr22₈ hnew₈ with
      ⟨s₁₀, t₁₀, hex₁₀, ht₁₀, hr22₁₀, hnew₁₀, harr₁₀, hreg₁₀⟩
    refine ⟨s₁₀, 3 + ((7 + (7 + (3 + (3 + (3 + (3 + (10 + t_b))))))) + 4) + t₁₀,
      .while_true hcond (by omega)
        (.seq (.seq hex₁ (.seq hex₂ (.seq hex₃ (.seq hex₄ (.seq hex₅ (.seq hex₆ (.seq hex₇ hex_b))))))) hex_inc)
        hex₁₀,
      by omega, hr22₁₀, hnew₁₀,
      fun a ha => by rw [harr₁₀ a ha]; exact harr₈ a ha,
      fun r h2 h3 h4 h5 h6 h7 h8 h9 h22 => by
        rw [hreg₁₀ r h2 h3 h4 h5 h6 h7 h8 h9 h22]
        change (s₈.setReg 2 (k + 1)).regs r = s.regs r
        rw [State.setReg_regs_ne _ _ h2]
        exact hreg₈ r h2 h3 h4 h5 h6 h7 h8 h9 h22⟩

theorem filterSubgraphEdgesProg_exec {w n : ℕ} (U X : Finset (Fin n)) (incX : Bool)
    (edges : List (Fin n × Fin n))
    (hw3 : 3 < 2 ^ w) (hn_w : n < 2 ^ w) (hm8_w : 8 + 2 * edges.length < 2 ^ w) {s : State}
    (hin : s.arrs 0 = [n, edges.length] ++ flatEdges edges)
    (hU : IsBitSet U 12 s) (hX : IsBitSet X 13 s)
    (hrm : s.regs 1 = edges.length) (hr14 : s.regs 14 = n)
    (hr28 : s.regs 28 = if incX then 1 else 0) :
    let L₁ := edges.filter (alg86KeepEdge U X incX)
    ∃ s' t,
      Exec w filterSubgraphEdgesProg s s' t ∧
      t ≤ 64 * edges.length + 28 ∧
      s'.regs 22 = L₁.length ∧
      s'.arrs 17 = ([n, L₁.length] ++ flatEdges L₁) ++
        List.replicate (6 + 2 * (edges.length - L₁.length)) 0 ∧
      (∀ a : Arr, a ≠ 17 → s'.arrs a = s.arrs a) ∧
      (∀ r : Reg, r ≠ 2 → r ≠ 3 → r ≠ 4 → r ≠ 5 → r ≠ 6 → r ≠ 7 → r ≠ 8 → r ≠ 9 → r ≠ 22 →
        s'.regs r = s.regs r) := by
  intro L₁
  have h0_w : 0 < 2 ^ w := by omega
  have hw : 1 < 2 ^ w := by omega
  have hw2 : 2 < 2 ^ w := by omega
  have h8_w : 8 < 2 ^ w := by omega
  have hm_w : edges.length < 2 ^ w := by omega
  have h2m_w : 2 * edges.length < 2 ^ w := by omega
  let s₁ := s.setArr 17 (List.replicate (8 + 2 * edges.length) 0)
  have hex₁ : Exec w (.alloc 17 (.op .add (.const 8) (.op .mul (.const 2) (.reg 1)))) s s₁
      (5 + (8 + 2 * edges.length)) :=
    .alloc (by simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hrm, h8_w, hw2, hm_w, h2m_w, hm8_w])
  let s₂ := s₁.setReg 22 0
  have hex₂ : Exec w (.assign 22 (.const 0)) s₁ s₂ 2 :=
    .assign (by simp [Expr.eval, checkWord, h0_w])
  let s₃ := s₂.setReg 2 0
  have hex₃ : Exec w (.assign 2 (.const 0)) s₂ s₃ 2 :=
    .assign (by simp [Expr.eval, checkWord, h0_w])
  have hnew₃ : s₃.arrs 17 =
      ([0, 0] ++ flatEdges ((edges.take 0).filter (alg86KeepEdge U X incX))) ++
        List.replicate (6 + 2 * (edges.length - ((edges.take 0).filter (alg86KeepEdge U X incX)).length)) 0 := by
    change List.replicate (8 + 2 * edges.length) 0 = _
    simp only [List.take_zero, List.filter_nil, flatEdges, List.length_nil, Nat.sub_zero]
    rw [show 8 + 2 * edges.length = (6 + 2 * edges.length) + 2 by omega,
      Nat.add_comm _ 2, List.replicate_add]
    rfl
  rcases filterSubgraphEdgesLoop_exec U X incX edges hw3 hn_w hm8_w edges.length 0 (by omega)
      (s := s₃) hin (hU.of_arr_eq rfl) (hX.of_arr_eq rfl) hrm rfl hr28 rfl hnew₃ with
    ⟨s₄, t₄, hex₄, ht₄, hr22₄, hnew₄, harr₄, hreg₄⟩
  have hL₁_le : L₁.length ≤ edges.length := List.length_filter_le _ _
  have hL₁_w : L₁.length < 2 ^ w := by omega
  have hr14_₄ : s₄.regs 14 = n := by
    rw [hreg₄ 14 (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide)]
    exact hr14
  have h17_len : 2 ≤ (s₄.arrs 17).length := by
    rw [hnew₄, List.length_append, List.length_append]
    simp only [List.length_cons, List.length_nil]
    omega
  let s₅ := s₄.writeArr 17 0 n
  have hex₅ : Exec w (.write 17 (.const 0) (.reg 14)) s₄ s₅ 3 :=
    .write (by simp [Expr.eval, checkWord, h0_w])
      (by simp [Expr.eval, checkWord, hr14_₄, hn_w])
      (by omega)
  let s₆ := s₅.writeArr 17 1 L₁.length
  have hex₆ : Exec w (.write 17 (.const 1) (.reg 22)) s₅ s₆ 3 :=
    .write (by simp [Expr.eval, checkWord, hw])
      (by simp [s₅, Expr.eval, checkWord, hr22₄, L₁, hL₁_w])
      (by simp [s₅]; omega)
  have hnew₆ : s₆.arrs 17 = ([n, L₁.length] ++ flatEdges L₁) ++
      List.replicate (6 + 2 * (edges.length - L₁.length)) 0 := by
    change ((s₄.arrs 17).set 0 n).set 1 L₁.length = _
    rw [hnew₄]
    simp [L₁]
  refine ⟨s₆, (5 + (8 + 2 * edges.length)) + (2 + (2 + (t₄ + (3 + 3)))),
    .seq hex₁ (.seq hex₂ (.seq hex₃ (.seq hex₄ (.seq hex₅ hex₆)))),
    by omega, hr22₄, hnew₆,
    fun a ha => by
      simp only [s₆, s₅, State.writeArr_arrs_ne _ _ _ ha]
      rw [harr₄ a ha]
      simp [s₃, s₂, s₁, ha],
    fun r h2 h3 h4 h5 h6 h7 h8 h9 h22 => by
      change s₄.regs r = s.regs r
      rw [hreg₄ r h2 h3 h4 h5 h6 h7 h8 h9 h22]
      simp [s₃, s₂, s₁, State.setReg, h2, h22]⟩

/-- Computes `U ∪ X` in `a_18`, filters `edges₀` by `alg86KeepEdge U X incX` into `a_17`, and
appends `encAlg86Subgraph (U ∪ X) (edges₀.filter (alg86KeepEdge U X incX))` to `outArr`. -/
def emitUXSubgraphProg : Cmd :=
  .seq alg86UnionBitSetProg
    (.seq filterSubgraphEdgesProg
      appendSubgraphToOutProg)

theorem emitUXSubgraphProg_exec {w n cap cnt : ℕ}
    (U X : Finset (Fin n)) (incX : Bool) (edges₀ : List (Fin n × Fin n))
    (pref : List ℕ)
    (hcap_le : pref.length + (n + 2 + 2 * edges₀.length) ≤ cap)
    (hw3 : 3 < 2 ^ w) (hm8_w : 8 + 2 * edges₀.length < 2 ^ w)
    (hcap_w : cap < 2 ^ w) (hcnt_w : cnt + 1 < 2 ^ w) {s : State}
    (hin : s.arrs 0 = [n, edges₀.length] ++ flatEdges edges₀)
    (hU : IsBitSet U 12 s) (hX : IsBitSet X 13 s)
    (hout : s.arrs outArr = pref ++ List.replicate (cap - pref.length) 0)
    (hr1 : s.regs 1 = edges₀.length) (hr14 : s.regs 14 = n)
    (hr25 : s.regs 25 = pref.length) (hr26 : s.regs 26 = cnt)
    (hr28 : s.regs 28 = if incX then 1 else 0) :
    let L₁ := edges₀.filter (alg86KeepEdge U X incX)
    ∃ s' t,
      Exec w emitUXSubgraphProg s s' t ∧
      t ≤ 39 * n + 98 * edges₀.length + 91 ∧
      s'.arrs outArr =
        (pref ++ encAlg86Subgraph (U ∪ X) L₁) ++
          List.replicate (cap - (pref ++ encAlg86Subgraph (U ∪ X) L₁).length) 0 ∧
      s'.regs 25 = (pref ++ encAlg86Subgraph (U ∪ X) L₁).length ∧
      s'.regs 26 = cnt + 1 ∧
      (∀ a : Arr, a ≠ outArr → a ≠ 17 → a ≠ 18 → s'.arrs a = s.arrs a) ∧
      (∀ r : Reg, r ≠ 2 → r ≠ 3 → r ≠ 4 → r ≠ 5 → r ≠ 6 → r ≠ 7 → r ≠ 8 → r ≠ 9 →
        r ≠ 21 → r ≠ 22 → r ≠ 25 → r ≠ 26 → s'.regs r = s.regs r) := by
  intro L₁
  have hw2 : 2 < 2 ^ w := by omega
  have hn_w : n < 2 ^ w := by omega
  have hL₁_le : L₁.length ≤ edges₀.length := List.length_filter_le _ _
  -- 1. alg86UnionBitSetProg
  rcases alg86UnionBitSetProg_exec U X hw2 hn_w hU hX hr14 with
    ⟨s₁, t₁, hex₁, ht₁, hUX₁, harr₁, hreg₁⟩
  -- 2. filterSubgraphEdgesProg
  rcases filterSubgraphEdgesProg_exec U X incX edges₀ hw3 hn_w hm8_w (s := s₁)
      (by rw [harr₁ 0 (by decide), hin])
      (hU.of_arr_eq (harr₁ 12 (by decide)))
      (hX.of_arr_eq (harr₁ 13 (by decide)))
      (by rw [hreg₁ 1 (by decide) (by decide) (by decide), hr1])
      (by rw [hreg₁ 14 (by decide) (by decide) (by decide), hr14])
      (by rw [hreg₁ 28 (by decide) (by decide) (by decide), hr28]) with
    ⟨s₂, t₂, hex₂, ht₂, hr22₂, h17₂, harr₂, hreg₂⟩
  -- 3. appendSubgraphToOutProg
  have hUX₂ : IsBitSet (U ∪ X) 18 s₂ := hUX₁.of_arr_eq (harr₂ 18 (by decide))
  have hout₂ : s₂.arrs outArr = pref ++ List.replicate (cap - pref.length) 0 := by
    rw [harr₂ outArr (by decide), harr₁ outArr (by decide), hout]
  have hr14_₂ : s₂.regs 14 = n := by
    rw [hreg₂ 14 (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide),
      hreg₁ 14 (by decide) (by decide) (by decide), hr14]
  have hr25_₂ : s₂.regs 25 = pref.length := by
    rw [hreg₂ 25 (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide),
      hreg₁ 25 (by decide) (by decide) (by decide), hr25]
  have hr26_₂ : s₂.regs 26 = cnt := by
    rw [hreg₂ 26 (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide),
      hreg₁ 26 (by decide) (by decide) (by decide), hr26]
  rcases appendSubgraphToOutProg_exec (U ∪ X) L₁ pref
      (List.replicate (6 + 2 * (edges₀.length - L₁.length)) 0)
      (by omega) hw2 hcap_w hcnt_w hUX₂ h17₂ hout₂ hr14_₂ hr22₂ hr25_₂ hr26_₂ with
    ⟨s₃, t₃, hex₃, ht₃, hout₃, hr25₃, hr26₃, harr₃, hreg₃⟩
  refine ⟨s₃, t₁ + (t₂ + t₃), .seq hex₁ (.seq hex₂ hex₃), by omega, hout₃, hr25₃, hr26₃,
    fun a hout h17 h18 => by rw [harr₃ a hout, harr₂ a h17, harr₁ a h18],
    fun r h2 h3 h4 h5 h6 h7 h8 h9 h21 h22 h25 h26 => by
      rw [hreg₃ r h2 h3 h21 h25 h26,
          hreg₂ r h2 h3 h4 h5 h6 h7 h8 h9 h22,
          hreg₁ r h2 h3 h4]⟩

/-- Set of edge indices in `Fin k` (as a subset of `Fin edges₀.length`) whose endpoints in `edges₀`
both lie in `X`. -/
def alg86XEdgeIndicesPrefix {n : ℕ} (edges₀ : List (Fin n × Fin n)) (X : Finset (Fin n)) :
    ℕ → Finset (Fin edges₀.length)
  | 0 => ∅
  | k + 1 =>
    if hk : k < edges₀.length then
      let jk : Fin edges₀.length := ⟨k, hk⟩
      let e := edges₀[k]'hk
      if e.1 ∈ X ∧ e.2 ∈ X then
        insert jk (alg86XEdgeIndicesPrefix edges₀ X k)
      else
        alg86XEdgeIndicesPrefix edges₀ X k
    else
      alg86XEdgeIndicesPrefix edges₀ X k

/-- Set of all edge indices `j : Fin edges₀.length` whose endpoints in `edges₀` both lie in `X`. -/
abbrev alg86XEdgeIndices {n : ℕ} (edges₀ : List (Fin n × Fin n)) (X : Finset (Fin n)) :
    Finset (Fin edges₀.length) :=
  alg86XEdgeIndicesPrefix edges₀ X edges₀.length

theorem mem_alg86XEdgeIndicesPrefix_iff {n : ℕ} (edges₀ : List (Fin n × Fin n))
    (X : Finset (Fin n)) (k : ℕ) (hk_le : k ≤ edges₀.length) (j : Fin edges₀.length) :
    j ∈ alg86XEdgeIndicesPrefix edges₀ X k ↔
      j.1 < k ∧ (edges₀[j.1]'j.2).1 ∈ X ∧ (edges₀[j.1]'j.2).2 ∈ X := by
  induction k with
  | zero => simp [alg86XEdgeIndicesPrefix]
  | succ k ih =>
    have hk_lt : k < edges₀.length := by omega
    simp only [alg86XEdgeIndicesPrefix, hk_lt, ↓reduceDIte]
    split_ifs with hX
    · rw [Finset.mem_insert, ih (by omega), Fin.ext_iff]
      constructor
      · rintro (rfl | ⟨hlt, h1, h2⟩)
        · exact ⟨by omega, hX.1, hX.2⟩
        · exact ⟨by omega, h1, h2⟩
      · rintro ⟨hlt, h1, h2⟩
        rcases Nat.lt_succ_iff_lt_or_eq.mp hlt with hlt' | heq
        · exact Or.inr ⟨hlt', h1, h2⟩
        · exact Or.inl heq
    · rw [ih (by omega)]
      constructor
      · rintro ⟨hlt, h1, h2⟩
        exact ⟨by omega, h1, h2⟩
      · rintro ⟨hlt, h1, h2⟩
        rcases Nat.lt_succ_iff_lt_or_eq.mp hlt with hlt' | heq
        · exact ⟨hlt', h1, h2⟩
        · exfalso; subst heq; exact hX ⟨h1, h2⟩

theorem mem_alg86XEdgeIndices_iff {n : ℕ} (edges₀ : List (Fin n × Fin n))
    (X : Finset (Fin n)) (j : Fin edges₀.length) :
    j ∈ alg86XEdgeIndices edges₀ X ↔
      (edges₀[j.1]'j.2).1 ∈ X ∧ (edges₀[j.1]'j.2).2 ∈ X := by
  rw [alg86XEdgeIndices, mem_alg86XEdgeIndicesPrefix_iff edges₀ X edges₀.length le_rfl]
  exact ⟨fun h => h.2, fun h => ⟨j.2, h⟩⟩

/-- Loop body of `markXEdgesProg`: reads the `r_2`-th edge `(u, v)` from `inArr = 0`, and if both
`u ∈ X` and `v ∈ X` (`a_13[u] * a_13[v] ≠ 0`), writes `1` to `a_51[r_2]`. -/
def markXEdgesBody : Cmd :=
  .seq (.assign 3 (.read 0 (.op .add (.const 2) (.op .mul (.const 2) (.reg 2)))))
    (.seq (.assign 4 (.read 0 (.op .add (.const 3) (.op .mul (.const 2) (.reg 2)))))
      (.seq (.assign 5 (.read 13 (.reg 3)))
        (.seq (.assign 6 (.read 13 (.reg 4)))
          (.ite (.op .mul (.reg 5) (.reg 6))
            (.write 51 (.reg 2) (.const 1))
            .skip))))

/-- Marks in `a_51` (`IsBitSet M 51`) all edge indices `j : Fin edges₀.length` whose endpoints in
`edges₀` both lie in `X` (`IsBitSet X 13`). -/
def markXEdgesProg : Cmd :=
  .seq (.assign 2 (.const 0))
    (forUp 2 (.reg 1) markXEdgesBody)

theorem markXEdgesLoop_exec {w n : ℕ} (edges₀ : List (Fin n × Fin n))
    (X : Finset (Fin n)) (M : Finset (Fin edges₀.length))
    (hw3 : 3 < 2 ^ w) (hn_w : n < 2 ^ w) (hm3_w : 3 + 2 * edges₀.length < 2 ^ w)
    (rem k : ℕ) (hrem : k + rem = edges₀.length) {s : State}
    (hin : s.arrs 0 = [n, edges₀.length] ++ flatEdges edges₀)
    (hX : IsBitSet X 13 s)
    (hM : IsBitSet (M ∪ alg86XEdgeIndicesPrefix edges₀ X k) 51 s)
    (hr1 : s.regs 1 = edges₀.length) (hr2 : s.regs 2 = k) :
    ∃ s' t,
      Exec w (forUp 2 (.reg 1) markXEdgesBody) s s' t ∧
      t ≤ 3 + 33 * rem ∧
      IsBitSet (M ∪ alg86XEdgeIndices edges₀ X) 51 s' ∧
      (∀ a : Arr, a ≠ 51 → s'.arrs a = s.arrs a) ∧
      (∀ r : Reg, r ≠ 2 → r ≠ 3 → r ≠ 4 → r ≠ 5 → r ≠ 6 → s'.regs r = s.regs r) := by
  have h0_w : 0 < 2 ^ w := by omega
  have hw : 1 < 2 ^ w := by omega
  have hw2 : 2 < 2 ^ w := by omega
  have hm_w : edges₀.length < 2 ^ w := by omega
  induction rem generalizing k s with
  | zero =>
    have hk_eq : k = edges₀.length := by omega
    subst hk_eq
    have hcond : (Expr.op .lt (.reg 2) (.reg 1)).eval w s = some 0 := by
      simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hr2, hr1, hm_w]
    exact ⟨s, 3, .while_false hcond, by omega, hM,
      fun _ _ => rfl, fun _ _ _ _ _ _ => rfl⟩
  | succ rem ih =>
    have hk_lt : k < edges₀.length := by omega
    have hk_w : k < 2 ^ w := by omega
    have h2k_w : 2 * k < 2 ^ w := by omega
    have h2k2_w : 2 + 2 * k < 2 ^ w := by omega
    have h2k3_w : 3 + 2 * k < 2 ^ w := by omega
    let jk : Fin edges₀.length := ⟨k, hk_lt⟩
    let e := edges₀[k]'hk_lt
    let u := e.1
    let v := e.2
    have hcond : (Expr.op .lt (.reg 2) (.reg 1)).eval w s = some 1 := by
      simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hr2, hr1, hk_w, hm_w, hk_lt, hw]
    have hin_u_lt : 2 + 2 * k < (s.arrs 0).length := by
      rw [hin]; simp [length_flatEdges]; omega
    have hin_u_get : (s.arrs 0)[2 + 2 * k]'hin_u_lt = u.1 := by
      have hidx : 2 + 2 * k = (2 * k) + 1 + 1 := by omega
      simp only [hin, hidx, List.cons_append, List.nil_append, List.getElem_cons_succ]
      exact getElem_flatEdges_even edges₀ hk_lt
    have hin_v_lt : 3 + 2 * k < (s.arrs 0).length := by
      rw [hin]; simp [length_flatEdges]; omega
    have hin_v_get : (s.arrs 0)[3 + 2 * k]'hin_v_lt = v.1 := by
      have hidx : 3 + 2 * k = (2 * k + 1) + 1 + 1 := by omega
      simp only [hin, hidx, List.cons_append, List.nil_append, List.getElem_cons_succ]
      exact getElem_flatEdges_odd edges₀ hk_lt
    have hu_w : u.1 < 2 ^ w := Nat.lt_trans u.2 hn_w
    have hv_w : v.1 < 2 ^ w := Nat.lt_trans v.2 hn_w
    let s₁ := s.setReg 3 u.1
    have hex₁ : Exec w (.assign 3 (.read 0 (.op .add (.const 2) (.op .mul (.const 2) (.reg 2))))) s s₁ 7 :=
      .assign (by
        simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hr2, hw2, hk_w, h2k_w, h2k2_w,
          hin_u_lt, hin_u_get, hu_w])
    let s₂ := s₁.setReg 4 v.1
    have hex₂ : Exec w (.assign 4 (.read 0 (.op .add (.const 3) (.op .mul (.const 2) (.reg 2))))) s₁ s₂ 7 :=
      .assign (by
        simp [s₁, State.setReg, Expr.eval, BinOp.eval, BinOp.raw, checkWord, hr2, hw2, hw3,
          hk_w, h2k_w, h2k3_w, hin_v_lt, hin_v_get, hv_w])
    have hu_X_lt : u.1 < (s.arrs 13).length := by rw [hX.1]; exact u.2
    let xb_u := (s.arrs 13)[u.1]'hu_X_lt
    have hxbu_eq : xb_u = if u ∈ X then 1 else 0 := hX.getElem_eq_ite u
    have hxbu_w : xb_u < 2 ^ w := by rw [hxbu_eq]; split_ifs <;> omega
    let s₃ := s₂.setReg 5 xb_u
    have hex₃ : Exec w (.assign 5 (.read 13 (.reg 3))) s₂ s₃ 3 :=
      .assign (by simp [s₂, s₁, State.setReg, Expr.eval, checkWord, hu_w, hu_X_lt, xb_u, hxbu_w])
    have hv_X_lt : v.1 < (s.arrs 13).length := by rw [hX.1]; exact v.2
    let xb_v := (s.arrs 13)[v.1]'hv_X_lt
    have hxbv_eq : xb_v = if v ∈ X then 1 else 0 := hX.getElem_eq_ite v
    have hxbv_w : xb_v < 2 ^ w := by rw [hxbv_eq]; split_ifs <;> omega
    let s₄ := s₃.setReg 6 xb_v
    have hex₄ : Exec w (.assign 6 (.read 13 (.reg 4))) s₃ s₄ 3 :=
      .assign (by simp [s₃, s₂, s₁, State.setReg, Expr.eval, checkWord, hv_w, hv_X_lt, xb_v, hxbv_w])
    have hstep : ∃ s₅ t_b,
        Exec w (.ite (.op .mul (.reg 5) (.reg 6)) (.write 51 (.reg 2) (.const 1)) .skip) s₄ s₅ t_b ∧
        t_b ≤ 6 ∧
        s₅.regs 2 = k ∧
        IsBitSet (M ∪ alg86XEdgeIndicesPrefix edges₀ X (k + 1)) 51 s₅ ∧
        (∀ a : Arr, a ≠ 51 → s₅.arrs a = s.arrs a) ∧
        (∀ r : Reg, r ≠ 3 → r ≠ 4 → r ≠ 5 → r ≠ 6 → s₅.regs r = s.regs r) := by
      by_cases huvX : u ∈ X ∧ v ∈ X
      · have hmul1 : xb_u * xb_v = 1 := by simp [hxbu_eq, hxbv_eq, huvX.1, huvX.2]
        have hcond_m : (Expr.op .mul (.reg 5) (.reg 6)).eval w s₄ = some 1 := by
          simp [s₄, s₃, s₂, s₁, State.setReg, Expr.eval, BinOp.eval, BinOp.raw, checkWord,
            hxbu_w, hxbv_w, hmul1, hw]
        have h51_len : k < (s₄.arrs 51).length := by
          change k < (s.arrs 51).length
          rw [hM.1]; exact hk_lt
        let s₅ := s₄.writeArr 51 k 1
        have hex_w : Exec w (.write 51 (.reg 2) (.const 1)) s₄ s₅ 3 :=
          .write (by simp [s₄, s₃, s₂, s₁, State.setReg, Expr.eval, checkWord, hr2, hk_w])
            (by simp [Expr.eval, checkWord, hw])
            h51_len
        have hM₅ : IsBitSet (M ∪ alg86XEdgeIndicesPrefix edges₀ X (k + 1)) 51 s₅ := by
          have hM₄ : IsBitSet (M ∪ alg86XEdgeIndicesPrefix edges₀ X k) 51 s₄ := hM.of_arr_eq rfl
          have hins := hM₄.write_one jk
          have hset_eq : insert jk (M ∪ alg86XEdgeIndicesPrefix edges₀ X k) =
              M ∪ alg86XEdgeIndicesPrefix edges₀ X (k + 1) := by
            simp [alg86XEdgeIndicesPrefix, hk_lt, e, u, v, huvX.1, huvX.2, jk]
          rwa [hset_eq] at hins
        exact ⟨s₅, 3 + 3, .ite_true hcond_m (by decide) hex_w, by omega, hr2, hM₅,
          fun a ha => by simp [s₅, s₄, s₃, s₂, s₁, ha],
          fun r h3 h4 h5 h6 => by simp [s₅, s₄, s₃, s₂, s₁, State.setReg, h3, h4, h5, h6]⟩
      · have hmul0 : xb_u * xb_v = 0 := by
          rw [hxbu_eq, hxbv_eq]
          by_cases hu : u ∈ X <;> by_cases hv : v ∈ X <;> simp [hu, hv] at huvX ⊢
        have hcond_m : (Expr.op .mul (.reg 5) (.reg 6)).eval w s₄ = some 0 := by
          simp [s₄, s₃, s₂, s₁, State.setReg, Expr.eval, BinOp.eval, BinOp.raw, checkWord,
            hxbu_w, hxbv_w, hmul0, h0_w]
        have hM₄ : IsBitSet (M ∪ alg86XEdgeIndicesPrefix edges₀ X (k + 1)) 51 s₄ := by
          have hset_eq : alg86XEdgeIndicesPrefix edges₀ X (k + 1) =
              alg86XEdgeIndicesPrefix edges₀ X k := by
            simp [alg86XEdgeIndicesPrefix, hk_lt, e, u, v, huvX]
          rw [hset_eq]
          exact hM.of_arr_eq rfl
        exact ⟨s₄, 3 + 1, .ite_false hcond_m (.skip s₄), by omega, hr2, hM₄,
          fun _ _ => rfl,
          fun r h3 h4 h5 h6 => by simp [s₄, s₃, s₂, s₁, State.setReg, h3, h4, h5, h6]⟩
    rcases hstep with ⟨s₅, t_b, hex_b, ht_b, hr2₅, hM₅, harr₅, hreg₅⟩
    let s₆ := s₅.setReg 2 (k + 1)
    have hex_inc : Exec w (.assign 2 (.op .add (.reg 2) (.const 1))) s₅ s₆ 4 :=
      .assign (by
        simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hr2₅, hk_w, hw,
          show k + 1 < 2 ^ w by omega])
    rcases ih (k + 1) (by omega) (s := s₆)
        (by change s₅.arrs 0 = _; rw [harr₅ 0 (by decide), hin])
        (hX.of_arr_eq (harr₅ 13 (by decide)))
        (hM₅.of_arr_eq rfl)
        (by
          change (s₅.setReg 2 (k + 1)).regs 1 = edges₀.length
          rw [State.setReg_regs_ne _ _ (by decide),
              hreg₅ 1 (by decide) (by decide) (by decide) (by decide), hr1])
        rfl with
      ⟨s₇, t₇, hex₇, ht₇, hM₇, harr₇, hreg₇⟩
    refine ⟨s₇, 3 + ((7 + (7 + (3 + (3 + t_b)))) + 4) + t₇,
      .while_true hcond (by omega) (.seq (.seq hex₁ (.seq hex₂ (.seq hex₃ (.seq hex₄ hex_b)))) hex_inc) hex₇,
      by omega, hM₇,
      fun a ha => by rw [harr₇ a ha]; exact harr₅ a ha,
      fun r h2 h3 h4 h5 h6 => by
        rw [hreg₇ r h2 h3 h4 h5 h6]
        change (s₅.setReg 2 (k + 1)).regs r = s.regs r
        rw [State.setReg_regs_ne _ _ h2]
        exact hreg₅ r h3 h4 h5 h6⟩

theorem markXEdgesProg_exec {w n : ℕ} (edges₀ : List (Fin n × Fin n))
    (X : Finset (Fin n)) (M : Finset (Fin edges₀.length))
    (hw3 : 3 < 2 ^ w) (hn_w : n < 2 ^ w) (hm3_w : 3 + 2 * edges₀.length < 2 ^ w) {s : State}
    (hin : s.arrs 0 = [n, edges₀.length] ++ flatEdges edges₀)
    (hX : IsBitSet X 13 s) (hM : IsBitSet M 51 s)
    (hr1 : s.regs 1 = edges₀.length) :
    ∃ s' t,
      Exec w markXEdgesProg s s' t ∧
      t ≤ 33 * edges₀.length + 5 ∧
      IsBitSet (M ∪ alg86XEdgeIndices edges₀ X) 51 s' ∧
      (∀ a : Arr, a ≠ 51 → s'.arrs a = s.arrs a) ∧
      (∀ r : Reg, r ≠ 2 → r ≠ 3 → r ≠ 4 → r ≠ 5 → r ≠ 6 → s'.regs r = s.regs r) := by
  have h0_w : 0 < 2 ^ w := by omega
  let s₁ := s.setReg 2 0
  have hex₁ : Exec w (.assign 2 (.const 0)) s s₁ 2 :=
    .assign (by simp [Expr.eval, checkWord, h0_w])
  have hM₁ : IsBitSet (M ∪ alg86XEdgeIndicesPrefix edges₀ X 0) 51 s₁ := by
    simp only [alg86XEdgeIndicesPrefix, Finset.union_empty]
    exact hM.of_arr_eq rfl
  rcases markXEdgesLoop_exec edges₀ X M hw3 hn_w hm3_w edges₀.length 0 (by omega) (s := s₁)
      hin (hX.of_arr_eq rfl) hM₁
      (by simp [s₁, State.setReg, hr1]) rfl with
    ⟨s₂, t₂, hex₂, ht₂, hM₂, harr₂, hreg₂⟩
  refine ⟨s₂, 2 + t₂, .seq hex₁ hex₂, by omega, hM₂,
    fun a ha => by rw [harr₂ a ha]; rfl,
    fun r h2 h3 h4 h5 h6 => by
      rw [hreg₂ r h2 h3 h4 h5 h6]
      simp [s₁, State.setReg, h2]⟩


end GraphMinor.Compute
