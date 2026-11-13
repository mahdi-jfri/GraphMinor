module

public import GraphMinor.Compute.Algorithm105Step2
public import GraphMinor.Compute.Join41
public import GraphMinor.Compute.FolioReduction

/-!
# Graph Minors XIII, Algorithm (10.5) in the Word RAM Model

This file formalizes Algorithm (10.5) of Robertson and Seymour, *Graph Minors. XIII. The Disjoint
Paths Problem*, J. Combin. Theory Ser. B **63** (1995), 65–110 (pages 108–109):

> **(10.5) Algorithm.**
> *Input:* A digraph $G$ and a subset $Z \subseteq V(G)$ with $|Z| \le \xi$.
> *Output:* The $\delta$-folio of $G$ relative to $Z$.
> *Running time:* $O(v^3)$.
>
> *Description:*
> (1) Let $p, C$ be as in (6.5). We apply (6.5) to $G, Z$, and obtain a subdigraph $G' \subseteq G$
>     with $Z \subseteq V(G')$ such that $G$ and $G'$ have the same $\delta$-folio relative to $Z$
>     and such that $|E(G')| \le C|V(G')|$.
>     Let $q = \binom{p}{2} + \xi - 1$; let $h$ be as in (10.3); let $\omega$ be as in (9.8). We set
>     $G_1 = G'$ and perform a recursion. At the beginning of the $i$th iteration we have a
>     subdigraph $G_i$ of $G'$ with $|V(G_i)| = |V(G')| - i + 1$ and with $Z \subseteq V(G_i)$, such
>     that the $\delta$-folios of $G_i$ and $G'$ relative to $Z$ are equal. The iteration proceeds
>     as follows. We apply (9.9) to $G_i \setminus Z$.
> (2) If we obtain a branch-decomposition of $G_i \setminus Z$ of width $\le \omega$, we convert it
>     to a branch-decomposition of $G_i$ of width $\le \omega + \xi$, compute the $\delta$-folio of
>     $G_i$ relative to $Z$ by (4.1), and stop.
> (3) If we obtain a model of $K_p$ in $G_i \setminus Z$ and hence in $G_i$, we apply (6.2) to find
>     a vertex $v$ of $G_i$ irrelevant to the $\delta$-folio of $G_i$ relative to $Z$; we set
>     $G_{i+1} = G_i \setminus v$ and return for the next iteration.
> (4) Otherwise, we obtain $X, H, \mathcal{A}$ as in Hypothesis C (with $G$ replaced by
>     $G_i \setminus Z$), where $|X| \le \binom{p}{2} - 1$ and $H$ has height $h$. Put
>     $X' = X \cup Z$; then $G_i, X', H, \mathcal{A}$ also satisfy Hypothesis C. We apply (10.4) to
>     $G_i, X', H, \mathcal{A}$, to compute an irrelevant vertex $v$ for the $\delta$-folio of $G_i$
>     relative to $X'$. Since $Z \subseteq X'$, $v$ is also irrelevant for the $\delta$-folio of
>     $G_i$ relative to $Z$, by (2.1). We set $G_{i+1} = G_i \setminus v$, and return for the next
>     iteration.

From `algorithm_10_5` we deduce `folioStatement_of_interfaces : … → FolioStatement δ ξ` and, via
`dp_of_folio` (`FolioReduction.lean`), `disjointPathsStatement_of_interfaces : … → DisjointPathsStatement`.
-/

@[expose] public section

namespace GraphMinor.Compute

open SimpleGraph Graph GraphMinor.Surface GraphMinor.GM09 Alg105

/-! ### Section 1: Encoding Lemmas for `MultiDigraph.deleteVertices` and Word-Size Scaling -/

/-- Monotonicity of `wordSize` under linear scaling `M ≤ K * (n + 1)`. -/
theorem wordSize_le_of_le_mul {c K M n : ℕ} (hM : M ≤ K * (n + 1)) :
    wordSize c M ≤ wordSize (c * (K + 3)) n := by
  have h1 : wordSize c M ≤ wordSize c (K * (n + 1)) := wordSize_mono_right c hM
  have hpow_K : K + 2 ≤ 2 ^ (K + 2) := Nat.le_of_lt Nat.lt_two_pow_self
  have h2 : K * (n + 1) + 2 ≤ (n + 2) * (K + 2) := by
    nlinarith
  have h3 : K * (n + 1) + 2 ≤ (n + 2) * 2 ^ (K + 2) :=
    le_trans h2 (Nat.mul_le_mul_left (n + 2) hpow_K)
  have hlt : n + 2 < 2 ^ (Nat.log 2 (n + 2) + 1) :=
    Nat.lt_pow_succ_log_self (by decide) _
  have hpow_pos : 0 < 2 ^ (K + 2) := Nat.two_pow_pos (K + 2)
  have h4 : (n + 2) * 2 ^ (K + 2) < 2 ^ (Nat.log 2 (n + 2) + 1 + (K + 2)) := by
    calc (n + 2) * 2 ^ (K + 2)
      _ < 2 ^ (Nat.log 2 (n + 2) + 1) * 2 ^ (K + 2) :=
        Nat.mul_lt_mul_of_pos_right hlt hpow_pos
      _ = 2 ^ (Nat.log 2 (n + 2) + 1 + (K + 2)) := (Nat.pow_add 2 _ (K + 2)).symm
  have hlog : Nat.log 2 (K * (n + 1) + 2) < Nat.log 2 (n + 2) + 1 + (K + 2) :=
    Nat.log_lt_of_lt_pow (by omega) (Nat.lt_of_le_of_lt h3 h4)
  have hlog_le : Nat.log 2 (K * (n + 1) + 2) + 1 ≤ (K + 3) * (Nat.log 2 (n + 2) + 1) := by
    nlinarith
  dsimp [wordSize] at h1 ⊢
  calc c * (Nat.log 2 (M + 2) + 1)
    _ ≤ c * (Nat.log 2 (K * (n + 1) + 2) + 1) := h1
    _ ≤ c * ((K + 3) * (Nat.log 2 (n + 2) + 1)) := Nat.mul_le_mul_left c hlog_le
    _ = c * (K + 3) * (Nat.log 2 (n + 2) + 1) := (Nat.mul_assoc c (K + 3) _).symm

theorem MultiDigraph.activePairsList_deleteVertices {n : ℕ} (G : MultiDigraph n)
    (Z : Finset (Fin n)) :
    (G.deleteVertices Z).activePairsList =
      G.activePairsList.filter (fun p => decide (p.1 ∉ Z ∧ p.2 ∉ Z)) := by
  unfold MultiDigraph.activePairsList
  rw [List.filter_filter]
  refine List.filter_congr fun p _ => ?_
  simp only [MultiDigraph.deleteVertices_edgeMult, Bool.decide_and]
  split_ifs with h
  · simp [h]
  · simp [h]

theorem MultiDigraph.numActivePairs_deleteVertices_le {n : ℕ} (G : MultiDigraph n)
    (Z : Finset (Fin n)) :
    (G.deleteVertices Z).numActivePairs ≤ G.numActivePairs := by
  simp only [MultiDigraph.numActivePairs, G.activePairsList_deleteVertices Z]
  exact List.length_filter_le _ _

/-- Filtered flat triples of `G` retaining only pairs `(u, v)` with `u ∉ Z ∧ v ∉ Z`. -/
def MultiDigraph.deleteVerticesTriplesAux {n : ℕ} (G : MultiDigraph n) (Z : Finset (Fin n)) :
    List (Fin n × Fin n) → List ℕ
  | [] => []
  | (u, v) :: ps =>
    if u ∉ Z ∧ v ∉ Z then
      u.1 :: v.1 :: G.edgeMult u v :: G.deleteVerticesTriplesAux Z ps
    else
      G.deleteVerticesTriplesAux Z ps

theorem MultiDigraph.deleteVerticesTriplesAux_eq_flatTriples {n : ℕ}
    (G : MultiDigraph n) (Z : Finset (Fin n)) (ps : List (Fin n × Fin n)) :
    G.deleteVerticesTriplesAux Z ps =
      (G.deleteVertices Z).flatTriples (ps.filter (fun p => decide (p.1 ∉ Z ∧ p.2 ∉ Z))) := by
  induction ps with
  | nil => rfl
  | cons p ps ih =>
    rcases p with ⟨u, v⟩
    by_cases h : u ∉ Z ∧ v ∉ Z
    · simp [MultiDigraph.deleteVerticesTriplesAux, MultiDigraph.flatTriples, h, ih]
    · simp [MultiDigraph.deleteVerticesTriplesAux, h, ih]

theorem MultiDigraph.length_deleteVerticesTriplesAux {n : ℕ}
    (G : MultiDigraph n) (Z : Finset (Fin n)) (ps : List (Fin n × Fin n)) :
    (G.deleteVerticesTriplesAux Z ps).length =
      3 * (ps.filter (fun p => decide (p.1 ∉ Z ∧ p.2 ∉ Z))).length := by
  rw [G.deleteVerticesTriplesAux_eq_flatTriples Z, MultiDigraph.length_flatTriples]

theorem MultiDigraph.enc_deleteVertices_eq {n : ℕ} (G : MultiDigraph n) (Z : Finset (Fin n)) :
    (G.deleteVertices Z).enc =
      [n, (G.activePairsList.filter (fun p => decide (p.1 ∉ Z ∧ p.2 ∉ Z))).length] ++
        G.deleteVerticesTriplesAux Z G.activePairsList := by
  rw [MultiDigraph.enc, MultiDigraph.numActivePairs, G.activePairsList_deleteVertices Z,
    G.deleteVerticesTriplesAux_eq_flatTriples Z]

/-! ### Section 2: Word RAM Gadget 1, Constructing `(G_i.deleteVertices Z_i).enc` -/

/-- Loop body of `deleteVerticesZProg`: reads `(u_k, v_k)` from `a_src`, tests whether
`a_Z[u_k] + a_Z[v_k] == 0` (that is, `u_k ∉ Z` and `v_k ∉ Z`), and if so appends
`(u_k, v_k, mult_k)` to `a_buf` and increments `m_del` (`r_base + 1`). -/
def deleteVerticesZBody (a_src a_Z a_buf : Arr) (r_base : Reg) : Cmd :=
  .seq (readTripleEndpoints a_src (r_base + 4) (r_base + 6) (r_base + 7) (r_base + 8))
    (.seq (.assign (r_base + 9)
        (.op .add (.read a_Z (.reg (r_base + 7))) (.read a_Z (.reg (r_base + 8)))))
      (.ite (.op .eq (.reg (r_base + 9)) (.const 0))
        (.seq (.assign (r_base + 9) (.read a_src (.op .add (.reg (r_base + 6)) (.const 2))))
          (.seq (bufPush3 a_buf (r_base + 5) (r_base + 7) (r_base + 8) (r_base + 9))
            (.assign (r_base + 1) (.op .add (.reg (r_base + 1)) (.const 1)))))
        .skip))

/-- Word RAM program that reads `G.enc` from `a_src` and `bitSetList Z` from `a_Z`, and writes
`(G.deleteVertices Z).enc` into `a_dst` using scratch buffer `a_buf` and registers
`r_base .. r_base + 9`. -/
def deleteVerticesZProg (a_src a_Z a_buf a_dst : Arr) (r_base : Reg) : Cmd :=
  .seq (.assign r_base (.read a_src (.const 0)))
    (.seq (.assign (r_base + 3) (.read a_src (.const 1)))
      (.seq (.assign (r_base + 1) (.const 0))
        (.seq (.assign (r_base + 5) (.op .add (.const 2) (.op .mul (.const 3) (.reg (r_base + 3)))))
          (.seq (.alloc a_buf (.reg (r_base + 5)))
            (.seq (.write a_buf (.const 0) (.reg r_base))
              (.seq (.assign (r_base + 5) (.const 2))
                (.seq (.assign (r_base + 4) (.const 0))
                  (.seq (forUp (r_base + 4) (.reg (r_base + 3))
                      (deleteVerticesZBody a_src a_Z a_buf r_base))
                    (.seq (.write a_buf (.const 1) (.reg (r_base + 1)))
                      (readSliceProg a_buf (.const 0) a_dst
                        (.reg (r_base + 5)) (r_base + 6)))))))))))

theorem deleteVerticesZLoop_exec {w n : ℕ} (G : MultiDigraph n) (Z : Finset (Fin n))
    (a_src a_Z a_buf : ℕ) (r_base : ℕ)
    (hne_sb : a_src ≠ a_buf) (hne_zb : a_Z ≠ a_buf)
    (hw3 : 3 < 2 ^ w) (hn_w : n < 2 ^ w)
    (hm3_w : 2 + 3 * G.numActivePairs < 2 ^ w)
    (hedges_w : G.numEdges < 2 ^ w)
    (suff : List (Fin n × Fin n)) :
    ∀ (pref : List (Fin n × Fin n)),
      G.activePairsList = pref ++ suff →
      ∀ (pfx : List ℕ) (extra_buf m_acc : ℕ),
        pfx.length = 2 + 3 * m_acc →
        m_acc + (suff.filter (fun p => decide (p.1 ∉ Z ∧ p.2 ∉ Z))).length ≤ G.numActivePairs →
        ∀ {s : State},
          s.arrs a_src = G.enc ++ [] →
          s.arrs a_Z = bitSetList Z →
          s.arrs a_buf = pfx ++ List.replicate (3 * suff.length + extra_buf) 0 →
          s.regs r_base = n →
          s.regs (r_base + 1) = m_acc →
          s.regs (r_base + 3) = G.numActivePairs →
          s.regs (r_base + 4) = pref.length →
          s.regs (r_base + 5) = pfx.length →
          ∃ s' t extra_buf',
            Exec w (forUp (r_base + 4) (.reg (r_base + 3))
              (deleteVerticesZBody a_src a_Z a_buf r_base)) s s' t ∧
            t ≤ 3 + 65 * suff.length ∧
            s'.arrs a_buf = pfx ++ G.deleteVerticesTriplesAux Z suff ++ List.replicate extra_buf' 0 ∧
            s'.regs r_base = n ∧
            s'.regs (r_base + 1) =
              m_acc + (suff.filter (fun p => decide (p.1 ∉ Z ∧ p.2 ∉ Z))).length ∧
            s'.regs (r_base + 5) = (pfx ++ G.deleteVerticesTriplesAux Z suff).length ∧
            (∀ a : ℕ, a ≠ a_buf → s'.arrs a = s.arrs a) ∧
            (∀ r < r_base, s'.regs r = s.regs r) := by
  have hw : 1 < 2 ^ w := by omega
  have hw2 : 2 < 2 ^ w := by omega
  have h0_w : 0 < 2 ^ w := by omega
  have hm'_w : G.numActivePairs < 2 ^ w := by omega
  induction suff with
  | nil =>
    intro pref hsplit pfx extra_buf m_acc hpfx_len hm_bound
      s hsrc hZ hbuf hr0 hr1 hr3 hr4 hr5
    have hlen_pref : pref.length = G.numActivePairs := by
      have := congrArg List.length hsplit
      simp only [List.append_nil] at this
      exact this.symm
    have hcond : (Expr.op .lt (.reg (r_base + 4)) (.reg (r_base + 3))).eval w s = some 0 := by
      simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hr4, hr3, hlen_pref, hm'_w]
    refine ⟨s, 3, extra_buf, .while_false hcond, by simp, ?_, hr0, ?_, ?_,
      fun _ _ => rfl, fun _ _ => rfl⟩
    · simpa [MultiDigraph.deleteVerticesTriplesAux] using hbuf
    · simpa using hr1
    · simpa [MultiDigraph.deleteVerticesTriplesAux] using hr5
  | cons p ps ih =>
    rcases p with ⟨u, v⟩
    intro pref hsplit pfx extra_buf m_acc hpfx_len hm_bound
      s hsrc hZ hbuf hr0 hr1 hr3 hr4 hr5
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
    have hZ₁ : s₁.arrs a_Z = bitSetList Z := by rw [harr₁]; exact hZ
    have hlen_Z₁ : (s₁.arrs a_Z).length = n := by rw [hZ₁, length_bitSetList]
    have hu_lenZ : u.1 < (s₁.arrs a_Z).length := by rw [hlen_Z₁]; exact u.2
    have hv_lenZ : v.1 < (s₁.arrs a_Z).length := by rw [hlen_Z₁]; exact v.2
    let zu := if u ∈ Z then 1 else 0
    let zv := if v ∈ Z then 1 else 0
    have hzu_eq : (s₁.arrs a_Z)[u.1]'hu_lenZ = zu := by simp [hZ₁, bitSetList, zu]
    have hzv_eq : (s₁.arrs a_Z)[v.1]'hv_lenZ = zv := by simp [hZ₁, bitSetList, zv]
    have hzu_w : zu < 2 ^ w := by dsimp [zu]; split_ifs <;> omega
    have hzv_w : zv < 2 ^ w := by dsimp [zv]; split_ifs <;> omega
    have hzuv_w : zu + zv < 2 ^ w := by dsimp [zu, zv]; split_ifs <;> omega
    -- 2. assign (r_base + 9) (a_Z[u] + a_Z[v])
    let s₂ := s₁.setReg (r_base + 9) (zu + zv)
    have hex₂ : Exec w (.assign (r_base + 9)
        (.op .add (.read a_Z (.reg (r_base + 7))) (.read a_Z (.reg (r_base + 8))))) s₁ s₂ 6 :=
      .assign (by simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord,
        hr7_1, hr8_1, hu_w, hv_w, hu_lenZ, hv_lenZ, hzu_eq, hzv_eq, hzu_w, hzv_w, hzuv_w])
    have hsplit' : G.activePairsList = (pref ++ [(u, v)]) ++ ps := by
      simp [hsplit, List.append_assoc]
    -- 3. Branch on `u ∉ Z ∧ v ∉ Z`
    by_cases hkeep : u ∉ Z ∧ v ∉ Z
    · have hzuv_0 : zu + zv = 0 := by dsimp [zu, zv]; simp [hkeep.1, hkeep.2]
      have hcond_z : (Expr.op .eq (.reg (r_base + 9)) (.const 0)).eval w s₂ = some 1 := by
        simp [s₂, Expr.eval, BinOp.eval, BinOp.raw, checkWord, hzuv_0, h0_w, hw]
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
          (List.filter (fun p => decide (p.1 ∉ Z ∧ p.2 ∉ Z)) ((u, v) :: ps)).length =
            (List.filter (fun p => decide (p.1 ∉ Z ∧ p.2 ∉ Z)) ps).length + 1 := by
        simp [hkeep]
      have hdel_uv :
          G.deleteVerticesTriplesAux Z ((u, v) :: ps) =
            u.1 :: v.1 :: m :: G.deleteVerticesTriplesAux Z ps := by
        simp [MultiDigraph.deleteVerticesTriplesAux, hkeep, m]
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
          (.ite (.op .eq (.reg (r_base + 9)) (.const 0))
            (.seq (.assign (r_base + 9) (.read a_src (.op .add (.reg (r_base + 6)) (.const 2))))
              (.seq (bufPush3 a_buf (r_base + 5) (r_base + 7) (r_base + 8) (r_base + 9))
                (.assign (r_base + 1) (.op .add (.reg (r_base + 1)) (.const 1)))))
            .skip)
          s₂ s₅ (3 + (5 + (t₄ + 4))) :=
        .ite_true hcond_z (by omega) (.seq hex₃ (.seq hex₄ hex₅))
      have hex_body : Exec w (deleteVerticesZBody a_src a_Z a_buf r_base) s s₅
          (t₁ + (6 + (3 + (5 + (t₄ + 4))))) :=
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
          (m_acc + 1) + (ps.filter (fun p => decide (p.1 ∉ Z ∧ p.2 ∉ Z))).length ≤
            G.numActivePairs := by
        rw [hflt_uv] at hm_bound; omega
      rcases ih (pref ++ [(u, v)]) hsplit' (pfx ++ [u.1, v.1, m]) extra_buf (m_acc + 1)
          (by simp [hpfx_len]; omega) hm_bound' (s := s₆)
          (by simp only [s₆, s₅, State.setReg_arrs]; rw [harr₄ a_src hne_sb]; simp [s₃, s₂, harr₁, hsrc])
          (by simp only [s₆, s₅, State.setReg_arrs]; rw [harr₄ a_Z hne_zb]; simp [s₃, s₂, harr₁, hZ])
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
      refine ⟨s₇, 3 + ((t₁ + (6 + (3 + (5 + (t₄ + 4))))) + 4) + t₇, extra_buf',
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
    · have hzuv_ne : zu + zv ≠ 0 := by
        dsimp [zu, zv]
        by_cases hu : u ∈ Z <;> by_cases hv : v ∈ Z
        · simp [hu, hv]
        · simp [hu, hv]
        · simp [hu, hv]
        · exfalso; exact hkeep ⟨hu, hv⟩
      have hcond_z : (Expr.op .eq (.reg (r_base + 9)) (.const 0)).eval w s₂ = some 0 := by
        simp [s₂, Expr.eval, BinOp.eval, BinOp.raw, checkWord, hzuv_w, h0_w]
        split_ifs <;> omega
      have hex_ite : Exec w
          (.ite (.op .eq (.reg (r_base + 9)) (.const 0))
            (.seq (.assign (r_base + 9) (.read a_src (.op .add (.reg (r_base + 6)) (.const 2))))
              (.seq (bufPush3 a_buf (r_base + 5) (r_base + 7) (r_base + 8) (r_base + 9))
                (.assign (r_base + 1) (.op .add (.reg (r_base + 1)) (.const 1)))))
            .skip)
          s₂ s₂ (3 + 1) :=
        .ite_false hcond_z (.skip s₂)
      have hex_body : Exec w (deleteVerticesZBody a_src a_Z a_buf r_base) s s₂
          (t₁ + (6 + (3 + 1))) :=
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
          m_acc + (ps.filter (fun p => decide (p.1 ∉ Z ∧ p.2 ∉ Z))).length ≤ G.numActivePairs := by
        simpa [hkeep] using hm_bound
      rcases ih (pref ++ [(u, v)]) hsplit' pfx (extra_buf + 3) m_acc
          hpfx_len hm_bound' (s := s₃)
          (by simp [s₃, s₂, harr₁, hsrc])
          (by simp [s₃, s₂, harr₁, hZ])
          hbuf₃
          (by simp [s₃, s₂, hreg₁ r_base (by omega) (by omega) (by omega), hr0])
          (by simp [s₃, s₂, hreg₁ (r_base + 1) (by omega) (by omega) (by omega), hr1])
          (by simp [s₃, s₂, hreg₁ (r_base + 3) (by omega) (by omega) (by omega), hr3])
          (by simp [s₃, k])
          (by simp [s₃, s₂, hreg₁ (r_base + 5) (by omega) (by omega) (by omega), hr5]) with
        ⟨s₄, t₄, extra_buf', hex₄, ht₄, hbuf₄, hr0_4, hr1_4, hr5_4, harr₄, hreg₄⟩
      refine ⟨s₄, 3 + ((t₁ + (6 + (3 + 1))) + 4) + t₄, extra_buf',
        .while_true hcond (by omega) (.seq hex_body hex_inc) hex₄,
        by simp only [List.length_cons]; omega,
        by simpa [MultiDigraph.deleteVerticesTriplesAux, hkeep] using hbuf₄,
        hr0_4,
        by simpa [hkeep] using hr1_4,
        by simpa [MultiDigraph.deleteVerticesTriplesAux, hkeep] using hr5_4,
        fun a ha => by rw [harr₄ a ha]; simp [s₃, s₂, harr₁],
        fun r hr => by
          rw [hreg₄ r hr]
          simp [s₃, s₂,
            State.setReg_regs_ne _ _ (by omega : (r : Reg) ≠ r_base + 4),
            State.setReg_regs_ne _ _ (by omega : (r : Reg) ≠ r_base + 9),
            hreg₁ r (by omega) (by omega) (by omega)]⟩

/-- Specification for `deleteVerticesZProg`: builds `(G.deleteVertices Z).enc` in `a_dst` in
`O(G.numActivePairs + 1)` steps. -/
theorem deleteVerticesZProg_exec {w n : ℕ} (G : MultiDigraph n) (Z : Finset (Fin n))
    (a_src a_Z a_buf a_dst : ℕ) (r_base : ℕ)
    (hne_sb : a_src ≠ a_buf) (hne_zb : a_Z ≠ a_buf) (hne_bd : a_buf ≠ a_dst)
    (hw3 : 3 < 2 ^ w) (hn_w : n < 2 ^ w)
    (hm3_w : 2 + 3 * G.numActivePairs < 2 ^ w)
    (hedges_w : G.numEdges < 2 ^ w)
    {s : State}
    (hsrc : s.arrs a_src = G.enc)
    (hZ : s.arrs a_Z = bitSetList Z) :
    ∃ s' t,
      Exec w (deleteVerticesZProg a_src a_Z a_buf a_dst r_base) s s' t ∧
      t ≤ 120 * G.numActivePairs + 80 ∧
      s'.arrs a_dst = (G.deleteVertices Z).enc ∧
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
  -- 8. Run `deleteVerticesZLoop_exec`
  have hbuf₈ : s₈.arrs a_buf = [n, 0] ++ List.replicate (3 * G.activePairsList.length + 0) 0 := by
    simp only [s₈, s₇, s₆, s₅, State.setReg_arrs, State.writeArr_arrs_self,
      State.setArr_arrs_self, MultiDigraph.numActivePairs]
    rw [show 2 + 3 * G.activePairsList.length = 2 + (3 * G.activePairsList.length + 0) by omega,
      List.replicate_add]
    rfl
  have hm_bound₀ :
      0 + (G.activePairsList.filter (fun p => decide (p.1 ∉ Z ∧ p.2 ∉ Z))).length ≤
        G.numActivePairs := by
    simp only [Nat.zero_add, MultiDigraph.numActivePairs]
    exact List.length_filter_le _ _
  rcases deleteVerticesZLoop_exec G Z a_src a_Z a_buf r_base hne_sb hne_zb hw3 hn_w hm3_w hedges_w
      G.activePairsList [] (by simp) [n, 0] 0 0 (by simp) hm_bound₀ (s := s₈)
      (by simp [s₈, s₇, s₆, s₅, s₄, s₃, s₂, s₁, show (a_src : Arr) ≠ a_buf from hne_sb, hsrc])
      (by simp [s₈, s₇, s₆, s₅, s₄, s₃, s₂, s₁, show (a_Z : Arr) ≠ a_buf from hne_zb, hZ])
      hbuf₈
      (by simp [s₈, s₇, s₆, s₅, s₄, s₃, s₂, s₁, State.setReg])
      (by simp [s₈, s₇, s₆, s₅, s₄, s₃, State.setReg])
      (by simp [s₈, s₇, s₆, s₅, s₄, s₃, s₂, State.setReg])
      (by simp [s₈])
      (by simp [s₈, s₇, State.setReg]) with
    ⟨s₉, t₉, extra_buf', hex₉, ht₉, hbuf₉, _, hr1_9, hr5_9, harr₉, hreg₉⟩
  simp only [Nat.zero_add] at hr1_9
  let m_del := (G.activePairsList.filter (fun p => decide (p.1 ∉ Z ∧ p.2 ∉ Z))).length
  have hr1_9' : s₉.regs (r_base + 1) = m_del := hr1_9
  have hm_del_le : m_del ≤ G.numActivePairs := List.length_filter_le _ _
  have hm_del_w : m_del < 2 ^ w := by omega
  have hlen_enc_del : ([n, m_del] ++ G.deleteVerticesTriplesAux Z G.activePairsList).length =
      2 + 3 * m_del := by
    simp [MultiDigraph.length_deleteVerticesTriplesAux, m_del]; omega
  have hr5_9' : s₉.regs (r_base + 5) = 2 + 3 * m_del := by
    rw [hr5_9]
    simp [MultiDigraph.length_deleteVerticesTriplesAux, m_del]
    omega
  -- 9. write a_buf 1 (.reg (r_base + 1))
  let s₁₀ := s₉.writeArr a_buf 1 m_del
  have hex₁₀ : Exec w (.write a_buf (.const 1) (.reg (r_base + 1))) s₉ s₁₀ 3 :=
    .write (by simp [Expr.eval, checkWord, hw])
      (by simp only [Expr.eval, hr1_9', checkWord_eq_some, and_true]; exact hm_del_w)
      (by rw [hbuf₉]; simp)
  have hbuf₁₀ : s₁₀.arrs a_buf =
      [] ++ (G.deleteVertices Z).enc ++ List.replicate extra_buf' 0 := by
    simp only [s₁₀, State.writeArr_arrs_self, hbuf₉, List.nil_append,
      MultiDigraph.enc_deleteVertices_eq, m_del]
    rfl
  -- 10. readSliceProg a_buf 0 a_dst (.reg (r_base + 5)) (r_base + 6)
  have hall_del_w : ∀ x ∈ (G.deleteVertices Z).enc, x < 2 ^ w := by
    intro x hx
    simp only [MultiDigraph.enc, List.cons_append, List.nil_append, List.mem_cons] at hx
    rcases hx with rfl | rfl | hx
    · exact hn_w
    · exact Nat.lt_of_le_of_lt (G.numActivePairs_deleteVertices_le Z) hm'_w
    · exact all_lt_flatTriples (G.deleteVertices Z) (G.deleteVertices Z).activePairsList hn_w
        (fun q _ => Nat.lt_of_le_of_lt
          (le_trans ((G.deleteVertices Z).edgeMult_le_numEdges q.1 q.2)
            (G.numEdges_deleteVertices_le Z))
          hedges_w) x hx
  have hlen_del_eq : (G.deleteVertices Z).enc.length = 2 + 3 * m_del := by
    rw [MultiDigraph.enc_deleteVertices_eq]
    exact hlen_enc_del
  have hoff_w : 0 + (2 + 3 * m_del) < 2 ^ w := by omega
  rcases readSliceProg_exec a_buf a_dst (.const 0) (r_base + 5) (r_base + 6)
      hne_bd (by omega)
      [] (G.deleteVertices Z).enc (List.replicate extra_buf' 0)
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

/-! ### Section 3: Word RAM Gadget 2, Pointwise Union of Bitsets `X' = X ∪ Z` -/

/-- Loop body of `unionBitSetProg`: sets `a_dst[r_i] := 0` if `a_X[r_i] + a_Z[r_i] == 0`, else `1`. -/
def unionBitSetBody (a_X a_Z a_dst : Arr) (r_i : Reg) : Cmd :=
  .ite (.op .eq (.op .add (.read a_X (.reg r_i)) (.read a_Z (.reg r_i))) (.const 0))
    (.write a_dst (.reg r_i) (.const 0))
    (.write a_dst (.reg r_i) (.const 1))

/-- Word RAM program computing `bitSetList (X ∪ Z)` in `a_dst` from `a_X = bitSetList X` and
`a_Z = bitSetList Z` of length `r_n = n`, using loop register `r_i`. -/
def unionBitSetProg (a_X a_Z a_dst : Arr) (r_n r_i : Reg) : Cmd :=
  .seq (.alloc a_dst (.reg r_n))
    (.seq (.assign r_i (.const 0))
      (forUp r_i (.reg r_n) (unionBitSetBody a_X a_Z a_dst r_i)))

theorem unionBitSetProg_exec {w n : ℕ} (X Z : Finset (Fin n))
    (a_X a_Z a_dst : ℕ) (r_n r_i : ℕ)
    (hne_Xd : a_X ≠ a_dst) (hne_Zd : a_Z ≠ a_dst) (hne_ni : r_n ≠ r_i)
    (hw2 : 2 < 2 ^ w) (hn_w : n < 2 ^ w)
    {s : State}
    (hX : s.arrs a_X = bitSetList X)
    (hZ : s.arrs a_Z = bitSetList Z)
    (hrn : s.regs r_n = n) :
    ∃ s' t,
      Exec w (unionBitSetProg a_X a_Z a_dst r_n r_i) s s' t ∧
      t ≤ 25 * n + 6 ∧
      s'.arrs a_dst = bitSetList (X ∪ Z) ∧
      (∀ a : ℕ, a ≠ a_dst → s'.arrs a = s.arrs a) ∧
      (∀ r : ℕ, r ≠ r_i → s'.regs r = s.regs r) := by
  have h0_w : 0 < 2 ^ w := by omega
  have hw : 1 < 2 ^ w := by omega
  let s₁ := s.setArr a_dst (List.replicate n 0)
  have hex₁ : Exec w (.alloc a_dst (.reg r_n)) s s₁ (1 + n) :=
    .alloc (by simp [Expr.eval, checkWord, hrn, hn_w])
  let s₂ := s₁.setReg r_i 0
  have hex₂ : Exec w (.assign r_i (.const 0)) s₁ s₂ 2 :=
    .assign (by simp [Expr.eval, checkWord, h0_w])
  let Inv (k : ℕ) (st : State) : Prop :=
    (∃ (hlen : (st.arrs a_dst).length = n),
      ∀ j : Fin n, j.1 < k →
        (st.arrs a_dst)[j.1]'(by rw [hlen]; exact j.2) =
          if j ∈ X ∪ Z then 1 else 0) ∧
    st.regs r_n = n ∧
    st.regs r_i = k ∧
    (∀ a : ℕ, a ≠ a_dst → st.arrs a = s.arrs a) ∧
    (∀ r : ℕ, r ≠ r_i → st.regs r = s.regs r)
  have hInv₀ : Inv 0 s₂ := by
    refine ⟨⟨by simp [s₂, s₁], fun _ hj => by omega⟩,
      by simp [s₂, s₁, State.setReg_regs_ne _ _ hne_ni, hrn],
      by simp [s₂],
      fun a ha => by simp [s₂, s₁, show (a : Arr) ≠ a_dst from ha],
      fun r hr => by simp [s₂, s₁, State.setReg_regs_ne _ _ hr]⟩
  have hLoop :
      ⦃Inv 0⦄[w]
        forUp r_i (.reg r_n) (unionBitSetBody a_X a_Z a_dst r_i)
      ⦃Inv n⦄ ≤ fun _ => 3 + n * (7 + 10) := by
    apply Triple.forUp_const Inv n 10 hw hn_w
    · intro k _ st ⟨_, hrn_k, hri_k, _, _⟩
      exact ⟨hri_k, by simp [Expr.eval, checkWord, hrn_k, hn_w]⟩
    · intro k hk st ⟨⟨hlen_k, hbuf_k⟩, hrn_k, hri_k, harr_other, hreg_other⟩
      have hk_w : k < 2 ^ w := by omega
      let u : Fin n := ⟨k, hk⟩
      have hX_st : st.arrs a_X = bitSetList X := (harr_other a_X hne_Xd).trans hX
      have hZ_st : st.arrs a_Z = bitSetList Z := (harr_other a_Z hne_Zd).trans hZ
      have hk_lenX : k < (st.arrs a_X).length := by rw [hX_st, length_bitSetList]; exact hk
      have hk_lenZ : k < (st.arrs a_Z).length := by rw [hZ_st, length_bitSetList]; exact hk
      let bx := if u ∈ X then 1 else 0
      let bz := if u ∈ Z then 1 else 0
      have hbx_eq : (st.arrs a_X)[k]'hk_lenX = bx := by simp [hX_st, bitSetList, bx, u]
      have hbz_eq : (st.arrs a_Z)[k]'hk_lenZ = bz := by simp [hZ_st, bitSetList, bz, u]
      have hbx_w : bx < 2 ^ w := by dsimp [bx]; split_ifs <;> omega
      have hbz_w : bz < 2 ^ w := by dsimp [bz]; split_ifs <;> omega
      have hbxz_w : bx + bz < 2 ^ w := by dsimp [bx, bz]; split_ifs <;> omega
      let b_union := if u ∈ X ∪ Z then 1 else 0
      let st₁ := st.writeArr a_dst k b_union
      have hex_body : Exec w (unionBitSetBody a_X a_Z a_dst r_i) st st₁ 10 := by
        by_cases hu_mem : u ∈ X ∪ Z
        · have hbxz_ne : bx + bz ≠ 0 := by
            dsimp [bx, bz]
            rcases Finset.mem_union.mp hu_mem with huX | huZ
            · simp [huX]
            · by_cases huX : u ∈ X <;> simp [huX, huZ]
          have hcond : (.op .eq (.op .add (.read a_X (.reg r_i)) (.read a_Z (.reg r_i)))
              (.const 0) : Expr).eval w st = some 0 := by
            simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hri_k, hk_w,
              hk_lenX, hk_lenZ, hbx_eq, hbz_eq, hbx_w, hbz_w, hbxz_w, h0_w]
            split_ifs <;> omega
          have hb_eq : b_union = 1 := by simp [b_union, hu_mem]
          have hex_w : Exec w (.write a_dst (.reg r_i) (.const 1)) st st₁ 3 := by
            dsimp [st₁]; rw [hb_eq]
            exact .write (by simp [Expr.eval, checkWord, hri_k, hk_w])
              (by simp [Expr.eval, checkWord, hw])
              (by simp [hlen_k, hk])
          exact .ite_false hcond hex_w
        · have huX : u ∉ X := fun h => hu_mem (Finset.mem_union_left Z h)
          have huZ : u ∉ Z := fun h => hu_mem (Finset.mem_union_right X h)
          have hbxz_0 : bx + bz = 0 := by dsimp [bx, bz]; simp [huX, huZ]
          have hcond : (.op .eq (.op .add (.read a_X (.reg r_i)) (.read a_Z (.reg r_i)))
              (.const 0) : Expr).eval w st = some 1 := by
            simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hri_k, hk_w,
              hk_lenX, hk_lenZ, hbx_eq, hbz_eq, hbx_w, hbz_w, hbxz_0, h0_w, hw]
          have hb_eq : b_union = 0 := by simp [b_union, hu_mem]
          have hex_w : Exec w (.write a_dst (.reg r_i) (.const 0)) st st₁ 3 := by
            dsimp [st₁]; rw [hb_eq]
            exact .write (by simp [Expr.eval, checkWord, hri_k, hk_w])
              (by simp [Expr.eval, checkWord, h0_w])
              (by simp [hlen_k, hk])
          exact .ite_true hcond (by decide) hex_w
      refine ⟨st₁, 10, hex_body, le_rfl,
        ⟨⟨by simp [st₁, hlen_k], fun j hj => ?_⟩,
         by simp [st₁, State.setReg_regs_ne _ _ hne_ni, hrn_k],
         by simp [st₁],
         fun a ha => by simp [st₁, show (a : Arr) ≠ a_dst from ha, harr_other a ha],
         fun r hr => by simp [st₁, State.setReg_regs_ne _ _ hr, hreg_other r hr]⟩,
        by simp [st₁, hri_k]⟩
      dsimp only [st₁]
      simp only [State.setReg_arrs, State.writeArr_arrs_self]
      by_cases hjk : j.1 = k
      · have hju : j = u := Fin.ext hjk
        subst hjk
        simp [b_union, hju]
      · rw [List.getElem_set_ne (Ne.symm hjk)]
        exact hbuf_k j (by omega)
  rcases hLoop s₂ hInv₀ with
    ⟨s₃, t₃, hex₃, ht₃, ⟨hlen₃, hbuf₃⟩, _, _, harr₃, hreg₃⟩
  dsimp only at ht₃
  have hdst₃ : s₃.arrs a_dst = bitSetList (X ∪ Z) := by
    apply List.ext_getElem
    · simp [hlen₃, length_bitSetList]
    · intro i hi₁ hi₂
      simp only [bitSetList, List.getElem_ofFn]
      exact hbuf₃ ⟨i, by omega⟩ (by omega)
  refine ⟨s₃, (1 + n) + (2 + t₃), .seq hex₁ (.seq hex₂ hex₃), by omega,
    hdst₃, harr₃, hreg₃⟩

/-! ### Section 4: Word RAM Gadget 3, Unpacking `encBitSetsUpTo X p` -/

/-- Unpack the first `j` branch-set bitlists (`j ≤ p`) from `a_src` into arrays `18 .. 18 + j - 1`,
where `r_26 = n` and `r_55` holds the current offset `j * n` in `a_src`. -/
def unpackCliqueModelUpTo (a_src : Arr) : ℕ → Cmd
  | 0 => .assign 55 (.const 0)
  | j + 1 =>
    .seq (unpackCliqueModelUpTo a_src j)
      (.seq (readSliceProg a_src (.reg 55) (18 + j) (.reg 26) 56)
        (.assign 55 (.op .add (.reg 55) (.reg 26))))

theorem unpackCliqueModelUpTo_exec {w n p : ℕ} (X : Fin p → Finset (Fin n))
    (a_src : ℕ) (ha_src : 18 + p ≤ a_src)
    (hw : 1 < 2 ^ w) (hn_w : n < 2 ^ w) (hpn_w : p * n < 2 ^ w) :
    ∀ j (hj : j ≤ p) {s : State}
      (_hsrc : s.arrs a_src = encBitSetsUpTo X p)
      (_hr26 : s.regs 26 = n),
      ∃ s' t,
        Exec w (unpackCliqueModelUpTo a_src j) s s' t ∧
        t ≤ 2 + j * (16 * n + 14) ∧
        s'.arrs a_src = encBitSetsUpTo X p ∧
        s'.regs 55 = j * n ∧
        (∀ k (hk : k < j), IsBitSet (X ⟨k, Nat.lt_of_lt_of_le hk hj⟩) (18 + k) s') ∧
        (∀ a : ℕ, a < 18 ∨ 18 + j ≤ a → s'.arrs a = s.arrs a) ∧
        (∀ r : ℕ, r < 55 → s'.regs r = s.regs r)
  | 0, _, s, hsrc, _ => by
    have h0_w : 0 < 2 ^ w := by omega
    let s₁ := s.setReg 55 0
    have hex₁ : Exec w (.assign 55 (.const 0)) s s₁ 2 :=
      .assign (by simp [Expr.eval, checkWord, h0_w])
    exact ⟨s₁, 2, hex₁, by omega, hsrc, by simp [s₁],
      fun _ hk => by omega,
      fun _ _ => rfl,
      fun r hr => by dsimp [s₁]; exact State.setReg_regs_ne s 0 (Nat.ne_of_lt hr)⟩
  | j + 1, hj, s, hsrc, hr26 => by
    have hj_lt : j < p := by omega
    rcases unpackCliqueModelUpTo_exec X a_src ha_src hw hn_w hpn_w j (by omega) hsrc hr26 with
      ⟨s₁, t₁, hex₁, ht₁, hsrc₁, hr55_1, hbits₁, harr₁, hreg₁⟩
    have hjn_le : j * n ≤ p * n := Nat.mul_le_mul_right n (by omega)
    have hjp1n_le : (j + 1) * n ≤ p * n := Nat.mul_le_mul_right n hj
    have hjn_w : j * n < 2 ^ w := by omega
    have hjp1n_w : j * n + n < 2 ^ w := by
      have : j * n + n = (j + 1) * n := (Nat.succ_mul j n).symm
      omega
    rcases encBitSetsUpTo_eq_append X (j + 1) hj with ⟨suf, hsuf⟩
    have hsrc₁_split : s₁.arrs a_src =
        encBitSetsUpTo X j ++ bitSetList (X ⟨j, hj_lt⟩) ++ suf := by
      rw [hsrc₁, hsuf]
      simp [encBitSetsUpTo, hj_lt, List.append_assoc]
    have hpre_len : (encBitSetsUpTo X j).length = j * n :=
      length_encBitSetsUpTo X j (by omega)
    have hmid_w : ∀ b ∈ bitSetList (X ⟨j, hj_lt⟩), b < 2 ^ w := by
      intro b hb
      rcases List.mem_iff_getElem.mp hb with ⟨idx, hidx, rfl⟩
      have hle1 := getElem_bitSetList_le_one (X ⟨j, hj_lt⟩) idx hidx
      omega
    have hr26_1 : s₁.regs 26 = n := (hreg₁ 26 (by decide)).trans hr26
    rcases readSliceProg_exec a_src (18 + j) (.reg 55) 26 56
        (by dsimp [Arr]; omega) (by decide)
        (encBitSetsUpTo X j) (bitSetList (X ⟨j, hj_lt⟩)) suf
        hpre_len (length_bitSetList _) hmid_w hw hjp1n_w
        (s := s₁)
        (by simp [Expr.eval, checkWord, hr55_1, hjn_w])
        hsrc₁_split
        hr26_1 with
      ⟨s₂, t₂, hex₂, ht₂, hdst₂, harr₂, hreg₂⟩
    dsimp [Expr.cost] at ht₂
    have hr55_2 : s₂.regs 55 = j * n := (hreg₂ 55 (by decide)).trans hr55_1
    have hr26_2 : s₂.regs 26 = n := (hreg₂ 26 (by decide)).trans hr26_1
    let s₃ := s₂.setReg 55 ((j + 1) * n)
    have hex₃ : Exec w (.assign 55 (.op .add (.reg 55) (.reg 26))) s₂ s₃ 4 :=
      .assign (by
        have hadd : j * n + n = (j + 1) * n := (Nat.succ_mul j n).symm
        simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hr55_2, hr26_2,
          hjn_w, hn_w, hadd, show (j + 1) * n < 2 ^ w by omega])
    have hmul : (j + 1) * (16 * n + 14) = j * (16 * n + 14) + (16 * n + 14) :=
      Nat.succ_mul j _
    refine ⟨s₃, t₁ + (t₂ + 4), .seq hex₁ (.seq hex₂ hex₃), by rw [hmul]; omega,
      by simp [s₃, harr₂ a_src (by dsimp [Arr]; omega), hsrc₁],
      by simp [s₃],
      fun k hk => ?_,
      fun a ha => ?_,
      fun r hr => by
        dsimp only [s₃]
        rw [State.setReg_regs_ne _ _ (Nat.ne_of_lt hr),
          hreg₂ r (Nat.lt_succ_of_lt hr), hreg₁ r hr]⟩
    · rcases Nat.lt_succ_iff_lt_or_eq.mp hk with hk_lt | rfl
      · exact (hbits₁ k hk_lt).of_arr_eq
          (by simp [s₃, harr₂ (18 + k) (by dsimp [Arr]; omega)])
      · exact IsBitSet.of_bitSetList (X ⟨k, hj_lt⟩) (18 + k) s₃ (by simp [s₃, hdst₂])
    · simp only [s₃, State.setReg_arrs]
      rw [harr₂ a (by dsimp [Arr]; omega)]
      exact harr₁ a (by omega)

/-- Unpack `p` bitsets of length `n` from array `a_src` into arrays `18, ..., 18 + p - 1`. -/
def unpackCliqueModelProg (a_src p : ℕ) : Cmd :=
  unpackCliqueModelUpTo a_src p

theorem unpackCliqueModelProg_exec {w n : ℕ} (a_src p : ℕ) (X : Fin p → Finset (Fin n))
    (ha_src : 18 + p ≤ a_src)
    (hw : 1 < 2 ^ w) (hn_w : n < 2 ^ w) (hpn_w : (p + 2) * n < 2 ^ w)
    {s : State}
    (hsrc : s.arrs a_src = encBitSetsUpTo X p)
    (hr26 : s.regs 26 = n) :
    ∃ s' t,
      Exec w (unpackCliqueModelProg a_src p) s s' t ∧
      t ≤ 2 + p * (16 * n + 14) ∧
      (∀ k : Fin p, IsBitSet (X k) (18 + k.1) s') ∧
      (∀ a : ℕ, a < 18 ∨ 18 + p ≤ a → s'.arrs a = s.arrs a) ∧
      (∀ r : ℕ, r < 55 → s'.regs r = s.regs r) := by
  have hp_w : p * n < 2 ^ w :=
    Nat.lt_of_le_of_lt (Nat.mul_le_mul_right n (by omega : p ≤ p + 2)) hpn_w
  rcases unpackCliqueModelUpTo_exec X a_src ha_src hw hn_w hp_w p le_rfl hsrc hr26 with
    ⟨s', t, hex, ht, _, _, hbits, harr, hreg⟩
  exact ⟨s', t, hex, ht, fun k => hbits k.1 k.2, harr, hreg⟩

/-! ### Section 5: Word RAM Gadget 4, Deleting an Irrelevant Vertex from Arrays `17` and `9` -/

/-- Delete vertex `r_25` from `G_i` (in array `17`, writing `(G_i.deleteVertex v_i).enc` to `18 + p`
and updating `r_26, r_27, r_28`) and from `Z_i` (in array `9`, writing
`bitSetList (deleteVertexFinset Z_i v_i)` to `18 + p + 1`), then set `r_40 := 1`. -/
def deleteFrom17And9Prog (p : ℕ) : Cmd :=
  .seq (deleteVertexMultiDigraphProg 17 2 (18 + p) 25 26)
    (.seq (deleteNthArrProg 9 2 26 25 29)
      (.seq (readSliceProg 9 (.const 0) (18 + p + 1) (.reg 26) 29)
        (.assign 40 (.const 1))))

theorem deleteFrom17And9Prog_exec {w n' : ℕ} (p : ℕ)
    (G_i : MultiDigraph (n' + 1)) (Z_i : Finset (Fin (n' + 1))) (v_i : Fin (n' + 1))
    (hw3 : 3 < 2 ^ w) (hnr_w : n' + 1 < 2 ^ w)
    (hm3_w : 2 + 3 * G_i.numActivePairs < 2 ^ w)
    (hedges_w : G_i.numEdges < 2 ^ w)
    {s : State}
    (hG17 : s.arrs 17 = G_i.enc)
    (hZ9 : s.arrs 9 = bitSetList Z_i)
    (hr25 : s.regs 25 = v_i.1) :
    ∃ s' t,
      Exec w (deleteFrom17And9Prog p) s s' t ∧
      t ≤ 130 * G_i.numActivePairs + 65 * (n' + 1) + 120 ∧
      s'.arrs (18 + p) = (G_i.deleteVertex v_i).enc ∧
      s'.arrs (18 + p + 1) = bitSetList (deleteVertexFinset Z_i v_i) ∧
      s'.regs 26 = n' ∧
      s'.regs 27 = (G_i.deleteVertex v_i).numActivePairs ∧
      s'.regs 28 = (G_i.deleteVertex v_i).numEdges ∧
      s'.regs 40 = 1 := by
  have hw : 1 < 2 ^ w := by omega
  have hn'_w : n' < 2 ^ w := by omega
  have hG17' : s.arrs 17 = G_i.enc ++ [] := by simp [hG17]
  have hedges_del_w : (G_i.deleteVertex v_i).numEdges < 2 ^ w :=
    Nat.lt_of_le_of_lt (Alg65Trace.numEdges_deleteVertex_le G_i v_i) hedges_w
  -- 1. deleteVertexMultiDigraphProg 17 2 (18 + p) 25 26
  rcases deleteVertexMultiDigraphProg_exec G_i v_i [] 17 2 (18 + p) 25 26
      (by decide) (by omega) (by decide) hw3 hnr_w hm3_w hedges_del_w
      hG17' hr25 with
    ⟨s₁, t₁, hex₁, ht₁, hG_arr₁, hr26_1, hr27_1, hr28_1, harr₁, hreg₁⟩
  -- 2. deleteNthArrProg 9 2 26 25 29
  have hr25_1 : s₁.regs 25 = v_i.1 := (hreg₁ 25 (by decide)).trans hr25
  have hZ_arr₁ : s₁.arrs 9 = List.ofFn (fun u : Fin (n' + 1) => if u ∈ Z_i then 1 else 0) := by
    rw [harr₁ 9 (by decide) (by omega)]; exact hZ9
  rcases deleteNthArrProg_exec (fun u : Fin (n' + 1) => if u ∈ Z_i then 1 else 0) v_i
      9 2 26 25 29 (by decide) (by decide) (by decide) hw hnr_w
      (fun _ => by split_ifs <;> omega) hZ_arr₁ hr26_1 hr25_1 with
    ⟨s₂, t₂, hex₂, ht₂, hZ_arr₂, harr₂, hreg₂⟩
  rw [← bitSetList_deleteVertexFinset Z_i v_i] at hZ_arr₂
  -- 3. copyListProg_exec 9 (18 + p + 1) 26 29
  have hZ_next_w : ∀ b ∈ bitSetList (deleteVertexFinset Z_i v_i), b < 2 ^ w := by
    intro b hb
    rcases List.mem_iff_getElem.mp hb with ⟨idx, hidx, rfl⟩
    have hle1 := getElem_bitSetList_le_one (deleteVertexFinset Z_i v_i) idx hidx
    omega
  rcases copyListProg_exec 9 (18 + p + 1) 26 29 (by omega) (by decide)
      (bitSetList (deleteVertexFinset Z_i v_i)) (length_bitSetList _) hZ_next_w hw hn'_w
      hZ_arr₂ (by rw [hreg₂ 26 (by decide)]; exact hr26_1) with
    ⟨s₃, t₃, hex₃, ht₃, hZ_arr₃, harr₃, hreg₃⟩
  -- 4. assign 40 (.const 1)
  let s₄ := s₃.setReg 40 1
  have hex₄ : Exec w (.assign 40 (.const 1)) s₃ s₄ 2 :=
    .assign (by simp [Expr.eval, checkWord, hw])
  refine ⟨s₄, t₁ + (t₂ + (t₃ + 2)), .seq hex₁ (.seq hex₂ (.seq hex₃ hex₄)), by omega,
    by simp [s₄, harr₃ (18 + p) (by omega), harr₂ (18 + p) (by omega) (by omega), hG_arr₁],
    by simp [s₄, hZ_arr₃],
    by simp [s₄, hreg₃ 26 (by decide), hreg₂ 26 (by decide), hr26_1],
    by simp [s₄, hreg₃ 27 (by decide), hreg₂ 27 (by decide), hr27_1],
    by simp [s₄, hreg₃ 28 (by decide), hreg₂ 28 (by decide), hr28_1],
    by simp [s₄]⟩

/-! ### Section 6: The Recursion of Algorithm (10.5) (Steps (2)–(4)) -/

theorem sumEdgeMult_ge_length {n : ℕ} (G : MultiDigraph n) :
    ∀ (ps : List (Fin n × Fin n)),
      (∀ p ∈ ps, 0 < G.edgeMult p.1 p.2) → ps.length ≤ G.sumEdgeMult ps
  | [], _ => le_rfl
  | p :: ps, hpos => by
    have hp : 1 ≤ G.edgeMult p.1 p.2 := hpos p List.mem_cons_self
    have hps := sumEdgeMult_ge_length G ps (fun q hq => hpos q (List.mem_cons_of_mem p hq))
    simp only [List.length_cons, MultiDigraph.sumEdgeMult]
    omega

theorem MultiDigraph.numActivePairs_le_numEdges {n : ℕ} (G : MultiDigraph n) :
    G.numActivePairs ≤ G.numEdges := by
  rw [← G.sumEdgeMult_activePairsList]
  exact sumEdgeMult_ge_length G G.activePairsList
    (fun p hp => (G.mem_activePairsList p).mp hp)

theorem encFolioSetRep_castCard {q₁ q₂ δ : ℕ} (h : q₁ = q₂) (F : FolioSetRep q₁ δ) :
    encFolioSetRep (F.castCard h) = encFolioSetRep F := by
  subst h
  rfl

/-- Loop invariant at the beginning of the `i`-th iteration of the recursion of Algorithm (10.5)
(page 108): we have a multi-digraph `G_i : MultiDigraph n_i` and `Z_i ⊆ V(G_i)` with `n_i ≤ x.n`,
`Z_i.card = x.Z.card`, `G_i.numEdges ≤ alg65Const ξ δ * x.n`, and the `δ`-folio of `G_i` relative
to `Z_i` equal to that of `x.G` relative to `x.Z`. -/
structure Alg105LoopState (ξ δ : ℕ) (x : FolioInput ξ)
    (n_i : ℕ) (G_i : MultiDigraph n_i) (Z_i : Finset (Fin n_i))
    (s : State) : Prop where
  hn_le : n_i ≤ x.n
  hZ_eq : Z_i.card = x.Z.card
  hedges_le : G_i.numEdges ≤ alg65Const ξ δ * x.n
  hfolio : ∀ F : FolioSetRep Z_i.card δ,
    IsDeltaFolioRep δ G_i Z_i F → IsDeltaFolioRep δ x.G x.Z (F.castCard hZ_eq)
  hG_arr : s.arrs (18 + alg62Param ξ δ) = G_i.enc
  hZ_arr : s.arrs (18 + alg62Param ξ δ + 1) = bitSetList Z_i
  hr26 : s.regs 26 = n_i
  hr27 : s.regs 27 = G_i.numActivePairs
  hr28 : s.regs 28 = G_i.numEdges
  hr40 : s.regs 40 = 1

/-- Step (2) of GM XIII Algorithm (10.5) (page 109):
"If we obtain a branch-decomposition of $G_i \setminus Z$ of width $\le \omega$, we convert it to a
branch-decomposition of $G_i$ of width $\le \omega + \xi$, compute the $\delta$-folio of $G_i$ relative to $Z$
by (4.1), and stop." -/
def alg105Step2Prog (p : ℕ) (prog41 : Cmd) : Cmd :=
  let b := alg105ArrBase p
  .seq (.assign 55 (.op .add (.const 2) (.op .mul (.const 3) (.reg 27))))
    (.seq (readSliceProg 17 (.const 0) b (.reg 55) 56)
      (.seq (readSliceProg 9 (.const 0) (b + 1) (.reg 26) 55)
        (.seq (convertBDProg b)
          (.seq prog41
            (.assign 40 (.const 0))))))

theorem alg105Step2Prog_exec {w n_i : ℕ} (p ξ δ ω C41 c41 : ℕ) (prog41 : Cmd)
    (OutRel : FolioInput ξ → List ℕ → Prop)
    (h41 : ∀ {w n_i : ℕ} (G_i : MultiDigraph n_i) (Z_i : Finset (Fin n_i))
      (t : ℕ) (par f_tau : ℕ → ℕ) (s : State),
      let b := alg105ArrBase p
      let N := n_i + G_i.numEdges + 1
      wordSize c41 N ≤ w →
      Z_i.card ≤ ξ →
      IsWrittenDigraphBD (max ω 2 + ξ) G_i.toComputeDigraph t par f_tau →
      s.arrs b = G_i.enc →
      s.arrs (b + 1) = bitSetList Z_i →
      s.regs 26 = n_i →
      s.regs 28 = G_i.numEdges →
      s.regs 52 = t →
      (s.arrs (b + 2)).length = t →
      (∀ z < t, (s.arrs (b + 2)).getD z 0 = par z) →
      (s.arrs (b + 3)).length = G_i.numEdges →
      (∀ e < G_i.numEdges, (s.arrs (b + 3)).getD e 0 = f_tau e) →
      s.arrs (b + 5) =
        List.ofFn (fun e : Fin G_i.toComputeDigraph.numEdges => (G_i.toComputeDigraph.tail e).1) →
      s.arrs (b + 6) =
        List.ofFn (fun e : Fin G_i.toComputeDigraph.numEdges => (G_i.toComputeDigraph.head e).1) →
      ∃ (s' : State) (time : ℕ),
        Exec w prog41 s s' time ∧
        time ≤ C41 * N ∧
        ∀ (x : FolioInput ξ) (hZ_eq : Z_i.card = x.Z.card),
          (∀ F : FolioSetRep Z_i.card δ,
            IsDeltaFolioRep δ G_i Z_i F → IsDeltaFolioRep δ x.G x.Z (F.castCard hZ_eq)) →
          OutRel x (s'.arrs outArr))
    (G_i : MultiDigraph n_i) (Z_i : Finset (Fin n_i))
    (t₀ : ℕ) (par₀ f_tau₀ : ℕ → ℕ)
    (hZ_card : Z_i.card ≤ ξ)
    (hw3 : 3 < 2 ^ w)
    (hnn_w : n_i * n_i < 2 ^ w)
    (henc_w : 2 + 3 * G_i.numActivePairs < 2 ^ w)
    (hm_w : 2 * G_i.numEdges + 1 < 2 ^ w)
    (hw41 : wordSize c41 (n_i + G_i.numEdges + 1) ≤ w)
    {s : State}
    (hG17 : s.arrs 17 = G_i.enc)
    (hZ9 : s.arrs 9 = bitSetList Z_i)
    (hr26 : s.regs 26 = n_i)
    (hr27 : s.regs 27 = G_i.numActivePairs)
    (hr28 : s.regs 28 = G_i.numEdges)
    (hr52 : s.regs 52 = t₀)
    (hb2_len : (s.arrs (alg105ArrBase p + 2)).length = t₀)
    (hb2_get : ∀ z < t₀, (s.arrs (alg105ArrBase p + 2)).getD z 0 = par₀ z)
    (hb3_len : (s.arrs (alg105ArrBase p + 3)).length = (G_i.deleteVertices Z_i).numEdges)
    (hb3_get : ∀ e < (G_i.deleteVertices Z_i).numEdges,
      (s.arrs (alg105ArrBase p + 3)).getD e 0 = f_tau₀ e)
    (hbd₀ : IsWrittenDigraphBD ω (G_i.deleteVertices Z_i).toComputeDigraph t₀ par₀ f_tau₀) :
    ∃ (s' : State) (time : ℕ),
      Exec w (alg105Step2Prog p prog41) s s' time ∧
      time ≤ (450 + C41) * (n_i + G_i.numEdges + 1) ^ 2 ∧
      s'.regs 40 = 0 ∧
      ∀ (x : FolioInput ξ) (hZ_eq : Z_i.card = x.Z.card),
        (∀ F : FolioSetRep Z_i.card δ,
          IsDeltaFolioRep δ G_i Z_i F → IsDeltaFolioRep δ x.G x.Z (F.castCard hZ_eq)) →
        OutRel x (s'.arrs outArr) := by
  let b := alg105ArrBase p
  have h0_w : 0 < 2 ^ w := by omega
  have hw : 1 < 2 ^ w := by omega
  have hw2 : 2 < 2 ^ w := by omega
  have hn_w : n_i < 2 ^ w := by
    rcases Nat.eq_zero_or_pos n_i with rfl | hpos
    · omega
    · nlinarith
  have hm'_w : G_i.numActivePairs < 2 ^ w := by omega
  have hedges_w : G_i.numEdges < 2 ^ w := by omega
  -- 1. Set `r_55 := 2 + 3 * r_27` and copy `G_i.enc` from `17` to `b`
  let s₁ := s.setReg 55 (2 + 3 * G_i.numActivePairs)
  have hex₁ : Exec w (.assign 55 (.op .add (.const 2) (.op .mul (.const 3) (.reg 27)))) s s₁ 6 :=
    .assign (by simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord,
      hr27, hw2, hw3, hm'_w, show 3 * G_i.numActivePairs < 2 ^ w by omega, henc_w])
  have henc_words_w : ∀ x ∈ G_i.enc, x < 2 ^ w := by
    intro x hx
    simp only [MultiDigraph.enc, List.cons_append, List.nil_append, List.mem_cons] at hx
    rcases hx with rfl | rfl | hx
    · exact hn_w
    · exact hm'_w
    · exact all_lt_flatTriples G_i G_i.activePairsList hn_w
        (fun q _ => Nat.lt_of_le_of_lt (G_i.edgeMult_le_numEdges q.1 q.2) hedges_w) x hx
  rcases copyListProg_exec 17 b 55 56 (by dsimp [b, alg105ArrBase]; omega) (by decide)
      G_i.enc G_i.length_enc henc_words_w hw henc_w (s := s₁)
      (by simp [s₁, hG17]) (by simp [s₁]) with
    ⟨s₂, t₂, hex₂, ht₂, hb_arr₂, harr₂, hreg₂⟩
  -- 2. Copy `bitSetList Z_i` from `9` to `b + 1`
  have hZ_words_w : ∀ x ∈ bitSetList Z_i, x < 2 ^ w := by
    intro x hx
    rcases List.mem_iff_getElem.mp hx with ⟨idx, hidx, rfl⟩
    have hle1 := getElem_bitSetList_le_one Z_i idx hidx
    omega
  have hr26_2 : s₂.regs 26 = n_i := by
    rw [hreg₂ 26 (by decide)]; simp [s₁, hr26]
  have hZ9_2 : s₂.arrs 9 = bitSetList Z_i := by
    rw [harr₂ 9 (by dsimp [b, alg105ArrBase]; omega)]; exact hZ9
  rcases copyListProg_exec 9 (b + 1) 26 55 (by dsimp [b, alg105ArrBase]; omega) (by decide)
      (bitSetList Z_i) (length_bitSetList Z_i) hZ_words_w hw hn_w hZ9_2 hr26_2 with
    ⟨s₃, t₃, hex₃, ht₃, hb1_arr₃, harr₃, hreg₃⟩
  -- 3. Run `convertBDProg b`
  have hb_arr₃ : s₃.arrs b = G_i.enc := by
    rw [harr₃ b (by dsimp [b, alg105ArrBase]; omega)]; exact hb_arr₂
  have hr26_3 : s₃.regs 26 = n_i := (hreg₃ 26 (by decide)).trans hr26_2
  have hr27_3 : s₃.regs 27 = G_i.numActivePairs := by
    rw [hreg₃ 27 (by decide), hreg₂ 27 (by decide)]; simp [s₁, hr27]
  have hr28_3 : s₃.regs 28 = G_i.numEdges := by
    rw [hreg₃ 28 (by decide), hreg₂ 28 (by decide)]; simp [s₁, hr28]
  have hr52_3 : s₃.regs 52 = t₀ := by
    rw [hreg₃ 52 (by decide), hreg₂ 52 (by decide)]; simp [s₁, hr52]
  have hb2_arr₃ : s₃.arrs (b + 2) = List.ofFn (fun z : Fin t₀ => par₀ z.1) := by
    rw [harr₃ (b + 2) (by dsimp [b, alg105ArrBase]; omega),
      harr₂ (b + 2) (by dsimp [b, alg105ArrBase]; omega)]
    exact eq_ofFn_of_getD_eq hb2_len hb2_get
  have hm_del_eq : (G_i.deleteVertices Z_i).toComputeDigraph.numEdges =
      (G_i.deleteVertices Z_i).numEdges :=
    (G_i.deleteVertices Z_i).length_directedEdgesList
  have hb3_arr₃ : s₃.arrs (b + 3) =
      List.ofFn (fun e : Fin (G_i.deleteVertices Z_i).toComputeDigraph.numEdges => f_tau₀ e.1) := by
    rw [harr₃ (b + 3) (by dsimp [b, alg105ArrBase]; omega),
      harr₂ (b + 3) (by dsimp [b, alg105ArrBase]; omega)]
    exact eq_ofFn_of_getD_eq (by rw [hm_del_eq]; exact hb3_len)
      (fun e he => hb3_get e (by rw [← hm_del_eq]; exact he))
  rcases convertBDProg_exec G_i Z_i b par₀ f_tau₀ hZ_card hw3 hnn_w henc_w hm_w hbd₀
      hb_arr₃ hb1_arr₃ hr26_3 hr27_3 hr28_3 hr52_3 hb2_arr₃ hb3_arr₃ with
    ⟨s₄, t₄, t, par, f_tau, hex₄, ht₄, hr52_4, hb2_arr₄, hb3_arr₄, hb5_arr₄, hb6_arr₄,
      hbd₄, harr₄, hreg₄⟩
  -- 4. Run `prog41`
  have hb_arr₄ : s₄.arrs b = G_i.enc := (harr₄ b (by dsimp [b, Arr]; omega)).trans hb_arr₃
  have hb1_arr₄ : s₄.arrs (b + 1) = bitSetList Z_i :=
    (harr₄ (b + 1) (by dsimp [b, Arr]; omega)).trans hb1_arr₃
  have hr26_4 : s₄.regs 26 = n_i := (hreg₄ 26 (by decide)).trans hr26_3
  have hr28_4 : s₄.regs 28 = G_i.numEdges := (hreg₄ 28 (by decide)).trans hr28_3
  have hb2_len₄ : (s₄.arrs (b + 2)).length = t := by
    rw [hb2_arr₄, List.length_ofFn]
  have hb2_get₄ : ∀ z < t, (s₄.arrs (b + 2)).getD z 0 = par z := by
    intro z hz
    rw [hb2_arr₄, List.getD_eq_getElem?_getD, List.getElem?_ofFn]
    simp [hz]
  have hm_eq : G_i.toComputeDigraph.numEdges = G_i.numEdges := G_i.length_directedEdgesList
  have hb3_len₄ : (s₄.arrs (b + 3)).length = G_i.numEdges := by
    rw [hb3_arr₄, List.length_ofFn, hm_eq]
  have hb3_get₄ : ∀ e < G_i.numEdges, (s₄.arrs (b + 3)).getD e 0 = f_tau e := by
    intro e he
    rw [hb3_arr₄, List.getD_eq_getElem?_getD, List.getElem?_ofFn]
    simp [he]
  rcases h41 G_i Z_i t par f_tau s₄ hw41 hZ_card hbd₄ hb_arr₄ hb1_arr₄ hr26_4 hr28_4 hr52_4
      hb2_len₄ hb2_get₄ hb3_len₄ hb3_get₄ hb5_arr₄ hb6_arr₄ with
    ⟨s₅, t₅, hex₅, ht₅, hout₅⟩
  -- 5. `.assign 40 (.const 0)`
  let s₆ := s₅.setReg 40 0
  have hex₆ : Exec w (.assign 40 (.const 0)) s₅ s₆ 2 :=
    .assign (by simp [Expr.eval, checkWord, h0_w])
  have hpairs_le : G_i.numActivePairs ≤ G_i.numEdges := G_i.numActivePairs_le_numEdges
  let N := n_i + G_i.numEdges + 1
  have hN_pos : 1 ≤ N := by dsimp [N]; omega
  have hN_sq : N ≤ N ^ 2 := by rw [Nat.pow_two]; exact Nat.le_mul_of_pos_left N hN_pos
  have ht23_N : 6 + t₂ + t₃ + 2 ≤ 100 * N := by dsimp [N]; omega
  have ht23_N2 : 6 + t₂ + t₃ + 2 ≤ 100 * N ^ 2 :=
    le_trans ht23_N (Nat.mul_le_mul_left 100 hN_sq)
  have hC41 : t₅ ≤ C41 * N ^ 2 := le_trans ht₅ (Nat.mul_le_mul_left C41 hN_sq)
  have ht_bound : 6 + (t₂ + (t₃ + (t₄ + (t₅ + 2)))) ≤ (450 + C41) * N ^ 2 := by
    rw [Nat.add_mul]
    generalize N ^ 2 = N2 at ht₄ ht23_N2 hC41 ⊢
    omega
  exact ⟨s₆, 6 + (t₂ + (t₃ + (t₄ + (t₅ + 2)))),
    .seq hex₁ (.seq hex₂ (.seq hex₃ (.seq hex₄ (.seq hex₅ hex₆)))),
    ht_bound, by simp [s₆], by simpa [s₆] using hout₅⟩

/-- Step (3) of GM XIII Algorithm (10.5) (page 109):
"If we obtain a model of $K_p$ in $G_i \setminus Z$ and hence in $G_i$, we apply (6.2) to find a vertex $v$
of $G_i$ irrelevant to the $\delta$-folio of $G_i$ relative to $Z$; we set $G_{i+1} = G_i \setminus v$ and return
for the next iteration." -/
def alg105Step3Prog (ξ δ : ℕ) : Cmd :=
  let p := alg62Param ξ δ
  let b := alg105ArrBase p
  .seq (unpackCliqueModelProg (b + 2) p)
    (.seq (toSimpleGraphProg 17 2 6 3 4 5 0)
      (.seq (.assign 14 (.reg 26))
        (.seq (.assign 19 (.op .mul (.const 2) (.reg 1)))
          (.seq (alg62CoreProg ξ δ)
            (deleteFrom17And9Prog p)))))

theorem alg105Step3Prog_exec {w n_i : ℕ} (ξ δ : ℕ) (x : FolioInput ξ)
    (G_i : MultiDigraph n_i) (Z_i : Finset (Fin n_i))
    (X : Fin (alg62Param ξ δ) → Finset (Fin n_i))
    (hw3 : 3 < 2 ^ w)
    (h2n_w : 2 * n_i < 2 ^ w)
    (hp_w : alg62Param ξ δ < 2 ^ w)
    (hpn_w : (alg62Param ξ δ + 2) * n_i < 2 ^ w)
    (henc_w : 2 + 3 * G_i.numActivePairs < 2 ^ w)
    (hm_w : 2 * G_i.numEdges + 1 < 2 ^ w)
    (hmodel_del : IsCliqueModel (G_i.deleteVertices Z_i).toSimpleGraph (alg62Param ξ δ) X)
    (hn_le : n_i ≤ x.n)
    (hZ_eq : Z_i.card = x.Z.card)
    (hedges_le : G_i.numEdges ≤ alg65Const ξ δ * x.n)
    (hfolio : ∀ F : FolioSetRep Z_i.card δ,
      IsDeltaFolioRep δ G_i Z_i F → IsDeltaFolioRep δ x.G x.Z (F.castCard hZ_eq))
    {s : State}
    (hG17 : s.arrs 17 = G_i.enc)
    (hZ9 : s.arrs 9 = bitSetList Z_i)
    (hr26 : s.regs 26 = n_i)
    (hr27 : s.regs 27 = G_i.numActivePairs)
    (hr28 : s.regs 28 = G_i.numEdges)
    (hb2 : s.arrs (alg105ArrBase (alg62Param ξ δ) + 2) = encBitSetsUpTo X (alg62Param ξ δ)) :
    let p := alg62Param ξ δ
    ∃ (n' : ℕ) (G_next : MultiDigraph n') (Z_next : Finset (Fin n')) (s' : State) (time : ℕ),
      n_i = n' + 1 ∧
      Exec w (alg105Step3Prog ξ δ) s s' time ∧
      time ≤ (600 + p * (ξ + 1) * 800) * (n_i + G_i.numEdges + 1) ^ 2 ∧
      Alg105LoopState ξ δ x n' G_next Z_next s' := by
  let p := alg62Param ξ δ
  let b := alg105ArrBase p
  have hp_pos : 0 < p := by dsimp [p, alg62Param]; omega
  have hmodel : IsCliqueModel G_i.toSimpleGraph p X :=
    G_i.isCliqueModel_of_deleteVertices Z_i hmodel_del
  rcases (hmodel.1 ⟨0, hp_pos⟩).1 with ⟨u₀, _⟩
  rcases n_i with _ | n'
  · exact u₀.elim0
  · have hw : 1 < 2 ^ w := by omega
    have hw2 : 2 < 2 ^ w := by omega
    have hnr_w : n' + 1 < 2 ^ w := by omega
    have hedges_w : G_i.numEdges < 2 ^ w := by omega
    have hpairs_le : G_i.numActivePairs ≤ G_i.numEdges := G_i.numActivePairs_le_numEdges
    -- 1. Unpack `X` from `b + 2` into `18 .. 18 + p - 1`
    rcases unpackCliqueModelProg_exec (b + 2) p X (by dsimp [b, alg105ArrBase]; omega)
        hw hnr_w hpn_w hb2 hr26 with
      ⟨s₁, t₁, hex₁, ht₁, hX_bits₁, harr₁, hreg₁⟩
    -- 2. Build CSR of `G_i.toSimpleGraph` in `(3, 4, 5)` from `17`
    have hG17_1 : s₁.arrs 17 = G_i.enc ++ [] := by
      rw [harr₁ 17 (Or.inl (by decide)), List.append_nil]; exact hG17
    rcases toSimpleGraphProg_exec G_i [] 17 2 6 3 4 5 0
        (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide)
        hw3 hnr_w henc_w hG17_1 with
      ⟨s₂, t₂, hex₂, ht₂, _, _, hr1_2, hadj_H₂, hent_H₂, harr₂, _⟩
    have hreg₂ : ∀ r : ℕ, 10 ≤ r → s₂.regs r = s₁.regs r :=
      fun r hr => Exec.regs_eq_of_not_mem_writtenRegs hex₂
        (not_mem_writtenRegs_toSimpleGraphProg 17 2 6 3 4 5 hr)
    let m_H := G_i.toSimpleGraph.edgeFinset.card
    have hm_H_eq : (edgeListOf G_i.toSimpleGraph).length = m_H :=
      length_edgeListOf_eq_card_edgeFinset G_i.toSimpleGraph
    rw [hm_H_eq] at hr1_2 hent_H₂
    have hm_H_le : m_H ≤ G_i.numActivePairs := by
      rw [← hm_H_eq, ← MultiDigraph.toSimplePairsAux_activePairsList]
      exact length_toSimplePairsAux_le (n' + 1) (n' + 1) G_i.activePairsList
    have hm_H_w : m_H < 2 ^ w := by omega
    have h2m_H_w : 2 * m_H < 2 ^ w := by omega
    have hr26_2 : s₂.regs 26 = n' + 1 := by
      rw [hreg₂ 26 (by decide), hreg₁ 26 (by decide), hr26]
    -- 3. Set `r_14 := r_26` and `r_19 := 2 * r_1`
    let s₃ := s₂.setReg 14 (n' + 1)
    have hex₃ : Exec w (.assign 14 (.reg 26)) s₂ s₃ 2 :=
      .assign (by simp [Expr.eval, checkWord, hr26_2, hnr_w])
    let s₄ := s₃.setReg 19 (2 * m_H)
    have hex₄ : Exec w (.assign 19 (.op .mul (.const 2) (.reg 1))) s₃ s₄ 4 :=
      .assign (by simp [s₃, State.setReg, Expr.eval, BinOp.eval, BinOp.raw, checkWord,
        hr1_2, hw2, hm_H_w, h2m_H_w])
    -- 4. Run `alg62CoreProg ξ δ`
    have hZ_card : Z_i.card ≤ ξ := hZ_eq ▸ x.hZ
    have hadj_H₄ : IsAdjList G_i.toSimpleGraph 3 4 5
        (edgeNeighbors (edgeListOf G_i.toSimpleGraph)) s₄ :=
      hadj_H₂.of_arrs_eq rfl rfl rfl
    have hent_H₄ : (s₄.arrs 5).length < 2 ^ w := by
      change (s₂.arrs 5).length < 2 ^ w
      rw [hent_H₂]; exact h2m_H_w
    have hZ_bit₄ : IsBitSet Z_i 9 s₄ := by
      apply IsBitSet.of_bitSetList
      change s₂.arrs 9 = bitSetList Z_i
      rw [harr₂ 9 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
        harr₁ 9 (Or.inl (by decide))]
      exact hZ9
    have hX_bits₄ : ∀ k : Fin p, IsBitSet (X k) (18 + k.1) s₄ := by
      intro k
      refine (hX_bits₁ k).of_arr_eq ?_
      change s₂.arrs (18 + k.1) = s₁.arrs (18 + k.1)
      exact harr₂ (18 + k.1) (by dsimp [Arr, inArr]; omega) (by dsimp [Arr, inArr]; omega)
        (by dsimp [Arr, inArr]; omega) (by dsimp [Arr, inArr]; omega)
        (by dsimp [Arr, inArr]; omega) (by dsimp [Arr, inArr]; omega)
    rcases alg62CoreProg_exec ξ δ G_i (edgeNeighbors (edgeListOf G_i.toSimpleGraph))
        Z_i X (2 * m_H) hZ_card hmodel hw2 h2n_w hp_w h2m_H_w le_rfl
        (s := s₄) (by simp [s₄, s₃, State.setReg]) (by simp [s₄])
        hadj_H₄ hent_H₄ hZ_bit₄ hX_bits₄ with
      ⟨s₅, t₅, i_i, v_i, VA_i, VB_i, hex₅, ht₅, hv_in, hsep, _, _, _,
        _, _, _, _, _, hr25_5, _, _, hZ_bit₅, _, harr₅, _⟩
    change t₅ ≤ 12 + p * (100 + 165 * (n' + 1) + 2 * m_H + 84 * m_H +
      (ξ + 1) * (65 + 264 * (n' + 1) + 62 * m_H)) at ht₅
    -- 5. Run `deleteFrom17And9Prog p`
    have hG17_5 : s₅.arrs 17 = G_i.enc := by
      rw [harr₅ 17 (Or.inr (Or.inr (Or.inr (Or.inl rfl))))]
      change s₂.arrs 17 = G_i.enc
      rw [harr₂ 17 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
        harr₁ 17 (Or.inl (by decide))]
      exact hG17
    have hZ9_5 : s₅.arrs 9 = bitSetList Z_i := hZ_bit₅.arr_eq_bitSetList
    rcases deleteFrom17And9Prog_exec p G_i Z_i v_i hw3 hnr_w henc_w hedges_w
        hG17_5 hZ9_5 hr25_5 with
      ⟨s₆, t₆, hex₆, ht₆, hG_arr₆, hZ_arr₆, hr26_6, hr27_6, hr28_6, hr40_6⟩
    -- 6. Assemble `Alg105LoopState` and step-count bound
    have hirr : GM13.IsIrrelevantVertex G_i.toGMDigraph δ Z_i.toNatSet v_i.1 :=
      isIrrelevantVertex_of_isAlg61Separation hZ_card hmodel hv_in hsep
    have hv_notZ : v_i ∉ Z_i := notMem_Z_of_isAlg61Separation hv_in hsep
    have hZ_next_card : (deleteVertexFinset Z_i v_i).card = Z_i.card :=
      card_deleteVertexFinset_of_notMem hv_notZ
    have hZ_next_eq : (deleteVertexFinset Z_i v_i).card = x.Z.card :=
      hZ_next_card.trans hZ_eq
    have hfolio_next : ∀ F : FolioSetRep (deleteVertexFinset Z_i v_i).card δ,
        IsDeltaFolioRep δ (G_i.deleteVertex v_i) (deleteVertexFinset Z_i v_i) F →
          IsDeltaFolioRep δ x.G x.Z (F.castCard hZ_next_eq) := by
      intro F hF
      have hiff := (isIrrelevantVertex_iff_forall_isDeltaFolioRep δ G_i Z_i v_i hv_notZ).mp
        hirr (F.castCard hZ_next_card)
      rw [Alg65Trace.castCard_trans] at hiff
      have hF' : IsDeltaFolioRep δ (G_i.eraseVertex v_i) (eraseVertexFinset Z_i v_i)
          (F.castCard (hZ_next_card.trans hZ_next_card.symm)) := hF
      have hG_i : IsDeltaFolioRep δ G_i Z_i (F.castCard hZ_next_card) := hiff.mpr hF'
      have hxG := hfolio (F.castCard hZ_next_card) hG_i
      rw [Alg65Trace.castCard_trans] at hxG
      exact hxG
    have hedges_next_le : (G_i.deleteVertex v_i).numEdges ≤ alg65Const ξ δ * x.n :=
      le_trans (Alg65Trace.numEdges_deleteVertex_le G_i v_i) hedges_le
    let N := n' + 1 + G_i.numEdges + 1
    have hN_pos : 1 ≤ N := by dsimp [N]; omega
    have hN_sq : N ≤ N ^ 2 := by rw [Nat.pow_two]; exact Nat.le_mul_of_pos_left N hN_pos
    have ht26_N : t₂ + 2 + 4 + t₆ + 14 ≤ 600 * N := by dsimp [N]; omega
    have ht26_N2 : t₂ + 2 + 4 + t₆ + 14 ≤ 600 * N ^ 2 :=
      le_trans ht26_N (Nat.mul_le_mul_left 600 hN_sq)
    have ht1_inner : 16 * (n' + 1) + 14 ≤ (ξ + 1) * (30 * N ^ 2) := by
      have h1 : 16 * (n' + 1) + 14 ≤ 30 * N := by dsimp [N]; omega
      have h2 : 30 * N ≤ 30 * N ^ 2 := Nat.mul_le_mul_left 30 hN_sq
      exact le_trans (le_trans h1 h2) (Nat.le_mul_of_pos_left _ (by omega))
    have ht1_p : t₁ ≤ 2 + p * ((ξ + 1) * (30 * N ^ 2)) :=
      le_trans ht₁ (Nat.add_le_add_left (Nat.mul_le_mul_left p ht1_inner) 2)
    have ht5_inner : 100 + 165 * (n' + 1) + 2 * m_H + 84 * m_H +
        (ξ + 1) * (65 + 264 * (n' + 1) + 62 * m_H) ≤ (ξ + 1) * (770 * N ^ 2) := by
      have h1 : 100 + 165 * (n' + 1) + 2 * m_H + 84 * m_H ≤ 360 * N := by dsimp [N]; omega
      have h2 : 360 * N ≤ (ξ + 1) * (360 * N) := Nat.le_mul_of_pos_left _ (by omega)
      have h3 : 65 + 264 * (n' + 1) + 62 * m_H ≤ 410 * N := by dsimp [N]; omega
      have h4 : (ξ + 1) * (65 + 264 * (n' + 1) + 62 * m_H) ≤ (ξ + 1) * (410 * N) :=
        Nat.mul_le_mul_left (ξ + 1) h3
      have h5 : (ξ + 1) * (360 * N) + (ξ + 1) * (410 * N) = (ξ + 1) * (770 * N) := by
        have h360 : 360 * N + 410 * N = 770 * N := by omega
        rw [← Nat.mul_add, h360]
      have h6 : (ξ + 1) * (770 * N) ≤ (ξ + 1) * (770 * N ^ 2) :=
        Nat.mul_le_mul_left (ξ + 1) (Nat.mul_le_mul_left 770 hN_sq)
      omega
    have ht5_p : t₅ ≤ 12 + p * ((ξ + 1) * (770 * N ^ 2)) :=
      le_trans ht₅ (Nat.add_le_add_left (Nat.mul_le_mul_left p ht5_inner) 12)
    have hp_sum :
        p * ((ξ + 1) * (30 * N ^ 2)) + p * ((ξ + 1) * (770 * N ^ 2)) =
          p * (ξ + 1) * 800 * N ^ 2 := by
      rw [← Nat.mul_add, ← Nat.mul_add]
      have : 30 * N ^ 2 + 770 * N ^ 2 = 800 * N ^ 2 := by omega
      rw [this, ← Nat.mul_assoc, ← Nat.mul_assoc]
    have ht_bound : t₁ + (t₂ + (2 + (4 + (t₅ + t₆)))) ≤
        (600 + p * (ξ + 1) * 800) * N ^ 2 := by
      rw [Nat.add_mul, ← hp_sum]
      generalize p * ((ξ + 1) * (30 * N ^ 2)) = P30 at ht1_p ⊢
      generalize p * ((ξ + 1) * (770 * N ^ 2)) = P770 at ht5_p ⊢
      generalize N ^ 2 = N2 at ht26_N2 ⊢
      omega
    exact ⟨n', G_i.deleteVertex v_i, deleteVertexFinset Z_i v_i,
      s₆, t₁ + (t₂ + (2 + (4 + (t₅ + t₆)))), rfl,
      .seq hex₁ (.seq hex₂ (.seq hex₃ (.seq hex₄ (.seq hex₅ hex₆)))),
      ht_bound,
      ⟨by omega, hZ_next_eq, hedges_next_le, hfolio_next,
        hG_arr₆, hZ_arr₆, hr26_6, hr27_6, hr28_6, hr40_6⟩⟩

/-- Step (4) of GM XIII Algorithm (10.5) (page 109):
"Put $X' = X \cup Z$; then $G_i$, $X'$, $H$, $\mathcal{A}$ also satisfy Hypothesis C. We apply (10.4) to
$G_i$, $X'$, $H$, $\mathcal{A}$, to compute an irrelevant vertex $v$ for the $\delta$-folio of $G_i$ relative to $X'$.
Since $Z \subseteq X'$, $v$ is also irrelevant for the $\delta$-folio of $G_i$ relative to $Z$, by (2.1). We set
$G_{i+1} = G_i \setminus v$, and return for the next iteration." -/
def alg105Step4Prog (p : ℕ) (prog104 : Cmd) : Cmd :=
  let b := alg105ArrBase p
  .seq (.assign 55 (.op .add (.const 2) (.op .mul (.const 3) (.reg 27))))
    (.seq (readSliceProg 17 (.const 0) b (.reg 55) 56)
      (.seq (unionBitSetProg (b + 2) 9 (b + 1) 26 55)
        (.seq prog104
          (.seq (.assign 25 (.reg 51))
            (deleteFrom17And9Prog p)))))

theorem alg105Step4Prog_exec {w n_i : ℕ} (dec : Case3BlockDecoder)
    (ξ δ h ω C104 c104 : ℕ) (prog104 : Cmd)
    (h104 : ∀ {w n_i : ℕ} (G_i : MultiDigraph n_i) (X' : Finset (Fin n_i))
      (block : List ℕ) (s : State),
      let p := alg62Param ξ δ
      let q := p.choose 2 + ξ - 1
      let b := alg105ArrBase p
      let N := n_i + G_i.numEdges + 1
      let H := dec.wall n_i G_i X' block
      let S_H := dec.society n_i G_i X' block
      let 𝒜 := dec.division n_i G_i X' block
      wordSize c104 (N + block.length) ≤ w →
      X'.card ≤ q →
      GM13.HypothesisC G_i.toGMDigraph X'.toNatSet.ncard X'.toNatSet H S_H 𝒜 →
      H.height = h →
      (∀ ⦃A : Graph ℕ (ℕ × ℕ × ℕ)⦄,
        GM13.IsInteriorMember H 𝒜 A →
          let bd := dec.branchDecomp n_i G_i X' block A
          E(A).ncard ≤ 1 ∨
            (GM13.IsGraphBranchDecomposition A bd.2.1 bd.2.2 ∧
              GM13.graphBranchDecompWidth A bd.2.1 bd.2.2 ≤ ω)) →
      s.arrs b = G_i.enc →
      s.arrs (b + 1) = bitSetList X' →
      s.arrs (b + 3) = block →
      ∃ (s' : State) (time : ℕ) (v : Fin n_i),
        Exec w prog104 s s' time ∧
        time ≤ C104 * N ^ 2 ∧
        s'.regs 51 = v.1 ∧
        GM13.IsIrrelevantVertex G_i.toGMDigraph δ X'.toNatSet v.1 ∧
        (∀ r < 50, s'.regs r = s.regs r) ∧
        (∀ a < b, s'.arrs a = s.arrs a))
    (x : FolioInput ξ)
    (G_i : MultiDigraph n_i) (Z_i X : Finset (Fin n_i)) (block : List ℕ)
    (hw3 : 3 < 2 ^ w)
    (hn_w : n_i < 2 ^ w)
    (henc_w : 2 + 3 * G_i.numActivePairs < 2 ^ w)
    (hedges_w : G_i.numEdges < 2 ^ w)
    (hw104 : wordSize c104 (n_i + G_i.numEdges + 1 + block.length) ≤ w)
    (hdisj : Disjoint X Z_i)
    (hX_lt : X.card < (alg62Param ξ δ).choose 2)
    (hheight : (dec.wall n_i G_i (X ∪ Z_i) block).height = h)
    (hflat : GM13.IsFlatWallIn
      (deleteVertices (G_i.toGMDigraph.deleteVertices Z_i.toNatSet).toGraph X.toNatSet)
      (dec.wall n_i G_i (X ∪ Z_i) block))
    (hsoc : GM13.IsWallSociety
      (deleteVertices (G_i.toGMDigraph.deleteVertices Z_i.toNatSet).toGraph X.toNatSet)
      (dec.wall n_i G_i (X ∪ Z_i) block) (dec.society n_i G_i (X ∪ Z_i) block))
    (hrural : GM13.IsRuralDivision (dec.society n_i G_i (X ∪ Z_i) block)
      (dec.division n_i G_i (X ∪ Z_i) block))
    (hbw : ∀ ⦃A : Graph ℕ (ℕ × ℕ × ℕ)⦄,
      GM13.IsInteriorMember (dec.wall n_i G_i (X ∪ Z_i) block)
        (dec.division n_i G_i (X ∪ Z_i) block) A →
        let bd := dec.branchDecomp n_i G_i (X ∪ Z_i) block A
        E(A).ncard ≤ 1 ∨
          (GM13.IsGraphBranchDecomposition A bd.2.1 bd.2.2 ∧
            GM13.graphBranchDecompWidth A bd.2.1 bd.2.2 ≤ ω))
    (hn_le : n_i ≤ x.n)
    (hZ_eq : Z_i.card = x.Z.card)
    (hedges_le : G_i.numEdges ≤ alg65Const ξ δ * x.n)
    (hfolio : ∀ F : FolioSetRep Z_i.card δ,
      IsDeltaFolioRep δ G_i Z_i F → IsDeltaFolioRep δ x.G x.Z (F.castCard hZ_eq))
    {s : State}
    (hG17 : s.arrs 17 = G_i.enc)
    (hZ9 : s.arrs 9 = bitSetList Z_i)
    (hr26 : s.regs 26 = n_i)
    (hr27 : s.regs 27 = G_i.numActivePairs)
    (hb2 : s.arrs (alg105ArrBase (alg62Param ξ δ) + 2) = bitSetList X)
    (hb3 : s.arrs (alg105ArrBase (alg62Param ξ δ) + 3) = block) :
    let p := alg62Param ξ δ
    ∃ (n' : ℕ) (G_next : MultiDigraph n') (Z_next : Finset (Fin n')) (s' : State) (time : ℕ),
      n_i = n' + 1 ∧
      Exec w (alg105Step4Prog p prog104) s s' time ∧
      time ≤ (300 + C104) * (n_i + G_i.numEdges + 1) ^ 2 ∧
      Alg105LoopState ξ δ x n' G_next Z_next s' := by
  let p := alg62Param ξ δ
  let b := alg105ArrBase p
  have hw : 1 < 2 ^ w := by omega
  have hw2 : 2 < 2 ^ w := by omega
  have hm'_w : G_i.numActivePairs < 2 ^ w := by omega
  have hZ_card : Z_i.card ≤ ξ := hZ_eq ▸ x.hZ
  -- 1. Set `r_55 := 2 + 3 * r_27` and copy `G_i.enc` from `17` to `b`
  let s₁ := s.setReg 55 (2 + 3 * G_i.numActivePairs)
  have hex₁ : Exec w (.assign 55 (.op .add (.const 2) (.op .mul (.const 3) (.reg 27)))) s s₁ 6 :=
    .assign (by simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord,
      hr27, hw2, hw3, hm'_w, show 3 * G_i.numActivePairs < 2 ^ w by omega, henc_w])
  have henc_words_w : ∀ x_w ∈ G_i.enc, x_w < 2 ^ w := by
    intro x_w hx
    simp only [MultiDigraph.enc, List.cons_append, List.nil_append, List.mem_cons] at hx
    rcases hx with rfl | rfl | hx
    · exact hn_w
    · exact hm'_w
    · exact all_lt_flatTriples G_i G_i.activePairsList hn_w
        (fun q _ => Nat.lt_of_le_of_lt (G_i.edgeMult_le_numEdges q.1 q.2) hedges_w) x_w hx
  rcases copyListProg_exec 17 b 55 56 (by dsimp [b, alg105ArrBase]; omega) (by decide)
      G_i.enc G_i.length_enc henc_words_w hw henc_w (s := s₁)
      (by simp [s₁, hG17]) (by simp [s₁]) with
    ⟨s₂, t₂, hex₂, ht₂, hb_arr₂, harr₂, hreg₂⟩
  -- 2. Compute `X' = X ∪ Z_i` in `b + 1` via `unionBitSetProg (b + 2) 9 (b + 1) 26 55`
  have hb2_2 : s₂.arrs (b + 2) = bitSetList X := by
    rw [harr₂ (b + 2) (by dsimp [b, alg105ArrBase]; omega)]; exact hb2
  have hZ9_2 : s₂.arrs 9 = bitSetList Z_i := by
    rw [harr₂ 9 (by dsimp [b, alg105ArrBase]; omega)]; exact hZ9
  have hr26_2 : s₂.regs 26 = n_i := by
    rw [hreg₂ 26 (by decide)]; simp [s₁, hr26]
  rcases unionBitSetProg_exec X Z_i (b + 2) 9 (b + 1) 26 55
      (by dsimp [b, alg105ArrBase]; omega) (by dsimp [b, alg105ArrBase]; omega)
      (by decide) hw2 hn_w hb2_2 hZ9_2 hr26_2 with
    ⟨s₃, t₃, hex₃, ht₃, hb1_arr₃, harr₃, _⟩
  -- 3. Apply `step4_hypothesisC_of_case3` and run `prog104`
  have hb_arr₃ : s₃.arrs b = G_i.enc := by
    rw [harr₃ b (by dsimp [b, alg105ArrBase]; omega)]; exact hb_arr₂
  have hb3_arr₃ : s₃.arrs (b + 3) = block := by
    rw [harr₃ (b + 3) (by dsimp [b, alg105ArrBase]; omega),
      harr₂ (b + 3) (by dsimp [b, alg105ArrBase]; omega)]
    exact hb3
  obtain ⟨hX'_card, hHypC, _hflat', hbw'⟩ :=
    step4_hypothesisC_of_case3 dec G_i Z_i X block
      hZ_card hdisj hX_lt hflat hsoc hrural hbw
  rcases h104 G_i (X ∪ Z_i) block s₃ hw104 hX'_card hHypC hheight hbw'
      hb_arr₃ hb1_arr₃ hb3_arr₃ with
    ⟨s₄, t₄, v_i, hex₄, ht₄, hr51_4, hirr_X', _, harr₄⟩
  -- 4. Since `v_i : Fin n_i`, `n_i = n' + 1`; set `r_25 := r_51` and run `deleteFrom17And9Prog p`
  rcases n_i with _ | n'
  · exact v_i.elim0
  · have hv_w : v_i.1 < 2 ^ w := Nat.lt_trans v_i.2 hn_w
    let s₅ := s₄.setReg 25 v_i.1
    have hex₅ : Exec w (.assign 25 (.reg 51)) s₄ s₅ 2 :=
      .assign (by simp [Expr.eval, checkWord, hr51_4, hv_w])
    have hG17_5 : s₅.arrs 17 = G_i.enc := by
      simp only [s₅, State.setReg_arrs]
      rw [harr₄ 17 (by dsimp [b, alg105ArrBase]; omega),
        harr₃ 17 (by dsimp [b, alg105ArrBase]; omega),
        harr₂ 17 (by dsimp [b, alg105ArrBase]; omega)]
      exact hG17
    have hZ9_5 : s₅.arrs 9 = bitSetList Z_i := by
      simp only [s₅, State.setReg_arrs]
      rw [harr₄ 9 (by dsimp [b, alg105ArrBase]; omega),
        harr₃ 9 (by dsimp [b, alg105ArrBase]; omega)]
      exact hZ9_2
    rcases deleteFrom17And9Prog_exec p G_i Z_i v_i hw3 hn_w henc_w hedges_w
        hG17_5 hZ9_5 (by simp [s₅]) with
      ⟨s₆, t₆, hex₆, ht₆, hG_arr₆, hZ_arr₆, hr26_6, hr27_6, hr28_6, hr40_6⟩
    -- 5. By GM XIII (2.1) (`GM13.theorem_2_1_proof`), `v_i` is irrelevant relative to `Z_i`
    have hsub_Z : Z_i.toNatSet ⊆ (X ∪ Z_i).toNatSet := by
      rw [toNatSet_union]; exact Set.subset_union_right
    have hv_notZ : v_i ∉ Z_i :=
      fun hvZ => hirr_X'.2.1 (hsub_Z ((mem_toNatSet_iff Z_i v_i).mpr hvZ))
    have hirr_Z : GM13.IsIrrelevantVertex G_i.toGMDigraph δ Z_i.toNatSet v_i.1 :=
      ⟨hirr_X'.1, fun h => hirr_X'.2.1 (hsub_Z h), GM13.theorem_2_1_proof hsub_Z hirr_X'.2.2⟩
    have hZ_next_card : (deleteVertexFinset Z_i v_i).card = Z_i.card :=
      card_deleteVertexFinset_of_notMem hv_notZ
    have hZ_next_eq : (deleteVertexFinset Z_i v_i).card = x.Z.card :=
      hZ_next_card.trans hZ_eq
    have hfolio_next : ∀ F : FolioSetRep (deleteVertexFinset Z_i v_i).card δ,
        IsDeltaFolioRep δ (G_i.deleteVertex v_i) (deleteVertexFinset Z_i v_i) F →
          IsDeltaFolioRep δ x.G x.Z (F.castCard hZ_next_eq) := by
      intro F hF
      have hiff := (isIrrelevantVertex_iff_forall_isDeltaFolioRep δ G_i Z_i v_i hv_notZ).mp
        hirr_Z (F.castCard hZ_next_card)
      rw [Alg65Trace.castCard_trans] at hiff
      have hF' : IsDeltaFolioRep δ (G_i.eraseVertex v_i) (eraseVertexFinset Z_i v_i)
          (F.castCard (hZ_next_card.trans hZ_next_card.symm)) := hF
      have hG_i : IsDeltaFolioRep δ G_i Z_i (F.castCard hZ_next_card) := hiff.mpr hF'
      have hxG := hfolio (F.castCard hZ_next_card) hG_i
      rw [Alg65Trace.castCard_trans] at hxG
      exact hxG
    have hedges_next_le : (G_i.deleteVertex v_i).numEdges ≤ alg65Const ξ δ * x.n :=
      le_trans (Alg65Trace.numEdges_deleteVertex_le G_i v_i) hedges_le
    have hpairs_le : G_i.numActivePairs ≤ G_i.numEdges := G_i.numActivePairs_le_numEdges
    let N := n' + 1 + G_i.numEdges + 1
    have hN_pos : 1 ≤ N := by dsimp [N]; omega
    have hN_sq : N ≤ N ^ 2 := by rw [Nat.pow_two]; exact Nat.le_mul_of_pos_left N hN_pos
    have hrest_N : 6 + t₂ + t₃ + 2 + t₆ ≤ 300 * N := by dsimp [N]; omega
    have hrest : 6 + t₂ + t₃ + 2 + t₆ ≤ 300 * N ^ 2 :=
      le_trans hrest_N (Nat.mul_le_mul_left 300 hN_sq)
    have ht_bound : 6 + (t₂ + (t₃ + (t₄ + (2 + t₆)))) ≤ (300 + C104) * N ^ 2 := by
      rw [Nat.add_mul]
      generalize N ^ 2 = N2 at hrest ht₄ ⊢
      omega
    exact ⟨n', G_i.deleteVertex v_i, deleteVertexFinset Z_i v_i,
      s₆, 6 + (t₂ + (t₃ + (t₄ + (2 + t₆)))), rfl,
      .seq hex₁ (.seq hex₂ (.seq hex₃ (.seq hex₄ (.seq hex₅ hex₆)))),
      ht_bound,
      ⟨by omega, hZ_next_eq, hedges_next_le, hfolio_next,
        hG_arr₆, hZ_arr₆, hr26_6, hr27_6, hr28_6, hr40_6⟩⟩

/-- Body of one iteration of the recursion of Algorithm (10.5) (pages 108–109):
1. Copies `G_i` and `Z_i` from `(18 + p, 18 + p + 1)` into `(17, 9)` and `Z_i` into `b + 1`.
2. Constructs `G_i \ Z_i` in array `b` (`deleteVerticesZProg 17 9 2 b 55`).
3. Applies `(9.9)` (`prog99`) to `G_i \ Z_i`.
4. Branches on the case tag `r_51`:
   - `r_51 = 0`: Step (2) (`alg105Step2Prog p prog41`),
   - `r_51 = 1`: Step (3) (`alg105Step3Prog ξ δ`),
   - `r_51 = 2`: Step (4) (`alg105Step4Prog p prog104`). -/
def alg105LoopBody (ξ δ : ℕ) (prog99 prog104 prog41 : Cmd) : Cmd :=
  let p := alg62Param ξ δ
  let b := alg105ArrBase p
  .seq (.assign 55 (.op .add (.const 2) (.op .mul (.const 3) (.reg 27))))
    (.seq (readSliceProg (18 + p) (.const 0) 17 (.reg 55) 56)
      (.seq (readSliceProg (18 + p + 1) (.const 0) 9 (.reg 26) 55)
        (.seq (readSliceProg 9 (.const 0) (b + 1) (.reg 26) 55)
          (.seq (deleteVerticesZProg 17 9 2 b 55)
            (.seq prog99
              (.ite (.op .eq (.reg 51) (.const 0))
                (alg105Step2Prog p prog41)
                (.ite (.op .eq (.reg 51) (.const 1))
                  (alg105Step3Prog ξ δ)
                  (alg105Step4Prog p prog104))))))))

/-- Main recursion loop of Algorithm (10.5):
executes `alg105LoopBody` while `r_40 != 0`. -/
def alg105LoopProg (ξ δ : ℕ) (prog99 prog104 prog41 : Cmd) : Cmd :=
  .while (.reg 40) (alg105LoopBody ξ δ prog99 prog104 prog41)

theorem alg105LoopBody_exec {w n_i : ℕ} (dec : Case3BlockDecoder)
    (ξ δ h ω C99 c99 C104 c104 C41 c41 : ℕ) (prog99 prog104 prog41 : Cmd)
    (h99 : ∀ {w n_i : ℕ} (G_i : MultiDigraph n_i) (Z_i : Finset (Fin n_i)) (s : State),
      let p := alg62Param ξ δ
      let b := alg105ArrBase p
      let D_del := G_i.deleteVertices Z_i
      let N := n_i + D_del.numEdges + 1
      wordSize c99 N ≤ w →
      s.arrs b = D_del.enc →
      s.arrs (b + 1) = bitSetList Z_i →
      ∃ s' time,
        Exec w prog99 s s' time ∧
        time ≤ C99 * (n_i + 1) * N ∧
        (∀ r < 50, s'.regs r = s.regs r) ∧
        (∀ a < b, s'.arrs a = s.arrs a) ∧
        ((s'.regs 51 = 0 ∧
            ∃ (t : ℕ) (par f_tau : ℕ → ℕ),
              s'.regs 52 = t ∧
              (s'.arrs (b + 2)).length = t ∧
              (∀ z < t, (s'.arrs (b + 2)).getD z 0 = par z) ∧
              (s'.arrs (b + 3)).length = D_del.numEdges ∧
              (∀ e < D_del.numEdges, (s'.arrs (b + 3)).getD e 0 = f_tau e) ∧
              IsWrittenDigraphBD ω D_del.toComputeDigraph t par f_tau) ∨
         (s'.regs 51 = 1 ∧
            ∃ X : Fin p → Finset (Fin n_i),
              s'.arrs (b + 2) = encBitSetsUpTo X p ∧
              (∀ j : Fin p, Disjoint (X j) Z_i) ∧
              IsCliqueModel D_del.toSimpleGraph p X) ∨
         (s'.regs 51 = 2 ∧
            ∃ (X : Finset (Fin n_i)) (block : List ℕ),
              s'.arrs (b + 2) = bitSetList X ∧
              s'.arrs (b + 3) = block ∧
              block.length ≤ C99 * N ∧
              (∀ x_b ∈ block, x_b < 2 ^ w) ∧
              Disjoint X Z_i ∧
              X.card < p.choose 2 ∧
              let X' := X ∪ Z_i
              let H := dec.wall n_i G_i X' block
              let S_H := dec.society n_i G_i X' block
              let 𝒜 := dec.division n_i G_i X' block
              H.height = h ∧
              GM13.IsFlatWallIn
                (deleteVertices (G_i.toGMDigraph.deleteVertices Z_i.toNatSet).toGraph
                  X.toNatSet) H ∧
              GM13.IsWallSociety
                (deleteVertices (G_i.toGMDigraph.deleteVertices Z_i.toNatSet).toGraph
                  X.toNatSet) H S_H ∧
              GM13.IsRuralDivision S_H 𝒜 ∧
              ∀ ⦃A : Graph ℕ (ℕ × ℕ × ℕ)⦄,
                GM13.IsInteriorMember H 𝒜 A →
                  let bd := dec.branchDecomp n_i G_i X' block A
                  E(A).ncard ≤ 1 ∨
                    (GM13.IsGraphBranchDecomposition A bd.2.1 bd.2.2 ∧
                      GM13.graphBranchDecompWidth A bd.2.1 bd.2.2 ≤ ω))))
    (h104 : ∀ {w n_i : ℕ} (G_i : MultiDigraph n_i) (X' : Finset (Fin n_i))
      (block : List ℕ) (s : State),
      let p := alg62Param ξ δ
      let q := p.choose 2 + ξ - 1
      let b := alg105ArrBase p
      let N := n_i + G_i.numEdges + 1
      let H := dec.wall n_i G_i X' block
      let S_H := dec.society n_i G_i X' block
      let 𝒜 := dec.division n_i G_i X' block
      wordSize c104 (N + block.length) ≤ w →
      X'.card ≤ q →
      GM13.HypothesisC G_i.toGMDigraph X'.toNatSet.ncard X'.toNatSet H S_H 𝒜 →
      H.height = h →
      (∀ ⦃A : Graph ℕ (ℕ × ℕ × ℕ)⦄,
        GM13.IsInteriorMember H 𝒜 A →
          let bd := dec.branchDecomp n_i G_i X' block A
          E(A).ncard ≤ 1 ∨
            (GM13.IsGraphBranchDecomposition A bd.2.1 bd.2.2 ∧
              GM13.graphBranchDecompWidth A bd.2.1 bd.2.2 ≤ ω)) →
      s.arrs b = G_i.enc →
      s.arrs (b + 1) = bitSetList X' →
      s.arrs (b + 3) = block →
      ∃ (s' : State) (time : ℕ) (v : Fin n_i),
        Exec w prog104 s s' time ∧
        time ≤ C104 * N ^ 2 ∧
        s'.regs 51 = v.1 ∧
        GM13.IsIrrelevantVertex G_i.toGMDigraph δ X'.toNatSet v.1 ∧
        (∀ r < 50, s'.regs r = s.regs r) ∧
        (∀ a < b, s'.arrs a = s.arrs a))
    (OutRel : FolioInput ξ → List ℕ → Prop)
    (h41 : ∀ {w n_i : ℕ} (G_i : MultiDigraph n_i) (Z_i : Finset (Fin n_i))
      (t : ℕ) (par f_tau : ℕ → ℕ) (s : State),
      let p := alg62Param ξ δ
      let b := alg105ArrBase p
      let N := n_i + G_i.numEdges + 1
      wordSize c41 N ≤ w →
      Z_i.card ≤ ξ →
      IsWrittenDigraphBD (max ω 2 + ξ) G_i.toComputeDigraph t par f_tau →
      s.arrs b = G_i.enc →
      s.arrs (b + 1) = bitSetList Z_i →
      s.regs 26 = n_i →
      s.regs 28 = G_i.numEdges →
      s.regs 52 = t →
      (s.arrs (b + 2)).length = t →
      (∀ z < t, (s.arrs (b + 2)).getD z 0 = par z) →
      (s.arrs (b + 3)).length = G_i.numEdges →
      (∀ e < G_i.numEdges, (s.arrs (b + 3)).getD e 0 = f_tau e) →
      s.arrs (b + 5) =
        List.ofFn (fun e : Fin G_i.toComputeDigraph.numEdges => (G_i.toComputeDigraph.tail e).1) →
      s.arrs (b + 6) =
        List.ofFn (fun e : Fin G_i.toComputeDigraph.numEdges => (G_i.toComputeDigraph.head e).1) →
      ∃ (s' : State) (time : ℕ),
        Exec w prog41 s s' time ∧
        time ≤ C41 * N ∧
        ∀ (x : FolioInput ξ) (hZ_eq : Z_i.card = x.Z.card),
          (∀ F : FolioSetRep Z_i.card δ,
            IsDeltaFolioRep δ G_i Z_i F → IsDeltaFolioRep δ x.G x.Z (F.castCard hZ_eq)) →
          OutRel x (s'.arrs outArr))
    (x : FolioInput ξ) (G_i : MultiDigraph n_i) (Z_i : Finset (Fin n_i))
    (hw3 : 3 < 2 ^ w)
    (hnn0_w : x.n * x.n < 2 ^ w)
    (h2n0_w : 2 * x.n < 2 ^ w)
    (hp_w : alg62Param ξ δ < 2 ^ w)
    (hpn0_w : (alg62Param ξ δ + 2) * x.n < 2 ^ w)
    (_hm_max_w : 2 * (alg65Const ξ δ * x.n) + 1 < 2 ^ w)
    (henc_max_w : 2 + 3 * (alg65Const ξ δ * x.n) < 2 ^ w)
    (hw99 : wordSize c99 ((alg65Const ξ δ + 1) * (x.n + 1)) ≤ w)
    (hw104 : wordSize c104 ((C99 + 1) * (alg65Const ξ δ + 1) * (x.n + 1)) ≤ w)
    (hw41 : wordSize c41 ((alg65Const ξ δ + 1) * (x.n + 1)) ≤ w)
    {s : State}
    (hst : Alg105LoopState ξ δ x n_i G_i Z_i s) :
    let p := alg62Param ξ δ
    let K_body := 900 + p * (ξ + 1) * 800 + C99 + C104 + C41
    ∃ s' time,
      Exec w (alg105LoopBody ξ δ prog99 prog104 prog41) s s' time ∧
      time ≤ K_body * (alg65Const ξ δ + 1) ^ 2 * (x.n + 1) ^ 2 ∧
      ((s'.regs 40 = 0 ∧ OutRel x (s'.arrs outArr)) ∨
       (∃ (n' : ℕ) (G_next : MultiDigraph n') (Z_next : Finset (Fin n')),
         n_i = n' + 1 ∧
         Alg105LoopState ξ δ x n' G_next Z_next s')) := by
  let p := alg62Param ξ δ
  let b := alg105ArrBase p
  let K_body := 900 + p * (ξ + 1) * 800 + C99 + C104 + C41
  have h0_w : 0 < 2 ^ w := by omega
  have hw : 1 < 2 ^ w := by omega
  have hw2 : 2 < 2 ^ w := by omega
  have hn_le := hst.hn_le
  have hedges_le := hst.hedges_le
  have hpairs_le : G_i.numActivePairs ≤ G_i.numEdges := G_i.numActivePairs_le_numEdges
  have hn_w : n_i < 2 ^ w := by omega
  have h2n_w : 2 * n_i < 2 ^ w := by omega
  have hnn_w : n_i * n_i < 2 ^ w :=
    Nat.lt_of_le_of_lt (Nat.mul_le_mul hn_le hn_le) hnn0_w
  have hpn_w : (p + 2) * n_i < 2 ^ w :=
    Nat.lt_of_le_of_lt (Nat.mul_le_mul_left (p + 2) hn_le) hpn0_w
  have henc_w : 2 + 3 * G_i.numActivePairs < 2 ^ w := by omega
  have hm_w : 2 * G_i.numEdges + 1 < 2 ^ w := by omega
  have hedges_w : G_i.numEdges < 2 ^ w := by omega
  have hm'_w : G_i.numActivePairs < 2 ^ w := by omega
  let N := n_i + G_i.numEdges + 1
  let D_del := G_i.deleteVertices Z_i
  let N_del := n_i + D_del.numEdges + 1
  have hdel_edges_le : D_del.numEdges ≤ G_i.numEdges := G_i.numEdges_deleteVertices_le Z_i
  have hN_del_le_N : N_del ≤ N := by dsimp [N_del, N]; omega
  have hN_le_max : N ≤ (alg65Const ξ δ + 1) * (x.n + 1) := by
    dsimp [N]
    rw [Nat.add_mul, Nat.one_mul, Nat.mul_add, Nat.mul_one]
    omega
  have hw99_i : wordSize c99 N_del ≤ w :=
    le_trans (wordSize_mono_right c99 (le_trans hN_del_le_N hN_le_max)) hw99
  have hw41_i : wordSize c41 N ≤ w :=
    le_trans (wordSize_mono_right c41 hN_le_max) hw41
  -- 1. Set `r_55 := 2 + 3 * r_27` and copy `G_i.enc` from `18 + p` to `17`
  let s₁ := s.setReg 55 (2 + 3 * G_i.numActivePairs)
  have hex₁ : Exec w (.assign 55 (.op .add (.const 2) (.op .mul (.const 3) (.reg 27)))) s s₁ 6 :=
    .assign (by simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord,
      hst.hr27, hw2, hw3, hm'_w, show 3 * G_i.numActivePairs < 2 ^ w by omega, henc_w])
  have henc_words_w : ∀ x_w ∈ G_i.enc, x_w < 2 ^ w := by
    intro x_w hx
    simp only [MultiDigraph.enc, List.cons_append, List.nil_append, List.mem_cons] at hx
    rcases hx with rfl | rfl | hx
    · exact hn_w
    · exact hm'_w
    · exact all_lt_flatTriples G_i G_i.activePairsList hn_w
        (fun q _ => Nat.lt_of_le_of_lt (G_i.edgeMult_le_numEdges q.1 q.2) hedges_w) x_w hx
  rcases copyListProg_exec (18 + p) 17 55 56 (by omega) (by decide)
      G_i.enc G_i.length_enc henc_words_w hw henc_w (s := s₁)
      (by dsimp [s₁, p]; exact hst.hG_arr) (by simp [s₁]) with
    ⟨s₂, t₂, hex₂, ht₂, hG17_2, harr₂, hreg₂⟩
  -- 2. Copy `bitSetList Z_i` from `18 + p + 1` to `9`
  have hZ_words_w : ∀ x_w ∈ bitSetList Z_i, x_w < 2 ^ w := by
    intro x_w hx
    rcases List.mem_iff_getElem.mp hx with ⟨idx, hidx, rfl⟩
    have hle1 := getElem_bitSetList_le_one Z_i idx hidx
    omega
  have hr26_2 : s₂.regs 26 = n_i := by
    rw [hreg₂ 26 (by decide)]; simp [s₁, hst.hr26]
  have hZ_arr₂ : s₂.arrs (18 + p + 1) = bitSetList Z_i := by
    rw [harr₂ (18 + p + 1) (by omega)]; exact hst.hZ_arr
  rcases copyListProg_exec (18 + p + 1) 9 26 55 (by omega) (by decide)
      (bitSetList Z_i) (length_bitSetList Z_i) hZ_words_w hw hn_w hZ_arr₂ hr26_2 with
    ⟨s₃, t₃, hex₃, ht₃, hZ9_3, harr₃, hreg₃⟩
  -- 3. Copy `bitSetList Z_i` from `9` to `b + 1`
  have hr26_3 : s₃.regs 26 = n_i := (hreg₃ 26 (by decide)).trans hr26_2
  rcases copyListProg_exec 9 (b + 1) 26 55 (by dsimp [b, alg105ArrBase]; omega) (by decide)
      (bitSetList Z_i) (length_bitSetList Z_i) hZ_words_w hw hn_w hZ9_3 hr26_3 with
    ⟨s₄, t₄, hex₄, ht₄, hb1_4, harr₄, hreg₄⟩
  -- 4. Build `D_del.enc` in `b` via `deleteVerticesZProg 17 9 2 b 55`
  have hG17_4 : s₄.arrs 17 = G_i.enc := by
    rw [harr₄ 17 (by dsimp [b, alg105ArrBase]; omega), harr₃ 17 (by decide)]
    exact hG17_2
  have hZ9_4 : s₄.arrs 9 = bitSetList Z_i := by
    rw [harr₄ 9 (by dsimp [b, alg105ArrBase]; omega)]; exact hZ9_3
  rcases deleteVerticesZProg_exec G_i Z_i 17 9 2 b 55
      (by decide) (by decide) (by dsimp [b, alg105ArrBase]; omega)
      hw3 hn_w henc_w hedges_w hG17_4 hZ9_4 with
    ⟨s₅, t₅, hex₅, ht₅, hb_5, harr₅, hreg₅⟩
  -- 5. Run `prog99`
  have hb1_5 : s₅.arrs (b + 1) = bitSetList Z_i := by
    rw [harr₅ (b + 1) (by dsimp [b, alg105ArrBase]; omega) (by dsimp [b, alg105ArrBase]; omega)]
    exact hb1_4
  rcases h99 G_i Z_i s₅ hw99_i hb_5 hb1_5 with
    ⟨s₆, t₆, hex₆, ht₆, hreg₆, harr₆, hcases₆⟩
  have hG17_6 : s₆.arrs 17 = G_i.enc := by
    rw [harr₆ 17 (by dsimp [b, alg105ArrBase]; omega),
      harr₅ 17 (by decide) (by dsimp [b, alg105ArrBase]; omega),
      harr₄ 17 (by dsimp [b, alg105ArrBase]; omega),
      harr₃ 17 (by decide)]
    exact hG17_2
  have hZ9_6 : s₆.arrs 9 = bitSetList Z_i := by
    rw [harr₆ 9 (by dsimp [b, alg105ArrBase]; omega),
      harr₅ 9 (by decide) (by dsimp [b, alg105ArrBase]; omega)]
    exact hZ9_4
  have hr26_6 : s₆.regs 26 = n_i := by
    rw [hreg₆ 26 (by decide), hreg₅ 26 (by decide)]; exact (hreg₄ 26 (by decide)).trans hr26_3
  have hr27_6 : s₆.regs 27 = G_i.numActivePairs := by
    rw [hreg₆ 27 (by decide), hreg₅ 27 (by decide), hreg₄ 27 (by decide),
      hreg₃ 27 (by decide), hreg₂ 27 (by decide)]
    simp [s₁, hst.hr27]
  have hr28_6 : s₆.regs 28 = G_i.numEdges := by
    rw [hreg₆ 28 (by decide), hreg₅ 28 (by decide), hreg₄ 28 (by decide),
      hreg₃ 28 (by decide), hreg₂ 28 (by decide)]
    simp [s₁, hst.hr28]
  have hZ_card : Z_i.card ≤ ξ := hst.hZ_eq ▸ x.hZ
  have hN_pos : 1 ≤ N := by dsimp [N]; omega
  have hN_sq : N ≤ N ^ 2 := by rw [Nat.pow_two]; exact Nat.le_mul_of_pos_left N hN_pos
  have hpre_N : 6 + t₂ + t₃ + t₄ + t₅ + 6 ≤ 300 * N := by dsimp [N]; omega
  have hpre_bound : 6 + t₂ + t₃ + t₄ + t₅ + 6 ≤ 300 * N ^ 2 :=
    le_trans hpre_N (Nat.mul_le_mul_left 300 hN_sq)
  have ht6_bound : t₆ ≤ C99 * N ^ 2 := by
    have h1 : (n_i + 1) * N_del ≤ N * N :=
      Nat.mul_le_mul (by dsimp [N]; omega) hN_del_le_N
    rw [Nat.mul_assoc] at ht₆
    rw [Nat.pow_two]
    exact le_trans ht₆ (Nat.mul_le_mul_left C99 h1)
  have hN_sq_le : N ^ 2 ≤ (alg65Const ξ δ + 1) ^ 2 * (x.n + 1) ^ 2 := by
    rw [← Nat.mul_pow]
    exact Nat.pow_le_pow_left hN_le_max 2
  -- 6. Branch on `hcases₆`
  rcases hcases₆ with
    ⟨hr51_0, t₀, par₀, f_tau₀, hr52_6, hb2_len₆, hb2_get₆, hb3_len₆, hb3_get₆, hbd₆⟩ |
    ⟨hr51_1, X, hb2_6, _, hmodel_del⟩ |
    ⟨hr51_2, X, block, hb2_6, hb3_6, hblock_len, _, hdisj, hX_lt,
      hheight, hflat, hsoc, hrural, hbw⟩
  · -- Case (i): `r_51 = 0` (`alg105Step2Prog`)
    have hcond0 : (.op .eq (.reg 51) (.const 0) : Expr).eval w s₆ = some 1 := by
      simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hr51_0, h0_w, hw]
    rcases alg105Step2Prog_exec p ξ δ ω C41 c41 prog41 OutRel h41 G_i Z_i t₀ par₀ f_tau₀
        hZ_card hw3 hnn_w henc_w hm_w hw41_i hG17_6 hZ9_6 hr26_6 hr27_6 hr28_6 hr52_6
        hb2_len₆ hb2_get₆ hb3_len₆ hb3_get₆ hbd₆ with
      ⟨s₇, t₇, hex₇, ht₇, hr40_7, hout₇⟩
    have hex_ite : Exec w
        (.ite (.op .eq (.reg 51) (.const 0))
          (alg105Step2Prog p prog41)
          (.ite (.op .eq (.reg 51) (.const 1))
            (alg105Step3Prog ξ δ)
            (alg105Step4Prog p prog104)))
        s₆ s₇ (3 + t₇) :=
      .ite_true hcond0 (by decide) hex₇
    have ht_N : 6 + (t₂ + (t₃ + (t₄ + (t₅ + (t₆ + (3 + t₇)))))) ≤ K_body * N ^ 2 := by
      have hK : 300 + C99 + (450 + C41) ≤ K_body := by dsimp [K_body]; omega
      have hmul := Nat.mul_le_mul_right (N ^ 2) hK
      rw [Nat.add_mul, Nat.add_mul] at hmul
      change t₇ ≤ (450 + C41) * N ^ 2 at ht₇
      generalize N ^ 2 = N2 at hpre_bound ht6_bound ht₇ hmul ⊢
      omega
    have ht_total : 6 + (t₂ + (t₃ + (t₄ + (t₅ + (t₆ + (3 + t₇)))))) ≤
        K_body * (alg65Const ξ δ + 1) ^ 2 * (x.n + 1) ^ 2 := by
      rw [Nat.mul_assoc]
      exact le_trans ht_N (Nat.mul_le_mul_left K_body hN_sq_le)
    exact ⟨s₇, 6 + (t₂ + (t₃ + (t₄ + (t₅ + (t₆ + (3 + t₇)))))),
      .seq hex₁ (.seq hex₂ (.seq hex₃ (.seq hex₄ (.seq hex₅ (.seq hex₆ hex_ite))))),
      ht_total, Or.inl ⟨hr40_7, hout₇ x hst.hZ_eq hst.hfolio⟩⟩
  · -- Case (ii): `r_51 = 1` (`alg105Step3Prog`)
    have hcond0 : (.op .eq (.reg 51) (.const 0) : Expr).eval w s₆ = some 0 := by
      simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hr51_1, h0_w, hw]
    have hcond1 : (.op .eq (.reg 51) (.const 1) : Expr).eval w s₆ = some 1 := by
      simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hr51_1, hw]
    rcases alg105Step3Prog_exec ξ δ x G_i Z_i X hw3 h2n_w hp_w hpn_w henc_w hm_w
        hmodel_del hst.hn_le hst.hZ_eq hst.hedges_le hst.hfolio
        hG17_6 hZ9_6 hr26_6 hr27_6 hr28_6 hb2_6 with
      ⟨n', G_next, Z_next, s₇, t₇, hni_eq, hex₇, ht₇, hst₇⟩
    have hex_ite1 : Exec w
        (.ite (.op .eq (.reg 51) (.const 1))
          (alg105Step3Prog ξ δ)
          (alg105Step4Prog p prog104))
        s₆ s₇ (3 + t₇) :=
      .ite_true hcond1 (by decide) hex₇
    have hex_ite0 : Exec w
        (.ite (.op .eq (.reg 51) (.const 0))
          (alg105Step2Prog p prog41)
          (.ite (.op .eq (.reg 51) (.const 1))
            (alg105Step3Prog ξ δ)
            (alg105Step4Prog p prog104)))
        s₆ s₇ (3 + (3 + t₇)) :=
      .ite_false hcond0 hex_ite1
    have ht_N : 6 + (t₂ + (t₃ + (t₄ + (t₅ + (t₆ + (3 + (3 + t₇))))))) ≤ K_body * N ^ 2 := by
      have hK : 300 + C99 + (600 + p * (ξ + 1) * 800) ≤ K_body := by dsimp [K_body]; omega
      have hmul := Nat.mul_le_mul_right (N ^ 2) hK
      rw [Nat.add_mul, Nat.add_mul] at hmul
      change t₇ ≤ (600 + p * (ξ + 1) * 800) * N ^ 2 at ht₇
      generalize N ^ 2 = N2 at hpre_bound ht6_bound ht₇ hmul ⊢
      omega
    have ht_total : 6 + (t₂ + (t₃ + (t₄ + (t₅ + (t₆ + (3 + (3 + t₇))))))) ≤
        K_body * (alg65Const ξ δ + 1) ^ 2 * (x.n + 1) ^ 2 := by
      rw [Nat.mul_assoc]
      exact le_trans ht_N (Nat.mul_le_mul_left K_body hN_sq_le)
    exact ⟨s₇, 6 + (t₂ + (t₃ + (t₄ + (t₅ + (t₆ + (3 + (3 + t₇))))))),
      .seq hex₁ (.seq hex₂ (.seq hex₃ (.seq hex₄ (.seq hex₅ (.seq hex₆ hex_ite0))))),
      ht_total, Or.inr ⟨n', G_next, Z_next, hni_eq, hst₇⟩⟩
  · -- Case (iii): `r_51 = 2` (`alg105Step4Prog`)
    have hcond0 : (.op .eq (.reg 51) (.const 0) : Expr).eval w s₆ = some 0 := by
      simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hr51_2, h0_w, hw2]
    have hcond1 : (.op .eq (.reg 51) (.const 1) : Expr).eval w s₆ = some 0 := by
      simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hr51_2, h0_w, hw, hw2]
    have hw104_i : wordSize c104 (N + block.length) ≤ w := by
      have hlen_le : N + block.length ≤ (C99 + 1) * (alg65Const ξ δ + 1) * (x.n + 1) := by
        have h1 : block.length ≤ C99 * N := le_trans hblock_len (Nat.mul_le_mul_left C99 hN_del_le_N)
        have h2 : N + block.length ≤ (C99 + 1) * N := by rw [Nat.add_mul, Nat.one_mul]; omega
        rw [Nat.mul_assoc]
        exact le_trans h2 (Nat.mul_le_mul_left (C99 + 1) hN_le_max)
      exact le_trans (wordSize_mono_right c104 hlen_le) hw104
    rcases alg105Step4Prog_exec dec ξ δ h ω C104 c104 prog104 h104 x G_i Z_i X block
        hw3 hn_w henc_w hedges_w hw104_i hdisj hX_lt hheight hflat hsoc hrural hbw
        hst.hn_le hst.hZ_eq hst.hedges_le hst.hfolio
        hG17_6 hZ9_6 hr26_6 hr27_6 hb2_6 hb3_6 with
      ⟨n', G_next, Z_next, s₇, t₇, hni_eq, hex₇, ht₇, hst₇⟩
    have hex_ite1 : Exec w
        (.ite (.op .eq (.reg 51) (.const 1))
          (alg105Step3Prog ξ δ)
          (alg105Step4Prog p prog104))
        s₆ s₇ (3 + t₇) :=
      .ite_false hcond1 hex₇
    have hex_ite0 : Exec w
        (.ite (.op .eq (.reg 51) (.const 0))
          (alg105Step2Prog p prog41)
          (.ite (.op .eq (.reg 51) (.const 1))
            (alg105Step3Prog ξ δ)
            (alg105Step4Prog p prog104)))
        s₆ s₇ (3 + (3 + t₇)) :=
      .ite_false hcond0 hex_ite1
    have ht_N : 6 + (t₂ + (t₃ + (t₄ + (t₅ + (t₆ + (3 + (3 + t₇))))))) ≤ K_body * N ^ 2 := by
      have hK : 300 + C99 + (300 + C104) ≤ K_body := by dsimp [K_body]; omega
      have hmul := Nat.mul_le_mul_right (N ^ 2) hK
      rw [Nat.add_mul, Nat.add_mul] at hmul
      change t₇ ≤ (300 + C104) * N ^ 2 at ht₇
      generalize N ^ 2 = N2 at hpre_bound ht6_bound ht₇ hmul ⊢
      omega
    have ht_total : 6 + (t₂ + (t₃ + (t₄ + (t₅ + (t₆ + (3 + (3 + t₇))))))) ≤
        K_body * (alg65Const ξ δ + 1) ^ 2 * (x.n + 1) ^ 2 := by
      rw [Nat.mul_assoc]
      exact le_trans ht_N (Nat.mul_le_mul_left K_body hN_sq_le)
    exact ⟨s₇, 6 + (t₂ + (t₃ + (t₄ + (t₅ + (t₆ + (3 + (3 + t₇))))))),
      .seq hex₁ (.seq hex₂ (.seq hex₃ (.seq hex₄ (.seq hex₅ (.seq hex₆ hex_ite0))))),
      ht_total, Or.inr ⟨n', G_next, Z_next, hni_eq, hst₇⟩⟩

theorem alg105Loop_exec {w : ℕ} (dec : Case3BlockDecoder)
    (ξ δ h ω C99 c99 C104 c104 C41 c41 : ℕ) (prog99 prog104 prog41 : Cmd)
    (h99 : ∀ {w n_i : ℕ} (G_i : MultiDigraph n_i) (Z_i : Finset (Fin n_i)) (s : State),
      let p := alg62Param ξ δ
      let b := alg105ArrBase p
      let D_del := G_i.deleteVertices Z_i
      let N := n_i + D_del.numEdges + 1
      wordSize c99 N ≤ w →
      s.arrs b = D_del.enc →
      s.arrs (b + 1) = bitSetList Z_i →
      ∃ s' time,
        Exec w prog99 s s' time ∧
        time ≤ C99 * (n_i + 1) * N ∧
        (∀ r < 50, s'.regs r = s.regs r) ∧
        (∀ a < b, s'.arrs a = s.arrs a) ∧
        ((s'.regs 51 = 0 ∧
            ∃ (t : ℕ) (par f_tau : ℕ → ℕ),
              s'.regs 52 = t ∧
              (s'.arrs (b + 2)).length = t ∧
              (∀ z < t, (s'.arrs (b + 2)).getD z 0 = par z) ∧
              (s'.arrs (b + 3)).length = D_del.numEdges ∧
              (∀ e < D_del.numEdges, (s'.arrs (b + 3)).getD e 0 = f_tau e) ∧
              IsWrittenDigraphBD ω D_del.toComputeDigraph t par f_tau) ∨
         (s'.regs 51 = 1 ∧
            ∃ X : Fin p → Finset (Fin n_i),
              s'.arrs (b + 2) = encBitSetsUpTo X p ∧
              (∀ j : Fin p, Disjoint (X j) Z_i) ∧
              IsCliqueModel D_del.toSimpleGraph p X) ∨
         (s'.regs 51 = 2 ∧
            ∃ (X : Finset (Fin n_i)) (block : List ℕ),
              s'.arrs (b + 2) = bitSetList X ∧
              s'.arrs (b + 3) = block ∧
              block.length ≤ C99 * N ∧
              (∀ x_b ∈ block, x_b < 2 ^ w) ∧
              Disjoint X Z_i ∧
              X.card < p.choose 2 ∧
              let X' := X ∪ Z_i
              let H := dec.wall n_i G_i X' block
              let S_H := dec.society n_i G_i X' block
              let 𝒜 := dec.division n_i G_i X' block
              H.height = h ∧
              GM13.IsFlatWallIn
                (deleteVertices (G_i.toGMDigraph.deleteVertices Z_i.toNatSet).toGraph
                  X.toNatSet) H ∧
              GM13.IsWallSociety
                (deleteVertices (G_i.toGMDigraph.deleteVertices Z_i.toNatSet).toGraph
                  X.toNatSet) H S_H ∧
              GM13.IsRuralDivision S_H 𝒜 ∧
              ∀ ⦃A : Graph ℕ (ℕ × ℕ × ℕ)⦄,
                GM13.IsInteriorMember H 𝒜 A →
                  let bd := dec.branchDecomp n_i G_i X' block A
                  E(A).ncard ≤ 1 ∨
                    (GM13.IsGraphBranchDecomposition A bd.2.1 bd.2.2 ∧
                      GM13.graphBranchDecompWidth A bd.2.1 bd.2.2 ≤ ω))))
    (h104 : ∀ {w n_i : ℕ} (G_i : MultiDigraph n_i) (X' : Finset (Fin n_i))
      (block : List ℕ) (s : State),
      let p := alg62Param ξ δ
      let q := p.choose 2 + ξ - 1
      let b := alg105ArrBase p
      let N := n_i + G_i.numEdges + 1
      let H := dec.wall n_i G_i X' block
      let S_H := dec.society n_i G_i X' block
      let 𝒜 := dec.division n_i G_i X' block
      wordSize c104 (N + block.length) ≤ w →
      X'.card ≤ q →
      GM13.HypothesisC G_i.toGMDigraph X'.toNatSet.ncard X'.toNatSet H S_H 𝒜 →
      H.height = h →
      (∀ ⦃A : Graph ℕ (ℕ × ℕ × ℕ)⦄,
        GM13.IsInteriorMember H 𝒜 A →
          let bd := dec.branchDecomp n_i G_i X' block A
          E(A).ncard ≤ 1 ∨
            (GM13.IsGraphBranchDecomposition A bd.2.1 bd.2.2 ∧
              GM13.graphBranchDecompWidth A bd.2.1 bd.2.2 ≤ ω)) →
      s.arrs b = G_i.enc →
      s.arrs (b + 1) = bitSetList X' →
      s.arrs (b + 3) = block →
      ∃ (s' : State) (time : ℕ) (v : Fin n_i),
        Exec w prog104 s s' time ∧
        time ≤ C104 * N ^ 2 ∧
        s'.regs 51 = v.1 ∧
        GM13.IsIrrelevantVertex G_i.toGMDigraph δ X'.toNatSet v.1 ∧
        (∀ r < 50, s'.regs r = s.regs r) ∧
        (∀ a < b, s'.arrs a = s.arrs a))
    (OutRel : FolioInput ξ → List ℕ → Prop)
    (h41 : ∀ {w n_i : ℕ} (G_i : MultiDigraph n_i) (Z_i : Finset (Fin n_i))
      (t : ℕ) (par f_tau : ℕ → ℕ) (s : State),
      let p := alg62Param ξ δ
      let b := alg105ArrBase p
      let N := n_i + G_i.numEdges + 1
      wordSize c41 N ≤ w →
      Z_i.card ≤ ξ →
      IsWrittenDigraphBD (max ω 2 + ξ) G_i.toComputeDigraph t par f_tau →
      s.arrs b = G_i.enc →
      s.arrs (b + 1) = bitSetList Z_i →
      s.regs 26 = n_i →
      s.regs 28 = G_i.numEdges →
      s.regs 52 = t →
      (s.arrs (b + 2)).length = t →
      (∀ z < t, (s.arrs (b + 2)).getD z 0 = par z) →
      (s.arrs (b + 3)).length = G_i.numEdges →
      (∀ e < G_i.numEdges, (s.arrs (b + 3)).getD e 0 = f_tau e) →
      s.arrs (b + 5) =
        List.ofFn (fun e : Fin G_i.toComputeDigraph.numEdges => (G_i.toComputeDigraph.tail e).1) →
      s.arrs (b + 6) =
        List.ofFn (fun e : Fin G_i.toComputeDigraph.numEdges => (G_i.toComputeDigraph.head e).1) →
      ∃ (s' : State) (time : ℕ),
        Exec w prog41 s s' time ∧
        time ≤ C41 * N ∧
        ∀ (x : FolioInput ξ) (hZ_eq : Z_i.card = x.Z.card),
          (∀ F : FolioSetRep Z_i.card δ,
            IsDeltaFolioRep δ G_i Z_i F → IsDeltaFolioRep δ x.G x.Z (F.castCard hZ_eq)) →
          OutRel x (s'.arrs outArr))
    (x : FolioInput ξ)
    (hw3 : 3 < 2 ^ w)
    (hnn0_w : x.n * x.n < 2 ^ w)
    (h2n0_w : 2 * x.n < 2 ^ w)
    (hp_w : alg62Param ξ δ < 2 ^ w)
    (hpn0_w : (alg62Param ξ δ + 2) * x.n < 2 ^ w)
    (hm_max_w : 2 * (alg65Const ξ δ * x.n) + 1 < 2 ^ w)
    (henc_max_w : 2 + 3 * (alg65Const ξ δ * x.n) < 2 ^ w)
    (hw99 : wordSize c99 ((alg65Const ξ δ + 1) * (x.n + 1)) ≤ w)
    (hw104 : wordSize c104 ((C99 + 1) * (alg65Const ξ δ + 1) * (x.n + 1)) ≤ w)
    (hw41 : wordSize c41 ((alg65Const ξ δ + 1) * (x.n + 1)) ≤ w) :
    let p := alg62Param ξ δ
    let K_iter := (900 + p * (ξ + 1) * 800 + C99 + C104 + C41) * (alg65Const ξ δ + 1) ^ 2
    ∀ (n_i : ℕ) (G_i : MultiDigraph n_i) (Z_i : Finset (Fin n_i)) {s : State},
      Alg105LoopState ξ δ x n_i G_i Z_i s →
      ∃ s' time,
        Exec w (alg105LoopProg ξ δ prog99 prog104 prog41) s s' time ∧
        time ≤ (n_i + 1) * (10 + K_iter * (x.n + 1) ^ 2) ∧
        OutRel x (s'.arrs outArr) := by
  intro p K_iter n_i
  have h0_w : 0 < 2 ^ w := by omega
  have hw : 1 < 2 ^ w := by omega
  induction n_i with
  | zero =>
    intro G_i Z_i s hst
    have hcond : (Expr.reg 40).eval w s = some 1 := by
      simp [Expr.eval, checkWord, hst.hr40, hw]
    rcases alg105LoopBody_exec dec ξ δ h ω C99 c99 C104 c104 C41 c41 prog99 prog104 prog41
        h99 h104 OutRel h41 x G_i Z_i hw3 hnn0_w h2n0_w hp_w hpn0_w hm_max_w henc_max_w
        hw99 hw104 hw41 hst with
      ⟨s₁, t₁, hex₁, ht₁, ⟨hr40_1, hvalid⟩ | ⟨n', _, _, h0_eq, _⟩⟩
    · have hcond_end : (Expr.reg 40).eval w s₁ = some 0 := by
        simp [Expr.eval, checkWord, hr40_1, h0_w]
      exact ⟨s₁, 1 + t₁ + 1, .while_true hcond (by decide) hex₁ (.while_false hcond_end),
        by dsimp [K_iter, p] at ht₁ ⊢; omega, hvalid⟩
    · omega
  | succ n' ih =>
    intro G_i Z_i s hst
    have hcond : (Expr.reg 40).eval w s = some 1 := by
      simp [Expr.eval, checkWord, hst.hr40, hw]
    rcases alg105LoopBody_exec dec ξ δ h ω C99 c99 C104 c104 C41 c41 prog99 prog104 prog41
        h99 h104 OutRel h41 x G_i Z_i hw3 hnn0_w h2n0_w hp_w hpn0_w hm_max_w henc_max_w
        hw99 hw104 hw41 hst with
      ⟨s₁, t₁, hex₁, ht₁, ⟨hr40_1, hvalid⟩ | ⟨n'', G_next, Z_next, hni_eq, hst₁⟩⟩
    · have hcond_end : (Expr.reg 40).eval w s₁ = some 0 := by
        simp [Expr.eval, checkWord, hr40_1, h0_w]
      have hle : 1 * (10 + K_iter * (x.n + 1) ^ 2) ≤
          (n' + 1 + 1) * (10 + K_iter * (x.n + 1) ^ 2) :=
        Nat.mul_le_mul_right _ (by omega)
      rw [Nat.one_mul] at hle
      exact ⟨s₁, 1 + t₁ + 1, .while_true hcond (by decide) hex₁ (.while_false hcond_end),
        by dsimp [K_iter, p] at ht₁ hle ⊢; omega, hvalid⟩
    · have hn''_eq : n' = n'' := by omega
      subst hn''_eq
      rcases ih G_next Z_next hst₁ with ⟨s₂, t₂, hex₂, ht₂, hvalid⟩
      have hmul : (n' + 1 + 1) * (10 + K_iter * (x.n + 1) ^ 2) =
          (n' + 1) * (10 + K_iter * (x.n + 1) ^ 2) + (10 + K_iter * (x.n + 1) ^ 2) :=
        Nat.succ_mul (n' + 1) _
      refine ⟨s₂, 1 + t₁ + t₂, .while_true hcond (by decide) hex₁ hex₂, ?_, hvalid⟩
      rw [hmul]; dsimp [K_iter, p] at ht₁ ht₂ ⊢; omega

/-! ### Section 7: Complete Algorithm (10.5), `FolioStatement`, and `DisjointPathsStatement` -/

/-- Step (1) of GM XIII Algorithm (10.5) (page 108):
applies Algorithm (6.5) (`capMultiDigraphProg` + `alg65LoopProg`) to `(G, Z)` to obtain a
subdigraph `G' = G_1` with `|E(G_1)| ≤ C |V(G_1)|` in array `18 + p` and `bitSetList Z_1` in array
`18 + p + 1`, then sets `r_40 := 1` and enters the recursion loop `alg105LoopProg`. -/
def alg105Prog (ξ δ : ℕ) (prog99 prog104 prog41 : Cmd) : Cmd :=
  let p := alg62Param ξ δ
  .seq (.assign 26 (.read inArr (.const 0)))
    (.seq (initIdArrProg (18 + p + 2) 26 29)
      (.seq (.assign 27 (.read inArr (.const 1)))
        (.seq (.assign 29 (.op .add (.const 2) (.op .mul (.const 3) (.reg 27))))
          (.seq (readSliceProg inArr (.reg 29) (18 + p + 1) (.reg 26) 30)
            (.seq (capMultiDigraphProg δ inArr 2 (18 + p) 26)
              (.seq (alg65LoopProg ξ δ)
                (.seq (.assign 40 (.const 1))
                  (alg105LoopProg ξ δ prog99 prog104 prog41))))))))

theorem algorithm_10_5_core (ξ δ h ω : ℕ) (dec : Case3BlockDecoder)
    (OutRel : FolioInput ξ → List ℕ → Prop)
    (h99_spec : Alg99Spec dec (alg62Param ξ δ) h ω)
    (h104_spec : Alg104Spec dec (alg62Param ξ δ) ((alg62Param ξ δ).choose 2 + ξ - 1) δ h ω)
    (prog41 : Cmd) (C41 c41 : ℕ)
    (h41 : ∀ {w n_i : ℕ} (G_i : MultiDigraph n_i) (Z_i : Finset (Fin n_i))
      (t : ℕ) (par f_tau : ℕ → ℕ) (s : State),
      let p := alg62Param ξ δ
      let b := alg105ArrBase p
      let N := n_i + G_i.numEdges + 1
      wordSize c41 N ≤ w →
      Z_i.card ≤ ξ →
      IsWrittenDigraphBD (max ω 2 + ξ) G_i.toComputeDigraph t par f_tau →
      s.arrs b = G_i.enc →
      s.arrs (b + 1) = bitSetList Z_i →
      s.regs 26 = n_i →
      s.regs 28 = G_i.numEdges →
      s.regs 52 = t →
      (s.arrs (b + 2)).length = t →
      (∀ z < t, (s.arrs (b + 2)).getD z 0 = par z) →
      (s.arrs (b + 3)).length = G_i.numEdges →
      (∀ e < G_i.numEdges, (s.arrs (b + 3)).getD e 0 = f_tau e) →
      s.arrs (b + 5) =
        List.ofFn (fun e : Fin G_i.toComputeDigraph.numEdges => (G_i.toComputeDigraph.tail e).1) →
      s.arrs (b + 6) =
        List.ofFn (fun e : Fin G_i.toComputeDigraph.numEdges => (G_i.toComputeDigraph.head e).1) →
      ∃ (s' : State) (time : ℕ),
        Exec w prog41 s s' time ∧
        time ≤ C41 * N ∧
        ∀ (x : FolioInput ξ) (hZ_eq : Z_i.card = x.Z.card),
          (∀ F : FolioSetRep Z_i.card δ,
            IsDeltaFolioRep δ G_i Z_i F → IsDeltaFolioRep δ x.G x.Z (F.castCard hZ_eq)) →
          OutRel x (s'.arrs outArr)) :
    ∃ P : Cmd,
      ComputesArrRelInTime (folioSize (ξ := ξ)) encFolioIn OutRel P
        (fun v => (v + 1) ^ 3) := by
  let p := alg62Param ξ δ
  let C_alg := alg65Const ξ δ
  let K_iter65 := alg65IterConst ξ δ
  rcases h99_spec with ⟨prog99, C99, c99, hc99_pos, hC99_pos, h99⟩
  rcases h104_spec with ⟨prog104, C104, c104, hc104_pos, hC104_pos, h104⟩
  let K_iter105 := (900 + p * (ξ + 1) * 800 + C99 + C104 + C41) * (C_alg + 1) ^ 2
  let c_total := (2 * p + 4) + c99 * (C_alg + 1 + 3) +
    c104 * ((C99 + 1) * (C_alg + 1) + 3) + c41 * (C_alg + 1 + 3)
  let C_total := 500 + K_iter65 + K_iter105
  have hp_pos : 1 ≤ p := by dsimp [p, alg62Param]; omega
  refine ⟨alg105Prog ξ δ prog99 prog104 prog41, C_total, c_total,
    by omega, by omega, fun x s₀ hs₀ => ?_⟩
  set w := wordSize c_total (folioSize x)
  have hw_base : wordSize (2 * p + 4) x.n ≤ w :=
    wordSize_mono_left (by dsimp [c_total]; omega) x.n
  have hw99 : wordSize c99 ((C_alg + 1) * (x.n + 1)) ≤ w :=
    le_trans (wordSize_le_of_le_mul le_rfl)
      (wordSize_mono_left (by dsimp [c_total]; omega) x.n)
  have hw104 : wordSize c104 ((C99 + 1) * (C_alg + 1) * (x.n + 1)) ≤ w :=
    le_trans (wordSize_le_of_le_mul le_rfl)
      (wordSize_mono_left (by dsimp [c_total]; omega) x.n)
  have hw41 : wordSize c41 ((C_alg + 1) * (x.n + 1)) ≤ w :=
    le_trans (wordSize_le_of_le_mul le_rfl)
      (wordSize_mono_left (by dsimp [c_total]; omega) x.n)
  have hpow_full : (x.n + 2) ^ (2 * p + 4) < 2 ^ w :=
    Nat.lt_of_lt_of_le (pow_lt_two_pow_wordSize (c := 2 * p + 4) (by omega) x.n)
      (Nat.pow_le_pow_right (by omega) hw_base)
  have h2_le_base : 2 ≤ x.n + 2 := by omega
  have h2_pow_lt : 2 ^ (2 * p + 4) ≤ (x.n + 2) ^ (2 * p + 4) :=
    Nat.pow_le_pow_left h2_le_base (2 * p + 4)
  have hw6 : 64 ≤ 2 ^ w := by
    have h6 : 6 ≤ 2 * p + 4 := by omega
    have h64 : 64 = 2 ^ 6 := by decide
    rw [h64]
    exact le_trans (Nat.pow_le_pow_right (by omega) h6)
      (le_trans h2_pow_lt (Nat.le_of_lt hpow_full))
  have h0_w : 0 < 2 ^ w := by omega
  have hw : 1 < 2 ^ w := by omega
  have hw2 : 2 < 2 ^ w := by omega
  have hw3 : 3 < 2 ^ w := by omega
  have hpow_le : ∀ j ≤ 2 * p + 4, (x.n + 2) ^ j < 2 ^ w := by
    intro j hj
    exact Nat.lt_of_le_of_lt (Nat.pow_le_pow_right (by omega) hj) hpow_full
  have hpow1 : x.n + 2 < 2 ^ w := by simpa using hpow_le 1 (by omega)
  have hpow2 : (x.n + 2) ^ 2 < 2 ^ w := hpow_le 2 (by omega)
  have hpow_64_w : (x.n + 2) ^ (p + 2) < 2 ^ w := hpow_le (p + 2) (by omega)
  have hm_sq : x.G.numActivePairs ≤ x.n * x.n := x.G.numActivePairs_le_sq
  have h8sq_w : 8 * (x.n * x.n) + 32 * x.n + 32 < 2 ^ w := by
    have h1 : 8 ≤ (x.n + 2) ^ 3 := by
      have h8 : 8 = 2 ^ 3 := by decide
      rw [h8]
      exact Nat.pow_le_pow_left h2_le_base 3
    have h2 : 8 * (x.n + 2) ^ 2 ≤ (x.n + 2) ^ 3 * (x.n + 2) ^ 2 :=
      Nat.mul_le_mul_right _ h1
    have h3 : (x.n + 2) ^ 3 * (x.n + 2) ^ 2 = (x.n + 2) ^ 5 := by
      rw [← Nat.pow_add]
    have h4 : 8 * (x.n * x.n) + 32 * x.n + 32 = 8 * (x.n + 2) ^ 2 := by
      rw [Nat.pow_two, Nat.add_mul, Nat.mul_add, Nat.mul_add]; omega
    have h5 : (x.n + 2) ^ 5 < 2 ^ w := hpow_le 5 (by omega)
    omega
  have hn0_w : x.n < 2 ^ w := by omega
  have h2n0_w : 2 * x.n < 2 ^ w := by omega
  have hnn0_w : x.n * x.n < 2 ^ w := by omega
  have hm3_in_w : 2 + 3 * x.G.numActivePairs < 2 ^ w := by omega
  have hm3_plus_n_w : 2 + 3 * x.G.numActivePairs + x.n < 2 ^ w := by omega
  have hcap_le_G : (x.G.cap δ).numActivePairs ≤ x.G.numActivePairs := by
    simp only [MultiDigraph.numActivePairs, MultiDigraph.activePairsList_cap]
    exact List.length_filter_le _ _
  have hm3_cap_w : 2 + 3 * (x.G.cap δ).numActivePairs < 2 ^ w := by omega
  have hδ1_le_2p : δ + 1 ≤ 2 ^ p := by
    have hδ_lt_p : δ < p := by dsimp [p, alg62Param]; omega
    exact le_trans hδ_lt_p (Nat.le_of_lt Nat.lt_two_pow_self)
  have hδ_w : δ + 1 < 2 ^ w := by
    have h1 : 2 ^ p ≤ (x.n + 2) ^ p := Nat.pow_le_pow_left h2_le_base p
    have h2 : (x.n + 2) ^ p < 2 ^ w := hpow_le p (by omega)
    omega
  have hedges_cap_le : (x.G.cap δ).numEdges ≤ (δ + 1) * (x.n * x.n) :=
    numEdges_le_of_edgeMult_le (x.G.cap δ) (δ + 1) (x.G.cap_edgeMult_le_succ δ)
  have hedges_cap_w : (x.G.cap δ).numEdges < 2 ^ w := by
    have h1 : (δ + 1) * (x.n * x.n) ≤ 2 ^ p * (x.n + 2) ^ 2 := by
      refine Nat.mul_le_mul hδ1_le_2p ?_
      rw [Nat.pow_two, Nat.add_mul, Nat.mul_add, Nat.mul_add]; omega
    have h2 : 2 ^ p * (x.n + 2) ^ 2 ≤ (x.n + 2) ^ p * (x.n + 2) ^ 2 :=
      Nat.mul_le_mul_right _ (Nat.pow_le_pow_left h2_le_base p)
    rw [← Nat.pow_add] at h2
    exact Nat.lt_of_le_of_lt (le_trans hedges_cap_le (le_trans h1 h2)) hpow_64_w
  have hp_w : p < 2 ^ w := by
    have h1 : p < 2 ^ p := Nat.lt_two_pow_self
    have h2 : 2 ^ p ≤ (x.n + 2) ^ p := Nat.pow_le_pow_left h2_le_base p
    exact Nat.lt_of_lt_of_le (Nat.lt_of_lt_of_le h1 h2) (Nat.le_of_lt (hpow_le p (by omega)))
  have hpn0_w : (p + 2) * x.n < 2 ^ w := by
    have h1 : p + 2 ≤ 2 ^ (p + 1) := by
      have hp_lt : p < 2 ^ p := Nat.lt_two_pow_self
      have hpow_succ : 2 ^ (p + 1) = 2 ^ p + 2 ^ p := by rw [Nat.pow_succ]; omega
      have hpow_ge2 : 2 ≤ 2 ^ p := by
        have : 2 ^ 1 ≤ 2 ^ p := Nat.pow_le_pow_right (by omega) hp_pos
        simpa using this
      omega
    have h2 : 2 ^ (p + 1) ≤ (x.n + 2) ^ (p + 1) := Nat.pow_le_pow_left h2_le_base (p + 1)
    have h3 : (p + 2) * x.n ≤ (x.n + 2) ^ (p + 1) * (x.n + 2) :=
      Nat.mul_le_mul (le_trans h1 h2) (by omega)
    rw [← Nat.pow_succ] at h3
    exact Nat.lt_of_le_of_lt h3 hpow_64_w
  have hC_le_pow : C_alg ≤ 2 ^ (2 * p + 2) := by
    change δ + 2 * (δ + 1) * 2 ^ (p - 3) ≤ 2 ^ (2 * p + 2)
    have h1 : 2 ^ (p - 3) ≤ 2 ^ p := Nat.pow_le_pow_right (by omega) (by omega)
    have h2 : 2 * (δ + 1) * 2 ^ (p - 3) ≤ 2 * 2 ^ p * 2 ^ p :=
      Nat.mul_le_mul (Nat.mul_le_mul_left 2 hδ1_le_2p) h1
    have h3 : 2 ^ p + 2 * 2 ^ p * 2 ^ p ≤ 2 ^ (2 * p + 2) := by
      have h4 : 2 * 2 ^ p * 2 ^ p = 2 * 2 ^ (2 * p) := by
        rw [Nat.mul_assoc, ← Nat.pow_add, ← Nat.two_mul]
      have h5 : 2 ^ p ≤ 2 ^ (2 * p) := Nat.pow_le_pow_right (by omega) (by omega)
      have h6 : 2 ^ (2 * p + 2) = 4 * 2 ^ (2 * p) := by
        rw [Nat.pow_add, Nat.mul_comm]
      omega
    exact le_trans (Nat.add_le_add (by omega : δ ≤ 2 ^ p) h2) h3
  have hC_pow_bound : C_alg * (x.n + 2) ≤ (x.n + 2) ^ (2 * p + 3) := by
    have h1 : C_alg * (x.n + 2) ≤ (x.n + 2) ^ (2 * p + 2) * (x.n + 2) :=
      Nat.mul_le_mul_right (x.n + 2)
        (le_trans hC_le_pow (Nat.pow_le_pow_left h2_le_base (2 * p + 2)))
    rwa [← Nat.pow_succ] at h1
  have hC_n_w : C_alg < 2 ^ w ∧ C_alg * x.n < 2 ^ w := by
    have h3 : (x.n + 2) ^ (2 * p + 3) < 2 ^ w := hpow_le (2 * p + 3) (by omega)
    have h4 : C_alg ≤ C_alg * (x.n + 2) := Nat.le_mul_of_pos_right _ (by omega)
    have h5 : C_alg * x.n ≤ C_alg * (x.n + 2) := Nat.mul_le_mul_left C_alg (by omega)
    omega
  have h3C_w : 2 + 3 * (C_alg * x.n) < 2 ^ w := by
    have hC_pos : 1 ≤ C_alg := by
      dsimp [C_alg, alg65Const]
      have : 0 < 2 * (δ + 1) * 2 ^ (alg62Param ξ δ - 3) :=
        Nat.mul_pos (by omega) (Nat.two_pow_pos _)
      omega
    have h1 : 3 * (C_alg * x.n) + 2 ≤ (x.n + 2) * (C_alg * (x.n + 2)) := by
      have hexp : (x.n + 2) * (C_alg * (x.n + 2)) =
          x.n * (C_alg * x.n) + (C_alg * x.n) * 2 + 2 * (C_alg * x.n) + 2 * (C_alg * 2) := by
        rw [Nat.mul_add C_alg x.n 2, Nat.add_mul x.n 2 _, Nat.mul_add x.n, Nat.mul_add 2,
          ← Nat.mul_assoc x.n C_alg 2, Nat.mul_comm x.n C_alg, ← Nat.add_assoc]
      rw [hexp]
      omega
    have h2 : (x.n + 2) * (C_alg * (x.n + 2)) ≤ (x.n + 2) * (x.n + 2) ^ (2 * p + 3) :=
      Nat.mul_le_mul_left (x.n + 2) hC_pow_bound
    have h3 : (x.n + 2) * (x.n + 2) ^ (2 * p + 3) = (x.n + 2) ^ (2 * p + 4) := by
      rw [Nat.mul_comm, ← Nat.pow_succ]
    omega
  have hm_max_w : 2 * (C_alg * x.n) + 1 < 2 ^ w := by omega
  -- Step (1): Execute Algorithm (6.5) on `x65 = ⟨x.n, x.G, x.Z, x.hZ⟩`
  let x65 : Alg65Input ξ δ := ⟨x.n, x.G, x.Z, x.hZ⟩
  have hin₀ : s₀.arrs inArr = x.G.enc ++ bitSetList x.Z := hs₀
  obtain ⟨h0_len, h0_val⟩ := enc_getElem_zero x.G _ hin₀
  let s₀' := s₀.setReg 26 x.n
  have hex₀' : Exec w (.assign 26 (.read inArr (.const 0))) s₀ s₀' 3 :=
    .assign (by simp [Expr.eval, checkWord, h0_w, h0_len, h0_val, hn0_w])
  rcases initIdArrProg_exec (18 + p + 2) 26 29 (by decide) hw hn0_w
      (s := s₀') (by simp [s₀']) with
    ⟨s₁, t₁, hex₁, ht₁, hemb₁, harr₁, hreg₁⟩
  have hin₁ : s₁.arrs inArr = x.G.enc ++ bitSetList x.Z := by
    rw [harr₁ inArr (by dsimp [inArr]; omega)]; exact hin₀
  have hr26_1 : s₁.regs 26 = x.n := by
    rw [hreg₁ 26 (by decide)]; rfl
  obtain ⟨h1_len, h1_val⟩ := enc_getElem_one x.G _ hin₁
  have hm_in_w : x.G.numActivePairs < 2 ^ w := by omega
  let s₂ := s₁.setReg 27 x.G.numActivePairs
  have hex₂ : Exec w (.assign 27 (.read inArr (.const 1))) s₁ s₂ 3 :=
    .assign (by simp [Expr.eval, checkWord, hw, h1_len, h1_val, hm_in_w])
  let s₃ := s₂.setReg 29 (2 + 3 * x.G.numActivePairs)
  have hex₃ : Exec w (.assign 29 (.op .add (.const 2) (.op .mul (.const 3) (.reg 27)))) s₂ s₃ 6 :=
    .assign (by simp [s₂, State.setReg, Expr.eval, BinOp.eval, BinOp.raw, checkWord,
      hw2, hw3, hm_in_w, show 3 * x.G.numActivePairs < 2 ^ w by omega, hm3_in_w])
  have hZ_w : ∀ b_z ∈ bitSetList x.Z, b_z < 2 ^ w := by
    intro b_z hb
    rcases List.mem_iff_getElem.mp hb with ⟨idx, hidx, rfl⟩
    have hle1 := getElem_bitSetList_le_one x.Z idx hidx
    omega
  have hin₃ : s₃.arrs inArr = x.G.enc ++ bitSetList x.Z ++ [] := by
    change s₁.arrs inArr = _
    rw [List.append_nil]; exact hin₁
  rcases readSliceProg_exec inArr (18 + p + 1) (.reg 29) 26 30
      (by dsimp [inArr]; omega) (by decide)
      x.G.enc (bitSetList x.Z) []
      x.G.length_enc (length_bitSetList x.Z) hZ_w hw hm3_plus_n_w
      (s := s₃)
      (by simp [s₃, Expr.eval, checkWord, hm3_in_w])
      hin₃
      (by change s₁.regs 26 = x.n; exact hr26_1) with
    ⟨s₄, t₄, hex₄, ht₄, hZ_arr₄, harr₄, _⟩
  dsimp [Expr.cost] at ht₄
  have hin₄ : s₄.arrs inArr = x.G.enc ++ bitSetList x.Z := by
    rw [harr₄ inArr (by dsimp [inArr]; omega)]; exact hin₁
  rcases capMultiDigraphProg_exec x.G δ (bitSetList x.Z) inArr 2 (18 + p) 26
      (by dsimp [inArr]; omega) (by omega)
      hw3 hn0_w hδ_w hm3_in_w hedges_cap_w hin₄ with
    ⟨s₅, t₅, hex₅, ht₅, hG_arr₅, hr26_5, hr27_5, hr28_5, harr₅, _⟩
  have hst₅ : Alg65LoopState ξ δ x65 x.n (x.G.cap δ) x.Z id s₅ := by
    refine ⟨.refl, hG_arr₅, ?_, ?_, hr26_5, hr27_5, hr28_5⟩
    · rw [harr₅ (18 + p + 1) (by omega) (by omega)]; exact hZ_arr₄
    · rw [harr₅ (18 + p + 2) (by omega) (by omega), harr₄ (18 + p + 2) (by omega)]
      exact hemb₁
  rcases alg65Loop_exec ξ δ x65 hw3 hn0_w h2n0_w hp_w hC_n_w hm3_cap_w hedges_cap_w hpow_64_w
      x.n (x.G.cap δ) x.Z id hst₅ with
    ⟨n₁, G₁, Z₁, emb₁, s₆, t₆, hex₆, ht₆, hedges₁, hst₆⟩
  -- Initialize `r_40 := 1` and build `Alg105LoopState` for `(n₁, G₁, Z₁)`
  let s₇ := s₆.setReg 40 1
  have hex₇ : Exec w (.assign 40 (.const 1)) s₆ s₇ 2 :=
    .assign (by simp [Expr.eval, checkWord, hw])
  have hn₁_le : n₁ ≤ x.n := hst₆.trace.le_num_vertices
  have hedges₁_le : G₁.numEdges ≤ C_alg * x.n :=
    le_trans hedges₁ (Nat.mul_le_mul_left C_alg hn₁_le)
  have hZ₁_eq : Z₁.card = x.Z.card := hst₆.trace.card_Z
  have hfolio₁ : ∀ F : FolioSetRep Z₁.card δ,
      IsDeltaFolioRep δ G₁ Z₁ F → IsDeltaFolioRep δ x.G x.Z (F.castCard hZ₁_eq) := by
    intro F hF
    have hiff := hst₆.trace.forall_isDeltaFolioRep_of_cap x.hZ (F.castCard hZ₁_eq)
    rw [Alg65Trace.castCard_trans] at hiff
    exact hiff.mpr hF
  have hst₇ : Alg105LoopState ξ δ x n₁ G₁ Z₁ s₇ :=
    ⟨hn₁_le, hZ₁_eq, hedges₁_le, hfolio₁,
      by simp [s₇, hst₆.hG_arr],
      by simp [s₇, hst₆.hZ_arr],
      by simp [s₇, State.setReg, hst₆.hr26],
      by simp [s₇, State.setReg, hst₆.hr27],
      by simp [s₇, State.setReg, hst₆.hr28],
      by simp [s₇]⟩
  -- Execute the recursion loop `alg105LoopProg`
  rcases alg105Loop_exec dec ξ δ h ω C99 c99 C104 c104 C41 c41 prog99 prog104 prog41
      h99 h104 OutRel h41 x hw3 hnn0_w h2n0_w hp_w hpn0_w hm_max_w h3C_w hw99 hw104 hw41
      n₁ G₁ Z₁ hst₇ with
    ⟨s₈, t₈, hex₈, ht₈, hvalid₈⟩
  refine ⟨s₈, 3 + (t₁ + (3 + (6 + (t₄ + (t₅ + (t₆ + (2 + t₈))))))),
    .seq hex₀' (.seq hex₁ (.seq hex₂ (.seq hex₃
      (.seq hex₄ (.seq hex₅ (.seq hex₆ (.seq hex₇ hex₈))))))),
    ?_, hvalid₈⟩
  -- Total running time `≤ C_total * (x.n + 1) ^ 3`
  let S := x.n + 1
  have hS_pos : 1 ≤ S := by omega
  have hS3_eq : S ^ 3 = S * S ^ 2 := by
    change S ^ (2 + 1) = S * S ^ 2
    rw [Nat.pow_add, Nat.pow_one, Nat.mul_comm]
  have hS2_eq : S ^ 2 = x.n * x.n + 2 * x.n + 1 := by
    rw [Nat.pow_two, Nat.add_mul, Nat.mul_add, Nat.mul_add]; omega
  have hS2_le_S3 : S ^ 2 ≤ S ^ 3 := by
    rw [hS3_eq]; exact Nat.le_mul_of_pos_left (S ^ 2) hS_pos
  have ht₆_bound : t₆ ≤ 5 * S ^ 2 + K_iter65 * S ^ 3 := by
    change t₆ ≤ 5 + x.n * (5 + K_iter65 * S ^ 2) at ht₆
    have h1 : x.n * (5 + K_iter65 * S ^ 2) = x.n * 5 + x.n * (K_iter65 * S ^ 2) :=
      Nat.mul_add x.n 5 (K_iter65 * S ^ 2)
    have h2 : x.n * (K_iter65 * S ^ 2) ≤ S * (K_iter65 * S ^ 2) :=
      Nat.mul_le_mul_right (K_iter65 * S ^ 2) (by omega)
    have h3 : S * (K_iter65 * S ^ 2) = K_iter65 * S ^ 3 := by
      rw [hS3_eq, ← Nat.mul_assoc, Nat.mul_comm S K_iter65, Nat.mul_assoc]
    have h4 : 5 + x.n * 5 ≤ 5 * S ^ 2 := by omega
    rw [h3] at h2
    rw [h1] at ht₆
    generalize K_iter65 * S ^ 3 = MK65 at h2 ht₆ ⊢
    omega
  have ht₈_bound : t₈ ≤ 10 * S ^ 2 + K_iter105 * S ^ 3 := by
    change t₈ ≤ (n₁ + 1) * (10 + K_iter105 * S ^ 2) at ht₈
    have h1 : (n₁ + 1) * (10 + K_iter105 * S ^ 2) ≤ S * (10 + K_iter105 * S ^ 2) :=
      Nat.mul_le_mul_right (10 + K_iter105 * S ^ 2) (by omega)
    have h2 : S * (10 + K_iter105 * S ^ 2) = S * 10 + S * (K_iter105 * S ^ 2) :=
      Nat.mul_add S 10 (K_iter105 * S ^ 2)
    have h3 : S * (K_iter105 * S ^ 2) = K_iter105 * S ^ 3 := by
      rw [hS3_eq, ← Nat.mul_assoc, Nat.mul_comm S K_iter105, Nat.mul_assoc]
    have h4 : S * 10 ≤ 10 * S ^ 2 := by
      have : S ≤ S ^ 2 := by rw [Nat.pow_two]; exact Nat.le_mul_of_pos_left S hS_pos
      omega
    rw [h2, h3] at h1
    generalize K_iter105 * S ^ 3 = MK105 at h1 ht₈ ⊢
    omega
  have hrest_S3 :
      3 + t₁ + 3 + 6 + t₄ + t₅ + 5 * S ^ 2 + 2 + 10 * S ^ 2 ≤ 500 * S ^ 3 := by
    have h1_S3 : 1 ≤ S ^ 3 := le_trans (by omega : 1 ≤ S ^ 2) hS2_le_S3
    have hn_S3 : x.n ≤ S ^ 3 := le_trans (by omega : x.n ≤ S ^ 2) hS2_le_S3
    have hm_S3 : x.G.numActivePairs ≤ S ^ 3 := le_trans (by omega : x.G.numActivePairs ≤ S ^ 2) hS2_le_S3
    clear ht₆ ht₆_bound ht₈ ht₈_bound hpow_full h2_pow_lt hpow_64_w hC_le_pow hC_pow_bound hC_n_w h3C_w
    omega
  have htotal_expand :
      C_total * S ^ 3 = 500 * S ^ 3 + K_iter65 * S ^ 3 + K_iter105 * S ^ 3 := by
    dsimp [C_total]
    rw [Nat.add_mul, Nat.add_mul]
  change _ ≤ C_total * S ^ 3
  rw [htotal_expand]
  generalize 500 * S ^ 3 = M500 at hrest_S3 ⊢
  generalize K_iter65 * S ^ 3 = MK65 at ht₆_bound ⊢
  generalize K_iter105 * S ^ 3 = MK105 at ht₈_bound ⊢
  clear ht₁ ht₄ ht₅ ht₆ ht₈ hpow_full h2_pow_lt hpow_64_w hC_le_pow hC_pow_bound hC_n_w h3C_w
  omega

/-- **GM XIII Algorithm (10.5)** (Robertson–Seymour, pages 108–109):
For fixed `ξ, δ : ℕ`, with `p = ⌊5ξ/2⌋ + 3δ + 1` (`alg62Param ξ δ`), `q = C(p, 2) + ξ - 1`, `h` as
in (10.3), and `ω` as in (9.8), assuming the subroutine specifications `Alg99Spec` and `Alg104Spec`
(with Step (2) invoking `join41Prog` / `alg41Prog` via `alg41Spec_proved`), there is a Word RAM
program solving the `δ`-Folio problem on any input `(G, Z)` with `|Z| ≤ ξ` in `O(v³)` steps
(`(v + 1)³`), producing an output satisfying `IsValidAlg105Output δ (max ω 2 + ξ)`. -/
theorem gm13_algorithm_10_5 (ξ δ h ω : ℕ) (dec : Case3BlockDecoder)
    (h99_spec : Alg99Spec dec (alg62Param ξ δ) h ω)
    (h104_spec : Alg104Spec dec (alg62Param ξ δ) ((alg62Param ξ δ).choose 2 + ξ - 1) δ h ω) :
    ∃ P : Cmd,
      ComputesArrRelInTime (folioSize (ξ := ξ)) encFolioIn
        (IsValidAlg105Output δ (max ω 2 + ξ)) P (fun v => (v + 1) ^ 3) := by
  rcases alg41Spec_proved (alg62Param ξ δ) ξ δ (max ω 2 + ξ) with
    ⟨prog41, C41, c41, _, _, h41⟩
  refine algorithm_10_5_core ξ δ h ω dec (IsValidAlg105Output δ (max ω 2 + ξ))
    h99_spec h104_spec prog41 C41 c41
    (fun G_i Z_i t par f_tau s hw hZ hbd hb hb1 hr26 hr28 hr52
      hb2_len hb2_get hb3_len hb3_get hb5 hb6 => ?_)
  rcases h41 G_i Z_i t par f_tau s hw hZ hbd hb hb1 hr26 hr28 hr52
      hb2_len hb2_get hb3_len hb3_get hb5 hb6 with
    ⟨s', time, bdCode, hbd_code, hex, htime, hvalid⟩
  exact ⟨s', time, hex, htime, fun x hZ_eq hfolio =>
    ⟨⟨_, G_i, Z_i, hZ, bdCode, hbd_code⟩, hZ_eq, hvalid,
      hfolio hvalid.toFolioSetRep hvalid.isDeltaFolioRep⟩⟩

/-- **Folio Problem in `O(v³)` from `Alg99Spec` and `Alg104Spec` Only**
(GM XIII, (10.5), pages 108–109):
For fixed `δ, ξ : ℕ`, given the two subroutine specifications (`Alg99Spec`, `Alg104Spec`) with a
shared `Case3BlockDecoder`, there is a Word RAM program computing `IsValidAlg105Output δ` in `O(v³)`
steps (`(v + 1)³`). -/
theorem folio_of_interfaces (δ ξ : ℕ)
    (dec : Case3BlockDecoder)
    (h99 : Alg99Spec dec (alg62Param ξ δ) (sec105WallHeight ξ δ)
      (sec105BranchWidth ξ δ))
    (h104 : Alg104Spec dec (alg62Param ξ δ) ((alg62Param ξ δ).choose 2 + ξ - 1) δ
      (sec105WallHeight ξ δ) (sec105BranchWidth ξ δ)) :
    ∃ P : Cmd,
      ComputesArrRelInTime (folioSize (ξ := ξ)) encFolioIn
        (IsValidAlg105Output δ (max (sec105BranchWidth ξ δ) 2 + ξ)) P
        (fun v => (v + 1) ^ 3) :=
  gm13_algorithm_10_5 ξ δ (sec105WallHeight ξ δ) (sec105BranchWidth ξ δ)
    dec h99 h104

/-- **Folio Problem in `O(v³)` from Subroutine Interfaces** (GM XIII, (10.5), pages 108–109):
For fixed `δ, ξ : ℕ`, given the subroutine specifications (`Alg99Spec`, `Alg104Spec`) and
`Alg105.Alg41RawSpec` (producing raw `encFolioSetRep F` in `outArr` as required by
`IsValidFolioOutput` in `FolioStatement.lean`), `FolioStatement δ ξ` holds. -/
theorem folioStatement_of_interfaces (δ ξ : ℕ)
    (dec : Case3BlockDecoder)
    (h99 : Alg99Spec dec (alg62Param ξ δ) (sec105WallHeight ξ δ)
      (sec105BranchWidth ξ δ))
    (h104 : Alg104Spec dec (alg62Param ξ δ) ((alg62Param ξ δ).choose 2 + ξ - 1) δ
      (sec105WallHeight ξ δ) (sec105BranchWidth ξ δ))
    (h41 : Alg105.Alg41RawSpec (alg62Param ξ δ) ξ δ
      (max (sec105BranchWidth ξ δ) 2 + ξ)) :
    FolioStatement δ ξ := by
  rcases h41 with ⟨prog41, C41, c41, _, _, h41_exec⟩
  refine algorithm_10_5_core ξ δ (sec105WallHeight ξ δ)
    (sec105BranchWidth ξ δ) dec (IsValidFolioOutput δ)
    h99 h104 prog41 C41 c41
    (fun G_i Z_i t par f_tau s hw hZ hbd hb hb1 hr26 hr28 hr52
      hb2_len hb2_get hb3_len hb3_get hb5 hb6 => ?_)
  rcases h41_exec G_i Z_i t par f_tau s hw hZ hbd hb hb1 hr26 hr28 hr52
      hb2_len hb2_get hb3_len hb3_get hb5 hb6 with
    ⟨s', time, F, hex, htime, hout, hF⟩
  exact ⟨s', time, hex, htime, fun x hZ_eq hfolio =>
    ⟨F.castCard hZ_eq, by rw [hout, encFolioSetRep_castCard], hfolio F hF⟩⟩

/-- **Disjoint Paths Problem in `O(v³)` from Subroutine Interfaces** (GM XIII, (10.5) + Section 2,
pages 69, 108–109):
Given the subroutine specifications (`Alg99Spec`, `Alg104Spec`) and `Alg105.Alg41RawSpec` for all
`δ, ξ : ℕ`, `DisjointPathsStatement` holds via `dp_of_folio` (`FolioReduction.lean`). -/
theorem disjointPathsStatement_of_interfaces
    (dec : Case3BlockDecoder)
    (h99 : ∀ ξ δ : ℕ, Alg99Spec dec (alg62Param ξ δ) (sec105WallHeight ξ δ)
      (sec105BranchWidth ξ δ))
    (h104 : ∀ ξ δ : ℕ, Alg104Spec dec (alg62Param ξ δ) ((alg62Param ξ δ).choose 2 + ξ - 1) δ
      (sec105WallHeight ξ δ) (sec105BranchWidth ξ δ))
    (h41 : ∀ ξ δ : ℕ, Alg105.Alg41RawSpec (alg62Param ξ δ) ξ δ
      (max (sec105BranchWidth ξ δ) 2 + ξ)) :
    DisjointPathsStatement :=
  dp_of_folio (fun δ ξ =>
    folioStatement_of_interfaces δ ξ dec (h99 ξ δ) (h104 ξ δ) (h41 ξ δ))

end GraphMinor.Compute
