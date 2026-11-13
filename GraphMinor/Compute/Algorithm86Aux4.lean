module

public import GraphMinor.Compute.Algorithm86Aux3

/-!
# Word RAM Division Builder and Pure Reader for GM XIII Algorithm (8.6)

This file assembles the passes of `Algorithm86Aux1..3.lean` into `alg86DivisionsProg`, which
computes a 4-linked core `(Z, C)` via `alg83Prog` and then computes and writes out both the raw
family $\mathcal{A}'$ (`alg86RawPairList`) and the quotient division $\mathcal{A}$
(`alg86DivPairList`) in linear time $O(v\varepsilon)$ (`alg81Size x`). It also defines the pure
stream readers `decAlg86SubgraphWords`, `decAlg86SubgraphsWords`, and `decAlg86PairListWords` and
proves their round-trip decoding theorems.
-/

@[expose] public section

namespace GraphMinor.Compute

open SimpleGraph

/-! ### Section 1: Pure Stream Readers for Encoded Subgraphs and Subgraph Lists -/

/-- Characterizes adjacency in `graphOfFlatEdges n ([n, edges.length] ++ flatEdges edges)` for any
list of vertex pairs `edges : List (Fin n × Fin n)`. -/
theorem adj_graphOfFlatEdges_iff {n : ℕ} (edges : List (Fin n × Fin n)) (u v : Fin n) :
    (graphOfFlatEdges n ([n, edges.length] ++ flatEdges edges)).Adj u v ↔
      u ≠ v ∧ ((u, v) ∈ edges ∨ (v, u) ∈ edges) := by
  let l := [n, edges.length] ++ flatEdges edges
  have hm : l.getD 1 0 = edges.length := by simp [l]
  have heven : ∀ k (hk : k < edges.length), l.getD (2 + 2 * k) 0 = (edges[k]'hk).1.1 := by
    intro k hk
    have hidx : 2 + 2 * k < l.length := by simp [l, length_flatEdges]; omega
    have h2 : 2 + 2 * k = (2 * k) + 1 + 1 := by omega
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hidx, Option.getD_some]
    simp only [l, h2, List.cons_append, List.nil_append, List.getElem_cons_succ]
    exact getElem_flatEdges_even edges hk
  have hodd : ∀ k (hk : k < edges.length), l.getD (2 + 2 * k + 1) 0 = (edges[k]'hk).2.1 := by
    intro k hk
    have hidx : 2 + 2 * k + 1 < l.length := by simp [l, length_flatEdges]; omega
    have h2 : 2 + 2 * k + 1 = (2 * k + 1) + 1 + 1 := by omega
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hidx, Option.getD_some]
    simp only [l, h2, List.cons_append, List.nil_append, List.getElem_cons_succ]
    exact getElem_flatEdges_odd edges hk
  change (graphOfFlatEdges n l).Adj u v ↔ _
  dsimp [graphOfFlatEdges]
  rw [hm]
  refine and_congr_right fun _ => ?_
  constructor
  · rintro ⟨k, hk, ⟨h1, h2⟩ | ⟨h1, h2⟩⟩
    · rw [heven k hk] at h1
      rw [hodd k hk] at h2
      left
      have heq : edges[k]'hk = (u, v) := Prod.ext (Fin.ext h1) (Fin.ext h2)
      exact heq ▸ List.getElem_mem hk
    · rw [heven k hk] at h1
      rw [hodd k hk] at h2
      right
      have heq : edges[k]'hk = (v, u) := Prod.ext (Fin.ext h1) (Fin.ext h2)
      exact heq ▸ List.getElem_mem hk
  · rintro (hmem | hmem)
    · rcases List.mem_iff_getElem.mp hmem with ⟨k, hk, heq⟩
      refine ⟨k, hk, Or.inl ⟨?_, ?_⟩⟩
      · rw [heven k hk, heq]
      · rw [hodd k hk, heq]
    · rcases List.mem_iff_getElem.mp hmem with ⟨k, hk, heq⟩
      refine ⟨k, hk, Or.inr ⟨?_, ?_⟩⟩
      · rw [heven k hk, heq]
      · rw [hodd k hk, heq]

/-- Pure stream reader that decodes one subgraph `(V, H)` from the front of `words : List ℕ` and
returns the remaining words. -/
def decAlg86SubgraphWords (n : ℕ) (words : List ℕ) :
    (Finset (Fin n) × SimpleGraph (Fin n)) × List ℕ :=
  let m := words.getD (n + 1) 0
  let len := n + 2 + 2 * m
  let V := finsetOfBitList n (words.take n)
  let H := graphOfFlatEdges n ((words.drop n).take (2 + 2 * m))
  ((V, H), words.drop len)

theorem decAlg86SubgraphWords_append {n : ℕ} (V : Finset (Fin n))
    (edges : List (Fin n × Fin n)) (rest : List ℕ) :
    decAlg86SubgraphWords n (encAlg86Subgraph V edges ++ rest) =
      ((V, graphOfFlatEdges n ([n, edges.length] ++ flatEdges edges)), rest) := by
  have hbit_len : (bitSetList V).length = n := length_bitSetList V
  have hflat_len : ([n, edges.length] ++ flatEdges edges).length = 2 + 2 * edges.length := by
    simp [length_flatEdges]; omega
  have henc_len : (encAlg86Subgraph V edges).length = n + 2 + 2 * edges.length :=
    length_encAlg86Subgraph V edges
  have hassoc :
      encAlg86Subgraph V edges ++ rest =
        bitSetList V ++ (([n, edges.length] ++ flatEdges edges) ++ rest) := by
    simp [encAlg86Subgraph, List.append_assoc]
  have hm : (encAlg86Subgraph V edges ++ rest).getD (n + 1) 0 = edges.length := by
    rw [hassoc, List.getD_eq_getElem?_getD,
      List.getElem?_append_right (by rw [hbit_len]; omega)]
    have hsub : n + 1 - (bitSetList V).length = 1 := by rw [hbit_len]; omega
    rw [hsub]
    simp
  have htake_n : (encAlg86Subgraph V edges ++ rest).take n = bitSetList V := by
    rw [hassoc]
    exact List.take_left' hbit_len
  have hdrop_n :
      (encAlg86Subgraph V edges ++ rest).drop n =
        ([n, edges.length] ++ flatEdges edges) ++ rest := by
    rw [hassoc]
    exact List.drop_left' hbit_len
  have htake_edges :
      ((([n, edges.length] ++ flatEdges edges) ++ rest)).take (2 + 2 * edges.length) =
        [n, edges.length] ++ flatEdges edges :=
    List.take_left' hflat_len
  have hdrop_len :
      (encAlg86Subgraph V edges ++ rest).drop (n + 2 + 2 * edges.length) = rest :=
    List.drop_left' henc_len
  unfold decAlg86SubgraphWords
  simp only [hm, htake_n, hdrop_n, htake_edges, hdrop_len, finsetOfBitList_bitSetList]

/-- Pure stream reader that decodes `k` subgraphs from the front of `words : List ℕ`. -/
def decAlg86SubgraphsWords (n : ℕ) :
    ℕ → List ℕ → List (Finset (Fin n) × SimpleGraph (Fin n)) × List ℕ
  | 0, words => ([], words)
  | k + 1, words =>
    let (p, rest₁) := decAlg86SubgraphWords n words
    let (ps, rest₂) := decAlg86SubgraphsWords n k rest₁
    (p :: ps, rest₂)

theorem decAlg86SubgraphsWords_append {n : ℕ}
    (L : List (Finset (Fin n) × List (Fin n × Fin n))) (rest : List ℕ) :
    decAlg86SubgraphsWords n L.length
      (L.flatMap (fun p => encAlg86Subgraph p.1 p.2) ++ rest) =
      (L.map (fun p => (p.1, graphOfFlatEdges n ([n, p.2.length] ++ flatEdges p.2))), rest) := by
  induction L generalizing rest with
  | nil => rfl
  | cons p ps ih =>
    simp only [List.length_cons, List.flatMap_cons, List.append_assoc,
      decAlg86SubgraphsWords, decAlg86SubgraphWords_append, ih, List.map_cons]

/-- Pure stream reader that decodes a length-prefixed list `encAlg86PairList L` of subgraphs from
`words : List ℕ`. -/
def decAlg86PairListWords (n : ℕ) (words : List ℕ) :
    List (Finset (Fin n) × SimpleGraph (Fin n)) × List ℕ :=
  decAlg86SubgraphsWords n (words.getD 0 0) (words.drop 1)

theorem decAlg86PairListWords_append {n : ℕ}
    (L : List (Finset (Fin n) × List (Fin n × Fin n))) (rest : List ℕ) :
    decAlg86PairListWords n (encAlg86PairList L ++ rest) =
      (L.map (fun p => (p.1, graphOfFlatEdges n ([n, p.2.length] ++ flatEdges p.2))), rest) := by
  unfold decAlg86PairListWords encAlg86PairList
  simp only [List.cons_append, List.nil_append, List.getD_cons_zero, List.drop_succ_cons,
    List.drop_zero]
  exact decAlg86SubgraphsWords_append L rest

/-! ### Section 2: Combined Subgraph Pair Lists and Length Bounds -/

/-- Complete list of `(V, edges)` pairs emitted for the raw division $\mathcal{A}'$. -/
noncomputable def alg86RawPairList {n : ℕ} (G : SimpleGraph (Fin n)) (Z omegaSet : Finset (Fin n))
    (edges₀ : List (Fin n × Fin n)) : List (Finset (Fin n) × List (Fin n × Fin n)) :=
  alg86TypeIPairs Z edges₀ ∅ edges₀.length ++
    alg86TypeIIPairs G Z edges₀ n ++
    alg86TypeIIIPairs omegaSet edges₀ n

/-- Complete list of `(V, edges)` pairs emitted for the quotient division $\mathcal{A}$. -/
noncomputable def alg86DivPairList {n : ℕ} (G : SimpleGraph (Fin n)) (Z omegaSet : Finset (Fin n))
    (edges₀ : List (Fin n × Fin n)) : List (Finset (Fin n) × List (Fin n × Fin n)) :=
  let M' := alg86CaseCMarked G Z edges₀ ∅ n
  alg86CaseCPairs G Z edges₀ n ++
    alg86TypeIPairs Z edges₀ M' edges₀.length ++
    alg86TypeIIIPairs omegaSet edges₀ n

lemma length_encAlg86PairList_raw_le {n : ℕ} (G : SimpleGraph (Fin n))
    (Z omegaSet : Finset (Fin n)) (edges₀ : List (Fin n × Fin n)) :
    (encAlg86PairList (alg86RawPairList G Z omegaSet edges₀)).length ≤
      1 + edges₀.length * (n + 4) + n * (n + 2 + 2 * edges₀.length) + n * (n + 2) ∧
    (alg86RawPairList G Z omegaSet edges₀).length ≤ edges₀.length + 2 * n := by
  obtain ⟨hf1, hl1⟩ := length_alg86TypeIPairs_le Z edges₀ ∅ edges₀.length
  have hf2 := length_flatMap_alg86TypeIIPairs_le G Z edges₀ n
  have hl2 := length_alg86TypeIIPairs_le G Z edges₀ n
  obtain ⟨hf3, hl3⟩ := length_alg86TypeIIIPairs_le omegaSet edges₀ n
  dsimp [encAlg86PairList, alg86RawPairList]
  simp only [List.flatMap_append, List.length_append]
  omega

lemma length_encAlg86PairList_div_le {n : ℕ} (G : SimpleGraph (Fin n))
    (Z omegaSet : Finset (Fin n)) (edges₀ : List (Fin n × Fin n)) :
    (encAlg86PairList (alg86DivPairList G Z omegaSet edges₀)).length ≤
      1 + n * (n + 2 + 2 * edges₀.length) + edges₀.length * (n + 4) + n * (n + 2) ∧
    (alg86DivPairList G Z omegaSet edges₀).length ≤ edges₀.length + 2 * n := by
  have hf1 := length_flatMap_alg86CaseCPairs_le G Z edges₀ n
  have hl1 := length_alg86CaseCPairs_le G Z edges₀ n
  obtain ⟨hf2, hl2⟩ := length_alg86TypeIPairs_le Z edges₀ (alg86CaseCMarked G Z edges₀ ∅ n) edges₀.length
  obtain ⟨hf3, hl3⟩ := length_alg86TypeIIIPairs_le omegaSet edges₀ n
  dsimp [encAlg86PairList, alg86DivPairList]
  simp only [List.flatMap_append, List.length_append]
  omega

/-! ### Section 3: Word RAM Program `alg86DivisionsProg` and Execution Proof -/

/-- Phase 1 of `alg86DivisionsProg`:
1. Saves `[x.n, m₀] ++ flatEdges edges₀` from `inArr = 0` into array `50`.
2. Runs `alg83Prog` to compute a 4-linked core `(Z, C)` with `edges_C`.
3. Copies `outArr = bitSetList Z ++ ([x.n, edges_C.length] ++ flatEdges edges_C)` into array `49`
   and restores `inArr = 0` from array `50`.
4. Parses `x.G` into `(3, 4, 5)` (with degrees in `2`) and builds the restricted adjacency list of
   `x.G \ Z` in `(6, 7, 8)`.
5. Allocates `outArr` of capacity `cap = 12 * alg81Size x` and writes
   `[0] ++ (bitSetList Z ++ ([x.n, edges_C.length] ++ flatEdges edges_C))` to `outArr`. -/
def alg86PrepProg : Cmd :=
  .seq (.assign 1 (.read 0 (.const 1)))
    (.seq (.assign 21 (.op .add (.const 2) (.op .mul (.const 2) (.reg 1))))
      (.seq (readSliceProg 0 (.const 0) 50 (.reg 21) 22)
        (.seq alg83Prog
          (.seq (.assign 1 (.read 0 (.const 1)))
            (.seq (.assign 20 (.op .add (.const 2) (.op .mul (.const 2) (.reg 1))))
              (.seq (.assign 21 (.op .add (.reg 14) (.reg 20)))
                (.seq (readSliceProg outArr (.const 0) 49 (.reg 21) 22)
                  (.seq (.assign 1 (.read 50 (.const 1)))
                    (.seq (.assign 20 (.op .add (.const 2) (.op .mul (.const 2) (.reg 1))))
                      (.seq (readSliceProg 50 (.const 0) 0 (.reg 20) 22)
                        (.seq (parseGraphProg 2 3 4 5 0)
                          (.seq (buildComplAndExtNhdProg 3 4 5 14 10 11)
                            (.seq (.assign 19 (.op .mul (.const 2) (.reg 1)))
                              (.seq (restrictGraphProg 3 4 5 10 6 7 8 14 19 2 3 4 5 6 7 8)
                                (.seq (.assign 22 (.op .add (.reg 14) (.const 1)))
                                  (.seq (.assign 23 (.op .add (.reg 1) (.reg 22)))
                                    (.seq (.assign 22 (.op .mul (.const 12) (.op .mul (.reg 22) (.reg 23))))
                                      (.seq (.alloc outArr (.reg 22))
                                        (.seq (.assign 25 (.const 1))
                                          (appendSliceToOutProg 49 21))))))))))))))))))))

theorem alg86PrepProg_exec {w : ℕ} (x : Alg81Input)
    (hw4 : 4 < 2 ^ w) (hsize_w : 16 * (alg81Size x + 2) < 2 ^ w) {s₀ : State}
    (hs₀ : s₀.arrs 0 = encAlg81In x) :
    let edges₀ := edgeListOf x.G
    let cap := 12 * alg81Size x
    ∃ s' t Z C edges_C,
      Exec w alg86PrepProg s₀ s' t ∧
      t ≤ 4200 * alg81Size x ∧
      Alg83Trace x Z C ∧
      x.omega.toFinset ⊆ Z ∧
      (∀ u u' : Fin x.n, C.Adj u u' → u ∈ Z ∧ u' ∈ Z) ∧
      IsFourLinkedCore x.omega Z C ∧
      IsSimpleEdgeList C edges_C ∧
      edges_C.length ≤ edges₀.length + 3 * x.n ∧
      s'.arrs 0 = [x.n, edges₀.length] ++ flatEdges edges₀ ∧
      IsAdjList x.G 3 4 5 (edgeNeighbors edges₀) s' ∧
      (s'.arrs 5).length = 2 * edges₀.length ∧
      IsAdjList (restrictGraph x.G (Finset.univ \ Z)) 6 7 8
        (restrictListFamily (Finset.univ \ Z) (edgeNeighbors edges₀)) s' ∧
      (s'.arrs 8).length < 2 ^ w ∧
      IsBitSet Z 14 s' ∧
      IsBitSet x.omega.toFinset 9 s' ∧
      (∃ (hd : (s'.arrs 2).length = x.n),
        ∀ v : Fin x.n, (s'.arrs 2)[v.1]'(by rw [hd]; exact v.2) = (edgeNeighbors edges₀ v).length) ∧
      s'.regs 1 = edges₀.length ∧
      s'.regs 14 = x.n ∧
      s'.arrs outArr =
        ([0] ++ (bitSetList Z ++ ([x.n, edges_C.length] ++ flatEdges edges_C))) ++
          List.replicate (cap - ([0] ++ (bitSetList Z ++ ([x.n, edges_C.length] ++ flatEdges edges_C))).length) 0 ∧
      s'.regs 25 = ([0] ++ (bitSetList Z ++ ([x.n, edges_C.length] ++ flatEdges edges_C))).length := by
  intro edges₀ cap
  have hm_eq : edges₀.length = x.G.edgeFinset.card :=
    length_edgeListOf_eq_card_edgeFinset x.G
  have hedges₀ : IsSimpleEdgeList x.G edges₀ := isSimpleEdgeList_edgeListOf x.G
  have hk_le_n : x.omega.length ≤ x.n := length_omega_le_n x.nodup_omega
  have hS_def : alg81Size x = (x.n + 1) * (edges₀.length + x.n + 1) := by
    dsimp [alg81Size, societySize]; rw [hm_eq]
  have hS_pos : 1 ≤ alg81Size x := by
    rw [hS_def]; exact Nat.mul_pos (by omega) (by omega)
  have hS_ge : edges₀.length + x.n + 1 ≤ alg81Size x := by
    rw [hS_def]
    have : 1 * (edges₀.length + x.n + 1) ≤ (x.n + 1) * (edges₀.length + x.n + 1) :=
      Nat.mul_le_mul_right _ (by omega)
    omega
  have h0_w : 0 < 2 ^ w := by omega
  have hw : 1 < 2 ^ w := by omega
  have hw2 : 2 < 2 ^ w := by omega
  have hw12 : 12 < 2 ^ w := by omega
  have hn_w : x.n < 2 ^ w := by omega
  have hm_w : edges₀.length < 2 ^ w := by omega
  have h2m_w : 2 * edges₀.length < 2 ^ w := by omega
  have hm2_w : 2 + 2 * edges₀.length < 2 ^ w := by omega
  have hcap_w : cap < 2 ^ w := by dsimp [cap]; omega
  -- 1. Save [x.n, m₀] ++ flatEdges edges₀ to array 50
  have hin₀ : s₀.arrs 0 =
      [] ++ ([x.n, edges₀.length] ++ flatEdges edges₀) ++
        ([x.omega.length] ++ x.omega.map Fin.val) := by
    simpa [encAlg81In, encGraph, edges₀, List.append_assoc] using hs₀
  have h1_idx₀ : 1 < (s₀.arrs 0).length := by simp [hs₀, encAlg81In, encGraph]
  have h1_val₀ : (s₀.arrs 0)[1]'h1_idx₀ = edges₀.length := by
    simp [hs₀, encAlg81In, encGraph, edges₀]
  let s₁ := s₀.setReg 1 edges₀.length
  have hex₁ : Exec w (.assign 1 (.read 0 (.const 1))) s₀ s₁ 3 :=
    .assign (by simp [Expr.eval, checkWord, hw, h1_idx₀, h1_val₀, hm_w])
  let s₂ := s₁.setReg 21 (2 + 2 * edges₀.length)
  have hex₂ : Exec w (.assign 21 (.op .add (.const 2) (.op .mul (.const 2) (.reg 1)))) s₁ s₂ 6 :=
    .assign (by simp [s₁, Expr.eval, BinOp.eval, BinOp.raw, checkWord, hw2, hm_w, h2m_w, hm2_w])
  have hslice₀_w : ∀ v ∈ [x.n, edges₀.length] ++ flatEdges edges₀, v < 2 ^ w := by
    intro v hv
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hv
    rcases hv with (rfl | rfl) | hv_flat
    · exact hn_w
    · exact hm_w
    · exact Nat.lt_trans (mem_flatEdges_lt edges₀ v hv_flat) hn_w
  rcases readSliceProg_exec (w := w) (n := 2 + 2 * edges₀.length) (off := 0) 0 50 (.const 0) 21 22
      (by decide) (by decide)
      [] ([x.n, edges₀.length] ++ flatEdges edges₀) ([x.omega.length] ++ x.omega.map Fin.val)
      rfl (by simp [length_flatEdges]; omega) hslice₀_w hw (by omega) (s := s₂)
      (by simp [Expr.eval, checkWord, h0_w])
      hin₀ (by simp [s₂]) with
    ⟨s₃, t₃, hex₃, ht₃, harr50_₃, harr₃, _⟩
  dsimp [Expr.cost] at ht₃
  have hs₃_0 : s₃.arrs 0 = encAlg81In x := by
    rw [harr₃ 0 (by decide)]; exact hs₀
  -- 2. Run alg83Prog
  rcases alg83Prog_exec x hw4 hsize_w hs₃_0 with
    ⟨s₄, t₄, Z, C, edges_C, hex₄, ht₄, htrace, hom_sub, hadj_Z, hcore4,
      hedges_C, hlen_C, hout₄, hin₄, hZ₄, hom₄, hconst₄⟩
  have harr50_₄ : s₄.arrs 50 = [x.n, edges₀.length] ++ flatEdges edges₀ := by
    rw [hex₄.arr_eq_of_preservesArr (by decide)]
    simpa using harr50_₃
  -- 3. Copy core from outArr to array 49
  have hlen_C' : edges_C.length ≤ edges₀.length + 3 * x.n := hlen_C
  have hmC_w : edges_C.length < 2 ^ w := by linarith [hsize_w, hS_ge, hlen_C']
  have h2mC_w : 2 * edges_C.length < 2 ^ w := by linarith [hsize_w, hS_ge, hlen_C']
  have hlenC2_w : 2 + 2 * edges_C.length < 2 ^ w := by linarith [hsize_w, hS_ge, hlen_C']
  let coreWords := bitSetList Z ++ ([x.n, edges_C.length] ++ flatEdges edges_C)
  let coreLen := x.n + (2 + 2 * edges_C.length)
  have hcoreLen_w : coreLen < 2 ^ w := by dsimp [coreLen]; linarith [hsize_w, hS_ge, hlen_C']
  have h1_idx₄ : 1 < (s₄.arrs 0).length := by simp [hin₄, length_flatEdges]
  have h1_val₄ : (s₄.arrs 0)[1]'h1_idx₄ = edges_C.length := by simp [hin₄]
  let s₅ := s₄.setReg 1 edges_C.length
  have hex₅ : Exec w (.assign 1 (.read 0 (.const 1))) s₄ s₅ 3 :=
    .assign (by simp [Expr.eval, checkWord, hw, h1_idx₄, h1_val₄, hmC_w])
  let s₆ := s₅.setReg 20 (2 + 2 * edges_C.length)
  have hex₆ : Exec w (.assign 20 (.op .add (.const 2) (.op .mul (.const 2) (.reg 1)))) s₅ s₆ 6 :=
    .assign (by simp [s₅, Expr.eval, BinOp.eval, BinOp.raw, checkWord, hw2, hmC_w, h2mC_w, hlenC2_w])
  have hr14_₆ : s₆.regs 14 = x.n := hconst₄.1
  have hr20_₆ : s₆.regs 20 = 2 + 2 * edges_C.length := by simp [s₆]
  let s₇ := s₆.setReg 21 coreLen
  have hex₇ : Exec w (.assign 21 (.op .add (.reg 14) (.reg 20))) s₆ s₇ 4 :=
    .assign (by simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord,
      hr14_₆, hr20_₆, hn_w, hlenC2_w, coreLen, hcoreLen_w])
  have hcoreWords_w : ∀ v ∈ coreWords, v < 2 ^ w :=
    mem_encAlg86Subgraph_w Z edges_C hw hn_w hmC_w
  have hout₇ : s₇.arrs outArr = [] ++ coreWords ++ [] := by
    simpa [s₇, s₆, s₅, coreWords] using hout₄
  rcases readSliceProg_exec (w := w) (n := coreLen) (off := 0) outArr 49 (.const 0) 21 22
      (by decide) (by decide)
      [] coreWords []
      rfl (by simp [coreWords, coreLen, length_bitSetList, length_flatEdges]; omega)
      hcoreWords_w hw (by omega)
      (by simp [Expr.eval, checkWord, h0_w])
      hout₇ (by simp [s₇]) with
    ⟨s₈, t₈, hex₈, ht₈, harr49_₈, harr₈, hreg₈⟩
  dsimp [Expr.cost] at ht₈
  -- 4. Restore inArr = 0 from array 50
  have harr50_₈ : s₈.arrs 50 = [x.n, edges₀.length] ++ flatEdges edges₀ := by
    rw [harr₈ 50 (by decide)]; exact harr50_₄
  have h1_idx₈ : 1 < (s₈.arrs 50).length := by simp [harr50_₈, length_flatEdges]
  have h1_val₈ : (s₈.arrs 50)[1]'h1_idx₈ = edges₀.length := by simp [harr50_₈]
  let s₉ := s₈.setReg 1 edges₀.length
  have hex₉ : Exec w (.assign 1 (.read 50 (.const 1))) s₈ s₉ 3 :=
    .assign (by simp [Expr.eval, checkWord, hw, h1_idx₈, h1_val₈, hm_w])
  let s₁₀ := s₉.setReg 20 (2 + 2 * edges₀.length)
  have hex₁₀ : Exec w (.assign 20 (.op .add (.const 2) (.op .mul (.const 2) (.reg 1)))) s₉ s₁₀ 6 :=
    .assign (by simp [s₉, Expr.eval, BinOp.eval, BinOp.raw, checkWord, hw2, hm_w, h2m_w, hm2_w])
  have harr50_₁₀ : s₁₀.arrs 50 = [] ++ ([x.n, edges₀.length] ++ flatEdges edges₀) ++ [] := by
    simpa [s₁₀, s₉] using harr50_₈
  rcases readSliceProg_exec (w := w) (n := 2 + 2 * edges₀.length) (off := 0) 50 0 (.const 0) 20 22
      (by decide) (by decide)
      [] ([x.n, edges₀.length] ++ flatEdges edges₀) []
      rfl (by simp [length_flatEdges]; omega) hslice₀_w hw (by omega)
      (by simp [Expr.eval, checkWord, h0_w])
      harr50_₁₀ (by simp [s₁₀]) with
    ⟨s₁₁, t₁₁, hex₁₁, ht₁₁, hin₁₁, harr₁₁, hreg₁₁⟩
  dsimp [Expr.cost] at ht₁₁
  -- 5. Parse x.G and restrict to Finset.univ \ Z
  have hin₁₁_extra : s₁₁.arrs 0 = [x.n, edges₀.length] ++ flatEdges edges₀ ++ [] := by
    simpa using hin₁₁
  rcases Triple.parseGraphProg_spec (w := w) x.G edges₀ [] 2 3 4 5 0 hedges₀
      (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      hw2 hn_w hm2_w s₁₁ hin₁₁_extra with
    ⟨s₁₂, t₁₂, hex₁₂, ht₁₂, hin₁₂, _, hr1_₁₂, hadj_G₁₂, hent_G₁₂, ⟨hdeg_len₁₂, hdeg_val₁₂⟩⟩
  dsimp only at ht₁₂
  rw [List.append_nil] at hin₁₂
  have hZ₁₂ : IsBitSet Z 14 s₁₂ := by
    refine hZ₄.of_arr_eq ?_
    rw [hex₁₂.arr_eq_of_preservesArr (by decide), harr₁₁ 14 (by decide)]
    change s₈.arrs 14 = s₄.arrs 14
    rw [harr₈ 14 (by decide)]
    rfl
  have hr14_₁₂ : s₁₂.regs 14 = x.n := by
    rw [hex₁₂.reg_eq_of_preservesReg (by decide), hreg₁₁ 14 (by decide)]
    change s₈.regs 14 = x.n
    rw [hreg₈ 14 (by decide)]
    exact hr14_₆
  have hent_G₁₂_w : (s₁₂.arrs 5).length < 2 ^ w := by rw [hent_G₁₂]; exact h2m_w
  have htot_G : totalAdjEntries (edgeNeighbors edges₀) = 2 * edges₀.length :=
    totalAdjEntries_edgeNeighbors edges₀ hedges₀.1
  rcases buildComplAndExtNhdProg_exec x.G (edgeNeighbors edges₀) Z 3 4 5 14 10 11
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide)
      hw hn_w hadj_G₁₂ hent_G₁₂_w hZ₁₂ hr14_₁₂ with
    ⟨s₁₃, t₁₃, hex₁₃, ht₁₃, hY₁₃, _, harr₁₃, hreg₁₃⟩
  rw [htot_G] at ht₁₃
  have hr1_₁₃ : s₁₃.regs 1 = edges₀.length := by
    rw [hreg₁₃ 1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]
    exact hr1_₁₂
  let s₁₄ := s₁₃.setReg 19 (2 * edges₀.length)
  have hex₁₄ : Exec w (.assign 19 (.op .mul (.const 2) (.reg 1))) s₁₃ s₁₄ 4 :=
    .assign (by simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hr1_₁₃, hw2, hm_w, h2m_w])
  have hadj_G₁₄ : IsAdjList x.G 3 4 5 (edgeNeighbors edges₀) s₁₄ :=
    hadj_G₁₂.of_arrs_eq (harr₁₃ 3 (by decide) (by decide))
      (harr₁₃ 4 (by decide) (by decide)) (harr₁₃ 5 (by decide) (by decide))
  have hent_G₁₄ : (s₁₄.arrs 5).length = 2 * edges₀.length := by
    change (s₁₃.arrs 5).length = _
    rw [harr₁₃ 5 (by decide) (by decide), hent_G₁₂]
  have hr14_₁₄ : s₁₄.regs 14 = x.n := by
    change s₁₃.regs 14 = x.n
    rw [hreg₁₃ 14 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]
    exact hr14_₁₂
  have hcards_le : (edgesInSet x.G (Finset.univ \ Z)).card ≤ edges₀.length := by
    rw [hm_eq]
    exact card_edgesInSet_le_card_edgeFinset x.G _
  rcases restrictGraphProg_exec x.G (edgeNeighbors edges₀) (Finset.univ \ Z)
      (2 * edges₀.length) 3 4 5 10 6 7 8 14 19 2 3 4 5 6 7 8
      (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide)
      hw hn_w h2m_w (by omega) hadj_G₁₄ (by rw [hent_G₁₄]; exact h2m_w)
      (hY₁₃.of_arr_eq rfl) hr14_₁₄ (by simp [s₁₄]) with
    ⟨s₁₅, t₁₅, hex₁₅, ht₁₅, hadj_Y₁₅, hent_Y₁₅, _, harr₁₅, hreg₁₅⟩
  rw [htot_G] at ht₁₅
  -- 6. Allocate outArr of size cap = 12 * alg81Size x and write [0] ++ coreWords
  have hr14_₁₅ : s₁₅.regs 14 = x.n := by
    rw [hreg₁₅ 14 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]
    exact hr14_₁₄
  have hr1_₁₅ : s₁₅.regs 1 = edges₀.length := by
    rw [hreg₁₅ 1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]
    exact hr1_₁₃
  have hr21_₁₅ : s₁₅.regs 21 = coreLen := by
    rw [hreg₁₅ 21 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]
    change s₁₃.regs 21 = coreLen
    rw [hreg₁₃ 21 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
        hex₁₂.reg_eq_of_preservesReg (by decide), hreg₁₁ 21 (by decide)]
    change s₈.regs 21 = coreLen
    rw [hreg₈ 21 (by decide)]
    simp [s₇]
  have hn1_w : x.n + 1 < 2 ^ w := by omega
  have hmn1_w : edges₀.length + (x.n + 1) < 2 ^ w := by omega
  have hS_w : (x.n + 1) * (edges₀.length + (x.n + 1)) < 2 ^ w := by
    have : (x.n + 1) * (edges₀.length + (x.n + 1)) = alg81Size x := by
      rw [hS_def]; ring
    omega
  have hcap_eq : 12 * ((x.n + 1) * (edges₀.length + (x.n + 1))) = cap := by
    dsimp [cap]; rw [hS_def]; ring
  let s₁₆ := s₁₅.setReg 22 (x.n + 1)
  have hex₁₆ : Exec w (.assign 22 (.op .add (.reg 14) (.const 1))) s₁₅ s₁₆ 4 :=
    .assign (by simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hr14_₁₅, hn_w, hw, hn1_w])
  let s₁₇ := s₁₆.setReg 23 (edges₀.length + (x.n + 1))
  have hex₁₇ : Exec w (.assign 23 (.op .add (.reg 1) (.reg 22))) s₁₆ s₁₇ 4 :=
    .assign (by simp [s₁₆, State.setReg, Expr.eval, BinOp.eval, BinOp.raw, checkWord,
      hr1_₁₅, hm_w, hn1_w, hmn1_w])
  let s₁₈ := s₁₇.setReg 22 cap
  have hex₁₈ : Exec w (.assign 22 (.op .mul (.const 12) (.op .mul (.reg 22) (.reg 23)))) s₁₇ s₁₈ 6 :=
    .assign (by
      simp [s₁₇, s₁₆, State.setReg, Expr.eval, BinOp.eval, BinOp.raw, checkWord,
        hw12, hn1_w, hmn1_w, hS_w, hcap_eq, hcap_w])
  let s₁₉ := s₁₈.setArr outArr (List.replicate cap 0)
  have hex₁₉ : Exec w (.alloc outArr (.reg 22)) s₁₈ s₁₉ (1 + cap) :=
    .alloc (by simp [s₁₈, Expr.eval, checkWord, hcap_w])
  let s₂₀ := s₁₉.setReg 25 1
  have hex₂₀ : Exec w (.assign 25 (.const 1)) s₁₉ s₂₀ 2 :=
    .assign (by simp [Expr.eval, checkWord, hw])
  have harr49_₂₀ : s₂₀.arrs 49 = coreWords ++ [] := by
    change s₁₅.arrs 49 = _
    rw [harr₁₅ 49 (by decide) (by decide) (by decide)]
    change s₁₃.arrs 49 = _
    rw [harr₁₃ 49 (by decide) (by decide),
        hex₁₂.arr_eq_of_preservesArr (by decide),
        harr₁₁ 49 (by decide)]
    change s₈.arrs 49 = _
    simpa using harr49_₈
  have hcap_ge1 : 1 ≤ cap := by dsimp [cap]; omega
  have hout₂₀ : s₂₀.arrs outArr = [0] ++ List.replicate (cap - [0].length) 0 := by
    change List.replicate cap 0 = [0] ++ List.replicate (cap - 1) 0
    have hrep : cap = (cap - 1) + 1 := by omega
    conv_lhs => rw [hrep, List.replicate_succ]
    rfl
  have hcore_cap : [0].length + coreLen ≤ cap := by
    change 1 + (x.n + (2 + 2 * edges_C.length)) ≤ 12 * alg81Size x
    linarith [hlen_C', hS_ge]
  rcases appendSliceToOutProg_exec 49 21 (by decide) (by decide) (by decide) (by decide)
      [0] coreWords []
      (by simp [coreWords, coreLen, length_bitSetList, length_flatEdges]; omega)
      hcoreWords_w hcore_cap hw hcap_w (s := s₂₀)
      harr49_₂₀ hout₂₀
      (by simp [s₂₀, s₁₉, s₁₈, s₁₇, s₁₆, State.setReg, hr21_₁₅])
      (by simp [s₂₀]) with
    ⟨s₂₁, t₂₁, hex₂₁, ht₂₁, hout₂₁, hr25_₂₁, harr₂₁, hreg₂₁⟩
  -- Preserve state facts to s₂₁
  have harr_21_12 : ∀ a : Arr, a ≠ outArr → a ≠ 6 → a ≠ 7 → a ≠ 8 → a ≠ 10 → a ≠ 11 →
      s₂₁.arrs a = s₁₂.arrs a := by
    intro a hout h6 h7 h8 h10 h11
    rw [harr₂₁ a hout]
    have h20_15 : s₂₀.arrs a = s₁₅.arrs a := by
      simp [s₂₀, s₁₉, s₁₈, s₁₇, s₁₆, State.setArr_arrs_ne _ _ hout]
    rw [h20_15, harr₁₅ a h6 h7 h8]
    change s₁₃.arrs a = s₁₂.arrs a
    rw [harr₁₃ a h10 h11]
  have hin₂₁ : s₂₁.arrs 0 = [x.n, edges₀.length] ++ flatEdges edges₀ := by
    rw [harr_21_12 0 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]
    exact hin₁₂
  have hadj_G₂₁ : IsAdjList x.G 3 4 5 (edgeNeighbors edges₀) s₂₁ :=
    hadj_G₁₂.of_arrs_eq
      (harr_21_12 3 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))
      (harr_21_12 4 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))
      (harr_21_12 5 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))
  have hent_G₂₁ : (s₂₁.arrs 5).length = 2 * edges₀.length := by
    rw [harr_21_12 5 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]
    exact hent_G₁₂
  have hadj_Y₂₁ : IsAdjList (restrictGraph x.G (Finset.univ \ Z)) 6 7 8
      (restrictListFamily (Finset.univ \ Z) (edgeNeighbors edges₀)) s₂₁ :=
    hadj_Y₁₅.of_arrs_eq
      (by rw [harr₂₁ 6 (by decide)]; rfl)
      (by rw [harr₂₁ 7 (by decide)]; rfl)
      (by rw [harr₂₁ 8 (by decide)]; rfl)
  have hent_Y₂₁ : (s₂₁.arrs 8).length < 2 ^ w := by
    rw [harr₂₁ 8 (by decide)]
    change (s₁₅.arrs 8).length < 2 ^ w
    rw [hent_Y₁₅]; exact h2m_w
  have hZ₂₁ : IsBitSet Z 14 s₂₁ :=
    hZ₁₂.of_arr_eq (harr_21_12 14 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))
  have hom₂₁ : IsBitSet x.omega.toFinset 9 s₂₁ := by
    refine hom₄.of_arr_eq ?_
    rw [harr_21_12 9 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
        hex₁₂.arr_eq_of_preservesArr (by decide),
        harr₁₁ 9 (by decide)]
    change s₈.arrs 9 = s₄.arrs 9
    rw [harr₈ 9 (by decide)]
    rfl
  have harr2_₂₁ : s₂₁.arrs 2 = s₁₂.arrs 2 :=
    harr_21_12 2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  have hdeg_len₂₁ : (s₂₁.arrs 2).length = x.n := by rw [harr2_₂₁, hdeg_len₁₂]
  have hdeg_val₂₁ :
      ∀ v : Fin x.n, (s₂₁.arrs 2)[v.1]'(by rw [hdeg_len₂₁]; exact v.2) = (edgeNeighbors edges₀ v).length := by
    intro v; simp only [harr2_₂₁]; exact hdeg_val₁₂ v
  have hr1_₂₁ : s₂₁.regs 1 = edges₀.length := by
    rw [hreg₂₁ 1 (by decide) (by decide) (by decide)]
    exact hr1_₁₅
  have hr14_₂₁ : s₂₁.regs 14 = x.n := by
    rw [hreg₂₁ 14 (by decide) (by decide) (by decide)]
    exact hr14_₁₅
  have hcore_len_eq : [0].length + coreLen = ([0] ++ coreWords).length := by
    simp [coreWords, coreLen, length_bitSetList, length_flatEdges]; omega
  rw [hcore_len_eq] at hout₂₁ hr25_₂₁
  have htime :
      3 + (6 + (t₃ + (t₄ + (3 + (6 + (4 + (t₈ + (3 + (6 + (t₁₁ + (t₁₂ + (t₁₃ + (4 + (t₁₅ +
        (4 + (4 + (6 + ((1 + cap) + (2 + t₂₁))))))))))))))))))) ≤ 4200 * alg81Size x := by
    dsimp [coreLen, cap] at ht₈ ht₂₁ ⊢
    linarith [ht₃, ht₄, ht₈, ht₁₁, ht₁₂, ht₁₃, ht₁₅, ht₂₁, hlen_C', hS_ge, hS_pos]
  refine ⟨s₂₁, _, Z, C, edges_C,
    .seq hex₁ (.seq hex₂ (.seq hex₃ (.seq hex₄ (.seq hex₅ (.seq hex₆ (.seq hex₇
      (.seq hex₈ (.seq hex₉ (.seq hex₁₀ (.seq hex₁₁ (.seq hex₁₂ (.seq hex₁₃
        (.seq hex₁₄ (.seq hex₁₅ (.seq hex₁₆ (.seq hex₁₇ (.seq hex₁₈
          (.seq hex₁₉ (.seq hex₂₀ hex₂₁))))))))))))))))))),
    htime, htrace, hom_sub, hadj_Z, hcore4, hedges_C, hlen_C,
    hin₂₁, hadj_G₂₁, hent_G₂₁, hadj_Y₂₁, hent_Y₂₁, hZ₂₁, hom₂₁,
    ⟨hdeg_len₂₁, hdeg_val₂₁⟩, hr1_₂₁, hr14_₂₁, hout₂₁, hr25_₂₁⟩

/-- Phase 2 of `alg86DivisionsProg`: emits `encAlg86PairList rawPairs` followed by
`encAlg86PairList divPairs` into `outArr`. -/
def alg86EmitBothProg : Cmd :=
  .seq (.assign 19 (.reg 25))
    (.seq (.assign 25 (.op .add (.reg 25) (.const 1)))
      (.seq (.assign 26 (.const 0))
        (.seq (.alloc 51 (.reg 1))
          (.seq alg86TypeIPassProg
            (.seq precomputeXTuplesProg
              (.seq alg86TypeIIPassProg
                (.seq alg86TypeIIIPassProg
                  (.seq (.write outArr (.reg 19) (.reg 26))
                    (.seq (.assign 19 (.reg 25))
                      (.seq (.assign 25 (.op .add (.reg 25) (.const 1)))
                        (.seq (.assign 26 (.const 0))
                          (.seq alg86CaseCPassProg
                            (.seq alg86TypeIPassProg
                              (.seq alg86TypeIIIPassProg
                                (.write outArr (.reg 19) (.reg 26))))))))))))))))

/-- Complete Word RAM program for the no-cross branch of GM XIII Algorithm (8.6):
runs `alg86PrepProg` followed by `alg86EmitBothProg`. -/
def alg86DivisionsProg : Cmd :=
  .seq alg86PrepProg alg86EmitBothProg

private lemma length_append_zero_append_eq (A B : List ℕ) (k : ℕ) :
    (A ++ [0] ++ B).length = (A ++ (k :: B)).length := by
  simp

private lemma set_append_zero_append (A B : List ℕ) (k cap : ℕ) :
    (A ++ [0] ++ B ++ List.replicate (cap - (A ++ [0] ++ B).length) 0).set A.length k =
      (A ++ (k :: B)) ++ List.replicate (cap - (A ++ (k :: B)).length) 0 := by
  rw [set_zero_between, length_append_zero_append_eq A B k]
  simp [List.append_assoc]

private lemma alg86Divisions_time_le (n m S t₀ t₅ t₆ t₇ t₈ t₁₃ t₁₄ t₁₅ : ℕ)
    (hS : S = n * m + n * n + 2 * n + m + 1)
    (ht₀ : t₀ ≤ 4200 * S)
    (ht₅ : t₅ ≤ m * (18 * n + 158) + 5)
    (ht₆ : t₆ ≤ n * (77 * n + 86 * m + 82) + 9)
    (ht₇ : t₇ ≤ n * (107 * n + 184 * m + 149) + 5)
    (ht₈ : t₈ ≤ n * (18 * n + 91) + 5)
    (ht₁₃ : t₁₃ ≤ n * (163 * n + 217 * m + 181) + 5)
    (ht₁₄ : t₁₄ ≤ m * (18 * n + 158) + 5)
    (ht₁₅ : t₁₅ ≤ n * (18 * n + 91) + 5) :
    t₀ + (2 + (4 + (2 + ((1 + m) + (t₅ + (t₆ + (t₇ + (t₈ + (3 +
      (2 + (4 + (2 + (t₁₃ + (t₁₄ + (t₁₅ + 3))))))))))))))) ≤ 5000 * S := by
  have h5 : m * (18 * n + 158) = 18 * (n * m) + 158 * m := by ring
  have h6 : n * (77 * n + 86 * m + 82) = 77 * (n * n) + 86 * (n * m) + 82 * n := by ring
  have h7 : n * (107 * n + 184 * m + 149) = 107 * (n * n) + 184 * (n * m) + 149 * n := by ring
  have h8 : n * (18 * n + 91) = 18 * (n * n) + 91 * n := by ring
  have h13 : n * (163 * n + 217 * m + 181) = 163 * (n * n) + 217 * (n * m) + 181 * n := by ring
  rw [h5] at ht₅ ht₁₄
  rw [h6] at ht₆
  rw [h7] at ht₇
  rw [h8] at ht₈ ht₁₅
  rw [h13] at ht₁₃
  rw [hS] at ht₀ ⊢
  omega

set_option maxHeartbeats 800000 in
theorem alg86DivisionsProg_exec {w : ℕ} (x : Alg81Input)
    (hw4 : 4 < 2 ^ w) (hsize_w : 16 * (alg81Size x + 2) < 2 ^ w) {s₀ : State}
    (hs₀ : s₀.arrs 0 = encAlg81In x) :
    let edges₀ := edgeListOf x.G
    let cap := 12 * alg81Size x
    ∃ s' t Z C edges_C,
      Exec w alg86DivisionsProg s₀ s' t ∧
      t ≤ 5000 * alg81Size x ∧
      Alg83Trace x Z C ∧
      x.omega.toFinset ⊆ Z ∧
      (∀ u u' : Fin x.n, C.Adj u u' → u ∈ Z ∧ u' ∈ Z) ∧
      IsFourLinkedCore x.omega Z C ∧
      IsSimpleEdgeList C edges_C ∧
      edges_C.length ≤ edges₀.length + 3 * x.n ∧
      let pref_core := [0] ++ (bitSetList Z ++ ([x.n, edges_C.length] ++ flatEdges edges_C))
      let rawPairs := alg86RawPairList x.G Z x.omega.toFinset edges₀
      let divPairs := alg86DivPairList x.G Z x.omega.toFinset edges₀
      let fullPref := pref_core ++ encAlg86PairList rawPairs ++ encAlg86PairList divPairs
      s'.arrs outArr = fullPref ++ List.replicate (cap - fullPref.length) 0 := by
  intro edges₀ cap
  have hm_eq : edges₀.length = x.G.edgeFinset.card :=
    length_edgeListOf_eq_card_edgeFinset x.G
  have hedges₀ : IsSimpleEdgeList x.G edges₀ := isSimpleEdgeList_edgeListOf x.G
  have hS_def : alg81Size x = (x.n + 1) * (edges₀.length + x.n + 1) := by
    dsimp [alg81Size, societySize]; rw [hm_eq]
  have hS_pos : 1 ≤ alg81Size x := by
    rw [hS_def]; exact Nat.mul_pos (by omega) (by omega)
  have hS_ge : edges₀.length + x.n + 1 ≤ alg81Size x := by
    rw [hS_def]
    have : 1 * (edges₀.length + x.n + 1) ≤ (x.n + 1) * (edges₀.length + x.n + 1) :=
      Nat.mul_le_mul_right _ (by omega)
    omega
  have h0_w : 0 < 2 ^ w := by omega
  have hw : 1 < 2 ^ w := by omega
  have hw2 : 2 < 2 ^ w := by omega
  have hw3 : 3 < 2 ^ w := by omega
  have hn_w : x.n < 2 ^ w := by omega
  have hm_w : edges₀.length < 2 ^ w := by omega
  have h2m_w : 2 * edges₀.length < 2 ^ w := by omega
  have hm3_w : 3 + 2 * edges₀.length < 2 ^ w := by omega
  have hm8_w : 8 + 2 * edges₀.length < 2 ^ w := by omega
  have hcap_w : cap < 2 ^ w := by dsimp [cap]; omega
  -- Phase 1: alg86PrepProg
  rcases alg86PrepProg_exec x hw4 hsize_w hs₀ with
    ⟨s₀', t₀, Z, C, edges_C, hex₀, ht₀, htrace, hom_sub, hadj_Z, hcore4,
      hedges_C, hlen_C, hin₀, hadj_G₀, hent_G₀, hadj_Y₀, hent_Y₀, hZ₀, hom₀,
      ⟨hdeg_len₀, hdeg_val₀⟩, hr1_₀, hr14_₀, hout₀, hr25_₀⟩
  have hlen_C' : edges_C.length ≤ edges₀.length + 3 * x.n := hlen_C
  obtain ⟨pref_core, hpref_core_def⟩ :
      ∃ l, l = [0] ++ (bitSetList Z ++ ([x.n, edges_C.length] ++ flatEdges edges_C)) := ⟨_, rfl⟩
  change s₀'.arrs outArr =
      ([0] ++ (bitSetList Z ++ ([x.n, edges_C.length] ++ flatEdges edges_C))) ++
        List.replicate (cap - ([0] ++ (bitSetList Z ++ ([x.n, edges_C.length] ++ flatEdges edges_C))).length) 0
    at hout₀
  change s₀'.regs 25 =
      ([0] ++ (bitSetList Z ++ ([x.n, edges_C.length] ++ flatEdges edges_C))).length
    at hr25_₀
  rw [← hpref_core_def] at hout₀ hr25_₀
  have hpref_core_len : pref_core.length = 1 + x.n + 2 + 2 * edges_C.length := by
    rw [hpref_core_def]
    simp [length_bitSetList, length_flatEdges]; omega
  have htot_G : totalAdjEntries (edgeNeighbors edges₀) ≤ 2 * edges₀.length := by
    rw [totalAdjEntries_edgeNeighbors edges₀ hedges₀.1]
  have htot_Y :
      totalAdjEntries (restrictListFamily (Finset.univ \ Z) (edgeNeighbors edges₀)) ≤
        2 * edges₀.length := by
    refine le_trans (Finset.sum_le_sum fun u _ =>
      restrictListUpTo_length_le (Finset.univ \ Z) u (edgeNeighbors edges₀ u) (edgeNeighbors edges₀ u).length) ?_
    exact htot_G
  have hdeg_w : ∀ v : Fin x.n, (edgeNeighbors edges₀ v).length < 2 ^ w := by
    intro v
    have hle := (isAdjListFamily_edgeNeighbors hedges₀ v).2.2.1
    omega
  -- Names for rawPairs and divPairs
  let L_raw1 := alg86TypeIPairs Z edges₀ ∅ edges₀.length
  let L_raw2 := alg86TypeIIPairs x.G Z edges₀ x.n
  let L_raw3 := alg86TypeIIIPairs x.omega.toFinset edges₀ x.n
  let rawPairs := alg86RawPairList x.G Z x.omega.toFinset edges₀
  let M' := alg86CaseCMarked x.G Z edges₀ ∅ x.n
  let L_div1 := alg86CaseCPairs x.G Z edges₀ x.n
  let L_div2 := alg86TypeIPairs Z edges₀ M' edges₀.length
  let L_div3 := alg86TypeIIIPairs x.omega.toFinset edges₀ x.n
  let divPairs := alg86DivPairList x.G Z x.omega.toFinset edges₀
  have hS_expand :
      alg81Size x =
        x.n * edges₀.length + x.n * x.n + 2 * x.n + edges₀.length + 1 := by
    rw [hS_def]; ring
  have htotal_cap :
      pref_core.length +
        (1 + edges₀.length * (x.n + 4) + x.n * (x.n + 2 + 2 * edges₀.length) + x.n * (x.n + 2)) +
        (1 + x.n * (x.n + 2 + 2 * edges₀.length) + edges₀.length * (x.n + 4) + x.n * (x.n + 2)) ≤ cap := by
    dsimp [cap]
    rw [hpref_core_len, hS_expand]
    have h1 : edges₀.length * (x.n + 4) = x.n * edges₀.length + 4 * edges₀.length := by ring
    have h2 : x.n * (x.n + 2 + 2 * edges₀.length) = x.n * x.n + 2 * x.n + 2 * (x.n * edges₀.length) := by ring
    have h3 : x.n * (x.n + 2) = x.n * x.n + 2 * x.n := by ring
    rw [h1, h2, h3]
    omega
  -- Step 1: r_19 := r_25, r_25 := r_25 + 1, r_26 := 0, alloc 51 r_1
  have hr25_0_eq : s₀'.regs 25 = pref_core.length := hr25_₀
  have hr1_0_eq : s₀'.regs 1 = edges₀.length := hr1_₀
  have hr25_0_w : pref_core.length < 2 ^ w := by omega
  have hr25_1_w : pref_core.length + 1 < 2 ^ w := by omega
  let s₁ := s₀'.setReg 19 pref_core.length
  have hex₁ : Exec w (.assign 19 (.reg 25)) s₀' s₁ 2 :=
    .assign (by simp [Expr.eval, checkWord, hr25_0_eq, hr25_0_w])
  let s₂ := s₁.setReg 25 (pref_core.length + 1)
  have hex₂ : Exec w (.assign 25 (.op .add (.reg 25) (.const 1))) s₁ s₂ 4 :=
    .assign (by simp [s₁, State.setReg, Expr.eval, BinOp.eval, BinOp.raw, checkWord,
      hr25_0_eq, hr25_0_w, hw, hr25_1_w])
  let s₃ := s₂.setReg 26 0
  have hex₃ : Exec w (.assign 26 (.const 0)) s₂ s₃ 2 :=
    .assign (by simp [Expr.eval, checkWord, h0_w])
  let s₄ := s₃.setArr 51 (List.replicate edges₀.length 0)
  have hex₄ : Exec w (.alloc 51 (.reg 1)) s₃ s₄ (1 + edges₀.length) :=
    .alloc (by simp [s₃, s₂, s₁, State.setReg, Expr.eval, checkWord, hr1_0_eq, hm_w])
  have hM_empty₄ : IsBitSet (∅ : Finset (Fin edges₀.length)) 51 s₄ := by
    refine ⟨by simp [s₄], ⟨fun idx => by simp [s₄], fun idx => by simp [s₄]⟩⟩
  let pref_r0 := pref_core ++ [0]
  have hout₄ : s₄.arrs outArr = pref_r0 ++ List.replicate (cap - pref_r0.length) 0 := by
    change s₀'.arrs outArr = _
    rw [hout₀]
    dsimp [pref_r0]
    have hrep : cap - pref_core.length = 1 + (cap - (pref_core ++ [0]).length) := by
      simp only [List.length_append, List.length_singleton]; omega
    rw [hrep, List.replicate_add, List.replicate_one, List.append_assoc]
  -- Step 2: alg86TypeIPassProg (raw)
  have hcap_r1 : pref_r0.length + edges₀.length * (x.n + 4) ≤ cap := by
    dsimp [pref_r0]; rw [List.length_append, List.length_singleton]; omega
  rcases alg86TypeIPassProg_exec Z edges₀ ∅ pref_r0 0
      hcap_r1 hw4 hn_w hm3_w hcap_w (by omega) (s := s₄)
      hin₀ (hZ₀.of_arr_eq rfl) hM_empty₄ hout₄
      hr1_₀ hr14_₀
      (by simp [s₄, s₃, s₂, pref_r0])
      (by simp [s₄, s₃]) with
    ⟨s₅, t₅, hex₅, ht₅, hout₅, hr25_₅, hr26_₅, harr₅, hreg₅⟩
  -- Step 3: precomputeXTuplesProg
  have harr5_₀ : ∀ a : Arr, a ≠ outArr → a ≠ 17 → a ≠ 18 → a ≠ 51 → s₅.arrs a = s₀'.arrs a := by
    intro a hout h17 h18 h51
    rw [harr₅ a hout h17 h18]
    simp [s₄, s₃, s₂, s₁, State.setArr, State.setReg, h51]
  have hadj_G₅ : IsAdjList x.G 3 4 5 (edgeNeighbors edges₀) s₅ :=
    hadj_G₀.of_arrs_eq
      (harr5_₀ 3 (by decide) (by decide) (by decide) (by decide))
      (harr5_₀ 4 (by decide) (by decide) (by decide) (by decide))
      (harr5_₀ 5 (by decide) (by decide) (by decide) (by decide))
  have hent_G₅ : (s₅.arrs 5).length < 2 ^ w := by
    rw [harr5_₀ 5 (by decide) (by decide) (by decide) (by decide), hent_G₀]
    exact h2m_w
  have hadj_Y₅ : IsAdjList (restrictGraph x.G (Finset.univ \ Z)) 6 7 8
      (restrictListFamily (Finset.univ \ Z) (edgeNeighbors edges₀)) s₅ :=
    hadj_Y₀.of_arrs_eq
      (harr5_₀ 6 (by decide) (by decide) (by decide) (by decide))
      (harr5_₀ 7 (by decide) (by decide) (by decide) (by decide))
      (harr5_₀ 8 (by decide) (by decide) (by decide) (by decide))
  have hent_Y₅ : (s₅.arrs 8).length < 2 ^ w := by
    rw [harr5_₀ 8 (by decide) (by decide) (by decide) (by decide)]; exact hent_Y₀
  have hZ₅ : IsBitSet Z 14 s₅ :=
    hZ₀.of_arr_eq (harr5_₀ 14 (by decide) (by decide) (by decide) (by decide))
  have hr14_₅ : s₅.regs 14 = x.n := by
    rw [hex₅.reg_eq_of_preservesReg (by decide)]; exact hr14_₀
  rcases precomputeXTuplesProg_exec x.G (edgeNeighbors edges₀)
      (restrictListFamily (Finset.univ \ Z) (edgeNeighbors edges₀)) Z
      htot_G htot_Y hw2 hn_w hadj_G₅ hent_G₅ hadj_Y₅ hent_Y₅ hZ₅ hr14_₅ with
    ⟨s₆, t₆, hex₆, ht₆, htup₆, harr₆, hreg₆⟩
  -- Step 4: alg86TypeIIPassProg (raw)
  let pref_r1 := pref_r0 ++ L_raw1.flatMap (fun p => encAlg86Subgraph p.1 p.2)
  have hcap_r2 : pref_r1.length + x.n * (x.n + 2 + 2 * edges₀.length) ≤ cap := by
    obtain ⟨hraw1_flat, _⟩ := length_alg86TypeIPairs_le Z edges₀ ∅ edges₀.length
    dsimp [pref_r1, pref_r0, L_raw1]
    simp only [List.length_append, List.length_singleton]
    omega
  have hin₆ : s₆.arrs 0 = [x.n, edges₀.length] ++ flatEdges edges₀ := by
    rw [hex₆.arr_eq_of_preservesArr (by decide),
        harr5_₀ 0 (by decide) (by decide) (by decide) (by decide)]
    exact hin₀
  have hadj_G₆ : IsAdjList x.G 3 4 5 (edgeNeighbors edges₀) s₆ :=
    hadj_G₅.of_arrs_eq
      (hex₆.arr_eq_of_preservesArr (by decide))
      (hex₆.arr_eq_of_preservesArr (by decide))
      (hex₆.arr_eq_of_preservesArr (by decide))
  have hent_G₆ : (s₆.arrs 5).length < 2 ^ w := by
    rw [hex₆.arr_eq_of_preservesArr (by decide)]; exact hent_G₅
  have hadj_Y₆ : IsAdjList (restrictGraph x.G (Finset.univ \ Z)) 6 7 8
      (restrictListFamily (Finset.univ \ Z) (edgeNeighbors edges₀)) s₆ :=
    hadj_Y₅.of_arrs_eq
      (hex₆.arr_eq_of_preservesArr (by decide))
      (hex₆.arr_eq_of_preservesArr (by decide))
      (hex₆.arr_eq_of_preservesArr (by decide))
  have hent_Y₆ : (s₆.arrs 8).length < 2 ^ w := by
    rw [hex₆.arr_eq_of_preservesArr (by decide)]; exact hent_Y₅
  have hZ₆ : IsBitSet Z 14 s₆ :=
    hZ₅.of_arr_eq (hex₆.arr_eq_of_preservesArr (by decide))
  have hout₆ : s₆.arrs outArr = pref_r1 ++ List.replicate (cap - pref_r1.length) 0 := by
    rw [hex₆.arr_eq_of_preservesArr (by decide)]; exact hout₅
  have hr1_₆ : s₆.regs 1 = edges₀.length := by
    rw [hex₆.reg_eq_of_preservesReg (by decide), hex₅.reg_eq_of_preservesReg (by decide)]
    exact hr1_₀
  have hr14_₆ : s₆.regs 14 = x.n := by
    rw [hex₆.reg_eq_of_preservesReg (by decide)]; exact hr14_₅
  have hr25_₆ : s₆.regs 25 = pref_r1.length := by
    rw [hex₆.reg_eq_of_preservesReg (by decide)]; exact hr25_₅
  have hr26_₆ : s₆.regs 26 = L_raw1.length := by
    rw [hex₆.reg_eq_of_preservesReg (by decide)]; simpa using hr26_₅
  clear hout₀ hout₄ hout₅ hr25_₅ hr26_₅
  rcases alg86TypeIIPassProg_exec x.G (edgeNeighbors edges₀)
      (restrictListFamily (Finset.univ \ Z) (edgeNeighbors edges₀)) Z edges₀
      pref_r1 L_raw1.length htot_G htot_Y hcap_r2 hw3 hn_w hm8_w hcap_w
      (by obtain ⟨_, hraw1_len⟩ := length_alg86TypeIPairs_le Z edges₀ ∅ edges₀.length
          dsimp [L_raw1]; omega)
      hin₆ hadj_G₆ hent_G₆ hadj_Y₆ hent_Y₆ hZ₆ hout₆ hr1_₆ hr14_₆ hr25_₆ hr26_₆ with
    ⟨s₇, t₇, hex₇, ht₇, hout₇, hr25_₇, hr26_₇, harr₇, hreg₇⟩
  clear hout₆ hr25_₆ hr26_₆
  -- Step 5: alg86TypeIIIPassProg (raw)
  let pref_r2 := pref_r1 ++ L_raw2.flatMap (fun p => encAlg86Subgraph p.1 p.2)
  have hcap_r3 : pref_r2.length + x.n * (x.n + 2) ≤ cap := by
    obtain ⟨hraw1_flat, _⟩ := length_alg86TypeIPairs_le Z edges₀ ∅ edges₀.length
    have hraw2_flat := length_flatMap_alg86TypeIIPairs_le x.G Z edges₀ x.n
    dsimp [pref_r2, pref_r1, pref_r0, L_raw1, L_raw2]
    simp only [List.length_append, List.length_singleton]
    omega
  have hom₇ : IsBitSet x.omega.toFinset 9 s₇ := by
    refine hom₀.of_arr_eq ?_
    rw [hex₇.arr_eq_of_preservesArr (by decide),
        hex₆.arr_eq_of_preservesArr (by decide),
        harr5_₀ 9 (by decide) (by decide) (by decide) (by decide)]
  have harr2_₇ : s₇.arrs 2 = s₀'.arrs 2 := by
    rw [hex₇.arr_eq_of_preservesArr (by decide),
        hex₆.arr_eq_of_preservesArr (by decide),
        harr5_₀ 2 (by decide) (by decide) (by decide) (by decide)]
  have hr14_₇ : s₇.regs 14 = x.n := by
    rw [hex₇.reg_eq_of_preservesReg (by decide)]; exact hr14_₆
  rcases alg86TypeIIIPassProg_exec x.omega.toFinset edges₀ pref_r2 (L_raw1.length + L_raw2.length)
      hcap_r3 hw2 hn_w h2m_w hcap_w
      (by obtain ⟨_, hraw1_len⟩ := length_alg86TypeIPairs_le Z edges₀ ∅ edges₀.length
          have hraw2_len := length_alg86TypeIIPairs_le x.G Z edges₀ x.n
          dsimp [L_raw1, L_raw2]; omega)
      (s := s₇)
      hom₇ (by rw [harr2_₇, hdeg_len₀])
      (fun v => by simp only [harr2_₇]; exact hdeg_val₀ v)
      hdeg_w hout₇ hr14_₇ hr25_₇ hr26_₇ with
    ⟨s₈, t₈, hex₈, ht₈, hout₈, hr25_₈, hr26_₈, harr₈, hreg₈⟩
  clear hout₇ hr25_₇ hr26_₇
  -- Step 6: write outArr[r_19] := r_26 (raw count)
  have hr19_₈ : s₈.regs 19 = pref_core.length := by
    rw [hex₈.reg_eq_of_preservesReg (by decide),
        hex₇.reg_eq_of_preservesReg (by decide),
        hex₆.reg_eq_of_preservesReg (by decide),
        hex₅.reg_eq_of_preservesReg (by decide)]
    rfl
  have hraw_cnt_eq : L_raw1.length + L_raw2.length + L_raw3.length = rawPairs.length := by
    simp [rawPairs, alg86RawPairList, L_raw1, L_raw2, L_raw3, Nat.add_assoc]
  have hr26_8_eq : s₈.regs 26 = rawPairs.length := hr26_₈.trans hraw_cnt_eq
  have hraw_cnt_w : rawPairs.length < 2 ^ w := by
    obtain ⟨_, hraw1_len⟩ := length_alg86TypeIPairs_le Z edges₀ ∅ edges₀.length
    have hraw2_len := length_alg86TypeIIPairs_le x.G Z edges₀ x.n
    obtain ⟨_, hraw3_len⟩ := length_alg86TypeIIIPairs_le x.omega.toFinset edges₀ x.n
    rw [← hraw_cnt_eq]
    dsimp [L_raw1, L_raw2, L_raw3]; omega
  let rawBody := (L_raw1 ++ L_raw2 ++ L_raw3).flatMap (fun p => encAlg86Subgraph p.1 p.2)
  have hout₈_form :
      s₈.arrs outArr =
        pref_core ++ [0] ++ rawBody ++
          List.replicate (cap - (pref_r2 ++ L_raw3.flatMap (fun p => encAlg86Subgraph p.1 p.2)).length) 0 := by
    rw [hout₈]
    dsimp [pref_r2, pref_r1, pref_r0, rawBody, L_raw3]
    simp only [List.flatMap_append, List.append_assoc]
  have hidx_r19 : pref_core.length < (s₈.arrs outArr).length := by
    simp only [hout₈_form, List.length_append, List.length_singleton]
    omega
  let s₉ := s₈.writeArr outArr pref_core.length rawPairs.length
  have hex₉ : Exec w (.write outArr (.reg 19) (.reg 26)) s₈ s₉ 3 :=
    .write (by simp [Expr.eval, checkWord, hr19_₈, hr25_0_w])
      (by simp [Expr.eval, checkWord, hr26_8_eq, hraw_cnt_w])
      hidx_r19
  obtain ⟨pref_raw, hpref_raw_def⟩ : ∃ l, l = pref_core ++ encAlg86PairList rawPairs := ⟨_, rfl⟩
  have hpref_raw_len :
      (pref_r2 ++ L_raw3.flatMap (fun p => encAlg86Subgraph p.1 p.2)).length = pref_raw.length := by
    rw [hpref_raw_def]
    dsimp [pref_r2, pref_r1, pref_r0, encAlg86PairList, rawPairs, alg86RawPairList,
      L_raw1, L_raw2, L_raw3]
    simp only [List.flatMap_append, List.length_append, List.length_cons, List.length_nil]
    omega
  have hout₉ : s₉.arrs outArr = pref_raw ++ List.replicate (cap - pref_raw.length) 0 := by
    change (s₈.arrs outArr).set pref_core.length rawPairs.length = _
    rw [hout₈_form, set_zero_between, hpref_raw_len, hpref_raw_def]
    dsimp [encAlg86PairList, rawPairs, alg86RawPairList, rawBody, L_raw1, L_raw2, L_raw3]
    simp only [List.append_assoc, List.cons_append, List.nil_append]
  -- Step 7: r_19 := r_25, r_25 := r_25 + 1, r_26 := 0
  have hr25_9_eq : s₉.regs 25 = pref_raw.length := by
    change s₈.regs 25 = _
    rw [hr25_₈, hpref_raw_len]
  clear hout₈ hr25_₈ hr26_₈ hout₈_form hpref_raw_len hidx_r19
  have hpref_raw_plus_div_cap :
      pref_raw.length +
        (1 + x.n * (x.n + 2 + 2 * edges₀.length) + edges₀.length * (x.n + 4) + x.n * (x.n + 2)) ≤ cap := by
    obtain ⟨hraw_enc_le, _⟩ := length_encAlg86PairList_raw_le x.G Z x.omega.toFinset edges₀
    have hpref_raw_eq_len : pref_raw.length = pref_core.length + (encAlg86PairList (alg86RawPairList x.G Z x.omega.toFinset edges₀)).length := by
      rw [hpref_raw_def]; exact List.length_append
    linarith [hpref_raw_eq_len, hraw_enc_le, htotal_cap]
  have hpref_raw_w : pref_raw.length < 2 ^ w := by omega
  have hpref_raw1_w : pref_raw.length + 1 < 2 ^ w := by omega
  let s₁₀ := s₉.setReg 19 pref_raw.length
  have hex₁₀ : Exec w (.assign 19 (.reg 25)) s₉ s₁₀ 2 :=
    .assign (by simp [Expr.eval, checkWord, hr25_9_eq, hpref_raw_w])
  let s₁₁ := s₁₀.setReg 25 (pref_raw.length + 1)
  have hex₁₁ : Exec w (.assign 25 (.op .add (.reg 25) (.const 1))) s₁₀ s₁₁ 4 :=
    .assign (by simp [s₁₀, State.setReg, Expr.eval, BinOp.eval, BinOp.raw, checkWord,
      hr25_9_eq, hpref_raw_w, hw, hpref_raw1_w])
  let s₁₂ := s₁₁.setReg 26 0
  have hex₁₂ : Exec w (.assign 26 (.const 0)) s₁₁ s₁₂ 2 :=
    .assign (by simp [Expr.eval, checkWord, h0_w])
  let pref_d0 := pref_raw ++ [0]
  have hout₁₂ : s₁₂.arrs outArr = pref_d0 ++ List.replicate (cap - pref_d0.length) 0 := by
    change s₉.arrs outArr = _
    rw [hout₉]
    dsimp [pref_d0]
    have hrep : cap - pref_raw.length = 1 + (cap - (pref_raw ++ [0]).length) := by
      simp only [List.length_append, List.length_singleton]; omega
    rw [hrep, List.replicate_add, List.replicate_one, List.append_assoc]
  clear hout₉
  -- Step 8: alg86CaseCPassProg (div)
  have hcap_d1 : pref_d0.length + x.n * (x.n + 2 + 2 * edges₀.length) ≤ cap := by
    dsimp [pref_d0]
    rw [List.length_append, List.length_singleton]
    omega
  have harr12_8 : ∀ a : Arr, a ≠ outArr → s₁₂.arrs a = s₈.arrs a := by
    intro a hout
    change s₉.arrs a = s₈.arrs a
    exact hex₉.arr_eq_of_preservesArr (by simp [Cmd.preservesArr]; exact Ne.symm hout)
  have harr12_6 : ∀ a : Arr, a ≠ outArr → a ≠ 12 → a ≠ 13 → a ≠ 15 → a ≠ 17 → a ≠ 18 →
      s₁₂.arrs a = s₆.arrs a := by
    intro a hout h12 h13 h15 h17 h18
    rw [harr12_8 a hout, harr₈ a hout h17 h18, harr₇ a hout h12 h13 h15 h17 h18]
  have hin₁₂ : s₁₂.arrs 0 = [x.n, edges₀.length] ++ flatEdges edges₀ := by
    rw [harr12_6 0 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]
    exact hin₆
  have hadj_G₁₂ : IsAdjList x.G 3 4 5 (edgeNeighbors edges₀) s₁₂ :=
    hadj_G₆.of_arrs_eq
      (harr12_6 3 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))
      (harr12_6 4 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))
      (harr12_6 5 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))
  have hent_G₁₂ : (s₁₂.arrs 5).length < 2 ^ w := by
    rw [harr12_6 5 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]
    exact hent_G₆
  have hadj_Y₁₂ : IsAdjList (restrictGraph x.G (Finset.univ \ Z)) 6 7 8
      (restrictListFamily (Finset.univ \ Z) (edgeNeighbors edges₀)) s₁₂ :=
    hadj_Y₆.of_arrs_eq
      (harr12_6 6 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))
      (harr12_6 7 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))
      (harr12_6 8 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))
  have hent_Y₁₂ : (s₁₂.arrs 8).length < 2 ^ w := by
    rw [harr12_6 8 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]
    exact hent_Y₆
  have hZ₁₂ : IsBitSet Z 14 s₁₂ :=
    hZ₆.of_arr_eq (harr12_6 14 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))
  have htup₁₂ : HasAlg86Tuples x.G Z s₁₂ :=
    htup₆.of_arrs_eq
      (harr12_6 52 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))
      (harr12_6 53 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))
      (harr12_6 54 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))
      (harr12_6 55 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))
  have hM₁₂ : IsBitSet (∅ : Finset (Fin edges₀.length)) 51 s₁₂ := by
    refine hM_empty₄.of_arr_eq ?_
    rw [harr12_6 51 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),
        hex₆.arr_eq_of_preservesArr (by decide),
        harr₅ 51 (by decide) (by decide) (by decide)]
  have hr1_₁₂ : s₁₂.regs 1 = edges₀.length := by
    change s₈.regs 1 = edges₀.length
    rw [hex₈.reg_eq_of_preservesReg (by decide), hex₇.reg_eq_of_preservesReg (by decide)]
    exact hr1_₆
  have hr14_₁₂ : s₁₂.regs 14 = x.n := by
    change s₈.regs 14 = x.n
    rw [hex₈.reg_eq_of_preservesReg (by decide)]; exact hr14_₇
  rcases alg86CaseCPassProg_exec x.G (edgeNeighbors edges₀)
      (restrictListFamily (Finset.univ \ Z) (edgeNeighbors edges₀)) Z edges₀ ∅
      pref_d0 0 htot_G htot_Y hcap_d1 hw3 hn_w hm8_w hcap_w (by omega)
      hin₁₂ hadj_G₁₂ hent_G₁₂ hadj_Y₁₂ hent_Y₁₂ hZ₁₂ htup₁₂ hM₁₂ hout₁₂
      hr1_₁₂ hr14_₁₂
      (by simp [s₁₂, s₁₁, pref_d0])
      (by simp [s₁₂]) with
    ⟨s₁₃, t₁₃, hex₁₃, ht₁₃, hM₁₃, hout₁₃, hr25_₁₃, hr26_₁₃, harr₁₃, hreg₁₃⟩
  clear hout₁₂
  -- Step 9: alg86TypeIPassProg (div)
  let pref_d1 := pref_d0 ++ L_div1.flatMap (fun p => encAlg86Subgraph p.1 p.2)
  have hcap_d2 : pref_d1.length + edges₀.length * (x.n + 4) ≤ cap := by
    have hdiv1_flat := length_flatMap_alg86CaseCPairs_le x.G Z edges₀ x.n
    dsimp [pref_d1, pref_d0, L_div1]
    rw [List.length_append, List.length_append, List.length_singleton]
    omega
  have hin₁₃ : s₁₃.arrs 0 = [x.n, edges₀.length] ++ flatEdges edges₀ := by
    rw [hex₁₃.arr_eq_of_preservesArr (by decide)]; exact hin₁₂
  have hZ₁₃ : IsBitSet Z 14 s₁₃ :=
    hZ₁₂.of_arr_eq (hex₁₃.arr_eq_of_preservesArr (by decide))
  have hr1_₁₃ : s₁₃.regs 1 = edges₀.length := by
    rw [hex₁₃.reg_eq_of_preservesReg (by decide)]; exact hr1_₁₂
  have hr14_₁₃ : s₁₃.regs 14 = x.n := by
    rw [hex₁₃.reg_eq_of_preservesReg (by decide)]; exact hr14_₁₂
  rcases alg86TypeIPassProg_exec Z edges₀ M' pref_d1 L_div1.length
      hcap_d2 hw4 hn_w hm3_w hcap_w
      (by have hdiv1_len := length_alg86CaseCPairs_le x.G Z edges₀ x.n
          dsimp [L_div1]; omega)
      (s := s₁₃)
      hin₁₃ hZ₁₃ hM₁₃ hout₁₃ hr1_₁₃ hr14_₁₃ hr25_₁₃ (by simpa using hr26_₁₃) with
    ⟨s₁₄, t₁₄, hex₁₄, ht₁₄, hout₁₄, hr25_₁₄, hr26_₁₄, harr₁₄, hreg₁₄⟩
  clear hout₁₃ hr25_₁₃ hr26_₁₃
  -- Step 10: alg86TypeIIIPassProg (div)
  let pref_d2 := pref_d1 ++ L_div2.flatMap (fun p => encAlg86Subgraph p.1 p.2)
  have hcap_d3 : pref_d2.length + x.n * (x.n + 2) ≤ cap := by
    have hdiv1_flat := length_flatMap_alg86CaseCPairs_le x.G Z edges₀ x.n
    obtain ⟨hdiv2_flat, _⟩ := length_alg86TypeIPairs_le Z edges₀ M' edges₀.length
    dsimp [pref_d2, pref_d1, pref_d0, L_div1, L_div2]
    rw [List.length_append, List.length_append, List.length_append, List.length_singleton]
    omega
  have hom₁₄ : IsBitSet x.omega.toFinset 9 s₁₄ := by
    refine hom₇.of_arr_eq ?_
    rw [hex₁₄.arr_eq_of_preservesArr (by decide),
        hex₁₃.arr_eq_of_preservesArr (by decide),
        harr12_8 9 (by decide),
        hex₈.arr_eq_of_preservesArr (by decide)]
  have harr2_₁₄ : s₁₄.arrs 2 = s₀'.arrs 2 := by
    rw [hex₁₄.arr_eq_of_preservesArr (by decide),
        hex₁₃.arr_eq_of_preservesArr (by decide),
        harr12_8 2 (by decide),
        hex₈.arr_eq_of_preservesArr (by decide), harr2_₇]
  have hr14_₁₄ : s₁₄.regs 14 = x.n := by
    rw [hex₁₄.reg_eq_of_preservesReg (by decide)]; exact hr14_₁₃
  rcases alg86TypeIIIPassProg_exec x.omega.toFinset edges₀ pref_d2 (L_div1.length + L_div2.length)
      hcap_d3 hw2 hn_w h2m_w hcap_w
      (by have hdiv1_len := length_alg86CaseCPairs_le x.G Z edges₀ x.n
          obtain ⟨_, hdiv2_len⟩ := length_alg86TypeIPairs_le Z edges₀ M' edges₀.length
          dsimp [L_div1, L_div2]; omega)
      (s := s₁₄)
      hom₁₄ (by rw [harr2_₁₄, hdeg_len₀])
      (fun v => by simp only [harr2_₁₄]; exact hdeg_val₀ v)
      hdeg_w hout₁₄ hr14_₁₄ hr25_₁₄ hr26_₁₄ with
    ⟨s₁₅, t₁₅, hex₁₅, ht₁₅, hout₁₅, hr25_₁₅, hr26_₁₅, harr₁₅, hreg₁₅⟩
  clear hout₁₄ hr25_₁₄ hr26_₁₄
  -- Step 11: write outArr[r_19] := r_26 (div count)
  have hr19_₁₅ : s₁₅.regs 19 = pref_raw.length := by
    rw [hex₁₅.reg_eq_of_preservesReg (by decide),
        hex₁₄.reg_eq_of_preservesReg (by decide),
        hex₁₃.reg_eq_of_preservesReg (by decide)]
    rfl
  have hdiv_cnt_eq : L_div1.length + L_div2.length + L_div3.length = divPairs.length := by
    simp [divPairs, alg86DivPairList, L_div1, L_div2, L_div3, M', Nat.add_assoc]
  have hr26_15_eq : s₁₅.regs 26 = divPairs.length := hr26_₁₅.trans hdiv_cnt_eq
  have hdiv_cnt_w : divPairs.length < 2 ^ w := by
    have hdiv1_len := length_alg86CaseCPairs_le x.G Z edges₀ x.n
    obtain ⟨_, hdiv2_len⟩ := length_alg86TypeIPairs_le Z edges₀ M' edges₀.length
    obtain ⟨_, hdiv3_len⟩ := length_alg86TypeIIIPairs_le x.omega.toFinset edges₀ x.n
    rw [← hdiv_cnt_eq]
    dsimp [L_div1, L_div2, L_div3]; omega
  let divBody := (L_div1 ++ L_div2 ++ L_div3).flatMap (fun p => encAlg86Subgraph p.1 p.2)
  have hout₁₅_form :
      s₁₅.arrs outArr =
        pref_raw ++ [0] ++ divBody ++
          List.replicate (cap - (pref_d2 ++ L_div3.flatMap (fun p => encAlg86Subgraph p.1 p.2)).length) 0 := by
    rw [hout₁₅]
    dsimp [pref_d2, pref_d1, pref_d0, divBody, L_div3]
    simp only [List.flatMap_append, List.append_assoc]
  have hidx_d19 : pref_raw.length < (s₁₅.arrs outArr).length := by
    simp only [hout₁₅_form, List.length_append, List.length_singleton]
    omega
  let s₁₆ := s₁₅.writeArr outArr pref_raw.length divPairs.length
  have hex₁₆ : Exec w (.write outArr (.reg 19) (.reg 26)) s₁₅ s₁₆ 3 :=
    .write (by simp [Expr.eval, checkWord, hr19_₁₅, hpref_raw_w])
      (by simp [Expr.eval, checkWord, hr26_15_eq, hdiv_cnt_w])
      hidx_d19
  let fullPref := pref_raw ++ encAlg86PairList divPairs
  have hfull_def : fullPref = pref_raw ++ (divPairs.length :: divBody) := rfl
  have hfull_len2 :
      (pref_d2 ++ L_div3.flatMap (fun p => encAlg86Subgraph p.1 p.2)).length =
        (pref_raw ++ [0] ++ divBody).length := by
    dsimp [pref_d2, pref_d1, pref_d0, divBody, L_div3]
    simp only [List.flatMap_append, List.append_assoc]
  have hfull_len :
      (pref_d2 ++ L_div3.flatMap (fun p => encAlg86Subgraph p.1 p.2)).length = fullPref.length := by
    rw [hfull_len2, hfull_def]
    exact length_append_zero_append_eq pref_raw divBody divPairs.length
  have hout₁₆ : s₁₆.arrs outArr = fullPref ++ List.replicate (cap - fullPref.length) 0 := by
    change (s₁₅.arrs outArr).set pref_raw.length divPairs.length = _
    rw [hout₁₅_form, hfull_len2, hfull_def]
    exact set_append_zero_append pref_raw divBody divPairs.length cap
  clear hout₁₅ hout₁₅_form hfull_len hfull_len2 hidx_d19
  have hex_emit :
      Exec w alg86EmitBothProg s₀' s₁₆
        (2 + (4 + (2 + ((1 + edges₀.length) + (t₅ + (t₆ + (t₇ + (t₈ + (3 +
          (2 + (4 + (2 + (t₁₃ + (t₁₄ + (t₁₅ + 3))))))))))))))) :=
    .seq hex₁ (.seq hex₂ (.seq hex₃ (.seq hex₄ (.seq hex₅ (.seq hex₆ (.seq hex₇
      (.seq hex₈ (.seq hex₉ (.seq hex₁₀ (.seq hex₁₁ (.seq hex₁₂ (.seq hex₁₃
        (.seq hex₁₄ (.seq hex₁₅ hex₁₆))))))))))))))
  have htime :
      t₀ + (2 + (4 + (2 + ((1 + edges₀.length) + (t₅ + (t₆ + (t₇ + (t₈ + (3 +
        (2 + (4 + (2 + (t₁₃ + (t₁₄ + (t₁₅ + 3))))))))))))))) ≤ 5000 * alg81Size x :=
    alg86Divisions_time_le x.n edges₀.length (alg81Size x) t₀ t₅ t₆ t₇ t₈ t₁₃ t₁₄ t₁₅
      hS_expand ht₀ ht₅ ht₆ ht₇ ht₈ ht₁₃ ht₁₄ ht₁₅
  have hfp :
      fullPref =
        ([0] ++ (bitSetList Z ++ ([x.n, edges_C.length] ++ flatEdges edges_C))) ++
          encAlg86PairList rawPairs ++ encAlg86PairList divPairs := by
    dsimp only [fullPref]
    rw [hpref_raw_def, hpref_core_def]
  have hout_final :
      s₁₆.arrs outArr =
        (([0] ++ (bitSetList Z ++ ([x.n, edges_C.length] ++ flatEdges edges_C))) ++
          encAlg86PairList rawPairs ++ encAlg86PairList divPairs) ++
        List.replicate (cap -
          (([0] ++ (bitSetList Z ++ ([x.n, edges_C.length] ++ flatEdges edges_C))) ++
            encAlg86PairList rawPairs ++ encAlg86PairList divPairs).length) 0 := by
    rw [← hfp]
    exact hout₁₆
  exact ⟨s₁₆, _, Z, C, edges_C, .seq hex₀ hex_emit, htime,
    htrace, hom_sub, hadj_Z, hcore4, hedges_C, hlen_C, hout_final⟩

end GraphMinor.Compute
