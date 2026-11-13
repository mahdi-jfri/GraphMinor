module

public import GraphMinor.Compute.GM13ClassFolio
public import GraphMinor.Compute.Algorithm44
public import GraphMinor.Compute.Algorithm101Defs
public import GraphMinor.Compute.GM13PairCapProg
import GraphMinor.Compute.GM13PairCapMinor

/-!
# The Word RAM program of Graph Minors XIII, (4.3)

The program caps multiplicities (`capPairProg`: at most `δ` loops at each vertex and at most
`δ + 1` edges between two distinct vertices), calls (3.3), and rejects its high-width outcome.
In the other outcome it calls (4.1) at the empty root set and reads the answer
from a finite decision tree for the fixed class. The proof counts all four steps.
-/

@[expose] public section
namespace GraphMinor.Compute

open GraphMinor GM13 Set Graph Classical

/-- The fixed finite lookup in Step (4) of XIII (4.3), page 77. -/
noncomputable def classLookup43 (ℱ : Set (Graph ℕ (ℕ × ℕ × ℕ))) (δ : ℕ) : Cmd :=
  folioTrieAuxProg 15 outReg 10 (maxFolioEncWord 0 δ)
    (classFolioAnswer43 ℱ δ) (maxFolioEncLen101 0 δ) []

/-- Steps (1)–(4) of XIII (4.3), page 77. Array `11` holds the capped graph,
`12` the graph returned by (3.3), `13` its decomposition, and `15` its folio.
The flag in register `10` says whether (3.3) kept the whole capped graph. -/
noncomputable def alg43Prog (ℱ : Set (Graph ℕ (ℕ × ℕ × ℕ))) (δ : ℕ)
    (P33 P41 : Cmd) : Cmd :=
  .seq (capPairProg δ inArr 10 11 10)
    (.seq P33
      (.ite (.op .eq (.reg 10) (.const 0))
        (.assign outReg (.const 0))
        (.seq (initEmptyZProg 14) (.seq P41 (classLookup43 ℱ δ)))))

/-- Time used by the fixed folio decision tree. -/
def classLookupTime43 (δ : ℕ) : ℕ :=
  (maxFolioEncLen101 0 δ + 1) * (4 * maxFolioEncWord 0 δ + 10)

/-- The word multiplier covers the two subroutine calls and the finite folio tree. -/
noncomputable def alg43WordConst (δ ω c33 c41 : ℕ) : ℕ :=
  alg44WordConst 0 δ ω c33 c41 + maxFolioEncLen101 0 δ + maxFolioEncWord 0 δ + 3

private theorem wordSize_mul43 (c : ℕ) {K M m : ℕ} (hK : 2 ≤ K) (hM : M ≤ K * m) :
    wordSize c M ≤ wordSize (c * K) m := by
  unfold wordSize
  have h1 : M + 2 ≤ K * (m + 1) := by nlinarith
  have h2 : M + 2 ≤ (m + 2) ^ K := le_trans h1 (mul_succ_le_pow_add_two K m)
  have h3 : (m + 2) ^ K < (2 ^ (Nat.log 2 (m + 2) + 1)) ^ K :=
    Nat.pow_lt_pow_left (lt_two_pow_log_succ m) (by omega)
  rw [← Nat.pow_mul, Nat.mul_comm _ K] at h3
  have hlog : Nat.log 2 (M + 2) < K * (Nat.log 2 (m + 2) + 1) :=
    Nat.log_lt_of_lt_pow (by omega) (lt_of_le_of_lt h2 h3)
  have hlog1 : Nat.log 2 (M + 2) + 1 ≤ K * (Nat.log 2 (m + 2) + 1) := by omega
  rw [Nat.mul_assoc]
  exact Nat.mul_le_mul_left c hlog1

/-- Execution of the finite tree, including its time and Boolean output. -/
theorem classLookup43_exec {w δ : ℕ} (ℱ : Set (Graph ℕ (ℕ × ℕ × ℕ)))
    (F : FolioSetRep 0 δ) (s : State) (hF : s.arrs 15 = encFolioSetRep F)
    (hw_len : maxFolioEncLen101 0 δ < 2 ^ w)
    (hw_word : maxFolioEncWord 0 δ + 1 < 2 ^ w) :
    ∃ s' t, Exec w (classLookup43 ℱ δ) s s' t ∧
      t ≤ classLookupTime43 δ ∧
      s'.regs outReg = classFolioAnswer43 ℱ δ (encFolioSetRep F) := by
  have hbounds := length_and_words_encFolioSetRep_le (q := 0) (by decide : 0 ≤ 0 + 3) F
  have hlen : (encFolioSetRep F).length < 2 ^ w := hbounds.1.trans_lt hw_len
  have hf : ∀ pref, classFolioAnswer43 ℱ δ pref < 2 ^ w := fun pref =>
    lt_of_le_of_lt (classFolioAnswer43_le_one ℱ δ pref) (by omega)
  obtain ⟨s', t, he, ht, ho, _, _⟩ := folioTrieAuxProg_exec 15 outReg 10
    (maxFolioEncWord 0 δ) (classFolioAnswer43 ℱ δ) hf F [] hbounds.2
    hw_word hlen (maxFolioEncLen101 0 δ) 0 (by omega) (by omega) hw_len s
    (by simpa using hF)
  exact ⟨s', t, by simpa only [List.take_zero, classLookup43] using he, ht, ho⟩

/-- The local execution proof for XIII (4.3), page 77. The finite basis and the
width cutoff are the data established before Step (1) in the paper's proof.
The final recognition theorem derives them from minor closure and planar exclusion. -/
theorem alg43Prog_exec
    (ℱ : Set (Graph ℕ (ℕ × ℕ × ℕ))) (B : Finset (Graph ℕ (ℕ × ℕ × ℕ)))
    (δ ω : ℕ) (hω : 2 ≤ ω)
    (hB : ∀ H ∈ B, V(H).Finite ∧ E(H).Finite ∧ V(H).ncard ≤ δ ∧ E(H).ncard ≤ δ)
    (hclass : ∀ G : Graph ℕ (ℕ × ℕ × ℕ), V(G).Finite → E(G).Finite →
      (G ∈ ℱ ↔ ∀ H ∈ B, ¬ IsIsoMinor H G))
    (hclosed : ∀ ⦃G₁ G₂ : Graph ℕ (ℕ × ℕ × ℕ)⦄,
      V(G₁).Finite → E(G₁).Finite → V(G₂).Finite → E(G₂).Finite →
      IsIsoMinor G₁ G₂ → G₂ ∈ ℱ → G₁ ∈ ℱ)
    (hhigh : ∀ G : Graph ℕ (ℕ × ℕ × ℕ), V(G).Finite → E(G).Finite →
      ¬ GraphBranchWidthLE G (ω - 1) → G ∉ ℱ)
    (P33 P41 : Cmd) (h33 : Alg33Spec ω 11 12 13 20 10 P33)
    (h41 : Alg41MultiSpec 0 δ (3 * ω) 12 14 13 15 16 20 10 P41) :
    ∃ C c : ℕ, 0 < C ∧ 0 < c ∧
      ∀ (n : ℕ) (G : MultiDigraph n) (w : ℕ),
        wordSize c ((n + 1) ^ 2) ≤ w → ∀ s : State,
        s.arrs inArr = G.enc →
        ∃ s' t, Exec w (alg43Prog ℱ δ P33 P41) s s' t ∧
          t ≤ C * (n + 1) ^ 2 ∧
          s'.regs outReg = if G.toGMDigraph.toGraph ∈ ℱ then 1 else 0 := by
  obtain ⟨C33, c33, hC33, hc33, run33⟩ := h33
  obtain ⟨C41, c41, hC41, hc41, run41⟩ := h41
  let C := alg44TimeConst 0 δ C33 C41 + 5 + classLookupTime43 δ + 230
  let c := alg43WordConst δ ω c33 c41
  have hC : 0 < C := by dsimp [C]; omega
  have hc : 0 < c := by dsimp [c, alg43WordConst]; omega
  refine ⟨C, c, hC, hc, ?_⟩
  intro n G w hw s hin
  have hS : 1 ≤ (n + 1) ^ 2 := Nat.one_le_pow _ _ (by omega)
  have hprod : c * (n + 1) ^ 2 < 2 ^ w := mul_lt_two_pow_of_wordSize_le hc hw
  have hc_lt : c < 2 ^ w := lt_of_le_of_lt (Nat.le_mul_of_pos_right c hS) hprod
  have h44prod : alg44WordConst 0 δ ω c33 c41 * (n + 1) ^ 2 < 2 ^ w :=
    lt_of_le_of_lt (Nat.mul_le_mul_right _ (by dsimp [c, alg43WordConst]; omega)) hprod
  have hm_act := G.numActivePairs_le_sq
  have hcap := (MultiDigraph.numEdges_capPair_le δ G).trans (lemma_4_4_cap_numEdges_le δ G)
  obtain ⟨hw3, hn_w, _, hδcap_w, hδ_w, hm3_w, hedges_w, h3ω_w, _, _, _⟩ :=
    alg44_word_bounds hm_act hcap h44prod
  have h0_w : 0 < 2 ^ w := by omega
  have h1_w : 1 < 2 ^ w := by omega
  have hlen_w : maxFolioEncLen101 0 δ < 2 ^ w := by dsimp [c, alg43WordConst] at hc_lt; omega
  have hword_w : maxFolioEncWord 0 δ + 1 < 2 ^ w := by dsimp [c, alg43WordConst] at hc_lt; omega
  obtain ⟨s₁, t₁, he₁, ht₁, hcap_arr, _, _, _, _, _⟩ :=
    capPairProg_exec G δ [] inArr 10 11 10 (by decide) (by decide)
      hw3 hn_w hδcap_w hm3_w hedges_w (by simpa using hin)
  have hsq : n * n ≤ (n + 1) ^ 2 := by
    have heq : (n + 1) ^ 2 = n * n + 2 * n + 1 := by ring
    omega
  have hM33 : (n + 1) ^ 2 + (G.capPair δ).numEdges ≤ (δ + 2) * (n + 1) ^ 2 := by
    have he := hcap.trans (Nat.mul_le_mul_left (δ + 1) hsq)
    calc (n + 1) ^ 2 + (G.capPair δ).numEdges
      _ ≤ (n + 1) ^ 2 + (δ + 1) * (n + 1) ^ 2 := Nat.add_le_add_left he _
      _ = (δ + 2) * (n + 1) ^ 2 := by ring
  have hw33 : wordSize c33 ((n + 1) ^ 2 + (G.capPair δ).numEdges) ≤ w := by
    apply (wordSize_mul43 c33 (by omega) hM33).trans
    apply (wordSize_mono_left (c₂ := c) ?_ _).trans hw
    dsimp [c, alg43WordConst, alg44WordConst]
    rw [Nat.add_mul]
    omega
  have hmult : ∀ pair ∈ (G.capPair δ).activePairsList,
      (G.capPair δ).edgeMult pair.1 pair.2 < 2 ^ w := by
    intro pair _
    exact lt_of_le_of_lt (G.capPair_edgeMult_le_succ δ _ _) hδcap_w
  obtain ⟨s₂, t₂, G₂, bdCode, he₂, ht₂, hG₂, hbd, hor, haG₂, habd, hflag, _, _⟩ :=
    run33 n (G.capPair δ) w hw33 h3ω_w hmult s₁ hcap_arr
  have hbase : t₂ ≤ alg44TimeConst 0 δ C33 C41 * (n + 1) ^ 2 := by
    have hbound := alg44_time_bound (p := 0) (C₄₁ := C41) (e₂ := G₂.numEdges)
      (t₁ := 0) (t_z := 0) (t₃ := 0) (t_ext := 0) hm_act hcap
      (MultiDigraph.numEdges_mono hG₂) (Nat.zero_le _) ht₂ (by omega) (by omega) (Nat.zero_le _)
    simpa using hbound
  -- the cap takes at most `150 m' + 80 ≤ 230 (n + 1)²` steps
  have hcapt : t₁ ≤ 230 * (n + 1) ^ 2 := by
    have := hm_act.trans hsq
    omega
  by_cases hEq : G₂ = G.capPair δ
  · have hrflag : s₂.regs 10 = 1 := by simpa only [ite_eq_left hEq] using hflag
    have hcond : (Expr.op .eq (.reg 10) (.const 0)).eval w s₂ = some 0 := by
      simp only [Expr.eval, BinOp.eval, BinOp.raw, hrflag,
        checkWord_of_lt h0_w, checkWord_of_lt h1_w, Nat.one_ne_zero, ↓reduceIte]
    obtain ⟨s₃, tz, hez, htz, haZ, harrz, _⟩ := initEmptyZProg_exec (w := w) (n := n) 14
      (by omega) s₂
    have hG₂edges : G₂.numEdges ≤ (G.capPair δ).numEdges := MultiDigraph.numEdges_mono hG₂
    have hM41 : G₂.numEdges + n + 1 ≤ (δ + 2) * (n + 1) ^ 2 := by
      have hnS : n + 1 ≤ (n + 1) ^ 2 := by
        have heq : (n + 1) ^ 2 = n * n + 2 * n + 1 := by ring
        omega
      have he := hG₂edges.trans (hcap.trans (Nat.mul_le_mul_left (δ + 1) hsq))
      calc G₂.numEdges + n + 1
        _ = G₂.numEdges + (n + 1) := by omega
        _ ≤ (δ + 1) * (n + 1) ^ 2 + (n + 1) ^ 2 := Nat.add_le_add he hnS
        _ = (δ + 2) * (n + 1) ^ 2 := by ring
    have hw41 : wordSize c41 (G₂.numEdges + n + 1) ≤ w := by
      apply (wordSize_mul43 c41 (by omega) hM41).trans
      apply (wordSize_mono_left (c₂ := c) ?_ _).trans hw
      dsimp [c, alg43WordConst, alg44WordConst]
      rw [Nat.add_mul]
      omega
    have hmult₂ : ∀ pair ∈ G₂.activePairsList, G₂.edgeMult pair.1 pair.2 < 2 ^ w := by
      intro pair _
      exact lt_of_le_of_lt ((hG₂ _ _).trans (G.capPair_edgeMult_le_succ δ _ _)) hδcap_w
    obtain ⟨s₄, t₄, F, models, he₄, ht₄, hF, haF, _, _, _⟩ :=
      run41 n G₂ [] bdCode w (by simp) hbd hw41 h3ω_w hmult₂ s₃
        (by rw [harrz 12 (by decide)]; exact haG₂) haZ
        (by rw [harrz 13 (by decide)]; exact habd)
    obtain ⟨s₅, t₅, he₅, ht₅, hout⟩ := classLookup43_exec ℱ F s₄ haF hlen_w hword_w
    have hanswer := classFolioAnswer43_correct ℱ B δ hB hclass hF
    have hcapmem := membership_capPair43 ℱ B δ hB hclass G
    rw [hEq] at hanswer
    rw [hanswer, ← hcapmem] at hout
    have htcore := alg44_time_bound (p := 0) (t_ext := 0) hm_act hcap hG₂edges (Nat.zero_le _) ht₂
      htz ht₄ (Nat.zero_le _)
    have hrest : 3 + t₅ ≤ (5 + classLookupTime43 δ) * (n + 1) ^ 2 := by
      have hm := Nat.le_mul_of_pos_right (5 + classLookupTime43 δ) hS
      omega
    refine ⟨s₅, t₁ + (t₂ + (3 + (tz + (t₄ + t₅)))),
      .seq he₁ (.seq he₂ (.ite_false hcond (.seq hez (.seq he₄ he₅)))), ?_, hout⟩
    have htotal : C * (n + 1) ^ 2 =
        alg44TimeConst 0 δ C33 C41 * (n + 1) ^ 2 +
          (5 + classLookupTime43 δ) * (n + 1) ^ 2 + 230 * (n + 1) ^ 2 := by dsimp [C]; ring
    rw [htotal]
    omega
  · have hnot : G.toGMDigraph.toGraph ∉ ℱ := by
      intro hmem
      have hnot₂ : G₂.toGMDigraph.toGraph ∉ ℱ := by
        apply hhigh _ G₂.isFinite_toGMDigraph.finite_V G₂.isFinite_toGMDigraph.finite_E
        have hhigh₂ : HasBranchWidthGe G₂ ω := by
          rcases hor with heq | ⟨_, hh⟩
          · exact (hEq heq).elim
          · exact isAlg33HighWidthCase_imp_hasBranchWidthGe hω hh
        exact hhigh₂.not_graphBranchWidthLE_sub_one (by omega)
      exact hnot₂ (hclosed G₂.isFinite_toGMDigraph.finite_V G₂.isFinite_toGMDigraph.finite_E
        G.isFinite_toGMDigraph.finite_V G.isFinite_toGMDigraph.finite_E
        (isIsoMinor_of_multi_le43 (hG₂.trans (G.capPair_le δ))) hmem)
    have hrflag : s₂.regs 10 = 0 := by simpa only [ite_eq_right hEq] using hflag
    have hcond : (Expr.op .eq (.reg 10) (.const 0)).eval w s₂ = some 1 := by
      simp only [Expr.eval, BinOp.eval, BinOp.raw, hrflag,
        checkWord_of_lt h0_w, checkWord_of_lt h1_w, ↓reduceIte]
    have hzero : (Expr.const 0).eval w s₂ = some 0 := by simp only [Expr.eval, checkWord_of_lt h0_w]
    refine ⟨s₂.setReg outReg 0, t₁ + (t₂ + (3 + 2)),
      .seq he₁ (.seq he₂ (.ite_true hcond (by decide) (.assign hzero))), ?_, ?_⟩
    · have hrest : 5 ≤ (5 + classLookupTime43 δ) * (n + 1) ^ 2 := by
        have hm := Nat.le_mul_of_pos_right (5 + classLookupTime43 δ) hS
        omega
      have htotal : C * (n + 1) ^ 2 =
          alg44TimeConst 0 δ C33 C41 * (n + 1) ^ 2 +
            (5 + classLookupTime43 δ) * (n + 1) ^ 2 + 230 * (n + 1) ^ 2 := by dsimp [C]; ring
      rw [htotal]
      omega
    · simp only [State.setReg_regs, ite_eq_right hnot, ↓reduceIte]

end GraphMinor.Compute
