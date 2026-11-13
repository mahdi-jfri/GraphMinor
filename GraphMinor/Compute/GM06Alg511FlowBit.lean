module

public import GraphMinor.Compute.Menger
import Mathlib.Tactic

/-!
# The machine flag of the initial flow search in VI (5.11)

The initial search on page 134 needs a machine-readable answer as
well as paths or a separator. Reuse the existing augmenting-path
program and its execution proof, retaining the output-head invariant
in each branch. The successful branch writes one and has a full path
system. The failed branch writes zero and a smaller separator. Weak
Menger duality then gives the exact meaning of the raw output flag.
-/

public section
namespace GraphMinor.Compute

/-- The verified maximum-flow program used in VI (5.11) returns a
raw success flag exactly when the requested disjoint paths exist,
with the same uniform linear bound in its Menger input size. -/
theorem gm06Alg511FlowBit_computesInTime :
    ComputesArrRelInTime disjointPathsSize encDisjointPathsIn
      (fun x out => IsValidDisjointPathsOutput x (decDisjointPathsOut x out) ∧
        (out.head? = some 1 →
          IsValidPathSystem x.G x.A x.B (decUsed x.n out) (decPred x.n out) (decSucc x.n out) ∧
          (pathStarts (decUsed x.n out) (decPred x.n out)).card = x.k ∧
          out.length = 1 + 3 * x.n) ∧
        (out.head? = some 0 ∨ out.head? = some 1) ∧
        (out.head? = some 1 ↔ ∃ P : Fin x.k → ABWalk x.G x.A x.B,
          PairwiseVertexDisjoint P ∧ ∀ i, (P i).walk.IsPath))
      disjointPathsEndToEndProg (fun s => s) := by
  unfold ComputesArrRelInTime ComputesRelInTime
  refine ⟨450, 3, by omega, by omega, fun x s₀ hs₀ => ?_⟩
  let edges := edgeListOf x.G
  have hedges : IsSimpleEdgeList x.G edges := isSimpleEdgeList_edgeListOf x.G
  have hm_eq : edges.length = x.G.edgeFinset.card := length_edgeListOf_eq_card_edgeFinset x.G
  have htot_eq : totalAdjEntries (edgeNeighbors edges) = 2 * edges.length :=
    totalAdjEntries_edgeNeighbors edges hedges.1
  set S := disjointPathsSize x
  let w := wordSize 3 S
  have hS_eq : S = (x.k + 1) * (x.n + edges.length + 1) := by simp [S, disjointPathsSize, hm_eq]
  have hnm_le_S : x.n + edges.length + 1 ≤ S := by
    rw [hS_eq]
    exact Nat.le_mul_of_pos_left _ (by omega)
  have hk_le_S : x.k + 1 ≤ S := by
    rw [hS_eq]
    exact Nat.le_mul_of_pos_right _ (by omega)
  have hpow3 : (S + 2) ^ 3 < 2 ^ w := pow_lt_two_pow_wordSize (c := 3) (by omega) S
  have h4S : 4 * (S + 2) ≤ (S + 2) ^ 3 := by
    have h1 : 4 ≤ (S + 2) ^ 2 := by
      calc 4 = 2 ^ 2 := rfl
        _ ≤ (S + 2) ^ 2 := Nat.pow_le_pow_left (by omega) 2
    have h2 : 4 * (S + 2) ≤ (S + 2) * (S + 2) ^ 2 := by
      simpa [Nat.mul_comm] using Nat.mul_le_mul_left (S + 2) h1
    simpa [Nat.pow_succ, Nat.mul_comm] using h2
  have hw_bound : 4 * (S + 2) < 2 ^ w := Nat.lt_of_le_of_lt h4S hpow3
  have h0_w : 0 < 2 ^ w := by omega
  have hw : 1 < 2 ^ w := by omega
  have hw2 : 2 < 2 ^ w := by omega
  have hn_w : x.n < 2 ^ w := by omega
  have h2n_w : 2 * x.n < 2 ^ w := by omega
  have h1n_w : 1 + x.n < 2 ^ w := by omega
  have h3n1_w : 1 + 3 * x.n < 2 ^ w := by omega
  have hm_w : edges.length < 2 ^ w := by omega
  have h2m_w : 2 * edges.length < 2 ^ w := by omega
  have hm2_w : 2 + 2 * edges.length < 2 ^ w := by omega
  have hm2n_w : 2 + 2 * edges.length + x.n < 2 ^ w := by omega
  have hm22n_w : 2 + 2 * edges.length + 2 * x.n < 2 ^ w := by omega
  have hk_w : x.k < 2 ^ w := by omega
  let extra := bitSetList x.A ++ bitSetList x.B ++ [x.k]
  have hin₀ : s₀.arrs inArr = [x.n, edges.length] ++ flatEdges edges ++ extra := by
    simpa [encDisjointPathsIn, encGraph, edges, extra, List.append_assoc] using hs₀
  -- 1. parseGraphProg 2 3 4 5 0
  rcases Triple.parseGraphProg_spec (w := w) x.G edges extra 2 3 4 5 0 hedges
      (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      hw2 hn_w hm2_w s₀ hin₀ with
    ⟨s₁, t₁, hex₁, ht₁, hin₁, hrn₁, hrm₁, hadj₁, hent₁, _⟩
  dsimp only at ht₁
  -- 2. readSliceProg for A into array 6
  have hin₁_A : s₁.arrs inArr =
      ([x.n, edges.length] ++ flatEdges edges) ++ bitSetList x.A ++ (bitSetList x.B ++ [x.k]) := by
    simpa [extra, List.append_assoc] using hin₁
  have hbitA_w : ∀ v ∈ bitSetList x.A, v < 2 ^ w := by
    intro v hv
    rcases List.mem_iff_getElem.mp hv with ⟨i, hi, rfl⟩
    have := getElem_bitSetList_le_one x.A i hi
    omega
  rcases readSliceProg_exec (w := w) (off := 2 + 2 * edges.length) inArr 6
      (.op .add (.const 2) (.op .mul (.const 2) (.reg 1))) 0 2
      (by decide) (by omega)
      ([x.n, edges.length] ++ flatEdges edges) (bitSetList x.A) (bitSetList x.B ++ [x.k])
      (by simp [length_flatEdges]; omega) (length_bitSetList x.A) hbitA_w hw hm2n_w
      (by simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hrm₁, hw2, hm_w, h2m_w, hm2_w])
      hin₁_A hrn₁ with
    ⟨s₂, t₂, hex₂, ht₂, harr6₂, harr_ne₂, hreg_lt₂⟩
  dsimp [Expr.cost] at ht₂
  -- 3. readSliceProg for B into array 7
  have hrn₂ : s₂.regs 0 = x.n := by rw [hreg_lt₂ 0 (by omega), hrn₁]
  have hrm₂ : s₂.regs 1 = edges.length := by rw [hreg_lt₂ 1 (by omega), hrm₁]
  have hin₂_B : s₂.arrs inArr =
      ([x.n, edges.length] ++ flatEdges edges ++ bitSetList x.A) ++ bitSetList x.B ++ [x.k] := by
    rw [harr_ne₂ inArr (by decide)]
    simpa [extra, List.append_assoc] using hin₁
  have hbitB_w : ∀ v ∈ bitSetList x.B, v < 2 ^ w := by
    intro v hv
    rcases List.mem_iff_getElem.mp hv with ⟨i, hi, rfl⟩
    have := getElem_bitSetList_le_one x.B i hi
    omega
  rcases readSliceProg_exec (w := w) (off := 2 + 2 * edges.length + x.n) inArr 7
      (.op .add (.op .add (.const 2) (.op .mul (.const 2) (.reg 1))) (.reg 0)) 0 2
      (by decide) (by omega)
      ([x.n, edges.length] ++ flatEdges edges ++ bitSetList x.A) (bitSetList x.B) [x.k]
      (by simp [length_flatEdges]; omega) (length_bitSetList x.B) hbitB_w hw (by omega)
      (by simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hrm₂, hrn₂,
        hw2, hm_w, h2m_w, hm2_w, hn_w, hm2n_w])
      hin₂_B hrn₂ with
    ⟨s₃, t₃, hex₃, ht₃, harr7₃, harr_ne₃, hreg_lt₃⟩
  dsimp [Expr.cost] at ht₃
  have hrn₃ : s₃.regs 0 = x.n := by rw [hreg_lt₃ 0 (by omega), hrn₂]
  have hrm₃ : s₃.regs 1 = edges.length := by rw [hreg_lt₃ 1 (by omega), hrm₂]
  have hin₃ : s₃.arrs inArr =
      [x.n, edges.length] ++ flatEdges edges ++ bitSetList x.A ++ bitSetList x.B ++ [x.k] := by
    rw [harr_ne₃ inArr (by decide), hin₂_B]
  -- 4. Set r_14 := n, r_15 := 2 * n, r_16 := k, r_17 := 0, r_18 := 1
  let s₄ := s₃.setReg 14 x.n
  have hex₄ : Exec w (.assign 14 (.reg 0)) s₃ s₄ 2 :=
    .assign (by simp [Expr.eval, checkWord, hrn₃, hn_w])
  let s₅ := s₄.setReg 15 (2 * x.n)
  have hex₅ : Exec w (.assign 15 (.op .mul (.const 2) (.reg 0))) s₄ s₅ 4 :=
    .assign (by
      simp [s₄, State.setReg, Expr.eval, BinOp.eval, BinOp.raw, checkWord,
        hrn₃, hw2, hn_w, h2n_w])
  obtain ⟨hlen_k, hget_k⟩ := inArr_getElem_k edges x.A x.B x.k hin₃
  let s₆ := s₅.setReg 16 x.k
  have hex₆ : Exec w (.assign 16 (.read inArr
      (.op .add (.op .add (.const 2) (.op .mul (.const 2) (.reg 1))) (.reg 15)))) s₅ s₆ 9 :=
    .assign (by
      simp [s₅, s₄, State.setReg, Expr.eval, BinOp.eval, BinOp.raw, checkWord,
        hrm₃, hw2, hm_w, h2m_w, hm2_w, h2n_w, hm22n_w, hlen_k, hget_k, hk_w])
  let s₇ := s₆.setReg 17 0
  have hex₇ : Exec w (.assign 17 (.const 0)) s₆ s₇ 2 :=
    .assign (by simp [Expr.eval, checkWord, h0_w])
  let s₈ := s₇.setReg 18 1
  have hex₈ : Exec w (.assign 18 (.const 1)) s₇ s₈ 2 :=
    .assign (by simp [Expr.eval, checkWord, hw])
  have hconst₈ : ConstRegs x.n x.k 2 s₈ := by
    refine ⟨by simp [s₈, s₇, s₆, s₅, s₄, State.setReg],
      by simp [s₈, s₇, s₆, s₅, State.setReg],
      by simp [s₈, s₇, s₆, State.setReg]⟩
  -- 5. initPathSystemRegProg 8 2
  rcases initPathSystemRegProg_exec (w := w) x.G x.A x.B 8 2 hw hn_w hconst₈ with
    ⟨s₉, t₉, hex₉, ht₉, hconst₉, hsys₉, hcard₉, harr₉, hreg₉⟩
  have harr9_lt8 : ∀ a : ℕ, a < 8 → s₉.arrs a = s₃.arrs a := by
    intro a ha
    rw [harr₉ a ha]
    rfl
  have hadj₉ : IsAdjList x.G 3 4 5 (edgeNeighbors edges) s₉ := by
    apply hadj₁.of_arrs_eq
    · rw [harr9_lt8 3 (by omega), harr_ne₃ 3 (by decide), harr_ne₂ 3 (by decide)]
    · rw [harr9_lt8 4 (by omega), harr_ne₃ 4 (by decide), harr_ne₂ 4 (by decide)]
    · rw [harr9_lt8 5 (by omega), harr_ne₃ 5 (by decide), harr_ne₂ 5 (by decide)]
  have hent₉ : (s₉.arrs 5).length < 2 ^ w := by
    rw [harr9_lt8 5 (by omega), harr_ne₃ 5 (by decide), harr_ne₂ 5 (by decide), hent₁]
    exact h2m_w
  have hA_bit₉ : IsBitSet x.A 6 s₉ := by
    apply IsBitSet.of_bitSetList
    rw [harr9_lt8 6 (by omega), harr_ne₃ 6 (by decide), harr6₂]
  have hB_bit₉ : IsBitSet x.B 7 s₉ := by
    apply IsBitSet.of_bitSetList
    rw [harr9_lt8 7 (by omega), harr7₃]
  have hr17_₉ : s₉.regs 17 = 0 := by
    rw [hreg₉ 17 (by omega)]
    simp [s₈, s₇, State.setReg]
  have hr18_₉ : s₉.regs 18 = 1 := by
    rw [hreg₉ 18 (by omega)]
    simp [s₈, State.setReg]
  -- 6. mengerLoopRegProg 3 4 5 6 7 8 2
  rcases mengerLoopRegProg_exec (w := w) x.G (edgeNeighbors edges) x.A x.B
      3 4 5 6 7 8 2 (by omega) (by omega) (by omega) (by omega) (by omega)
      hw h2n_w hk_w x.k 0 (by omega)
      hconst₉ hadj₉ hent₉ hA_bit₉ hB_bit₉ hsys₉ hcard₉ hr17_₉ hr18_₉ with
    ⟨s₁₀, t₁₀, hex₁₀, ht₁₀, hconst₁₀, _, _, hres₁₀⟩
  -- 7. mengerOutputRegProg 8 2
  rcases hres₁₀ with ⟨hok1, used', pred', succ', hsys₁₀, hcard₁₀⟩ |
      ⟨hok0, used', pred', succ', items, hsys₁₀, hcard_lt₁₀, hvis₁₀, hpar₁₀, hclosed₁₀, hinit₁₀, hnoB₁₀⟩
  · have hcond_out : (Expr.reg 18).eval w s₁₀ = some 1 := by
      simp [Expr.eval, checkWord, hok1, hw]
    rcases writePathSystemOutProg_exec (w := w) x.G x.A x.B used' pred' succ' 8 2
        (by decide) hw h3n1_w hconst₁₀ hsys₁₀ with
      ⟨s₁₁, t₁₁, hex₁₁, ht₁₁, hout₁₁⟩
    have hex_out : Exec w (mengerOutputRegProg 8 2) s₁₀ s₁₁ (1 + t₁₁) :=
      .ite_true hcond_out (by omega) hex₁₁
    have hvalid := isValidDisjointPathsOutput_of_pathSystem x hsys₁₀ hcard₁₀ hout₁₁
    have htime :
        t₁ + (t₂ + (t₃ + (2 + (4 + (9 + (2 + (2 + (t₉ + (t₁₀ + (1 + t₁₁)))))))))) ≤ 450 * S := by
      have htot_le : totalAdjEntries (edgeNeighbors edges) = 2 * edges.length := htot_eq
      have hloop_le :
          x.k * (65 + 264 * x.n + 31 * totalAdjEntries (edgeNeighbors edges)) ≤
            x.k * (264 * (x.n + edges.length + 1)) := by
        rw [htot_le]
        apply Nat.mul_le_mul_left
        omega
      have hk_le : x.k * (x.n + edges.length + 1) ≤ S := by
        rw [hS_eq, Nat.add_mul, Nat.one_mul]
        omega
      have hk_nm_le : x.k * (264 * (x.n + edges.length + 1)) ≤ 264 * S := by
        rw [Nat.mul_left_comm x.k 264]
        omega
      omega
    refine ⟨s₁₁, _,
      .seq hex₁ (.seq hex₂ (.seq hex₃ (.seq hex₄ (.seq hex₅
        (.seq hex₆ (.seq hex₇ (.seq hex₈ (.seq hex₉ (.seq hex₁₀ hex_out))))))))),
      htime, hvalid, ?_, (by simp [hout₁₁]), ?_⟩
    · intro _
      obtain ⟨hU, hP, hS⟩ := decUsed_pred_succ_eq_of_isPathSystemArrs hsys₁₀.2
      rw [← hout₁₁] at hU hP hS
      rw [hU, hP, hS]
      refine ⟨hsys₁₀.1, hcard₁₀, ?_⟩
      obtain ⟨hlenU, hlenP, hlenS, _⟩ := hsys₁₀.2
      simp only [hout₁₁, List.length_append, List.length_singleton, hlenU, hlenP, hlenS]
      omega
    · constructor
      · intro _
        exact ⟨extractDisjointPaths hsys₁₀.1 hcard₁₀,
          extractDisjointPaths_sound hsys₁₀.1 hcard₁₀⟩
      · intro _
        simp [hout₁₁]
  · have hcond_out : (Expr.reg 18).eval w s₁₀ = some 0 := by
      simp [Expr.eval, checkWord, hok0, h0_w]
    rcases writeResCutOutProg_exec (w := w) 8 2 (by decide) hw h2n_w h1n_w hconst₁₀ hvis₁₀ with
      ⟨s₁₁, t₁₁, hex₁₁, ht₁₁, hout₁₁⟩
    have hex_out : Exec w (mengerOutputRegProg 8 2) s₁₀ s₁₁ (1 + t₁₁) :=
      .ite_false hcond_out hex₁₁
    have hvalid := isValidDisjointPathsOutput_of_resCut x hsys₁₀.1 hcard_lt₁₀
      hpar₁₀.2.1 hclosed₁₀ hinit₁₀ hnoB₁₀ hout₁₁
    have htime :
        t₁ + (t₂ + (t₃ + (2 + (4 + (9 + (2 + (2 + (t₉ + (t₁₀ + (1 + t₁₁)))))))))) ≤ 450 * S := by
      have htot_le : totalAdjEntries (edgeNeighbors edges) = 2 * edges.length := htot_eq
      have hloop_le :
          x.k * (65 + 264 * x.n + 31 * totalAdjEntries (edgeNeighbors edges)) ≤
            x.k * (264 * (x.n + edges.length + 1)) := by
        rw [htot_le]
        apply Nat.mul_le_mul_left
        omega
      have hk_le : x.k * (x.n + edges.length + 1) ≤ S := by
        rw [hS_eq, Nat.add_mul, Nat.one_mul]
        omega
      have hk_nm_le : x.k * (264 * (x.n + edges.length + 1)) ≤ 264 * S := by
        rw [Nat.mul_left_comm x.k 264]
        omega
      omega
    refine ⟨s₁₁, _,
      .seq hex₁ (.seq hex₂ (.seq hex₃ (.seq hex₄ (.seq hex₅
        (.seq hex₆ (.seq hex₇ (.seq hex₈ (.seq hex₉ (.seq hex₁₀ hex_out))))))))),
      htime, hvalid, (by
        intro hh
        simp [hout₁₁] at hh), (by simp [hout₁₁]), ?_⟩
    have hhead : (s₁₁.arrs outArr).head? ≠ some 1 := by simp [hout₁₁]
    have hsep :
        (finsetOfBitList x.n (s₁₁.arrs outArr).tail).card < x.k ∧
        IsABSeparator x.G x.A x.B (finsetOfBitList x.n (s₁₁.arrs outArr).tail) := by
      simpa only [decDisjointPathsOut, hhead, ↓reduceIte, IsValidDisjointPathsOutput] using hvalid
    constructor
    · intro hh
      exact False.elim (hhead hh)
    · rintro ⟨P, hP, _⟩
      exact False.elim (Nat.not_le_of_gt hsep.1
        (card_le_of_disjoint_walks_and_separator P hP hsep.2))

end GraphMinor.Compute
