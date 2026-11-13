module

public import GraphMinor.Compute.Algorithm72Wall
public import GraphMinor.Compute.Specs13
import GraphMinor.Compute.Join13Adapter72
import GraphMinor.Compute.Algorithm41Aux20

/-!
# Graph Minors XIII, Algorithm (7.2) on the Word RAM

This file formalizes Statement (7.1) and Algorithm (7.2) from Robertson and Seymour,
*Graph Minors. XIII. The Disjoint Paths Problem*, J. Combin. Theory Ser. B **63** (1995), 65–110
(Section 7, page 89):

> **(7.1)** *For $h \ge 2$, even, if every graph with branch-width $\ge \omega/3$ has a minor
> isomorphic to the elementary wall of height $h$, then there is an algorithm as in (7.2), with
> running time $O(v^2 + \varepsilon)$.*
>
> **(7.2) Algorithm.**
> *Input:* A graph $G$.
> *Output:* Either a branch-decomposition of $G$ of width $\le \omega$, or a wall of height $h$
> which is a subgraph of $G$.
> *Description:* Given input $G$, we apply (4.4) to $G$ to determine if there is a model of the
> elementary wall of height $H$ in $G$ and to find one if one exists. If we find one, we construct
> from it a wall of height $h$ and stop. If there is none, then $G$ has branch-width $< \omega/3$.
> We apply (3.3) to $G$ and obtain a subgraph $G'$ of $G$ and a branch-decomposition of $G'$ of
> width $\le \omega$, such that either $G' = G$ or $G'$ has branch-width $\ge \omega/3$. Thus
> $G' = G$, and we have a branch-decomposition of $G$ of width $\le \omega$. We stop.
>
> This algorithm involves one application of (4.4) and one of (3.3); thus, it has running time
> $O(v^2 + \varepsilon)$. $\square$
-/

@[expose] public section

namespace GraphMinor.Compute

open SimpleGraph
open scoped BigOperators

/-! ### Section 1: Input, Output, and Step-by-Step Mathematical Claims of (7.1)–(7.2) -/

/-- Input to GM XIII Algorithm (7.2): a graph `G : MultiDigraph n` on `n` vertices. -/
structure Alg72Input where
  /-- Number of vertices `|V(G)|`. -/
  n : ℕ
  /-- The input graph `G` on `Fin n`. -/
  G : MultiDigraph n

/-- Problem size `v(G)² + ε(G) = (|V(G)| + 1)² + (|E(G)| + |V(G)| + 1)` for GM XIII (7.1)–(7.2)
(page 89: "with running time $O(v^2 + \varepsilon)$"). -/
def alg72Size (x : Alg72Input) : ℕ :=
  (x.n + 1) ^ 2 + (x.G.numEdges + x.n + 1)

/-- Flat Word RAM input encoding of `x : Alg72Input` in `inArr`: `x.G.enc`. -/
def encAlg72In (x : Alg72Input) : List ℕ :=
  x.G.enc

/-- Output specification of GM XIII Algorithm (7.2) (page 89:
"Either a branch-decomposition of $G$ of width $\le \omega$, or a wall of height $h$ which is a
subgraph of $G$"), parameterized by wall height `h` and branch-width parameter `ω₀` where
`ω = 3 * ω₀`:
either `out = 0 :: code` where `code` is a branch-decomposition `(T, τ)` of `x.G` of width
`≤ 3 * ω₀` written out in the flat `List ℕ` format (`IsValidBranchDecompCode (3 * ω₀) x.G code`),
or `out = 1 :: W.encList` for a valid wall `W : WallOfHeight h x.G` (`W.IsValid`) of height `h`
in `x.G` (which by `W.isWallIn_toGMWall` is a `GM13.Wall` of height `h` that is a wall in
`x.G.toGMDigraph.toGraph`). -/
def IsAlg72Output (h ω₀ : ℕ) (x : Alg72Input) (out : List ℕ) : Prop :=
  (∃ code : List ℕ, out = 0 :: code ∧ IsValidBranchDecompCode (3 * ω₀) x.G code) ∨
  (∃ W : WallOfHeight h x.G, W.IsValid ∧ out = 1 :: W.encList)

/-- For even `h ≥ 2`, any valid `W : WallOfHeight h x.G` in the second outcome of `IsAlg72Output`
gives a `GM13.Wall ℕ (ℕ × ℕ × ℕ)` of height `h` (`(W.toGMWall h2 he hW).height = h`) that is a wall in
`x.G.toGMDigraph.toGraph` (`GM13.IsWallIn x.G.toGMDigraph.toGraph (W.toGMWall h2 he hW)`). -/
theorem IsAlg72Output.wall_isWallIn_toGMWall {h : ℕ} (h2 : 2 ≤ h) (he : Even h)
    {x : Alg72Input} {W : WallOfHeight h x.G} (hW : W.IsValid) :
    (W.toGMWall h2 he hW).height = h ∧
    GM13.IsWallIn x.G.toGMDigraph.toGraph (W.toGMWall h2 he hW) :=
  ⟨rfl, W.isWallIn_toGMWall h2 he hW⟩

/-- Every valid `bdCode` satisfying `IsValidBranchDecompCode B G bdCode` has length at most
`2 + 3 * G.numEdges` and all words at most `2 * G.numEdges`. -/
theorem IsValidBranchDecompCode.length_and_words_le {B n : ℕ} {G : MultiDigraph n}
    {bdCode : List ℕ} (h : IsValidBranchDecompCode B G bdCode) :
    bdCode.length ≤ 2 + 3 * G.numEdges ∧ ∀ x ∈ bdCode, x ≤ 2 * G.numEdges := by
  rcases h with ⟨hm, ht_le, hlen, hcase⟩
  refine ⟨by omega, fun x hx => ?_⟩
  rcases List.mem_iff_getElem.mp hx with ⟨i, hi, rfl⟩
  have hgetD : bdCode.getD i 0 = bdCode[i]'hi := by simp [List.getD, hi]
  rw [← hgetD]
  by_cases hi0 : i = 0
  · subst hi0
    change bdNumTreeVerts bdCode ≤ 2 * G.numEdges
    omega
  · by_cases hi1 : i = 1
    · subst hi1
      change bdNumGraphEdges bdCode ≤ 2 * G.numEdges
      omega
    · rcases hcase with ⟨_, ht0, hzero⟩ | ⟨_, ht, hp0, hp, htau, _⟩
      · have hi_eq : i = 2 + (i - 2) := by omega
        have hik : i - 2 < bdNumGraphEdges bdCode := by omega
        rw [hi_eq, hzero (i - 2) hik]
        omega
      · by_cases hit : i < 2 + bdNumTreeVerts bdCode
        · by_cases hi2 : i = 2
          · subst hi2; rw [hp0]; omega
          · have hz_pos : 0 < i - 2 := by omega
            have hz_lt : i - 2 < bdNumTreeVerts bdCode := by omega
            have hlt := hp (i - 2) hz_pos hz_lt
            unfold bdParent at hlt
            have hi_eq : 2 + (i - 2) = i := by omega
            rw [hi_eq] at hlt
            omega
        · have he_lt : i - (2 + bdNumTreeVerts bdCode) < G.numEdges := by omega
          have hlt := htau ⟨i - (2 + bdNumTreeVerts bdCode), he_lt⟩
          have hi_eq : 2 + bdNumTreeVerts bdCode + (i - (2 + bdNumTreeVerts bdCode)) = i := by omega
          dsimp only at hlt
          rw [hi_eq] at hlt
          omega

/-- Every edge multiplicity `G.edgeMult u v` is bounded by the total number of edges `G.numEdges`. -/
theorem edgeMult_le_numEdges {n : ℕ} (G : MultiDigraph n) (u v : Fin n) :
    G.edgeMult u v ≤ G.numEdges := by
  unfold MultiDigraph.numEdges
  refine le_trans
    (Finset.single_le_sum (f := fun v' => G.edgeMult u v')
      (fun v' _ => Nat.zero_le _) (Finset.mem_univ v)) ?_
  exact Finset.single_le_sum (f := fun u' => ∑ v', G.edgeMult u' v')
    (fun u' _ => Nat.zero_le _) (Finset.mem_univ u)

/-- **GM XIII (7.2), Step (1) Branch-Width Claim (page 89)**:
"If there is none, then $G$ has branch-width $< \omega/3$." -/
theorem lemma_7_2_not_hasBranchWidthGe {h n ω₀ : ℕ}
    (h71 : HasPlanarGridThreshold (elemWallEdges h) ω₀)
    {G : MultiDigraph n}
    (hnoG : ¬ HasDigraphModel (elemWallEdges h) G) :
    ¬ HasBranchWidthGe G ω₀ :=
  fun hbw => hnoG (h71 G hbw)

/-- **GM XIII (7.2), Step (2) Subgraph Equality Claim (page 89)**:
"We apply (3.3) to $G$ and obtain a subgraph $G'$ of $G$ and a branch-decomposition of $G'$ of
width $\le \omega$, such that either $G' = G$ or $G'$ has branch-width $\ge \omega/3$. Thus
$G' = G$, and we have a branch-decomposition of $G$ of width $\le \omega$." -/
theorem lemma_7_2_eq_G {h n ω₀ : ℕ}
    (h71 : HasPlanarGridThreshold (elemWallEdges h) ω₀)
    {G G' : MultiDigraph n}
    (hnoG : ¬ HasDigraphModel (elemWallEdges h) G)
    (hle : G' ≤ G)
    (hor : G' = G ∨ HasBranchWidthGe G' ω₀) :
    G' = G := by
  rcases hor with hEq | hbw
  · exact hEq
  · exfalso
    exact hnoG (hasDigraphModel_mono hle (h71 G' hbw))

/-- **GM XIII (7.2), Step (2) Branch-Decomposition Conclusion (page 89)**:
When Algorithm (4.4) reports no model of the elementary wall of height `h` in `G`, the
branch-decomposition `bdCode` output by Algorithm (3.3) on `G` satisfies
`IsAlg72Output h ω₀ ⟨n, G⟩ (0 :: bdCode)`. -/
theorem lemma_7_2_branch_decomp_out {h n ω₀ : ℕ}
    (h71 : HasPlanarGridThreshold (elemWallEdges h) ω₀)
    {G G' : MultiDigraph n} {bdCode : List ℕ}
    (hnoG : ¬ HasDigraphModel (elemWallEdges h) G)
    (hle : G' ≤ G)
    (hbd : IsValidBranchDecompCode (3 * ω₀) G' bdCode)
    (hor : G' = G ∨ HasBranchWidthGe G' ω₀) :
    IsAlg72Output h ω₀ ⟨n, G⟩ (0 :: bdCode) := by
  have hEq : G' = G := lemma_7_2_eq_G h71 hnoG hle hor
  subst hEq
  exact Or.inl ⟨bdCode, rfl, hbd⟩

/-! ### Section 2: Word RAM Program `alg72Prog` and Execution Proof -/

/-- Prepend a leading `0` word to array `a_src` into `a_dst`, using registers `r_base .. r_base + 4`. -/
def prependZeroProg (a_src a_dst : Arr) (r_base : Reg) : Cmd :=
  .seq (.assign r_base (.len a_src))
    (.seq (.alloc a_dst (.op .add (.reg r_base) (.const 1)))
      (.seq (.write a_dst (.const 0) (.const 0))
        (.seq (.assign (r_base + 1) (.const 0))
          (.seq (.assign (r_base + 2) (.const 1))
            (bufAppendSlice a_src a_dst (r_base + 1) (r_base + 2)
              r_base (r_base + 3) (r_base + 4))))))

theorem prependZeroProg_exec {w : ℕ} (a_src a_dst r_base : ℕ)
    (hne : a_src ≠ a_dst)
    (hw : 1 < 2 ^ w)
    (code : List ℕ)
    (hlen_w : code.length + 1 < 2 ^ w)
    (hcode_w : ∀ x ∈ code, x < 2 ^ w)
    {s : State}
    (hsrc : s.arrs a_src = code) :
    ∃ s' t,
      Exec w (prependZeroProg a_src a_dst r_base) s s' t ∧
      t ≤ 20 + 20 * code.length ∧
      s'.arrs a_dst = 0 :: code ∧
      (∀ a : ℕ, a ≠ a_dst → s'.arrs a = s.arrs a) ∧
      (∀ r < r_base, s'.regs r = s.regs r) := by
  have h0_w : 0 < 2 ^ w := by omega
  have hlen0_w : code.length < 2 ^ w := by omega
  let s₁ := s.setReg r_base code.length
  have hex₁ : Exec w (.assign r_base (.len a_src)) s s₁ 2 :=
    .assign (by simp [Expr.eval, checkWord, hsrc, hlen0_w])
  let s₂ := s₁.setArr a_dst (List.replicate (code.length + 1) 0)
  have hex₂ : Exec w (.alloc a_dst (.op .add (.reg r_base) (.const 1))) s₁ s₂
      (3 + (code.length + 1)) :=
    .alloc (by simp [s₁, Expr.eval, BinOp.eval, BinOp.raw, checkWord, hlen0_w, hw, hlen_w])
  let s₃ := s₂.writeArr a_dst 0 0
  have hex₃ : Exec w (.write a_dst (.const 0) (.const 0)) s₂ s₃ 3 :=
    .write (by simp [Expr.eval, checkWord, h0_w])
      (by simp [Expr.eval, checkWord, h0_w])
      (by simp [s₂])
  let s₄ := s₃.setReg (r_base + 1) 0
  have hex₄ : Exec w (.assign (r_base + 1) (.const 0)) s₃ s₄ 2 :=
    .assign (by simp [Expr.eval, checkWord, h0_w])
  let s₅ := s₄.setReg (r_base + 2) 1
  have hex₅ : Exec w (.assign (r_base + 2) (.const 1)) s₄ s₅ 2 :=
    .assign (by simp [Expr.eval, checkWord, hw])
  have hsrc₅ : s₅.arrs a_src = ([] : List ℕ) ++ code ++ [] := by
    simp [s₅, s₄, s₃, State.writeArr, s₂, State.setArr_arrs_ne _ _ hne, s₁, hsrc]
  have hdst₅ : s₅.arrs a_dst = [0] ++ List.replicate (code.length + 0) 0 := by
    simp [s₅, s₄, s₃, State.writeArr, s₂, List.replicate_succ]
  rcases bufAppendSlice_exec a_src a_dst (r_base + 1) (r_base + 2) r_base (r_base + 3) (r_base + 4)
      hne (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
      (by omega) (by omega) (by omega) hw
      [] code [] [0] 0 rfl rfl (by simp; omega) (by simp; omega) hcode_w (s := s₅)
      hsrc₅ hdst₅ (by simp [s₅, s₄]) (by simp [s₅]) (by simp [s₅, s₄, s₃, s₂, s₁]) with
    ⟨s', t₆, hex₆, ht₆, hdst', _, harr', hreg'⟩
  refine ⟨s', 2 + ((3 + (code.length + 1)) + (3 + (2 + (2 + t₆)))),
    .seq hex₁ (.seq hex₂ (.seq hex₃ (.seq hex₄ (.seq hex₅ hex₆)))),
    by omega,
    by simpa using hdst',
    fun a ha => by
      rw [harr' a ha]
      simp [s₅, s₄, s₃, State.writeArr, s₂, State.setArr_arrs_ne _ _ ha, s₁],
    fun r hr => by
      rw [hreg' r (by omega) (by omega) (by omega)]
      simp [s₅, s₄, s₃, s₂, s₁,
        show r ≠ r_base + 2 by omega, show r ≠ r_base + 1 by omega, show r ≠ r_base by omega]⟩

/-- Word RAM program for GM XIII Algorithm (7.2) (page 89):
* **Step (1):** Directly calls our
  `alg44Prog (elemWallNumVerts h) (elemWallEdges h) a_in a_out a_scratch r_base P33_44 P41_44`
  to decide whether `G` has a model of the elementary wall of height `h`, writing `[1] ++ M.enc` or
  `[0]` to `a_out`.
* **Step (2):** Reads the decision flag `a_out[0]` into `r_base`.
  - If `r_base = 1` ("If we find one, we construct from it a wall of height $h$ and stop", page 89),
    calls `modelToWallProg h hh a_in a_out a_scratch r_base` to construct a valid
    `W : WallOfHeight h G` (`W.IsValid`) from `M` and write `[1] ++ W.encList` (`1 :: W.encList`)
    to `a_out`.
  - Otherwise (`r_base = 0`), calls `P33_G` (Algorithm (3.3) on `G`, writing `bdCode` to
    `a_scratch + 8`) followed by `prependZeroProg (a_scratch + 8) a_out r_base` to write
    `0 :: bdCode` into `a_out`. -/
noncomputable def alg72Prog (h : ℕ) (hh : 1 ≤ h) (a_in a_out a_scratch r_base : ℕ)
    (P33_44 P41_44 P33_G : Cmd) : Cmd :=
  .seq (alg44Prog (elemWallNumVerts h) (elemWallEdges h) a_in a_out a_scratch r_base P33_44 P41_44)
    (.seq (.assign r_base (.read a_out (.const 0)))
      (.ite (.op .eq (.reg r_base) (.const 1))
        (modelToWallProg h hh a_in a_out a_scratch r_base)
        (.seq P33_G (prependZeroProg (a_scratch + 8) a_out r_base))))

/-- Time bound multiplier for `alg72Prog`. -/
def alg72TimeConst (h C₄₄ C₃₃ : ℕ) : ℕ :=
  let p := elemWallNumVerts h
  let m := (elemWallEdges h).length
  C₄₄ + C₃₃ + 310 + 300 * p + 100 * m

/-- Word-size constant for `alg72Prog`. -/
def alg72WordConst (h ω₀ c_w44 c_w33 : ℕ) : ℕ :=
  let p := elemWallNumVerts h
  let m := (elemWallEdges h).length
  c_w44 + c_w33 + 3 * ω₀ + 10 + 2 * p + 3 * m

theorem alg72_word_bounds {h ω₀ c_w44 c_w33 n m_act e pow_w : ℕ}
    (hm_act : m_act ≤ n * n)
    (hprod : alg72WordConst h ω₀ c_w44 c_w33 * ((n + 1) ^ 2 + (e + n + 1)) < pow_w) :
    3 < pow_w ∧
    3 * ω₀ < pow_w ∧
    3 + 3 * e < pow_w ∧
    2 + 3 * m_act < pow_w ∧
    n * n < pow_w ∧
    3 + 2 * (elemWallEdges h).length + elemWallNumVerts h * n < pow_w ∧
    4 + elemWallNumVerts h + (elemWallEdges h).length +
      2 * (elemWallEdges h).length * n < pow_w := by
  unfold alg72WordConst at hprod
  dsimp only at hprod
  generalize (elemWallEdges h).length = m at hprod ⊢
  generalize elemWallNumVerts h = p at hprod ⊢
  let S := (n + 1) ^ 2 + (e + n + 1)
  change (c_w44 + c_w33 + 3 * ω₀ + 10 + 2 * p + 3 * m) * S < pow_w at hprod
  have hsq : (n + 1) ^ 2 = n * n + 2 * n + 1 := by ring
  have h1 : 1 ≤ S := by dsimp [S]; omega
  have he : e + 1 ≤ S := by dsimp [S]; omega
  have hnn : n * n + 1 ≤ S := by dsimp [S]; omega
  have hn : n + 1 ≤ S := by dsimp [S]; omega
  have hexp :
      (c_w44 + c_w33 + 3 * ω₀ + 10 + 2 * p + 3 * m) * S =
        (c_w44 + c_w33) * S + (3 * ω₀) * S + 10 * S + 2 * (p * S) + 3 * (m * S) := by ring
  have h_w : 3 * ω₀ ≤ (3 * ω₀) * S := Nat.le_mul_of_pos_right _ (by omega)
  have h_p : p + p * n ≤ p * S := by
    have : p + p * n = p * (1 + n) := by ring
    have : p * (1 + n) ≤ p * S := Nat.mul_le_mul_left p (by omega)
    omega
  have h_m : m + m * n ≤ m * S := by
    have : m + m * n = m * (1 + n) := by ring
    have : m * (1 + n) ≤ m * S := Nat.mul_le_mul_left m (by omega)
    omega
  have h_2mn : 2 * m * n = 2 * (m * n) := by ring
  refine ⟨by omega, by omega, by omega, by omega, by omega, by omega, by omega⟩

theorem alg72_time_bound_true {h C₄₄ C₃₃ n m_act e t₁ t_wall : ℕ}
    (hm_act : m_act ≤ n * n)
    (ht₁ : t₁ ≤ C₄₄ * (n + 1) ^ 2)
    (ht_wall : t_wall ≤ modelToWallTime h n m_act) :
    t₁ + (3 + (3 + t_wall)) ≤ alg72TimeConst h C₄₄ C₃₃ * ((n + 1) ^ 2 + (e + n + 1)) := by
  unfold alg72TimeConst
  dsimp only
  unfold modelToWallTime at ht_wall
  dsimp only at ht_wall
  generalize (elemWallEdges h).length = m at ht_wall ⊢
  generalize elemWallNumVerts h = p at ht_wall ⊢
  let S := (n + 1) ^ 2 + (e + n + 1)
  change t₁ + (3 + (3 + t_wall)) ≤ (C₄₄ + C₃₃ + 310 + 300 * p + 100 * m) * S
  have hsq : (n + 1) ^ 2 = n * n + 2 * n + 1 := by ring
  have hS_ge : (n + 1) ^ 2 ≤ S := by dsimp [S]; omega
  have ht1_S : t₁ ≤ C₄₄ * S := le_trans ht₁ (Nat.mul_le_mul_left C₄₄ hS_ge)
  have hp_term : 62 * p + 21 * p * n + (215 + 264 * n + 43 * n * n) * p ≤ 300 * p * S := by
    have h_in : 62 + 21 * n + (215 + 264 * n + 43 * n * n) ≤ 300 * S := by
      have : 43 * n * n = 43 * (n * n) := by ring
      have : 300 * (n + 1) ^ 2 = 300 * (n * n) + 600 * n + 300 := by ring
      have : 300 * (n + 1) ^ 2 ≤ 300 * S := Nat.mul_le_mul_left 300 hS_ge
      omega
    have h_lhs : 62 * p + 21 * p * n + (215 + 264 * n + 43 * n * n) * p =
        p * (62 + 21 * n + (215 + 264 * n + 43 * n * n)) := by ring
    have h_rhs : 300 * p * S = p * (300 * S) := by ring
    rw [h_lhs, h_rhs]
    exact Nat.mul_le_mul_left p h_in
  have hm_term : 88 * m + 80 * m * n ≤ 100 * m * S := by
    have h_in : 88 + 80 * n ≤ 100 * S := by
      have : 100 * (n + 1) ^ 2 = 100 * (n * n) + 200 * n + 100 := by ring
      have : 100 * (n + 1) ^ 2 ≤ 100 * S := Nat.mul_le_mul_left 100 hS_ge
      omega
    have h_lhs : 88 * m + 80 * m * n = m * (88 + 80 * n) := by ring
    have h_rhs : 100 * m * S = m * (100 * S) := by ring
    rw [h_lhs, h_rhs]
    exact Nat.mul_le_mul_left m h_in
  have h_wall_split :
      260 + 62 * p + 88 * m + (21 * p + 80 * m) * n + n * n + 40 * m_act +
        (215 + 264 * n + 43 * n * n) * p =
        (260 + n * n + 40 * m_act) +
          (62 * p + 21 * p * n + (215 + 264 * n + 43 * n * n) * p) +
          (88 * m + 80 * m * n) := by ring
  have h_const : 6 + (260 + n * n + 40 * m_act) ≤ 310 * S := by
    have : 310 * (n + 1) ^ 2 = 310 * (n * n) + 620 * n + 310 := by ring
    have : 310 * (n + 1) ^ 2 ≤ 310 * S := Nat.mul_le_mul_left 310 hS_ge
    omega
  have h_rhs_split :
      (C₄₄ + C₃₃ + 310 + 300 * p + 100 * m) * S =
        C₄₄ * S + C₃₃ * S + 310 * S + 300 * p * S + 100 * m * S := by ring
  omega

theorem alg72_time_bound_false {h C₄₄ C₃₃ n e t₁ t₂ t_prep : ℕ}
    (ht₁ : t₁ ≤ C₄₄ * (n + 1) ^ 2)
    (ht₂ : t₂ ≤ C₃₃ * ((n + 1) ^ 2 + (e + n + 1)))
    (ht_prep : t_prep ≤ 60 + 60 * e) :
    t₁ + (3 + (3 + (t₂ + t_prep))) ≤ alg72TimeConst h C₄₄ C₃₃ * ((n + 1) ^ 2 + (e + n + 1)) := by
  unfold alg72TimeConst
  dsimp only
  generalize (elemWallEdges h).length = m
  generalize elemWallNumVerts h = p
  let S := (n + 1) ^ 2 + (e + n + 1)
  change t₂ ≤ C₃₃ * S at ht₂
  change t₁ + (3 + (3 + (t₂ + t_prep))) ≤ (C₄₄ + C₃₃ + 310 + 300 * p + 100 * m) * S
  have hS_ge : (n + 1) ^ 2 ≤ S := by dsimp [S]; omega
  have he : e + 1 ≤ S := by dsimp [S]; omega
  have ht1_S : t₁ ≤ C₄₄ * S := le_trans ht₁ (Nat.mul_le_mul_left C₄₄ hS_ge)
  have h_rhs_split :
      (C₄₄ + C₃₃ + 310 + 300 * p + 100 * m) * S =
        C₄₄ * S + C₃₃ * S + 310 * S + (300 * p + 100 * m) * S := by ring
  have h_310 : 6 + t_prep ≤ 310 * S := by omega
  omega

/-- General execution theorem for `alg72Prog` on arbitrary input, output and scratch arrays. -/
theorem alg72Prog_exec (h ω₀ : ℕ) (hh : 1 ≤ h) (hω₀ : 2 ≤ ω₀)
    (h71 : HasPlanarGridThreshold (elemWallEdges h) ω₀)
    (a_in a_out a_scratch a_base r_base : ℕ)
    (P33_44 P41_44 P33_G : Cmd)
    (hP33_44 : Alg33Spec ω₀ (a_scratch + 1) (a_scratch + 2) (a_scratch + 3) a_base r_base P33_44)
    (hP41_44 : Alg41Spec 0 ((elemWallEdges h).length + elemWallNumVerts h) (3 * ω₀)
      (a_scratch + 2) (a_scratch + 4) (a_scratch + 3) (a_scratch + 5) (a_scratch + 6)
      a_base r_base P41_44)
    (hP33_G : Alg33Spec ω₀ a_in (a_scratch + 7) (a_scratch + 8) a_base r_base P33_G)
    (ha_in_out : a_in ≠ a_out)
    (ha_in_lt : a_in < a_scratch)
    (ha_out_lt : a_out < a_scratch)
    (ha_sc_lt : a_scratch + 8 < a_base) :
    ∃ (C₇₂ c_w : ℕ), 0 < C₇₂ ∧ 0 < c_w ∧
      ∀ (n : ℕ) (G : MultiDigraph n) (w : ℕ),
        wordSize c_w ((n + 1) ^ 2 + (G.numEdges + n + 1)) ≤ w →
        ∀ (s : State),
          s.arrs a_in = G.enc →
          ∃ (s' : State) (t : ℕ),
            Exec w (alg72Prog h hh a_in a_out a_scratch r_base P33_44 P41_44 P33_G) s s' t ∧
            t ≤ C₇₂ * ((n + 1) ^ 2 + (G.numEdges + n + 1)) ∧
            IsAlg72Output h ω₀ ⟨n, G⟩ (s'.arrs a_out) ∧
            (∀ r < r_base, s'.regs r = s.regs r) ∧
            (∀ a < a_scratch, a ≠ a_out → s'.arrs a = s.arrs a) := by
  rcases alg44Prog_exec (elemWallEdges h) ω₀ hω₀ h71 a_in a_out a_scratch a_base r_base
      P33_44 P41_44 hP33_44 hP41_44 (by omega) (Or.inl ha_out_lt) (by omega) with
    ⟨C₄₄, c_w44, hC44_pos, hcw44_pos, h44_exec⟩
  rcases hP33_G with ⟨C₃₃, c_w33, hC33_pos, hcw33_pos, h33_exec⟩
  let C₇₂ := alg72TimeConst h C₄₄ C₃₃
  let c_w := alg72WordConst h ω₀ c_w44 c_w33
  have hC72_pos : 0 < C₇₂ := by unfold C₇₂ alg72TimeConst; dsimp only; omega
  have hcw_pos : 0 < c_w := by unfold c_w alg72WordConst; dsimp only; omega
  refine ⟨C₇₂, c_w, hC72_pos, hcw_pos, fun n G w hw s hin => ?_⟩
  have h_prod_lt : c_w * ((n + 1) ^ 2 + (G.numEdges + n + 1)) < 2 ^ w :=
    mul_lt_two_pow_of_wordSize_le hcw_pos hw
  have hm_act_le : G.numActivePairs ≤ n * n := G.numActivePairs_le_sq
  rcases alg72_word_bounds hm_act_le h_prod_lt with
    ⟨hw3, h3ω_w, he_w, hG_w, hnn_w, henc_w, hbuf_w⟩
  have hw0 : 0 < 2 ^ w := by omega
  have hw1 : 1 < 2 ^ w := by omega
  -- Step (1): Execute alg44Prog on G:
  have hw_44 : wordSize c_w44 ((n + 1) ^ 2) ≤ w := by
    refine le_trans (wordSize_mono_left (c₂ := c_w) (by unfold c_w alg72WordConst; dsimp only; omega) _) ?_
    exact le_trans (wordSize_mono_right c_w (by omega)) hw
  rcases h44_exec n G w hw_44 s hin with
    ⟨s₁, t₁, hex₁, ht₁, h44_out, hreg₁, harr₁⟩
  have ha_in_s1 : s₁.arrs a_in = G.enc := by
    rw [harr₁ a_in ha_in_lt ha_in_out, hin]
  -- Case split on the output of alg44Prog:
  rcases h44_out with ⟨M, hM_valid, hout_M⟩ | ⟨hnoG, hout_0⟩
  · -- Case 1: alg44Prog found a model M of the elementary wall of height h in G:
    have hlen_pos : 0 < (s₁.arrs a_out).length := by simp [hout_M]
    have hget0 : (s₁.arrs a_out)[0]'hlen_pos = 1 := by simp [hout_M]
    have heval_rd : (Expr.read a_out (.const 0)).eval w s₁ = some 1 := by
      simp [Expr.eval, checkWord, hw0, hw1, hlen_pos, hget0]
    let s₂ := s₁.setReg r_base 1
    have hex_rd : Exec w (.assign r_base (.read a_out (.const 0))) s₁ s₂ 3 := .assign heval_rd
    have hcond : (Expr.op .eq (.reg r_base) (.const 1)).eval w s₂ = some 1 := by
      simp [s₂, Expr.eval, BinOp.eval, BinOp.raw, checkWord, hw1]
    have ha_in_s2 : s₂.arrs a_in = G.enc := by simpa [s₂] using ha_in_s1
    have hout_s2 : s₂.arrs a_out = [1] ++ M.enc := by simpa [s₂] using hout_M
    rcases modelToWallProg_exec hh G M hM_valid a_in a_out a_scratch r_base
        ha_in_lt ha_out_lt ha_in_out hw3 hG_w hnn_w henc_w hbuf_w
        ha_in_s2 hout_s2 with
      ⟨s₃, t_wall, hex_wall, ht_wall, hW_valid, hout_wall, harr_wall, hreg_wall⟩
    have hex_ite :
        Exec w (.ite (.op .eq (.reg r_base) (.const 1))
          (modelToWallProg h hh a_in a_out a_scratch r_base)
          (.seq P33_G (prependZeroProg (a_scratch + 8) a_out r_base))) s₂ s₃ (3 + t_wall) :=
      .ite_true hcond (by omega) hex_wall
    refine ⟨s₃, t₁ + (3 + (3 + t_wall)), .seq hex₁ (.seq hex_rd hex_ite),
      alg72_time_bound_true hm_act_le ht₁ ht_wall,
      Or.inr ⟨modelToWall hh M, hW_valid, hout_wall⟩, ?_, ?_⟩
    · intro r hr
      have hr_ne : (r : Reg) ≠ r_base := by omega
      rw [hreg_wall r hr]
      simp [s₂, hr_ne, hreg₁ r hr]
    · intro a ha ha_out
      rw [harr_wall a ha ha_out]
      simpa [s₂] using harr₁ a ha ha_out
  · -- Case 2: alg44Prog reported no model of the elementary wall of height h in G:
    have hlen_pos : 0 < (s₁.arrs a_out).length := by simp [hout_0]
    have hget0 : (s₁.arrs a_out)[0]'hlen_pos = 0 := by simp [hout_0]
    have heval_rd : (Expr.read a_out (.const 0)).eval w s₁ = some 0 := by
      simp [Expr.eval, checkWord, hw0, hlen_pos, hget0]
    let s₂ := s₁.setReg r_base 0
    have hex_rd : Exec w (.assign r_base (.read a_out (.const 0))) s₁ s₂ 3 := .assign heval_rd
    have hcond : (Expr.op .eq (.reg r_base) (.const 1)).eval w s₂ = some 0 := by
      simp [s₂, Expr.eval, BinOp.eval, BinOp.raw, checkWord, hw0, hw1]
    have hw_33 : wordSize c_w33 ((n + 1) ^ 2 + G.numEdges) ≤ w := by
      refine le_trans (wordSize_mono_left (c₂ := c_w) (by unfold c_w alg72WordConst; dsimp only; omega) _) ?_
      exact le_trans (wordSize_mono_right c_w (by omega)) hw
    have hmult_w : ∀ pair ∈ G.activePairsList, G.edgeMult pair.1 pair.2 < 2 ^ w := by
      intro pair _
      have hle : G.edgeMult pair.1 pair.2 ≤ G.numEdges := edgeMult_le_numEdges G pair.1 pair.2
      have h1_le_c : 1 ≤ c_w := hcw_pos
      have h_e_lt : G.numEdges < c_w * ((n + 1) ^ 2 + (G.numEdges + n + 1)) := by nlinarith
      omega
    have ha_in_s2 : s₂.arrs a_in = G.enc := by simpa [s₂] using ha_in_s1
    rcases h33_exec n G w hw_33 h3ω_w hmult_w s₂ ha_in_s2 with
      ⟨s₃, t₂, G', bdCode, hex_33, ht₂, hG'_le, hG'_bd, hG'_or_raw, _, ha_bd, _, hreg₃, harr₃⟩
    have hG'_or : G' = G ∨ HasBranchWidthGe G' ω₀ := by
      rcases hG'_or_raw with rfl | ⟨_, hhigh⟩
      · exact Or.inl rfl
      · exact Or.inr (isAlg33HighWidthCase_imp_hasBranchWidthGe hω₀ hhigh)
    have hEq : G' = G := lemma_7_2_eq_G h71 hnoG hG'_le hG'_or
    rw [hEq] at hG'_bd
    rcases hG'_bd.length_and_words_le with ⟨hbd_len, hbd_words⟩
    have hbd_len_w : bdCode.length + 1 < 2 ^ w := by omega
    have hbd_code_w : ∀ x ∈ bdCode, x < 2 ^ w := by
      intro x hx
      have := hbd_words x hx
      omega
    rcases prependZeroProg_exec (a_scratch + 8) a_out r_base (by omega) hw1
        bdCode hbd_len_w hbd_code_w ha_bd with
      ⟨s₄, t_prep, hex_prep, ht_prep, hout_s4, harr_prep, hreg_prep⟩
    have hex_ite :
        Exec w (.ite (.op .eq (.reg r_base) (.const 1))
          (modelToWallProg h hh a_in a_out a_scratch r_base)
          (.seq P33_G (prependZeroProg (a_scratch + 8) a_out r_base))) s₂ s₄
          (3 + (t₂ + t_prep)) :=
      .ite_false hcond (.seq hex_33 hex_prep)
    have hout_72 : IsAlg72Output h ω₀ ⟨n, G⟩ (s₄.arrs a_out) := by
      rw [hout_s4]
      exact Or.inl ⟨bdCode, rfl, hG'_bd⟩
    refine ⟨s₄, t₁ + (3 + (3 + (t₂ + t_prep))), .seq hex₁ (.seq hex_rd hex_ite),
      alg72_time_bound_false ht₁ ht₂ (by omega), hout_72, ?_, ?_⟩
    · intro r hr
      have hr_ne : (r : Reg) ≠ r_base := by omega
      rw [hreg_prep r hr, hreg₃ r hr]
      simp [s₂, hr_ne, hreg₁ r hr]
    · intro a ha ha_out
      have ha_lt_base : a < a_base := by omega
      rw [harr_prep a ha_out, harr₃ a ha_lt_base (by omega) (by omega)]
      simpa [s₂] using harr₁ a ha ha_out

/-- **GM XIII (7.1)–(7.2) Algorithm (page 89)**:
For `h ≥ 1` and branch-width threshold `ω₀ ≥ 2` (`ω = 3 * ω₀`) such that every graph with
branch-width `≥ ω₀` has a minor isomorphic to the elementary wall of height `h`
(`HasPlanarGridThreshold (elemWallEdges h) ω₀`), given subroutines `P33_44`, `P41_44`, and `P33_G`
implementing Algorithms (3.3) and (4.1), `alg72Prog` outputs either a branch-decomposition `(T, τ)`
of `G` of width `≤ 3 * ω₀` written out as `0 :: code` in `outArr` or a wall
`W : WallOfHeight h G` (`W.IsValid`) of height `h` which is a subgraph of `G`, written out as
`[1] ++ W.encList` (`1 :: W.encList`) in `outArr`, in running time `O(v² + ε)`. -/
theorem algorithm_7_2_from_specs (h ω₀ : ℕ) (hh : 1 ≤ h) (hω₀ : 2 ≤ ω₀)
    (h71 : HasPlanarGridThreshold (elemWallEdges h) ω₀)
    (P33_44 P41_44 P33_G : Cmd)
    (hP33_44 : Alg33Spec ω₀ 11 12 13 20 10 P33_44)
    (hP41_44 : Alg41Spec 0 ((elemWallEdges h).length + elemWallNumVerts h) (3 * ω₀)
      12 14 13 15 16 20 10 P41_44)
    (hP33_G : Alg33Spec ω₀ inArr 17 18 20 10 P33_G) :
    ComputesArrRelInTime alg72Size encAlg72In (IsAlg72Output h ω₀)
      (alg72Prog h hh inArr outArr 10 10 P33_44 P41_44 P33_G) (fun m => m) := by
  rcases alg72Prog_exec h ω₀ hh hω₀ h71 inArr outArr 10 20 10 P33_44 P41_44 P33_G
      hP33_44 hP41_44 hP33_G (by decide) (by decide) (by decide) (by decide) with
    ⟨C₇₂, c_w, hC72, hcw, hexec⟩
  refine ⟨C₇₂, c_w, hC72, hcw, fun x s hin => ?_⟩
  rcases hexec x.n x.G (wordSize c_w (alg72Size x)) (le_refl _) s hin with
    ⟨s', t, hex, ht, hout, _⟩
  exact ⟨s', t, hex, ht, hout⟩

/-- **GM XIII (7.1)–(7.2) Algorithm joined with `gm13_algorithm_3_3` (`Join433.lean`),
`GM13.theorem_4_2_proof`, and `GM13.isPlanarGraph_elementaryWall` (`Join413.lean`) (page 89)**:
"(7.1) *For $h \ge 2$, even, if every graph with branch-width $\ge \omega/3$ has a minor
isomorphic to the elementary wall of height $h$, then there is an algorithm as in (7.2), with
running time $O(v^2 + \varepsilon)$.*
(7.2) Algorithm.
*Input:* A graph $G$.
*Output:* Either a branch-decomposition of $G$ of width $\le \omega$, or a wall of height $h$
which is a subgraph of $G$." -/
theorem gm13_algorithm_7_2 (h : ℕ) (hh : 2 ≤ h) (_he : Even h)
    :
    ∃ (ω₀ : ℕ) (P72 : Cmd),
      2 ≤ ω₀ ∧
      ComputesArrRelInTime alg72Size encAlg72In (IsAlg72Output h ω₀) P72 (fun m => m) := by
  rcases exists_elemWall_planarGridThreshold h with ⟨ω₀, hω₀, h71⟩
  rcases alg41Spec72_of_claim41
      (fun δ ξ B => ⟨alg41CoreProg δ ξ B, algorithm_4_1_core δ ξ B⟩)
      ((elemWallEdges h).length + elemWallNumVerts h) (3 * ω₀) with ⟨P41_44, hP41_44⟩
  have hP33_44 : Alg33Spec ω₀ 11 12 13 20 10 (alg33MultiProg ω₀ 11 12 13 20 10) :=
    alg33Spec_of_algorithm_3_3 ω₀ hω₀ 11 12 13 20 10
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  have hP33_G : Alg33Spec ω₀ inArr 17 18 20 10 (alg33MultiProg ω₀ inArr 17 18 20 10) :=
    alg33Spec_of_algorithm_3_3 ω₀ hω₀ inArr 17 18 20 10
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  refine ⟨ω₀,
    alg72Prog h (by omega) inArr outArr 10 10
      (alg33MultiProg ω₀ 11 12 13 20 10) P41_44 (alg33MultiProg ω₀ inArr 17 18 20 10),
    hω₀,
    algorithm_7_2_from_specs h ω₀ (by omega) hω₀ h71 _ P41_44 _ hP33_44 hP41_44 hP33_G⟩

/-- **Proof of `Algorithm72Statement` (`Specs13.lean`) from `gm13_algorithm_7_2`:** -/
theorem algorithm_7_2_statement : Algorithm72Statement := by
  intro h hh he
  rcases gm13_algorithm_7_2 h hh he with ⟨ω₀, P72, _, C, c, hC, hc, hexec⟩
  refine ⟨3 * ω₀, P72, C, c, hC, hc, fun x s hin => ?_⟩
  have hsize_eq : algorithm72Size x = alg72Size ⟨x.n, x.G⟩ := by
    unfold algorithm72Size alg72Size
    dsimp only
    omega
  rw [hsize_eq]
  exact hexec ⟨x.n, x.G⟩ s hin

end GraphMinor.Compute
