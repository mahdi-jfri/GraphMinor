module

public import GraphMinor.Compute.Algorithm44ModelBridge
public import GraphMinor.Compute.Algorithm44BranchWidth
public import GraphMinor.Compute.Join413
public import GraphMinor.Compute.Join433
public import GraphMinor.Compute.Join441
import GraphMinor.Compute.Join13Adapter72
import GraphMinor.Compute.Algorithm41Aux20

/-!
# Graph Minors XIII, Algorithm (4.4) on the Word RAM

This file formalizes Algorithm (4.4) from Robertson and Seymour, *Graph Minors. XIII. The Disjoint
Paths Problem*, J. Combin. Theory Ser. B **63** (1995), 65–110 (Section 4, page 77):

> **(4.4) Algorithm.**
> *Input:* A graph $G$.
> *Output:* Decides if there is a model of $H$ in $G$, and outputs such a model if one exists.
> *Running time:* $O(v^2)$.
>
> *Description:* Let $\omega$ be as in (4.2), with $\omega \ge 2$.
> (1) We choose a maximal subgraph $G_1$ of $G$ with at most $|E(H)|$ loops at every vertex and at
> most $|E(H)| + 1$ edges mutually parallel. There is a model of $H$ in $G$ if and only if there is
> one in $G_1$.
> (2) We apply (3.3) to $G_1$. We obtain a subgraph $G_2$ of $G_1$, and a branch-decomposition of
> $G_2$ of width $\le 3\omega$, such that either $G_2 = G_1$ or $G_2$ has branch-width $\ge \omega$.
> From the choice of $\omega$, it follows that either $G_2 = G_1$ or there is a model of $H$ in
> $G_2$. Consequently there is a model of $H$ in $G_1$ if and only if there is one in $G_2$.
> (3) We test if $G_2$ has an $H$-minor, and if so find a model of it in $G_2$, by using (4.1) to
> compute the $\varepsilon(H)$-folio of $G_2$ relative to $\emptyset$ and a modelling of it.
>
> From step (1), $|E(G_1)| \le O(v^2)$. Step (2) therefore takes time $O(v^2)$, and so does step
> (3). Thus the algorithm has running time $O(v^2)$ in total.
-/

@[expose] public section

namespace GraphMinor.Compute

open SimpleGraph
open scoped BigOperators

/-! ### Section 1: Input, Output, and Step-by-Step Mathematical Claims of (4.4) -/

/-- Input to GM XIII Algorithm (4.4): a graph `G : MultiDigraph n` on `n` vertices. -/
structure Alg44Input where
  /-- Number of vertices `|V(G)|`. -/
  n : ℕ
  /-- The input graph `G` on `Fin n`. -/
  G : MultiDigraph n

/-- Problem size `v(G)² = (|V(G)| + 1)²` for GM XIII Algorithm (4.4) (where `v = |V(G)| + 1`,
GM XIII page 66). -/
def alg44Size (x : Alg44Input) : ℕ :=
  (x.n + 1) ^ 2

/-- Flat Word RAM input encoding of `x : Alg44Input` in `inArr`: `x.G.enc`. -/
def encAlg44In (x : Alg44Input) : List ℕ :=
  x.G.enc

/-- Output specification of GM XIII Algorithm (4.4) (page 77:
"Decides if there is a model of $H$ in $G$, and outputs such a model if one exists."):
either `HasDigraphModel edgesH x.G` holds and `out = [1] ++ M.enc` for a valid model
`M : MultiDigraphModel edgesH x.G`, or `¬ HasDigraphModel edgesH x.G` and `out = [0]`. -/
def IsAlg44Output {p : ℕ} (edgesH : List (Fin p × Fin p)) (x : Alg44Input) (out : List ℕ) : Prop :=
  (∃ M : MultiDigraphModel edgesH x.G, M.IsValid ∧ out = [1] ++ M.enc) ∨
  (¬ HasDigraphModel edgesH x.G ∧ out = [0])

/-- **GM XIII (4.4), Step (1) Claim (page 77)**:
"We choose a maximal subgraph $G_1$ of $G$ with at most $|E(H)|$ loops at every vertex and at most
$|E(H)| + 1$ edges mutually parallel. There is a model of $H$ in $G$ if and only if there is one in
$G_1$." -/
theorem lemma_4_4_step_1 {p n : ℕ} (edgesH : List (Fin p × Fin p)) (G : MultiDigraph n) :
    HasDigraphModel edgesH G ↔ HasDigraphModel edgesH (G.cap edgesH.length) :=
  (hasDigraphModel_cap_iff edgesH G).symm

/-- **GM XIII (4.4), Step (1) Edge Bound (page 77)**:
"From step (1), $|E(G_1)| \le O(v^2)$."
Specifically, `(G.cap δ).numEdges ≤ (δ + 1) * (n * n)`. -/
theorem lemma_4_4_cap_numEdges_le {n : ℕ} (δ : ℕ) (G : MultiDigraph n) :
    (G.cap δ).numEdges ≤ (δ + 1) * (n * n) := by
  calc (G.cap δ).numEdges
    _ = ∑ u : Fin n, ∑ v : Fin n, (G.cap δ).edgeMult u v := rfl
    _ ≤ ∑ _u : Fin n, ∑ _v : Fin n, (δ + 1) :=
      Finset.sum_le_sum fun u _ => Finset.sum_le_sum fun v _ => G.cap_edgeMult_le_succ δ u v
    _ = (δ + 1) * (n * n) := by
      simp [Finset.sum_const, Finset.card_univ, Fintype.card_fin]
      ring

/-- **GM XIII (4.4), Step (2) First Claim (page 77)**:
"From the choice of $\omega$, it follows that either $G_2 = G_1$ or there is a model of $H$ in
$G_2$." -/
theorem lemma_4_4_step_2_or {p n : ℕ} {edgesH : List (Fin p × Fin p)} {ω : ℕ}
    (h42 : HasPlanarGridThreshold edgesH ω)
    {G₁ G₂ : MultiDigraph n}
    (h33 : G₂ = G₁ ∨ HasBranchWidthGe G₂ ω) :
    G₂ = G₁ ∨ HasDigraphModel edgesH G₂ := by
  rcases h33 with rfl | hbw
  · exact Or.inl rfl
  · exact Or.inr (h42 G₂ hbw)

/-- **GM XIII (4.4), Step (2) Second Claim (page 77)**:
"Consequently there is a model of $H$ in $G_1$ if and only if there is one in $G_2$." -/
theorem lemma_4_4_step_2_iff {p n : ℕ} {edgesH : List (Fin p × Fin p)} {ω : ℕ}
    (h42 : HasPlanarGridThreshold edgesH ω)
    {G₁ G₂ : MultiDigraph n} (hle : G₂ ≤ G₁)
    (h33 : G₂ = G₁ ∨ HasBranchWidthGe G₂ ω) :
    HasDigraphModel edgesH G₁ ↔ HasDigraphModel edgesH G₂ := by
  constructor
  · intro hG1
    rcases lemma_4_4_step_2_or h42 h33 with rfl | hG2
    · exact hG1
    · exact hG2
  · exact hasDigraphModel_mono hle

/-- **GM XIII (4.4), Step (3) Correctness Claim (page 77)**:
Combining Steps (1), (2), and (3), the modelling decision and witness produced by (4.1) on `G₂`
satisfies `IsAlg44Output edgesH ⟨n, G⟩ out`. -/
theorem lemma_4_4_step_3 {p n : ℕ} {edgesH : List (Fin p × Fin p)} {ω : ℕ}
    (h42 : HasPlanarGridThreshold edgesH ω)
    {G G₂ : MultiDigraph n}
    (hle : G₂ ≤ G.cap edgesH.length)
    (h33 : G₂ = G.cap edgesH.length ∨ HasBranchWidthGe G₂ ω)
    {out : List ℕ}
    (h41 : (∃ M : MultiDigraphModel edgesH G₂, M.IsValid ∧ out = [1] ++ M.enc) ∨
           (¬ HasDigraphModel edgesH G₂ ∧ out = [0])) :
    IsAlg44Output edgesH ⟨n, G⟩ out := by
  rcases h41 with ⟨M, hM, hout⟩ | ⟨hnoG2, hout⟩
  · have hleG : G₂ ≤ G := le_trans hle (G.cap_le edgesH.length)
    refine Or.inl ⟨M.castGraph, hM.mono hleG, hout⟩
  · have hnoG1 : ¬ HasDigraphModel edgesH (G.cap edgesH.length) :=
      fun hG1 => hnoG2 ((lemma_4_4_step_2_iff h42 hle h33).mp hG1)
    have hnoG : ¬ HasDigraphModel edgesH G :=
      fun hG => hnoG1 ((lemma_4_4_step_1 edgesH G).mp hG)
    exact Or.inr ⟨hnoG, hout⟩

/-! ### Section 2: Word RAM Program `alg44Prog` and Execution Proof -/

/-- Initialize array `a_Z` with `[0]` (`[([].length)] ++ [].map Fin.val`, representing `Z = ∅`). -/
def initEmptyZProg (a_Z : Arr) : Cmd :=
  .seq (.alloc a_Z (.const 1))
    (.write a_Z (.const 0) (.const 0))

theorem initEmptyZProg_exec {w n : ℕ} (a_Z : ℕ) (hw : 1 < 2 ^ w) (s : State) :
    ∃ s' t,
      Exec w (initEmptyZProg a_Z) s s' t ∧
      t ≤ 5 ∧
      s'.arrs a_Z = [([] : List (Fin n)).length] ++ ([] : List (Fin n)).map Fin.val ∧
      (∀ a : ℕ, a ≠ a_Z → s'.arrs a = s.arrs a) ∧
      (∀ r : ℕ, s'.regs r = s.regs r) := by
  have h0_w : 0 < 2 ^ w := by omega
  let s₁ := s.setArr a_Z (List.replicate 1 0)
  have hex₁ : Exec w (.alloc a_Z (.const 1)) s s₁ 2 :=
    .alloc (by simp [Expr.eval, checkWord, hw])
  let s₂ := s₁.writeArr a_Z 0 0
  have hex₂ : Exec w (.write a_Z (.const 0) (.const 0)) s₁ s₂ 3 :=
    .write (by simp [Expr.eval, checkWord, h0_w])
      (by simp [Expr.eval, checkWord, h0_w])
      (by simp [s₁])
  refine ⟨s₂, 2 + 3, .seq hex₁ hex₂, by omega,
    by simp [s₂, s₁, State.writeArr],
    fun a ha => by simp [s₂, s₁, State.writeArr, State.setArr_arrs_ne _ _ ha],
    fun _ => rfl⟩

/-- Word RAM program for GM XIII Algorithm (4.4) (page 77):
* **Step (1):** Calls `capMultiDigraphProg edgesH.length a_in a_scratch (a_scratch + 1) r_base` to
  construct `G₁ = G.cap |E(H)|` in array `a_scratch + 1`.
* **Step (2):** Calls `P33` (Algorithm (3.3)) on `a_scratch + 1` to construct `G₂ ≤ G₁` in
  `a_scratch + 2` and a branch-decomposition `bdCode` of `G₂` of width `≤ 3 * ω` in `a_scratch + 3`.
* **Step (3):** Initializes `Z = ∅` (`[0]`) in `a_scratch + 4`, calls `P41` (Algorithm (4.1)) on
  `(G₂, ∅, bdCode)` to compute the `ε(H)`-folio `F` in `a_scratch + 5` and its modelling `models`
  in `a_scratch + 6`, and calls `extractTargetModelProg` to extract a model of `H` (or `[0]`) into
  `a_out`. -/
noncomputable def alg44Prog (p : ℕ) (edgesH : List (Fin p × Fin p))
    (a_in a_out a_scratch r_base : ℕ) (P33 P41 : Cmd) : Cmd :=
  .seq (capMultiDigraphProg edgesH.length a_in a_scratch (a_scratch + 1) r_base)
    (.seq P33
      (.seq (initEmptyZProg (a_scratch + 4))
        (.seq P41
          (extractTargetModelProg p edgesH (a_scratch + 2) (a_scratch + 5) (a_scratch + 6)
            a_out r_base))))

/-- Bound `wordSize c M` by `wordSize (c * K) m` whenever `M ≤ K * m` and `2 ≤ K`. -/
private theorem wordSize_le_of_le_mul (c : ℕ) {K M m : ℕ} (hK : 2 ≤ K) (hM : M ≤ K * m) :
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

/-- Irreducible wrapper around `(allDetailLeCodes 0 (m_H + p)).length` so arithmetic tactics treat
it as an atomic constant rather than unfolding the bounded word-list enumeration. -/
irreducible_def folioCodeCount (m_H p : ℕ) : ℕ :=
  (allDetailLeCodes 0 (m_H + p)).length

theorem length_allDetailLeCodes_eq_folioCodeCount (m_H p : ℕ) :
    (allDetailLeCodes 0 (m_H + p)).length = folioCodeCount m_H p := by
  rw [folioCodeCount]

/-- Time bound multiplier for `alg44Prog`. -/
def alg44TimeConst (p m_H C₃₃ C₄₁ : ℕ) : ℕ :=
  let K := folioCodeCount m_H p
  let C_ext := 25 + (26 + (90 + 54 * m_H + 34 * p) * K) * K
  (m_H + 3) * (200 + C₃₃ + C₄₁ + C_ext)

/-- Word-size constant for `alg44Prog`. -/
def alg44WordConst (p m_H ω c_w33 c_w41 : ℕ) : ℕ :=
  let δ := m_H + p
  let K := folioCodeCount m_H p
  (c_w33 + c_w41) * (m_H + 2) + 3 * ω + 10 + 4 * δ + K * (3 + 3 * δ)

theorem alg44_word_bounds {p m_H ω c_w33 c_w41 n m_act e₁ pow_w : ℕ}
    (hm_act : m_act ≤ n * n)
    (he₁ : e₁ ≤ (m_H + 1) * (n * n))
    (hprod : alg44WordConst p m_H ω c_w33 c_w41 * (n + 1) ^ 2 < pow_w) :
    3 < pow_w ∧
    n < pow_w ∧
    p < pow_w ∧
    m_H + 1 < pow_w ∧
    m_H + p < pow_w ∧
    2 + 3 * m_act < pow_w ∧
    e₁ < pow_w ∧
    3 * ω < pow_w ∧
    3 + 2 * m_H + p * n < pow_w ∧
    (1 + folioCodeCount m_H p * (3 + 2 * (m_H + p))) + 3 + 2 * (m_H + p) < pow_w ∧
    (1 + folioCodeCount m_H p * (3 + 2 * (m_H + p) + (m_H + p) * n)) +
      3 + 2 * m_H + p * n < pow_w := by
  unfold alg44WordConst at hprod
  dsimp only at hprod
  generalize folioCodeCount m_H p = K at hprod ⊢
  let S := (n + 1) ^ 2
  change ((c_w33 + c_w41) * (m_H + 2) + 3 * ω + 10 + 4 * (m_H + p) + K * (3 + 3 * (m_H + p))) * S < pow_w at hprod
  have hsq : S = n * n + 2 * n + 1 := by dsimp [S]; ring
  have h1 : 1 ≤ S := by omega
  have h2 : n * n ≤ S := by omega
  have h3 : n + 1 ≤ S := by omega
  have h_exp :
      ((c_w33 + c_w41) * (m_H + 2) + 3 * ω + 10 + 4 * (m_H + p) + K * (3 + 3 * (m_H + p))) * S =
        (c_w33 + c_w41) * (m_H + 2) * S + (3 * ω) * S + 10 * S +
          4 * (m_H + p) * S + (K * (3 + 3 * (m_H + p))) * S := by ring
  have h_w : 3 * ω ≤ (3 * ω) * S := Nat.le_mul_of_pos_right _ (by omega)
  have h_mp : m_H + p ≤ (m_H + p) * S := Nat.le_mul_of_pos_right _ (by omega)
  have hi_eq : (4 * (m_H + p)) * S = 4 * ((m_H + p) * S) := by ring
  have h_e1 : e₁ ≤ (m_H + 1) * S := le_trans he₁ (Nat.mul_le_mul_left _ h2)
  have h_e1' : (m_H + 1) * S ≤ 10 * S + (4 * (m_H + p)) * S := by
    have : (4 * (m_H + p)) * S = 4 * (m_H * S) + 4 * (p * S) := by ring
    have : (m_H + 1) * S = m_H * S + S := by ring
    omega
  have h_pn : p * n ≤ (m_H + p) * S := by
    have : p * n ≤ (m_H + p) * n := Nat.mul_le_mul_right n (by omega)
    have : (m_H + p) * n ≤ (m_H + p) * S := Nat.mul_le_mul_left _ (by omega)
    omega
  have h_kf : K * (3 + 2 * (m_H + p)) ≤ (K * (3 + 3 * (m_H + p))) * S := by
    have hle1 : K * (3 + 2 * (m_H + p)) ≤ K * (3 + 3 * (m_H + p)) :=
      Nat.mul_le_mul_left K (by omega)
    exact le_trans hle1 (Nat.le_mul_of_pos_right _ (by omega))
  have h_km : K * (3 + 2 * (m_H + p) + (m_H + p) * n) ≤ (K * (3 + 3 * (m_H + p))) * S := by
    have h_inner : 3 + 2 * (m_H + p) + (m_H + p) * n ≤ (3 + 3 * (m_H + p)) * S := by
      have : (m_H + p) * n ≤ (m_H + p) * S := Nat.mul_le_mul_left _ (by omega)
      have : 3 + 2 * (m_H + p) ≤ (3 + 2 * (m_H + p)) * S := Nat.le_mul_of_pos_right _ (by omega)
      have : (3 + 3 * (m_H + p)) * S = (3 + 2 * (m_H + p)) * S + (m_H + p) * S := by ring
      omega
    have hmul := Nat.mul_le_mul_left K h_inner
    rwa [← Nat.mul_assoc] at hmul
  refine ⟨by omega, by omega, by omega, by omega, by omega,
    by omega, by omega, by omega, by omega, by omega, by omega⟩

theorem alg44_time_bound {p m_H C₃₃ C₄₁ n m_act e₁ e₂ t₁ t₂ t_z t₃ t_ext : ℕ}
    (hm_act_le : m_act ≤ n * n)
    (he₁_le : e₁ ≤ (m_H + 1) * (n * n))
    (he₂_le : e₂ ≤ e₁)
    (ht₁ : t₁ ≤ 115 * m_act + 80)
    (ht₂ : t₂ ≤ C₃₃ * ((n + 1) ^ 2 + (e₁ + n + 1)))
    (ht_z : t_z ≤ 5)
    (ht₃ : t₃ ≤ C₄₁ * (e₂ + n + 1))
    (ht_ext : t_ext ≤ extractTargetModelTime p m_H n) :
    t₁ + (t₂ + (t_z + (t₃ + t_ext))) ≤ alg44TimeConst p m_H C₃₃ C₄₁ * (n + 1) ^ 2 := by
  unfold alg44TimeConst
  dsimp only
  unfold extractTargetModelTime at ht_ext
  dsimp only at ht_ext
  rw [length_allDetailLeCodes_eq_folioCodeCount] at ht_ext
  generalize folioCodeCount m_H p = K at ht_ext ⊢
  have hsq : (n + 1) ^ 2 = n * n + 2 * n + 1 := by ring
  have h1 : 1 ≤ (n + 1) ^ 2 := by omega
  have h2 : n * n ≤ (n + 1) ^ 2 := by omega
  have h3 : n + 1 ≤ (n + 1) ^ 2 := by omega
  have h_e1_n : (n + 1) ^ 2 + (e₁ + n + 1) ≤ (m_H + 3) * (n + 1) ^ 2 := by nlinarith
  have ht2' : t₂ ≤ C₃₃ * ((m_H + 3) * (n + 1) ^ 2) :=
    le_trans ht₂ (Nat.mul_le_mul_left _ h_e1_n)
  have h_e2_n : e₂ + n + 1 ≤ (m_H + 3) * (n + 1) ^ 2 := by nlinarith
  have ht3' : t₃ ≤ C₄₁ * ((m_H + 3) * (n + 1) ^ 2) :=
    le_trans ht₃ (Nat.mul_le_mul_left _ h_e2_n)
  have ht1' : t₁ + t_z ≤ 200 * ((m_H + 3) * (n + 1) ^ 2) := by nlinarith
  have hcand_le : candStepTime p m_H n ≤ (90 + 54 * m_H + 34 * p) * (n + 1) := by
    unfold candStepTime
    nlinarith
  have hcandK_le :
      26 + candStepTime p m_H n * K ≤
        (26 + (90 + 54 * m_H + 34 * p) * K) * (n + 1) := by
    have hmul := Nat.mul_le_mul_right K hcand_le
    have hadd :
        26 + (90 + 54 * m_H + 34 * p) * (n + 1) * K ≤
          (26 + (90 + 54 * m_H + 34 * p) * K) * (n + 1) := by
      have hr : (26 + (90 + 54 * m_H + 34 * p) * K) * (n + 1) =
          26 * n + 26 + (90 + 54 * m_H + 34 * p) * (n + 1) * K := by ring
      omega
    omega
  have hext_le :
      25 + (26 + candStepTime p m_H n * K) * K ≤
        (25 + (26 + (90 + 54 * m_H + 34 * p) * K) * K) * (n + 1) ^ 2 := by
    have hmulK := Nat.mul_le_mul_right K hcandK_le
    have hr1 : (26 + (90 + 54 * m_H + 34 * p) * K) * (n + 1) * K =
        ((26 + (90 + 54 * m_H + 34 * p) * K) * K) * (n + 1) := by ring
    have hr2 : ((26 + (90 + 54 * m_H + 34 * p) * K) * K) * (n + 1) ≤
        ((26 + (90 + 54 * m_H + 34 * p) * K) * K) * (n + 1) ^ 2 :=
      Nat.mul_le_mul_left _ h3
    have hr3 : 25 ≤ 25 * (n + 1) ^ 2 := by omega
    have hr4 : (25 + (26 + (90 + 54 * m_H + 34 * p) * K) * K) * (n + 1) ^ 2 =
        25 * (n + 1) ^ 2 + ((26 + (90 + 54 * m_H + 34 * p) * K) * K) * (n + 1) ^ 2 := by ring
    omega
  let C_ext := 25 + (26 + (90 + 54 * m_H + 34 * p) * K) * K
  have htext_step : t_ext ≤ C_ext * (n + 1) ^ 2 := le_trans ht_ext hext_le
  have htext' : t_ext ≤ C_ext * ((m_H + 3) * (n + 1) ^ 2) := by
    have hle_m : (n + 1) ^ 2 ≤ (m_H + 3) * (n + 1) ^ 2 :=
      Nat.le_mul_of_pos_left _ (by omega)
    exact le_trans htext_step (Nat.mul_le_mul_left C_ext hle_m)
  change t₁ + (t₂ + (t_z + (t₃ + t_ext))) ≤
    (m_H + 3) * (200 + C₃₃ + C₄₁ + C_ext) * (n + 1) ^ 2
  have hrhs : (m_H + 3) * (200 + C₃₃ + C₄₁ + C_ext) * (n + 1) ^ 2 =
      200 * ((m_H + 3) * (n + 1) ^ 2) +
      C₃₃ * ((m_H + 3) * (n + 1) ^ 2) +
      C₄₁ * ((m_H + 3) * (n + 1) ^ 2) +
      C_ext * ((m_H + 3) * (n + 1) ^ 2) := by ring
  omega

/-- General execution theorem for `alg44Prog` on arbitrary input, output and scratch arrays, used
both for the standalone `ComputesArrRelInTime` theorem `gm13_algorithm_4_4` and as a direct
subroutine call inside Algorithm (7.2) (`GraphMinor.Compute.Algorithm72`). -/
theorem alg44Prog_exec {p : ℕ} (edgesH : List (Fin p × Fin p)) (ω : ℕ) (hω : 2 ≤ ω)
    (h42 : HasPlanarGridThreshold edgesH ω)
    (a_in a_out a_scratch a_base r_base : ℕ)
    (P33 P41 : Cmd)
    (hP33 : Alg33Spec ω (a_scratch + 1) (a_scratch + 2) (a_scratch + 3) a_base r_base P33)
    (hP41 : Alg41Spec 0 (edgesH.length + p) (3 * ω)
      (a_scratch + 2) (a_scratch + 4) (a_scratch + 3) (a_scratch + 5) (a_scratch + 6)
      a_base r_base P41)
    (ha_in_sc : a_in ≠ a_scratch)
    (ha_out_sc : a_out < a_scratch ∨ a_base ≤ a_out)
    (ha_sc_lt : a_scratch + 6 < a_base) :
    ∃ (C₄₄ c_w : ℕ), 0 < C₄₄ ∧ 0 < c_w ∧
      ∀ (n : ℕ) (G : MultiDigraph n) (w : ℕ),
        wordSize c_w ((n + 1) ^ 2) ≤ w →
        ∀ (s : State),
          s.arrs a_in = G.enc →
          ∃ (s' : State) (t : ℕ),
            Exec w (alg44Prog p edgesH a_in a_out a_scratch r_base P33 P41) s s' t ∧
            t ≤ C₄₄ * (n + 1) ^ 2 ∧
            IsAlg44Output edgesH ⟨n, G⟩ (s'.arrs a_out) ∧
            (∀ r < r_base, s'.regs r = s.regs r) ∧
            (∀ a < a_scratch, a ≠ a_out → s'.arrs a = s.arrs a) := by
  rcases hP33 with ⟨C₃₃, c_w33, hC33_pos, hcw33_pos, h33_exec⟩
  rcases (alg41MultiSpec_iff_alg41Spec 0 (edgesH.length + p) (3 * ω)
      (a_scratch + 2) (a_scratch + 4) (a_scratch + 3) (a_scratch + 5) (a_scratch + 6)
      a_base r_base P41).mpr hP41 with
    ⟨C₄₁, c_w41, hC41_pos, hcw41_pos, h41_exec⟩
  have hC44_pos : 0 < alg44TimeConst p edgesH.length C₃₃ C₄₁ := by
    unfold alg44TimeConst
    dsimp only
    exact Nat.mul_pos (by omega) (by omega)
  have hcw_pos : 0 < alg44WordConst p edgesH.length ω c_w33 c_w41 := by
    unfold alg44WordConst
    dsimp only
    omega
  refine ⟨alg44TimeConst p edgesH.length C₃₃ C₄₁,
    alg44WordConst p edgesH.length ω c_w33 c_w41,
    hC44_pos, hcw_pos, fun n G w hw s hin => ?_⟩
  have h_prod_lt : alg44WordConst p edgesH.length ω c_w33 c_w41 * (n + 1) ^ 2 < 2 ^ w :=
    mul_lt_two_pow_of_wordSize_le hcw_pos hw
  have hm_act_le : G.numActivePairs ≤ n * n := G.numActivePairs_le_sq
  have hcap_edges_le : (G.cap edgesH.length).numEdges ≤ (edgesH.length + 1) * (n * n) :=
    lemma_4_4_cap_numEdges_le edgesH.length G
  rcases alg44_word_bounds hm_act_le hcap_edges_le h_prod_lt with
    ⟨hw3, hn_w, hp_w, hδ_cap_w, hδ_w, hm3_w, hedges_w, h3ω_w, hout_len_w, hf_bound_w, hm_bound_w⟩
  -- Step (1): Execute capMultiDigraphProg on G:
  have hin_extra : s.arrs a_in = G.enc ++ [] := by simp [hin]
  rcases capMultiDigraphProg_exec G edgesH.length [] a_in a_scratch (a_scratch + 1) r_base
      ha_in_sc (by omega) hw3 hn_w hδ_cap_w hm3_w hedges_w hin_extra with
    ⟨s₁, t₁, hex₁, ht₁, ha_G1, _, _, _, harr₁, hreg₁⟩
  -- Step (2): Execute P33 on G₁ = G.cap edgesH.length:
  have hsq_ge : n * n ≤ (n + 1) ^ 2 := by
    have : (n + 1) ^ 2 = n * n + 2 * n + 1 := by ring
    omega
  have hM33_le : (n + 1) ^ 2 + (G.cap edgesH.length).numEdges ≤
      (edgesH.length + 2) * (n + 1) ^ 2 := by
    have h1 : (G.cap edgesH.length).numEdges ≤ (edgesH.length + 1) * (n + 1) ^ 2 :=
      le_trans hcap_edges_le (Nat.mul_le_mul_left _ hsq_ge)
    have h2 : (edgesH.length + 2) * (n + 1) ^ 2 =
        (n + 1) ^ 2 + (edgesH.length + 1) * (n + 1) ^ 2 := by ring
    omega
  have hw_33 : wordSize c_w33 ((n + 1) ^ 2 + (G.cap edgesH.length).numEdges) ≤ w := by
    have h1 := wordSize_le_of_le_mul c_w33 (by omega) hM33_le
    have h2 : c_w33 * (edgesH.length + 2) ≤ alg44WordConst p edgesH.length ω c_w33 c_w41 := by
      unfold alg44WordConst; dsimp only; rw [Nat.add_mul]; omega
    exact le_trans h1 (le_trans (wordSize_mono_left h2 _) hw)
  have hmult1_w : ∀ pair ∈ (G.cap edgesH.length).activePairsList,
      (G.cap edgesH.length).edgeMult pair.1 pair.2 < 2 ^ w := by
    intro pair _
    have hle := G.cap_edgeMult_le_succ edgesH.length pair.1 pair.2
    omega
  rcases h33_exec n (G.cap edgesH.length) w hw_33 h3ω_w hmult1_w s₁ ha_G1 with
    ⟨s₂, t₂, G₂, bdCode, hex₂, ht₂, hG2_le, hG2_bd, hG2_or_raw, ha_G2, ha_bd, _, hreg₂, harr₂⟩
  have hG2_or : G₂ = G.cap edgesH.length ∨ HasBranchWidthGe G₂ ω := by
    rcases hG2_or_raw with rfl | ⟨_, hhigh⟩
    · exact Or.inl rfl
    · exact Or.inr (isAlg33HighWidthCase_imp_hasBranchWidthGe hω hhigh)
  -- Step (3a): Initialize empty Z = [] in `a_scratch + 4`:
  rcases initEmptyZProg_exec (w := w) (n := n) (a_scratch + 4) (by omega) s₂ with
    ⟨s₃, t_z, hex_z, ht_z, ha_Z, harr_z, hreg_z⟩
  -- Step (3b): Execute P41 on `(G₂, [], bdCode)`:
  have hG2_edges_le : G₂.numEdges ≤ (G.cap edgesH.length).numEdges :=
    MultiDigraph.numEdges_mono hG2_le
  have hM41_le : G₂.numEdges + n + 1 ≤ (edgesH.length + 2) * (n + 1) ^ 2 := by
    have h1 : n + 1 ≤ (n + 1) ^ 2 := by
      have : (n + 1) ^ 2 = n * n + 2 * n + 1 := by ring
      omega
    omega
  have hw_41 : wordSize c_w41 (G₂.numEdges + n + 1) ≤ w := by
    have h1 := wordSize_le_of_le_mul c_w41 (by omega) hM41_le
    have h2 : c_w41 * (edgesH.length + 2) ≤ alg44WordConst p edgesH.length ω c_w33 c_w41 := by
      unfold alg44WordConst; dsimp only; rw [Nat.add_mul]; omega
    exact le_trans h1 (le_trans (wordSize_mono_left h2 _) hw)
  have hmult2_w : ∀ pair ∈ G₂.activePairsList, G₂.edgeMult pair.1 pair.2 < 2 ^ w := by
    intro pair _
    have hle : G₂.edgeMult pair.1 pair.2 ≤ (G.cap edgesH.length).edgeMult pair.1 pair.2 :=
      hG2_le pair.1 pair.2
    have hle1 := G.cap_edgeMult_le_succ edgesH.length pair.1 pair.2
    omega
  have ha_G2_s3 : s₃.arrs (a_scratch + 2) = G₂.enc := by
    rw [harr_z (a_scratch + 2) (by omega), ha_G2]
  have ha_bd_s3 : s₃.arrs (a_scratch + 3) = bdCode := by
    rw [harr_z (a_scratch + 3) (by omega), ha_bd]
  rcases h41_exec n G₂ [] bdCode w (by simp) hG2_bd hw_41 h3ω_w hmult2_w s₃
      ha_G2_s3 ha_Z ha_bd_s3 with
    ⟨s₄, t₃, F, models, hex₃, ht₃, hfolio_prop, ha_folio, ha_models, hreg₃, harr₃⟩
  -- Step (3c): Execute `extractTargetModelProg` to extract model of H into `a_out`:
  have ha_G2_s4 : s₄.arrs (a_scratch + 2) = G₂.enc := by
    rw [harr₃ (a_scratch + 2) (by omega) (by omega) (by omega), ha_G2_s3]
  have hf_len_le :
      (encFolioSetRep F).length ≤
        1 + folioCodeCount edgesH.length p * (3 + 2 * (edgesH.length + p)) := by
    rw [← length_allDetailLeCodes_eq_folioCodeCount]
    simpa only [List.length_nil, Nat.add_zero] using length_encFolioSetRep_le F
  have hm_len_le :
      (encFolioModels F models).length ≤
        1 + folioCodeCount edgesH.length p *
          (3 + 2 * (edgesH.length + p) + (edgesH.length + p) * n) := by
    rw [← length_allDetailLeCodes_eq_folioCodeCount]
    simpa only [List.length_nil, Nat.zero_add, MultiDigraph.toMultiComputeRootedDigraph,
      MultiDigraph.toMultiComputeDigraph] using length_encFolioModels_le F models
  have hf_len_w : (encFolioSetRep F).length + 3 + 2 * (edgesH.length + p) < 2 ^ w := by omega
  have hm_len_w :
      (encFolioModels F models).length + 3 + 2 * edgesH.length + p * n < 2 ^ w := by omega
  rcases extractTargetModelProg_exec edgesH G₂ F models hfolio_prop
      (a_scratch + 2) (a_scratch + 5) (a_scratch + 6) a_out r_base
      (by omega) (by omega) (by omega)
      hw3 hn_w hp_w hδ_w hout_len_w hf_len_w hm_len_w
      ha_G2_s4 ha_folio ha_models with
    ⟨s₅, t_ext, hex_ext, ht_ext, h41_out, harr_ext, hreg_ext⟩
  refine ⟨s₅, t₁ + (t₂ + (t_z + (t₃ + t_ext))),
    .seq hex₁ (.seq hex₂ (.seq hex_z (.seq hex₃ hex_ext))),
    alg44_time_bound hm_act_le hcap_edges_le hG2_edges_le ht₁ ht₂ ht_z ht₃ ht_ext,
    lemma_4_4_step_3 h42 hG2_le hG2_or h41_out, ?_, ?_⟩
  · -- Register preservation:
    intro r hr
    rw [hreg_ext r hr, hreg₃ r hr, hreg_z r, hreg₂ r hr, hreg₁ r hr]
  · -- Array preservation:
    intro a ha ha_out
    have ha_lt_base : a < a_base := by omega
    rw [harr_ext a ha_out,
        harr₃ a ha_lt_base (by omega) (by omega),
        harr_z a (by omega),
        harr₂ a ha_lt_base (by omega) (by omega),
        harr₁ a (by omega) (by omega)]

/-- **GM XIII (4.4) Algorithm with explicit subroutine specs (page 77)**:
Given a planar graph `H` (with `p` vertices and edges `edgesH`), branch-width threshold `ω ≥ 2` as
in (4.2), and subroutines `P33` (Algorithm (3.3)) and `P41` (Algorithm (4.1)), `alg44Prog` decides
if there is a model of `H` in the input graph `G` and outputs such a model if one exists, in running
time `O(v²)`. -/
theorem algorithm_4_4_from_specs {p : ℕ} (edgesH : List (Fin p × Fin p)) (ω : ℕ) (hω : 2 ≤ ω)
    (h42 : HasPlanarGridThreshold edgesH ω)
    (P33 P41 : Cmd)
    (hP33 : Alg33Spec ω 11 12 13 20 10 P33)
    (hP41 : Alg41Spec 0 (edgesH.length + p) (3 * ω) 12 14 13 15 16 20 10 P41) :
    ComputesArrRelInTime alg44Size encAlg44In (IsAlg44Output edgesH)
      (alg44Prog p edgesH inArr outArr 10 10 P33 P41) (fun m => m) := by
  rcases alg44Prog_exec edgesH ω hω h42 inArr outArr 10 20 10 P33 P41 hP33 hP41
      (by decide) (Or.inl (by decide)) (by decide) with
    ⟨C₄₄, c_w, hC44, hcw, hexec⟩
  refine ⟨C₄₄, c_w, hC44, hcw, fun x s hin => ?_⟩
  rcases hexec x.n x.G (wordSize c_w (alg44Size x)) (le_refl _) s hin with
    ⟨s', t, hex, ht, hout, _⟩
  exact ⟨s', t, hex, ht, hout⟩

/-- **GM XIII (4.4) Algorithm joined with `gm13_algorithm_3_3` (`Join433.lean`) and `GM13.theorem_4_2_proof`
(`Join413.lean`) (page 77)**:
"Let $H$ be a planar graph. ...
(4.4) **Algorithm.**
*Input:* A graph $G$.
*Output:* Decides if there is a model of $H$ in $G$, and outputs such a model if one exists.
*Running time:* $O(v^2)$." -/
theorem gm13_algorithm_4_4 {p : ℕ} (edgesH : List (Fin p × Fin p))
    (hPlanar : IsPlanar (targetGMGraph p edgesH)) :
    ∃ (P44 : Cmd),
      ComputesArrRelInTime alg44Size encAlg44In (IsAlg44Output edgesH) P44 (fun m => m) := by
  rcases exists_hasPlanarGridThreshold_of_isPlanarGraph edgesH hPlanar with ⟨ω, hω, h42⟩
  rcases alg41Spec72_of_claim41
      (fun δ ξ B => ⟨alg41CoreProg δ ξ B, algorithm_4_1_core δ ξ B⟩)
      (edgesH.length + p) (3 * ω) with ⟨P41, hP41_spec⟩
  have hP33 : Alg33Spec ω 11 12 13 20 10 (alg33MultiProg ω 11 12 13 20 10) :=
    alg33Spec_of_algorithm_3_3 ω hω 11 12 13 20 10
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  exact ⟨alg44Prog p edgesH inArr outArr 10 10 (alg33MultiProg ω 11 12 13 20 10) P41,
    algorithm_4_4_from_specs edgesH ω hω h42 _ P41 hP33 hP41_spec⟩

end GraphMinor.Compute
