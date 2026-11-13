module

public import GraphMinor.Compute.Algorithm94Init

/-!
# Graph Minors XIII, Algorithm (9.4): Dividing Subwalls or $K_p$ Minor in $O(\varepsilon(G))$ Time

This file formalizes **Algorithm (9.4)** (and proves **(9.3)**, `Algorithm94Statement`) from
Robertson and Seymour, *Graph Minors. XIII. The Disjoint Paths Problem*, page 102,
on the shared `MultiDigraph` and `WallOfHeight` formats:

> *(9.3) For any $p \ge 0$ there exists $k, r \ge 0$ such that there is an algorithm as in (9.4),
> with running time $\le C\varepsilon(G)$, where $C$ depends on $p, t$, and the height of $H$.*
>
> *(9.4) Algorithm.*
> *Input:* A graph $G$, a wall $H \subseteq G$ with distance function $d$, and subwalls
> $H_1, \dots, H_t$ of $H$ with $d(H_i, H_j) \ge r$ ($1 \le i < j \le t$).
> *Output:* Either
> (i) a model of $K_p$ in $G$, or
> (ii) a subset $X \subseteq V(G)$ with $|X| < \binom{p}{2}$ and a subset
> $I \subseteq \{1, \dots, t\}$ with $|I| \ge t - k$ such that for all $i \in I$, $H_i$ is dividing
> in $(G \setminus X) \cup H$.
-/

@[expose] public section

namespace GraphMinor.Compute

open SimpleGraph Classical

/-! ### Section 1: Unrolled Iteration Loop for Algorithm (9.4) -/

/-- Unrolled recursion of Algorithm (9.4) over `rem` remaining iterations (`idx + rem = p.choose 2`):
- When `rem = 0` (`idx = p.choose 2`): constructs `encAlg77In x77` in `inArr` from `a_G`, `a_W`,
  and `a_stars`, executes `P77`, slices `encBitSetsUpTo K p` (`p * x.n` words at offset
  `2 + 2 * (completeGraphEdges p).length`) from `outArr` into `arr 26`, and prepends `0` into
  `outArr`.
- When `rem + 1`:
  1. Copies `a_G` to `arr 9`, `a_X` to `arr 16`, and `a_WV` to `arr 11`,
  2. Runs `buildWallUnionCsrProg h (B_arr + 6)` (building `G'.enc` in `arr 23` and CSR in
     `20, 21, 22`),
  3. Sets `reg 1 := reg B_reg` (`x.n`) and `reg 2 := len 22`,
  4. Runs `alg94ScanSubwallsProg h (B_arr + 3) k t`,
  5. If `reg 15 < t - k` is false (`t - k ≤ div_cnt`), outputs `1 :: (bitSetList X ++ arr 18)`
     (Case (ii));
  6. Otherwise (`k ≤ nonDiv_cnt`), constructs `encAlg92In x92` in `inArr` from `arr 23`, `a_W`,
     and `arr 24`, and runs `P92`:
     - If `outArr[0] ≠ 0` (`K_p` model `1 :: encBitSetsUpTo K p`), writes `outArr[0] := 0`;
     - If `outArr[0] = 0` (`(l, m)`-star `0 :: c.1 :: encHPaths r`), marks `c` in `a_X`, appends
       `c.1 :: encHPaths r` to `a_stars`, and recurses on `(rem, idx + 1)`. -/
def alg94IterProg (p h k t B_arr B_reg : ℕ) (P77 P92 : Cmd) : ℕ → ℕ → Cmd
  | 0, _ =>
    let a_G : Arr := B_arr
    let a_W : Arr := B_arr + 1
    let a_stars : Arr := B_arr + 5
    let r_n_save : Reg := B_reg
    .seq (copyArrLoopProg a_G inArr 14 15)
      (.seq (.assign 14 (.len inArr))
        (.seq (.assign 15 (.len a_W))
          (.seq (appendArrProg inArr a_W 30 14 15 20)
            (.seq (.assign 15 (.len a_stars))
              (.seq (appendArrProg inArr a_stars 30 14 15 20)
                (.seq P77
                  (.seq (.assign 14 (.op .mul (.const p) (.reg r_n_save)))
                    (.seq (readSliceProg outArr
                        (.const (2 + 2 * (completeGraphEdges p).length)) 26 (.reg 14) 20)
                      (prependWordProg (.const 0) 26 outArr 14 20)))))))))
  | rem + 1, idx =>
    let a_G : Arr := B_arr
    let a_W : Arr := B_arr + 1
    let a_WV : Arr := B_arr + 2
    let a_sub : Arr := B_arr + 3
    let a_X : Arr := B_arr + 4
    let a_stars : Arr := B_arr + 5
    let baseSuccArr : ℕ := B_arr + 6
    let r_n_save : Reg := B_reg
    .seq (copyArrLoopProg a_G 9 14 15)
      (.seq (copyArrLoopProg a_X 16 14 15)
        (.seq (copyArrLoopProg a_WV 11 14 15)
          (.seq (buildWallUnionCsrProg h baseSuccArr)
            (.seq (.assign 1 (.reg r_n_save))
              (.seq (.assign 2 (.len 22))
                (.seq (alg94ScanSubwallsProg h a_sub k t)
                  (.ite (.op .lt (.reg 15) (.const (t - k)))
                    (.seq (copyArrLoopProg 23 inArr 14 15)
                      (.seq (.assign 14 (.len inArr))
                        (.seq (.assign 15 (.len a_W))
                          (.seq (appendArrProg inArr a_W 30 14 15 20)
                            (.seq (.assign 15 (.len 24))
                              (.seq (appendArrProg inArr 24 30 14 15 20)
                                (.seq P92
                                  (.seq (.assign 14 (.read outArr (.const 0)))
                                    (.ite (.reg 14)
                                      (.write outArr (.const 0) (.const 0))
                                      (.seq (.assign 14 (.read outArr (.const 1)))
                                        (.seq (.write a_X (.reg 14) (.const 1))
                                          (.seq (.assign 15 (.op .sub (.len outArr) (.const 1)))
                                            (.seq (readSliceProg outArr (.const 1) 26 (.reg 15) 20)
                                              (.seq (.assign 14 (.len a_stars))
                                                (.seq (appendArrProg a_stars 26 30 14 15 20)
                                                  (alg94IterProg p h k t B_arr B_reg P77 P92
                                                    rem (idx + 1)))))))))))))))))
                    (.seq (copyArrLoopProg a_X 26 14 15)
                      (.seq (.assign 14 (.reg r_n_save))
                        (.seq (.assign 15 (.const t))
                          (.seq (appendArrProg 26 18 30 14 15 20)
                            (prependWordProg (.const 1) 26 outArr 14 20))))))))))))

/-- Base cost bound (`rem = 0`) for `alg94IterProg`. -/
def alg94BaseCost (p l h n m_edges C₇₇ : ℕ) : ℕ :=
  200 + 90 * (2 + 3 * m_edges) + 60 * maxWallEncLen h n +
    18 * (p.choose 2 * (1 + l * (n + 1))) + C₇₇ * m_edges + C₇₇ * (n + 1) + 34 * (p * n)

/-- Per-iteration step cost bound (`rem + 1`) for `alg94IterProg`. -/
def alg94IterStepCost (p l h k t n m_edges B_arr C₉₂ : ℕ) : ℕ :=
  650 + 110 * (2 + 3 * m_edges) +
    (291 + (isWallUnionEdgeExpr h (B_arr + 6) 16 (3 + 6) (3 + 7)).cost) * m_edges +
    150 * n + 60 * t +
    t * alg94ScanStepCost h n k (2 * m_edges) (2 * m_edges) +
    60 * maxWallEncLen h n + 18 * (k * maxWallEncLen h n) +
    C₉₂ * (m_edges + n + 1) +
    35 * (p.choose 2 * (1 + l * (n + 1))) + 34 * (1 + l * (n + 1))

private lemma alg94_base_bound
    {p l h n m_edges C₇₇ : ℕ}
    {t₁ t₄ t₆ t₇ t₉ t₁₀ lenG lenW lenStars : ℕ}
    (ht₁ : t₁ ≤ 8 + 15 * lenG)
    (hlenG : lenG ≤ 2 + 3 * m_edges)
    (ht₄ : t₄ ≤ 34 * lenG + 18 * lenW + 36)
    (hlenW : lenW ≤ maxWallEncLen h n)
    (ht₆ : t₆ ≤ 34 * lenG + 34 * lenW + 18 * lenStars + 36)
    (hlenStars : lenStars ≤ p.choose 2 * (1 + l * (n + 1)))
    (ht₇ : t₇ ≤ C₇₇ * (m_edges + n + 1))
    (ht₉ : t₉ ≤ 16 * (p * n) + 8 + 1)
    (ht₁₀ : t₁₀ ≤ 18 * (p * n) + 17 + 1) :
    t₁ + (2 + (2 + (t₄ + (2 + (t₆ + (t₇ + (4 + (t₉ + t₁₀)))))))) ≤
      alg94BaseCost p l h n m_edges C₇₇ := by
  have h7 : C₇₇ * (m_edges + n + 1) = C₇₇ * m_edges + C₇₇ * (n + 1) := by
    rw [Nat.add_assoc, Nat.mul_add]
  rw [h7] at ht₇
  unfold alg94BaseCost
  generalize maxWallEncLen h n = mw at hlenW ⊢
  generalize p.choose 2 * (1 + l * (n + 1)) = psl at hlenStars ⊢
  generalize C₇₇ * m_edges = cm at ht₇ ⊢
  generalize C₇₇ * (n + 1) = cn at ht₇ ⊢
  generalize p * n = pn at ht₉ ht₁₀ ⊢
  omega

private lemma alg94_split22 {t₁ t₂ t₃ t₄ t₇ t₈ t₁₁ t₁₃ t₁₄ t₁₉ t₂₁ C1 C2 RHS : ℕ}
    (h1 : t₁ + (t₂ + (t₃ + (t₄ + (2 + (2 + (t₇ + (3 + (t₈ + 2)))))))) ≤ C1)
    (h2 : 2 + (t₁₁ + (2 + (t₁₃ + (t₁₄ + (3 + (1 + (3 + (3 + (4 + (t₁₉ + (2 + t₂₁))))))))))) ≤ C2)
    (hsum : C1 + C2 ≤ RHS) :
    t₁ + (t₂ + (t₃ + (t₄ + (2 + (2 + (t₇ +
      (3 + (t₈ + (2 + (2 + (t₁₁ + (2 + (t₁₃ + (t₁₄ + (3 +
        (1 + (3 + (3 + (4 + (t₁₉ + (2 + t₂₁))))))))))))))))))))) ≤ RHS := by
  have heq :
      t₁ + (t₂ + (t₃ + (t₄ + (2 + (2 + (t₇ +
        (3 + (t₈ + (2 + (2 + (t₁₁ + (2 + (t₁₃ + (t₁₄ + (3 +
          (1 + (3 + (3 + (4 + (t₁₉ + (2 + t₂₁))))))))))))))))))))) =
      (t₁ + (t₂ + (t₃ + (t₄ + (2 + (2 + (t₇ + (3 + (t₈ + 2))))))))) +
      (2 + (t₁₁ + (2 + (t₁₃ + (t₁₄ + (3 + (1 + (3 + (3 + (4 + (t₁₉ + (2 + t₂₁)))))))))))) := by
    simp only [Nat.add_assoc]
  rw [heq]
  exact le_trans (Nat.add_le_add h1 h2) hsum

private lemma alg94_part1_bound
    {t₁ t₂ t₃ t₄ t₇ t₈ lenG m_edges n t scanCost tsc eca ecm : ℕ}
    (ht₁ : t₁ ≤ 8 + 15 * lenG)
    (hlenG : lenG ≤ 2 + 3 * m_edges)
    (ht₂ : t₂ ≤ 8 + 15 * n)
    (ht₃ : t₃ ≤ 8 + 15 * n)
    (ht₄ : t₄ ≤ 187 + 23 * n + eca)
    (hb4 : eca ≤ ecm)
    (ht₇ : t₇ ≤ 11 + t + scanCost)
    (hscan : scanCost ≤ tsc)
    (ht₈ : t₈ ≤ 8 + 15 * (2 + 3 * m_edges)) :
    t₁ + (t₂ + (t₃ + (t₄ + (2 + (2 + (t₇ + (3 + (t₈ + 2)))))))) ≤
      239 + 30 * (2 + 3 * m_edges) + ecm + 53 * n + t + tsc := by
  omega

private lemma alg94_part2_bound
    {t₁₁ t₁₃ t₁₄ t₁₉ t₂₁ lenG' m_edges lenW mw lenND kmw c92m lenStarNew sl lenStarsCur pcsl : ℕ}
    (hlenG' : lenG' ≤ 2 + 3 * m_edges)
    (ht₁₁ : t₁₁ ≤ 34 * lenG' + 18 * lenW + 36)
    (hlenW : lenW ≤ mw)
    (ht₁₃ : t₁₃ ≤ (34 * lenG' + 34 * lenW) + 18 * lenND + 36)
    (hlenND : lenND ≤ kmw)
    (ht₁₄ : t₁₄ ≤ c92m)
    (ht₁₉ : t₁₉ ≤ 16 * lenStarNew + 8 + 1)
    (hlenStarNew : lenStarNew ≤ sl)
    (ht₂₁ : t₂₁ ≤ 34 * lenStarsCur + 18 * lenStarNew + 36)
    (hlenStarsCur : lenStarsCur ≤ pcsl) :
    2 + (t₁₁ + (2 + (t₁₃ + (t₁₄ + (3 + (1 + (3 + (3 + (4 + (t₁₉ + (2 + t₂₁))))))))))) ≤
      137 + 68 * (2 + 3 * m_edges) + 52 * mw + 18 * kmw + c92m + 34 * pcsl + 34 * sl := by
  omega

private lemma alg94_parts_sum
    {m_edges ecm n t tsc mw kmw c92m pcsl sl : ℕ} :
    (239 + 30 * (2 + 3 * m_edges) + ecm + 53 * n + t + tsc) +
      (137 + 68 * (2 + 3 * m_edges) + 52 * mw + 18 * kmw + c92m + 34 * pcsl + 34 * sl) ≤
    650 + 110 * (2 + 3 * m_edges) + ecm + 150 * n + 60 * t + tsc +
      60 * mw + 18 * kmw + c92m + 35 * pcsl + 34 * sl := by
  omega

private lemma alg94_step_bound_7a_star
    {p l h k t n m_edges B_arr C₉₂ : ℕ}
    {t₁ t₂ t₃ t₄ t₇ t₈ t₁₁ t₁₃ t₁₄ t₁₉ t₂₁ : ℕ}
    {lenG lenG' lenW lenND lenStarNew lenStarsCur scanCost m_act : ℕ}
    (ht₁ : t₁ ≤ 8 + 15 * lenG)
    (hlenG : lenG ≤ 2 + 3 * m_edges)
    (ht₂ : t₂ ≤ 8 + 15 * n)
    (ht₃ : t₃ ≤ 8 + 15 * n)
    (ht₄ : t₄ ≤ 187 + 23 * n +
      (291 + (isWallUnionEdgeExpr h (B_arr + 6) 16 (3 + 6) (3 + 7)).cost) * m_act)
    (hb4 : (291 + (isWallUnionEdgeExpr h (B_arr + 6) 16 (3 + 6) (3 + 7)).cost) * m_act ≤
      (291 + (isWallUnionEdgeExpr h (B_arr + 6) 16 (3 + 6) (3 + 7)).cost) * m_edges)
    (ht₇ : t₇ ≤ 11 + t + scanCost)
    (hscan : scanCost ≤ t * alg94ScanStepCost h n k (2 * m_edges) (2 * m_edges))
    (ht₈ : t₈ ≤ 8 + 15 * lenG')
    (hlenG' : lenG' ≤ 2 + 3 * m_edges)
    (ht₁₁ : t₁₁ ≤ 34 * lenG' + 18 * lenW + 36)
    (hlenW : lenW ≤ maxWallEncLen h n)
    (ht₁₃ : t₁₃ ≤ (34 * lenG' + 34 * lenW) + 18 * lenND + 36)
    (hlenND : lenND ≤ k * maxWallEncLen h n)
    (ht₁₄ : t₁₄ ≤ C₉₂ * (m_edges + n + 1))
    (ht₁₉ : t₁₉ ≤ 16 * lenStarNew + 8 + 1)
    (hlenStarNew : lenStarNew ≤ 1 + l * (n + 1))
    (ht₂₁ : t₂₁ ≤ 34 * lenStarsCur + 18 * lenStarNew + 36)
    (hlenStarsCur : lenStarsCur ≤ p.choose 2 * (1 + l * (n + 1))) :
    t₁ + (t₂ + (t₃ + (t₄ + (2 + (2 + (t₇ +
      (3 + (t₈ + (2 + (2 + (t₁₁ + (2 + (t₁₃ + (t₁₄ + (3 +
        (1 + (3 + (3 + (4 + (t₁₉ + (2 + t₂₁))))))))))))))))))))) ≤
      alg94IterStepCost p l h k t n m_edges B_arr C₉₂ := by
  unfold alg94IterStepCost
  generalize (isWallUnionEdgeExpr h (B_arr + 6) 16 (3 + 6) (3 + 7)).cost = ec at ht₄ hb4 ⊢
  generalize alg94ScanStepCost h n k (2 * m_edges) (2 * m_edges) = sc at hscan ⊢
  generalize maxWallEncLen h n = mw at hlenW hlenND ⊢
  generalize p.choose 2 = pc at hlenStarsCur ⊢
  have ht₈' : t₈ ≤ 8 + 15 * (2 + 3 * m_edges) := le_trans ht₈ (by omega)
  exact alg94_split22
    (alg94_part1_bound ht₁ hlenG ht₂ ht₃ ht₄ hb4 ht₇ hscan ht₈')
    (alg94_part2_bound hlenG' ht₁₁ hlenW ht₁₃ hlenND ht₁₄ ht₁₉ hlenStarNew ht₂₁ hlenStarsCur)
    alg94_parts_sum

private lemma alg94_step_bound_7a_clique
    {p l h k t n m_edges B_arr C₉₂ : ℕ}
    {t₁ t₂ t₃ t₄ t₇ t₈ t₁₁ t₁₃ t₁₄ : ℕ}
    {lenG lenG' lenW lenND scanCost m_act : ℕ}
    (ht₁ : t₁ ≤ 8 + 15 * lenG)
    (hlenG : lenG ≤ 2 + 3 * m_edges)
    (ht₂ : t₂ ≤ 8 + 15 * n)
    (ht₃ : t₃ ≤ 8 + 15 * n)
    (ht₄ : t₄ ≤ 187 + 23 * n +
      (291 + (isWallUnionEdgeExpr h (B_arr + 6) 16 (3 + 6) (3 + 7)).cost) * m_act)
    (hb4 : (291 + (isWallUnionEdgeExpr h (B_arr + 6) 16 (3 + 6) (3 + 7)).cost) * m_act ≤
      (291 + (isWallUnionEdgeExpr h (B_arr + 6) 16 (3 + 6) (3 + 7)).cost) * m_edges)
    (ht₇ : t₇ ≤ 11 + t + scanCost)
    (hscan : scanCost ≤ t * alg94ScanStepCost h n k (2 * m_edges) (2 * m_edges))
    (ht₈ : t₈ ≤ 8 + 15 * lenG')
    (hlenG' : lenG' ≤ 2 + 3 * m_edges)
    (ht₁₁ : t₁₁ ≤ 34 * lenG' + 18 * lenW + 36)
    (hlenW : lenW ≤ maxWallEncLen h n)
    (ht₁₃ : t₁₃ ≤ (34 * lenG' + 34 * lenW) + 18 * lenND + 36)
    (hlenND : lenND ≤ k * maxWallEncLen h n)
    (ht₁₄ : t₁₄ ≤ C₉₂ * (m_edges + n + 1)) :
    t₁ + (t₂ + (t₃ + (t₄ + (2 + (2 + (t₇ +
      (3 + (t₈ + (2 + (2 + (t₁₁ + (2 + (t₁₃ + (t₁₄ + (3 + (1 + 3)))))))))))))))) ≤
      alg94IterStepCost p l h k t n m_edges B_arr C₉₂ := by
  unfold alg94IterStepCost
  generalize (isWallUnionEdgeExpr h (B_arr + 6) 16 (3 + 6) (3 + 7)).cost = ec at ht₄ hb4 ⊢
  generalize alg94ScanStepCost h n k (2 * m_edges) (2 * m_edges) = sc at hscan ⊢
  generalize maxWallEncLen h n = mw at hlenW hlenND ⊢
  generalize 1 + l * (n + 1) = sl
  generalize p.choose 2 = pc
  omega

private lemma alg94_step_bound_7b
    {p l h k t n m_edges B_arr C₉₂ : ℕ}
    {t₁ t₂ t₃ t₄ t₇ t₈ t₁₁ t₁₂ : ℕ}
    {lenG scanCost m_act : ℕ}
    (ht₁ : t₁ ≤ 8 + 15 * lenG)
    (hlenG : lenG ≤ 2 + 3 * m_edges)
    (ht₂ : t₂ ≤ 8 + 15 * n)
    (ht₃ : t₃ ≤ 8 + 15 * n)
    (ht₄ : t₄ ≤ 187 + 23 * n +
      (291 + (isWallUnionEdgeExpr h (B_arr + 6) 16 (3 + 6) (3 + 7)).cost) * m_act)
    (hb4 : (291 + (isWallUnionEdgeExpr h (B_arr + 6) 16 (3 + 6) (3 + 7)).cost) * m_act ≤
      (291 + (isWallUnionEdgeExpr h (B_arr + 6) 16 (3 + 6) (3 + 7)).cost) * m_edges)
    (ht₇ : t₇ ≤ 11 + t + scanCost)
    (hscan : scanCost ≤ t * alg94ScanStepCost h n k (2 * m_edges) (2 * m_edges))
    (ht₈ : t₈ ≤ 8 + 15 * n)
    (ht₁₁ : t₁₁ ≤ 34 * n + 18 * t + 36)
    (ht₁₂ : t₁₂ ≤ 18 * (n + t) + 17 + 1) :
    t₁ + (t₂ + (t₃ + (t₄ + (2 + (2 + (t₇ +
      (3 + (t₈ + (2 + (2 + (t₁₁ + t₁₂))))))))))) ≤
      alg94IterStepCost p l h k t n m_edges B_arr C₉₂ := by
  unfold alg94IterStepCost
  generalize (isWallUnionEdgeExpr h (B_arr + 6) 16 (3 + 6) (3 + 7)).cost = ec at ht₄ hb4 ⊢
  generalize alg94ScanStepCost h n k (2 * m_edges) (2 * m_edges) = sc at hscan ⊢
  generalize maxWallEncLen h n = mw
  generalize 1 + l * (n + 1) = sl
  generalize p.choose 2 = pc
  omega

private lemma alg94_add22_assoc (t₁ t₂ t₃ t₄ t₇ t₈ t₁₁ t₁₃ t₁₄ t₁₉ t₂₁ t_rem : ℕ) :
    t₁ + (t₂ + (t₃ + (t₄ + (2 + (2 + (t₇ +
      (3 + (t₈ + (2 + (2 + (t₁₁ + (2 + (t₁₃ + (t₁₄ + (3 +
        (1 + (3 + (3 + (4 + (t₁₉ + (2 + (t₂₁ + t_rem)))))))))))))))))))))) =
    (t₁ + (t₂ + (t₃ + (t₄ + (2 + (2 + (t₇ +
      (3 + (t₈ + (2 + (2 + (t₁₁ + (2 + (t₁₃ + (t₁₄ + (3 +
        (1 + (3 + (3 + (4 + (t₁₉ + (2 + t₂₁)))))))))))))))))))))) + t_rem := by
  simp only [Nat.add_assoc]

private lemma alg94_step_add_rem_le (step base rem : ℕ) :
    step + (base + rem * step) ≤ base + (rem + 1) * step := by
  rw [Nat.add_one_mul]
  omega

private lemma alg94_total_bound {t₁ t₂ t₃ t₄ t₇ t₈ t₁₁ t₁₃ t₁₄ t₁₉ t₂₁ t_rem base step rem : ℕ}
    (hstep :
      t₁ + (t₂ + (t₃ + (t₄ + (2 + (2 + (t₇ +
        (3 + (t₈ + (2 + (2 + (t₁₁ + (2 + (t₁₃ + (t₁₄ + (3 +
          (1 + (3 + (3 + (4 + (t₁₉ + (2 + t₂₁))))))))))))))))))))) ≤ step)
    (hrem : t_rem ≤ base + rem * step) :
    t₁ + (t₂ + (t₃ + (t₄ + (2 + (2 + (t₇ +
      (3 + (t₈ + (2 + (2 + (t₁₁ + (2 + (t₁₃ + (t₁₄ + (3 +
        (1 + (3 + (3 + (4 + (t₁₉ + (2 + (t₂₁ + t_rem)))))))))))))))))))))) ≤
      base + (rem + 1) * step := by
  rw [alg94_add22_assoc]
  exact le_trans (Nat.add_le_add hstep hrem) (alg94_step_add_rem_le step base rem)

private lemma alg94_single_bound {t_step base step rem : ℕ}
    (hstep : t_step ≤ step) :
    t_step ≤ base + (rem + 1) * step := by
  rw [Nat.add_one_mul]
  omega

set_option maxHeartbeats 2000000 in
theorem alg94IterProg_exec {w p l m h k r t B_arr B_reg C₇₇ C₉₂ : ℕ}
    {P77 P92 : Cmd}
    (h2 : 2 ≤ h) (he : Even h) (hl3 : 3 ≤ l)
    (hB_arr : 50 ≤ B_arr)
    (_hB_arr77 : folioCallerArrBase P77 ≤ B_arr)
    (hB_arr92 : folioCallerArrBase P92 ≤ B_arr)
    (hB_reg : 30 ≤ B_reg)
    (hB_reg77 : folioCallerRegBase P77 ≤ B_reg)
    (hB_reg92 : folioCallerRegBase P92 ≤ B_reg)
    (x : Alg94Input p t h k r)
    (hexec77 : ∀ (x77 : Alg77Input p l m),
      x77.n = x.n → x77.G.numEdges ≤ x.G.numEdges →
      ∀ (s : State), s.arrs inArr = encAlg77In x77 →
      ∃ (s' : State) (time : ℕ),
        Exec w P77 s s' time ∧
        time ≤ C₇₇ * alg77Size x77 ∧
        IsAlg77Output p x77 (s'.arrs outArr) ∧
        (∀ r : Reg, folioCallerRegBase P77 ≤ r → s'.regs r = s.regs r) ∧
        (∀ a : Arr, folioCallerArrBase P77 ≤ a → s'.arrs a = s.arrs a))
    (hexec92 : ∀ (x92 : Alg92Input l m p h k r),
      x92.n = x.n → x92.G.numEdges ≤ x.G.numEdges →
      ∀ (s : State), s.arrs inArr = encAlg92In x92 →
      ∃ (s' : State) (time : ℕ),
        Exec w P92 s s' time ∧
        time ≤ C₉₂ * alg92Size x92 ∧
        IsAlg92Output l m p x92 (s'.arrs outArr) ∧
        (∀ r : Reg, folioCallerRegBase P92 ≤ r → s'.regs r = s.regs r) ∧
        (∀ a : Arr, folioCallerArrBase P92 ≤ a → s'.arrs a = s.arrs a))
    (hw_bound :
      (2 + 3 * x.G.numActivePairs) +
      (t + k + 2) * maxWallEncLen h x.n +
      (p.choose 2 + 2) * (1 + l * (x.n + 1)) +
      (2 + 2 * (completeGraphEdges p).length + p * x.n) +
      3 + 2 * elemWallNumVerts h + h + x.n + 2 * x.G.numEdges < 2 ^ w)
    (rem idx : ℕ) (hrem : idx + rem = p.choose 2)
    (centers : Fin idx → Fin x.n)
    (rays : Fin idx → Fin l → List (Fin x.n))
    (hcenters_inj : Function.Injective centers)
    (hrays : ∀ a i, x.W.IsStarRay (centers a) (rays a i))
    (hrays_meet : ∀ a, ∀ i j : Fin l, i ≠ j → ∀ v, v ∈ rays a i → v ∈ rays a j → v = centers a)
    (hends_dist : ∀ a, ∀ i j : Fin l, i ≠ j → ∀ u v,
      (rays a i).getLast? = some u → (rays a j).getLast? = some v → m ≤ x.W.brickDist u v)
    {s : State}
    (hr_n : s.regs B_reg = x.n)
    (harrG : s.arrs B_arr = x.G.enc)
    (harrW : s.arrs (B_arr + 1) = x.W.encList)
    (hWV : IsBitSet x.W.vertexFinset (B_arr + 2) s)
    (harrSub : s.arrs (B_arr + 3) = (List.finRange t).flatMap (fun j => (x.W_sub j).encList))
    (hX : IsBitSet (Finset.univ.image centers) (B_arr + 4) s)
    (harrStars : s.arrs (B_arr + 5) =
      (List.finRange idx).flatMap (fun a => (centers a).1 :: encHPaths (rays a)))
    (hsucc : IsWallSuccArrs x.W (B_arr + 6) s) :
    ∃ s' time,
      Exec w (alg94IterProg p h k t B_arr B_reg P77 P92 rem idx) s s' time ∧
      time ≤ alg94BaseCost p l h x.n x.G.numEdges C₇₇ +
        rem * alg94IterStepCost p l h k t x.n x.G.numEdges B_arr C₉₂ ∧
      IsAlg94Output p t k x (s'.arrs outArr) := by
  have hw3 : 3 < 2 ^ w := by omega
  have hw1 : 1 < 2 ^ w := by omega
  have h0_w : 0 < 2 ^ w := by omega
  have hn_w : x.n < 2 ^ w := by omega
  have hn1_w : x.n + 1 < 2 ^ w := by omega
  have hh_w : h < 2 ^ w := by omega
  have hc2_w : 3 + 2 * elemWallNumVerts h < 2 ^ w := by omega
  have he_w : x.G.numEdges < 2 ^ w := by omega
  have hm3_w : 2 + 3 * x.G.numActivePairs < 2 ^ w := by omega
  have hm_w : x.G.numActivePairs < 2 ^ w := by omega
  have hinArr : (inArr : ℕ) < 1 := by decide
  have hmax_pos : 1 ≤ maxWallEncLen h x.n := maxWallEncLen_pos h x.n
  have hG_len : x.G.enc.length = 2 + 3 * x.G.numActivePairs := MultiDigraph.length_enc x.G
  have hG_enc_w : ∀ v ∈ x.G.enc, v < 2 ^ w := all_lt_enc_multiDigraph x.G hn_w hm_w he_w
  have hW_len_le : x.W.encList.length ≤ maxWallEncLen h x.n := by
    have h1 := Alg91.length_encList_le_of_isValid x.hW_valid.2.2
    have h2 := length_elemWallEdges_le h
    unfold maxWallEncLen; omega
  have hmax1_le : maxWallEncLen h x.n ≤ (t + k + 2) * maxWallEncLen h x.n := by
    have : 1 * maxWallEncLen h x.n ≤ (t + k + 2) * maxWallEncLen h x.n :=
      Nat.mul_le_mul_right _ (by omega)
    omega
  have hW_len_w : x.W.encList.length < 2 ^ w := by omega
  have hW_enc_w : ∀ v ∈ x.W.encList, v < 2 ^ w :=
    all_lt_encList_of_isValid x.W x.hW_valid.2.2 le_rfl hh_w hc2_w hn_w
  have he_le_m : x.G.numActivePairs ≤ x.G.numEdges := Alg91.numActivePairs_le_numEdges x.G
  have hG_len_le : x.G.enc.length ≤ 2 + 3 * x.G.numEdges := by omega
  induction rem generalizing idx s with
  | zero =>
    have hidx_eq : idx = p.choose 2 := by omega
    subst hidx_eq
    let stars_flat :=
      (List.finRange (p.choose 2)).flatMap (fun a => (centers a).1 :: encHPaths (rays a))
    have hstars_len_le : stars_flat.length ≤ p.choose 2 * (1 + l * (x.n + 1)) := by
      have hbound : ∀ xs : List (Fin (p.choose 2)),
          (xs.flatMap (fun a => (centers a).1 :: encHPaths (rays a))).length ≤
            xs.length * (1 + l * (x.n + 1)) := by
        intro xs
        induction xs with
        | nil => simp
        | cons a xs ih =>
          simp only [List.flatMap_cons, List.length_append]
          have ha := (length_star_enc_le (hrays a)).1
          have hcons : (a :: xs).length = xs.length + 1 := rfl
          rw [hcons, Nat.add_one_mul]; omega
      simpa [stars_flat] using hbound (List.finRange (p.choose 2))
    have hstars_enc_w : ∀ v ∈ stars_flat, v < 2 ^ w := by
      intro v hv
      dsimp [stars_flat] at hv
      rw [List.mem_flatMap] at hv
      rcases hv with ⟨a, _, hva⟩
      exact (length_star_enc_le (hrays a)).2 w hw1 hn1_w v hva
    have hGW_stars_w :
        x.G.enc.length + x.W.encList.length + stars_flat.length < 2 ^ w := by
      have h1 : 1 * maxWallEncLen h x.n ≤ (t + k + 2) * maxWallEncLen h x.n :=
        Nat.mul_le_mul_right _ (by omega)
      have h2 : p.choose 2 * (1 + l * (x.n + 1)) ≤
          (p.choose 2 + 2) * (1 + l * (x.n + 1)) :=
        Nat.mul_le_mul_right _ (by omega)
      omega
    -- 1. copyArrLoopProg B_arr inArr 14 15
    rcases copyArrLoopProg_exec B_arr inArr 14 15
        (ne_arr_of_ne (by dsimp [inArr]; omega)) (by decide) hw1 s
        (by rw [harrG]; omega) (by rw [harrG]; exact hG_enc_w) with
      ⟨s₁, t₁, hex₁, ht₁, hin₁, harr₁, hreg₁⟩
    rw [harrG] at hin₁ ht₁
    -- 2. reg 14 := len inArr, reg 15 := len (B_arr + 1)
    let s₂ := s₁.setReg 14 x.G.enc.length
    have hex₂ : Exec w (.assign 14 (.len inArr)) s₁ s₂ 2 :=
      .assign (by
        have hlen_w : x.G.enc.length < 2 ^ w := by omega
        simp only [Expr.eval, checkWord, hin₁, hlen_w, ↓reduceIte])
    have harrW_2 : s₂.arrs (B_arr + 1) = x.W.encList := by
      simp only [s₂, State.setReg_arrs]
      rw [harr₁ (B_arr + 1) (ne_arr_of_ne (by dsimp [inArr]; omega)), harrW]
    let s₃ := s₂.setReg 15 x.W.encList.length
    have hex₃ : Exec w (.assign 15 (.len (B_arr + 1))) s₂ s₃ 2 :=
      .assign (by simp [Expr.eval, checkWord, harrW_2, hW_len_w])
    -- 3. appendArrProg inArr (B_arr + 1) 30 14 15 20
    rcases appendArrProg_exec (s := s₃) inArr (B_arr + 1) 30 14 15 20
        (by dsimp [inArr]; omega) (by decide) (by omega)
        (by decide) (by decide) (by decide)
        x.G.enc x.W.encList hG_enc_w hW_enc_w hw1 (by omega)
        (by exact hin₁) (by exact harrW_2)
        rfl rfl with
      ⟨s₄, t₄, hex₄, ht₄, hin₄, hr14_4, harr₄, hreg₄⟩
    -- 4. reg 15 := len (B_arr + 5)
    have harrStars_4 : s₄.arrs (B_arr + 5) = stars_flat := by
      rw [harr₄ (B_arr + 5) (by dsimp [inArr]; omega) (by omega)]
      simp only [s₃, s₂, State.setReg_arrs]
      rw [harr₁ (B_arr + 5) (ne_arr_of_ne (by dsimp [inArr]; omega)), harrStars]
    let s₅ := s₄.setReg 15 stars_flat.length
    have hex₅ : Exec w (.assign 15 (.len (B_arr + 5))) s₄ s₅ 2 :=
      .assign (by simp [Expr.eval, checkWord, harrStars_4, show stars_flat.length < 2 ^ w by omega])
    -- 5. appendArrProg inArr (B_arr + 5) 30 14 15 20
    have hGW_enc_w : ∀ v ∈ x.G.enc ++ x.W.encList, v < 2 ^ w := by
      intro v hv
      rw [List.mem_append] at hv
      rcases hv with hv | hv
      · exact hG_enc_w v hv
      · exact hW_enc_w v hv
    rcases appendArrProg_exec (s := s₅) inArr (B_arr + 5) 30 14 15 20
        (by dsimp [inArr]; omega) (by decide) (by omega)
        (by decide) (by decide) (by decide)
        (x.G.enc ++ x.W.encList) stars_flat hGW_enc_w hstars_enc_w hw1
        (by rw [List.length_append]; omega)
        (by exact hin₄) (by exact harrStars_4)
        (by rw [List.length_append]; exact hr14_4) rfl with
      ⟨s₆, t₆, hex₆, ht₆, hin₆, _, harr₆, hreg₆⟩
    -- 6. Call P77
    let x77 : Alg77Input p l m :=
      { n := x.n
        h := h
        G := x.G
        W := x.W
        centers := centers
        rays := rays
        hW_valid := x.hW_valid
        hcenters := hcenters_inj
        hrays := hrays
        hrays_meet := hrays_meet
        hends_dist := hends_dist }
    rcases hexec77 x77 rfl le_rfl s₆ hin₆ with ⟨s₇, t₇, hex₇, ht₇, hout₇, hreg₇, _⟩
    rcases hout₇ with ⟨M, hM_out⟩
    obtain ⟨preM, hM_split, hpreM_len⟩ := encUnderlyingGraphModel_split M
    -- 7. reg 14 := p * reg B_reg
    have hrB_7 : s₇.regs B_reg = x.n := by
      rw [hreg₇ B_reg hB_reg77,
        hreg₆ B_reg (Or.inr (by omega)) (by omega)]
      dsimp [s₅]
      rw [State.setReg_regs_ne _ _ (by omega : (B_reg : Reg) ≠ 15),
        hreg₄ B_reg (Or.inr (by omega)) (by omega)]
      dsimp [s₃, s₂]
      rw [State.setReg_regs_ne _ _ (by omega : (B_reg : Reg) ≠ 15),
        State.setReg_regs_ne _ _ (by omega : (B_reg : Reg) ≠ 14),
        hreg₁ B_reg (ne_reg_of_ne (by omega)) (ne_reg_of_ne (by omega)), hr_n]
    have hp_w : p < 2 ^ w := by
      have : p ≤ 2 + 2 * (completeGraphEdges p).length + p * x.n := by
        have hpos : 1 ≤ x.n := (x.W.branchVert (elemWallMiddle₁Idx x.hW_valid.1)).pos
        have : p * 1 ≤ p * x.n := Nat.mul_le_mul_left p hpos
        omega
      omega
    have hpn_w : p * x.n < 2 ^ w := by omega
    let s₈ := s₇.setReg 14 (p * x.n)
    have hex₈ : Exec w (.assign 14 (.op .mul (.const p) (.reg B_reg))) s₇ s₈ 4 :=
      .assign (by simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hrB_7, hp_w, hn_w, hpn_w])
    -- 8. readSliceProg outArr (2 + 2 * (completeGraphEdges p).length) 26 (reg 14) 20
    let K := fun u : Fin p => (M.vertMap u).verts
    have hK_len : (encBitSetsUpTo K p).length = p * x.n := length_encBitSetsUpTo K p le_rfl
    have hK_w : ∀ v ∈ encBitSetsUpTo K p, v < 2 ^ w := all_lt_encBitSetsUpTo K hw1 p le_rfl
    have hhdr_w : 2 + 2 * (completeGraphEdges p).length < 2 ^ w := by omega
    rcases readSliceProg_exec_full (s := s₈) outArr 26
        (.const (2 + 2 * (completeGraphEdges p).length)) 14 20
        (by decide) (by decide) preM (encBitSetsUpTo K p) []
        hpreM_len hK_len hK_w hw1 (by omega)
        (by simp [Expr.eval, checkWord, hhdr_w])
        (by change s₇.arrs outArr = _; rw [hM_out, hM_split]; rfl)
        (by simp [s₈]) with
      ⟨s₉, t₉, hex₉, ht₉, harr26_9, _, hreg₉⟩
    -- 9. prependWordProg (.const 0) 26 outArr 14 20
    have hr14_9 : s₉.regs 14 = (encBitSetsUpTo K p).length := by
      rw [hreg₉ 14 (Or.inl (by decide)), hK_len]; simp [s₈]
    rcases prependWordProg_exec (tag := 0) (.const 0) 26 outArr 14 20
        (by decide) (by decide) (encBitSetsUpTo K p) hK_w hw1
        (by rw [hK_len]; omega)
        (fun _ => by simp [Expr.eval, checkWord, h0_w])
        harr26_9 hr14_9 with
      ⟨s₁₀, t₁₀, hex₁₀, ht₁₀, hout₁₀, _, _⟩
    dsimp [Expr.cost] at ht₉ ht₁₀
    rw [hK_len] at ht₁₀
    rw [List.length_append, Nat.mul_add] at ht₆
    have ht_bound :
        t₁ + (2 + (2 + (t₄ + (2 + (t₆ + (t₇ + (4 + (t₉ + t₁₀)))))))) ≤
          alg94BaseCost p l h x.n x.G.numEdges C₇₇ :=
      alg94_base_bound ht₁ hG_len_le ht₄ hW_len_le ht₆ hstars_len_le ht₇ ht₉ ht₁₀
    refine ⟨s₁₀,
      t₁ + (2 + (2 + (t₄ + (2 + (t₆ + (t₇ + (4 + (t₉ + t₁₀)))))))),
      .seq hex₁ (.seq hex₂ (.seq hex₃ (.seq hex₄ (.seq hex₅
        (.seq hex₆ (.seq hex₇ (.seq hex₈ (.seq hex₉ hex₁₀)))))))),
      by simpa using ht_bound,
      .inl ⟨K, hout₁₀, M.to_isCliqueModel⟩⟩
  | succ rem ih =>
    let X : Finset (Fin x.n) := Finset.univ.image centers
    let G' := WallOfHeight.wallUnionMultiDigraph x.G X x.W
    let lists' := edgeNeighbors (edgeListOf G'.toSimpleGraph)
    let exprCost := (isWallUnionEdgeExpr h (B_arr + 6) 16 (3 + 6) (3 + 7)).cost
    let W' := x.W.castGraph G'
    let W_sub' := fun j : Fin t => (x.W_sub j).castGraph G'
    have hW'_valid : W'.IsValid :=
      WallOfHeight.isValid_castGraph_wallUnionMultiDigraph X x.hW_valid.2.2
    have hsub' : ∀ j : Fin t, (W_sub' j).IsSubwallOf W' :=
      fun j => isSubwallOf_castGraph (x.hsub j)
    have hX_w : ∀ v ∈ s.arrs (B_arr + 4), v < 2 ^ w := hX.all_lt hw1
    have hWV_w : ∀ v ∈ s.arrs (B_arr + 2), v < 2 ^ w := hWV.all_lt hw1
    -- 1. copyArrLoopProg B_arr 9 14 15
    rcases copyArrLoopProg_exec B_arr 9 14 15
        (ne_arr_of_ne (by omega)) (by decide) hw1 s
        (by rw [harrG]; omega) (by rw [harrG]; exact hG_enc_w) with
      ⟨s₁, t₁, hex₁, ht₁, harr9_1, harr₁, hreg₁⟩
    rw [harrG] at harr9_1 ht₁
    -- 2. copyArrLoopProg (B_arr + 4) 16 14 15
    have harrX_1 : s₁.arrs (B_arr + 4) = s.arrs (B_arr + 4) :=
      harr₁ (B_arr + 4) (ne_arr_of_ne (by omega))
    rcases copyArrLoopProg_exec (B_arr + 4) 16 14 15
        (ne_arr_of_ne (by omega)) (by decide) hw1 s₁
        (by rw [harrX_1, hX.1]; exact hn_w) (by rw [harrX_1]; exact hX_w) with
      ⟨s₂, t₂, hex₂, ht₂, harr16_2, harr₂, hreg₂⟩
    rw [harrX_1, hX.1] at ht₂
    have hX_2 : IsBitSet X 16 s₂ := hX.of_arr_eq' (harr16_2.trans harrX_1)
    -- 3. copyArrLoopProg (B_arr + 2) 11 14 15
    have harrWV_2 : s₂.arrs (B_arr + 2) = s.arrs (B_arr + 2) := by
      rw [harr₂ (B_arr + 2) (ne_arr_of_ne (by omega)),
        harr₁ (B_arr + 2) (ne_arr_of_ne (by omega))]
    rcases copyArrLoopProg_exec (B_arr + 2) 11 14 15
        (ne_arr_of_ne (by omega)) (by decide) hw1 s₂
        (by rw [harrWV_2, hWV.1]; exact hn_w) (by rw [harrWV_2]; exact hWV_w) with
      ⟨s₃, t₃, hex₃, ht₃, harr11_3, harr₃, hreg₃⟩
    rw [harrWV_2, hWV.1] at ht₃
    have hWV_3 : IsBitSet x.W.vertexFinset 11 s₃ := hWV.of_arr_eq' (harr11_3.trans harrWV_2)
    -- 4. buildWallUnionCsrProg h (B_arr + 6)
    have harr9_3 : s₃.arrs 9 = x.G.enc := by
      rw [harr₃ 9 (ne_arr_of_ne (by decide)), harr₂ 9 (ne_arr_of_ne (by decide)), harr9_1]
    have hX_3 : IsBitSet X 16 s₃ := hX_2.of_arr_eq (harr₃ 16 (ne_arr_of_ne (by decide)))
    have hsucc_3 : IsWallSuccArrs x.W (B_arr + 6) s₃ :=
      hsucc.of_arrs_eq (fun k => by
        rw [harr₃ (B_arr + 6 + k.1) (ne_arr_of_ne (by omega)),
          harr₂ (B_arr + 6 + k.1) (ne_arr_of_ne (by omega)),
          harr₁ (B_arr + 6 + k.1) (ne_arr_of_ne (by omega))])
    rcases buildWallUnionCsrProg_exec x.G X x.W x.hW_valid.2.2 (B_arr + 6) (by omega)
        hw3 hn1_w hm3_w he_w harr9_3 hX_3 hsucc_3 with
      ⟨s₄, t₄, hex₄, ht₄, harr23_4, hadj₄, hent₄, htot₄, harr₄, hreg₄⟩
    -- 5. reg 1 := reg B_reg, reg 2 := len 22
    have hrB_4 : s₄.regs B_reg = x.n := by
      rw [hreg₄ B_reg (Or.inr (by omega)),
        hreg₃ B_reg (ne_reg_of_ne (by omega)) (ne_reg_of_ne (by omega)),
        hreg₂ B_reg (ne_reg_of_ne (by omega)) (ne_reg_of_ne (by omega)),
        hreg₁ B_reg (ne_reg_of_ne (by omega)) (ne_reg_of_ne (by omega)), hr_n]
    let cap := (s₄.arrs 22).length
    have hcap_eq_tot : totalAdjEntries lists' = cap := by
      dsimp [cap]; rw [htot₄, hent₄]
    have hG'_edges_le : G'.numEdges ≤ x.G.numEdges :=
      WallOfHeight.wallUnionMultiDigraph_numEdges_le x.G X x.W
    have hcap_le_2m : cap ≤ 2 * x.G.numEdges := by
      have hcard_le := le_trans (edgeFinset_card_toSimpleGraph_le_numEdges G') hG'_edges_le
      dsimp [cap]
      rw [hent₄]
      exact Nat.mul_le_mul_left 2 hcard_le
    have hcap_w : cap < 2 ^ w := Nat.lt_of_le_of_lt hcap_le_2m (by omega)
    let s₅ := s₄.setReg 1 x.n
    have hex₅ : Exec w (.assign 1 (.reg B_reg)) s₄ s₅ 2 :=
      .assign (by simp [Expr.eval, checkWord, hrB_4, hn_w])
    let s₆ := s₅.setReg 2 cap
    have hex₆ : Exec w (.assign 2 (.len 22)) s₅ s₆ 2 :=
      .assign (by simp [Expr.eval, checkWord, s₅, cap, hcap_w])
    -- 6. alg94ScanSubwallsProg h (B_arr + 3) k t
    have hWV_6 : IsBitSet W'.vertexFinset 11 s₆ := by
      have h11 : s₆.arrs 11 = s₃.arrs 11 := by
        simp only [s₆, s₅, State.setReg_arrs]
        exact harr₄ 11 (by decide) (by decide) (by decide) (by decide) (by decide)
          (by decide) (by decide)
      rw [show W'.vertexFinset = x.W.vertexFinset from WallOfHeight.castGraph_vertexFinset x.W G']
      exact hWV_3.of_arr_eq h11
    have harrSub_6 :
        s₆.arrs (B_arr + 3) = (List.finRange t).flatMap (fun j => (W_sub' j).encList) := by
      simp only [s₆, s₅, State.setReg_arrs]
      rw [harr₄ (B_arr + 3) (by omega) (by omega) (by omega) (by omega) (by omega)
        (by omega) (by omega),
        harr₃ (B_arr + 3) (ne_arr_of_ne (by omega)),
        harr₂ (B_arr + 3) (ne_arr_of_ne (by omega)),
        harr₁ (B_arr + 3) (ne_arr_of_ne (by omega)), harrSub]
      rfl
    rcases alg94ScanSubwallsProg_exec (w := w) (k := k) (s := s₆) G' lists' W' W_sub' h2 he hW'_valid hsub'
        (B_arr + 3) (by omega) cap
        (by omega) (by omega)
        (hadj₄.of_arrs_eq rfl rfl rfl)
        hcap_w
        hWV_6 harrSub_6
        (by simp [s₆, s₅]) (by simp [s₆]) with
      ⟨s₇, t₇, hex₇, ht₇, harr18_7, harr24_7, hr15_7, _, harr₇, hreg₇⟩
    have hstep_cost_le :
        t * alg94ScanStepCost h x.n k cap (totalAdjEntries lists') ≤
          t * alg94ScanStepCost h x.n k (2 * x.G.numEdges) (2 * x.G.numEdges) := by
      apply Nat.mul_le_mul_left t
      unfold alg94ScanStepCost
      have h1 : 89 * cap ≤ 89 * (2 * x.G.numEdges) := Nat.mul_le_mul_left 89 hcap_le_2m
      have h2 : 88 * totalAdjEntries lists' ≤ 88 * (2 * x.G.numEdges) := by
        rw [hcap_eq_tot]; exact Nat.mul_le_mul_left 88 hcap_le_2m
      omega
    -- Preserve key registers and arrays at s₇
    have hrB_7 : s₇.regs B_reg = x.n := by
      rw [hreg₇ B_reg (Or.inr (by omega))]
      simp only [s₆, s₅]
      rw [State.setReg_regs_ne _ _ (by omega : (B_reg : Reg) ≠ 2),
        State.setReg_regs_ne _ _ (by omega : (B_reg : Reg) ≠ 1), hrB_4]
    have harrB_7 : ∀ d : ℕ, s₇.arrs (B_arr + d) = s.arrs (B_arr + d) := by
      intro d
      rw [harr₇ (B_arr + d) (Or.inr (by omega))]
      simp only [s₆, s₅, State.setReg_arrs]
      rw [harr₄ (B_arr + d) (by omega) (by omega) (by omega) (by omega) (by omega)
        (by omega) (by omega),
        harr₃ (B_arr + d) (ne_arr_of_ne (by omega)),
        harr₂ (B_arr + d) (ne_arr_of_ne (by omega)),
        harr₁ (B_arr + d) (ne_arr_of_ne (by omega))]
    have harr23_7 : s₇.arrs 23 = G'.enc := by
      rw [harr₇ 23 (Or.inl ⟨by decide, by decide⟩)]
      exact harr23_4
    -- 7. Branch on reg 15 < t - k
    let div_cnt := (divIndicesUpTo W' W_sub' t).length
    let nd_cnt := (nonDivIndicesUpTo W' W_sub' t).length
    have hsum_cnt : div_cnt + nd_cnt = t :=
      divIndicesUpTo_add_nonDivIndicesUpTo W' W_sub' t le_rfl
    have ht_le_max : t ≤ (t + k + 2) * maxWallEncLen h x.n := by
      calc t ≤ t + k + 2 := by omega
        _ = (t + k + 2) * 1 := (Nat.mul_one _).symm
        _ ≤ (t + k + 2) * maxWallEncLen h x.n := Nat.mul_le_mul_left _ hmax_pos
    have ht_w : t < 2 ^ w := by omega
    have hdiv_w : div_cnt < 2 ^ w := by omega
    have htk_w : t - k < 2 ^ w := by omega
    by_cases hlt : div_cnt < t - k
    · -- Case 7a: div_cnt < t - k, so k ≤ nd_cnt
      have hk_le_nd : k ≤ nd_cnt := by omega
      have heval_lt : Expr.eval w s₇ (.op .lt (.reg 15) (.const (t - k))) = some 1 := by
        simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hr15_7, div_cnt, hdiv_w, htk_w, hlt, hw1]
      have hm'_le : G'.numActivePairs ≤ x.G.numActivePairs :=
        numActivePairs_wallUnionMultiDigraph_le x.G X x.W
      have hG'_len : G'.enc.length = 2 + 3 * G'.numActivePairs := MultiDigraph.length_enc G'
      have hG'_len_le : G'.enc.length ≤ 2 + 3 * x.G.numEdges := by omega
      have hG'_enc_w : ∀ v ∈ G'.enc, v < 2 ^ w :=
        all_lt_enc_multiDigraph G' hn_w (by omega) (by omega)
      -- 7a.1: copyArrLoopProg 23 inArr 14 15
      rcases copyArrLoopProg_exec 23 inArr 14 15
          (by decide) (by decide) hw1 s₇
          (by rw [harr23_7]; omega) (by rw [harr23_7]; exact hG'_enc_w) with
        ⟨s₈, t₈, hex₈, ht₈, hin₈, harr₈, hreg₈⟩
      rw [harr23_7] at hin₈ ht₈
      -- 7a.2: reg 14 := len inArr, reg 15 := len (B_arr + 1)
      let s₉ := s₈.setReg 14 G'.enc.length
      have hex₉ : Exec w (.assign 14 (.len inArr)) s₈ s₉ 2 :=
        .assign (by
          have hlen_w : G'.enc.length < 2 ^ w := by omega
          simp only [Expr.eval, checkWord, hin₈, hlen_w, ↓reduceIte])
      have harrW_9 : s₉.arrs (B_arr + 1) = x.W.encList := by
        simp only [s₉, State.setReg_arrs]
        rw [harr₈ (B_arr + 1) (ne_arr_of_ne (by dsimp [inArr]; omega)), harrB_7 1, harrW]
      let s₁₀ := s₉.setReg 15 x.W.encList.length
      have hex₁₀ : Exec w (.assign 15 (.len (B_arr + 1))) s₉ s₁₀ 2 :=
        .assign (by simp [Expr.eval, checkWord, harrW_9, hW_len_w])
      -- 7a.3: appendArrProg inArr (B_arr + 1) 30 14 15 20
      rcases appendArrProg_exec (s := s₁₀) inArr (B_arr + 1) 30 14 15 20
          (by dsimp [inArr]; omega) (by decide) (by omega)
          (by decide) (by decide) (by decide)
          G'.enc x.W.encList hG'_enc_w hW_enc_w hw1
          (by omega)
          (by exact hin₈) (by exact harrW_9)
          rfl rfl with
        ⟨s₁₁, t₁₁, hex₁₁, ht₁₁, hin₁₁, hr14_11, harr₁₁, hreg₁₁⟩
      -- 7a.4: reg 15 := len 24
      have harr24_11 : s₁₁.arrs 24 = nonDivEncUpTo W' W_sub' k t := by
        rw [harr₁₁ 24 (by decide) (by decide)]
        exact (harr₈ 24 (by decide)).trans harr24_7
      have hnd_len_le : (nonDivEncUpTo W' W_sub' k t).length ≤ k * maxWallEncLen h x.n := by
        have hlen := length_nonDivEncUpTo_le W' hW'_valid W_sub' hsub' k t
        have htake : ((nonDivIndicesUpTo W' W_sub' t).take k).length ≤ k := List.length_take_le k _
        exact le_trans hlen (Nat.mul_le_mul_right _ htake)
      have hnd_enc_w : ∀ v ∈ nonDivEncUpTo W' W_sub' k t, v < 2 ^ w := by
        intro v hv
        unfold nonDivEncUpTo at hv
        rw [List.mem_flatMap] at hv
        rcases hv with ⟨idx_sub, _, hv_idx⟩
        exact all_lt_encList_of_isValid (W_sub' idx_sub)
          (W'.isValid_of_isSubwallOf hW'_valid (hsub' idx_sub)) (le_of_isSubwallOf (hsub' idx_sub))
          hh_w hc2_w hn_w v hv_idx
      have hGW'_nd_w :
          G'.enc.length + x.W.encList.length + (nonDivEncUpTo W' W_sub' k t).length < 2 ^ w := by
        have : (1 + k) * maxWallEncLen h x.n ≤ (t + k + 2) * maxWallEncLen h x.n :=
          Nat.mul_le_mul_right _ (by omega)
        rw [Nat.add_mul, Nat.one_mul] at this
        omega
      let s₁₂ := s₁₁.setReg 15 (nonDivEncUpTo W' W_sub' k t).length
      have hex₁₂ : Exec w (.assign 15 (.len 24)) s₁₁ s₁₂ 2 :=
        .assign (by simp [Expr.eval, checkWord, harr24_11,
          show (nonDivEncUpTo W' W_sub' k t).length < 2 ^ w by omega])
      -- 7a.5: appendArrProg inArr 24 30 14 15 20
      have hGW'_enc_w : ∀ v ∈ G'.enc ++ x.W.encList, v < 2 ^ w := by
        intro v hv
        rw [List.mem_append] at hv
        rcases hv with hv | hv
        · exact hG'_enc_w v hv
        · exact hW_enc_w v hv
      rcases appendArrProg_exec (s := s₁₂) inArr 24 30 14 15 20
          (by decide) (by decide) (by decide)
          (by decide) (by decide) (by decide)
          (G'.enc ++ x.W.encList) (nonDivEncUpTo W' W_sub' k t) hGW'_enc_w hnd_enc_w hw1
          (by rw [List.length_append]; exact hGW'_nd_w)
          (by exact hin₁₁) (by exact harr24_11)
          (by rw [List.length_append]; exact hr14_11) rfl with
        ⟨s₁₃, t₁₃, hex₁₃, ht₁₃, hin₁₃, _, harr₁₃, hreg₁₃⟩
      rw [List.length_append, Nat.mul_add] at ht₁₃
      -- 7a.6: Call P92
      let idx_nd := nonDivSubwallIdx W' W_sub' hk_le_nd
      have hdist_W' : ∀ i j : Fin t, i ≠ j →
          ∀ u ∈ (W_sub' i).vertexFinset, ∀ v ∈ (W_sub' j).vertexFinset,
            r ≤ W'.brickDist u v := by
        intro i j hij u hu v hv
        rw [show (W_sub' i).vertexFinset = (x.W_sub i).vertexFinset from
          WallOfHeight.castGraph_vertexFinset (x.W_sub i) G'] at hu
        rw [show (W_sub' j).vertexFinset = (x.W_sub j).vertexFinset from
          WallOfHeight.castGraph_vertexFinset (x.W_sub j) G'] at hv
        rw [show W'.brickDist u v = x.W.brickDist u v from
          WallOfHeight.castGraph_brickDist x.W G' u v]
        exact x.hdist i j hij u hu v hv
      have hnd_props := nonDivSubwallIdx_props W' W_sub' hsub' hdist_W' hk_le_nd
      let x92 : Alg92Input l m p h k r :=
        { n := x.n
          G := G'
          W := W'
          h_sub := fun a => x.h_sub (idx_nd a)
          W_sub := fun a => W_sub' (idx_nd a)
          hW_valid := ⟨h2, he, hW'_valid⟩
          hnondiv := hnd_props.1
          hdist := hnd_props.2 }
      have hin₁₃_eq : s₁₃.arrs inArr = encAlg92In x92 := by
        rw [hin₁₃]
        dsimp [encAlg92In, x92]
        rw [WallOfHeight.castGraph_encList, flatMap_nonDivSubwallIdx_encList W' W_sub' hk_le_nd]
      rcases hexec92 x92 rfl hG'_edges_le s₁₃ hin₁₃_eq with
        ⟨s₁₄, t₁₄, hex₁₄, ht₁₄, hout₁₄, hreg₁₄, harr₁₄⟩
      have h92_sz : alg92Size x92 ≤ x.G.numEdges + x.n + 1 := by
        dsimp [alg92Size, x92]; omega
      have ht₁₄_le : t₁₄ ≤ C₉₂ * (x.G.numEdges + x.n + 1) :=
        le_trans ht₁₄ (Nat.mul_le_mul_left C₉₂ h92_sz)
      -- Preserve B_reg and B_arr + d at s₁₄
      have hrB_14 : s₁₄.regs B_reg = x.n := by
        rw [hreg₁₄ B_reg hB_reg92,
          hreg₁₃ B_reg (Or.inr (by omega)) (by omega)]
        dsimp [s₁₂]
        rw [State.setReg_regs_ne _ _ (by omega : (B_reg : Reg) ≠ 15),
          hreg₁₁ B_reg (Or.inr (by omega)) (by omega)]
        dsimp [s₁₀, s₉]
        rw [State.setReg_regs_ne _ _ (by omega : (B_reg : Reg) ≠ 15),
          State.setReg_regs_ne _ _ (by omega : (B_reg : Reg) ≠ 14),
          hreg₈ B_reg (ne_reg_of_ne (by omega)) (ne_reg_of_ne (by omega)), hrB_7]
      have harrB_14 : ∀ d : ℕ, s₁₄.arrs (B_arr + d) = s.arrs (B_arr + d) := by
        intro d
        rw [harr₁₄ (B_arr + d) (le_trans hB_arr92 (Nat.le_add_right B_arr d)),
          harr₁₃ (B_arr + d) (by dsimp [inArr]; omega) (by omega)]
        simp only [s₁₂, State.setReg_arrs]
        rw [harr₁₁ (B_arr + d) (by dsimp [inArr]; omega) (by omega)]
        simp only [s₁₀, s₉, State.setReg_arrs]
        rw [harr₈ (B_arr + d) (ne_arr_of_ne (by dsimp [inArr]; omega)), harrB_7 d]
      rcases hout₁₄ with ⟨c, r_new, hout_star, hrays_new, hmeet_new, hdist_new⟩ |
          ⟨K, hout_K, hK_model⟩
      · -- Subbranch 2: (l, m)-star 0 :: c.1 :: encHPaths r_new
        let s₁₅ := s₁₄.setReg 14 0
        have hex₁₅ : Exec w (.assign 14 (.read outArr (.const 0))) s₁₄ s₁₅ 3 :=
          .assign (by simp [Expr.eval, checkWord, hout_star, h0_w])
        have hc_w : c.1 < 2 ^ w := by have : c.1 < x.n := c.2; omega
        let s₁₆ := s₁₅.setReg 14 c.1
        have hex₁₆ : Exec w (.assign 14 (.read outArr (.const 1))) s₁₅ s₁₆ 3 :=
          .assign (by simp [Expr.eval, checkWord, s₁₅, hout_star, hw1, hc_w])
        have harrX_16 : s₁₆.arrs (B_arr + 4) = s.arrs (B_arr + 4) := by
          simp [s₁₆, s₁₅, harrB_14 4]
        let s₁₇ := s₁₆.writeArr (B_arr + 4) c.1 1
        have hex₁₇ : Exec w (.write (B_arr + 4) (.reg 14) (.const 1)) s₁₆ s₁₇ 3 :=
          .write (by simp [Expr.eval, checkWord, s₁₆, hc_w])
            (by simp [Expr.eval, checkWord, hw1])
            (by rw [harrX_16, hX.1]; exact c.2)
        have hX_17 : IsBitSet (Finset.univ.image (snocCenters centers c)) (B_arr + 4) s₁₇ := by
          rw [image_snocCenters]
          exact (hX.of_arr_eq harrX_16).write_one c
        have hrays_G : ∀ i : Fin l, x.W.IsStarRay c (r_new i) :=
          fun i => (isStarRay_wallUnionMultiDigraph X x.W (hrays_new i)).1
        have hc_not_X : c ∉ X :=
          (isStarRay_wallUnionMultiDigraph X x.W (hrays_new ⟨0, by omega⟩)).2
        let star_new := c.1 :: encHPaths r_new
        have hstar_new_props := length_star_enc_le hrays_G
        have hstar_new_len_le : star_new.length ≤ 1 + l * (x.n + 1) := hstar_new_props.1
        have hstar_new_w : ∀ v ∈ star_new, v < 2 ^ w := hstar_new_props.2 w hw1 hn1_w
        have hstar_new_1_w : 1 + star_new.length < 2 ^ w := by
          have : 1 + (1 + l * (x.n + 1)) ≤ (p.choose 2 + 2) * (1 + l * (x.n + 1)) := by
            have : 2 * (1 + l * (x.n + 1)) ≤ (p.choose 2 + 2) * (1 + l * (x.n + 1)) :=
              Nat.mul_le_mul_right _ (by omega)
            omega
          omega
        have hout_17 : s₁₇.arrs outArr = [0] ++ star_new ++ [] := by
          simp only [s₁₇]
          rw [State.writeArr_arrs_ne (a := B_arr + 4) (a' := outArr) _ _ _
            (ne_arr_of_ne (by dsimp [outArr]; omega))]
          simp [s₁₆, s₁₅, hout_star, star_new]
        let s₁₈ := s₁₇.setReg 15 star_new.length
        have hex₁₈ : Exec w (.assign 15 (.op .sub (.len outArr) (.const 1))) s₁₇ s₁₈ 4 := by
          have hout_len_eq : (s₁₇.arrs outArr).length = star_new.length + 1 := by
            rw [hout_17]; simp
          exact .assign (by
            simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hout_len_eq,
              show star_new.length + 1 < 2 ^ w by omega, hw1,
              show star_new.length < 2 ^ w by omega])
        -- readSliceProg outArr 1 26 (reg 15) 20
        rcases readSliceProg_exec_full (s := s₁₈) outArr 26 (.const 1) 15 20
            (by decide) (by decide) [0] star_new []
            rfl rfl hstar_new_w hw1
            (by simpa [List.length_append] using hstar_new_1_w)
            (by simp [Expr.eval, checkWord, hw1])
            (by exact hout_17)
            (by simp [s₁₈]) with
          ⟨s₁₉, t₁₉, hex₁₉, ht₁₉, harr26_19, harr₁₉, hreg₁₉⟩
        dsimp [Expr.cost] at ht₁₉
        -- reg 14 := len (B_arr + 5)
        let stars_cur :=
          (List.finRange idx).flatMap (fun a => (centers a).1 :: encHPaths (rays a))
        have harrStars_19 : s₁₉.arrs (B_arr + 5) = stars_cur := by
          rw [harr₁₉ (B_arr + 5) (by omega)]
          change (s₁₆.writeArr (B_arr + 4) c.1 1).arrs (B_arr + 5) = stars_cur
          rw [State.writeArr_arrs_ne (a := B_arr + 4) (a' := B_arr + 5) _ _ _
            (ne_arr_of_ne (by omega))]
          change s₁₄.arrs (B_arr + 5) = stars_cur
          rw [harrB_14 5, harrStars]
        have hstars_cur_len_le : stars_cur.length ≤ p.choose 2 * (1 + l * (x.n + 1)) := by
          have hbound : ∀ xs : List (Fin idx),
              (xs.flatMap (fun a => (centers a).1 :: encHPaths (rays a))).length ≤
                xs.length * (1 + l * (x.n + 1)) := by
            intro xs
            induction xs with
            | nil => simp
            | cons a xs ih_xs =>
              simp only [List.flatMap_cons, List.length_append]
              have ha := (length_star_enc_le (hrays a)).1
              have hcons : (a :: xs).length = xs.length + 1 := rfl
              rw [hcons, Nat.add_one_mul]; omega
          have h1 := hbound (List.finRange idx)
          rw [List.length_finRange] at h1
          have h2 : idx * (1 + l * (x.n + 1)) ≤ p.choose 2 * (1 + l * (x.n + 1)) :=
            Nat.mul_le_mul_right _ (by omega)
          exact le_trans h1 h2
        have hstars_cur_w : ∀ v ∈ stars_cur, v < 2 ^ w := by
          intro v hv
          dsimp [stars_cur] at hv
          rw [List.mem_flatMap] at hv
          rcases hv with ⟨a, _, hva⟩
          exact (length_star_enc_le (hrays a)).2 w hw1 hn1_w v hva
        have hstars_next_w : stars_cur.length + star_new.length < 2 ^ w := by
          have : (p.choose 2 + 1) * (1 + l * (x.n + 1)) ≤
              (p.choose 2 + 2) * (1 + l * (x.n + 1)) :=
            Nat.mul_le_mul_right _ (by omega)
          rw [Nat.add_mul, Nat.one_mul] at this
          omega
        let s₂₀ := s₁₉.setReg 14 stars_cur.length
        have hex₂₀ : Exec w (.assign 14 (.len (B_arr + 5))) s₁₉ s₂₀ 2 :=
          .assign (by simp [Expr.eval, checkWord, harrStars_19,
            show stars_cur.length < 2 ^ w by omega])
        -- appendArrProg (B_arr + 5) 26 30 14 15 20
        have hr15_20 : s₂₀.regs 15 = star_new.length := by
          dsimp [s₂₀]
          rw [State.setReg_regs_ne _ _ (by decide : (15 : Reg) ≠ 14),
            hreg₁₉ 15 (Or.inl (by decide))]
          simp [s₁₈]
        rcases appendArrProg_exec (s := s₂₀) (B_arr + 5) 26 30 14 15 20
            (by omega) (by omega) (by decide)
            (by decide) (by decide) (by decide)
            stars_cur star_new hstars_cur_w hstar_new_w hw1 hstars_next_w
            (by exact harrStars_19) (by exact harr26_19)
            rfl hr15_20 with
          ⟨s₂₁, t₂₁, hex₂₁, ht₂₁, harrStars_21, _, harr₂₁, hreg₂₁⟩
        -- Recurse with ih
        have hcenters'_inj : Function.Injective (snocCenters centers c) :=
          injective_snocCenters hcenters_inj hc_not_X
        have hrays' : ∀ a i, x.W.IsStarRay (snocCenters centers c a) (snocRays rays r_new a i) := by
          intro a i
          by_cases ha : a.1 < idx
          · simp [snocCenters, snocRays, ha, hrays ⟨a.1, ha⟩ i]
          · simp [snocCenters, snocRays, ha, hrays_G i]
        have hmeet' : ∀ a, ∀ i j : Fin l, i ≠ j → ∀ v,
            v ∈ snocRays rays r_new a i → v ∈ snocRays rays r_new a j →
            v = snocCenters centers c a := by
          intro a i j hij v hvi hvj
          by_cases ha : a.1 < idx
          · simp only [snocCenters, snocRays, ha, ↓reduceDIte] at hvi hvj ⊢
            exact hrays_meet ⟨a.1, ha⟩ i j hij v hvi hvj
          · simp only [snocCenters, snocRays, ha, ↓reduceDIte] at hvi hvj ⊢
            exact hmeet_new i j hij v hvi hvj
        have hdist' : ∀ a, ∀ i j : Fin l, i ≠ j → ∀ u v,
            (snocRays rays r_new a i).getLast? = some u →
            (snocRays rays r_new a j).getLast? = some v → m ≤ x.W.brickDist u v := by
          intro a i j hij u v hu hv
          by_cases ha : a.1 < idx
          · simp only [snocRays, ha, ↓reduceDIte] at hu hv
            exact hends_dist ⟨a.1, ha⟩ i j hij u v hu hv
          · simp only [snocRays, ha, ↓reduceDIte] at hu hv
            exact hdist_new i j hij u v hu hv
        have hrB_21 : s₂₁.regs B_reg = x.n := by
          rw [hreg₂₁ B_reg (Or.inr (by omega)) (by omega)]
          change (s₁₉.setReg 14 stars_cur.length).regs B_reg = x.n
          rw [State.setReg_regs_ne _ _ (by omega : (B_reg : Reg) ≠ 14),
            hreg₁₉ B_reg (Or.inr (by omega))]
          change (s₁₇.setReg 15 star_new.length).regs B_reg = x.n
          rw [State.setReg_regs_ne _ _ (by omega : (B_reg : Reg) ≠ 15)]
          change ((s₁₄.setReg 14 0).setReg 14 c.1).regs B_reg = x.n
          rw [State.setReg_regs_ne _ _ (by omega : (B_reg : Reg) ≠ 14),
            State.setReg_regs_ne _ _ (by omega : (B_reg : Reg) ≠ 14), hrB_14]
        have harrB_21 : ∀ d : ℕ, d ≠ 4 → d ≠ 5 → s₂₁.arrs (B_arr + d) = s.arrs (B_arr + d) := by
          intro d hd4 hd5
          rw [harr₂₁ (B_arr + d) (by omega) (by omega)]
          change s₁₉.arrs (B_arr + d) = s.arrs (B_arr + d)
          rw [harr₁₉ (B_arr + d) (by omega)]
          change (s₁₆.writeArr (B_arr + 4) c.1 1).arrs (B_arr + d) = s.arrs (B_arr + d)
          rw [State.writeArr_arrs_ne (a := B_arr + 4) (a' := B_arr + d) _ _ _
            (ne_arr_of_ne (by omega))]
          exact harrB_14 d
        have hX_21 : IsBitSet (Finset.univ.image (snocCenters centers c)) (B_arr + 4) s₂₁ := by
          apply hX_17.of_arr_eq
          rw [harr₂₁ (B_arr + 4) (by omega) (by omega)]
          exact harr₁₉ (B_arr + 4) (by omega)
        have harrStars_21' :
            s₂₁.arrs (B_arr + 5) =
              (List.finRange (idx + 1)).flatMap
                (fun a => (snocCenters centers c a).1 :: encHPaths (snocRays rays r_new a)) := by
          rw [harrStars_21, flatMap_snocStars]
        rcases ih (idx + 1) (by omega) (snocCenters centers c) (snocRays rays r_new)
            hcenters'_inj hrays' hmeet' hdist' hrB_21
            (by
              have h0 := harrB_21 0 (by decide) (by decide)
              rw [Nat.add_zero] at h0
              exact h0.trans harrG)
            (by rw [harrB_21 1 (by decide) (by decide), harrW])
            (hWV.of_arr_eq (harrB_21 2 (by decide) (by decide)))
            (by rw [harrB_21 3 (by decide) (by decide), harrSub])
            hX_21 harrStars_21'
            (hsucc.of_arrs_eq (fun k => by
              rw [Nat.add_assoc]
              exact harrB_21 (6 + k.1) (by omega) (by omega))) with
          ⟨s_end, t_rem, hex_rem, ht_rem, hout_end⟩
        have hb4 :
            (291 + exprCost) * x.G.numActivePairs ≤
            (291 + exprCost) * x.G.numEdges :=
          Nat.mul_le_mul_left _ he_le_m
        have hstep_bound :
            t₁ + (t₂ + (t₃ + (t₄ + (2 + (2 + (t₇ +
              (3 + (t₈ + (2 + (2 + (t₁₁ + (2 + (t₁₃ + (t₁₄ + (3 +
                (1 + (3 + (3 + (4 + (t₁₉ + (2 + t₂₁))))))))))))))))))))) ≤
              alg94IterStepCost p l h k t x.n x.G.numEdges B_arr C₉₂ :=
          alg94_step_bound_7a_star ht₁ hG_len_le ht₂ ht₃ ht₄ hb4 ht₇ hstep_cost_le
            ht₈ hG'_len_le ht₁₁ hW_len_le ht₁₃ hnd_len_le ht₁₄_le
            ht₁₉ hstar_new_len_le ht₂₁ hstars_cur_len_le
        have hex_step :
            Exec w (alg94IterProg p h k t B_arr B_reg P77 P92 (rem + 1) idx) s s_end _ :=
          .seq hex₁ (.seq hex₂ (.seq hex₃ (.seq hex₄ (.seq hex₅ (.seq hex₆ (.seq hex₇
            (.ite_true heval_lt (by decide)
              (.seq hex₈ (.seq hex₉ (.seq hex₁₀ (.seq hex₁₁ (.seq hex₁₂
                (.seq hex₁₃ (.seq hex₁₄ (.seq hex₁₅
                  (.ite_false (by simp [Expr.eval, checkWord, s₁₅, h0_w])
                    (.seq hex₁₆ (.seq hex₁₇ (.seq hex₁₈
                      (.seq hex₁₉ (.seq hex₂₀ (.seq hex₂₁ hex_rem))))))))))))))))))))))
        refine ⟨s_end, _, hex_step,
          alg94_total_bound hstep_bound ht_rem,
          hout_end⟩
      · -- Subbranch 1: K_p model 1 :: encBitSetsUpTo K p
        let s₁₅ := s₁₄.setReg 14 1
        have hex₁₅ : Exec w (.assign 14 (.read outArr (.const 0))) s₁₄ s₁₅ 3 :=
          .assign (by simp [Expr.eval, checkWord, hout_K, h0_w, hw1])
        let s₁₆ := s₁₅.writeArr outArr 0 0
        have hex₁₆ : Exec w (.write outArr (.const 0) (.const 0)) s₁₅ s₁₆ 3 :=
          .write (by simp [Expr.eval, checkWord, h0_w])
            (by simp [Expr.eval, checkWord, h0_w])
            (by simp [s₁₅, hout_K])
        have hout_16 : s₁₆.arrs outArr = 0 :: encBitSetsUpTo K p := by
          simp [s₁₆, s₁₅, hout_K]
        have hK_G : IsCliqueModel x.G.toSimpleGraph p K :=
          hK_model.mono (WallOfHeight.wallUnionMultiDigraph_toSimpleGraph_le x.G X x.W)
        have hb4 :
            (291 + exprCost) * x.G.numActivePairs ≤
            (291 + exprCost) * x.G.numEdges :=
          Nat.mul_le_mul_left _ he_le_m
        have hstep_bound :
            t₁ + (t₂ + (t₃ + (t₄ + (2 + (2 + (t₇ +
              (3 + (t₈ + (2 + (2 + (t₁₁ + (2 + (t₁₃ + (t₁₄ + (3 + (1 + 3)))))))))))))))) ≤
              alg94IterStepCost p l h k t x.n x.G.numEdges B_arr C₉₂ :=
          alg94_step_bound_7a_clique ht₁ hG_len_le ht₂ ht₃ ht₄ hb4 ht₇ hstep_cost_le
            ht₈ hG'_len_le ht₁₁ hW_len_le ht₁₃ hnd_len_le ht₁₄_le
        have heval14 : Expr.eval w s₁₅ (.reg 14) = some 1 := by
          simp [Expr.eval, checkWord, s₁₅, hw1]
        have hex_step :
            Exec w (alg94IterProg p h k t B_arr B_reg P77 P92 (rem + 1) idx) s s₁₆ _ :=
          .seq hex₁ (.seq hex₂ (.seq hex₃ (.seq hex₄ (.seq hex₅ (.seq hex₆ (.seq hex₇
            (.ite_true heval_lt (by decide)
              (.seq hex₈ (.seq hex₉ (.seq hex₁₀ (.seq hex₁₁ (.seq hex₁₂
                (.seq hex₁₃ (.seq hex₁₄ (.seq hex₁₅
                  (.ite_true heval14 (by decide) hex₁₆))))))))))))))))
        refine ⟨s₁₆, _, hex_step,
          alg94_single_bound hstep_bound,
          .inl ⟨K, hout_16, hK_G⟩⟩
    · -- Case 7b: ¬ (div_cnt < t - k), so t - k ≤ div_cnt
      have htk_le_div : t - k ≤ div_cnt := by omega
      have heval_lt : Expr.eval w s₇ (.op .lt (.reg 15) (.const (t - k))) = some 0 := by
        simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hr15_7, div_cnt, hdiv_w, htk_w, hlt, h0_w]
      -- 7b.1: copyArrLoopProg (B_arr + 4) 26 14 15
      have harrX_7 : s₇.arrs (B_arr + 4) = bitSetList X := by
        rw [harrB_7 4, hX.arr_eq_bitSetList]
      rcases copyArrLoopProg_exec (B_arr + 4) 26 14 15
          (ne_arr_of_ne (by omega)) (by decide) hw1 s₇
          (by rw [harrB_7 4, hX.1]; exact hn_w) (by rw [harrB_7 4]; exact hX_w) with
        ⟨s₈, t₈, hex₈, ht₈, harr26_8, harr₈, hreg₈⟩
      rw [harrX_7, length_bitSetList] at ht₈
      rw [harrX_7] at harr26_8
      -- 7b.2: reg 14 := reg B_reg, reg 15 := t
      have hrB_8 : s₈.regs B_reg = x.n := by
        rw [hreg₈ B_reg (ne_reg_of_ne (by omega)) (ne_reg_of_ne (by omega)), hrB_7]
      let s₉ := s₈.setReg 14 x.n
      have hex₉ : Exec w (.assign 14 (.reg B_reg)) s₈ s₉ 2 :=
        .assign (by simp [Expr.eval, checkWord, hrB_8, hn_w])
      let s₁₀ := s₉.setReg 15 t
      have hex₁₀ : Exec w (.assign 15 (.const t)) s₉ s₁₀ 2 :=
        .assign (by simp [Expr.eval, checkWord, ht_w])
      -- 7b.3: appendArrProg 26 18 30 14 15 20
      let I : Finset (Fin t) := (divIndicesUpTo W' W_sub' t).toFinset
      let indI := (List.finRange t).map (fun j => if j ∈ I then 1 else 0)
      have harr18_10 : s₁₀.arrs 18 = indI := by
        simp only [s₁₀, s₉, State.setReg_arrs]
        rw [harr₈ 18 (by decide), harr18_7]
        apply List.map_congr_left
        intro j _
        exact if_congr (mem_divIndicesUpTo_toFinset_iff W' W_sub' j).symm rfl rfl
      have hindI_len : indI.length = t := by simp [indI]
      have hindI_w : ∀ v ∈ indI, v < 2 ^ w := by
        intro v hv
        dsimp [indI] at hv
        rw [List.mem_map] at hv
        rcases hv with ⟨j, _, rfl⟩
        split_ifs <;> omega
      have hX_list_w : ∀ v ∈ bitSetList X, v < 2 ^ w := all_lt_bitSetList X hw1
      have hnt_w : x.n + t < 2 ^ w := by omega
      rcases appendArrProg_exec 26 18 30 14 15 20
          (by decide) (by decide) (by decide)
          (by decide) (by decide) (by decide)
          (bitSetList X) indI hX_list_w hindI_w hw1
          (by rw [length_bitSetList, hindI_len]; exact hnt_w)
          (by simp [s₁₀, s₉, harr26_8]) harr18_10
          (by simp [s₁₀, s₉, length_bitSetList]) (by simp [s₁₀, hindI_len]) with
        ⟨s₁₁, t₁₁, hex₁₁, ht₁₁, harr26_11, hr14_11, _, _⟩
      rw [length_bitSetList, hindI_len] at ht₁₁ hr14_11
      -- 7b.4: prependWordProg (.const 1) 26 outArr 14 20
      have hXI_w : ∀ v ∈ bitSetList X ++ indI, v < 2 ^ w := by
        intro v hv
        rw [List.mem_append] at hv
        rcases hv with hv | hv
        · exact hX_list_w v hv
        · exact hindI_w v hv
      rcases prependWordProg_exec (tag := 1) (.const 1) 26 outArr 14 20
          (by decide) (by decide) (bitSetList X ++ indI) hXI_w hw1
          (by rw [List.length_append, length_bitSetList, hindI_len]; omega)
          (fun _ => by simp [Expr.eval, checkWord, hw1])
          harr26_11
          (by rw [List.length_append, length_bitSetList, hindI_len]; exact hr14_11) with
        ⟨s₁₂, t₁₂, hex₁₂, ht₁₂, hout₁₂, _, _⟩
      dsimp [Expr.cost] at ht₁₂
      rw [List.length_append, length_bitSetList, hindI_len] at ht₁₂
      have hb4 :
          (291 + exprCost) * x.G.numActivePairs ≤
          (291 + exprCost) * x.G.numEdges :=
        Nat.mul_le_mul_left _ he_le_m
      have hstep_bound :
          t₁ + (t₂ + (t₃ + (t₄ + (2 + (2 + (t₇ +
            (3 + (t₈ + (2 + (2 + (t₁₁ + t₁₂))))))))))) ≤
            alg94IterStepCost p l h k t x.n x.G.numEdges B_arr C₉₂ :=
        alg94_step_bound_7b ht₁ hG_len_le ht₂ ht₃ ht₄ hb4 ht₇ hstep_cost_le ht₈ ht₁₁ ht₁₂
      have hX_card_lt : X.card < p.choose 2 := by
        have hcard_le : X.card ≤ idx := by
          calc X.card = (Finset.univ.image centers).card := rfl
            _ ≤ (Finset.univ : Finset (Fin idx)).card := Finset.card_image_le
            _ = idx := by simp
        omega
      have hI_card : t - k ≤ I.card := by
        rw [divIndicesUpTo_toFinset_card W' W_sub']
        exact htk_le_div
      have hI_div : ∀ a ∈ I, W'.IsDividingSubwall (W_sub' a) := by
        intro a ha
        exact (mem_divIndicesUpTo_toFinset_iff W' W_sub' a).mp ha
      have hex_step :
          Exec w (alg94IterProg p h k t B_arr B_reg P77 P92 (rem + 1) idx) s s₁₂ _ :=
        .seq hex₁ (.seq hex₂ (.seq hex₃ (.seq hex₄ (.seq hex₅ (.seq hex₆ (.seq hex₇
          (.ite_false heval_lt
            (.seq hex₈ (.seq hex₉ (.seq hex₁₀ (.seq hex₁₁ hex₁₂)))))))))))
      refine ⟨s₁₂, _, hex_step,
        alg94_single_bound hstep_bound,
        .inr ⟨X, I, hout₁₂, hX_card_lt, hI_card, hI_div⟩⟩

/-! ### Section 2: Complete Word RAM Program and Main Theorem for Algorithm (9.4) -/

/-- Complete Word RAM program for **Algorithm (9.4)** when `2 ≤ p`:
initializes the state arrays via `alg94InitProg` and runs `alg94IterProg` for `p.choose 2`
iterations. -/
def alg94Prog (p h : ℕ) (h2 : 2 ≤ h) (k t : ℕ) (P77 P92 : Cmd) : Cmd :=
  let B_arr := alg94ArrBase P77 P92
  let B_reg := alg94RegBase P77 P92
  .seq (alg94InitProg h h2 B_arr B_reg)
    (alg94IterProg p h k t B_arr B_reg P77 P92 (p.choose 2) 0)

/-- **Graph Minors XIII, (9.3) and Algorithm (9.4)** (Section 9, page 102):
For every `p ≥ 0`, there exist `k, r ≥ 0` such that for every `t` and every even height `h ≥ 2`,
there is a Word RAM program `P` with running time `≤ C * ε(G)` (where `C` depends only on `p, t`,
and the height `h` of `H`) that computes an output satisfying `IsAlg94Output p t k`. -/
theorem gm13_algorithm_9_4
    (h77 : Algorithm77Statement)
    (h92 : Algorithm92Statement) :
    Algorithm94Statement := by
  intro p
  rcases p with _ | _ | p2
  · exact ⟨0, 0, fun t h _ _ => ⟨alg94ProgZero, alg94_zero t h⟩⟩
  · exact ⟨0, 0, fun t h _ _ => ⟨alg94ProgOne, alg94_one t h⟩⟩
  · set p := p2 + 2
    have hp2 : 2 ≤ p := by omega
    obtain ⟨l, m, hl3, P77, hP77⟩ := h77 p hp2
    rcases hP77.subroutine_exec with ⟨C₇₇, c₇₇, _, _, hexec77⟩
    obtain ⟨k, r, h92_alg⟩ := h92 l m p hl3
    refine ⟨k, r, fun t h h2 he => ?_⟩
    obtain ⟨P92, hP92⟩ := h92_alg h h2 he
    rcases hP92.subroutine_exec with ⟨C₉₂, c₉₂, _, _, hexec92⟩
    let B_arr := alg94ArrBase P77 P92
    let B_reg := alg94RegBase P77 P92
    have hB_arr : 50 ≤ B_arr := le_max_left 50 _
    have hB_arr77 : folioCallerArrBase P77 ≤ B_arr :=
      le_max_of_le_right (le_max_left _ _)
    have hB_arr92 : folioCallerArrBase P92 ≤ B_arr :=
      le_max_of_le_right (le_max_right _ _)
    have hB_reg : 30 ≤ B_reg := le_max_left 30 _
    have hB_reg77 : folioCallerRegBase P77 ≤ B_reg :=
      le_max_of_le_right (le_max_left _ _)
    have hB_reg92 : folioCallerRegBase P92 ≤ B_reg :=
      le_max_of_le_right (le_max_right _ _)
    let exprCost := (isWallUnionEdgeExpr h (B_arr + 6) 16 (3 + 6) (3 + 7)).cost
    let C_init : ℕ := alg94InitFactor t h
    let C_base : ℕ :=
      650 + 60 * (4 + 3 * elemWallNumVerts h) +
        18 * (p.choose 2 * (1 + l)) + 2 * C₇₇ + 34 * p
    let C_step : ℕ :=
      1350 + 291 + exprCost + 60 * t +
        t * alg94ScanFactor h k +
        60 * (4 + 3 * elemWallNumVerts h) +
        18 * (k * (4 + 3 * elemWallNumVerts h)) +
        C₉₂ + 35 * (p.choose 2 * (1 + l)) + 34 * (1 + l)
    let C_total : ℕ := C_init + C_base + p.choose 2 * C_step + 1
    let K_factor : ℕ :=
      5 + (t + k + 2) * (4 + 3 * elemWallNumVerts h) +
        (p.choose 2 + 2) * (1 + l) +
        (2 + 2 * (completeGraphEdges p).length + p) +
        (3 + 2 * elemWallNumVerts h + h) + 3
    let c_total : ℕ := c₇₇ + c₉₂ + K_factor + 2
    refine ⟨alg94Prog p h h2 k t P77 P92, C_total, c_total, by omega, by omega, ?_⟩
    intro x s₀ hs₀
    let w := wordSize c_total (alg94Size x)
    have hmul_w : K_factor * (alg94Size x + 2) < 2 ^ w :=
      mul_lt_two_pow_wordSize_of_succ_le (A := K_factor) (c := c_total) (n := alg94Size x) (by omega)
    have hsz_pos : 1 ≤ alg94Size x := by unfold alg94Size; omega
    have hm_le_sz : x.G.numActivePairs ≤ alg94Size x := by
      have := Alg91.numActivePairs_le_numEdges x.G
      unfold alg94Size; omega
    have hn_le_sz : x.n ≤ alg94Size x := by unfold alg94Size; omega
    have hn1_le_sz : x.n + 1 ≤ alg94Size x := by unfold alg94Size; omega
    have he_le_sz : x.G.numEdges ≤ alg94Size x := by unfold alg94Size; omega
    have hmax_sz : maxWallEncLen h x.n ≤ (4 + 3 * elemWallNumVerts h) * alg94Size x :=
      maxWallEncLen_le_mul h x.n (alg94Size x) hsz_pos hn_le_sz
    have hl_sz : 1 + l * (x.n + 1) ≤ (1 + l) * alg94Size x := by
      have h1 : l * (x.n + 1) ≤ l * alg94Size x := Nat.mul_le_mul_left l hn1_le_sz
      rw [Nat.add_mul, Nat.one_mul]; omega
    have hw_bound :
        (2 + 3 * x.G.numActivePairs) +
        (t + k + 2) * maxWallEncLen h x.n +
        (p.choose 2 + 2) * (1 + l * (x.n + 1)) +
        (2 + 2 * (completeGraphEdges p).length + p * x.n) +
        3 + 2 * elemWallNumVerts h + h + x.n + 2 * x.G.numEdges < 2 ^ w := by
      have htk_le :
          (t + k + 2) * maxWallEncLen h x.n ≤
            (t + k + 2) * (4 + 3 * elemWallNumVerts h) * alg94Size x := by
        rw [Nat.mul_assoc]
        exact Nat.mul_le_mul_left _ hmax_sz
      have hp_stars_le :
          (p.choose 2 + 2) * (1 + l * (x.n + 1)) ≤
            (p.choose 2 + 2) * (1 + l) * alg94Size x := by
        rw [Nat.mul_assoc]
        exact Nat.mul_le_mul_left _ hl_sz
      have hmod_le :
          2 + 2 * (completeGraphEdges p).length + p * x.n ≤
            (2 + 2 * (completeGraphEdges p).length + p) * alg94Size x := by
        have h1 : (2 + 2 * (completeGraphEdges p).length) * 1 ≤
            (2 + 2 * (completeGraphEdges p).length) * alg94Size x :=
          Nat.mul_le_mul_left _ hsz_pos
        have h2 : p * x.n ≤ p * alg94Size x := Nat.mul_le_mul_left p hn_le_sz
        have h3 : (2 + 2 * (completeGraphEdges p).length) * alg94Size x + p * alg94Size x =
            (2 + 2 * (completeGraphEdges p).length + p) * alg94Size x := by ring
        omega
      have hsum_le :
          (2 + 3 * x.G.numActivePairs) +
          (t + k + 2) * maxWallEncLen h x.n +
          (p.choose 2 + 2) * (1 + l * (x.n + 1)) +
          (2 + 2 * (completeGraphEdges p).length + p * x.n) +
          3 + 2 * elemWallNumVerts h + h + x.n + 2 * x.G.numEdges ≤
            K_factor * alg94Size x := by
        have hconst : (3 + 2 * elemWallNumVerts h + h) * 1 ≤
            (3 + 2 * elemWallNumVerts h + h) * alg94Size x :=
          Nat.mul_le_mul_left _ hsz_pos
        have hK_exp : K_factor * alg94Size x =
            5 * alg94Size x +
            (t + k + 2) * (4 + 3 * elemWallNumVerts h) * alg94Size x +
            (p.choose 2 + 2) * (1 + l) * alg94Size x +
            (2 + 2 * (completeGraphEdges p).length + p) * alg94Size x +
            (3 + 2 * elemWallNumVerts h + h) * alg94Size x +
            3 * alg94Size x := by
          dsimp [K_factor]; ring
        omega
      have hle_mul : K_factor * alg94Size x ≤ K_factor * (alg94Size x + 2) :=
        Nat.mul_le_mul_left K_factor (by omega)
      omega
    have hin_w : (encAlg94In x).length < 2 ^ w := by
      have hin := length_encAlg94In_le x
      have htk : (t + 1) * maxWallEncLen h x.n ≤ (t + k + 2) * maxWallEncLen h x.n :=
        Nat.mul_le_mul_right _ (by omega)
      omega
    rcases alg94InitProg_exec (w := w) h2 x B_arr B_reg hB_arr hB_reg
        (by omega) (by omega) (by omega) (by omega) (by omega) hin_w hs₀ with
      ⟨s₁, t₁, hex₁, ht₁, hr_n₁, harrG₁, harrW₁, hWV₁, harrSub₁, hX₁, harrStars₁, hsucc₁⟩
    have hexec77' : ∀ (x77 : Alg77Input p l m),
        x77.n = x.n → x77.G.numEdges ≤ x.G.numEdges →
        ∀ (s : State), s.arrs inArr = encAlg77In x77 →
        ∃ (s' : State) (time : ℕ),
          Exec w P77 s s' time ∧
          time ≤ C₇₇ * alg77Size x77 ∧
          IsAlg77Output p x77 (s'.arrs outArr) ∧
          (∀ r : Reg, folioCallerRegBase P77 ≤ r → s'.regs r = s.regs r) ∧
          (∀ a : Arr, folioCallerArrBase P77 ≤ a → s'.arrs a = s.arrs a) := by
      intro x77 hn_eq hm_le s hs_in
      have hsz_le : alg77Size x77 ≤ alg94Size x := by
        dsimp [alg77Size, alg94Size]; omega
      have hw77 : wordSize c₇₇ (alg77Size x77) ≤ w :=
        le_trans (wordSize_mono_right c₇₇ hsz_le) (wordSize_mono_left (by omega) _)
      exact hexec77 x77 w hw77 s hs_in
    have hexec92' : ∀ (x92 : Alg92Input l m p h k r),
        x92.n = x.n → x92.G.numEdges ≤ x.G.numEdges →
        ∀ (s : State), s.arrs inArr = encAlg92In x92 →
        ∃ (s' : State) (time : ℕ),
          Exec w P92 s s' time ∧
          time ≤ C₉₂ * alg92Size x92 ∧
          IsAlg92Output l m p x92 (s'.arrs outArr) ∧
          (∀ r : Reg, folioCallerRegBase P92 ≤ r → s'.regs r = s.regs r) ∧
          (∀ a : Arr, folioCallerArrBase P92 ≤ a → s'.arrs a = s.arrs a) := by
      intro x92 hn_eq hm_le s hs_in
      have hsz_le : alg92Size x92 ≤ alg94Size x := by
        dsimp [alg92Size, alg94Size]; omega
      have hw92 : wordSize c₉₂ (alg92Size x92) ≤ w :=
        le_trans (wordSize_mono_right c₉₂ hsz_le) (wordSize_mono_left (by omega) _)
      exact hexec92 x92 w hw92 s hs_in
    rcases alg94IterProg_exec h2 he hl3 hB_arr hB_arr77 hB_arr92 hB_reg hB_reg77 hB_reg92
        x hexec77' hexec92' hw_bound (p.choose 2) 0 (by omega)
        Fin.elim0 (fun a => Fin.elim0 a)
        (fun a => Fin.elim0 a) (fun a => Fin.elim0 a)
        (fun a => Fin.elim0 a) (fun a => Fin.elim0 a)
        hr_n₁ harrG₁ harrW₁ hWV₁ harrSub₁
        (by
          have hemp : (Finset.univ.image (Fin.elim0 : Fin 0 → Fin x.n)) = ∅ := by simp
          rw [hemp]; exact hX₁)
        (by simpa using harrStars₁) hsucc₁ with
      ⟨s₂, t₂, hex₂, ht₂, hout₂⟩
    refine ⟨s₂, t₁ + t₂, .seq hex₁ hex₂, ?_, hout₂⟩
    -- Prove t₁ + t₂ ≤ C_total * alg94Size x
    have h1 : t₁ ≤ C_init * alg94Size x :=
      le_trans ht₁ (alg94InitCost_le_mul x)
    have h2_base : alg94BaseCost p l h x.n x.G.numEdges C₇₇ ≤ C_base * alg94Size x := by
      unfold alg94BaseCost
      have hb_m : 90 * (2 + 3 * x.G.numEdges) ≤ 450 * alg94Size x := by
        unfold alg94Size; omega
      have hb_w : 60 * maxWallEncLen h x.n ≤ 60 * (4 + 3 * elemWallNumVerts h) * alg94Size x := by
        rw [Nat.mul_assoc]
        exact Nat.mul_le_mul_left 60 hmax_sz
      have hb_s : 18 * (p.choose 2 * (1 + l * (x.n + 1))) ≤
          18 * (p.choose 2 * (1 + l)) * alg94Size x := by
        have := Nat.mul_le_mul_left (18 * p.choose 2) hl_sz
        calc 18 * (p.choose 2 * (1 + l * (x.n + 1)))
            = (18 * p.choose 2) * (1 + l * (x.n + 1)) := by ring
          _ ≤ (18 * p.choose 2) * ((1 + l) * alg94Size x) := this
          _ = 18 * (p.choose 2 * (1 + l)) * alg94Size x := by ring
      have hb_77 : C₇₇ * x.G.numEdges + C₇₇ * (x.n + 1) ≤ 2 * C₇₇ * alg94Size x := by
        have h_e : C₇₇ * x.G.numEdges ≤ C₇₇ * alg94Size x := Nat.mul_le_mul_left C₇₇ he_le_sz
        have h_n : C₇₇ * (x.n + 1) ≤ C₇₇ * alg94Size x := Nat.mul_le_mul_left C₇₇ hn1_le_sz
        calc C₇₇ * x.G.numEdges + C₇₇ * (x.n + 1) ≤ C₇₇ * alg94Size x + C₇₇ * alg94Size x := by omega
          _ = 2 * C₇₇ * alg94Size x := by ring
      have hb_pn : 34 * (p * x.n) ≤ 34 * p * alg94Size x := by
        rw [← Nat.mul_assoc]
        exact Nat.mul_le_mul_left (34 * p) hn_le_sz
      have hb_c : 200 * 1 ≤ 200 * alg94Size x := Nat.mul_le_mul_left 200 hsz_pos
      dsimp [C_base]
      simp only [Nat.add_mul]
      omega
    have h3_step :
        alg94IterStepCost p l h k t x.n x.G.numEdges B_arr C₉₂ ≤ C_step * alg94Size x := by
      unfold alg94IterStepCost
      have hs_m : 110 * (2 + 3 * x.G.numEdges) ≤ 550 * alg94Size x := by
        unfold alg94Size; omega
      have hs_e : (291 + exprCost) * x.G.numEdges ≤ (291 + exprCost) * alg94Size x :=
        Nat.mul_le_mul_left _ he_le_sz
      have hs_tscan :
          t * alg94ScanStepCost h x.n k (2 * x.G.numEdges) (2 * x.G.numEdges) ≤
            t * alg94ScanFactor h k * alg94Size x := by
        rw [Nat.mul_assoc]
        exact Nat.mul_le_mul_left t
          (alg94ScanStepCost_le_mul h x.n x.G.numEdges k (alg94Size x) hsz_pos hn_le_sz he_le_sz)
      have hs_w : 60 * maxWallEncLen h x.n ≤ 60 * (4 + 3 * elemWallNumVerts h) * alg94Size x := by
        rw [Nat.mul_assoc]
        exact Nat.mul_le_mul_left 60 hmax_sz
      have hs_kw : 18 * (k * maxWallEncLen h x.n) ≤
          18 * (k * (4 + 3 * elemWallNumVerts h)) * alg94Size x := by
        have := Nat.mul_le_mul_left (18 * k) hmax_sz
        calc 18 * (k * maxWallEncLen h x.n)
            = (18 * k) * maxWallEncLen h x.n := by ring
          _ ≤ (18 * k) * ((4 + 3 * elemWallNumVerts h) * alg94Size x) := this
          _ = 18 * (k * (4 + 3 * elemWallNumVerts h)) * alg94Size x := by ring
      have hs_s1 : 35 * (p.choose 2 * (1 + l * (x.n + 1))) ≤
          35 * (p.choose 2 * (1 + l)) * alg94Size x := by
        have := Nat.mul_le_mul_left (35 * p.choose 2) hl_sz
        calc 35 * (p.choose 2 * (1 + l * (x.n + 1)))
            = (35 * p.choose 2) * (1 + l * (x.n + 1)) := by ring
          _ ≤ (35 * p.choose 2) * ((1 + l) * alg94Size x) := this
          _ = 35 * (p.choose 2 * (1 + l)) * alg94Size x := by ring
      have hs_s2 : 34 * (1 + l * (x.n + 1)) ≤ 34 * (1 + l) * alg94Size x := by
        rw [Nat.mul_assoc]
        exact Nat.mul_le_mul_left 34 hl_sz
      have hs_c : (650 + 60 * t) * 1 ≤ (650 + 60 * t) * alg94Size x :=
        Nat.mul_le_mul_left _ hsz_pos
      have hs_n : 150 * x.n ≤ 150 * alg94Size x := Nat.mul_le_mul_left 150 hn_le_sz
      have hs_92 : C₉₂ * (x.G.numEdges + x.n + 1) = C₉₂ * alg94Size x := rfl
      dsimp only [C_step, exprCost] at hs_e ⊢
      simp only [Nat.add_mul, Nat.mul_one] at hs_e hs_c ⊢
      omega
    have h3_p2 :
        p.choose 2 * alg94IterStepCost p l h k t x.n x.G.numEdges B_arr C₉₂ ≤
          (p.choose 2 * C_step) * alg94Size x := by
      rw [Nat.mul_assoc]
      exact Nat.mul_le_mul_left (p.choose 2) h3_step
    dsimp [C_total]
    simp only [Nat.add_mul]
    omega

end GraphMinor.Compute

end
