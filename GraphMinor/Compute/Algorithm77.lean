module

public import GraphMinor.Compute.Algorithm77Prog75Full
public import GraphMinor.Compute.Algorithm74

@[expose] public section

/-!
# Algorithm (7.7) of Graph Minors XIII: Models of $K_p$ from Stars Over a Wall

This file completes the Word RAM formalization of **Graph Minors XIII, (7.7)** (Section 7,
page 93):

> **(7.7)** *For every integer $p \ge 2$, there exist integers $l, m \ge 0$ with $l \ge 3$ such
> that if there are $\binom{p}{2}$ $(l, m)$-stars in a graph $G$ with distinct centers, over some
> wall in $G$, then $G$ has a $K_p$-minor. Moreover, there is an algorithm, with running time
> $\le C\varepsilon(G)$, where $C$ depends only on $p$, which, given $\binom{p}{2}$ $(l, m)$-stars
> with distinct centers over a wall $H$ in a graph $G$, finds a model of $K_p$ in $G$.*

The algorithm composes:
1. `runStep75Cmd p (alg74LiftRadius p)` (`GraphMinor/Compute/Algorithm77Prog75Full.lean`), which
   executes (7.6) (repeatedly applying (7.3) with $r = 0$ and extending star rays by minimal paths
   in the wall) followed by the inductive construction of (7.5) (Case A and Case B) and packs the
   resulting $\binom{p}{2}$ disjoint $H$-paths into `inArr` as `encAlg74In (runStep75 hp hr x)`.
2. `alg74Prog p` (`GraphMinor/Compute/Algorithm74.lean`), which runs the algorithm of (7.4) on the
   packed `Alg74Input p (alg74LiftRadius p)` in `inArr` and writes `encUnderlyingGraphModel M` into
   `outArr`.
-/

namespace GraphMinor.Compute

/-- Number of rays $l = 2\binom{p}{2}^2 - \binom{p}{2} + 3$ per star in GM XIII (7.7). -/
def alg77StarDeg (p : ℕ) : ℕ :=
  2 * (p.choose 2) ^ 2 - p.choose 2 + 3

/-- Pairwise end-distance $m = 2r + 4\binom{p}{2}$ per star in GM XIII (7.7), where
$r = \text{alg74LiftRadius}(p)$ is the distance parameter of (7.4). -/
def alg77StarDist (p : ℕ) : ℕ :=
  2 * alg74LiftRadius p + 4 * p.choose 2

/-- Complete Word RAM program for GM XIII (7.7): runs `runStep75Cmd p (alg74LiftRadius p)` to
reduce the $\binom{p}{2}$ stars over $W$ to $\binom{p}{2}$ far $H$-paths over a subwall in `inArr`,
then runs `alg74Prog p` to construct a model of $K_p$ in `outArr`. -/
def alg77Prog (p : ℕ) : Cmd :=
  .seq (runStep75Cmd p (alg74LiftRadius p)) (alg74Prog p)

theorem three_le_alg77StarDeg {p : ℕ} (hp : 2 ≤ p) : 3 ≤ alg77StarDeg p := by
  unfold alg77StarDeg
  have hk : 1 ≤ p.choose 2 := Nat.choose_pos hp
  have : p.choose 2 ≤ 2 * (p.choose 2) ^ 2 := by nlinarith
  omega

theorem two_le_alg74LiftRadius (p : ℕ) : 2 ≤ alg74LiftRadius p := by
  unfold alg74LiftRadius
  omega

theorem length_encHPaths_le_of_nodup {n k : ℕ} (paths : Fin k → List (Fin n))
    (hP_len : ∀ i : Fin k, (paths i).length ≤ n) :
    (encHPaths paths).length ≤ k * (n + 1) := by
  rw [← encHPathsFrom_zero_eq_encHPaths]
  exact length_encHPathsFrom_le paths hP_len k 0

theorem length_flatMap_stars_le {p l m : ℕ} (x : Alg77Input p l m) :
    ∀ (as : List (Fin (p.choose 2))),
      (as.flatMap (fun a => (x.centers a).1 :: encHPaths (x.rays a))).length ≤
        as.length * ((l + 1) * (x.n + 1))
  | [] => by simp
  | a :: rest => by
    have hrays_len : ∀ j : Fin l, (x.rays a j).length ≤ x.n :=
      fun j => length_le_of_nodup_fin (x.hrays a j).choose_spec.2.2.1
    have henc := length_encHPaths_le_of_nodup (x.rays a) hrays_len
    have ih := length_flatMap_stars_le x rest
    simp only [List.flatMap_cons, List.length_append, List.length_cons]
    calc (encHPaths (x.rays a)).length + 1 +
          (rest.flatMap (fun b => (x.centers b).1 :: encHPaths (x.rays b))).length
        ≤ (l + 1) * (x.n + 1) + rest.length * ((l + 1) * (x.n + 1)) := by nlinarith
      _ = (rest.length + 1) * ((l + 1) * (x.n + 1)) := by ring

theorem length_encAlg77In_le {p l m : ℕ} (x : Alg77Input p l m) :
    (encAlg77In x).length ≤ ((p.choose 2) * (l + 1) + 8) * alg77Size x := by
  have hact : x.G.numActivePairs ≤ x.G.numEdges := numActivePairs_le_numEdges x.G
  have hW : x.W.encList.length ≤ 3 + 3 * x.n := x.W.length_encList_le x.hW_valid.2.2
  have hstars := length_flatMap_stars_le x (List.finRange (p.choose 2))
  simp only [List.length_finRange] at hstars
  have henc : (encAlg77In x).length =
      (2 + 3 * x.G.numActivePairs) + x.W.encList.length +
        ((List.finRange (p.choose 2)).flatMap
          (fun a => (x.centers a).1 :: encHPaths (x.rays a))).length := by
    simp [encAlg77In, MultiDigraph.length_enc, List.length_append]
    omega
  have hsize : alg77Size x = x.G.numEdges + x.n + 1 := rfl
  nlinarith

theorem length_encAlg74In_le {p r : ℕ} (y : Alg74Input p r) :
    (encAlg74In y).length ≤ (p.choose 2 + 8) * alg74Size y := by
  have hact : y.G.numActivePairs ≤ y.G.numEdges := numActivePairs_le_numEdges y.G
  have hW : y.W.encList.length ≤ 3 + 3 * y.n := y.W.length_encList_le y.hW_valid.2.2
  have hP_len : ∀ j : Fin (p.choose 2), (y.paths j).length ≤ y.n :=
    fun j => length_le_of_nodup_fin (y.hpaths_valid j).choose_spec.2.1
  have hpaths := length_encHPaths_le_of_nodup y.paths hP_len
  have henc : (encAlg74In y).length =
      (2 + 3 * y.G.numActivePairs) + y.W.encList.length + (encHPaths y.paths).length := by
    simp [encAlg74In, MultiDigraph.length_enc, List.length_append]
    omega
  have hsize : alg74Size y = y.G.numEdges + y.n + 1 := rfl
  nlinarith

/-- Word-size constant $c(p) \ge 1$ for `alg77Prog p`. -/
def alg77WordConst (p : ℕ) : ℕ :=
  let k := p.choose 2
  let l := alg77StarDeg p
  alg74WordConst p + k * (l + 1) + l + 2 * alg74LiftRadius p + 20

theorem section5WordBounds_of_mul_lt {w p : ℕ}
    (y : Alg74Input p (alg74LiftRadius p))
    (hmul_w : alg74WordConst p * (alg74Size y + 2) < 2 ^ w) :
    Section5WordBounds w p (alg74LiftRadius p) y := by
  let K := (completeGraphEdges p).length
  let c := alg74WordConst p
  let m := alg74Size y
  have hm_eq : m = y.G.numEdges + y.n + 1 := rfl
  have hm_ge1 : 1 ≤ m := by omega
  have hact_le : y.G.numActivePairs ≤ y.G.numEdges := numActivePairs_le_numEdges y.G
  have hVJ_le : elemWallNumVerts y.h ≤ y.n ∧ 2 * y.h ≤ elemWallNumVerts y.h :=
    elemWallNumVerts_le_n y
  have hh1 : 1 ≤ y.h := by have := y.hW_valid.1; omega
  have h2h2_le_VJ : 2 * y.h + 2 ≤ elemWallNumVerts y.h :=
    two_mul_add_two_le_elemWallNumVerts hh1
  have hEJ_le : (elemWallEdges y.h).length ≤ 2 * elemWallNumVerts y.h :=
    length_elemWallEdges_le y.h
  have hW_len_le : y.W.encList.length ≤ 3 + 3 * y.n :=
    y.W.length_encList_le y.hW_valid.2.2
  have hpaths_len_le : (encHPaths y.paths).length ≤ K * (y.n + 1) := by
    rw [← encHPathsSlice_finRange]
    simpa [K] using length_encHPathsSlice_le y (List.finRange K)
  have hin_len_eq :
      (encAlg74In y).length =
        2 + 3 * y.G.numActivePairs + y.W.encList.length + (encHPaths y.paths).length := by
    simp [encAlg74In, MultiDigraph.length_enc]
    omega
  have hc_def : c = 4 * K + 3 * p + alg74BoxMarginConst p + 12 := rfl
  change c * (m + 2) < 2 ^ w at hmul_w
  refine
    { hw3 := by nlinarith
      hp_w := by nlinarith
      hK_w := by change K < 2 ^ w; nlinarith
      hn_w := by nlinarith
      hm_w := by nlinarith
      hwall_w := by nlinarith
      hVJW_w := by nlinarith
      hroute_w := by nlinarith
      hin_w := by nlinarith
      hout_w := by change 2 + 2 * K + p * y.n < 2 ^ w; nlinarith }

theorem alg77_word_bounds {p : ℕ} (hp : 2 ≤ p)
    (x : Alg77Input p (alg77StarDeg p) (alg77StarDist p)) :
    let w := wordSize (alg77WordConst p) (alg77Size x)
    let y := runStep75 hp (two_le_alg74LiftRadius p) x
    4 * x.n + 12 < 2 ^ w ∧
    x.G.numEdges < 2 ^ w ∧
    alg77StarDeg p < 2 ^ w ∧
    2 * alg74LiftRadius p < 2 ^ w ∧
    (encAlg77In x).length < 2 ^ w ∧
    (encAlg74In y).length < 2 ^ w ∧
    Section5WordBounds w p (alg74LiftRadius p) y := by
  dsimp only
  let c := alg77WordConst p
  let m := alg77Size x
  let w := wordSize c m
  have hc1 : 1 ≤ c := by unfold c alg77WordConst; dsimp only; omega
  have hmul_w : c * (m + 2) < 2 ^ w := mul_lt_two_pow_wordSize hc1 m
  have hm_eq : m = x.G.numEdges + x.n + 1 := rfl
  have hm_ge1 : 1 ≤ m := by omega
  have hin_x : (encAlg77In x).length ≤ ((p.choose 2) * (alg77StarDeg p + 1) + 8) * m :=
    length_encAlg77In_le x
  have hc_def : c = alg74WordConst p + (p.choose 2) * (alg77StarDeg p + 1) +
      alg77StarDeg p + 2 * alg74LiftRadius p + 20 := rfl
  have h1 : 4 * x.n + 12 < 2 ^ w := by nlinarith
  have h2 : x.G.numEdges < 2 ^ w := by nlinarith
  have h3 : alg77StarDeg p < 2 ^ w := by nlinarith
  have h4 : 2 * alg74LiftRadius p < 2 ^ w := by nlinarith
  have h5 : (encAlg77In x).length < 2 ^ w := by nlinarith
  have hy_size : alg74Size (runStep75 hp (two_le_alg74LiftRadius p) x) = m := by
    simp [alg74Size, m, alg77Size,
      runStep75_n hp (two_le_alg74LiftRadius p) x,
      runStep75_G hp (two_le_alg74LiftRadius p) x]
  have hmul74 : alg74WordConst p * (alg74Size (runStep75 hp (two_le_alg74LiftRadius p) x) + 2) < 2 ^ w := by
    rw [hy_size]
    nlinarith
  have hw74 : Section5WordBounds w p (alg74LiftRadius p) (runStep75 hp (two_le_alg74LiftRadius p) x) :=
    section5WordBounds_of_mul_lt _ hmul74
  exact ⟨h1, h2, h3, h4, h5, hw74.hin_w, hw74⟩

theorem step75HitScanTime_le (l n m : ℕ) (hn : n ≤ m) (hm : 1 ≤ m) :
    step75HitScanTime l n ≤ step75HitScanTime l 1 * m := by
  unfold step75HitScanTime
  nlinarith

theorem step75TailTime_le (l k n m : ℕ) (hn : n ≤ m) (hm : 1 ≤ m) :
    step75TailTime l k n ≤ step75TailTime l k 1 * m := by
  unfold step75TailTime
  have h1 : (k + 1) * (2 * l * (22 * n + 16) + 240 * n + 155) ≤
      (k + 1) * (2 * l * (22 * 1 + 16) + 240 * 1 + 155) * m := by
    calc (k + 1) * (2 * l * (22 * n + 16) + 240 * n + 155)
        ≤ (k + 1) * ((2 * l * (22 * 1 + 16) + 240 * 1 + 155) * m) :=
          Nat.mul_le_mul_left (k + 1) (by nlinarith)
      _ = (k + 1) * (2 * l * (22 * 1 + 16) + 240 * 1 + 155) * m := by ring
  have h2 : ((79 * n + 242500) * k + 30) * l ≤
      ((79 * 1 + 242500) * k + 30) * l * m := by
    calc ((79 * n + 242500) * k + 30) * l
        ≤ (((79 * 1 + 242500) * k + 30) * m) * l :=
          Nat.mul_le_mul_right l (by nlinarith)
      _ = ((79 * 1 + 242500) * k + 30) * l * m := by ring
  nlinarith

theorem step75OneStepBound_le (l k n m : ℕ) (hn : n ≤ m) (hm : 1 ≤ m) :
    step75OneStepBound l k n ≤ step75OneStepBound l k 1 * m := by
  unfold step75OneStepBound
  have h1 : k * (l * (23 * n + 25) + 1) ≤ k * (l * (23 * 1 + 25) + 1) * m := by
    calc k * (l * (23 * n + 25) + 1)
        ≤ k * ((l * (23 * 1 + 25) + 1) * m) := Nat.mul_le_mul_left k (by nlinarith)
      _ = k * (l * (23 * 1 + 25) + 1) * m := by ring
  have h2 : k * step75HitScanTime l n ≤ k * step75HitScanTime l 1 * m := by
    calc k * step75HitScanTime l n
        ≤ k * (step75HitScanTime l 1 * m) :=
          Nat.mul_le_mul_left k (step75HitScanTime_le l n m hn hm)
      _ = k * step75HitScanTime l 1 * m := by ring
  have h3 := step75TailTime_le l k n m hn hm
  nlinarith

theorem runStep75TimeBound_le (p D n L m : ℕ) (hn : n ≤ m) (hL : L ≤ D * m) (hm : 1 ≤ m) :
    runStep75TimeBound p n L ≤ runStep75TimeBound p 1 D * m := by
  unfold runStep75TimeBound
  dsimp only
  generalize p.choose 2 = k
  generalize 2 * k ^ 2 - k + 3 = l
  have h1 : k * (k * (l * (745 * n + 1230) + 1) + 5700 * n + 5700) ≤
      k * (k * (l * (745 * 1 + 1230) + 1) + 5700 * 1 + 5700) * m := by
    have ha : l * (745 * n + 1230) + 1 ≤ (l * (745 * 1 + 1230) + 1) * m := by
      calc l * (745 * n + 1230) + 1
          ≤ l * ((745 * 1 + 1230) * m) + 1 * m :=
            Nat.add_le_add (Nat.mul_le_mul_left l (by omega)) (by omega)
        _ = (l * (745 * 1 + 1230) + 1) * m := by ring
    have hb : k * (l * (745 * n + 1230) + 1) + 5700 * n + 5700 ≤
        (k * (l * (745 * 1 + 1230) + 1) + 5700 * 1 + 5700) * m := by
      have hb1 : 5700 * n + 5700 ≤ (5700 * 1 + 5700) * m := by omega
      calc k * (l * (745 * n + 1230) + 1) + 5700 * n + 5700
          = k * (l * (745 * n + 1230) + 1) + (5700 * n + 5700) := by ring
        _ ≤ k * ((l * (745 * 1 + 1230) + 1) * m) + (5700 * 1 + 5700) * m :=
            Nat.add_le_add (Nat.mul_le_mul_left k ha) hb1
        _ = (k * (l * (745 * 1 + 1230) + 1) + 5700 * 1 + 5700) * m := by ring
    calc k * (k * (l * (745 * n + 1230) + 1) + 5700 * n + 5700)
        ≤ k * ((k * (l * (745 * 1 + 1230) + 1) + 5700 * 1 + 5700) * m) :=
          Nat.mul_le_mul_left k hb
      _ = k * (k * (l * (745 * 1 + 1230) + 1) + 5700 * 1 + 5700) * m := by ring
  have h2 : k * (l * (22 * n + 25) + 9) ≤ k * (l * (22 * 1 + 25) + 9) * m := by
    have hc : l * (22 * n + 25) + 9 ≤ (l * (22 * 1 + 25) + 9) * m := by
      calc l * (22 * n + 25) + 9
          ≤ l * ((22 * 1 + 25) * m) + 9 * m :=
            Nat.add_le_add (Nat.mul_le_mul_left l (by omega)) (by omega)
        _ = (l * (22 * 1 + 25) + 9) * m := by ring
    calc k * (l * (22 * n + 25) + 9)
        ≤ k * ((l * (22 * 1 + 25) + 9) * m) := Nat.mul_le_mul_left k hc
      _ = k * (l * (22 * 1 + 25) + 9) * m := by ring
  have h3 : k * step75OneStepBound l k n + 1 ≤ (k * step75OneStepBound l k 1 + 1) * m := by
    calc k * step75OneStepBound l k n + 1
        ≤ k * (step75OneStepBound l k 1 * m) + 1 * m :=
          Nat.add_le_add (Nat.mul_le_mul_left k (step75OneStepBound_le l k n m hn hm)) (by omega)
      _ = (k * step75OneStepBound l k 1 + 1) * m := by ring
  have h4 : k * (21 * n + 21) ≤ k * (21 * 1 + 21) * m := by
    calc k * (21 * n + 21)
        ≤ k * ((21 * 1 + 21) * m) := Nat.mul_le_mul_left k (by omega)
      _ = k * (21 * 1 + 21) * m := by ring
  have h5 : k * (2 * l + 1) + 1 ≤ (k * (2 * l + 1) + 1) * m :=
    Nat.le_mul_of_pos_right _ (by omega)
  have h6 : 414 * n + 300 ≤ (414 * 1 + 300) * m := by omega
  have h7 : 44 * L + 35 ≤ (44 * D + 35) * m := by
    calc 44 * L + 35
        ≤ 44 * (D * m) + 35 * m :=
          Nat.add_le_add (Nat.mul_le_mul_left 44 hL) (Nat.le_mul_of_pos_right 35 hm)
      _ = (44 * D + 35) * m := by ring
  calc k * (k * (l * (745 * n + 1230) + 1) + 5700 * n + 5700) +
        k * (l * (22 * n + 25) + 9) + 414 * n + 300 +
        (k * (2 * l + 1) + 1) +
        (k * step75OneStepBound l k n + 1) +
        (k * (21 * n + 21) + 44 * L + 35)
      = k * (k * (l * (745 * n + 1230) + 1) + 5700 * n + 5700) +
        k * (l * (22 * n + 25) + 9) + (414 * n + 300) +
        (k * (2 * l + 1) + 1) +
        (k * step75OneStepBound l k n + 1) +
        (k * (21 * n + 21) + (44 * L + 35)) := by ring
    _ ≤ k * (k * (l * (745 * 1 + 1230) + 1) + 5700 * 1 + 5700) * m +
        k * (l * (22 * 1 + 25) + 9) * m + (414 * 1 + 300) * m +
        (k * (2 * l + 1) + 1) * m +
        (k * step75OneStepBound l k 1 + 1) * m +
        (k * (21 * 1 + 21) * m + (44 * D + 35) * m) :=
          Nat.add_le_add
            (Nat.add_le_add
              (Nat.add_le_add
                (Nat.add_le_add
                  (Nat.add_le_add h1 h2)
                  h6)
                h5)
              h3)
            (Nat.add_le_add h4 h7)
    _ = (k * (k * (l * (745 * 1 + 1230) + 1) + 5700 * 1 + 5700) +
        k * (l * (22 * 1 + 25) + 9) + 414 * 1 + 300 +
        (k * (2 * l + 1) + 1) +
        (k * step75OneStepBound l k 1 + 1) +
        (k * (21 * 1 + 21) + 44 * D + 35)) * m := by ring

/-- Time-bound constant $C(p) \ge 1$ for `alg77Prog p`: running time is
$\le \text{alg77TimeConst}(p) \cdot \text{alg77Size}(x)$. -/
def alg77TimeConst (p : ℕ) : ℕ :=
  runStep75TimeBound p 1 (p.choose 2 + 8) + alg74TimeConst p

theorem alg74Prog_time_le {w p : ℕ} (hp : 2 ≤ p)
    (y : Alg74Input p (alg74LiftRadius p)) {s : State}
    (hw : Section5WordBounds w p (alg74LiftRadius p) y)
    (hin : s.arrs inArr = encAlg74In y) :
    ∃ s' t,
      Exec w (alg74Prog p) s s' t ∧
      t ≤ alg74TimeConst p * alg74Size y ∧
      IsAlg74Output p (alg74LiftRadius p) y (s'.arrs outArr) := by
  rcases alg74Prog_exec hp y hw hin with ⟨s', t, hex, ht, hout⟩
  refine ⟨s', t, hex, ?_, ⟨alg74UnderlyingModel hp y, hout⟩⟩
  let K := (completeGraphEdges p).length
  let V_J := elemWallNumVerts y.h
  let E_J := (elemWallEdges y.h).length
  let m := alg74Size y
  have hm_eq : m = y.G.numEdges + y.n + 1 := rfl
  have hact_le : y.G.numActivePairs ≤ y.G.numEdges := numActivePairs_le_numEdges y.G
  have hVJ_le : V_J ≤ y.n := (elemWallNumVerts_le_n y).1
  have hEJ_le : E_J ≤ 2 * V_J := length_elemWallEdges_le y.h
  have hW_len_le : y.W.encList.length ≤ 3 + 3 * y.n :=
    y.W.length_encList_le y.hW_valid.2.2
  have h1 : (p + 1) * y.n ≤ (p + 1) * m :=
    Nat.mul_le_mul_left (p + 1) (by omega)
  have h2 : (30 * y.G.numActivePairs + 23 * y.n + 65) * K + 2 * K ≤ (67 * K) * m := by
    have hle : 30 * y.G.numActivePairs + 23 * y.n + 65 + 2 ≤ 67 * m := by omega
    calc (30 * y.G.numActivePairs + 23 * y.n + 65) * K + 2 * K
      _ = (30 * y.G.numActivePairs + 23 * y.n + 65 + 2) * K := by ring
      _ ≤ (67 * m) * K := Nat.mul_le_mul_right K hle
      _ = (67 * K) * m := by ring
  have h3 : (routeTerminalsCmd p).maxTime ≤ (routeTerminalsCmd p).maxTime * m :=
    Nat.le_mul_of_pos_right _ (by omega)
  have h4 :
      ((markWallBranchVertsBody p).maxTime + 3) * V_J ≤
        ((markWallBranchVertsBody p).maxTime + 3) * m :=
    Nat.mul_le_mul_left _ (by omega)
  have h5 :
      (markActCost p (List.finRange p) + 30) * E_J ≤
        (2 * (markActCost p (List.finRange p) + 30)) * m := by
    calc (markActCost p (List.finRange p) + 30) * E_J
      _ ≤ (markActCost p (List.finRange p) + 30) * (2 * m) :=
        Nat.mul_le_mul_left _ (by omega)
      _ = (2 * (markActCost p (List.finRange p) + 30)) * m := by ring
  have h6 : 23 * p * y.W.encList.length ≤ (69 * p) * m := by
    calc 23 * p * y.W.encList.length
      _ ≤ 23 * p * (3 * m) := Nat.mul_le_mul_left (23 * p) (by omega)
      _ = (69 * p) * m := by ring
  have h7 :
      2 * E_J + 60 + (22 * V_J + 26 * E_J + 17 * y.W.encList.length + 25) +
        (95 * V_J + 10) + 1 + 15 + 10 ≤ (281 + 180) * m := by
    omega
  have hsum :
      alg74TimeConst p * m =
        (p + 1) * m + (281 + 180) * m + (69 * p) * m + (67 * K) * m +
        (routeTerminalsCmd p).maxTime * m +
        ((markWallBranchVertsBody p).maxTime + 3) * m +
        (2 * (markActCost p (List.finRange p) + 30)) * m := by
    unfold alg74TimeConst
    dsimp only [K]
    ring
  change t ≤ alg74TimeConst p * m
  change t ≤
    ((p + 1) * y.n + 2 * E_J + 2 * K + 60) +
    (22 * V_J + 26 * E_J + 17 * y.W.encList.length + 25) +
    (95 * V_J + 10) +
    ((30 * y.G.numActivePairs + 23 * y.n + 65) * K + 1) +
    (routeTerminalsCmd p).maxTime +
    (((markWallBranchVertsBody p).maxTime + 3) * V_J + 15) +
    ((markActCost p (List.finRange p) + 30) * E_J +
      23 * p * y.W.encList.length + 10) at ht
  omega

/-- **Graph Minors XIII, (7.7) Algorithm** (Section 7, page 93):
For every integer `p ≥ 2`, there exist `l, m` (`3 ≤ l`) and a Word RAM program `P` with running time
`≤ C(p) * ε(G)` that, given `p.choose 2` `(l, m)`-stars with distinct centers over a wall `W` in `G`,
outputs a model of $K_p$ in `G`. -/
public theorem gm13_algorithm_7_7 : Algorithm77Statement := by
  intro p hp
  refine ⟨alg77StarDeg p, alg77StarDist p, three_le_alg77StarDeg hp,
    alg77Prog p, alg77TimeConst p, alg77WordConst p, ?_, ?_, ?_⟩
  · unfold alg77TimeConst alg74TimeConst; dsimp only; omega
  · unfold alg77WordConst; dsimp only; omega
  · intro x s hin
    let w := wordSize (alg77WordConst p) (alg77Size x)
    let r := alg74LiftRadius p
    have hr : 2 ≤ r := two_le_alg74LiftRadius p
    let y := runStep75 hp hr x
    obtain ⟨hword, hedges_w, hl_w, h2r_w, hin_x_w, hin_y_w, hw74⟩ :=
      alg77_word_bounds hp x
    rcases runStep75Cmd_exec hp hr x hword hedges_w hl_w h2r_w hin_x_w hin_y_w hin with
      ⟨s₁, t₁, hex₁, ht₁, hin₁⟩
    rcases alg74Prog_time_le hp y hw74 hin₁ with
      ⟨s₂, t₂, hex₂, ht₂, hout₂⟩
    have hy_size : alg74Size y = alg77Size x := by
      simp [alg74Size, alg77Size, y, runStep75_n hp hr x, runStep75_G hp hr x]
    have hL_y : (encAlg74In y).length ≤ (p.choose 2 + 8) * alg77Size x := by
      rw [← hy_size]
      exact length_encAlg74In_le y
    have ht₁_le : t₁ ≤ runStep75TimeBound p 1 (p.choose 2 + 8) * alg77Size x :=
      Nat.le_trans ht₁ (runStep75TimeBound_le p (p.choose 2 + 8) x.n (encAlg74In y).length
        (alg77Size x) (by unfold alg77Size; omega) hL_y (by unfold alg77Size; omega))
    rw [hy_size] at ht₂
    have hout77 : IsAlg77Output p x (s₂.arrs outArr) :=
      (isAlg77Output_iff_isAlg74Output_runStep75 hp hr x (s₂.arrs outArr)).mpr hout₂
    refine ⟨s₂, t₁ + t₂, .seq hex₁ hex₂, ?_, hout77⟩
    calc t₁ + t₂
      _ ≤ runStep75TimeBound p 1 (p.choose 2 + 8) * alg77Size x +
            alg74TimeConst p * alg77Size x := Nat.add_le_add ht₁_le ht₂
      _ = alg77TimeConst p * alg77Size x := by unfold alg77TimeConst; ring

end GraphMinor.Compute
