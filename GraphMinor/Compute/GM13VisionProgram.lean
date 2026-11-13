module

public import GraphMinor.Compute.GM13VisionCore
import GraphMinor.Compute.Join13Adapter101
import GraphMinor.Compute.Algorithm41Aux20

/-!
# Graph Minors XIII, (10.1): a vision in quadratic time

The input consists of the graph, root set, wall, rural division and the supplied
interior branch-decompositions. The wall representation includes its vertex and
perimeter bitsets. The program is independent of its height. It computes the
attachment sequences, extended members, their folios and models, and attachment
vertices. The proved (4.1) program supplies every folio call.
-/

@[expose] public section
namespace GraphMinor.Compute

open Set Function Graph SimpleGraph Classical
open GraphMinor GraphMinor.Surface GraphMinor.GM09 GraphMinor.GM13

/-- Input data of XIII (10.1), pages 106–107: a graph, root set, wall and rural
division satisfying Hypothesis C, and the given bounded-width decompositions of
interior members. The parameter `q` bounds the number of roots. -/
structure Alg101Input (q ω : ℕ) where
  n : ℕ
  G : MultiDigraph n
  X : Finset (Fin n)
  root_bound : X.card ≤ q
  division : ParsedCase3Block (G.deleteVertices X) X
  hypothesisC : HypothesisC G.toGMDigraph X.card X.toNatSet
    division.toGMWall division.toSociety division.toDivision
  decompositions : ∀ j : Fin division.members.length,
    isMemberInterior division.wallSec.W (division.members[j.1]'j.2) = true →
      MemberBranchDecompValid G X ω (division.members[j.1]'j.2)

/-- The serialized rural division and the wall subdivision in the (10.1) input. -/
def Alg101Input.block {q ω : ℕ} (x : Alg101Input q ω) : List ℕ :=
  encCase3Block x.division.wallSec.W x.division.K_vList x.division.K_eList
    x.division.corners x.division.members

/-- The graph size `ε = |V(G)| + |E(G)| + 1` used in XIII (10.1), page 107. -/
def alg101Size {q ω : ℕ} (x : Alg101Input q ω) : ℕ := x.n + x.G.numEdges + 1

/-- The five input arrays encode the given graph, roots, division, and the wall's
vertex and perimeter sets. They carry no folio or vision answer. -/
def IsAlg101InputState {q ω : ℕ} (p : ℕ) (x : Alg101Input q ω) (s : State) : Prop :=
  s.arrs (a101_G p) = x.G.enc ∧
  s.arrs (a101_X p) = bitSetList x.X ∧
  s.arrs (a101_block p) = x.block ∧
  s.arrs (a101_perim p) = bitSetList x.division.wallSec.W.perimFinset ∧
  s.arrs (a101_WH p) = bitSetList x.division.wallSec.W.vertexFinset

/-- The output is a parsed vision, including a correct folio and its models for
each interior member. Its geometric data give `vOut.toGMVision`. -/
def IsAlg101Output {q ω : ℕ} (δ : ℕ) (x : Alg101Input q ω) (words : List ℕ) : Prop :=
  ∃ vOut : ParsedVisionOutput x.G x.X x.division q δ,
    parseVisionOutput x.G x.X x.division q δ words = some vOut ∧
    ∀ (j : Fin x.division.members.length)
      (_ : isMemberInterior x.division.wallSec.W (x.division.members[j.1]'j.2) = true),
      let m := vOut.recordAt j
      ∃ folioOut : ParsedFolioAndModels
          (tildeAMultiDigraph m.tildeA_vList m.tildeA_eList)
          (prefixRootFinset m.tildeA_vList.length (m.sSeq ++ vOut.xSeq).length) δ,
        parseFolioAndModelsFull (tildeAMultiDigraph m.tildeA_vList m.tildeA_eList)
          (prefixRootFinset m.tildeA_vList.length (m.sSeq ++ vOut.xSeq).length)
          δ m.folioWords = some folioOut ∧
        IsDeltaFolioRep δ (tildeAMultiDigraph m.tildeA_vList m.tildeA_eList)
          (prefixRootFinset m.tildeA_vList.length (m.sSeq ++ vOut.xSeq).length) folioOut.folio

private theorem add_one_le_power101 (N m : ℕ) : m + 1 ≤ (N + 2) ^ m := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Nat.pow_succ]
    have hm := Nat.mul_le_mul ih (show 2 ≤ N + 2 by omega)
    omega

private theorem vision_word_budget101 (N m : ℕ) :
    (m + 1) * ((N + 2) * (N + 2)) < 2 ^ wordSize (m + 2) N := by
  have hle : (m + 1) * ((N + 2) * (N + 2)) ≤ (N + 2) ^ (m + 2) := by
    rw [Nat.pow_add, Nat.pow_two]
    exact Nat.mul_le_mul_right _ (add_one_le_power101 N m)
  exact hle.trans_lt (pow_lt_two_pow_wordSize (by omega) N)

/-- Graph Minors XIII, Algorithm (10.1), pages 106–107:
"*Input:* $G$, $X$, $H$, $\mathcal{A}$ satisfying Hypothesis C, and an integer $\delta \ge 0$,
and for each interior $A \in \mathcal{A}$ a branch-decomposition of $A$ of width $\le \omega$."
"*Output:* A vision."
"*Running time:* $O(\varepsilon^2)$."

The one program works for every wall height. Its correctness includes the
geometric vision data, the interior folios and their models. The only input
conditions are Hypothesis C and the supplied decompositions, as printed. -/
theorem gm13_algorithm_10_1 (p q δ ω : ℕ) :
    ∃ P : Cmd,
      ComputesRelInTime (alg101Size (q := q) (ω := ω)) (IsAlg101InputState p)
        (fun x s => IsAlg101Output δ x (s.arrs (a101_visBuf p)))
        P (fun ε => ε ^ 2) := by
  obtain ⟨prog41, C41, c41, hc41, hC41, h41⟩ := alg41Spec101_of_claim41
    (fun δ ξ B => ⟨alg41CoreProg δ ξ B, algorithm_4_1_core δ ξ B⟩)
    p (q + 3) δ (max ω 2 + q)
  let m := c41 + C41 + maxFolioRepCode q δ + maxFolioEncLen101 q δ + maxFolioEncWord q δ + q + 30
  have hC : 0 < alg101TimeConst q δ C41 := by unfold alg101TimeConst; omega
  refine ⟨alg101UniformProg p q δ C41 prog41, alg101TimeConst q δ C41, m + 2,
    hC, by omega, ?_⟩
  intro x s hs
  obtain ⟨hG, hX, hblock, hperim, hWH⟩ := hs
  let N := alg101Size x
  let w := wordSize (m + 2) N
  have hmain_w : (m + 1) * ((N + 2) * (N + 2)) < 2 ^ w := vision_word_budget101 N m
  have hsq_pos : 1 ≤ (N + 2) * (N + 2) := Nat.mul_pos (by omega) (by omega)
  have hm_lt_w : m + 1 < 2 ^ w :=
    lt_of_le_of_lt (Nat.le_mul_of_pos_right (m + 1) hsq_pos) hmain_w
  have hn_le_N : x.n ≤ N := by dsimp [N, alg101Size]; omega
  have hnsq_le : x.n * x.n ≤ (N + 2) * (N + 2) := Nat.mul_le_mul (by omega) (by omega)
  have h2nsq_w : 2 + 6 * (x.n * x.n) < 2 ^ w := by
    have h1 : 7 * ((N + 2) * (N + 2)) ≤ (m + 1) * ((N + 2) * (N + 2)) :=
      Nat.mul_le_mul_right _ (by dsimp [m]; omega)
    omega
  have hN_w : 24 * N < 2 ^ w := by
    have h1 : N ≤ (N + 2) * (N + 2) := le_trans (by omega) (Nat.le_mul_self (N + 2))
    have h2 : 24 * ((N + 2) * (N + 2)) ≤ (m + 1) * ((N + 2) * (N + 2)) :=
      Nat.mul_le_mul_right _ (by dsimp [m]; omega)
    have h3 := Nat.mul_le_mul_left 24 h1
    omega
  have hw41 : wordSize c41 N ≤ w := wordSize_mono_left (by dsimp [m]; omega) N
  have hC41_w : C41 < 2 ^ w := by dsimp [m] at hm_lt_w; omega
  have hvis_cap_w : (2 + x.n) + N * memberPerCap C41 x.n x.G.numEdges < 2 ^ w := by
    have hcap_eq : N * memberPerCap C41 x.n x.G.numEdges = (C41 + 18) * (N * N) := by
      unfold memberPerCap
      change N * (C41 * N + 18 * N) = (C41 + 18) * (N * N)
      ring
    rw [hcap_eq]
    have hN2 : N * N ≤ (N + 2) * (N + 2) := Nat.mul_le_mul (by omega) (by omega)
    have h1 : (C41 + 18) * (N * N) ≤ (C41 + 18) * ((N + 2) * (N + 2)) :=
      Nat.mul_le_mul_left (C41 + 18) hN2
    have h2 : 2 + x.n ≤ (N + 2) * (N + 2) :=
      le_trans (by omega) (Nat.le_mul_self (N + 2))
    have h3 : (C41 + 19) * ((N + 2) * (N + 2)) ≤ (m + 1) * ((N + 2) * (N + 2)) :=
      Nat.mul_le_mul_right _ (by dsimp [m]; omega)
    have h4 : (C41 + 19) * ((N + 2) * (N + 2)) =
        (C41 + 18) * ((N + 2) * (N + 2)) + (N + 2) * (N + 2) := Nat.succ_mul (C41 + 18) _
    omega
  have hw_code : maxFolioRepCode q δ < 2 ^ w := by dsimp [m] at hm_lt_w; omega
  have hw_len : maxFolioEncLen101 q δ < 2 ^ w := by dsimp [m] at hm_lt_w; omega
  have hw_word : maxFolioEncWord q δ + 1 < 2 ^ w := by dsimp [m] at hm_lt_w; omega
  have hw_q : q + 4 < 2 ^ w := by dsimp [m] at hm_lt_w; omega
  obtain ⟨s', t, vOut, he, ht, hp, _, hrep, _⟩ := alg101UniformProg_exec h41
    x.G x.root_bound x.division x.hypothesisC x.decompositions x.block
    (parseCase3Block_encCase3Block x.division)
    h2nsq_w hN_w hw41 hC41_w hvis_cap_w hw_code hw_len hw_word hw_q
    hG hX hblock hperim hWH
  refine ⟨s', t, he, ht, vOut, hp, ?_⟩
  intro j hInt
  obtain ⟨f, hparse, _⟩ := vOut.exists_parsedFolioAndModels_at j hInt
  exact ⟨f, hparse, hrep j hInt f hparse⟩

end GraphMinor.Compute
