module

public import GraphMinor.Compute.Algorithm104
import GraphMinor.Compute.Join13Adapter101
import GraphMinor.Compute.Algorithm41Aux20

/-!
# Proof of `Alg104Spec` for Graph Minors XIII, Algorithm (10.4)

This file proves `alg104Spec_proved`, showing that `alg104Prog` with the pure reading Case (iii)
block decoder `case3Decoder : Case3BlockDecoder` satisfies `Alg104Spec case3Decoder p q δ h ω`
(defined in `GraphMinor/Compute/Specs105.lean`) for the wall height
`h = GM13.sec10MaxWallHeight GM13.theorem_10_2_proof.{0, 0} q δ` of **Graph Minors XIII, (10.3)**
(Robertson and Seymour, *Graph Minors. XIII. The Disjoint Paths Problem*,
J. Combin. Theory Ser. B **63** (1995), pages 107–108). The proved core program of (4.1)
supplies the folio subroutine through its adapter.
-/

@[expose] public section

namespace GraphMinor.Compute

open Set Function Graph SimpleGraph
open GraphMinor GraphMinor.Surface GraphMinor.GM09 GraphMinor.GM13

private theorem add_one_le_add_two_pow (N m : ℕ) : m + 1 ≤ (N + 2) ^ m := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Nat.pow_succ]
    have h2 : 2 ≤ N + 2 := by omega
    have hmul := Nat.mul_le_mul ih h2
    omega

private theorem mul_sq_lt_two_pow_wordSize (N B m : ℕ) :
    (m + 1) * ((N + 2) * (N + 2)) < 2 ^ wordSize (m + 2) (N + B) := by
  have h1 : (m + 1) * ((N + 2) * (N + 2)) ≤ (N + 2) ^ (m + 2) := by
    rw [Nat.pow_add, Nat.pow_two]
    exact Nat.mul_le_mul_right ((N + 2) * (N + 2)) (add_one_le_add_two_pow N m)
  have h2 : (N + 2) ^ (m + 2) < 2 ^ wordSize (m + 2) N :=
    pow_lt_two_pow_wordSize (by omega) N
  have h3 : 2 ^ wordSize (m + 2) N ≤ 2 ^ wordSize (m + 2) (N + B) :=
    Nat.pow_le_pow_right (by omega) (wordSize_mono_right (m + 2) (by omega))
  exact lt_of_le_of_lt h1 (lt_of_lt_of_le h2 h3)

/-- Word-size multiplier constant $c_{104}(q, \delta, c_{41}, C_{41})$ for `alg104Prog`. -/
def alg104WordConst (q δ c41 C41 : ℕ) : ℕ :=
  (c41 + C41 + maxFolioRepCode q δ + maxFolioEncLen101 q δ + maxFolioEncWord q δ + q + 30) + 2

/-- **Proof of `Alg104Spec` for Graph Minors XIII, Algorithm (10.4)** (pages 107–108, by the proof
of **(10.3)** on page 108):
For any parameters `p, q, δ, ω : ℕ`, with `h = GM13.sec10MaxWallHeight GM13.theorem_10_2_proof.{0, 0} q δ`,
the Word RAM program
`alg104Prog` with `case3Decoder : Case3BlockDecoder` satisfies `Alg104Spec case3Decoder p q δ h ω`. -/
theorem alg104Spec_proved {p q δ ω : ℕ} :
    Alg104Spec case3Decoder p q δ
      (GM13.sec10MaxWallHeight GM13.theorem_10_2_proof.{0, 0} q δ) ω := by
  rcases alg41Spec101_of_claim41
      (fun δ ξ B => ⟨alg41CoreProg δ ξ B, algorithm_4_1_core δ ξ B⟩)
      p (q + 3) δ (max ω 2 + q) with ⟨prog41, C41, c41, hc41, hC41, h41_prog⟩
  let h := GM13.sec10MaxWallHeight GM13.theorem_10_2_proof.{0, 0} q δ
  let m := c41 + C41 + maxFolioRepCode q δ + maxFolioEncLen101 q δ + maxFolioEncWord q δ + q + 30
  have hC_pos : 0 < alg104TimeConst q δ h C41 := by
    unfold alg104TimeConst alg101TimeConst; omega
  refine ⟨alg104Prog p q δ h C41 prog41, alg104TimeConst q δ h C41, m + 2, by omega, hC_pos, ?_⟩
  intro w n_i G_i X' block s N H S_H 𝒜 hw hx_card hHypC hH_height hbd_spec hG hX hblock
  -- 1. Unpack `parseCase3Block` from `HypothesisC`
  rcases exists_parsedCase3Block_of_hypothesisC G_i X' block hHypC with ⟨blk, hparse_blk⟩
  have hH_eq : H = blk.toGMWall := by
    dsimp [H]; simp [case3Decoder, case3WallOfDel, hparse_blk]
  have hSH_eq : S_H = blk.toSociety := by
    dsimp [S_H]; simp [case3Decoder, case3SocietyOfDel, hparse_blk]
  have hdiv_eq : 𝒜 = blk.toDivision := by
    dsimp [𝒜]; simp [case3Decoder, case3DivisionOfDel, hparse_blk]
  have hC_blk :
      GM13.HypothesisC G_i.toGMDigraph X'.toNatSet.ncard X'.toNatSet
        blk.toGMWall blk.toSociety blk.toDivision := by
    rwa [hH_eq, hSH_eq, hdiv_eq] at hHypC
  have hblk_h : blk.wallSec.h = h := by
    have h1 : blk.toGMWall.height = blk.wallSec.h := rfl
    rw [← h1, ← hH_eq, hH_height]
  have hH_ge : GM13.sec10WallHeight GM13.theorem_10_2_proof.{0, 0} X'.card δ ≤ blk.wallSec.h := by
    rw [hblk_h]
    exact GM13.sec10WallHeight_le_sec10MaxWallHeight hx_card δ
  have hbd_all :
      ∀ j : Fin blk.members.length,
        isMemberInterior blk.wallSec.W (blk.members[j.1]'j.2) = true →
        MemberBranchDecompValid G_i X' ω (blk.members[j.1]'j.2) := by
    intro j hInt
    have hr_mem : (blk.members[j.1]'j.2) ∈ blk.members := List.getElem_mem j.2
    have hInt_gm :
        GM13.IsInteriorMember blk.toGMWall blk.toDivision
          ((blk.members[j.1]'j.2).toSubgraph (delGraph G_i X')) :=
      (isInteriorMember_toSubgraph_iff blk hr_mem).mpr hInt
    rw [← hH_eq, ← hdiv_eq] at hInt_gm
    have hbd_j := hbd_spec hInt_gm
    dsimp only at hbd_j
    rw [blk.branchDecomp_toSubgraph hparse_blk hr_mem] at hbd_j
    exact hbd_j
  -- 2. Establish word-size bounds from `wordSize (m + 2) (N + block.length) ≤ w`
  have hpow_le : 2 ^ wordSize (m + 2) (N + block.length) ≤ 2 ^ w :=
    Nat.pow_le_pow_right (by omega) hw
  have hmain_w : (m + 1) * ((N + 2) * (N + 2)) < 2 ^ w :=
    lt_of_lt_of_le (mul_sq_lt_two_pow_wordSize N block.length m) hpow_le
  have hsq_pos : 1 ≤ (N + 2) * (N + 2) := Nat.mul_pos (by omega) (by omega)
  have hm_lt_w : m + 1 < 2 ^ w :=
    lt_of_le_of_lt (Nat.le_mul_of_pos_right (m + 1) hsq_pos) hmain_w
  have hn_le_N : n_i ≤ N := by dsimp [N]; omega
  have hnsq_le : n_i * n_i ≤ (N + 2) * (N + 2) :=
    Nat.mul_le_mul (by omega) (by omega)
  have h2nsq_w : 2 + 6 * (n_i * n_i) < 2 ^ w := by
    have h1 : 7 * ((N + 2) * (N + 2)) ≤ (m + 1) * ((N + 2) * (N + 2)) :=
      Nat.mul_le_mul_right _ (by dsimp [m]; omega)
    omega
  have hN_w : 24 * N < 2 ^ w := by
    have h1 : N ≤ (N + 2) * (N + 2) := le_trans (by omega) (Nat.le_mul_self (N + 2))
    have h2 : 24 * ((N + 2) * (N + 2)) ≤ (m + 1) * ((N + 2) * (N + 2)) :=
      Nat.mul_le_mul_right _ (by dsimp [m]; omega)
    have h3 := Nat.mul_le_mul_left 24 h1
    omega
  have hw41 : wordSize c41 N ≤ w :=
    le_trans (wordSize_mono_left (by dsimp [m]; omega) N)
      (le_trans (wordSize_mono_right (m + 2) (by omega)) hw)
  have hC41_w : C41 < 2 ^ w := by dsimp [m] at hm_lt_w; omega
  have hvis_cap_w : (2 + n_i) + N * memberPerCap C41 n_i G_i.numEdges < 2 ^ w := by
    have hcap_eq : N * memberPerCap C41 n_i G_i.numEdges = (C41 + 18) * (N * N) := by
      unfold memberPerCap
      change N * (C41 * N + 18 * N) = (C41 + 18) * (N * N)
      ring
    rw [hcap_eq]
    have hN2 : N * N ≤ (N + 2) * (N + 2) := Nat.mul_le_mul (by omega) (by omega)
    have h1 : (C41 + 18) * (N * N) ≤ (C41 + 18) * ((N + 2) * (N + 2)) :=
      Nat.mul_le_mul_left (C41 + 18) hN2
    have h2 : 2 + n_i ≤ (N + 2) * (N + 2) :=
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
  -- 3. Execute `alg104Prog`
  rw [← hblk_h]
  exact alg104Prog_exec h41_prog G_i hx_card blk hC_blk hH_ge hbd_all block hparse_blk
    h2nsq_w hN_w hw41 hC41_w hvis_cap_w hw_code hw_len hw_word hw_q hG hX hblock

/-- Specialization of `alg104Spec_proved` to the parameters
`p = alg62Param ξ δ`, `q = (alg62Param ξ δ).choose 2 + ξ - 1`, `h = sec105WallHeight ξ δ`,
and `ω = sec105BranchWidth ξ δ` used by `folio_of_interfaces` and `gm13_algorithm_10_5` in
`GraphMinor/Compute/Algorithm105.lean`. -/
theorem alg104Spec_sec105 (ξ δ : ℕ) :
    Alg104Spec case3Decoder (alg62Param ξ δ) ((alg62Param ξ δ).choose 2 + ξ - 1) δ
      (sec105WallHeight ξ δ) (sec105BranchWidth ξ δ) :=
  alg104Spec_proved

/-- Graph Minors XIII, Algorithm (10.4), pages 107–108:
"A vertex irrelevant to the $\delta$-folio of $G$ relative to $X$."
The program of `Alg104Spec` computes this vertex in quadratic time, using the
proved (4.1) program and the homogeneous-wall recursion of (10.3). -/
theorem gm13_algorithm_10_4 (p q δ ω : ℕ) :
    Alg104Spec case3Decoder p q δ
      (GM13.sec10MaxWallHeight GM13.theorem_10_2_proof.{0, 0} q δ) ω :=
  alg104Spec_proved

end GraphMinor.Compute
