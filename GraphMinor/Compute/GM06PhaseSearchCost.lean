module

public import GraphMinor.Compute.GM06PhaseSize
public import GraphMinor.Compute.GM06PhaseSearchExec

/-!
# A uniform bound for a component search

The explicit FIND_4 cost in Sections 12 and 13 of our proof of VI (5.7) (outlined in
`GraphMinor/GM06/Alg57Algorithm.lean`) is cubic in the copied label spaces and boundary lengths.
Every one of those sizes is bounded by the current phase size. This file includes boundary
preparation and a successful core installation in one uniform cubic bound.
-/

public section
namespace GraphMinor.Compute

private theorem directed_cost_le {B n m r u d : ℕ}
    (hn : n ≤ B) (hm : m ≤ B) (hr : r ≤ B) (hu : u ≤ B) (hd : d ≤ B) :
    gm06Find4DartsCost n m r u d ≤ 10000 * (B + 1) ^ 3 := by
  let Q := B + 1
  have hQ : 1 ≤ Q := by simp only [Q]; omega
  have hnQ : n ≤ Q := by simp only [Q]; omega
  have hmQ : m ≤ Q := by simp only [Q]; omega
  have hrQ : r ≤ Q := by simp only [Q]; omega
  have huQ : u ≤ Q := by simp only [Q]; omega
  have hdQ : d ≤ Q := by simp only [Q]; omega
  have hQQ : Q ≤ Q * Q := by simpa only [Nat.mul_one] using Nat.mul_le_mul_left Q hQ
  have hQQQ : Q * Q ≤ Q * Q * Q := by simpa only [Nat.mul_one] using Nat.mul_le_mul_left (Q * Q) hQ
  have hnn : n * n ≤ Q * Q := Nat.mul_le_mul hnQ hnQ
  have hcore : 523 + 251 * n + 150 * m + 100 * r + 100 * u + 78 * (n * n) + 129 * d ≤ 2100 * (Q * Q) := by
    omega
  have hscan : r * (523 + 251 * n + 150 * m + 100 * r + 100 * u + 78 * (n * n) + 129 * d) ≤
      2100 * (Q * Q * Q) := by
    calc
      _ ≤ Q * (2100 * (Q * Q)) := Nat.mul_le_mul hrQ hcore
      _ = _ := by ring
  have htailCore : 70 + 13 * (2 * m) ≤ 100 * Q := by omega
  have htail : n * (70 + 13 * (2 * m)) ≤ 100 * (Q * Q) := by
    calc
      _ ≤ Q * (100 * Q) := Nat.mul_le_mul hnQ htailCore
      _ = _ := by ring
  have hrest : 36 + 127 + 100 * n + 350 * m + 100 * (r + 1) + 100 * u ≤ 1000 * Q := by omega
  unfold gm06Find4DartsCost gm06Find4Cost
  have hpow : (B + 1) ^ 3 = Q * Q * Q := by simp only [Q]; ring
  rw [hpow]
  omega

/-- The cost of every actual cuff-indexed component search is
uniformly cubic in the current structural input sizes. -/
theorem gm06Reduction4PhaseSearchCost_le_size {m i : ℕ} (x : GM06SuccessorInput)
    (hnd : x.rotations.flatten.Nodup) (hcount : x.linkage.length = x.innerCuff.length)
    (hi : i < x.innerCuff.length) (part : GM06CutData) (hp : part ∈ gm06PhaseComponents x m) :
    gm06Reduction4PhaseSearchCost x m i part ≤ 2000000 * gm06PhaseSize x m ^ 3 := by
  let N := gm06PhaseSize x m
  have hN : 1 ≤ N := gm06PhaseSize_pos x m
  have hik : i < x.linkage.length := by omega
  have hk : 0 < x.innerCuff.length := by omega
  have hnext : gm06PhaseNext x i < x.linkage.length := by
    have hmod := Nat.mod_lt (i + 1) hk
    exact hcount ▸ hmod
  have hr : (x.linkage[i]?.getD []).length ≤ N := by
    have hs : [x.linkage[i]].Sublist x.linkage := List.singleton_sublist.mpr (List.getElem_mem hik)
    have hl : x.linkage[i].length ≤ x.linkage.flatten.length := by simpa using hs.flatten.length_le
    simp only [List.getElem?_eq_getElem hik, Option.getD_some]
    simp only [N, gm06PhaseSize]
    omega
  have hu : (x.linkage[gm06PhaseNext x i]?.getD []).length + 1 ≤ 2 * N := by
    have hs : [x.linkage[gm06PhaseNext x i]].Sublist x.linkage := List.singleton_sublist.mpr (List.getElem_mem hnext)
    have hl : x.linkage[gm06PhaseNext x i].length ≤ x.linkage.flatten.length := by simpa using hs.flatten.length_le
    simp only [List.getElem?_eq_getElem hnext, Option.getD_some]
    simp only [N, gm06PhaseSize]
    omega
  obtain ⟨_, _, hsub, _⟩ := gm06PhaseComponents_encoding x hnd part hp
  have hd := gm06SplitRotationRows_length_le
    (gm06BuildCutTables x.vertexCount m x.endpoints x.linkage x.innerCuff x.outerCuff) x.rotations
  have hflat : part.rotations.flatten.length ≤ 2 * N := by
    have hl := hsub.length_le
    change part.rotations.flatten.length ≤ (gm06SplitRotationRows _ x.rotations).flatten.length at hl
    simp only [N, gm06PhaseSize]
    omega
  have hvertices : 2 * x.vertexCount ≤ 4 * N := by simp only [N, gm06PhaseSize]; omega
  have hedges : 2 * (m + x.innerCuff.length + x.outerCuff.length) ≤ 4 * N := by simp only [N, gm06PhaseSize]; omega
  have hcost := directed_cost_le hvertices hedges (by omega : (x.linkage[i]?.getD []).length ≤ 4 * N)
    (by omega : (x.linkage[gm06PhaseNext x i]?.getD []).length + 1 ≤ 4 * N)
    (by omega : part.rotations.flatten.length ≤ 4 * N)
  have h5 : 4 * N + 1 ≤ 5 * N := by omega
  have hcost' := hcost.trans (Nat.mul_le_mul_left 10000 (Nat.pow_le_pow_left h5 3))
  have hpow : (5 * N) ^ 3 = 125 * N ^ 3 := by ring
  rw [hpow] at hcost'
  have hpath := gm06FaceCode_length x.linkage
  have hprefix : 1000 + 1000 * (gm06EncodeRows x.linkage).length + 400 * x.vertexCount +
      100 * (m + x.innerCuff.length + x.outerCuff.length) ≤ 3000 * N := by
    simp only [N, gm06PhaseSize]
    omega
  have hNN : N ≤ N * N := by simpa only [Nat.mul_one] using Nat.mul_le_mul_left N hN
  have hNNN : N * N ≤ N * N * N := by simpa only [Nat.mul_one] using Nat.mul_le_mul_left (N * N) hN
  have hcube : N ≤ N ^ 3 := by rw [show N ^ 3 = N * N * N by ring]; exact hNN.trans hNNN
  unfold gm06Reduction4PhaseSearchCost
  change _ ≤ 2000000 * N ^ 3
  omega

/-- The complete component face preparation has a uniform quadratic
bound, including construction of its active-end list. -/
theorem gm06PhaseComponentFacesCost_le_size {m : ℕ} (x : GM06SuccessorInput)
    (hnd : x.rotations.flatten.Nodup) (part : GM06CutData) (hp : part ∈ gm06PhaseComponents x m) :
    300 + 2 * x.vertexCount + 1300 * (m + x.innerCuff.length + x.outerCuff.length) +
      100 * part.rotations.length + 100 * part.rotations.flatten.length +
      part.activeDarts.length * (60 + 72 * (m + x.innerCuff.length + x.outerCuff.length)) ≤
        10000 * gm06PhaseSize x m ^ 2 := by
  let S := gm06PhaseSize x m
  have hS : 1 ≤ S := gm06PhaseSize_pos x m
  obtain ⟨hn, ha, _, hr, _, _⟩ := gm06PhaseSize_bounds x m
  have hcode := gm06PhaseComponents_code_length x hnd part hp
  have hlength := gm06FaceCode_length part.rotations
  have hrot : part.rotations.length ≤ 2 * S := by omega
  have hflat : part.rotations.flatten.length ≤ 2 * S := by omega
  obtain ⟨_, _, _, _, hcanon, _⟩ := gm06PhaseComponents_encoding x hnd part hp
  have hactive : part.activeDarts.length ≤ 4 * (m + x.innerCuff.length + x.outerCuff.length) := by
    rw [hcanon]
    exact (List.length_filter_le _ _).trans (by simp)
  have hactiveS : part.activeDarts.length ≤ 4 * S := by omega
  have hcross : part.activeDarts.length * (m + x.innerCuff.length + x.outerCuff.length) ≤ 4 * (S * S) := by
    calc
      _ ≤ (4 * S) * S := Nat.mul_le_mul hactiveS ha
      _ = _ := by ring
  have hSS : S ≤ S * S := by simpa only [Nat.mul_one] using Nat.mul_le_mul_left S hS
  change _ ≤ 10000 * S ^ 2
  rw [pow_two]
  nlinarith only [hn, ha, hrot, hflat, hactiveS, hcross, hSS, hS]

end GraphMinor.Compute
