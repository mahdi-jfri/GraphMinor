module

public import GraphMinor.Compute.Algorithm41Aux5

/-!
# Boundary Merge and Table Combination Step for GM XIII (4.1)

This file implements the Word RAM boundary-merging gadget (`mergeBoundaryProg`) and the table
combination step (`combineStepProg`) for Algorithm (4.1) of Robertson and Seymour,
*Graph Minors. XIII. The Disjoint Paths Problem* (pages 75–76):

1. **Section 1 (`rankBelow`, `cutoffAt`, `encBoundaryMask`, `mcodeDigit`):**
   Proves the rank-cutoff invariants for sorted boundary arrays and the base-8 encoding of the
   3-bit boundary membership mask `(ZA, ZB, Z')` on `ZA ∪ ZB`.
2. **Section 2 (`mergeBoundaryProg` and `mergeBoundaryProg_exec`):**
   Merges the sorted boundary arrays `(a_acc_zV, a_acc_zI)` of `(ZA, EA)` and `(a_rhs_zV, a_rhs_zI)`
   of `(ZB, EB)` in `O(Q_max ξ ω)` steps into `(a_out_zV, a_out_zI)` for `(Z', EA ∪ EB)` while
   accumulating `mcode = encBoundaryMask ZA ZB Z'` in register `13`.
3. **Section 3 (`canonCombineRecipes`, `combineStepProg`, and `combineStepProg_exec`):**
   Dispatches on `(r_tidA, r_tidB, mcode)` via `branchOnBound` to construct the combined
   `ValidPieceBuffer` for `rawCombineTables δ α_A α_B hcov β es_A es_B` in `bufA`.
-/

@[expose] public section

namespace GraphMinor.Compute

open SimpleGraph

/-! ### Section 1: `rankBelow`, `cutoffAt`, and Base-8 Boundary Mask Encoding -/

private theorem getD_set_ne (L : List ℕ) (k v p : ℕ) (hne : p ≠ k) :
    (L.set k v).getD p 0 = L.getD p 0 := by
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_set_ne hne.symm]

private theorem getD_set_eq (L : List ℕ) (k v : ℕ) (hk : k < L.length) :
    (L.set k v).getD k 0 = v := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_set_self hk, Option.getD_some]

theorem finsetSubIdx_strictMono {n : ℕ} {S₁ S₂ : Finset (Fin n)} (hsub : S₁ ⊆ S₂) :
    StrictMono (finsetSubIdx hsub) := by
  intro i j hij
  by_contra hge
  have hle : finsetSubIdx hsub j ≤ finsetSubIdx hsub i := not_lt.mp hge
  have hle' : finsetRootFn S₂ (finsetSubIdx hsub j) ≤ finsetRootFn S₂ (finsetSubIdx hsub i) :=
    (finsetRootFn_strictMono S₂).monotone hle
  rw [finsetRootFn_finsetSubIdx_apply, finsetRootFn_finsetSubIdx_apply] at hle'
  exact not_lt_of_ge hle' (finsetRootFn_strictMono S₁ hij)

private theorem card_filter_val_lt {q k : ℕ} (hk : k ≤ q) :
    (Finset.univ.filter (fun i : Fin q => i.1 < k)).card = k := by
  have hmap : (Finset.univ.filter (fun i : Fin q => i.1 < k)).image Fin.val = Finset.range k := by
    ext m
    simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_range]
    exact ⟨by rintro ⟨i, hi, rfl⟩; exact hi, fun hm => ⟨⟨m, by omega⟩, hm, rfl⟩⟩
  rw [← Finset.card_image_of_injective _ Fin.val_injective, hmap, Finset.card_range]

private theorem downward_closed_eq_filter_lt_card {q : ℕ} (F : Finset (Fin q))
    (hdown : ∀ i j : Fin q, i < j → j ∈ F → i ∈ F) :
    F = Finset.univ.filter (fun i : Fin q => i.1 < F.card) := by
  have hcard_le : F.card ≤ q := by
    calc F.card ≤ (Finset.univ : Finset (Fin q)).card := Finset.card_le_card (Finset.subset_univ _)
      _ = q := Finset.card_fin q
  have hsub : F ⊆ Finset.univ.filter (fun i : Fin q => i.1 < F.card) := by
    intro j hj
    rw [Finset.mem_filter]
    refine ⟨Finset.mem_univ j, ?_⟩
    have hsub_j : Finset.univ.filter (fun i : Fin q => i.1 < j.1 + 1) ⊆ F := by
      intro i hi
      rw [Finset.mem_filter] at hi
      by_cases hij : i = j
      · exact hij ▸ hj
      · have hlt : i < j := Fin.lt_def.mpr (by have := Fin.ext_iff.not.mp hij; omega)
        exact hdown i j hlt hj
    have hle_j := Finset.card_le_card hsub_j
    rw [card_filter_val_lt (by omega)] at hle_j
    omega
  exact Finset.eq_of_subset_of_card_le hsub (by rw [card_filter_val_lt hcard_le])

/-- Number of elements of `S : Finset (Fin n)` with value strictly less than `v`. -/
def rankBelow {n : ℕ} (S : Finset (Fin n)) (v : ℕ) : ℕ :=
  (Finset.univ.filter (fun i : Fin S.card => (finsetRootFn S i).1 < v)).card

theorem rankBelow_le_card {n : ℕ} (S : Finset (Fin n)) (v : ℕ) :
    rankBelow S v ≤ S.card := by
  calc rankBelow S v ≤ (Finset.univ : Finset (Fin S.card)).card :=
        Finset.card_le_card (Finset.subset_univ _)
    _ = S.card := Finset.card_fin _

theorem lt_rankBelow_iff {n : ℕ} (S : Finset (Fin n)) (v : ℕ) (i : Fin S.card) :
    i.1 < rankBelow S v ↔ (finsetRootFn S i).1 < v := by
  let F := Finset.univ.filter (fun j : Fin S.card => (finsetRootFn S j).1 < v)
  have hdown : ∀ a b : Fin S.card, a < b → b ∈ F → a ∈ F := by
    intro a b hab hb
    simp only [F, Finset.mem_filter, Finset.mem_univ, true_and] at hb ⊢
    exact Nat.lt_trans (finsetRootFn_strictMono S hab) hb
  have heq := downward_closed_eq_filter_lt_card F hdown
  have hmem : i ∈ F ↔ i ∈ Finset.univ.filter (fun j : Fin S.card => j.1 < F.card) := by
    rw [← heq]
  simpa [F, rankBelow] using hmem.symm

/-- Value cutoff at index `k` of `U : Finset (Fin n)`: `(finsetRootFn U ⟨k, hk⟩).1` for
`k < U.card`, and `n` for `k ≥ U.card`. -/
def cutoffAt {n : ℕ} (U : Finset (Fin n)) (k : ℕ) : ℕ :=
  if hk : k < U.card then (finsetRootFn U ⟨k, hk⟩).1 else n

theorem cutoffAt_le {n : ℕ} (U : Finset (Fin n)) (k : ℕ) :
    cutoffAt U k ≤ n := by
  dsimp [cutoffAt]; split_ifs with hk
  · exact le_of_lt (finsetRootFn U ⟨k, hk⟩).2
  · exact le_refl n

theorem rankBelow_cutoffAt_zero {n : ℕ} {U S : Finset (Fin n)} (hSU : S ⊆ U) :
    rankBelow S (cutoffAt U 0) = 0 := by
  by_contra hne
  have hpos : 0 < rankBelow S (cutoffAt U 0) := Nat.pos_of_ne_zero hne
  have hle := rankBelow_le_card S (cutoffAt U 0)
  let i0 : Fin S.card := ⟨0, by omega⟩
  have hlt := (lt_rankBelow_iff S (cutoffAt U 0) i0).mp hpos
  rcases exists_finsetRootFn_eq (hSU (finsetRootFn_mem S i0)) with ⟨j, hj⟩
  have hU_pos : 0 < U.card := by have := j.2; omega
  have hcut : cutoffAt U 0 = (finsetRootFn U ⟨0, hU_pos⟩).1 := by simp [cutoffAt, hU_pos]
  have hle_j : (finsetRootFn U ⟨0, hU_pos⟩).1 ≤ (finsetRootFn U j).1 :=
    Fin.le_def.mp ((finsetRootFn_strictMono U).monotone (Fin.le_def.mpr (Nat.zero_le j.1)))
  rw [hcut, ← hj] at hlt
  omega

theorem rankBelow_cutoffAt_full {n : ℕ} (U S : Finset (Fin n)) :
    rankBelow S (cutoffAt U U.card) = S.card := by
  have hcut : cutoffAt U U.card = n := by simp [cutoffAt]
  rw [hcut]
  unfold rankBelow
  have hfilt : Finset.univ.filter (fun i : Fin S.card => (finsetRootFn S i).1 < n) = Finset.univ := by
    ext i; simp
  rw [hfilt, Finset.card_fin]

theorem mem_subset_lt_cutoffAt_succ_iff {n : ℕ} {U S : Finset (Fin n)} (hSU : S ⊆ U)
    {k : ℕ} (hk : k < U.card) (u : Fin n) (hu : u ∈ S) :
    u.1 < cutoffAt U (k + 1) ↔ u.1 ≤ (finsetRootFn U ⟨k, hk⟩).1 := by
  rcases exists_finsetRootFn_eq (hSU hu) with ⟨j, rfl⟩
  constructor
  · intro hlt
    by_contra hgt
    have hlt_w : finsetRootFn U ⟨k, hk⟩ < finsetRootFn U j :=
      Fin.lt_def.mpr (not_le.mp hgt)
    have hkj : k < j.1 := by
      by_contra hle
      exact not_le_of_gt hlt_w ((finsetRootFn_strictMono U).monotone (Fin.le_def.mpr (not_lt.mp hle)))
    have hk1 : k + 1 < U.card := by have := j.2; omega
    have hcut : cutoffAt U (k + 1) = (finsetRootFn U ⟨k + 1, hk1⟩).1 := by simp [cutoffAt, hk1]
    have hle_j : (finsetRootFn U ⟨k + 1, hk1⟩).1 ≤ (finsetRootFn U j).1 :=
      Fin.le_def.mp ((finsetRootFn_strictMono U).monotone (Fin.le_def.mpr (by dsimp; omega)))
    rw [hcut] at hlt
    omega
  · intro hle
    by_cases hk1 : k + 1 < U.card
    · simp only [cutoffAt, hk1, ↓reduceDIte]
      have hlt_next : (finsetRootFn U ⟨k, hk⟩).1 < (finsetRootFn U ⟨k + 1, hk1⟩).1 :=
        finsetRootFn_strictMono U (Fin.lt_def.mpr (Nat.lt_succ_self k))
      omega
    · simp only [cutoffAt, hk1, ↓reduceDIte]
      exact (finsetRootFn U j).2

theorem rankBelow_cutoffAt_step_mem {n : ℕ} {U S : Finset (Fin n)} (hSU : S ⊆ U)
    {k : ℕ} (hk : k < U.card) (hw : finsetRootFn U ⟨k, hk⟩ ∈ S) :
    ∃ (hi : rankBelow S (cutoffAt U k) < S.card),
      finsetRootFn S ⟨rankBelow S (cutoffAt U k), hi⟩ = finsetRootFn U ⟨k, hk⟩ ∧
      rankBelow S (cutoffAt U (k + 1)) = rankBelow S (cutoffAt U k) + 1 := by
  have hcut_k : cutoffAt U k = (finsetRootFn U ⟨k, hk⟩).1 := by simp [cutoffAt, hk]
  rcases exists_finsetRootFn_eq hw with ⟨i₀, hi₀⟩
  have hi_eq : rankBelow S (cutoffAt U k) = i₀.1 := by
    have h1 : ¬(i₀.1 < rankBelow S (cutoffAt U k)) := by
      rw [lt_rankBelow_iff, hcut_k, hi₀]; exact Nat.lt_irrefl _
    have h2 : ∀ j : Fin S.card, j.1 < i₀.1 → j.1 < rankBelow S (cutoffAt U k) := by
      intro j hj
      rw [lt_rankBelow_iff, hcut_k, ← hi₀]
      exact finsetRootFn_strictMono S (Fin.lt_def.mpr hj)
    by_contra hne
    have hlt : rankBelow S (cutoffAt U k) < i₀.1 := by omega
    have hi₀_lt := i₀.2
    have hself := h2 ⟨rankBelow S (cutoffAt U k), by omega⟩ hlt
    dsimp at hself
    omega
  have hi_lt : rankBelow S (cutoffAt U k) < S.card := by rw [hi_eq]; exact i₀.2
  refine ⟨hi_lt, ?_, ?_⟩
  · rw [show (⟨rankBelow S (cutoffAt U k), hi_lt⟩ : Fin S.card) = i₀ from Fin.ext hi_eq, hi₀]
  · have h3 : ¬(i₀.1 + 1 < rankBelow S (cutoffAt U (k + 1))) := by
      intro hlt
      have hi1_lt : i₀.1 + 1 < S.card :=
        Nat.lt_of_lt_of_le hlt (rankBelow_le_card S (cutoffAt U (k + 1)))
      let j1 : Fin S.card := ⟨i₀.1 + 1, hi1_lt⟩
      have hcut1 := (lt_rankBelow_iff S (cutoffAt U (k + 1)) j1).mp hlt
      rw [mem_subset_lt_cutoffAt_succ_iff hSU hk (finsetRootFn S j1) (finsetRootFn_mem S j1)] at hcut1
      have hgt : (finsetRootFn U ⟨k, hk⟩).1 < (finsetRootFn S j1).1 := by
        rw [← hi₀]; exact finsetRootFn_strictMono S (Fin.lt_def.mpr (Nat.lt_succ_self i₀.1))
      omega
    have h4 : i₀.1 < rankBelow S (cutoffAt U (k + 1)) := by
      rw [lt_rankBelow_iff, mem_subset_lt_cutoffAt_succ_iff hSU hk (finsetRootFn S i₀)
        (finsetRootFn_mem S i₀), hi₀]
    omega

theorem rankBelow_cutoffAt_step_notMem {n : ℕ} {U S : Finset (Fin n)} (hSU : S ⊆ U)
    {k : ℕ} (hk : k < U.card) (hw : finsetRootFn U ⟨k, hk⟩ ∉ S) :
    rankBelow S (cutoffAt U (k + 1)) = rankBelow S (cutoffAt U k) ∧
    (∀ hi : rankBelow S (cutoffAt U k) < S.card,
      (finsetRootFn U ⟨k, hk⟩).1 < (finsetRootFn S ⟨rankBelow S (cutoffAt U k), hi⟩).1) := by
  have hcut_k : cutoffAt U k = (finsetRootFn U ⟨k, hk⟩).1 := by simp [cutoffAt, hk]
  refine ⟨?_, fun hi => ?_⟩
  · unfold rankBelow
    congr 1
    ext j
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, hcut_k]
    rw [mem_subset_lt_cutoffAt_succ_iff hSU hk (finsetRootFn S j) (finsetRootFn_mem S j)]
    have hne : (finsetRootFn S j).1 ≠ (finsetRootFn U ⟨k, hk⟩).1 := fun h =>
      hw (Fin.ext h ▸ finsetRootFn_mem S j)
    omega
  · have hnot : ¬(rankBelow S (cutoffAt U k) < rankBelow S (cutoffAt U k)) := Nat.lt_irrefl _
    rw [lt_rankBelow_iff S (cutoffAt U k) ⟨rankBelow S (cutoffAt U k), hi⟩] at hnot
    have hne : (finsetRootFn S ⟨rankBelow S (cutoffAt U k), hi⟩).1 ≠ (finsetRootFn U ⟨k, hk⟩).1 :=
      fun h => hw (Fin.ext h ▸ finsetRootFn_mem S ⟨rankBelow S (cutoffAt U k), hi⟩)
    omega

theorem packBase_append (B : ℕ) (xs ys : List ℕ) :
    packBase B (xs ++ ys) = packBase B xs + B ^ xs.length * packBase B ys := by
  induction xs with
  | nil => simp [packBase]
  | cons x xs ih =>
    simp only [List.cons_append, packBase, List.length_cons, ih, Nat.pow_succ']
    rw [Nat.left_distrib, ← Nat.add_assoc, ← Nat.mul_assoc]

theorem packBase_append_singleton (B : ℕ) (xs : List ℕ) (d : ℕ) :
    packBase B (xs ++ [d]) = packBase B xs + d * B ^ xs.length := by
  rw [packBase_append]; simp [packBase, Nat.mul_comm]

/-- Extract the `k`-th base-8 digit `(mcode / 8 ^ k) % 8` from `mcode`. -/
def mcodeDigit (mcode k : ℕ) : ℕ :=
  (mcode / 8 ^ k) % 8

theorem mcodeDigit_packBase (ds : List ℕ) (hds : ∀ d ∈ ds, d < 8) (k : ℕ) :
    mcodeDigit (packBase 8 ds) k = ds.getD k 0 := by
  induction ds generalizing k with
  | nil => simp [mcodeDigit, packBase]
  | cons d ds ih =>
    have hd : d < 8 := hds d List.mem_cons_self
    have hds' : ∀ x ∈ ds, x < 8 := fun x hx => hds x (List.mem_cons_of_mem d hx)
    cases k with
    | zero =>
      simp only [mcodeDigit, Nat.pow_zero, Nat.div_one, packBase, List.getD_cons_zero]
      rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hd]
    | succ k' =>
      simp only [mcodeDigit, Nat.pow_succ', packBase, List.getD_cons_succ]
      rw [← Nat.div_div_eq_div_mul, Nat.add_mul_div_left _ _ (by decide : 0 < 8),
          Nat.div_eq_of_lt hd, Nat.zero_add]
      exact ih hds' k'

/-- 3-bit membership digit `∈ {1, ..., 7}` for the `k`-th vertex of `ZA ∪ ZB`:
bit 0 is `∈ ZA`, bit 1 is `∈ ZB`, bit 2 is `∈ Z'`. -/
def boundaryMaskDigit {n : ℕ} (ZA ZB Z' : Finset (Fin n)) (k : Fin (ZA ∪ ZB).card) : ℕ :=
  let w := finsetRootFn (ZA ∪ ZB) k
  (if w ∈ ZA then 1 else 0) + (if w ∈ ZB then 2 else 0) + (if w ∈ Z' then 4 else 0)

theorem boundaryMaskDigit_pos_and_lt {n : ℕ} (ZA ZB Z' : Finset (Fin n))
    (k : Fin (ZA ∪ ZB).card) :
    1 ≤ boundaryMaskDigit ZA ZB Z' k ∧ boundaryMaskDigit ZA ZB Z' k < 8 := by
  dsimp [boundaryMaskDigit]
  have hmem := Finset.mem_union.mp (finsetRootFn_mem (ZA ∪ ZB) k)
  rcases hmem with hA | hB <;> split_ifs <;> omega

/-- Base-8 integer encoding of the boundary membership masks of `(ZA, ZB, Z')` on `ZA ∪ ZB`. -/
def encBoundaryMask {n : ℕ} (ZA ZB Z' : Finset (Fin n)) : ℕ :=
  packBase 8 ((List.finRange (ZA ∪ ZB).card).map (boundaryMaskDigit ZA ZB Z'))

/-- Strict upper bound `8 ^ (Q_max ξ ω)` on `encBoundaryMask ZA ZB Z'`. -/
def M_max (ξ ω : ℕ) : ℕ :=
  8 ^ (Q_max ξ ω)

theorem encBoundaryMask_lt {n ξ ω : ℕ} (ZA ZB Z' : Finset (Fin n))
    (hq : (ZA ∪ ZB).card ≤ Q_max ξ ω) :
    encBoundaryMask ZA ZB Z' < M_max ξ ω := by
  unfold encBoundaryMask M_max
  let ds := (List.finRange (ZA ∪ ZB).card).map (boundaryMaskDigit ZA ZB Z')
  have hlen : ds.length = (ZA ∪ ZB).card := by simp [ds]
  have hlt : packBase 8 ds < 8 ^ ds.length := by
    refine packBase_lt (by decide : 0 < 8) ds fun d hd => ?_
    rcases List.mem_map.mp hd with ⟨k, _, rfl⟩
    exact (boundaryMaskDigit_pos_and_lt ZA ZB Z' k).2
  rw [hlen] at hlt
  exact Nat.lt_of_lt_of_le hlt (Nat.pow_le_pow_right (by decide : 0 < 8) hq)

/-! ### Section 2: Word RAM Boundary Merge Program (`mergeBoundaryProg`) and Execution Proof -/

/-- Condition `(r_10 < r_qA) || (r_11 < r_qB)` of the boundary merge loop. -/
def mergeBoundaryCond : Expr :=
  .op .lt (.const 0)
    (.op .add (.op .lt (.reg 10) (.reg r_qA)) (.op .lt (.reg 11) (.reg r_qB)))

/-- Body of the boundary merge loop:
- `r_10 = i` (index in `ZA`), `r_11 = j` (index in `ZB`), `r_12 = k'` (index in `Z'`),
- `r_13 = mcode`, `r_14 = 8 ^ k`,
- `r_15..r_19` are scratch registers. -/
def mergeBoundaryBody : Cmd :=
  .seq (.ite (.op .lt (.reg 10) (.reg r_qA))
      (.assign 15 (.read a_acc_zV (.reg 10)))
      (.assign 15 (.reg 0)))
  (.seq (.ite (.op .lt (.reg 11) (.reg r_qB))
      (.assign 16 (.read a_rhs_zV (.reg 11)))
      (.assign 16 (.reg 0)))
  (.seq (.ite (.op .lt (.reg 15) (.reg 16))
      (.assign 17 (.reg 15))
      (.assign 17 (.reg 16)))
  (.seq (.assign 18 (.const 0))
  (.seq (.assign 19 (.const 0))
  (.seq (.ite (.op .eq (.reg 15) (.reg 17))
      (.seq (.assign 18 (.read a_acc_zI (.reg 10)))
      (.seq (.assign 19 (.const 1))
            (.assign 10 (.op .add (.reg 10) (.const 1)))))
      .skip)
  (.seq (.ite (.op .eq (.reg 16) (.reg 17))
      (.seq (.assign 15 (.read a_rhs_zI (.reg 11)))
      (.seq (.assign 18 (.op .add (.reg 18) (.reg 15)))
      (.seq (.assign 19 (.op .add (.reg 19) (.const 2)))
            (.assign 11 (.op .add (.reg 11) (.const 1))))))
      .skip)
  (.seq (.assign 15 (.read a_cap (.reg 17)))
  (.seq (.ite (.op .lt (.reg 18) (.reg 15))
      (.seq (.write a_out_zV (.reg 12) (.reg 17))
      (.seq (.write a_out_zI (.reg 12) (.reg 18))
      (.seq (.assign 12 (.op .add (.reg 12) (.const 1)))
            (.assign 19 (.op .add (.reg 19) (.const 4))))))
      .skip)
  (.seq (.assign 13 (.op .add (.reg 13) (.op .mul (.reg 19) (.reg 14))))
        (.assign 14 (.op .mul (.const 8) (.reg 14))))))))))))

/-- Word RAM program merging `(a_acc_zV, a_acc_zI)` and `(a_rhs_zV, a_rhs_zI)` into
`(a_out_zV, a_out_zI)` while computing `r_12 = Z'.card` and `r_13 = encBoundaryMask ZA ZB Z'`. -/
def mergeBoundaryProg : Cmd :=
  .seq (.assign 10 (.const 0))
  (.seq (.assign 11 (.const 0))
  (.seq (.assign 12 (.const 0))
  (.seq (.assign 13 (.const 0))
  (.seq (.assign 14 (.const 1))
        (.while mergeBoundaryCond mergeBoundaryBody)))))

private theorem eval_read_reg_of_getD {w : ℕ} {s : State} {a : Arr} {r : Reg} {idx val : ℕ}
    (hr : s.regs r = idx) (hidx_w : idx < 2 ^ w) (hval_w : val < 2 ^ w)
    (hlen : idx < (s.arrs a).length) (hget : (s.arrs a).getD idx 0 = val) :
    (Expr.read a (.reg r)).eval w s = some val := by
  have hget' : (s.arrs a)[idx]'hlen = val := by
    rw [← hget, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hlen, Option.getD_some]
  simp [Expr.eval, checkWord, hr, hidx_w, hlen, hget', hval_w]

theorem mergeBoundaryLoop_exec {w ξ ω : ℕ} {G : ComputeDigraph}
    {Z ZA ZB Z' : Finset (Fin G.numVerts)}
    {EA EB : Finset (Fin G.numEdges)}
    (hq_le : (ZA ∪ ZB).card ≤ Q_max ξ ω)
    (hinc_union : ∀ u ∈ ZA ∪ ZB,
      subInc G (EA ∪ EB) u =
        (if u ∈ ZA then subInc G EA u else 0) + (if u ∈ ZB then subInc G EB u else 0))
    (hZ'_iff : ∀ u : Fin G.numVerts,
      u ∈ Z' ↔ u ∈ ZA ∪ ZB ∧ subInc G (EA ∪ EB) u < capVal G Z u)
    (hw8 : 8 < 2 ^ w) (hn_w : G.numVerts < 2 ^ w)
    (hm1_w : G.numEdges + 1 < 2 ^ w) (hM_w : 8 ^ (Q_max ξ ω) < 2 ^ w)
    (rem k : ℕ) (hrem : k + rem = (ZA ∪ ZB).card) {s : State}
    (hr0 : s.regs 0 = G.numVerts)
    (hr_qA : s.regs r_qA = ZA.card)
    (hr_qB : s.regs r_qB = ZB.card)
    (hr10 : s.regs 10 = rankBelow ZA (cutoffAt (ZA ∪ ZB) k))
    (hr11 : s.regs 11 = rankBelow ZB (cutoffAt (ZA ∪ ZB) k))
    (hr12 : s.regs 12 = rankBelow Z' (cutoffAt (ZA ∪ ZB) k))
    (hr13 : s.regs 13 =
      packBase 8 (((List.finRange (ZA ∪ ZB).card).map (boundaryMaskDigit ZA ZB Z')).take k))
    (hr14 : s.regs 14 = 8 ^ k)
    (hcap : s.arrs a_cap = List.ofFn (capVal G Z))
    (hzVA_len : (s.arrs a_acc_zV).length = Q_max ξ ω)
    (hzIA_len : (s.arrs a_acc_zI).length = Q_max ξ ω)
    (hzVB_len : (s.arrs a_rhs_zV).length = Q_max ξ ω)
    (hzIB_len : (s.arrs a_rhs_zI).length = Q_max ξ ω)
    (hzVA : ∀ i : Fin ZA.card, (s.arrs a_acc_zV).getD i.1 0 = (finsetRootFn ZA i).1)
    (hzIA : ∀ i : Fin ZA.card, (s.arrs a_acc_zI).getD i.1 0 = subInc G EA (finsetRootFn ZA i))
    (hzVB : ∀ j : Fin ZB.card, (s.arrs a_rhs_zV).getD j.1 0 = (finsetRootFn ZB j).1)
    (hzIB : ∀ j : Fin ZB.card, (s.arrs a_rhs_zI).getD j.1 0 = subInc G EB (finsetRootFn ZB j))
    (houtV_len : (s.arrs a_out_zV).length = Q_max ξ ω)
    (houtI_len : (s.arrs a_out_zI).length = Q_max ξ ω)
    (houtV : ∀ idx : Fin Z'.card, idx.1 < rankBelow Z' (cutoffAt (ZA ∪ ZB) k) →
      (s.arrs a_out_zV).getD idx.1 0 = (finsetRootFn Z' idx).1)
    (houtI : ∀ idx : Fin Z'.card, idx.1 < rankBelow Z' (cutoffAt (ZA ∪ ZB) k) →
      (s.arrs a_out_zI).getD idx.1 0 = subInc G (EA ∪ EB) (finsetRootFn Z' idx)) :
    ∃ s' t_loop,
      Exec w (.while mergeBoundaryCond mergeBoundaryBody) s s' t_loop ∧
      t_loop ≤ 9 + 95 * rem ∧
      s'.regs 12 = Z'.card ∧
      s'.regs 13 = encBoundaryMask ZA ZB Z' ∧
      (s'.arrs a_out_zV).length = Q_max ξ ω ∧
      (s'.arrs a_out_zI).length = Q_max ξ ω ∧
      (∀ idx : Fin Z'.card, (s'.arrs a_out_zV).getD idx.1 0 = (finsetRootFn Z' idx).1) ∧
      (∀ idx : Fin Z'.card,
        (s'.arrs a_out_zI).getD idx.1 0 = subInc G (EA ∪ EB) (finsetRootFn Z' idx)) ∧
      (∀ r < 10, s'.regs r = s.regs r) ∧
      (∀ a, a ≠ a_out_zV → a ≠ a_out_zI → s'.arrs a = s.arrs a) := by
  have hZA_sub : ZA ⊆ ZA ∪ ZB := Finset.subset_union_left
  have hZB_sub : ZB ⊆ ZA ∪ ZB := Finset.subset_union_right
  have hZ'_sub : Z' ⊆ ZA ∪ ZB := fun u hu => (hZ'_iff u).mp hu |>.1
  have h0_w : 0 < 2 ^ w := by omega
  have hw1 : 1 < 2 ^ w := by omega
  have hw2 : 2 < 2 ^ w := by omega
  have hw4 : 4 < 2 ^ w := by omega
  have hQ_le_M : Q_max ξ ω ≤ 8 ^ (Q_max ξ ω) :=
    le_trans (Nat.le_of_lt (Nat.lt_two_pow_self)) (Nat.pow_le_pow_left (by decide) _)
  have hqA_le : ZA.card ≤ Q_max ξ ω := (Finset.card_le_card hZA_sub).trans hq_le
  have hqB_le : ZB.card ≤ Q_max ξ ω := (Finset.card_le_card hZB_sub).trans hq_le
  have hq'_le : Z'.card ≤ Q_max ξ ω := (Finset.card_le_card hZ'_sub).trans hq_le
  have hqA_w : ZA.card < 2 ^ w := by omega
  have hqB_w : ZB.card < 2 ^ w := by omega
  induction rem generalizing k s with
  | zero =>
    have hk_eq : k = (ZA ∪ ZB).card := by omega
    subst hk_eq
    have hi_eq : rankBelow ZA (cutoffAt (ZA ∪ ZB) (ZA ∪ ZB).card) = ZA.card :=
      rankBelow_cutoffAt_full (ZA ∪ ZB) ZA
    have hj_eq : rankBelow ZB (cutoffAt (ZA ∪ ZB) (ZA ∪ ZB).card) = ZB.card :=
      rankBelow_cutoffAt_full (ZA ∪ ZB) ZB
    have hk'_eq : rankBelow Z' (cutoffAt (ZA ∪ ZB) (ZA ∪ ZB).card) = Z'.card :=
      rankBelow_cutoffAt_full (ZA ∪ ZB) Z'
    have hcond : mergeBoundaryCond.eval w s = some 0 := by
      simp [mergeBoundaryCond, Expr.eval, BinOp.eval, BinOp.raw, checkWord,
        hr10, hr11, hr_qA, hr_qB, hi_eq, hj_eq, hqA_w, hqB_w, h0_w]
    have htake :
        ((List.finRange (ZA ∪ ZB).card).map (boundaryMaskDigit ZA ZB Z')).take (ZA ∪ ZB).card =
        (List.finRange (ZA ∪ ZB).card).map (boundaryMaskDigit ZA ZB Z') :=
      List.take_of_length_le (by simp)
    refine ⟨s, 9, .while_false hcond, by omega,
      hr12.trans hk'_eq, by rw [hr13, htake]; rfl,
      houtV_len, houtI_len,
      fun idx => houtV idx (by rw [hk'_eq]; exact idx.2),
      fun idx => houtI idx (by rw [hk'_eq]; exact idx.2),
      fun _ _ => rfl, fun _ _ _ => rfl⟩
  | succ rem ih =>
    have hk_lt : k < (ZA ∪ ZB).card := by omega
    let u := finsetRootFn (ZA ∪ ZB) ⟨k, hk_lt⟩
    let i := rankBelow ZA (cutoffAt (ZA ∪ ZB) k)
    let j := rankBelow ZB (cutoffAt (ZA ∪ ZB) k)
    let k' := rankBelow Z' (cutoffAt (ZA ∪ ZB) k)
    have hi_le : i ≤ ZA.card := rankBelow_le_card ZA _
    have hj_le : j ≤ ZB.card := rankBelow_le_card ZB _
    have hk'_le : k' ≤ Z'.card := rankBelow_le_card Z' _
    have hi_w : i < 2 ^ w := by omega
    have hj_w : j < 2 ^ w := by omega
    have hk'_w : k' < 2 ^ w := by omega
    have hu_w : u.1 < 2 ^ w := Nat.lt_trans u.2 hn_w
    -- Either `u ∈ ZA` or `u ∈ ZB`
    have hu_mem : u ∈ ZA ∨ u ∈ ZB := Finset.mem_union.mp (finsetRootFn_mem (ZA ∪ ZB) ⟨k, hk_lt⟩)
    -- Step 0: Evaluate loop condition `mergeBoundaryCond` to `some 1`
    have h_or_lt : i < ZA.card ∨ j < ZB.card := by
      rcases hu_mem with huA | huB
      · exact Or.inl (rankBelow_cutoffAt_step_mem hZA_sub hk_lt huA).1
      · exact Or.inr (rankBelow_cutoffAt_step_mem hZB_sub hk_lt huB).1
    have hcond : mergeBoundaryCond.eval w s = some 1 := by
      have hb1_w : (if i < ZA.card then 1 else 0) < 2 ^ w := by split_ifs <;> omega
      have hb2_w : (if j < ZB.card then 1 else 0) < 2 ^ w := by split_ifs <;> omega
      have hsum_w : (if i < ZA.card then 1 else 0) + (if j < ZB.card then 1 else 0) < 2 ^ w := by
        split_ifs <;> omega
      have hsum_pos : 0 < (if i < ZA.card then 1 else 0) + (if j < ZB.card then 1 else 0) := by
        rcases h_or_lt with h1 | h2
        · simp [h1]
        · simp [h2]
      simp [mergeBoundaryCond, Expr.eval, BinOp.eval, BinOp.raw, checkWord,
        hr10, hr11, hr_qA, hr_qB, i, j, hi_w, hj_w, hqA_w, hqB_w, h0_w, hw1,
        hb1_w, hb2_w, hsum_w, hsum_pos]
    -- Step 1: `vA` in `r_15`
    let vA : ℕ := if hi : i < ZA.card then (finsetRootFn ZA ⟨i, hi⟩).1 else G.numVerts
    have hvA_le : vA ≤ G.numVerts := by
      dsimp [vA]; split_ifs with hi
      · exact le_of_lt (finsetRootFn ZA ⟨i, hi⟩).2
      · exact le_refl _
    have hvA_w : vA < 2 ^ w := by omega
    let s₁ := s.setReg 15 vA
    have hex₁ : ∃ t₁ ≤ 6, Exec w (.ite (.op .lt (.reg 10) (.reg r_qA))
        (.assign 15 (.read a_acc_zV (.reg 10))) (.assign 15 (.reg 0))) s s₁ t₁ := by
      by_cases hi : i < ZA.card
      · have hc : (Expr.op .lt (.reg 10) (.reg r_qA)).eval w s = some 1 := by
          simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hr10, hr_qA, i, hi, hi_w, hqA_w, hw1]
        have hs1 : s₁ = s.setReg 15 (finsetRootFn ZA ⟨i, hi⟩).1 := by simp [s₁, vA, hi]
        refine ⟨6, le_refl 6, hs1 ▸ .ite_true hc (by decide)
          (.assign (eval_read_reg_of_getD hr10 hi_w
            (Nat.lt_trans (finsetRootFn ZA ⟨i, hi⟩).2 hn_w)
            (by rw [hzVA_len]; exact Nat.lt_of_lt_of_le hi hqA_le) (hzVA ⟨i, hi⟩)))⟩
      · have hc : (Expr.op .lt (.reg 10) (.reg r_qA)).eval w s = some 0 := by
          simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord, hr10, hr_qA, i, hi, hi_w, hqA_w, h0_w]
        have hs1 : s₁ = s.setReg 15 G.numVerts := by simp [s₁, vA, hi]
        refine ⟨5, by decide, hs1 ▸ .ite_false hc
          (.assign (by simp [Expr.eval, checkWord, hr0, hn_w]))⟩
    rcases hex₁ with ⟨t₁, ht₁, hex₁⟩
    -- Step 2: `vB` in `r_16`
    let vB : ℕ := if hj : j < ZB.card then (finsetRootFn ZB ⟨j, hj⟩).1 else G.numVerts
    have hvB_le : vB ≤ G.numVerts := by
      dsimp [vB]; split_ifs with hj
      · exact le_of_lt (finsetRootFn ZB ⟨j, hj⟩).2
      · exact le_refl _
    have hvB_w : vB < 2 ^ w := by omega
    let s₂ := s₁.setReg 16 vB
    have hex₂ : ∃ t₂ ≤ 6, Exec w (.ite (.op .lt (.reg 11) (.reg r_qB))
        (.assign 16 (.read a_rhs_zV (.reg 11))) (.assign 16 (.reg 0))) s₁ s₂ t₂ := by
      by_cases hj : j < ZB.card
      · have hc : (Expr.op .lt (.reg 11) (.reg r_qB)).eval w s₁ = some 1 := by
          simp [s₁, Expr.eval, BinOp.eval, BinOp.raw, checkWord, hr11, hr_qB, j, hj, hj_w, hqB_w, hw1]
        have hs2 : s₂ = s₁.setReg 16 (finsetRootFn ZB ⟨j, hj⟩).1 := by simp [s₂, vB, hj]
        refine ⟨6, le_refl 6, hs2 ▸ .ite_true hc (by decide)
          (.assign (eval_read_reg_of_getD (by simpa [s₁] using hr11) hj_w
            (Nat.lt_trans (finsetRootFn ZB ⟨j, hj⟩).2 hn_w)
            (by rw [State.setReg_arrs, hzVB_len]; exact Nat.lt_of_lt_of_le hj hqB_le)
            (hzVB ⟨j, hj⟩)))⟩
      · have hc : (Expr.op .lt (.reg 11) (.reg r_qB)).eval w s₁ = some 0 := by
          simp [s₁, Expr.eval, BinOp.eval, BinOp.raw, checkWord, hr11, hr_qB, j, hj, hj_w, hqB_w, h0_w]
        have hs2 : s₂ = s₁.setReg 16 G.numVerts := by simp [s₂, vB, hj]
        refine ⟨5, by decide, hs2 ▸ .ite_false hc
          (.assign (by simp [s₁, Expr.eval, checkWord, hr0, hn_w]))⟩
    rcases hex₂ with ⟨t₂, ht₂, hex₂⟩
    -- Establish `vA` and `vB` properties relative to `u.1`
    have hvA_prop : (u ∈ ZA → vA = u.1) ∧ (u ∉ ZA → u.1 < vA) := by
      constructor
      · intro huA
        rcases rankBelow_cutoffAt_step_mem hZA_sub hk_lt huA with ⟨hi, hroot, _⟩
        simp [vA, i, hi, u, hroot]
      · intro huA
        have hstep := (rankBelow_cutoffAt_step_notMem hZA_sub hk_lt huA).2
        dsimp [vA]; split_ifs with hi
        · exact hstep hi
        · exact u.2
    have hvB_prop : (u ∈ ZB → vB = u.1) ∧ (u ∉ ZB → u.1 < vB) := by
      constructor
      · intro huB
        rcases rankBelow_cutoffAt_step_mem hZB_sub hk_lt huB with ⟨hj, hroot, _⟩
        simp [vB, j, hj, u, hroot]
      · intro huB
        have hstep := (rankBelow_cutoffAt_step_notMem hZB_sub hk_lt huB).2
        dsimp [vB]; split_ifs with hj
        · exact hstep hj
        · exact u.2
    have hmin_eq : (if vA < vB then vA else vB) = u.1 := by
      split_ifs with hlt
      · rcases hu_mem with huA | huB
        · exact hvA_prop.1 huA
        · have h2 := hvB_prop.1 huB
          by_cases huA : u ∈ ZA
          · exact hvA_prop.1 huA
          · have h1 := hvA_prop.2 huA; omega
      · rcases hu_mem with huA | huB
        · have h1 := hvA_prop.1 huA
          by_cases huB : u ∈ ZB
          · exact hvB_prop.1 huB
          · have h2 := hvB_prop.2 huB; omega
        · exact hvB_prop.1 huB
    have hvA_eq_iff : vA = u.1 ↔ u ∈ ZA :=
      ⟨fun h => by by_contra hnot; have := hvA_prop.2 hnot; omega, hvA_prop.1⟩
    have hvB_eq_iff : vB = u.1 ↔ u ∈ ZB :=
      ⟨fun h => by by_contra hnot; have := hvB_prop.2 hnot; omega, hvB_prop.1⟩
    -- Step 3: `u.1` in `r_17`
    let s₃ := s₂.setReg 17 u.1
    have hex₃ : Exec w (.ite (.op .lt (.reg 15) (.reg 16))
        (.assign 17 (.reg 15)) (.assign 17 (.reg 16))) s₂ s₃ 5 := by
      by_cases hlt : vA < vB
      · have hc : (Expr.op .lt (.reg 15) (.reg 16)).eval w s₂ = some 1 := by
          simp [s₂, s₁, Expr.eval, BinOp.eval, BinOp.raw, checkWord, hvA_w, hvB_w, hlt, hw1]
        have hu_vA : u.1 = vA := by rw [← hmin_eq]; simp [hlt]
        have hs3 : s₃ = s₂.setReg 17 vA := by simp [s₃, hu_vA]
        exact hs3 ▸ .ite_true hc (by decide) (.assign (by simp [s₂, s₁, Expr.eval, checkWord, hvA_w]))
      · have hc : (Expr.op .lt (.reg 15) (.reg 16)).eval w s₂ = some 0 := by
          simp [s₂, s₁, Expr.eval, BinOp.eval, BinOp.raw, checkWord, hvA_w, hvB_w, hlt, h0_w]
        have hu_vB : u.1 = vB := by rw [← hmin_eq]; simp [hlt]
        have hs3 : s₃ = s₂.setReg 17 vB := by simp [s₃, hu_vB]
        exact hs3 ▸ .ite_false hc (.assign (by simp [s₂, Expr.eval, checkWord, hvB_w]))
    -- Step 4: Initialize `r_18 := 0; r_19 := 0` and process `ZA`
    let s₃_a := (s₃.setReg 18 0).setReg 19 0
    have hex_4a : Exec w (.assign 18 (.const 0)) s₃ (s₃.setReg 18 0) 2 :=
      .assign (by simp [Expr.eval, checkWord, h0_w])
    have hex_4b : Exec w (.assign 19 (.const 0)) (s₃.setReg 18 0) s₃_a 2 :=
      .assign (by simp [Expr.eval, checkWord, h0_w])
    let i_next := rankBelow ZA (cutoffAt (ZA ∪ ZB) (k + 1))
    let incA := if u ∈ ZA then subInc G EA u else 0
    let bA := if u ∈ ZA then 1 else 0
    have hincA_le : incA ≤ G.numEdges := by
      dsimp [incA]; split_ifs
      · exact (subInc_le_totalInc G EA u).trans (totalInc_le_numEdges G u)
      · exact Nat.zero_le _
    have hincA_w : incA < 2 ^ w := by omega
    have hbA_w : bA < 2 ^ w := by dsimp [bA]; split_ifs <;> omega
    let s₄ := ((s₃_a.setReg 18 incA).setReg 19 bA).setReg 10 i_next
    have hex₄ : ∃ t₄ ≤ 12, Exec w (.ite (.op .eq (.reg 15) (.reg 17))
        (.seq (.assign 18 (.read a_acc_zI (.reg 10)))
        (.seq (.assign 19 (.const 1))
              (.assign 10 (.op .add (.reg 10) (.const 1)))))
        .skip) s₃_a s₄ t₄ := by
      by_cases huA : u ∈ ZA
      · rcases rankBelow_cutoffAt_step_mem hZA_sub hk_lt huA with ⟨hi, hroot, hi_step⟩
        have hvA_u : vA = u.1 := hvA_prop.1 huA
        have hc : (Expr.op .eq (.reg 15) (.reg 17)).eval w s₃_a = some 1 := by
          simp [s₃_a, s₃, s₂, s₁, hvA_u, Expr.eval, BinOp.eval, BinOp.raw, checkWord, hu_w, hw1]
        have hgetI : (s₃_a.arrs a_acc_zI).getD i 0 = subInc G EA u := by
          change (s.arrs a_acc_zI).getD i 0 = subInc G EA (finsetRootFn (ZA ∪ ZB) ⟨k, hk_lt⟩)
          rw [← hroot]
          exact hzIA ⟨i, hi⟩
        have hincAu_w : subInc G EA u < 2 ^ w := by
          have := (subInc_le_totalInc G EA u).trans (totalInc_le_numEdges G u); omega
        have hi1_w : i + 1 < 2 ^ w := by omega
        have hs4 : s₄ = ((s₃_a.setReg 18 (subInc G EA u)).setReg 19 1).setReg 10 (i + 1) := by
          simp [s₄, incA, bA, huA, i_next, i, hi_step]
        refine ⟨12, le_refl 12, hs4 ▸ .ite_true hc (by decide)
          (.seq (.assign (eval_read_reg_of_getD (by simpa [s₃_a, s₃, s₂, s₁] using hr10)
                  hi_w hincAu_w
                  (by change i < (s.arrs a_acc_zI).length; rw [hzIA_len]; exact Nat.lt_of_lt_of_le hi hqA_le)
                  hgetI))
          (.seq (.assign (by simp [Expr.eval, checkWord, hw1]))
                (.assign (by simp [s₃_a, s₃, s₂, s₁, Expr.eval, BinOp.eval, BinOp.raw,
                  checkWord, hr10, i, hi_w, hw1, hi1_w]))))⟩
      · have hvA_ne : vA ≠ u.1 := mt hvA_eq_iff.mp huA
        have hc : (Expr.op .eq (.reg 15) (.reg 17)).eval w s₃_a = some 0 := by
          simp [s₃_a, s₃, s₂, s₁, hvA_ne, Expr.eval, BinOp.eval, BinOp.raw, checkWord, hvA_w, hu_w, h0_w]
        have hi_step := (rankBelow_cutoffAt_step_notMem hZA_sub hk_lt huA).1
        have hs4 : s₄ = s₃_a := by
          ext : 1
          · funext r
            dsimp [s₄, incA, bA, i_next]
            by_cases h10 : r = 10
            · subst h10; simp [s₃_a, s₃, s₂, s₁, hi_step, hr10]
            · by_cases h19 : r = 19
              · subst h19; simp [s₃_a, huA]
              · by_cases h18 : r = 18
                · subst h18; simp [s₃_a, huA]
                · simp [h10, h19, h18]
          · rfl
        rw [hs4]
        exact ⟨4, by decide, .ite_false hc (.skip s₃_a)⟩
    rcases hex₄ with ⟨t₄, ht₄, hex₄⟩
    -- Step 5: Process `ZB`
    let j_next := rankBelow ZB (cutoffAt (ZA ∪ ZB) (k + 1))
    let incU := subInc G (EA ∪ EB) u
    let bAB := bA + (if u ∈ ZB then 2 else 0)
    have hincU_eq : incU = incA + (if u ∈ ZB then subInc G EB u else 0) :=
      hinc_union u (finsetRootFn_mem (ZA ∪ ZB) ⟨k, hk_lt⟩)
    have hincU_le : incU ≤ G.numEdges :=
      (subInc_le_totalInc G (EA ∪ EB) u).trans (totalInc_le_numEdges G u)
    have hincU_w : incU < 2 ^ w := by omega
    have hbAB_w : bAB < 2 ^ w := by dsimp [bAB, bA]; split_ifs <;> omega
    let s₅ := (((s₄.setReg 15 (if u ∈ ZB then subInc G EB u else 0)).setReg 18 incU).setReg
      19 bAB).setReg 11 j_next
    have hex₅ : ∃ t₅ ≤ 18, Exec w (.ite (.op .eq (.reg 16) (.reg 17))
        (.seq (.assign 15 (.read a_rhs_zI (.reg 11)))
        (.seq (.assign 18 (.op .add (.reg 18) (.reg 15)))
        (.seq (.assign 19 (.op .add (.reg 19) (.const 2)))
              (.assign 11 (.op .add (.reg 11) (.const 1))))))
        .skip) s₄ (if u ∈ ZB then s₅ else s₄) t₅ := by
      by_cases huB : u ∈ ZB
      · rcases rankBelow_cutoffAt_step_mem hZB_sub hk_lt huB with ⟨hj, hroot, hj_step⟩
        have hvB_u : vB = u.1 := hvB_prop.1 huB
        have hc : (Expr.op .eq (.reg 16) (.reg 17)).eval w s₄ = some 1 := by
          simp [s₄, s₃_a, s₃, s₂, hvB_u, Expr.eval, BinOp.eval, BinOp.raw, checkWord, hu_w, hw1]
        have hgetI : (s₄.arrs a_rhs_zI).getD j 0 = subInc G EB u := by
          change (s.arrs a_rhs_zI).getD j 0 = subInc G EB (finsetRootFn (ZA ∪ ZB) ⟨k, hk_lt⟩)
          rw [← hroot]
          exact hzIB ⟨j, hj⟩
        have hincB_w : subInc G EB u < 2 ^ w := by
          have := (subInc_le_totalInc G EB u).trans (totalInc_le_numEdges G u); omega
        have hj1_w : j + 1 < 2 ^ w := by omega
        have hsum_inc : incA + subInc G EB u = incU := by rw [hincU_eq]; simp [huB]
        have hsum_b : bA + 2 = bAB := by simp [bAB, huB]
        simp only [huB, ↓reduceIte]
        have hs5 : s₅ = (((s₄.setReg 15 (subInc G EB u)).setReg 18 (incA + subInc G EB u)).setReg
            19 (bA + 2)).setReg 11 (j + 1) := by
          simp [s₅, huB, hsum_inc, hsum_b, j_next, j, hj_step]
        refine ⟨18, le_refl 18, hs5 ▸ .ite_true hc (by decide)
          (.seq (.assign (eval_read_reg_of_getD (by simpa [s₄, s₃_a, s₃, s₂, s₁] using hr11)
                  hj_w hincB_w
                  (by change j < (s.arrs a_rhs_zI).length; rw [hzIB_len]; exact Nat.lt_of_lt_of_le hj hqB_le)
                  hgetI))
          (.seq (.assign (by simp [s₄, Expr.eval, BinOp.eval, BinOp.raw, checkWord,
                  hincA_w, hincB_w, hsum_inc, hincU_w]))
          (.seq (.assign (by simp [s₄, Expr.eval, BinOp.eval, BinOp.raw, checkWord,
                  hbA_w, hw2, hsum_b, hbAB_w]))
                (.assign (by simp [s₄, s₃_a, s₃, s₂, s₁, Expr.eval, BinOp.eval, BinOp.raw,
                  checkWord, hr11, j, hj_w, hw1, hj1_w])))))⟩
      · have hvB_ne : vB ≠ u.1 := mt hvB_eq_iff.mp huB
        have hc : (Expr.op .eq (.reg 16) (.reg 17)).eval w s₄ = some 0 := by
          simp [s₄, s₃_a, s₃, s₂, hvB_ne, Expr.eval, BinOp.eval, BinOp.raw, checkWord, hvB_w, hu_w, h0_w]
        simp only [huB, ↓reduceIte]
        exact ⟨4, by decide, .ite_false hc (.skip s₄)⟩
    rcases hex₅ with ⟨t₅, ht₅, hex₅⟩
    let s₅' := if u ∈ ZB then s₅ else s₄
    have hr10_5 : s₅'.regs 10 = i_next := by dsimp [s₅', s₅, s₄]; split_ifs <;> rfl
    have hr11_5 : s₅'.regs 11 = j_next := by
      dsimp [s₅', s₅, s₄]; split_ifs with huB
      · rfl
      · have hj_step := (rankBelow_cutoffAt_step_notMem hZB_sub hk_lt huB).1
        simp [s₃_a, s₃, s₂, s₁, j_next, hj_step, hr11]
    have hr12_5 : s₅'.regs 12 = k' := by
      dsimp [s₅', s₅, s₄, s₃_a, s₃, s₂, s₁]; split_ifs <;> exact hr12
    have hr13_5 : s₅'.regs 13 = s.regs 13 := by
      dsimp [s₅', s₅, s₄, s₃_a, s₃, s₂, s₁]; split_ifs <;> rfl
    have hr14_5 : s₅'.regs 14 = 8 ^ k := by
      dsimp [s₅', s₅, s₄, s₃_a, s₃, s₂, s₁]; split_ifs <;> exact hr14
    have hr17_5 : s₅'.regs 17 = u.1 := by
      dsimp [s₅', s₅, s₄, s₃_a, s₃]; split_ifs <;> rfl
    have hr18_5 : s₅'.regs 18 = incU := by
      dsimp [s₅', s₅, s₄]; split_ifs with huB
      · rfl
      · rw [hincU_eq]; simp [huB]
    have hr19_5 : s₅'.regs 19 = bAB := by
      dsimp [s₅', s₅, s₄]; split_ifs with huB
      · rfl
      · simp [bAB, huB]
    have harr_5 : s₅'.arrs = s.arrs := by
      dsimp [s₅', s₅, s₄, s₃_a, s₃, s₂, s₁]; split_ifs <;> rfl
    -- Step 6: Read `a_cap[u.1]` and process `Z'`
    let capU := capVal G Z u
    have hcapU_le : capU ≤ G.numEdges + 1 := by
      dsimp [capU, capVal]; split_ifs
      · omega
      · have := totalInc_le_numEdges G u; omega
    have hcapU_w : capU < 2 ^ w := by omega
    let s₆_a := s₅'.setReg 15 capU
    have hex_6a : Exec w (.assign 15 (.read a_cap (.reg 17))) s₅' s₆_a 3 :=
      .assign (by simp [Expr.eval, checkWord, hr17_5, hu_w, harr_5, hcap, u.2, capU, hcapU_w])
    let k'_next := rankBelow Z' (cutoffAt (ZA ∪ ZB) (k + 1))
    let d_k := boundaryMaskDigit ZA ZB Z' ⟨k, hk_lt⟩
    have hdk_eq : d_k = bAB + (if u ∈ Z' then 4 else 0) := by rfl
    have hdk_w : d_k < 2 ^ w := by
      have := (boundaryMaskDigit_pos_and_lt ZA ZB Z' ⟨k, hk_lt⟩).2; omega
    have hu_Z'_iff : u ∈ Z' ↔ incU < capU := by
      rw [hZ'_iff u]; exact and_iff_right (finsetRootFn_mem (ZA ∪ ZB) ⟨k, hk_lt⟩)
    let s₆_true := (((s₆_a.writeArr a_out_zV k' u.1).writeArr a_out_zI k' incU).setReg
      12 (k' + 1)).setReg 19 (bAB + 4)
    let s₆ := if u ∈ Z' then s₆_true else s₆_a
    have hex₆ : ∃ t₆ ≤ 17, Exec w (.ite (.op .lt (.reg 18) (.reg 15))
        (.seq (.write a_out_zV (.reg 12) (.reg 17))
        (.seq (.write a_out_zI (.reg 12) (.reg 18))
        (.seq (.assign 12 (.op .add (.reg 12) (.const 1)))
              (.assign 19 (.op .add (.reg 19) (.const 4))))))
        .skip) s₆_a s₆ t₆ := by
      by_cases huZ' : u ∈ Z'
      · rcases rankBelow_cutoffAt_step_mem hZ'_sub hk_lt huZ' with ⟨hk'_lt, _, _⟩
        have hlt_cap : incU < capU := hu_Z'_iff.mp huZ'
        have hc : (Expr.op .lt (.reg 18) (.reg 15)).eval w s₆_a = some 1 := by
          simp [s₆_a, Expr.eval, BinOp.eval, BinOp.raw, checkWord, hr18_5, hincU_w, hcapU_w, hlt_cap, hw1]
        have hk'_Q : k' < Q_max ξ ω := Nat.lt_of_lt_of_le hk'_lt hq'_le
        have hk'1_w : k' + 1 < 2 ^ w := by omega
        have hbAB4_w : bAB + 4 < 2 ^ w := by dsimp [bAB, bA]; split_ifs <;> omega
        simp only [s₆, huZ', ↓reduceIte]
        refine ⟨17, le_refl 17, .ite_true hc (by decide)
          (.seq (.write (by simp [s₆_a, Expr.eval, checkWord, hr12_5, hk'_w])
                        (by simp [s₆_a, Expr.eval, checkWord, hr17_5, hu_w])
                        (by simp [s₆_a, harr_5, houtV_len, hk'_Q]))
          (.seq (.write (by simp [s₆_a, Expr.eval, checkWord, hr12_5, hk'_w])
                        (by simp [s₆_a, Expr.eval, checkWord, hr18_5, hincU_w])
                        (by simp [s₆_a, harr_5, houtI_len, hk'_Q]))
          (.seq (.assign (by simp [s₆_a, Expr.eval, BinOp.eval, BinOp.raw, checkWord, hr12_5, hk'_w, hw1, hk'1_w]))
                (.assign (by simp [s₆_a, Expr.eval, BinOp.eval, BinOp.raw, checkWord, hr19_5, hbAB_w, hw4, hbAB4_w])))))⟩
      · have hnot_cap : ¬(incU < capU) := mt hu_Z'_iff.mpr huZ'
        have hc : (Expr.op .lt (.reg 18) (.reg 15)).eval w s₆_a = some 0 := by
          simp [s₆_a, Expr.eval, BinOp.eval, BinOp.raw, checkWord, hr18_5, hincU_w, hcapU_w, hnot_cap, h0_w]
        simp only [s₆, huZ', ↓reduceIte]
        exact ⟨4, by decide, .ite_false hc (.skip s₆_a)⟩
    rcases hex₆ with ⟨t₆, ht₆, hex₆⟩
    -- Step 7: Update `r_13 := mcode + d_k * 8^k` and `r_14 := 8^(k+1)`
    have hr12_6 : s₆.regs 12 = k'_next := by
      dsimp [s₆, s₆_true, s₆_a]; split_ifs with huZ'
      · rcases rankBelow_cutoffAt_step_mem hZ'_sub hk_lt huZ' with ⟨_, _, hk'_step⟩
        simp [k'_next, k', hk'_step]
      · have hk'_step := (rankBelow_cutoffAt_step_notMem hZ'_sub hk_lt huZ').1
        simp [k'_next, hk'_step, k', hr12_5]
    have hr13_6 : s₆.regs 13 = s.regs 13 := by
      dsimp [s₆, s₆_true, s₆_a]; split_ifs <;> exact hr13_5
    have hr14_6 : s₆.regs 14 = 8 ^ k := by
      dsimp [s₆, s₆_true, s₆_a]; split_ifs <;> exact hr14_5
    have hr19_6 : s₆.regs 19 = d_k := by
      dsimp [s₆, s₆_true, s₆_a]; split_ifs with huZ'
      · simp [hdk_eq, huZ']
      · simp [hdk_eq, huZ', hr19_5]
    let ds_all := (List.finRange (ZA ∪ ZB).card).map (boundaryMaskDigit ZA ZB Z')
    have hds_len : k < ds_all.length := by simp [ds_all, hk_lt]
    have hds_get : ds_all[k] = d_k := by simp [ds_all, d_k]
    have htake_succ : ds_all.take (k + 1) = ds_all.take k ++ [d_k] := by
      rw [List.take_add_one, List.getElem?_eq_getElem hds_len, Option.toList_some, hds_get]
    let mcode_next := packBase 8 (ds_all.take (k + 1))
    have hmcode_eq : s.regs 13 + d_k * 8 ^ k = mcode_next := by
      dsimp [mcode_next]
      rw [hr13, htake_succ, packBase_append_singleton]
      simp [ds_all, Nat.le_of_lt hk_lt]
    have hp8_le : 8 ^ (k + 1) ≤ 8 ^ (Q_max ξ ω) :=
      Nat.pow_le_pow_right (by decide : 0 < 8) (by omega)
    have hp8_k_w : 8 ^ k < 2 ^ w := by
      have : 8 ^ k ≤ 8 ^ (k + 1) := Nat.pow_le_pow_right (by decide : 0 < 8) (Nat.le_succ k)
      omega
    have hp8_succ_w : 8 ^ (k + 1) < 2 ^ w := by omega
    have hmcode_next_lt : mcode_next < 8 ^ (k + 1) := by
      have hlen1 : (ds_all.take (k + 1)).length = k + 1 := by simp [ds_all]; omega
      rw [← hlen1]
      refine packBase_lt (by decide : 0 < 8) _ fun d hd => ?_
      rcases List.mem_map.mp (List.mem_of_mem_take hd) with ⟨idx, _, rfl⟩
      exact (boundaryMaskDigit_pos_and_lt ZA ZB Z' idx).2
    have hmcode_next_w : mcode_next < 2 ^ w := by omega
    have hmcode_cur_w : s.regs 13 < 2 ^ w := by omega
    have hprod_w : d_k * 8 ^ k < 2 ^ w := by omega
    let s₇_a := s₆.setReg 13 mcode_next
    have hex_7a : Exec w (.assign 13 (.op .add (.reg 13) (.op .mul (.reg 19) (.reg 14)))) s₆ s₇_a 6 :=
      .assign (by simp [Expr.eval, BinOp.eval, BinOp.raw, checkWord,
        hr13_6, hr14_6, hr19_6, hmcode_cur_w, hdk_w, hp8_k_w, hprod_w, hmcode_eq, hmcode_next_w])
    let s₇ := s₇_a.setReg 14 (8 ^ (k + 1))
    have hex_7b : Exec w (.assign 14 (.op .mul (.const 8) (.reg 14))) s₇_a s₇ 4 :=
      .assign (by simp [s₇_a, Expr.eval, BinOp.eval, BinOp.raw, checkWord,
        hr14_6, hw8, hp8_k_w, ← Nat.pow_succ', hp8_succ_w])
    have hex_body : Exec w mergeBoundaryBody s s₇
        (t₁ + (t₂ + (5 + (2 + (2 + (t₄ + (t₅ + (3 + (t₆ + (6 + 4)))))))))) :=
      .seq hex₁ (.seq hex₂ (.seq hex₃ (.seq hex_4a (.seq hex_4b
        (.seq hex₄ (.seq hex₅ (.seq hex_6a (.seq hex₆ (.seq hex_7a hex_7b)))))))))
    -- Verify array invariants at `s₇`
    have houtV_7 : ∀ idx : Fin Z'.card, idx.1 < k'_next →
        (s₇.arrs a_out_zV).getD idx.1 0 = (finsetRootFn Z' idx).1 := by
      intro idx hidx
      dsimp [s₇, s₇_a, s₆, s₆_true, s₆_a]
      split_ifs with huZ'
      · rcases rankBelow_cutoffAt_step_mem hZ'_sub hk_lt huZ' with ⟨hk'_lt, hroot, hk'_step⟩
        simp only [State.setReg_arrs,
          State.writeArr_arrs_ne _ _ _ (by decide : a_out_zV ≠ a_out_zI),
          State.writeArr_arrs_self, harr_5]
        by_cases h_eq : idx.1 = k'
        · rw [h_eq, getD_set_eq _ k' u.1 (by rw [houtV_len]; exact Nat.lt_of_lt_of_le hk'_lt hq'_le),
              show idx = ⟨k', hk'_lt⟩ from Fin.ext h_eq, hroot]
        · rw [getD_set_ne _ k' u.1 idx.1 h_eq]
          exact houtV idx (by dsimp [k'_next, k'] at hidx hk'_step; omega)
      · have hk'_step := (rankBelow_cutoffAt_step_notMem hZ'_sub hk_lt huZ').1
        simp only [State.setReg_arrs, harr_5]
        exact houtV idx (by dsimp [k'_next, k'] at hidx hk'_step; omega)
    have houtI_7 : ∀ idx : Fin Z'.card, idx.1 < k'_next →
        (s₇.arrs a_out_zI).getD idx.1 0 = subInc G (EA ∪ EB) (finsetRootFn Z' idx) := by
      intro idx hidx
      dsimp [s₇, s₇_a, s₆, s₆_true, s₆_a]
      split_ifs with huZ'
      · rcases rankBelow_cutoffAt_step_mem hZ'_sub hk_lt huZ' with ⟨hk'_lt, hroot, hk'_step⟩
        simp only [State.setReg_arrs, State.writeArr_arrs_self,
          State.writeArr_arrs_ne _ _ _ (by decide : a_out_zI ≠ a_out_zV), harr_5]
        by_cases h_eq : idx.1 = k'
        · rw [h_eq, getD_set_eq _ k' incU (by rw [houtI_len]; exact Nat.lt_of_lt_of_le hk'_lt hq'_le),
              show idx = ⟨k', hk'_lt⟩ from Fin.ext h_eq, hroot]
        · rw [getD_set_ne _ k' incU idx.1 h_eq]
          exact houtI idx (by dsimp [k'_next, k'] at hidx hk'_step; omega)
      · have hk'_step := (rankBelow_cutoffAt_step_notMem hZ'_sub hk_lt huZ').1
        simp only [State.setReg_arrs, harr_5]
        exact houtI idx (by dsimp [k'_next, k'] at hidx hk'_step; omega)
    have harr_ne_7 : ∀ a, a ≠ a_out_zV → a ≠ a_out_zI → s₇.arrs a = s.arrs a := by
      intro a ha1 ha2
      dsimp [s₇, s₇_a, s₆, s₆_true, s₆_a]
      split_ifs <;> simp [ha1, ha2, harr_5]
    have hreg_lt10_7 : ∀ r < 10, s₇.regs r = s.regs r := by
      intro r hr
      have h10 : r ≠ 10 := Nat.ne_of_lt (Nat.lt_of_lt_of_le hr (by decide : 10 ≤ 10))
      have h11 : r ≠ 11 := Nat.ne_of_lt (Nat.lt_trans hr (by decide : 10 < 11))
      have h12 : r ≠ 12 := Nat.ne_of_lt (Nat.lt_trans hr (by decide : 10 < 12))
      have h13 : r ≠ 13 := Nat.ne_of_lt (Nat.lt_trans hr (by decide : 10 < 13))
      have h14 : r ≠ 14 := Nat.ne_of_lt (Nat.lt_trans hr (by decide : 10 < 14))
      have h15 : r ≠ 15 := Nat.ne_of_lt (Nat.lt_trans hr (by decide : 10 < 15))
      have h16 : r ≠ 16 := Nat.ne_of_lt (Nat.lt_trans hr (by decide : 10 < 16))
      have h17 : r ≠ 17 := Nat.ne_of_lt (Nat.lt_trans hr (by decide : 10 < 17))
      have h18 : r ≠ 18 := Nat.ne_of_lt (Nat.lt_trans hr (by decide : 10 < 18))
      have h19 : r ≠ 19 := Nat.ne_of_lt (Nat.lt_trans hr (by decide : 10 < 19))
      dsimp [s₇, s₇_a, s₆, s₆_true, s₆_a, s₅', s₅, s₄, s₃_a, s₃, s₂, s₁]
      split_ifs <;> simp [h10, h11, h12, h13, h14, h15, h16, h17, h18, h19]
    rcases ih (k + 1) (by omega) (s := s₇)
        (by rw [hreg_lt10_7 0 (by decide), hr0])
        (by rw [hreg_lt10_7 r_qA (by decide), hr_qA])
        (by rw [hreg_lt10_7 r_qB (by decide), hr_qB])
        (by dsimp [s₇, s₇_a, s₆, s₆_true, s₆_a]; split_ifs <;> exact hr10_5)
        (by dsimp [s₇, s₇_a, s₆, s₆_true, s₆_a]; split_ifs <;> exact hr11_5)
        (by simp [s₇, s₇_a, hr12_6, k'_next])
        (by simp [s₇, s₇_a, mcode_next, ds_all])
        (by simp [s₇])
        (by rw [harr_ne_7 a_cap (by decide) (by decide), hcap])
        (by rw [harr_ne_7 a_acc_zV (by decide) (by decide), hzVA_len])
        (by rw [harr_ne_7 a_acc_zI (by decide) (by decide), hzIA_len])
        (by rw [harr_ne_7 a_rhs_zV (by decide) (by decide), hzVB_len])
        (by rw [harr_ne_7 a_rhs_zI (by decide) (by decide), hzIB_len])
        (fun i => by rw [harr_ne_7 a_acc_zV (by decide) (by decide)]; exact hzVA i)
        (fun i => by rw [harr_ne_7 a_acc_zI (by decide) (by decide)]; exact hzIA i)
        (fun j => by rw [harr_ne_7 a_rhs_zV (by decide) (by decide)]; exact hzVB j)
        (fun j => by rw [harr_ne_7 a_rhs_zI (by decide) (by decide)]; exact hzIB j)
        (by dsimp [s₇, s₇_a, s₆, s₆_true, s₆_a]; split_ifs <;> simp [harr_5, houtV_len])
        (by dsimp [s₇, s₇_a, s₆, s₆_true, s₆_a]; split_ifs <;> simp [harr_5, houtI_len])
        houtV_7 houtI_7 with
      ⟨s', t_ih, hex_ih, ht_ih, hr12', hr13', houtV_len', houtI_len', houtV', houtI', hreg', harr'⟩
    refine ⟨s', 9 + (t₁ + (t₂ + (5 + (2 + (2 + (t₄ + (t₅ + (3 + (t₆ + (6 + 4)))))))))) + t_ih,
      .while_true hcond (by decide) hex_body hex_ih,
      by omega, hr12', hr13', houtV_len', houtI_len', houtV', houtI',
      fun r hr => (hreg' r hr).trans (hreg_lt10_7 r hr),
      fun a ha1 ha2 => (harr' a ha1 ha2).trans (harr_ne_7 a ha1 ha2)⟩

theorem mergeBoundaryProg_exec {w ξ ω : ℕ} {G : ComputeDigraph}
    {Z ZA ZB Z' : Finset (Fin G.numVerts)}
    {EA EB : Finset (Fin G.numEdges)}
    (hq_le : (ZA ∪ ZB).card ≤ Q_max ξ ω)
    (hinc_union : ∀ u ∈ ZA ∪ ZB,
      subInc G (EA ∪ EB) u =
        (if u ∈ ZA then subInc G EA u else 0) + (if u ∈ ZB then subInc G EB u else 0))
    (hZ'_iff : ∀ u : Fin G.numVerts,
      u ∈ Z' ↔ u ∈ ZA ∪ ZB ∧ subInc G (EA ∪ EB) u < capVal G Z u)
    (hw8 : 8 < 2 ^ w) (hn_w : G.numVerts < 2 ^ w)
    (hm1_w : G.numEdges + 1 < 2 ^ w) (hM_w : 8 ^ (Q_max ξ ω) < 2 ^ w)
    {s : State}
    (hr0 : s.regs 0 = G.numVerts)
    (hr_qA : s.regs r_qA = ZA.card)
    (hr_qB : s.regs r_qB = ZB.card)
    (hcap : s.arrs a_cap = List.ofFn (capVal G Z))
    (hzVA_len : (s.arrs a_acc_zV).length = Q_max ξ ω)
    (hzIA_len : (s.arrs a_acc_zI).length = Q_max ξ ω)
    (hzVB_len : (s.arrs a_rhs_zV).length = Q_max ξ ω)
    (hzIB_len : (s.arrs a_rhs_zI).length = Q_max ξ ω)
    (hzVA : ∀ i : Fin ZA.card, (s.arrs a_acc_zV).getD i.1 0 = (finsetRootFn ZA i).1)
    (hzIA : ∀ i : Fin ZA.card, (s.arrs a_acc_zI).getD i.1 0 = subInc G EA (finsetRootFn ZA i))
    (hzVB : ∀ j : Fin ZB.card, (s.arrs a_rhs_zV).getD j.1 0 = (finsetRootFn ZB j).1)
    (hzIB : ∀ j : Fin ZB.card, (s.arrs a_rhs_zI).getD j.1 0 = subInc G EB (finsetRootFn ZB j))
    (houtV_len : (s.arrs a_out_zV).length = Q_max ξ ω)
    (houtI_len : (s.arrs a_out_zI).length = Q_max ξ ω) :
    ∃ s' t_merge,
      Exec w mergeBoundaryProg s s' t_merge ∧
      t_merge ≤ 20 + 95 * Q_max ξ ω ∧
      s'.regs 12 = Z'.card ∧
      s'.regs 13 = encBoundaryMask ZA ZB Z' ∧
      (s'.arrs a_out_zV).length = Q_max ξ ω ∧
      (s'.arrs a_out_zI).length = Q_max ξ ω ∧
      (∀ idx : Fin Z'.card, (s'.arrs a_out_zV).getD idx.1 0 = (finsetRootFn Z' idx).1) ∧
      (∀ idx : Fin Z'.card,
        (s'.arrs a_out_zI).getD idx.1 0 = subInc G (EA ∪ EB) (finsetRootFn Z' idx)) ∧
      (∀ r < 10, s'.regs r = s.regs r) ∧
      (∀ a, a ≠ a_out_zV → a ≠ a_out_zI → s'.arrs a = s.arrs a) := by
  have h0_w : 0 < 2 ^ w := by omega
  have hw1 : 1 < 2 ^ w := by omega
  have hZ'_sub : Z' ⊆ ZA ∪ ZB := fun u hu => (hZ'_iff u).mp hu |>.1
  let s_a := s.setReg 10 0
  let s_b := s_a.setReg 11 0
  let s_c := s_b.setReg 12 0
  let s_d := s_c.setReg 13 0
  let s₁ := s_d.setReg 14 1
  have hex1 : Exec w (.assign 10 (.const 0)) s s_a 2 :=
    .assign (by simp [Expr.eval, checkWord, h0_w])
  have hex2 : Exec w (.assign 11 (.const 0)) s_a s_b 2 :=
    .assign (by simp [Expr.eval, checkWord, h0_w])
  have hex3 : Exec w (.assign 12 (.const 0)) s_b s_c 2 :=
    .assign (by simp [Expr.eval, checkWord, h0_w])
  have hex4 : Exec w (.assign 13 (.const 0)) s_c s_d 2 :=
    .assign (by simp [Expr.eval, checkWord, h0_w])
  have hex5 : Exec w (.assign 14 (.const 1)) s_d s₁ 2 :=
    .assign (by simp [Expr.eval, checkWord, hw1])
  rcases mergeBoundaryLoop_exec hq_le hinc_union hZ'_iff hw8 hn_w hm1_w hM_w
      (ZA ∪ ZB).card 0 (Nat.zero_add _) (s := s₁)
      (by simp [s₁, s_d, s_c, s_b, s_a, hr0])
      (by simp [s₁, s_d, s_c, s_b, s_a, hr_qA])
      (by simp [s₁, s_d, s_c, s_b, s_a, hr_qB])
      (by simp [s₁, s_d, s_c, s_b, s_a, rankBelow_cutoffAt_zero (Finset.subset_union_left : ZA ⊆ ZA ∪ ZB)])
      (by simp [s₁, s_d, s_c, s_b, s_a, rankBelow_cutoffAt_zero (Finset.subset_union_right : ZB ⊆ ZA ∪ ZB)])
      (by simp [s₁, s_d, s_c, s_b, s_a, rankBelow_cutoffAt_zero hZ'_sub])
      (by simp [s₁, s_d, packBase]) (by simp [s₁])
      (by simp [s₁, s_d, s_c, s_b, s_a, hcap])
      hzVA_len hzIA_len hzVB_len hzIB_len
      hzVA hzIA hzVB hzIB
      (by simp [s₁, s_d, s_c, s_b, s_a, houtV_len])
      (by simp [s₁, s_d, s_c, s_b, s_a, houtI_len])
      (fun idx h => by rw [rankBelow_cutoffAt_zero hZ'_sub] at h; omega)
      (fun idx h => by rw [rankBelow_cutoffAt_zero hZ'_sub] at h; omega) with
    ⟨s', t_loop, hex_loop, ht_loop, hr12', hr13', houtV_len', houtI_len', houtV', houtI', hreg', harr'⟩
  refine ⟨s', 2 + (2 + (2 + (2 + (2 + t_loop)))),
    .seq hex1 (.seq hex2 (.seq hex3 (.seq hex4 (.seq hex5 hex_loop)))),
    by omega, hr12', hr13', houtV_len', houtI_len', houtV', houtI',
    fun r hr => by
      rw [hreg' r hr]
      simp [s₁, s_d, s_c, s_b, s_a,
        Nat.ne_of_lt (Nat.lt_of_lt_of_le hr (by decide : 10 ≤ 10)),
        Nat.ne_of_lt (Nat.lt_trans hr (by decide : 10 < 11)),
        Nat.ne_of_lt (Nat.lt_trans hr (by decide : 10 < 12)),
        Nat.ne_of_lt (Nat.lt_trans hr (by decide : 10 < 13)),
        Nat.ne_of_lt (Nat.lt_trans hr (by decide : 10 < 14))],
    fun a ha1 ha2 => harr' a ha1 ha2⟩

end GraphMinor.Compute
