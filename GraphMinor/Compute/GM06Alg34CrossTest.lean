module

public import GraphMinor.Compute.GM06Alg34TagPartition
public import Mathlib.Data.List.FinRange

/-!
# Crossing comparisons at four cuff positions

Compare four positions in the supplied cyclic list. They cross exactly
when the four labels are distinct and the two remaining positions lie
on different sides of the first pair. A pair of positive equal tags
identifies one division block. These two finite tests are combined for
the RAM scan without choosing a geometric object.
-/

@[expose] public section
namespace GraphMinor.Compute

open Set GM06

/-- The alternating-position test on a cyclic list. -/
def gm06PositionCross (i j k l : ℕ) : Bool :=
  decide (i ≠ j ∧ k ≠ l ∧ i ≠ k ∧ i ≠ l ∧ j ≠ k ∧ j ≠ l) &&
    (GM06DrawingData.cyclicBetween i j k != GM06DrawingData.cyclicBetween i j l)

/-- The finite comparison made by one iteration of the crossing scan.
The two pairs must belong to distinct, nonzero division tags. -/
def gm06QuadPattern (i j k l ci cj ck cl : ℕ) : Bool :=
  gm06PositionCross i j k l && decide (ci = cj ∧ ck = cl ∧ ci ≠ ck ∧ ci ≠ 0 ∧ ck ≠ 0)

/-- The comparison using the actual supplied labels and their block tags. -/
def gm06QuadTest {n : ℕ} (D : List (List (Fin n))) (L : List (Fin n))
    (i j k l : Fin L.length) : Bool :=
  gm06QuadPattern i.val j.val k.val l.val
    (gm06BlockTag D (L.get i)) (gm06BlockTag D (L.get j))
    (gm06BlockTag D (L.get k)) (gm06BlockTag D (L.get l))

private theorem gm06_idxOf_get {n : ℕ} {L : List (Fin n)} (hL : L.Nodup) (i : Fin L.length) :
    L.idxOf (L.get i) = i.val := by
  have hb := List.idxOf_lt_length_iff.mpr (L.get_mem i)
  have hg := List.idxOf_get (a := L.get i) hb
  have hi : (⟨L.idxOf (L.get i), hb⟩ : Fin L.length) = i := hL.get_inj_iff.mp hg
  exact congrArg Fin.val hi

/-- The test on positions is the supplied cyclic-list crossing test. -/
theorem gm06PositionCross_eq {n : ℕ} {L : List (Fin n)} (hL : L.Nodup)
    (i j k l : Fin L.length) :
    gm06PositionCross i.val j.val k.val l.val =
      GM06DrawingData.crossesOnList L (L.get i) (L.get j) (L.get k) (L.get l) := by
  have heq (p q : Fin L.length) : L.get p = L.get q ↔ p.val = q.val :=
    hL.get_inj_iff.trans Fin.ext_iff
  simp only [gm06PositionCross, GM06DrawingData.crossesOnList, List.get_mem,
    true_and, ne_eq, heq, gm06_idxOf_get hL]

/-- The mathematical test scans all four cuff positions. -/
def gm06CrossScan {n : ℕ} (D : List (List (Fin n))) (L : List (Fin n)) : Bool :=
  (List.finRange L.length).all fun i => (List.finRange L.length).all fun j =>
    (List.finRange L.length).all fun k => (List.finRange L.length).all fun l =>
      !(gm06QuadTest D L i j k l)

theorem gm06CrossScan_eq_true_iff {n : ℕ} (D : List (List (Fin n))) (L : List (Fin n)) :
    gm06CrossScan D L = true ↔ ∀ i j k l : Fin L.length, gm06QuadTest D L i j k l = false := by
  simp only [gm06CrossScan, List.all_eq_true, List.mem_finRange, forall_const, Bool.not_eq_true']

private theorem gm06_finset_ne_sets {n : ℕ} {A B : List (Fin n)}
    (hne : A.toFinset ≠ B.toFinset) : GM06DrawingData.block A ≠ GM06DrawingData.block B := by
  intro heq
  apply hne
  ext a
  simpa only [List.mem_toFinset, GM06DrawingData.block, mem_ofPred_eq] using Set.ext_iff.mp heq a

/-- For a supplied division, testing all four cyclic positions is exactly
the cross-free check used at the start of VI (3.4), page 121. -/
theorem gm06CrossScan_iff_crossFree (x : GM06DrawingData) {L : List (Fin x.n)}
    (hL : x.cuffs = [L]) (hnd : L.Nodup) (hD : IsDivision x.divisionSet) :
    gm06CrossScan x.division L = true ↔ x.crossFree = true := by
  have hD' : IsDivision (gm06BlockSets x.division) := hD
  have hcross (a c b d : Fin x.n) : x.crosses a c b d =
      GM06DrawingData.crossesOnList L a c b d := by
    simp only [GM06DrawingData.crosses, hL, List.any_cons, List.any_nil, Bool.or_false]
  rw [gm06CrossScan_eq_true_iff, GM06DrawingData.crossFree_eq_true_iff]
  constructor
  · intro hscan A hA B hB hne a ha c hc b hb d hd
    cases hx : x.crosses a c b d with
    | false => rfl
    | true =>
      have hcrossL : GM06DrawingData.crossesOnList L a c b d = true := (hcross a c b d).symm.trans hx
      have hguard := hcrossL
      simp only [GM06DrawingData.crossesOnList, Bool.and_eq_true, decide_eq_true_eq] at hguard
      obtain ⟨i, hi⟩ := List.mem_iff_get.mp hguard.1.1
      obtain ⟨j, hj⟩ := List.mem_iff_get.mp hguard.1.2.1
      obtain ⟨k, hk⟩ := List.mem_iff_get.mp hguard.1.2.2.1
      obtain ⟨l, hl⟩ := List.mem_iff_get.mp hguard.1.2.2.2.1
      have hac := gm06BlockTag_eq_of_same_block hD' hA ha hc
      have hbd := gm06BlockTag_eq_of_same_block hD' hB hb hd
      have hpa : gm06BlockTag x.division a ≠ 0 := fun hz =>
        (gm06BlockTag_eq_zero_iff x.division a).mp hz A hA ha
      have hpb : gm06BlockTag x.division b ≠ 0 := fun hz =>
        (gm06BlockTag_eq_zero_iff x.division b).mp hz B hB hb
      have hab : gm06BlockTag x.division a ≠ gm06BlockTag x.division b := by
        intro heq
        obtain ⟨C, hC, haC, hbC⟩ := gm06BlockTag_common_block x.division a b heq hpa
        have hAC := gm06BlockSets_eq_of_common hD' hA hC ha haC
        have hBC := gm06BlockSets_eq_of_common hD' hB hC hb hbC
        exact gm06_finset_ne_sets hne (hAC.trans hBC.symm)
      have hpos : gm06PositionCross i.val j.val k.val l.val = true := by
        rw [gm06PositionCross_eq hnd, hi, hj, hk, hl]
        exact hcrossL
      have hq : gm06QuadTest x.division L i j k l = true := by
        simp only [gm06QuadTest, gm06QuadPattern, hi, hj, hk, hl,
          Bool.and_eq_true, decide_eq_true_eq]
        exact ⟨hpos, hac, hbd, hab, hpa, hpb⟩
      exact False.elim (Bool.noConfusion ((hscan i j k l).symm.trans hq))
  · intro hcf i j k l
    cases hq : gm06QuadTest x.division L i j k l with
    | false => rfl
    | true =>
      have ht := hq
      simp only [gm06QuadTest, gm06QuadPattern, Bool.and_eq_true, decide_eq_true_eq] at ht
      obtain ⟨A, hA, ha, hc⟩ := (gm06BlockTag_eq_pos_iff hD' _ _).mp ⟨ht.2.1, ht.2.2.2.2.1⟩
      obtain ⟨B, hB, hb, hd⟩ := (gm06BlockTag_eq_pos_iff hD' _ _).mp ⟨ht.2.2.1, ht.2.2.2.2.2⟩
      have hne : A.toFinset ≠ B.toFinset := by
        intro heq
        have hbA : L.get k ∈ A := by
          have hm : L.get k ∈ B.toFinset := List.mem_toFinset.mpr hb
          exact List.mem_toFinset.mp (heq.symm ▸ hm)
        exact ht.2.2.2.1 (gm06BlockTag_eq_of_same_block hD' hA ha hbA)
      have hfalse := hcf A hA B hB hne (L.get i) ha (L.get j) hc (L.get k) hb (L.get l) hd
      have htrue : x.crosses (L.get i) (L.get j) (L.get k) (L.get l) = true := by
        rw [hcross, ← gm06PositionCross_eq hnd]
        exact ht.1
      exact False.elim (Bool.noConfusion (hfalse.symm.trans htrue))

end GraphMinor.Compute
