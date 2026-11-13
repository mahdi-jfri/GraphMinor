module

public import GraphMinor.GM21.Section6Cuts
import Mathlib.Order.Preorder.Finite
import Mathlib.Data.Finset.Max
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Push
import Mathlib.Data.Set.Card.Arithmetic
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
# Graph Minors XXI, proof of (6.5): counting the jumps region by region

In the proof of (6.5) (page 26 of the preprint) the presentation has two supports, and the
regions $r_1, \dots, r_t$ that meet both of them are separated by the jumps $P_1, \dots, P_{t-1}$
between the two supports:
"For $1 \le i < t$, let $P_i$ be the $\Sigma$-jump with $\bar{r}_i \cap \bar{r}_{i+1} = U(P_i)$
... Since every $\Sigma$-jump $J$ with $U(J) \subseteq R_i \cup I_1 \cup I_2$ either has both ends
in $I_1$ or has both ends in $I_2$ ... it follows that $R_i$ includes at most $2\lambda'$
$\Sigma$-jumps. Counting $P_1, \ldots, P_{t-1}$, and using the fact that $t \le n$, we deduce that
there are at most $2\lambda't + t - 1 \le \lambda$ $\Sigma$-jumps altogether".

This file does this count with positions along the boundary, as in `Section6Cuts`, for any number
`r` of supports. Support `j` occupies the block of positions `[a j, b j]`, the blocks are disjoint,
and every end of a jump lies in a block. A jump with its two ends in different blocks `j ≠ j'` is
a *cross* jump (`blockCross`); in the proof of (6.5) these are the `P_i`.

The ends in `[a j, b j]` of the cross jumps, together with `a j` and `b j`, cut `[a j, b j]` into
intervals, the supports `I_j` of the regions. No jump crosses such an interval (`noCross_gap`),
and every jump with both ends in `[a j, b j]` lies in one of them. So if each such interval holds
at most `lam` jumps and there are at most `m` cross jumps from one block to another, then at most
`r ((2 r m + 1) lam) + r r m` jumps exist (`ncard_le_of_blocks`).
-/

@[expose] public section

namespace GraphMinor
namespace GM21
namespace Cuts

open Set

universe u

variable {ι : Type u} {lo hi : ι → ℝ} {T : Set ι}

/-- No jump of `T` crosses the interval `[x, y]`. -/
def NoCross (lo hi : ι → ℝ) (T : Set ι) (x y : ℝ) : Prop :=
  ∀ J ∈ T, ¬ (x < lo J ∧ lo J < y ∧ y < hi J) ∧ ¬ (lo J < x ∧ x < hi J ∧ hi J < y)

/-- The jumps with first end in the block `[a₁, b₁]` and second end in the block `[a₂, b₂]`. -/
def blockCross (lo hi : ι → ℝ) (T : Set ι) (a₁ b₁ a₂ b₂ : ℝ) : Set ι :=
  {J ∈ T | lo J ∈ Icc a₁ b₁ ∧ hi J ∈ Icc a₂ b₂}

/-- The jumps leaving the block `[a, b]` forwards: first end in the block, second end after it. -/
def outFwd (lo hi : ι → ℝ) (T : Set ι) (a b : ℝ) : Set ι :=
  {P ∈ T | a ≤ lo P ∧ lo P ≤ b ∧ b < hi P}

/-- The jumps leaving the block `[a, b]` backwards: first end before the block, second end in
it. -/
def outBwd (lo hi : ι → ℝ) (T : Set ι) (a b : ℝ) : Set ι :=
  {P ∈ T | lo P < a ∧ a ≤ hi P ∧ hi P ≤ b}

section block

variable (hlt : ∀ J ∈ T, lo J < hi J)
  (hlam : ∀ J ∈ T, ∀ J' ∈ T, ¬ (lo J < lo J' ∧ lo J' < hi J ∧ hi J < hi J'))
  {a b : ℝ}

/-- The cut points of the block `[a, b]`: `a`, and the ends in the block of the jumps leaving it. -/
def cutPoints (lo hi : ι → ℝ) (T : Set ι) (a b : ℝ) : Set ℝ :=
  insert a (lo '' outFwd lo hi T a b ∪ hi '' outBwd lo hi T a b)

include hlam in
/-- **No jump crosses a gap.** Let `g < h` lie in the block `[a, b]`, where `g` is a cut point and
`h` is a cut point or `b`, with no cut point strictly between them. Then no jump crosses `[g, h]`.
-/
theorem noCross_gap {g h : ℝ} (hag : a ≤ g) (hhb : h ≤ b)
    (hg : g ∈ cutPoints lo hi T a b) (hh : h ∈ cutPoints lo hi T a b ∨ h = b)
    (hnone : ∀ y ∈ cutPoints lo hi T a b, ¬ (g < y ∧ y < h)) :
    NoCross lo hi T g h := by
  intro J hJ
  constructor
  · rintro ⟨h1, h2, h3⟩
    by_cases hJb : hi J ≤ b
    · -- `h < hi J ≤ b`, so `h` is a cut point other than `a`.
      rcases hh with hh | rfl
      · rcases hh with rfl | ⟨P, hP, rfl⟩ | ⟨P, hP, rfl⟩
        · linarith
        · exact hlam J hJ P hP.1 ⟨h2, h3, by linarith [hP.2.2.2]⟩
        · exact hlam P hP.1 J hJ ⟨by linarith [hP.2.1], h2, h3⟩
      · linarith
    · push Not at hJb
      exact hnone (lo J) (Or.inr (Or.inl ⟨J, ⟨hJ, by linarith, by linarith, hJb⟩, rfl⟩)) ⟨h1, h2⟩
  · rintro ⟨h1, h2, h3⟩
    by_cases hJa : a ≤ lo J
    · -- `a ≤ lo J < g`, so `g` is a cut point other than `a`.
      rcases hg with rfl | ⟨P, hP, rfl⟩ | ⟨P, hP, rfl⟩
      · linarith
      · exact hlam J hJ P hP.1 ⟨h1, h2, by linarith [hP.2.2.2]⟩
      · exact hlam P hP.1 J hJ ⟨by linarith [hP.2.1], h1, h2⟩
    · push Not at hJa
      exact hnone (hi J) (Or.inr (Or.inr ⟨J, ⟨hJ, hJa, by linarith, by linarith⟩, rfl⟩)) ⟨h2, h3⟩

include hlt hlam in
/-- **The jumps of one block.** If each interval between consecutive cut points of `[a, b]`
holds at most `lam` jumps, and at most `M` jumps leave the block, then at most `(M + 1) * lam`
jumps have both ends in `[a, b]`. -/
theorem ncard_block_le (hT : T.Finite) (hab : a ≤ b) {M lam : ℕ}
    (hM : (outFwd lo hi T a b).ncard + (outBwd lo hi T a b).ncard ≤ M)
    (hint : ∀ g h : ℝ, g < h → a ≤ g → h ≤ b → g ∈ cutPoints lo hi T a b →
      (h ∈ cutPoints lo hi T a b ∨ h = b) →
      NoCross lo hi T g h → (insideSet lo hi T ⟨g, h, true⟩).ncard ≤ lam) :
    {J ∈ T | lo J ∈ Icc a b ∧ hi J ∈ Icc a b}.ncard ≤ (M + 1) * lam := by
  classical
  have hF : (outFwd lo hi T a b).Finite := hT.subset fun J hJ => hJ.1
  have hB : (outBwd lo hi T a b).Finite := hT.subset fun J hJ => hJ.1
  set GL : Finset ℝ := insert a (hF.toFinset.image lo ∪ hB.toFinset.image hi) with hGL
  have hGLmem : ∀ y, y ∈ GL ↔ y ∈ cutPoints lo hi T a b := by
    intro y
    simp [hGL, cutPoints]
  have hGLcard : GL.card ≤ M + 1 := by
    calc GL.card ≤ (hF.toFinset.image lo ∪ hB.toFinset.image hi).card + 1 :=
          Finset.card_insert_le _ _
      _ ≤ (hF.toFinset.image lo).card + (hB.toFinset.image hi).card + 1 := by
          gcongr; exact Finset.card_union_le _ _
      _ ≤ hF.toFinset.card + hB.toFinset.card + 1 := by
          gcongr <;> exact Finset.card_image_le
      _ = (outFwd lo hi T a b).ncard + (outBwd lo hi T a b).ncard + 1 := by
          rw [ncard_eq_toFinset_card _ hF, ncard_eq_toFinset_card _ hB]
      _ ≤ M + 1 := by omega
  have hGL_ge : ∀ y ∈ GL, a ≤ y ∧ y ≤ b := by
    intro y hy
    rcases (hGLmem y).1 hy with rfl | ⟨P, hP, rfl⟩ | ⟨P, hP, rfl⟩
    · exact ⟨le_rfl, hab⟩
    · exact ⟨hP.2.1, hP.2.2.1⟩
    · exact ⟨hP.2.2.1, hP.2.2.2⟩
  -- The next cut point after `g`, or `b`.
  let nxt : ℝ → ℝ := fun g => ((GL.filter (g < ·)) ∪ {b}).min' ⟨b, by simp⟩
  have hnxt_le : ∀ g, nxt g ≤ b := fun g => Finset.min'_le _ _ (by simp)
  have hnxt_lt : ∀ g, ∀ y ∈ GL, g < y → nxt g ≤ y := fun g y hy hgy =>
    Finset.min'_le _ _ (Finset.mem_union_left _ (Finset.mem_filter.2 ⟨hy, hgy⟩))
  have hnxt_mem : ∀ g, nxt g ∈ cutPoints lo hi T a b ∨ nxt g = b := by
    intro g
    have h := Finset.min'_mem ((GL.filter (g < ·)) ∪ {b}) ⟨b, by simp⟩
    rcases Finset.mem_union.1 h with h | h
    · exact Or.inl ((hGLmem _).1 (Finset.mem_filter.1 h).1)
    · exact Or.inr (Finset.mem_singleton.1 h)
  -- Each interval between consecutive cut points holds at most `lam` jumps.
  have hbound : ∀ g ∈ GL, (insideSet lo hi T ⟨g, nxt g, true⟩).ncard ≤ lam := by
    intro g hg
    by_cases hgn : g < nxt g
    · have hgc := (hGLmem g).1 hg
      refine hint g (nxt g) hgn (hGL_ge g hg).1 (hnxt_le g) hgc (hnxt_mem g)
        (noCross_gap hlam (hGL_ge g hg).1 (hnxt_le g) hgc (hnxt_mem g) ?_)
      rintro y hy ⟨h1, h2⟩
      exact absurd (hnxt_lt g y ((hGLmem y).2 hy) h1) (not_le.2 h2)
    · have : insideSet lo hi T ⟨g, nxt g, true⟩ = ∅ := by
        refine eq_empty_of_forall_notMem ?_
        rintro J ⟨hJ, h1, h2, -⟩
        change g ≤ lo J at h1
        change hi J ≤ nxt g at h2
        have := hlt J hJ
        push Not at hgn
        linarith
      rw [this, ncard_empty]
      exact Nat.zero_le _
  -- Every jump with both ends in `[a, b]` lies in one of these intervals.
  have hcover : {J ∈ T | lo J ∈ Icc a b ∧ hi J ∈ Icc a b} ⊆
      ⋃ g ∈ GL, insideSet lo hi T ⟨g, nxt g, true⟩ := by
    rintro J ⟨hJ, ⟨hJa, -⟩, ⟨-, hJb⟩⟩
    have hne : (GL.filter (· ≤ lo J)).Nonempty :=
      ⟨a, Finset.mem_filter.2 ⟨Finset.mem_insert_self _ _, hJa⟩⟩
    set g := (GL.filter (· ≤ lo J)).max' hne with hg_def
    have hgmem := Finset.max'_mem _ hne
    have hgGL : g ∈ GL := (Finset.mem_filter.1 hgmem).1
    have hglo : g ≤ lo J := (Finset.mem_filter.1 hgmem).2
    refine mem_biUnion (x := g) (Finset.mem_coe.2 hgGL) ⟨hJ, hglo, ?_, Or.inl rfl⟩
    show hi J ≤ nxt g
    refine Finset.le_min' _ _ _ fun y hy => ?_
    rcases Finset.mem_union.1 hy with hy | hy
    · obtain ⟨hyGL, hgy⟩ := Finset.mem_filter.1 hy
      have hylo : lo J < y := by
        by_contra h
        push Not at h
        have := Finset.le_max' _ y
          (Finset.mem_filter.2 ⟨hyGL, h⟩ : y ∈ GL.filter (· ≤ lo J))
        rw [← hg_def] at this
        linarith
      by_contra h
      push Not at h
      rcases (hGLmem y).1 hyGL with rfl | ⟨P, hP, rfl⟩ | ⟨P, hP, rfl⟩
      · linarith
      · exact hlam J hJ P hP.1 ⟨hylo, h, by linarith [hP.2.2.2]⟩
      · exact hlam P hP.1 J hJ ⟨by linarith [hP.2.1], hylo, h⟩
    · rw [Finset.mem_singleton.1 hy]
      exact hJb
  calc {J ∈ T | lo J ∈ Icc a b ∧ hi J ∈ Icc a b}.ncard
      ≤ (⋃ g ∈ GL, insideSet lo hi T ⟨g, nxt g, true⟩).ncard := by
        refine ncard_le_ncard hcover ?_
        exact ((Set.toFinite (GL : Set ℝ)).biUnion fun g _ => hT.subset fun J hJ => hJ.1)
    _ ≤ ∑ g ∈ GL, (insideSet lo hi T ⟨g, nxt g, true⟩).ncard := by
        have := GL.set_ncard_biUnion_le (fun g => insideSet lo hi T ⟨g, nxt g, true⟩)
        simpa using this
    _ ≤ ∑ _g ∈ GL, lam := Finset.sum_le_sum hbound
    _ = GL.card * lam := by rw [Finset.sum_const, smul_eq_mul]
    _ ≤ (M + 1) * lam := Nat.mul_le_mul_right _ hGLcard

end block

/-- A union of `|s|` sets of size at most `m` has size at most `|s| * m`. -/
theorem ncard_biUnion_le_mul {κ α : Type*} (s : Finset κ) (X : κ → Set α) {m : ℕ}
    (hX : ∀ k ∈ s, (X k).ncard ≤ m) : (⋃ k ∈ s, X k).ncard ≤ s.card * m := by
  calc (⋃ k ∈ s, X k).ncard ≤ ∑ k ∈ s, (X k).ncard := s.set_ncard_biUnion_le X
    _ ≤ ∑ _k ∈ s, m := Finset.sum_le_sum hX
    _ = s.card * m := by rw [Finset.sum_const, smul_eq_mul]

/-- **The count of the proof of (6.5), for `r` supports.** Let the blocks `[a j, b j]` be disjoint
and hold all ends of the jumps. If at most `m` jumps go from one block to another given block, and
each interval between consecutive cut points of a block holds at most `lam` jumps, then there are
at most `r ((2 r m + 1) lam) + r r m` jumps. -/
theorem ncard_le_of_blocks (hlt : ∀ J ∈ T, lo J < hi J)
    (hlam : ∀ J ∈ T, ∀ J' ∈ T, ¬ (lo J < lo J' ∧ lo J' < hi J ∧ hi J < hi J'))
    (hT : T.Finite) {r : ℕ} {a b : Fin r → ℝ} (hab : ∀ j, a j ≤ b j)
    (hlo : ∀ J ∈ T, ∃ j, lo J ∈ Icc (a j) (b j)) (hhi : ∀ J ∈ T, ∃ j, hi J ∈ Icc (a j) (b j))
    {m lam : ℕ}
    (hcross : ∀ j j', j ≠ j' → (blockCross lo hi T (a j) (b j) (a j') (b j')).ncard ≤ m)
    (hint : ∀ j, ∀ g h : ℝ, g < h → a j ≤ g → h ≤ b j → g ∈ cutPoints lo hi T (a j) (b j) →
      (h ∈ cutPoints lo hi T (a j) (b j) ∨ h = b j) →
      NoCross lo hi T g h → (insideSet lo hi T ⟨g, h, true⟩).ncard ≤ lam) :
    T.ncard ≤ r * ((2 * (r * m) + 1) * lam) + r * (r * m) := by
  classical
  have hfin : ∀ X ⊆ T, X.Finite := fun X hX => hT.subset hX
  have hothers : ∀ j, ((Finset.univ : Finset (Fin r)).filter (· ≠ j)).card ≤ r := fun j =>
    (Finset.card_filter_le _ _).trans (by simp)
  -- At most `r m` jumps leave a block forwards, and at most `r m` backwards.
  have hfwd : ∀ j, (outFwd lo hi T (a j) (b j)).ncard ≤ r * m := by
    intro j
    have hsub : outFwd lo hi T (a j) (b j) ⊆
        ⋃ j' ∈ (Finset.univ : Finset (Fin r)).filter (· ≠ j),
          blockCross lo hi T (a j) (b j) (a j') (b j') := by
      rintro P ⟨hP, h1, h2, h3⟩
      obtain ⟨j', hj'⟩ := hhi P hP
      have hne : j' ≠ j := by
        rintro rfl
        linarith [hj'.2]
      exact mem_biUnion (x := j') (by simp [hne]) ⟨hP, ⟨h1, h2⟩, hj'⟩
    refine (ncard_le_ncard hsub ((Set.toFinite _).biUnion fun j' _ =>
      hfin _ fun J hJ => hJ.1)).trans ?_
    refine (ncard_biUnion_le_mul _ _ fun j' hj' => hcross j j' ?_).trans ?_
    · exact (Finset.mem_filter.1 hj').2.symm
    · exact Nat.mul_le_mul_right _ (hothers j)
  have hbwd : ∀ j, (outBwd lo hi T (a j) (b j)).ncard ≤ r * m := by
    intro j
    have hsub : outBwd lo hi T (a j) (b j) ⊆
        ⋃ j' ∈ (Finset.univ : Finset (Fin r)).filter (· ≠ j),
          blockCross lo hi T (a j') (b j') (a j) (b j) := by
      rintro P ⟨hP, h1, h2, h3⟩
      obtain ⟨j', hj'⟩ := hlo P hP
      have hne : j' ≠ j := by
        rintro rfl
        linarith [hj'.1]
      exact mem_biUnion (x := j') (by simp [hne]) ⟨hP, hj', ⟨h2, h3⟩⟩
    refine (ncard_le_ncard hsub ((Set.toFinite _).biUnion fun j' _ =>
      hfin _ fun J hJ => hJ.1)).trans ?_
    refine (ncard_biUnion_le_mul _ _ fun j' hj' => hcross j' j ?_).trans ?_
    · exact (Finset.mem_filter.1 hj').2
    · exact Nat.mul_le_mul_right _ (hothers j)
  -- Each jump has both ends in one block or is a cross jump.
  have hsub : T ⊆ (⋃ j ∈ (Finset.univ : Finset (Fin r)),
        {J ∈ T | lo J ∈ Icc (a j) (b j) ∧ hi J ∈ Icc (a j) (b j)}) ∪
      ⋃ j ∈ (Finset.univ : Finset (Fin r)), ⋃ j' ∈ (Finset.univ : Finset (Fin r)).filter (· ≠ j),
        blockCross lo hi T (a j) (b j) (a j') (b j') := by
    intro J hJ
    obtain ⟨j, hj⟩ := hlo J hJ
    obtain ⟨j', hj'⟩ := hhi J hJ
    by_cases hjj : j' = j
    · subst hjj
      exact Or.inl (mem_biUnion (x := j') (by simp) ⟨hJ, hj, hj'⟩)
    · exact Or.inr (mem_biUnion (x := j) (by simp)
        (mem_biUnion (x := j') (by simp [hjj]) ⟨hJ, hj, hj'⟩))
  have hU1 : (⋃ j ∈ (Finset.univ : Finset (Fin r)),
      {J ∈ T | lo J ∈ Icc (a j) (b j) ∧ hi J ∈ Icc (a j) (b j)}).ncard ≤
      r * ((2 * (r * m) + 1) * lam) := by
    refine (ncard_biUnion_le_mul (m := (2 * (r * m) + 1) * lam) _ _ fun j _ => ?_).trans
      (by simp)
    refine ncard_block_le hlt hlam hT (hab j) (M := 2 * (r * m)) ?_ (hint j)
    linarith [hfwd j, hbwd j]
  have hU2 : (⋃ j ∈ (Finset.univ : Finset (Fin r)),
      ⋃ j' ∈ (Finset.univ : Finset (Fin r)).filter (· ≠ j),
        blockCross lo hi T (a j) (b j) (a j') (b j')).ncard ≤ r * (r * m) := by
    refine (ncard_biUnion_le_mul (m := r * m) _ _ fun j _ => ?_).trans (by simp)
    refine (ncard_biUnion_le_mul _ _ fun j' hj' => hcross j j' ?_).trans ?_
    · exact (Finset.mem_filter.1 hj').2.symm
    · exact Nat.mul_le_mul_right _ (hothers j)
  calc T.ncard ≤ _ := ncard_le_ncard hsub (((Set.toFinite _).biUnion fun j _ =>
          hfin _ fun J hJ => hJ.1).union ((Set.toFinite _).biUnion fun j _ =>
          (Set.toFinite _).biUnion fun j' _ => hfin _ fun J hJ => hJ.1))
    _ ≤ _ := ncard_union_le _ _
    _ ≤ _ := Nat.add_le_add hU1 hU2

end Cuts
end GM21
end GraphMinor
