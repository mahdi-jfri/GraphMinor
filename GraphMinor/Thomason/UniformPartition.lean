module
public import GraphMinor.Thomason.UniformPairSums
public import GraphMinor.Thomason.CliqueMinorOfBranches
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Order.Interval.Finset.Fin
import Mathlib.Data.Finset.Sort
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith

/-!
# Lemma 1 of the note: a random partition into blocks

This is Lemma 1 of the note `docs/thomason/uniform_minor_bound.tex`,
in a form that allows blocks of different sizes. Let `H` have `n`
vertices, each with at most `q` non-neighbours other than itself. Choose
`N` disjoint blocks, block `i` with `s i` vertices, uniformly at random,
and let `A i > 0`. Call block `i` good if it leaves at most
`A i * n (q / n) ^ s i` vertices undominated. Then delete

* every block that is not good, in expectation at most `1 / A i` per block;
* every disconnected block, in expectation at most
  `(2 ^ (s i - 1) - 1) (q / (n - s i + 1)) ^ (s i - 1)` per block;
* for each pair `i < j` with block `i` good and no edge between the two
  blocks, the block `i`, in expectation at most
  `(A i * n (q / n) ^ s i / (n - s i)) ^ s j` per pair.

The remaining blocks are connected, disjoint and pairwise adjacent, so
they form a complete minor. If the expected number left exceeds `m - 1`,
some choice leaves at least `m` blocks.

The expectations are sums over all injective maps from the positions to
the vertices, bounded in `UniformBlockSums.lean` and `UniformPairSums.lean`.
-/

public section
namespace GraphMinor.Thomason.Uniform
open Finset

variable {W : Type*} [Fintype W] [DecidableEq W] (H : SimpleGraph W) [DecidableRel H.Adj]

/-- A block that does not lie among the undominated vertices of a disjoint
block has an edge to it. -/
theorem adj_of_not_subset_undom {S S' : Finset W} (hdis : Disjoint S S')
    (h : ¬ S' ⊆ undom H S) : ∃ v ∈ S, ∃ w ∈ S', H.Adj v w := by
  obtain ⟨w, hw, hwU⟩ := Finset.not_subset.mp h
  rw [mem_undom] at hwU
  obtain ⟨v, hv, hvn⟩ := Finset.not_subset.mp hwU
  rw [mem_nonNbr] at hvn
  refine ⟨v, hv, w, hw, ?_⟩
  by_contra hadj
  refine hvn ⟨fun hvw => Finset.disjoint_left.mp hdis hv (hvw ▸ hw), fun h' => hadj h'.symm⟩

/-- Lemma 1 of the note `docs/thomason/uniform_minor_bound.tex`, with blocks of
sizes `s i`: if the expected number of surviving blocks exceeds `m - 1`,
then `H` has a `K_m` minor. -/
theorem clique_isIsoMinor_of_blocks (q : ℕ) (hq : ∀ v, (nonNbr H v).card ≤ q)
    {N : ℕ} (s : Fin N → ℕ) (hs : ∀ i, 1 ≤ s i) (hsum : ∑ i, s i ≤ Fintype.card W)
    (A : Fin N → ℝ) (hA : ∀ i, 0 < A i) (m : ℕ)
    (hB : (m : ℝ) - 1 < N -
      ∑ i, (((2 : ℝ) ^ (s i - 1) - 1) *
          ((q : ℝ) / ((Fintype.card W : ℝ) - s i + 1)) ^ (s i - 1) + 1 / A i) -
      ∑ i, ∑ j ∈ univ.filter (fun j => i < j),
        (A i * (Fintype.card W * ((q : ℝ) / Fintype.card W) ^ s i) /
          ((Fintype.card W : ℝ) - s i)) ^ s j) :
    IsIsoMinor (Graph.ofSimpleGraph (⊤ : SimpleGraph (Fin m))) (Graph.ofSimpleGraph H) := by
  classical
  have hsle (i : Fin N) : s i ≤ Fintype.card W :=
    (Finset.single_le_sum (fun j _ => Nat.zero_le (s j)) (mem_univ i)).trans hsum
  let a : Fin N → ℝ := fun i => A i * (Fintype.card W * ((q : ℝ) / Fintype.card W) ^ s i)
  have ha (i : Fin N) : 0 ≤ a i := mul_nonneg (hA i).le (by positivity)
  let good : Fin N → (Pos s ↪ W) → Prop := fun i g => ((undom H (block g i)).card : ℝ) ≤ a i
  let conn : Fin N → (Pos s ↪ W) → Prop := fun i g =>
    (H.induce ((block g i : Finset W) : Set W)).Connected
  let pr : Fin N → Fin N → (Pos s ↪ W) → Prop := fun i j g =>
    good i g ∧ block g j ⊆ undom H (block g i)
  let Gs : (Pos s ↪ W) → Finset (Fin N) := fun g => univ.filter (fun i => good i g ∧ conn i g)
  let Zp : (Pos s ↪ W) → Finset (Fin N × Fin N) := fun g =>
    (univ ×ˢ univ).filter (fun p => p.1 < p.2 ∧ pr p.1 p.2 g)
  let Surv : (Pos s ↪ W) → Finset (Fin N) := fun g => Gs g \ (Zp g).image Prod.fst
  -- the survivors of one choice
  have hlower (g : Pos s ↪ W) :
      (N : ℝ) - ∑ i, (if ¬ good i g then (1 : ℝ) else 0) -
        ∑ i, (if ¬ conn i g then (1 : ℝ) else 0) -
        ∑ i, ∑ j ∈ univ.filter (fun j => i < j), (if pr i j g then (1 : ℝ) else 0) ≤
      (Surv g).card := by
    have hG : N ≤ (Gs g).card + (univ.filter (fun i => ¬ good i g)).card +
        (univ.filter (fun i => ¬ conn i g)).card := by
      have hsub : (univ : Finset (Fin N)) ⊆
          Gs g ∪ univ.filter (fun i => ¬ good i g) ∪ univ.filter (fun i => ¬ conn i g) := by
        intro i _
        by_cases h1 : good i g <;> by_cases h2 : conn i g <;> simp [Gs, h1, h2]
      calc N = (univ : Finset (Fin N)).card := by simp
        _ ≤ _ := card_le_card hsub
        _ ≤ _ := card_union_le _ _
        _ ≤ _ := Nat.add_le_add_right (card_union_le _ _) _
    have hS : (Gs g).card ≤ (Surv g).card + (Zp g).card :=
      (card_le_card_sdiff_add_card).trans (Nat.add_le_add_left card_image_le _)
    have hZ : ((Zp g).card : ℝ) =
        ∑ i, ∑ j ∈ univ.filter (fun j => i < j), (if pr i j g then (1 : ℝ) else 0) := by
      rw [card_filter]
      push_cast
      rw [Finset.sum_product]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Finset.sum_filter]
      refine Finset.sum_congr rfl fun j _ => ?_
      by_cases h1 : i < j <;> by_cases h2 : pr i j g <;> simp [h1, h2]
    have h1 : ((univ.filter (fun i => ¬ good i g)).card : ℝ) =
        ∑ i, (if ¬ good i g then (1 : ℝ) else 0) := by
      rw [card_filter]; push_cast; rfl
    have h2 : ((univ.filter (fun i => ¬ conn i g)).card : ℝ) =
        ∑ i, (if ¬ conn i g then (1 : ℝ) else 0) := by
      rw [card_filter]; push_cast; rfl
    have hG' : (N : ℝ) ≤ (Gs g).card + (univ.filter (fun i => ¬ good i g)).card +
        (univ.filter (fun i => ¬ conn i g)).card := by exact_mod_cast hG
    have hS' : ((Gs g).card : ℝ) ≤ (Surv g).card + (Zp g).card := by exact_mod_cast hS
    rw [← h1, ← h2, ← hZ]
    linarith
  -- the expected losses
  set T : ℝ := (Fintype.card (Pos s ↪ W) : ℝ) with hT_def
  have hbad (i : Fin N) : ∑ g : Pos s ↪ W, (if ¬ good i g then (1 : ℝ) else 0) ≤ T / A i := by
    refine le_trans (le_of_eq ?_) (sum_not_good_le H q hq i (A i) (hA i))
    refine Finset.sum_congr rfl fun g _ => ?_
    simp only [good, not_le, a]
  have hdisc (i : Fin N) : ∑ g : Pos s ↪ W, (if ¬ conn i g then (1 : ℝ) else 0) ≤
      T * (((2 : ℝ) ^ (s i - 1) - 1) *
        ((q : ℝ) / ((Fintype.card W : ℝ) - s i + 1)) ^ (s i - 1)) :=
    sum_not_connected_le H q hq i (hs i) (hsle i)
  have hpair (i j : Fin N) (hij : i < j) : ∑ g : Pos s ↪ W, (if pr i j g then (1 : ℝ) else 0) ≤
      T * (a i / ((Fintype.card W : ℝ) - s i)) ^ s j :=
    sum_pair_le H hij.ne (a i) (ha i) (hsle i)
  have hsumlower : T * ((m : ℝ) - 1) < ∑ g : Pos s ↪ W, ((Surv g).card : ℝ) := by
    have hTpos : 0 < T := by
      rw [hT_def, Fintype.card_embedding_eq]
      exact_mod_cast Nat.descFactorial_pos.mpr (card_pos_eq (s := s) ▸ hsum)
    refine lt_of_lt_of_le ?_ (Finset.sum_le_sum fun g _ => hlower g)
    rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib, Finset.sum_sub_distrib,
      Finset.sum_const, Finset.card_univ, nsmul_eq_mul, Finset.sum_comm,
      Finset.sum_comm (f := fun g i => if ¬ conn i g then (1 : ℝ) else 0),
      Finset.sum_comm (f := fun g i => ∑ j ∈ univ.filter (fun j => i < j),
        (if pr i j g then (1 : ℝ) else 0))]
    let F : Fin N → ℝ := fun i => ((2 : ℝ) ^ (s i - 1) - 1) *
      ((q : ℝ) / ((Fintype.card W : ℝ) - s i + 1)) ^ (s i - 1)
    let M : Fin N → Fin N → ℝ := fun i j => (a i / ((Fintype.card W : ℝ) - s i)) ^ s j
    have hB2 : (m : ℝ) - 1 < N - (∑ i, F i + ∑ i, 1 / A i) -
        ∑ i, ∑ j ∈ univ.filter (fun j => i < j), M i j := by
      rw [← Finset.sum_add_distrib]; exact hB
    have hb' : ∑ i, ∑ g : Pos s ↪ W, (if ¬ good i g then (1 : ℝ) else 0) ≤
        T * ∑ i, 1 / A i := by
      rw [Finset.mul_sum]
      exact Finset.sum_le_sum fun i _ => (hbad i).trans (le_of_eq (by ring))
    have hd' : ∑ i, ∑ g : Pos s ↪ W, (if ¬ conn i g then (1 : ℝ) else 0) ≤
        T * ∑ i, F i := by
      rw [Finset.mul_sum]
      exact Finset.sum_le_sum fun i _ => hdisc i
    have hp' : ∑ i, ∑ g : Pos s ↪ W, ∑ j ∈ univ.filter (fun j => i < j),
        (if pr i j g then (1 : ℝ) else 0) ≤
        T * ∑ i, ∑ j ∈ univ.filter (fun j => i < j), M i j := by
      rw [Finset.mul_sum]
      refine Finset.sum_le_sum fun i _ => ?_
      rw [Finset.mul_sum, Finset.sum_comm]
      exact Finset.sum_le_sum fun j hj => hpair i j (Finset.mem_filter.mp hj).2
    have hmul := mul_lt_mul_of_pos_left hB2 hTpos
    generalize ∑ i, F i = X at hmul hd'
    generalize ∑ i, 1 / A i = Y at hmul hb'
    generalize ∑ i, ∑ j ∈ univ.filter (fun j => i < j), M i j = Z at hmul hp'
    have hexp : T * ((N : ℝ) - (X + Y) - Z) = T * N - T * X - T * Y - T * Z := by ring
    rw [hexp] at hmul
    rw [← hT_def]
    linarith
  -- a good choice
  obtain ⟨g, -, hg⟩ := Finset.exists_lt_of_sum_lt (s := (univ : Finset (Pos s ↪ W)))
    (f := fun _ => ((m : ℝ) - 1)) (g := fun g => ((Surv g).card : ℝ)) (by
      rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      exact hsumlower)
  have hm : m ≤ (Surv g).card := by
    have : (m : ℝ) < (Surv g).card + 1 := by linarith
    exact_mod_cast Nat.lt_succ_iff.mp (by exact_mod_cast this)
  obtain ⟨t, hts, htc⟩ := Finset.exists_subset_card_eq hm
  let e := t.orderEmbOfFin htc
  have hsurv (k : Fin m) : e k ∈ Surv g := hts (t.orderEmbOfFin_mem htc k)
  have hGs (k : Fin m) : good (e k) g ∧ conn (e k) g := by
    have := (Finset.mem_sdiff.mp (hsurv k)).1
    simpa [Gs] using this
  have hadj_lt (k l : Fin m) (hkl : e k < e l) :
      ∃ v ∈ block g (e k), ∃ w ∈ block g (e l), H.Adj v w := by
    refine adj_of_not_subset_undom H (disjoint_block g hkl.ne) fun hsub => ?_
    have hnot := (Finset.mem_sdiff.mp (hsurv k)).2
    apply hnot
    refine Finset.mem_image.mpr ⟨(e k, e l), ?_, rfl⟩
    simp only [Zp, Finset.mem_filter, Finset.mem_product, Finset.mem_univ, true_and]
    exact ⟨hkl, (hGs k).1, hsub⟩
  refine clique_isIsoMinor_of_branches H (fun k => block g (e k)) (fun k => (hGs k).2)
    (fun k l hkl => disjoint_block g (fun h => hkl (e.injective h))) fun k l hkl => ?_
  rcases lt_or_gt_of_ne (fun h : e k = e l => hkl (e.injective h)) with h | h
  · exact hadj_lt k l h
  · obtain ⟨v, hv, w, hw, hvw⟩ := hadj_lt l k h
    exact ⟨w, hw, v, hv, hvw.symm⟩

end GraphMinor.Thomason.Uniform
