module
public import GraphMinor.Thomason.UniformSamples
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Subgraph
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Data.Fintype.Powerset
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# The loss estimates for one block

Fix a graph `H` on `n` vertices in which every vertex has at most `q`
non-neighbours other than itself. We count the injective maps of a finite
set of `s` positions into the vertices whose image is a bad block.

* The vertices not dominated by the image, summed over all injective maps,
  are at most `n (q / n) ^ s` times the number of maps. A vertex is not
  dominated exactly when all `s` samples are among its non-neighbours.
* At most `(2 ^ (s - 1) - 1) n q ^ (s - 1)` injective maps have a
  disconnected image. A disconnected image has a cut with no edges across
  it. For a fixed cut, all edges of a double star across the cut join
  non-neighbours, and such maps are counted from the centres outwards.

These are the domination and connectivity estimates in the proof of
Lemma 1 of the note `docs/thomason/uniform_minor_bound.tex`.
-/

public section
namespace GraphMinor.Thomason.Uniform
open Finset

variable {W : Type*} [Fintype W] [DecidableEq W] (H : SimpleGraph W) [DecidableRel H.Adj]

/-- The vertices other than `v` that are not adjacent to `v`. -/
def nonNbr (v : W) : Finset W := univ.filter (fun w => w ≠ v ∧ ¬ H.Adj v w)

/-- The vertices not dominated by `S`: those outside `S` with no neighbour
in `S`. -/
def undom (S : Finset W) : Finset W := univ.filter (fun v => S ⊆ nonNbr H v)

theorem mem_nonNbr {v w : W} : w ∈ nonNbr H v ↔ w ≠ v ∧ ¬ H.Adj v w := by
  simp [nonNbr]

theorem mem_nonNbr_comm {v w : W} : w ∈ nonNbr H v ↔ v ∈ nonNbr H w := by
  rw [mem_nonNbr, mem_nonNbr, H.adj_comm]
  exact and_congr ne_comm Iff.rfl

theorem mem_undom {S : Finset W} {v : W} : v ∈ undom H S ↔ S ⊆ nonNbr H v := by
  simp [undom]

theorem card_nonNbr_le (v : W) : (nonNbr H v).card ≤ Fintype.card W :=
  card_le_univ _

section Domination
variable {α : Type*} [Fintype α] [DecidableEq α]

/-- Counting pairs of an injective map and a vertex it does not dominate,
in the two orders. -/
theorem sum_card_undom :
    ∑ f : α ↪ W, ((undom H (univ.image f)).card : ℝ) =
      ∑ v, ((nonNbr H v).card.descFactorial (Fintype.card α) : ℝ) := by
  have hrow (f : α ↪ W) : ((undom H (univ.image f)).card : ℝ) =
      ∑ v, if ∀ x, f x ∈ nonNbr H v then (1 : ℝ) else 0 := by
    rw [undom, card_filter]
    push_cast
    refine Finset.sum_congr rfl fun v _ => ?_
    simp only [image_subset_iff, mem_univ, true_implies]
  simp only [hrow]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun v _ => ?_
  rw [← card_embedding_into (α := α) (nonNbr H v), card_filter]
  push_cast
  rfl

/-- The expected number of undominated vertices of a block of `s`
distinct samples is at most `n (q / n) ^ s`. -/
theorem sum_card_undom_le (q : ℕ) (hq : ∀ v, (nonNbr H v).card ≤ q) :
    ∑ f : α ↪ W, ((undom H (univ.image f)).card : ℝ) ≤
      (Fintype.card (α ↪ W) : ℝ) *
        (Fintype.card W * ((q : ℝ) / Fintype.card W) ^ Fintype.card α) := by
  rw [sum_card_undom, Fintype.card_embedding_eq]
  set n := Fintype.card W
  set s := Fintype.card α
  have hterm (v : W) : ((nonNbr H v).card.descFactorial s : ℝ) ≤
      (n.descFactorial s : ℝ) * ((q : ℝ) / n) ^ s := by
    rcases le_or_gt s n with hsn | hsn
    · have hd := descFactorial_div_le_pow (card_nonNbr_le H v) hsn
      have hpos : (0 : ℝ) < n.descFactorial s := by
        exact_mod_cast Nat.descFactorial_pos.mpr hsn
      rw [div_le_iff₀ hpos] at hd
      refine hd.trans ?_
      rw [mul_comm]
      refine mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) ?_ s) hpos.le
      exact div_le_div_of_nonneg_right (by exact_mod_cast hq v) (by positivity)
    · have h0 : (nonNbr H v).card.descFactorial s = 0 :=
        Nat.descFactorial_eq_zero_iff_lt.mpr ((card_nonNbr_le H v).trans_lt hsn)
      rw [h0, Nat.cast_zero]
      positivity
  calc ∑ v, ((nonNbr H v).card.descFactorial s : ℝ)
      ≤ ∑ _v : W, (n.descFactorial s : ℝ) * ((q : ℝ) / n) ^ s :=
        Finset.sum_le_sum fun v _ => hterm v
    _ = (n.descFactorial s : ℝ) * (n * ((q : ℝ) / n) ^ s) := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]; ring

end Domination

section Connectivity
variable {α : Type*} [Fintype α] [DecidableEq α]

/-- A disconnected image has a cut of the positions, containing a given
position, with no edge across it: take the positions whose image is
reachable from the image of `x₀`. -/
theorem exists_cut_of_not_connected (f : α ↪ W) (x₀ : α)
    (hnc : ¬ (H.induce ((univ.image f : Finset W) : Set W)).Connected) :
    ∃ X : Finset α, x₀ ∈ X ∧ X ≠ univ ∧ ∀ x ∈ X, ∀ y ∉ X, ¬ H.Adj (f x) (f y) := by
  classical
  set S : Finset W := univ.image f
  have hmem (x : α) : f x ∈ ((S : Finset W) : Set W) := by
    simp [S]
  let G' := H.induce ((S : Finset W) : Set W)
  let X : Finset α := univ.filter (fun x => G'.Reachable ⟨f x₀, hmem x₀⟩ ⟨f x, hmem x⟩)
  refine ⟨X, by simp [X], ?_, ?_⟩
  · intro hX
    apply hnc
    have hall (x : α) : G'.Reachable ⟨f x₀, hmem x₀⟩ ⟨f x, hmem x⟩ := by
      have : x ∈ X := hX ▸ mem_univ x
      simpa [X] using this
    have hnon : Nonempty ↥((S : Finset W) : Set W) := ⟨⟨f x₀, hmem x₀⟩⟩
    have hrep (u : ↥((S : Finset W) : Set W)) : ∃ x, (⟨f x, hmem x⟩ : ↥((S : Finset W) : Set W)) = u := by
      obtain ⟨x, -, hx⟩ := Finset.mem_image.mp (Finset.mem_coe.mp u.2)
      exact ⟨x, Subtype.ext hx⟩
    refine ⟨fun u v => ?_⟩
    obtain ⟨x, rfl⟩ := hrep u
    obtain ⟨y, rfl⟩ := hrep v
    exact (hall x).symm.trans (hall y)
  · intro x hx y hy hadj
    apply hy
    have hx' : G'.Reachable ⟨f x₀, hmem x₀⟩ ⟨f x, hmem x⟩ := by simpa [X] using hx
    have hG : G'.Adj ⟨f x, hmem x⟩ ⟨f y, hmem y⟩ := hadj
    simpa [X] using hx'.trans hG.reachable

/-- For a fixed cut, the maps sending every pair across the cut to
non-neighbours number at most `n q ^ (s - 1)`. All edges of the double
star with centres `x₀` and `y₀` must map to non-neighbour pairs. -/
theorem card_cut_maps_le (q : ℕ) (hq : ∀ v, (nonNbr H v).card ≤ q)
    (X : Finset α) {x₀ y₀ : α} (hx₀ : x₀ ∈ X) (hy₀ : y₀ ∉ X) :
    (univ.filter (fun f : α → W => ∀ x ∈ X, ∀ y ∉ X, f y ∈ nonNbr H (f x))).card ≤
      Fintype.card W * q ^ (Fintype.card α - 1) := by
  have hne : x₀ ≠ y₀ := fun h => hy₀ (h ▸ hx₀)
  let t : W → W → α → Finset W := fun a b z =>
    if z = x₀ then {a} else if z = y₀ then {b} else if z ∈ X then nonNbr H b else nonNbr H a
  have hsub : univ.filter (fun f : α → W => ∀ x ∈ X, ∀ y ∉ X, f y ∈ nonNbr H (f x)) ⊆
      univ.biUnion (fun a => (nonNbr H a).biUnion (fun b => Fintype.piFinset (t a b))) := by
    intro f hf
    simp only [mem_filter, mem_univ, true_and] at hf
    simp only [mem_biUnion, mem_univ, true_and, Fintype.mem_piFinset]
    refine ⟨f x₀, f y₀, hf x₀ hx₀ y₀ hy₀, fun z => ?_⟩
    simp only [t]
    split_ifs with h1 h2 h3
    · simp [h1]
    · simp [h2]
    · exact (mem_nonNbr_comm H).mp (hf z h3 y₀ hy₀)
    · exact hf x₀ hx₀ z h3
  have hprod (a b : W) : (Fintype.piFinset (t a b)).card ≤ q ^ (Fintype.card α - 2) := by
    rw [Fintype.card_piFinset]
    calc ∏ z, (t a b z).card
        ≤ ∏ z, (if z = x₀ ∨ z = y₀ then 1 else q) := by
          refine Finset.prod_le_prod' fun z _ => ?_
          simp only [t]
          split_ifs <;> simp_all
      _ = q ^ (Fintype.card α - 2) := by
          rw [Finset.prod_ite, Finset.prod_const_one, one_mul, Finset.prod_const]
          congr 1
          have : univ.filter (fun z => ¬(z = x₀ ∨ z = y₀)) = univ \ {x₀, y₀} := by
            ext z; simp
          rw [this, card_sdiff_of_subset (subset_univ _), card_univ, card_pair hne]
  have hs : 2 ≤ Fintype.card α := by
    rw [← card_pair hne]; exact card_le_univ _
  calc _ ≤ _ := card_le_card hsub
    _ ≤ ∑ a, ∑ b ∈ nonNbr H a, (Fintype.piFinset (t a b)).card :=
        card_biUnion_le.trans (Finset.sum_le_sum fun a _ => card_biUnion_le)
    _ ≤ ∑ _a : W, q * q ^ (Fintype.card α - 2) := by
        refine Finset.sum_le_sum fun a _ => ?_
        calc ∑ b ∈ nonNbr H a, (Fintype.piFinset (t a b)).card
            ≤ ∑ _b ∈ nonNbr H a, q ^ (Fintype.card α - 2) := Finset.sum_le_sum fun b _ => hprod a b
          _ = (nonNbr H a).card * q ^ (Fintype.card α - 2) := by rw [sum_const, smul_eq_mul]
          _ ≤ q * q ^ (Fintype.card α - 2) := Nat.mul_le_mul_right _ (hq a)
    _ = Fintype.card W * q ^ (Fintype.card α - 1) := by
        rw [sum_const, card_univ, smul_eq_mul, ← pow_succ']
        congr 2
        omega

open Classical in
/-- At most `(2 ^ (s - 1) - 1) n q ^ (s - 1)` injective maps of `s`
positions have a disconnected image. -/
theorem card_not_connected_le (q : ℕ) (hq : ∀ v, (nonNbr H v).card ≤ q) (x₀ : α) :
    (univ.filter (fun f : α ↪ W =>
        ¬ (H.induce ((univ.image f : Finset W) : Set W)).Connected)).card ≤
      (2 ^ (Fintype.card α - 1) - 1) * (Fintype.card W * q ^ (Fintype.card α - 1)) := by
  let cuts : Finset (Finset α) :=
    ((univ.erase x₀).powerset.erase (univ.erase x₀)).image (insert x₀)
  have hcuts : cuts.card ≤ 2 ^ (Fintype.card α - 1) - 1 := by
    refine card_image_le.trans ?_
    rw [card_erase_of_mem (mem_powerset_self _), card_powerset,
      card_erase_of_mem (mem_univ _), card_univ]
  have hmemcut (X : Finset α) (hx : x₀ ∈ X) (hX : X ≠ univ) : X ∈ cuts := by
    refine mem_image.mpr ⟨X.erase x₀, ?_, insert_erase hx⟩
    refine mem_erase.mpr ⟨fun h => hX ?_, ?_⟩
    · rw [← insert_erase hx, h, insert_erase (mem_univ _)]
    · exact mem_powerset.mpr (erase_subset_erase _ (subset_univ _))
  have hcut_props (X : Finset α) (hX : X ∈ cuts) : x₀ ∈ X ∧ X ≠ univ := by
    obtain ⟨Y, hY, rfl⟩ := mem_image.mp hX
    obtain ⟨hYne, hYsub⟩ := mem_erase.mp hY
    refine ⟨mem_insert_self _ _, fun h => hYne ?_⟩
    have hYsub' := mem_powerset.mp hYsub
    refine Finset.Subset.antisymm hYsub' fun z hz => ?_
    have hz' : z ∈ insert x₀ Y := h ▸ mem_univ z
    rcases mem_insert.mp hz' with h1 | h1
    · exact absurd h1 (ne_of_mem_erase hz)
    · exact h1
  have hsub : univ.filter (fun f : α ↪ W =>
        ¬ (H.induce ((univ.image f : Finset W) : Set W)).Connected) ⊆
      cuts.biUnion (fun X => univ.filter (fun f : α ↪ W =>
        ∀ x ∈ X, ∀ y ∉ X, f y ∈ nonNbr H (f x))) := by
    intro f hf
    simp only [mem_filter, mem_univ, true_and] at hf
    obtain ⟨X, hx, hX, hcut⟩ := exists_cut_of_not_connected H f x₀ hf
    refine mem_biUnion.mpr ⟨X, hmemcut X hx hX, ?_⟩
    simp only [mem_filter, mem_univ, true_and]
    intro x hxX y hyX
    refine (mem_nonNbr H).mpr ⟨fun h => ?_, hcut x hxX y hyX⟩
    exact hyX (f.injective h ▸ hxX)
  have hper (X : Finset α) (hX : X ∈ cuts) :
      (univ.filter (fun f : α ↪ W => ∀ x ∈ X, ∀ y ∉ X, f y ∈ nonNbr H (f x))).card ≤
        Fintype.card W * q ^ (Fintype.card α - 1) := by
    obtain ⟨hx, hXu⟩ := hcut_props X hX
    obtain ⟨y₀, hy₀⟩ : ∃ y₀, y₀ ∉ X := by
      by_contra h
      exact hXu (eq_univ_of_forall fun z => not_not.mp fun hz => h ⟨z, hz⟩)
    refine le_trans ?_ (card_cut_maps_le H q hq X hx hy₀)
    refine card_le_card_of_injOn (fun f : α ↪ W => (f : α → W)) ?_ ?_
    · intro f hf
      simp only [coe_filter, Set.mem_ofPred_eq, mem_univ, true_and] at hf ⊢
      exact hf
    · intro f _ g _ h
      exact DFunLike.coe_injective h
  calc _ ≤ _ := card_le_card hsub
    _ ≤ ∑ X ∈ cuts, (univ.filter (fun f : α ↪ W =>
          ∀ x ∈ X, ∀ y ∉ X, f y ∈ nonNbr H (f x))).card := card_biUnion_le
    _ ≤ ∑ _X ∈ cuts, Fintype.card W * q ^ (Fintype.card α - 1) := Finset.sum_le_sum hper
    _ = cuts.card * (Fintype.card W * q ^ (Fintype.card α - 1)) := by
        rw [sum_const, smul_eq_mul]
    _ ≤ _ := Nat.mul_le_mul_right _ hcuts

end Connectivity

end GraphMinor.Thomason.Uniform
