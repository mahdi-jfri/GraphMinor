module

public import GraphMinor.GM02.ArrangementInsertion
public import Mathlib.Data.Set.Card
import GraphMinor.GM02.InsertionBound
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Basic.Finite.Sum

/-!
# Counting path-list arrangements

Erase the vertices of the finite separator one at a time. The erased
arrangement and one insertion slot determine the original arrangement.
There are two unused labels, one slot at the start of each path, and one
after each remaining vertex. This proves the product bound used for
II (2.8), and its power bound for at least three vertices.
-/

public section
namespace GraphMinor.GM02
open Set Finset Classical
universe u t

private theorem empty_arrangements_subsingleton {α : Type u} {I : Type t} :
    Subsingleton (PathListArrangement (∅ : Set α) I) := by
  constructor
  intro A B
  have hp : ∀ C : PathListArrangement (∅ : Set α) I, ∀ i, C.paths i = [] := by
    intro C i
    apply List.eq_nil_iff_forall_not_mem.2
    intro v hv
    exact C.vertex_mem i v hv
  apply PathListArrangement.ext_data
  · funext i
    rw [hp A i, hp B i]
  · exact (Set.eq_empty_of_subset_empty A.marked_subset).trans
      (Set.eq_empty_of_subset_empty B.marked_subset).symm

/-- The erasure injection gives finiteness and the insertion product bound
for disjoint path lists with two labels on unused vertices. -/
theorem finite_arrangements_and_card_le {α : Type u} {I : Type t} [Finite I]
    {S : Set α} (hS : S.Finite) :
    Finite (PathListArrangement S I) ∧
      Nat.card (PathListArrangement S I) ≤
        ∏ i ∈ Finset.range S.ncard, (Nat.card I + i + 2) := by
  induction S, hS using Set.Finite.induction_on with
  | empty =>
    let _ := empty_arrangements_subsingleton (α := α) (I := I)
    refine ⟨inferInstance, ?_⟩
    exact Nat.card_le_card_of_injective (fun _ => (() : Unit))
      (fun A B _ => Subsingleton.elim A B) |>.trans (by simp [Nat.card_eq_fintype_card])
  | @insert a S ha hS ih =>
    let _ : Finite S := hS.to_subtype
    have hcut : insert a S \ {a} = S := by
      ext x
      simp only [Set.mem_sdiff, Set.mem_insert_iff, Set.mem_singleton_iff]
      constructor
      · rintro ⟨h | h, hn⟩
        · exact (hn h).elim
        · exact h
      · intro hx
        exact ⟨Or.inr hx, fun heq => ha (heq ▸ hx)⟩
    let _ : Finite (PathListArrangement (insert a S \ {a}) I) := by
      rw [hcut]
      exact ih.1
    let _ : Finite (insert a S \ {a} : Set α) := ((hS.insert a).sdiff).to_subtype
    let _ : Finite (PathListArrangement (insert a S) I) :=
      Finite.of_injective (PathListArrangement.erasureEncoding a)
        (PathListArrangement.erasureEncoding_injective a)
    refine ⟨inferInstance, ?_⟩
    have hc := Nat.card_le_card_of_injective (PathListArrangement.erasureEncoding
      (S := insert a S) (I := I) a) (PathListArrangement.erasureEncoding_injective a)
    have hb : Nat.card Bool = 2 := by simp [Nat.card_eq_fintype_card]
    simp only [Nat.card_prod, Nat.card_sum, ArrangementSlot, hb, Nat.card_coe_set_eq, hcut] at hc
    have hsize : (insert a S).ncard = S.ncard + 1 := Set.ncard_insert_of_notMem ha hS
    rw [hsize, Finset.prod_range_succ]
    calc
      Nat.card (PathListArrangement (insert a S) I) ≤
          Nat.card (PathListArrangement S I) * (2 + (Nat.card I + S.ncard)) := hc
      _ ≤ (∏ i ∈ Finset.range S.ncard, (Nat.card I + i + 2)) *
          (Nat.card I + S.ncard + 2) := by
        simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
          Nat.mul_le_mul_right (2 + (Nat.card I + S.ncard)) ih.2

/-- The path-list insertion bound in the range of at least three vertices. -/
theorem card_arrangements_le_pow {α : Type u} {I : Type t} [Finite I]
    {S : Set α} (hS : S.Finite) (hn : 3 ≤ S.ncard) :
    Nat.card (PathListArrangement S I) ≤ (Nat.card I + S.ncard) ^ S.ncard :=
  (finite_arrangements_and_card_le (I := I) hS).2.trans
    (insertion_product_le_pow (Nat.card I) S.ncard hn)

end GraphMinor.GM02
