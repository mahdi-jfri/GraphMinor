module

public import GraphMinor.GM06.Defs
import GraphMinor.Compute.GM06CountPositions
import Mathlib.Tactic

/-!
# From labelled edge ends to the drawing valency

The finite input lists both ends of every edge. A bijection with the
graph's edge set and the actual link relation identify these labels
with the graph. Under this correspondence, the endpoint count is the
valency of VI, Section 1, page 116, including the factor two for loops.
-/

public section
namespace GraphMinor.Compute
open Set
universe u v

private theorem ncard_edge_labels {β : Type v} {E P : Set β} {m : ℕ}
    (edge : Fin m ≃ E) (hsub : P ⊆ E) :
    P.ncard = ({i : Fin m | (edge i).val ∈ P} : Set (Fin m)).ncard := by
  let f := fun i : Fin m => (edge i).val
  have hf : Function.Injective f := Subtype.val_injective.comp edge.injective
  have hP : f '' {i : Fin m | f i ∈ P} = P := by
    ext e
    constructor
    · rintro ⟨i, hi, rfl⟩; exact hi
    · intro he
      obtain ⟨i, hi⟩ := edge.surjective ⟨e, hsub he⟩
      have hval : f i = e := congrArg Subtype.val hi
      refine ⟨i, ?_, hval⟩
      change f i ∈ P
      rw [hval]
      exact he
  calc
    P.ncard = (f '' {i : Fin m | f i ∈ P}).ncard := congrArg Set.ncard hP.symm
    _ = _ := Set.ncard_image_of_injective _ hf

private theorem endpoint_count_loops {α : Type u} [DecidableEq α]
    (pairs : List (α × α)) (a : α) :
    (pairs.flatMap fun p => [p.1, p.2]).count a =
      (pairs.filter fun p => decide ((p.1 = a ∧ p.2 ≠ a) ∨ (p.2 = a ∧ p.1 ≠ a))).length +
      2 * (pairs.filter fun p => decide (p.1 = a ∧ p.2 = a)).length := by
  induction pairs with
  | nil => simp
  | cons p pairs ih =>
    simp only [List.flatMap_cons, List.count_append, ih]
    have he₁ : (a = p.1) ↔ (p.1 = a) := eq_comm
    have he₂ : (a = p.2) ↔ (p.2 = a) := eq_comm
    by_cases h₁ : p.1 = a <;> by_cases h₂ : p.2 = a <;>
      simp [h₁, h₂, he₁, he₂] <;> omega

/-- The valency of VI, Section 1, page 116, is the endpoint-list count
under a bijection with the actual edges and their actual ends. -/
theorem gm06VertexValency_eq_endpoint_count {α : Type u} {β : Type v} [DecidableEq α]
    (G : Graph α β) (pairs : List (α × α)) (edge : Fin pairs.length ≃ G.edgeSet)
    (hlink : ∀ i : Fin pairs.length, G.IsLink (edge i).val pairs[i.val].1 pairs[i.val].2)
    (a : α) :
    GM06.vertexValency G a = (pairs.flatMap fun p => [p.1, p.2]).count a := by
  classical
  let N : Set β := {e ∈ G.edgeSet | ∃ b ≠ a, G.IsLink e a b}
  let L : Set β := {e ∈ G.edgeSet | G.IsLink e a a}
  have hnon (i : Fin pairs.length) :
      (∃ b ≠ a, G.IsLink (edge i).val a b) ↔
        (pairs[i.val].1 = a ∧ pairs[i.val].2 ≠ a) ∨
          (pairs[i.val].2 = a ∧ pairs[i.val].1 ≠ a) := by
    constructor
    · rintro ⟨b, hb, hl⟩
      rcases (hlink i).eq_and_eq_or_eq_and_eq hl with ⟨ha, hc⟩ | ⟨ha, hc⟩
      · exact Or.inl ⟨ha, fun h => hb (hc.symm.trans h)⟩
      · exact Or.inr ⟨hc, fun h => hb (ha.symm.trans h)⟩
    · rintro (⟨ha, hb⟩ | ⟨hb, ha⟩)
      · exact ⟨pairs[i.val].2, hb, ha ▸ hlink i⟩
      · exact ⟨pairs[i.val].1, ha, hb ▸ (hlink i).symm⟩
  have hloop (i : Fin pairs.length) : G.IsLink (edge i).val a a ↔
      pairs[i.val].1 = a ∧ pairs[i.val].2 = a := by
    simpa only [or_self] using (hlink i).isLink_iff (x' := a) (y' := a)
  have hN : N.ncard =
      ({i : Fin pairs.length | (pairs[i.val].1 = a ∧ pairs[i.val].2 ≠ a) ∨
        (pairs[i.val].2 = a ∧ pairs[i.val].1 ≠ a)} : Set (Fin pairs.length)).ncard := by
    rw [ncard_edge_labels edge (fun _ h => h.1)]
    congr 1
    ext i
    simpa only [N, mem_ofPred_eq, (edge i).property, true_and] using hnon i
  have hL : L.ncard =
      ({i : Fin pairs.length | pairs[i.val].1 = a ∧ pairs[i.val].2 = a} : Set (Fin pairs.length)).ncard := by
    rw [ncard_edge_labels edge (fun _ h => h.1)]
    congr 1
    ext i
    simpa only [L, mem_ofPred_eq, (edge i).property, true_and] using hloop i
  change N.ncard + 2 * L.ncard = _
  rw [hN, hL,
    gm06Ncard_indices_eq_filter_length pairs
      (fun p => (p.1 = a ∧ p.2 ≠ a) ∨ (p.2 = a ∧ p.1 ≠ a)),
    gm06Ncard_indices_eq_filter_length pairs (fun p => p.1 = a ∧ p.2 = a)]
  exact (endpoint_count_loops pairs a).symm

end GraphMinor.Compute
