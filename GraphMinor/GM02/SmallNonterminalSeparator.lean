module

public import GraphMinor.GM02.CrossingSchemeEncoding
import GraphMinor.GM02.SmallTerminalSeparator
import GraphMinor.GM02.CrossingPathParity
import GraphMinor.GM02.ArrangementCount
import GraphMinor.GM02.OddArrangementCount
import GraphMinor.GM02.EvenArrangementCount
import Mathlib.Tactic.Linarith

/-!
# Small separators without original terminals

All crossing schemes have the same list-length parity profile when no
separator vertex is an original terminal. If a path has odd length, its
single vertex and one unused bit determine a small arrangement. Otherwise
all lists are even: on one vertex they are empty, and on two vertices
there are at most four empty-list labelings or two orders on one path.
This finishes the small cases of the bound in II (2.8).
-/

public section
namespace GraphMinor.GM02
open Graph Set Classical
universe u v

private theorem four_le_square (k : ℕ) : 4 ≤ (2 + k) ^ 2 := by
  exact Nat.pow_le_pow_left (by omega : 2 ≤ 2 + k) 2
private theorem four_add_two_le_square (k : ℕ) : 4 + 2 * k ≤ (2 + k) ^ 2 := by nlinarith

/-- II (2.8)'s count on at most two separator vertices, when neither is
an original terminal. The length parity profile is fixed across schemes. -/
theorem card_crossingSchemes_le_of_small_nonterminal {α : Type u} {β : Type v}
    {G H H' : Graph α β} (A₀ : Termination V(G))
    (hX : (V(H) ∩ V(H')).Finite) (hn : (V(H) ∩ V(H')).ncard ≤ 2)
    (hno : Disjoint (V(H) ∩ V(H')) A₀.support) :
    Nat.card (CrossingScheme G H H' A₀) ≤
      max 2 (((V(H) ∩ V(H')).ncard + A₀.index) ^ (V(H) ∩ V(H')).ncard) := by
  by_cases hz : (V(H) ∩ V(H')).ncard = 0
  · exact card_crossingSchemes_le_of_empty_separator A₀ hX hz
  have hsize : (V(H) ∩ V(H')).ncard = 1 ∨ (V(H) ∩ V(H')).ncard = 2 := by omega
  cases isEmpty_or_nonempty (CrossingScheme G H H' A₀) with
  | inl he =>
    let _ := he
    rw [Nat.card_of_isEmpty]
    exact Nat.zero_le _
  | inr he =>
    let C₀ : CrossingScheme G H H' A₀ := Classical.choice he
    let S := V(H) ∩ V(H')
    let I := {p // p ∈ A₀.pairs}
    let profile : I → ℕ := fun p => (C₀.pathListArrangement.paths p).length % 2
    let T := {A : PathListArrangement S I // ∀ i, (A.paths i).length % 2 = profile i}
    let _ := (finite_arrangements_and_card_le (I := I) hX).1
    let f : CrossingScheme G H H' A₀ → T := fun C =>
      ⟨C.pathListArrangement, fun p => C.internal_length_mod_two_eq C₀ hno p⟩
    have hf : Function.Injective f := by
      intro C D heq
      exact crossingScheme_pathListArrangement_injective (congrArg Subtype.val heq)
    have hc := Nat.card_le_card_of_injective f hf
    have hi : Nat.card I = A₀.index := by simp [I, Nat.card_eq_fintype_card, Termination.index]
    by_cases hodd : ∃ i, profile i = 1
    · obtain ⟨i, hi⟩ := hodd
      have hb := card_arrangements_with_odd_profile hX hn profile hi
      have hbound : Nat.card (CrossingScheme G H H' A₀) ≤ S.ncard * 2 := hc.trans hb
      rcases hsize with hone | htwo
      · change S.ncard = 1 at hone
        rw [hone] at hbound
        exact hbound.trans (le_max_left _ _)
      · change S.ncard = 2 at htwo
        rw [htwo] at hbound
        apply hbound.trans
        apply le_max_of_le_right
        change 4 ≤ (S.ncard + A₀.index) ^ S.ncard
        rw [htwo]
        exact four_le_square _
    · have heven : ∀ i, profile i = 0 := by
        intro i
        have hlt : profile i < 2 := Nat.mod_lt _ (by omega)
        have hne : profile i ≠ 1 := fun h => hodd ⟨i, h⟩
        omega
      have hcard : Nat.card T = Nat.card {A : PathListArrangement S I //
          ∀ i, (A.paths i).length % 2 = 0} := by
        simp only [T, heven]
      rw [hcard] at hc
      rcases hsize with hone | htwo
      · have hb := card_even_arrangements_of_ncard_one (I := I) hone
        exact (hc.trans hb).trans (le_max_left _ _)
      · have hb := card_even_arrangements_of_ncard_two (I := I) htwo
        rw [hi] at hb
        apply (hc.trans hb).trans
        apply le_max_of_le_right
        rw [htwo]
        exact four_add_two_le_square _

end GraphMinor.GM02
