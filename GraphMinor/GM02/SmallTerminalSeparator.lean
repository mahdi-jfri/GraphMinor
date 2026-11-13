module

public import GraphMinor.GM02.CrossingSchemeEncoding
import GraphMinor.GM02.ArrangementAbsent
import GraphMinor.GM02.ArrangementCount
import Mathlib.Tactic.Linarith

/-!
# Small separators containing an original terminal

In II (2.8), an original terminal is never in an internal path list. Its
erasure therefore leaves only two possible marked bits. With at most two
separator vertices, the remaining arrangement has at most one vertex and
the insertion product gives the printed bound directly. The empty
separator case follows from the empty arrangement count.
-/

public section
namespace GraphMinor.GM02
open Graph Set Classical
universe u v

private theorem card_bound_of_empty_separator {α : Type u} {β : Type v}
    {G H H' : Graph α β} (A₀ : Termination V(G))
    (hX : (V(H) ∩ V(H')).Finite) (hn : (V(H) ∩ V(H')).ncard = 0) :
    Nat.card (CrossingScheme G H H' A₀) ≤ 1 := by
  let _ := (finite_arrangements_and_card_le (I := {p // p ∈ A₀.pairs}) hX).1
  have hc := Nat.card_le_card_of_injective CrossingScheme.pathListArrangement
    (crossingScheme_pathListArrangement_injective (G := G) (H := H) (H' := H') (A₀ := A₀))
  have hb := (finite_arrangements_and_card_le (I := {p // p ∈ A₀.pairs}) hX).2
  rw [hn] at hb
  exact hc.trans (by simpa using hb)

/-- II (2.8)'s bound for an empty separator. -/
theorem card_crossingSchemes_le_of_empty_separator {α : Type u} {β : Type v}
    {G H H' : Graph α β} (A₀ : Termination V(G))
    (hX : (V(H) ∩ V(H')).Finite) (hn : (V(H) ∩ V(H')).ncard = 0) :
    Nat.card (CrossingScheme G H H' A₀) ≤
      max 2 (((V(H) ∩ V(H')).ncard + A₀.index) ^ (V(H) ∩ V(H')).ncard) := by
  exact (card_bound_of_empty_separator A₀ hX hn).trans (by omega)

/-- II (2.8)'s bound when a separator of at most two vertices contains
an original terminal. Its erased encoding loses only one marked bit. -/
theorem card_crossingSchemes_le_of_small_terminal {α : Type u} {β : Type v}
    {G H H' : Graph α β} (A₀ : Termination V(G))
    (hX : (V(H) ∩ V(H')).Finite) (hn : (V(H) ∩ V(H')).ncard ≤ 2)
    {a : α} (haX : a ∈ V(H) ∩ V(H')) (ha₀ : a ∈ A₀.support) :
    Nat.card (CrossingScheme G H H' A₀) ≤
      max 2 (((V(H) ∩ V(H')).ncard + A₀.index) ^ (V(H) ∩ V(H')).ncard) := by
  let S := V(H) ∩ V(H')
  let I := {p // p ∈ A₀.pairs}
  have haAbsent : ∀ C : CrossingScheme G H H' A₀, ∀ p,
      a ∉ C.pathListArrangement.paths p := by
    intro C p hap
    have h := of_decide_eq_true (List.mem_filter.1 hap).2
    exact h.2 ha₀
  let f : CrossingScheme G H H' A₀ → PathListArrangement (S \ {a}) I × Bool :=
    fun C => (C.pathListArrangement.erase a, decide (a ∈ C.pathListArrangement.marked))
  have hf : Function.Injective f := by
    intro C D heq
    apply crossingScheme_pathListArrangement_injective
    apply PathListArrangement.eq_of_erase_of_absent a (haAbsent C) (haAbsent D)
      (congrArg Prod.fst heq)
    have hbit := congrArg Prod.snd heq
    change decide (a ∈ C.pathListArrangement.marked) =
      decide (a ∈ D.pathListArrangement.marked) at hbit
    simpa using (congrArg (fun b : Bool => b = true) hbit).to_iff
  have hsmall := finite_arrangements_and_card_le (I := I) (hX.sdiff (t := {a}))
  let _ := hsmall.1
  have hc := Nat.card_le_card_of_injective f hf
  have hb : Nat.card Bool = 2 := by simp [Nat.card_eq_fintype_card]
  rw [Nat.card_prod, hb] at hc
  have hi : Nat.card I = A₀.index := by
    simp [I, Nat.card_eq_fintype_card, Termination.index]
  have hsize : (S \ {a}).ncard = S.ncard - 1 := by
    exact Set.ncard_sdiff_singleton_of_mem haX
  have hpos : 0 < S.ncard := Set.ncard_pos hX |>.2 ⟨a, haX⟩
  have hn' : S.ncard = 1 ∨ S.ncard = 2 := by change S.ncard ≤ 2 at hn; omega
  have hbound := (Nat.mul_le_mul_right 2 hsmall.2)
  rw [hsize, hi] at hbound
  rcases hn' with hone | htwo
  · rw [hone] at hbound
    have hc2 : Nat.card (CrossingScheme G H H' A₀) ≤ 2 := hc.trans (by simpa using hbound)
    exact hc2.trans (le_max_left _ _)
  · rw [htwo] at hbound
    have hc2 : Nat.card (CrossingScheme G H H' A₀) ≤ (A₀.index + 2) * 2 :=
      hc.trans (by simpa using hbound)
    apply hc2.trans
    apply le_max_of_le_right
    change (A₀.index + 2) * 2 ≤ (S.ncard + A₀.index) ^ S.ncard
    rw [htwo]
    nlinarith

end GraphMinor.GM02
