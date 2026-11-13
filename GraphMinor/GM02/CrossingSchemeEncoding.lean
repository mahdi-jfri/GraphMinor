module

public import GraphMinor.GM02.CrossingPathLists
public import GraphMinor.GM02.CrossingSchemeFinite
import GraphMinor.GM02.RecoverCrossingPaths
import GraphMinor.GM02.RecoverCrossingSupports
import GraphMinor.GM02.MatchingInPaths
import GraphMinor.GM02.ArrangementCount

/-!
# Injecting crossing schemes into path-list arrangements

The lists recover the graph of all path pieces. The marks recover both
supports and both reserved sets. A matching inside disjoint paths is
uniquely determined by its support, so the terminations are recovered too.
The arrangement count then proves II (2.8) when the separator has at least
three vertices. The smaller cases use the parity constraints separately.
-/

public section
namespace GraphMinor.GM02
open Graph SimpleGraph Set Classical
universe u v

private theorem left_graph_le {α : Type u} {β : Type v}
    {G H H' : Graph α β} {A₀ : Termination V(G)} (C : CrossingScheme G H H' A₀) :
    C.left.pairGraph ≤ C.pairGraph := by
  intro a b hab
  apply (SimpleGraph.fromEdgeSet_adj _).2
  exact ⟨Finset.mem_union_left _ (C.left.pairGraph_adj_iff.1 hab), hab.ne⟩

private theorem right_graph_le {α : Type u} {β : Type v}
    {G H H' : Graph α β} {A₀ : Termination V(G)} (C : CrossingScheme G H H' A₀) :
    C.right.pairGraph ≤ C.pairGraph := by
  intro a b hab
  apply (SimpleGraph.fromEdgeSet_adj _).2
  exact ⟨Finset.mem_union_right _ (C.right.pairGraph_adj_iff.1 hab), hab.ne⟩

private theorem path_lists_cover {α : Type u} {β : Type v}
    {G H H' : Graph α β} {A₀ : Termination V(G)} (C : CrossingScheme G H H' A₀) :
    ∀ a b, C.pairGraph.Adj a b →
      ∃ p, (listEdgeGraph (C.pairPath p).support).Adj a b := by
  intro a b hab
  obtain ⟨p, hp⟩ := C.path_union.choose_spec.2.2.2 s(a, b)
    ((SimpleGraph.mem_edgeSet _).2 hab)
  change s(a, b) ∈ (C.pairPath p).edges at hp
  rw [SimpleGraph.Walk.edges_eq_zipWith_support] at hp
  exact ⟨p, (SimpleGraph.fromEdgeSet_adj _).2 ⟨hp, hab.ne⟩⟩

/-- The path-list encoding is injective on crossing schemes. All four
parts of the scheme are recovered from the lists and marks. -/
theorem crossingScheme_pathListArrangement_injective {α : Type u} {β : Type v}
    {G H H' : Graph α β} {A₀ : Termination V(G)} :
    Function.Injective (CrossingScheme.pathListArrangement (G := G) (H := H) (H' := H')
      (A₀ := A₀)) := by
  intro C D h
  have hpaths := congrArg PathListArrangement.paths h
  have hF := CrossingScheme.pairGraph_eq_of_lists hpaths
  have hleft := CrossingScheme.left_support_eq_of_encoding h
  have hright := CrossingScheme.right_support_eq_of_encoding h
  have hleftD : D.left.pairGraph ≤ C.pairGraph := hF ▸ left_graph_le D
  have hrightD : D.right.pairGraph ≤ C.pairGraph := hF ▸ right_graph_le D
  have hL : C.left = D.left := Termination.eq_of_support_in_paths C.left D.left
    (fun p => (C.pairPath p).support) (fun p => (C.pairPath_isPath p).support_nodup)
    (fun p q hpq => C.pairPath_disjoint p q hpq) (path_lists_cover C)
    (left_graph_le C) hleftD hleft
  have hR : C.right = D.right := Termination.eq_of_support_in_paths C.right D.right
    (fun p => (C.pairPath p).support) (fun p => (C.pairPath_isPath p).support_nodup)
    (fun p q hpq => C.pairPath_disjoint p q hpq) (path_lists_cover C)
    (right_graph_le C) hrightD hright
  have hz := CrossingScheme.reserved_eq_of_encoding h
  exact CrossingScheme.ext_data hL hR hz.1 hz.2

/-- The numerical bound in II (2.8) for a separator of at least three
vertices, from the insertion count for its path-list encoding. -/
theorem card_crossingSchemes_le_pow_of_three_le {α : Type u} {β : Type v}
    {G H H' : Graph α β} (A₀ : Termination V(G))
    (hX : (V(H) ∩ V(H')).Finite) (hn : 3 ≤ (V(H) ∩ V(H')).ncard) :
    Nat.card (CrossingScheme G H H' A₀) ≤
      ((V(H) ∩ V(H')).ncard + A₀.index) ^ (V(H) ∩ V(H')).ncard := by
  let _ : Finite (PathListArrangement (V(H) ∩ V(H')) {p // p ∈ A₀.pairs}) :=
    (finite_arrangements_and_card_le (I := {p // p ∈ A₀.pairs}) hX).1
  have hi : Nat.card {p // p ∈ A₀.pairs} = A₀.index := by
    simp [Nat.card_eq_fintype_card, Termination.index]
  have hcard := Nat.card_le_card_of_injective CrossingScheme.pathListArrangement
    (crossingScheme_pathListArrangement_injective (G := G) (H := H) (H' := H') (A₀ := A₀))
  have hb := card_arrangements_le_pow (I := {p // p ∈ A₀.pairs}) hX hn
  rw [hi, Nat.add_comm] at hb
  exact hcard.trans hb

end GraphMinor.GM02
