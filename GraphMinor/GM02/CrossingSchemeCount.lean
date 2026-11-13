module

public import GraphMinor.GM02.CrossingScheme
import GraphMinor.GM02.CrossingSchemeFinite
import GraphMinor.GM02.CrossingSchemeEncoding
import GraphMinor.GM02.SmallTerminalSeparator
import GraphMinor.GM02.SmallNonterminalSeparator

/-!
# The number of crossing schemes

Graph Minors II (2.8) leaves its counting proof to the reader. Encode each
scheme by disjoint ordered lists of internal separator vertices and marks
on unused or terminal separator vertices. Erasing one vertex loses one
insertion slot. The product of slot counts gives the printed bound for
three or more separator vertices. On at most two vertices, fixed path
parities and the marked-terminal case give the bound directly.
-/

public section
namespace GraphMinor.GM02
open Graph Set Classical
universe u v

/-- Graph Minors II, (2.8), page 315:
"The number of different crossing schemes for $\\mathscr{A}_0$ with respect
to $(H, H')$ is at most"
$\\max(2, (|X| + k)^{|X|})$.

The proof supplies the enumeration omitted in the paper. Finiteness is
included explicitly, so the natural cardinal bound cannot hold merely
because an infinite type has natural cardinal zero. -/
theorem theorem_2_8_proof {α : Type u} {β : Type v} {G H H' : Graph α β}
    (hV : (V(G)).Finite) (hsep : IsSeparation G H H') (A₀ : Termination V(G)) :
    Finite (CrossingScheme G H H' A₀) ∧
      Nat.card (CrossingScheme G H H' A₀) ≤
        max 2 (((V(H) ∩ V(H')).ncard + A₀.index) ^ (V(H) ∩ V(H')).ncard) := by
  have hX : (V(H) ∩ V(H')).Finite :=
    hV.subset (Set.inter_subset_left.trans hsep.1.vertexSet_mono)
  refine ⟨finite_crossingSchemes A₀ hX, ?_⟩
  by_cases hn : 3 ≤ (V(H) ∩ V(H')).ncard
  · exact (card_crossingSchemes_le_pow_of_three_le A₀ hX hn).trans (le_max_right _ _)
  · have hn' : (V(H) ∩ V(H')).ncard ≤ 2 := by omega
    by_cases ht : ∃ a ∈ V(H) ∩ V(H'), a ∈ A₀.support
    · obtain ⟨a, haX, ha₀⟩ := ht
      exact card_crossingSchemes_le_of_small_terminal A₀ hX hn' haX ha₀
    · have hno : Disjoint (V(H) ∩ V(H')) A₀.support :=
        Set.disjoint_left.2 (fun a haX ha₀ => ht ⟨a, haX, ha₀⟩)
      exact card_crossingSchemes_le_of_small_nonterminal A₀ hX hn' hno

end GraphMinor.GM02
