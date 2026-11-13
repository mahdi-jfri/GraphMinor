module

public import GraphMinor.GM10.Section4K4
import GraphMinor.GM10.Section4Nonsimple
import GraphMinor.GM10.Section4SimpleReduction
import GraphMinor.GM10.DiracLowValency

/-!
# Graph Minors X, (4.2): small branch-width

The width-two characterization is proved by the paper's induction on
size. Loops and parallel edges are removed first. In the remaining
simple graph, the proved external low-valency input gives a nonisolated
vertex incident with at most two edges. The local reduction decreases
the number of edges, and the restoration lemmas preserve the bound two.
The three small-width characterizations are then assembled as (4.2).
-/

public section

namespace GraphMinor.GM10

open Graph Hypergraph SimpleGraph Classical

universe u v

/-- The reverse implication of Graph Minors X, (4.2)(iii), page 165,
proved by induction on the number of edges with the low-valency input
proved separately. -/
theorem branchWidth_le_two_of_not_isIsoMinor_completeGraphGraph_four
    {α : Type u} {β : Type v} (G : Graph α β)
    (hV : V(G).Finite) (hE : E(G).Finite)
    (hno : ¬ IsIsoMinor (completeGraphGraph 4) G) :
    branchWidth (Hypergraph.ofGraph G hV hE) ≤ 2 := by
  suffices ∀ n, ∀ (G : Graph α β) (hV : V(G).Finite) (hE : E(G).Finite),
      ¬ IsIsoMinor (completeGraphGraph 4) G → E(G).ncard = n →
      branchWidth (Hypergraph.ofGraph G hV hE) ≤ 2 by
    exact this _ G hV hE hno rfl
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro G hV hE hno hn
    by_cases hsmall : E(G).ncard ≤ 1
    · rw [branchWidth_eq_zero_of_ncard_edgeSet_le_one hsmall]
      omega
    have hcard : 2 ≤ E(G).ncard := by omega
    have hred : ∃ (H : Graph α β) (hVH : V(H).Finite) (hEH : E(H).Finite),
        IsIsoMinor H G ∧ E(H).ncard < E(G).ncard ∧
          (branchWidth (Hypergraph.ofGraph H hVH hEH) ≤ 2 →
            branchWidth (Hypergraph.ofGraph G hV hE) ≤ 2) := by
      by_cases hs : G.Simple
      · let : G.Simple := hs
        let A := {x : α // ∃ e, G.Inc e x}
        have hactive : {x : α | ∃ e, G.Inc e x}.Finite :=
          hV.subset (fun x ⟨e, he⟩ ↦ he.vertex_mem)
        let : Fintype A := hactive.fintype
        have hnonempty : Nonempty A := by
          have hne : E(G).Nonempty := (Set.ncard_pos hE).1 (by omega)
          obtain ⟨d, hd⟩ := hne
          obtain ⟨x, y, hxy⟩ := Graph.exists_isLink_of_mem_edgeSet hd
          exact ⟨⟨x, d, hxy.inc_left⟩⟩
        let : Nonempty A := hnonempty
        have hnoS : ¬ IsIsoMinor (completeGraphGraph 4)
            (Graph.ofSimpleGraph (nonisolatedSimpleGraph G)) := by
          intro hm
          exact hno (hm.trans (nonisolatedSimpleGraph_isIsoMinor G hV))
        obtain ⟨x, hx⟩ := exists_small_neighbor_set_of_not_completeGraphGraph_four_minor
          (nonisolatedSimpleGraph G) hnoS
        exact exists_smaller_minor_at_small_neighbor_set G hV hE hcard x hx
      · exact exists_smaller_minor_of_not_simple G hV hE hcard hs
    obtain ⟨H, hVH, hEH, hHG, hlt, hrestore⟩ := hred
    have hnoH : ¬ IsIsoMinor (completeGraphGraph 4) H :=
      fun hm ↦ hno (hm.trans hHG)
    exact hrestore (ih E(H).ncard (by omega) H hVH hEH hnoH rfl)

/-- Graph Minors X, (4.2)(iii), page 165: a finite graph has branch-width
at most two exactly when it has no minor isomorphic to `K₄`. -/
theorem branchWidth_le_two_iff_not_isIsoMinor_completeGraphGraph_four
    {α : Type u} {β : Type v} (G : Graph α β)
    (hV : V(G).Finite) (hE : E(G).Finite) :
    branchWidth (Hypergraph.ofGraph G hV hE) ≤ 2 ↔
      ¬ IsIsoMinor (completeGraphGraph 4) G :=
  ⟨not_isIsoMinor_completeGraphGraph_four_of_branchWidth_le_two hV hE,
    branchWidth_le_two_of_not_isIsoMinor_completeGraphGraph_four G hV hE⟩

/-- Graph Minors X, (4.2), page 165:
"(4.2) *A graph $G$ has branch-width*
(i) *$0$ if and only if every component of $G$ has $\le 1$ edge*
(ii) *$\le 1$ if and only if every component of $G$ has $\le 1$ vertex of valency $\ge 2$*
(iii) *$\le 2$ if and only if $G$ has no $K_4$ minor.*"
The loop case in the printed proof of (ii) is corrected by the leaf-cut
argument documented in `branchWidth_le_one_iff_components_le_one_deg_ge_two`. -/
theorem theorem_4_2_proof {α : Type u} {β : Type v} (G : Graph α β)
    (hV : V(G).Finite) (hE : E(G).Finite) :
    (branchWidth (Hypergraph.ofGraph G hV hE) = 0 ↔
      ∀ C, IsConnectedComponent (Hypergraph.ofGraph G hV hE) C → C.edgeSet.ncard ≤ 1) ∧
    (branchWidth (Hypergraph.ofGraph G hV hE) ≤ 1 ↔
      ∀ C, IsConnectedComponent (Hypergraph.ofGraph G hV hE) C →
        {x ∈ C.vertexSet | 2 ≤ {e ∈ (Hypergraph.ofGraph G hV hE).edgeSet |
          (Hypergraph.ofGraph G hV hE).Inc e x}.ncard}.ncard ≤ 1) ∧
    (branchWidth (Hypergraph.ofGraph G hV hE) ≤ 2 ↔
      ¬ IsIsoMinor (completeGraphGraph 4) G) :=
  ⟨branchWidth_eq_zero_iff_components_le_one_edge hV hE,
    branchWidth_le_one_iff_components_le_one_deg_ge_two hV hE,
    branchWidth_le_two_iff_not_isIsoMinor_completeGraphGraph_four G hV hE⟩

end GraphMinor.GM10
