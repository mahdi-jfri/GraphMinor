module

public import GraphMinor.GM10.Section7ModelSeparation
public import GraphMinor.GM10.Section7
import GraphMinor.GM10.TangleLemmas

/-!
# The canonical tangle read through a grid model

We use the edge representatives of the model to write the inducing formula
of Graph Minors X (6.1). A small-order separation pulls back to the grid
without increasing its order. The column rank condition rules out a row
on the tangle's small side. This identifies the induced tangle with the
truncation, rather than merely finding a grid minor.
-/

@[expose] public section

namespace GraphMinor.GM10

open Hypergraph RST94 Set Graph

universe u v

/-- The formula of Graph Minors X (6.1), page 170, with the edges of the grid
named by their model representatives. The left edge set of a canonical grid
separation must have exactly the representatives on the original left side.
This definition carries no claim that the formula is a tangle. -/
def gridModelInducedTangle {α : Type u} {β : Type v} (G : Hypergraph α β)
    (g : ℕ) (ηe : Sym2 (Fin g × Fin g) → β) :
    Set (Hypergraph α β × Hypergraph α β) :=
  {p | G.IsSeparation p.1 p.2 ∧ separationOrder p.1 p.2 < g ∧
    ∃ q ∈ gridTangle g, ηe '' q.1.edgeSet =
      p.1.edgeSet ∩ ηe '' (gridHypergraph g).edgeSet}

/-- The separation obtained from a member of the original tangle belongs to
the canonical grid tangle. Its order is bounded by the separator injection,
and its left edge set contains no row by the column rank condition. -/
theorem exists_canonical_grid_separation {α : Type u} {β : Type v}
    {G : Graph α β} {hV : V(G).Finite} {hE : E(G).Finite}
    {T : Set (Hypergraph α β × Hypergraph α β)} {θ g : ℕ}
    (hT : IsTangle (Hypergraph.ofGraph G hV hE) θ T)
    {W : ℕ → ℕ → Set α}
    (hW : IsGrid (Hypergraph.ofGraph G hV hE) T θ g W) (hg : 2 ≤ g)
    {ηe : Sym2 (Fin g × Fin g) → β}
    (hm : IsMinorModel (GM01.gridGraph g) G (fun z => W z.1 z.2) ηe)
    (hηe : ∀ e ∈ E(GM01.gridGraph g), ∃ u v x y,
      e = s(u, v) ∧ u ≠ v ∧ x ∈ W u.1 u.2 ∧ y ∈ W v.1 v.2 ∧ G.IsLink (ηe e) x y)
    {A B : Hypergraph α β} (hAB : (A, B) ∈ T) (hord : separationOrder A B < g) :
    ∃ A' B', (A', B') ∈ gridTangle g ∧
      A'.edgeSet = (gridHypergraph g).edgeSet ∩ ηe ⁻¹' A.edgeSet := by
  obtain ⟨A', B', hs, ho, he⟩ := exists_grid_model_separation hW hm (hT.isSeparation hAB)
  refine ⟨A', B', ⟨hs, ho.trans_lt hord, ?_, ?_⟩, he⟩
  · have hbound : edgeBoundary (gridHypergraph g) A'.edgeSet ⊆ (A' ∩ B').vertexSet := by
      rintro z ⟨hz, ⟨e, heA, hez⟩, ⟨f, ⟨hf, hfA⟩, hfz⟩⟩
      have hfB : f ∈ B'.edgeSet := (hs.edgeSet_union.symm ▸ hf).resolve_left hfA
      exact ⟨A'.vertex_mem_of_inc ((inc_iff_of_le hs.left_le heA).2 hez),
        B'.vertex_mem_of_inc ((inc_iff_of_le hs.right_le hfB).2 hfz)⟩
    exact (ncard_le_ncard hbound (A' ∩ B').vertexSet_finite).trans_lt (ho.trans_lt hord)
  · intro i hi
    apply no_row hT hW hg hηe hAB hord i
    rintro f ⟨e, heRow, rfl⟩
    exact (show e ∈ (gridHypergraph g).edgeSet ∩ ηe ⁻¹' A.edgeSet from he ▸ hi heRow).2

/-- The canonical tangle of a grid model with the column rank condition induces
exactly the truncation of the original tangle. No domination assertion is
assumed: it is derived using the two tangle orientations. -/
theorem truncation_eq_gridModelInducedTangle {α : Type u} {β : Type v}
    {G : Graph α β} {hV : V(G).Finite} {hE : E(G).Finite}
    {T : Set (Hypergraph α β × Hypergraph α β)} {θ g : ℕ}
    (hT : IsTangle (Hypergraph.ofGraph G hV hE) θ T)
    {W : ℕ → ℕ → Set α}
    (hW : IsGrid (Hypergraph.ofGraph G hV hE) T θ g W)
    (hg : 2 ≤ g) (hgle : g ≤ θ)
    {ηe : Sym2 (Fin g × Fin g) → β}
    (hm : IsMinorModel (GM01.gridGraph g) G (fun z => W z.1 z.2) ηe)
    (hηe : ∀ e ∈ E(GM01.gridGraph g), ∃ u v x y,
      e = s(u, v) ∧ u ≠ v ∧ x ∈ W u.1 u.2 ∧ y ∈ W v.1 v.2 ∧ G.IsLink (ηe e) x y) :
    truncation T g = gridModelInducedTangle (Hypergraph.ofGraph G hV hE) g ηe := by
  ext ⟨A, B⟩
  constructor
  · rintro ⟨hAB, hord⟩
    obtain ⟨A', B', hc, he⟩ := exists_canonical_grid_separation hT hW hg hm hηe hAB hord
    refine ⟨hT.isSeparation hAB, hord, (A', B'), hc, ?_⟩
    rw [he]
    ext f
    constructor
    · rintro ⟨e, ⟨he, heA⟩, rfl⟩
      exact ⟨heA, e, he, rfl⟩
    · rintro ⟨hfA, e, he, rfl⟩
      exact ⟨e, ⟨he, hfA⟩, rfl⟩
  · rintro ⟨hs, hord, ⟨A', B'⟩, hc, he⟩
    refine ⟨?_, hord⟩
    rcases hT.axiom1 hs (hord.trans_le hgle) with hAB | hBA
    · exact hAB
    · exfalso
      obtain ⟨L, R, hL, hLE⟩ := exists_canonical_grid_separation hT hW hg hm hηe hBA
        (by rwa [separationOrder_comm])
      apply theorem_2_3_proof (theorem_7_3_proof hg) hg hc hL hc
      apply Subset.antisymm
      · exact union_subset (union_subset hc.1.left_le.edgeSet_subset hL.1.left_le.edgeSet_subset)
          hc.1.left_le.edgeSet_subset
      · intro e heG
        have hfG : ηe e ∈ (Hypergraph.ofGraph G hV hE).edgeSet := hm.edge_mem e heG
        rcases hs.edgeSet_union.symm ▸ hfG with hfA | hfB
        · have hf : ηe e ∈ ηe '' A'.edgeSet := he.symm ▸ ⟨hfA, e, heG, rfl⟩
          obtain ⟨f, hf, hfe⟩ := hf
          have hfe' := hm.edge_injOn (hc.1.left_le.edgeSet_subset hf) heG hfe
          exact Or.inl (Or.inl (hfe' ▸ hf))
        · exact Or.inl (Or.inr (hLE.symm ▸ ⟨heG, hfB⟩))

end GraphMinor.GM10
