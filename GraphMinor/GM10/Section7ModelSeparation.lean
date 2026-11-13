module

public import GraphMinor.RST94.Theorem23
public import GraphMinor.GM10.BranchWidth

/-!
# Separations read through a grid model

A vertex in the edge boundary of the pulled-back edge set has its branch set
meeting both sides of the original separation. Connectivity gives a vertex of
the original separator in that branch set. Disjoint branch sets give distinct
separator vertices, which bounds the order of the pulled-back separation.
-/

public section

namespace GraphMinor.GM10

open Hypergraph RST94 Set Graph

universe u v

/-- The edge boundary of a cut read through a grid model has no more vertices
than the original separator. Each boundary branch set supplies a distinct
vertex of that separator. -/
theorem grid_model_boundary_le {α : Type u} {β : Type v}
    {G : Graph α β} {hV : V(G).Finite} {hE : E(G).Finite}
    {T : Set (Hypergraph α β × Hypergraph α β)} {θ g : ℕ}
    {W : ℕ → ℕ → Set α}
    (hW : IsGrid (Hypergraph.ofGraph G hV hE) T θ g W)
    {ηe : Sym2 (Fin g × Fin g) → β}
    (hm : IsMinorModel (GM01.gridGraph g) G (fun z => W z.1 z.2) ηe)
    {A B : Hypergraph α β} (hs : (Hypergraph.ofGraph G hV hE).IsSeparation A B) :
    (branchEdgeBoundary (gridHypergraph g) (ηe ⁻¹' A.edgeSet)).ncard ≤
      separationOrder A B := by
  let D := branchEdgeBoundary (gridHypergraph g) (ηe ⁻¹' A.edgeSet)
  have hex : ∀ z ∈ D, ∃ x ∈ W z.1 z.2, x ∈ (A ∩ B).vertexSet := by
    rintro z ⟨hz, ⟨e, heA, hez⟩, ⟨f, ⟨hf, hfA⟩, hfz⟩⟩
    have he : e ∈ E(GM01.gridGraph g) := (gridHypergraph g).edge_mem_of_inc hez
    have hz' : z ∈ V(GM01.gridGraph g) := hz
    obtain ⟨x, hx, hxe⟩ := (hm.inc_iff z hz' e he).1 hez
    obtain ⟨y, hy, hyf⟩ := (hm.inc_iff z hz' f hf).1 hfz
    have hxA : x ∈ A.vertexSet := A.vertex_mem_of_inc
      ((inc_iff_of_le hs.left_le heA).2 hxe)
    have hfB : ηe f ∈ B.edgeSet :=
      (hs.edgeSet_union.symm ▸ (show ηe f ∈ (Hypergraph.ofGraph G hV hE).edgeSet from hm.edge_mem f hf)).resolve_left hfA
    have hyB : y ∈ B.vertexSet := B.vertex_mem_of_inc
      ((inc_iff_of_le hs.right_le hfB).2 hyf)
    exact (hW.conn z.1 z.1.2 z.2 z.2.2).meets_sep hs hx hy hxA hyB
  let f : D → (A ∩ B).vertexSet := fun z =>
    ⟨(hex z z.2).choose, (hex z z.2).choose_spec.2⟩
  have hf : Function.Injective f := by
    intro z z' heq
    apply Subtype.ext
    by_contra hne
    have hd := hm.vertex_disjoint z.1 z.2.1 z'.1 z'.2.1 hne
    have hx := (hex z z.2).choose_spec.1
    have hx' := (hex z' z'.2).choose_spec.1
    have heq' : (hex z z.2).choose = (hex z' z'.2).choose := congrArg Subtype.val heq
    exact disjoint_left.1 hd hx (heq' ▸ hx')
  change D.ncard ≤ (A ∩ B).vertexSet.ncard
  rw [← Nat.card_coe_set_eq, ← Nat.card_coe_set_eq]
  have : Finite (A ∩ B).vertexSet := (A ∩ B).vertexSet_finite
  exact Nat.card_le_card_of_injective f hf

/-- A separation of the original graph gives a separation of the labelled grid
with the pulled-back edge set on its left, and with no larger order. -/
theorem exists_grid_model_separation {α : Type u} {β : Type v}
    {G : Graph α β} {hV : V(G).Finite} {hE : E(G).Finite}
    {T : Set (Hypergraph α β × Hypergraph α β)} {θ g : ℕ}
    {W : ℕ → ℕ → Set α}
    (hW : IsGrid (Hypergraph.ofGraph G hV hE) T θ g W)
    {ηe : Sym2 (Fin g × Fin g) → β}
    (hm : IsMinorModel (GM01.gridGraph g) G (fun z => W z.1 z.2) ηe)
    {A B : Hypergraph α β} (hs : (Hypergraph.ofGraph G hV hE).IsSeparation A B) :
    ∃ A' B', (gridHypergraph g).IsSeparation A' B' ∧
      separationOrder A' B' ≤ separationOrder A B ∧
      A'.edgeSet = (gridHypergraph g).edgeSet ∩ ηe ⁻¹' A.edgeSet := by
  let X := (gridHypergraph g).edgeSet ∩ ηe ⁻¹' A.edgeSet
  refine ⟨sepLeft (gridHypergraph g) X, sepRight (gridHypergraph g) X,
    isSeparation_sepLeft_sepRight _ _, ?_, ?_⟩
  · rw [separationOrder_sepLeft_sepRight _ inter_subset_left]
    have heq : branchEdgeBoundary (gridHypergraph g) X =
        branchEdgeBoundary (gridHypergraph g) (ηe ⁻¹' A.edgeSet) := by
      ext z
      simp only [branchEdgeBoundary, X, mem_sep_iff, mem_inter_iff, mem_sdiff,
        not_and]
      constructor
      · rintro ⟨hz, ⟨e, ⟨he, heA⟩, hez⟩, ⟨f, ⟨hf, hfA⟩, hfz⟩⟩
        exact ⟨hz, ⟨e, heA, hez⟩, ⟨f, ⟨hf, hfA hf⟩, hfz⟩⟩
      · rintro ⟨hz, ⟨e, heA, hez⟩, ⟨f, ⟨hf, hfA⟩, hfz⟩⟩
        exact ⟨hz, ⟨e, ⟨(gridHypergraph g).edge_mem_of_inc hez, heA⟩, hez⟩,
          ⟨f, ⟨hf, fun _ => hfA⟩, hfz⟩⟩
    rw [heq]
    exact grid_model_boundary_le hW hm hs
  · change X ∩ (gridHypergraph g).edgeSet = X
    exact inter_eq_self_of_subset_left inter_subset_left

end GraphMinor.GM10
