module

public import GraphMinor.GM02.TreeWidthVertices

/-!
# Renaming the vertices of simple recursive instances

After restricting a child instance to its actual vertices, a bijection
numbers those vertices. Map decomposition bags and prescribed paths by
the same bijection. Bag sizes and feasibility do not change, so a
recursive answer on the numbered instance applies to the original child.
-/

public section
namespace GraphMinor.GM02
open Graph Set SimpleGraph Classical
universe u u' t

/-- Rename every bag along a simple graph isomorphism. -/
theorem IsTreeDecomposition.mapSimpleIso {α : Type u} {α' : Type u'} {ι : Type t}
    {F : SimpleGraph α} {H : SimpleGraph α'} {T : SimpleGraph ι} {B : ι → Set α}
    (hD : IsTreeDecomposition (Graph.ofSimpleGraph F) T B) (φ : F ≃g H) :
    IsTreeDecomposition (Graph.ofSimpleGraph H) T (fun i => φ '' B i) := by
  refine ⟨hD.isTree, ?_, ?_, ?_⟩
  · ext a
    constructor
    · intro _
      trivial
    · intro _
      have ha : φ.symm a ∈ ⋃ i, B i := by rw [hD.iUnion_eq]; trivial
      obtain ⟨i, hi⟩ := Set.mem_iUnion.1 ha
      exact Set.mem_iUnion.2 ⟨i, ⟨φ.symm a, hi, φ.apply_symm_apply a⟩⟩
  · intro e a b he
    have hab := (Graph.ofSimpleGraph_adj_iff a b).1 ⟨e, he⟩
    have hf : F.Adj (φ.symm a) (φ.symm b) := (φ.symm.map_rel_iff).2 hab
    have hlink : (Graph.ofSimpleGraph F).IsLink s(φ.symm a, φ.symm b) (φ.symm a) (φ.symm b) :=
      ⟨rfl, (SimpleGraph.mem_edgeSet _).2 hf⟩
    obtain ⟨i, hi, hj⟩ := hD.edge_mem hlink
    exact ⟨i, ⟨φ.symm a, hi, φ.apply_symm_apply a⟩, ⟨φ.symm b, hj, φ.apply_symm_apply b⟩⟩
  · intro i j k hp a ha
    obtain ⟨b, hb, rfl⟩ := ha.1
    obtain ⟨c, hc, hcb⟩ := ha.2
    have he : c = b := φ.injective hcb
    exact ⟨b, hD.inter_subset hp ⟨hb, he ▸ hc⟩, rfl⟩

/-- Numbering vertices preserves every width bound. -/
theorem treeWidthLE_simpleIso_iff {α : Type u} {α' : Type u'}
    {F : SimpleGraph α} {H : SimpleGraph α'} (φ : F ≃g H) (w : ℕ) :
    TreeWidthLE (Graph.ofSimpleGraph F) w ↔ TreeWidthLE (Graph.ofSimpleGraph H) w := by
  have transfer {V : Type u} {W : Type u'} {F : SimpleGraph V} {H : SimpleGraph W}
      (φ : F ≃g H) (hw : TreeWidthLE (Graph.ofSimpleGraph F) w) :
      TreeWidthLE (Graph.ofSimpleGraph H) w := by
    obtain ⟨ι, hι, T, B, hD, hwidth⟩ := hw
    refine ⟨ι, hι, T, fun i => φ '' B i, hD.mapSimpleIso φ, ?_⟩
    intro i
    rw [Set.ncard_image_of_injective _ φ.injective]
    exact hwidth i
  constructor
  · exact transfer φ
  · intro hw
    obtain ⟨ι, hι, T, B, hD, hwidth⟩ := hw
    refine ⟨ι, hι, T, fun i => φ.symm '' B i, hD.mapSimpleIso φ.symm, ?_⟩
    intro i
    rw [Set.ncard_image_of_injective _ φ.symm.injective]
    exact hwidth i

/-- Numbering the prescribed endpoints by the graph isomorphism preserves
feasibility of the simple terminated instance. -/
theorem feasible_simpleIso_iff {α : Type u} {α' : Type u'}
    {F : SimpleGraph α} {H : SimpleGraph α'} {S : Set α}
    (A : Termination S) (φ : F ≃g H) :
    (A.mapEmbedding ⟨φ, φ.injective⟩).Feasible (Graph.ofSimpleGraph H) ↔
      A.Feasible (Graph.ofSimpleGraph F) := by
  let ψ : pathGraph (Graph.ofSimpleGraph F) ≃g pathGraph (Graph.ofSimpleGraph H) :=
    { toEquiv := φ.toEquiv
      map_rel_iff' := by
        rw [pathGraph_ofSimpleGraph, pathGraph_ofSimpleGraph]
        exact φ.map_rel_iff }
  exact feasible_mapIso_iff A _ _ ψ

end GraphMinor.GM02
