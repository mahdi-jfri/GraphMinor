module

public import GraphMinor.GM05.Statements
import GraphMinor.GM05.IntersectionSurfacePacking
import GraphMinor.GM05.SurfaceExpansionFamilies
import GraphMinor.GM05.ExpansionMultiplicity
import GraphMinor.GM05.ULiftExpansions
import GraphMinor.GM05.EmptyDrawingPlanar

/-!
# Nonplanar graphs do not have the Erdős–Pósa property

This proves GM V, (8.14), page 113. Choose the closed surface on
which every drawn graph has no two disjoint expansions of the fixed
nonplanar graph. For a proposed transversal bound `m`, construct
`2m+1` specified expansions of vertex multiplicity at most two.
Relabel the finite host into the required universes. A transversal
of at most `m` vertices misses one specified expansion, contradicting
the Erdős–Pósa property at packing size two.
-/

public section
namespace GraphMinor.GM05
open Set Surface Graph
universe u v u' v'

/-- Graph Minors V, (8.14), page 113:
"$H$ does not have the Erdös–Pósa property."
The graph `H` is finite and nonplanar, as fixed before (8.12). -/
theorem theorem_8_14_proof : Theorem814Statement.{u,v,u',v'} := by
  classical
  intro α β H hVH hEH hnp hEP
  obtain ⟨m,hbound⟩ := hEP 2
  obtain ⟨S,τ,hS,hΓ,hno⟩ := exists_surface_excluding_two_expansions H hVH hEH hnp
  let : TopologicalSpace S := τ
  obtain ⟨Γ⟩ := hΓ
  have hUne : Γ.drawing.U.Nonempty := by
    by_contra hh
    exact hnp (isPlanar_of_empty_drawing_support Γ (not_nonempty_iff_eq_empty.mp hh))
  let : Nonempty S := ⟨hUne.choose⟩
  obtain ⟨D,A,hA,hmult⟩ := exists_surface_expansion_family hS Γ (2*m+1)
  let G : Graph (ULift.{u} S) (ULift.{v} (Set S)) := uliftGraph.{0,0,u,v} D.toGraph
  have hGfinite : V(G).Finite ∧ E(G).Finite := uliftGraph_finite.{0,0,u,v}
    D.toGraph D.finite_V D.finite_edges
  have hex : ∀ i, ∃ B : Graph (ULift.{u} S) (ULift.{v} (Set S)),
      IsHExpansion H G B ∧ ∀ x ∈ V(B), x.down ∈ V(A i) :=
    fun i ↦ exists_ulift_expansion (hA i)
  choose B hB hBA using hex
  have hmult' : ∀ x : ULift.{u} S, {i | x ∈ V(B i)}.ncard ≤ 2 := by
    intro x
    have hsub : {i | x ∈ V(B i)} ⊆ {i | x.down ∈ V(A i)} := fun i hi ↦ hBA i x hi
    exact (ncard_le_ncard hsub (toFinite _)).trans (hmult x.down)
  rcases hbound G hGfinite.1 hGfinite.2 with hp | ⟨X,hX,hcard,hhit⟩
  · have hsmall : HasDisjointExpansions H D.toGraph 2 :=
      disjointExpansions_of_ulift hVH hEH D.finite_V D.finite_edges hp
    exact hno D hsmall
  · exact lemma_8_14_no_small_transversal m B hB hmult' (hGfinite.1.subset hX) hcard hhit

end GraphMinor.GM05
