module

public import GraphMinor.GM01.TreeDegrees
public import GraphMinor.GM09.Basic
import GraphMinor.GM16.SubcubicSubdivision
import GraphMinor.GM01.SubgraphIso
import GraphMinor.GM01.SubdivisionConnected
import GraphMinor.Minor.Basic

/-!
# Subdivisions representing the other tree minors

Graph Minors I, page 60, replaces each `Y_(γ−1)` minor in `X_i`
by a subdivision. Pass to the simple graph on its actual vertices,
extract its ordinary model, and apply the proved subcubic construction.
The selected subgraph is connected and still has the original tree
as a minor. This also covers `Y_0`, the single-vertex extension used
when `γ = 1`.
-/

public section

namespace GraphMinor.GM01

open Set Graph SimpleGraph Function GraphMinor.GM09

/-- The explicit `Y_ℓ` subdivision on page 60 of GM01, including its
retained tree minor. Edge-label nonemptiness is supplied in Part 3 by
the positive-height rooted binary-tree model in the root set. -/
theorem exists_forestTree_subdivision {α β : Type*} [Nonempty β] {G : Graph α β}
    (hVfin : V(G).Finite) (hEfin : E(G).Finite) (ℓ : ℕ)
    (h : IsIsoMinor (forestTreeGraph ℓ) G) :
    ∃ (N : Graph α β) (c : (forestTree ℓ).verts → α)
      (P : (forestTree ℓ).coe.edgeSet → Graph α β),
      N ≤ G ∧ Injective c ∧ V(N) = range c ∪ ⋃ e, V(P e) ∧ E(N) = ⋃ e, E(P e) ∧
      (∀ e : (forestTree ℓ).coe.edgeSet, ∃ a b, e.val = s(a,b) ∧
        (forestTree ℓ).coe.Adj a b ∧ IsGraphPathWithEnds N (P e) (c a) (c b) ∧
        V(P e) ∩ range c = {c a,c b}) ∧
      (∀ e f : (forestTree ℓ).coe.edgeSet, e ≠ f →
        Disjoint E(P e) E(P f) ∧ V(P e) ∩ V(P f) ⊆ range c) ∧
      GraphConnected N ∧ IsIsoMinor (forestTreeGraph ℓ) N := by
  let : Finite (forestTree ℓ).verts := (forestTree_vertices_finite ℓ).to_subtype
  have hSimple : IsIsoMinor (Graph.ofSimpleGraph (forestTree ℓ).coe) G :=
    (subgraphSimpleGraphIso (forestTree ℓ)).isIsoMinor_left h
  obtain ⟨ηv, ηe, hModel⟩ := exists_isMinorModel_of_isIsoMinor hVfin hEfin hSimple
  obtain ⟨N, c, P, hN, hc, _, hV, hE, hPaths, hInter, ηv', hModel'⟩ :=
    GraphMinor.GM16.exists_subcubic_subdivision_with_minor hModel (forestTree_coe_neighborSet_ncard_le_three ℓ)
  have hConn : GraphConnected N := subdivision_connected (forestTree_connected ℓ).coe
    ⟨none, forestTree_centre_mem ℓ⟩ N c P hV (fun e ↦ by
      obtain ⟨a, b, he, hab, hP, _, _⟩ := hPaths e
      exact ⟨a, b, he, hab, hP⟩)
  have hRetSimple : IsIsoMinor (Graph.ofSimpleGraph (forestTree ℓ).coe) N :=
    isIsoMinor_of_isMinorModel _ N (by exact Set.finite_univ) (Set.toFinite _)
      (hVfin.subset hN.vertexSet_mono) (hEfin.subset hN.edgeSet_mono) ηv' ηe hModel'
  have hRet := (subgraphSimpleGraphIso (forestTree ℓ)).symm.isIsoMinor_left hRetSimple
  refine ⟨N, c, P, hN, hc, hV, hE, ?_, hInter, hConn, hRet⟩
  intro e
  obtain ⟨a, b, he, hab, hP, _, hRange⟩ := hPaths e
  exact ⟨a, b, he, hab, hP, hRange⟩

end GraphMinor.GM01
