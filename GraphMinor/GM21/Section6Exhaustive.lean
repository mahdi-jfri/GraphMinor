module

public import GraphMinor.GM21.Defs
import GraphMinor.GM21.LinkageLemmas
import GraphMinor.GM21.Section7Three

/-!
# Graph Minors XXI, Section 6: exhaustive linkages

Graph Minors XXI, Section 6 (page 24 of the preprint): "If $L$ is exhaustive then it follows
that $\Gamma$ is a forest and every vertex of $\Gamma$ not in $bd(\Sigma)$ has degree 2 in
$\Gamma$."

We prove both parts. `Γ` is a subgraph of the linkage `L`, so it is a linkage of `G`
(`IsExhaustiveLinkage.isLinkage`): every component is a path. A vertex of `Γ` outside `bd(Σ)` is
in no `H_j`, so it is not a terminal of `L` and has degree 2 in `L`; all its edges in `L` are
edges of `Γ`, since an edge of `H_j` at it would put it in `H_j`
(`IsExhaustiveLinkage.vertexDegree_eq_two`).
-/

@[expose] public section

namespace GraphMinor
namespace GM21

open Set Hypergraph GraphMinor.GM10 GraphMinor.Surface

universe u v w

variable {α : Type u} {β : Type v} {S : Type w} [TopologicalSpace S]
  {G : Hypergraph α β} {Γ : Drawing S} {Γ_sub : Hypergraph α β}
  {ιV : S → α} {ιE : Set S → β} {r : ℕ} {F_star : Fin r → Set S} {H : Fin r → Hypergraph α β}
  {μ : BoundaryUnit S → Hypergraph α β} {q : Fin r → ℕ} {L : Hypergraph α β}

/-- "If $L$ is exhaustive then it follows that $\Gamma$ is a forest": `Γ` is a subgraph of the
linkage `L`, so every component of `Γ` is a path. -/
theorem IsExhaustiveLinkage.isLinkage (hP : IsPresentation G Γ Γ_sub ιV ιE r F_star H μ q)
    (hL : IsExhaustiveLinkage G Γ_sub r H L) : IsLinkage G Γ_sub :=
  isLinkage_of_le hL.1.1 hL.2.1 hP.drawing_subgraph

/-- "every vertex of $\Gamma$ not in $bd(\Sigma)$ has degree 2 in $\Gamma$" (Graph Minors XXI,
Section 6, page 24 of the preprint), for an exhaustive linkage `L`. -/
theorem IsExhaustiveLinkage.vertexDegree_eq_two
    (hP : IsPresentation G Γ Γ_sub ιV ιE r F_star H μ q)
    (hL : IsExhaustiveLinkage G Γ_sub r H L) {x : S} (hx : x ∈ Γ.V) (hxbd : x ∉ bd S) :
    vertexDegree Γ_sub (ιV x) = 2 := by
  obtain ⟨hLv, hΓL, hterm⟩ := hL
  have hLlink := hLv.1
  have hyΓ : ιV x ∈ Γ_sub.vertexSet := hP.ιV_image ▸ mem_image_of_mem ιV hx
  -- `ιV x` is in no `H_j`: otherwise `x` would lie in a support, hence in `bd(Σ)`.
  have hnoH : ∀ j, ιV x ∉ (H j).vertexSet := by
    intro j hj
    have hy : ιV x ∈ ιV '' (Γ.V ∩ F_star j) := hP.v1_inter_V j ▸ ⟨hj, hyΓ⟩
    obtain ⟨u, hu, hux⟩ := hy
    have hux' : u = x := hP.ιV_injOn hu.1 hx hux
    exact hxbd (hux' ▸ subset_bd_of_isSupportOfDrawing (hP.supports_isSupport j) hu.2)
  have hyL : ιV x ∈ L.vertexSet := hLv.2.1 ▸ hP.drawing_subgraph.vertexSet_subset hyΓ
  -- So `ιV x` is not a terminal of `L`, and has two edges in `L`.
  have hnotT : ιV x ∉ terminals L := fun h => by
    have := hterm h
    simp only [mem_iUnion] at this
    obtain ⟨j, hj⟩ := this
    exact hnoH j hj
  have h2 : (incidentEdges L (ιV x)).ncard = 2 := (hLlink.notMem_terminals_iff hyL).1 hnotT
  -- Every edge of `L` at `ιV x` is an edge of `Γ`.
  have hinc : incidentEdges Γ_sub (ιV x) = incidentEdges L (ιV x) := by
    apply Subset.antisymm (incidentEdges_subset_of_le hΓL _)
    rintro e ⟨he, hinc⟩
    have heG : e ∈ G.edgeSet := hLlink.1.edgeSet_subset he
    rw [hP.v1_union_E] at heG
    have hincG : G.Inc e (ιV x) := GM10.inc_of_le hLlink.1 hinc
    rcases heG with heH | heΓ
    · simp only [mem_iUnion] at heH
      obtain ⟨j, hj⟩ := heH
      exact absurd ((H j).vertex_mem_of_inc ((GM10.inc_iff_of_le (hP.v1_sub j) hj).2 hincG))
        (hnoH j)
    · exact ⟨heΓ, (GM10.inc_iff_of_le hP.drawing_subgraph heΓ).2 hincG⟩
  have hloop : ∀ e ∈ Γ_sub.edgeSet, (Γ_sub.ends e).ncard = 2 := fun e he =>
    (IsExhaustiveLinkage.isLinkage hP ⟨hLv, hΓL, hterm⟩).ends_ncard_eq_two he
  rw [vertexDegree_eq_ncard_incidentEdges hloop, hinc, h2]

end GM21
end GraphMinor
