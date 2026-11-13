module

public import GraphMinor.GM04.Painting
public import GraphMinor.GM06.Section3Dual
import GraphMinor.GM04.NumberedPatchwork
import GraphMinor.GM04.CirclePairing
import GraphMinor.GM04.PaintingDrawing
import GraphMinor.GM04.SpanningForest
import GraphMinor.GM04.DrawingIdentity
import GraphMinor.GM04.RealizationComponents
import GraphMinor.GM11.PaintingCells

/-!
# Graph Minors IV, (9.2)

Associate to each labelled painting its robust patchwork of noncrossing
pairings and apply (9.1). Take a spanning forest of a realization of the
resulting expansion, then draw it in the undeleted cells. Walk connections
are preserved, so the vertex sets of the expansion are still components.
The expansion's march and label properties give the remaining conclusions.

The printed second part of (c), page 253, lacks the word “distinct” before
the vertices. We insert that word. Otherwise a component would have to be
disjoint from itself, already failing for the one-node painting with no cells.
-/

public section

namespace GraphMinor.GM04

open Set Surface Graph

universe u w

private theorem boundary_ncard {Ω : Type w} {S : Type u} [TopologicalSpace S]
    (P : LabelledPainting Ω S) {e : Set S} (he : e ∈ P.painting.E) :
    (closure e \ e).ncard = (P.μ e).length := by
  classical
  rw [← P.μ_set e he, ← List.coe_toFinset]
  exact (Set.ncard_coe_finset _).trans (List.toFinset_card_of_nodup (P.μ_nodup e he))

/-- Graph Minors IV, (9.2), pages 253–254: a sequence of labelled paintings
of bounded tree-width has an expansion by components of a drawn forest,
with its edges inside cells and with the prescribed marches and labels.
The second part of printed (c) is corrected to apply to distinct vertices,
as explained in the module docstring. -/
theorem theorem_9_2_proof {Ω : Type w} [Preorder Ω] (hΩ : WellQuasiOrderedLE Ω)
    {S : Type u} [TopologicalSpace S] [T2Space S] (hS : IsClosedSurface S)
    (n : ℕ) (P : ℕ → LabelledPainting Ω S)
    (htw : ∀ i, TreeWidthLE (P i).toRootedHypergraph n) :
    ∃ i j, i < j ∧ ∃ (Ξ : Drawing S) (σv : S → Graph S (Set S)) (σe : Set S → Set S),
      Ξ.V = (P j).painting.V ∧ IsGraphForest Ξ.toGraph ∧
      (∀ f ∈ Ξ.E, ∃ e ∈ (P j).painting.E, f ⊆ e) ∧
      (∀ v ∈ (P i).painting.V, GM06.IsGraphComponent (σv v) Ξ.toGraph) ∧
      Set.MapsTo σe (P i).painting.E (P j).painting.E ∧
      Set.InjOn σe (P i).painting.E ∧
      (∀ v ∈ (P i).painting.V, ∀ v' ∈ (P i).painting.V, v ≠ v' →
        Disjoint (GM06.compPointSet (σv v)) (GM06.compPointSet (σv v'))) ∧
      (∀ v ∈ (P i).painting.V, ∀ e ∈ (P i).painting.E,
        ∀ f ∈ E(σv v), Disjoint f (σe e)) ∧
      (∀ e ∈ (P i).painting.E,
        (closure e \ e).ncard = (closure (σe e) \ σe e).ncard ∧
        ((P i).μ e).length = ((P j).μ (σe e)).length ∧
        ∀ k (hk : k < ((P i).μ e).length) (hk' : k < ((P j).μ (σe e)).length),
          ((P j).μ (σe e))[k] ∈ V(σv ((P i).μ e)[k])) ∧
      ((P i).roots.length = (P j).roots.length ∧
        ∀ k (hk : k < (P i).roots.length) (hk' : k < (P j).roots.length),
          (P j).roots[k] ∈ V(σv (P i).roots[k])) ∧
      (∀ e ∈ (P i).painting.E, (P i).φ e ≤ (P j).φ (σe e)) := by
  classical
  obtain ⟨i, j, hij, ηv, ηe, hη, H, hReal⟩ := theorem_9_1_proved hΩ n
    (fun i ↦ (P i).toPatchwork) (fun i ↦ (P i).toPatchwork_isRobust hS) htw
  have hHN : H.verts = (P j).painting.V := hReal.1.verts_eq
  have hHV : H.verts.Finite := hHN ▸ (P j).painting.finite_V
  have hHE : E(GM01.toGraph H).Finite := GM01.finite_edgeSet_of_finite_verts hHV
  obtain ⟨F, hF, hVF, hforest, hwalk⟩ := exists_spanning_forest (GM01.toGraph H) hHE
  have hVF' : V(F) = (P j).painting.V := hVF.trans hHN
  obtain ⟨Γ, hΓV, hID, hcells⟩ := (P j).exists_drawing_of_realization_subgraph hS
    (ηe '' (P i).painting.E) hReal.1 F hF hVF' (hHE.subset hF.edgeSet_mono)
  have hΓF : Γ.drawing.V = V(F) := hΓV.trans hVF'.symm
  have hΓforest := GraphDrawing.isGraphForest_of_vertex_id Γ hΓF hID hforest
  have hconnections (x y : S) : Nonempty (GraphWalk Γ.drawing.toGraph x y) ↔
      Nonempty (GraphWalk (GM01.toGraph H) x y) :=
    (GraphDrawing.walk_iff_of_vertex_id Γ hΓF hID x y).symm.trans (hwalk x y)
  have hreach (x : H.verts) : GM06.reachSet Γ.drawing.toGraph x = componentVerts H x :=
    (reachSet_eq_of_walk_iff (hΓV.trans hHN.symm) hconnections x).trans
      (reachSet_toGraph_eq_componentVerts H x)
  have hcomp : ∀ v : (P i).painting.V, ∃ x : H.verts, componentVerts H x = ηv v := by
    intro v
    obtain ⟨D, ⟨x, rfl⟩, hD⟩ := hReal.2 v v.property
    exact ⟨x, hD⟩
  choose x hx using hcomp
  let σv (v : S) : Graph S (Set S) :=
    if hv : v ∈ (P i).painting.V then GM06.compOf Γ.drawing.toGraph (x ⟨v, hv⟩)
    else Graph.noEdge ∅ (Set S)
  have hσ (v : S) (hv : v ∈ (P i).painting.V) :
      σv v = GM06.compOf Γ.drawing.toGraph (x ⟨v, hv⟩) := by
    simp only [σv, hv, ↓reduceDIte]
  have hroot (v : (P i).painting.V) : (x v).val ∈ V(Γ.drawing.toGraph) := by
    change (x v).val ∈ Γ.drawing.V
    rw [hΓV, ← hHN]
    exact (x v).property
  have hσcomp (v : S) (hv : v ∈ (P i).painting.V) :
      GM06.IsGraphComponent (σv v) Γ.drawing.toGraph := by
    rw [hσ v hv]
    exact GM06.isGraphComponent_compOf (hroot ⟨v, hv⟩)
  have hσV (v : S) (hv : v ∈ (P i).painting.V) : V(σv v) = ηv v := by
    rw [hσ v hv, GM06.vertexSet_compOf, hreach, hx]
  refine ⟨i, j, hij, Γ.drawing, σv, ηe, hΓV, hΓforest, ?_, hσcomp,
    hη.edge_mem, hη.edge_injOn, ?_, ?_, ?_, ?_, hη.φ_le⟩
  · intro f hf
    obtain ⟨e, he, hfe⟩ := hcells f hf
    exact ⟨e, he.1, hfe⟩
  · intro v hv v' hv' hne
    apply GM06.disjoint_compPointSet_of_ne Γ.drawing (hσcomp v hv) (hσcomp v' hv')
    intro heq
    have hsets : ηv v = ηv v' :=
      (hσV v hv).symm.trans ((congrArg Graph.vertexSet heq).trans (hσV v' hv'))
    obtain ⟨z, hz⟩ := hη.vertex_nonempty v hv
    exact Set.disjoint_left.mp (hη.vertex_disjoint v hv v' hv' hne) hz (hsets ▸ hz)
  · intro v hv e he f hf
    have hfΞ : f ∈ Γ.drawing.E := (hσcomp v hv).1.edgeSet_mono hf
    obtain ⟨t, ht, hft⟩ := hcells f hfΞ
    apply Set.disjoint_left.mpr
    intro z hzf hze
    have hneq : t ≠ ηe e := fun h ↦ ht.2 (h ▸ mem_image_of_mem ηe he)
    exact hneq (GM11.arcComponent_eq ht.1 (hη.edge_mem e he) (hft hzf) hze)
  · intro e he
    have he' := hη.edge_mem e he
    refine ⟨(boundary_ncard (P i) he).trans
      ((hη.μ_length e he).trans (boundary_ncard (P j) he').symm), hη.μ_length e he, ?_⟩
    intro k hk hk'
    have hv : ((P i).μ e)[k] ∈ (P i).painting.V := by
      have hinc : ((P i).μ e)[k] ∈ (P i).toRootedHypergraph.ends e := by
        rw [(P i).ends_eq he, ← (P i).μ_set e he]
        exact List.getElem_mem hk
      exact (P i).toRootedHypergraph.vertex_mem_of_inc hinc
    rw [hσV _ hv]
    exact hη.μ_mem e he k hk hk'
  · refine ⟨hη.roots_length, ?_⟩
    intro k hk hk'
    have hv := (P i).roots_subset _ (List.getElem_mem hk)
    rw [hσV _ hv]
    exact hη.roots_mem k hk hk'

end GraphMinor.GM04
