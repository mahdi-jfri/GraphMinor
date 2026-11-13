module

public import GraphMinor.Surface.SurfaceGraph
import GraphMinor.GM08.Section18GraphSubdivision
import GraphMinor.GM19.Section6Tri
import Lean.Elab.Tactic.Omega

/-!
# Euler sums do not depend on the cutting-graph subdivision

Refine two graphs on the same set at each other's vertices. Their
vertices and open edge components then agree, so their edges agree.
Each refinement preserves the Euler sum. Thus the refined graph in
the cut construction has the Euler sum of the printed schism shape.
-/

public section

namespace GraphMinor.GM08

open Set Topology GraphMinor.Surface

private theorem edges_eq_of_vertices_and_carrier_eq {S : Type} [TopologicalSpace S]
    [T2Space S] {V : Set S} {E D : Set (Set S)} (hE : IsGraph V E)
    (hD : IsGraph V D) (hgr : gr V E = gr V D) : E = D := by
  have hsub : ∀ {E D : Set (Set S)}, IsGraph V E → IsGraph V D →
      gr V E = gr V D → E ⊆ D := by
    intro E D hg hh hcarrier e he
    have hpart : e \ V ∈ arcComponentsIn (gr V D \ V) := by
      rw [← hcarrier, GM19.IsGraphD.arcComponents_eq hg]
      exact mem_image_of_mem _ he
    rw [GM19.IsGraphD.arcComponents_eq hh] at hpart
    obtain ⟨d, hd, hde⟩ := hpart
    have hde' : d = e := by
      rw [← GM19.IsGraphD.closure_diff hh hd, ← GM19.IsGraphD.closure_diff hg he]
      exact congrArg closure hde
    exact hde' ▸ hd
  exact subset_antisymm (hsub hE hD hgr) (hsub hD hE hgr.symm)

/-- The Euler sum of a finite geometric graph depends only on its
carrier. This justifies using the original schism shape instead of its
auxiliary graph subdivision in VIII (18.2), page 286. -/
theorem graph_euler_eq_of_carrier_eq {S : Type} [TopologicalSpace S] [T2Space S]
    {V W : Set S} {E D : Set (Set S)} (hE : IsGraph V E) (hD : IsGraph W D)
    (hgr : gr V E = gr W D) :
    (V.ncard : ℤ) - E.ncard = (W.ncard : ℤ) - D.ncard := by
  have hWV : W ⊆ gr V E := fun x hx => hgr.symm ▸ (Or.inl hx : x ∈ gr W D)
  have hVW : V ⊆ gr W D := fun x hx => hgr ▸ (Or.inl hx : x ∈ gr V E)
  obtain ⟨E', hE', hgrE', _, hcountE⟩ := exists_graph_subdivision_at_finite_set hE hD.fin hWV
  obtain ⟨D', hD', hgrD', _, hcountD⟩ := exists_graph_subdivision_at_finite_set hD hE.fin hVW
  have hD'' : IsGraph (V ∪ W) D' := union_comm W V ▸ hD'
  have hcarrier : gr (V ∪ W) E' = gr (V ∪ W) D' :=
    hgrE'.trans (hgr.trans (by simpa only [union_comm] using hgrD'.symm))
  have hedges : E' = D' := edges_eq_of_vertices_and_carrier_eq hE' hD'' hcarrier
  rw [hedges] at hcountE
  rw [union_comm W V] at hcountD
  omega

end GraphMinor.GM08
