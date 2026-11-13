module

public import GraphMinor.GM01.SubdivisionPathsOutside
public import GraphMinor.GM01.CombSpineCuts
import Lean.Elab.Tactic.Omega

/-!
# The upper boundary of a skipped comb block

The two-cell minor in the skipped block of Graph Minors I, (4.1), page 55,
uses source vertices at or before the next cut. The later source side
consists of vertices with larger spine index. The proved source cut
property closes that side after deletion of its spine vertex. Applying
the subdivision cut lemmas excludes the selected centres and paths from
the later region, including binary copies at the cut's own position.
-/

public section

namespace GraphMinor.GM01

open Set Graph SimpleGraph

/-- A source centre at or before the cut is outside its later region. -/
theorem comb_subdivision_centre_not_mem_later_region {α β : Type*} {γ L : ℕ}
    {N : Graph α β} {c : (pathComb γ L).verts → α} (hc : Function.Injective c)
    {P : (pathComb γ L).coe.edgeSet → Graph α β} (hPN : ∀ e, P e ≤ N)
    (hE : E(N) = ⋃ e, E(P e))
    (hPaths : ∀ e : (pathComb γ L).coe.edgeSet, ∃ a b, e.val = s(a,b) ∧
      V(P e) ∩ range c = {c a,c b})
    (hInter : ∀ e f : (pathComb γ L).coe.edgeSet, e ≠ f → V(P e) ∩ V(P f) ⊆ range c)
    (q : Fin L) (hq : q.val < L - 1) (v : (pathComb γ L).verts)
    (hv : (pathCombSpineIndex v.val).val ≤ q.val) :
    c v ∉ vertexAvoidanceRegion N
      (c ⟨Sum.inl ⟨L - 1, by omega⟩, pathComb_spine_mem γ L _⟩)
      (c ⟨Sum.inl q, pathComb_spine_mem γ L q⟩) := by
  let D : Set (pathComb γ L).verts := {w | q.val < (pathCombSpineIndex w.val).val}
  let r : (pathComb γ L).verts := ⟨Sum.inl q, pathComb_spine_mem γ L q⟩
  have hD : ∀ {a b : (pathComb γ L).verts}, (pathComb γ L).coe.Adj a b →
      a ∈ D → b ≠ r → b ∈ D := by
    intro a b hab ha hbr
    exact pathComb_after_cut_adj_closed hab ha (fun h ↦ hbr (Subtype.ext h))
  apply subdivision_centre_not_mem_region hc hPN hE hPaths hInter D r hD
    ⟨Sum.inl ⟨L - 1, by omega⟩, pathComb_spine_mem γ L _⟩ hq v
  change ¬ q.val < (pathCombSpineIndex v.val).val
  omega

/-- A replacing path with both source ends at or before a cut is disjoint
from the later region. This supplies the upper boundary of a skipped block. -/
theorem comb_subdivision_path_disjoint_later_region {α β : Type*} {γ L : ℕ}
    {N : Graph α β} {c : (pathComb γ L).verts → α} (hc : Function.Injective c)
    {P : (pathComb γ L).coe.edgeSet → Graph α β} (hPN : ∀ e, P e ≤ N)
    (hE : E(N) = ⋃ e, E(P e))
    (hPaths : ∀ e : (pathComb γ L).coe.edgeSet, ∃ a b, e.val = s(a,b) ∧
      V(P e) ∩ range c = {c a,c b})
    (hInter : ∀ e f : (pathComb γ L).coe.edgeSet, e ≠ f → V(P e) ∩ V(P f) ⊆ range c)
    (q : Fin L) (hq : q.val < L - 1) (e : (pathComb γ L).coe.edgeSet)
    (hEnds : ∀ v ∈ e.val, (pathCombSpineIndex v.val).val ≤ q.val) :
    Disjoint V(P e) (vertexAvoidanceRegion N
      (c ⟨Sum.inl ⟨L - 1, by omega⟩, pathComb_spine_mem γ L _⟩)
      (c ⟨Sum.inl q, pathComb_spine_mem γ L q⟩)) := by
  let D : Set (pathComb γ L).verts := {w | q.val < (pathCombSpineIndex w.val).val}
  let r : (pathComb γ L).verts := ⟨Sum.inl q, pathComb_spine_mem γ L q⟩
  have hD : ∀ {a b : (pathComb γ L).verts}, (pathComb γ L).coe.Adj a b →
      a ∈ D → b ≠ r → b ∈ D := by
    intro a b hab ha hbr
    exact pathComb_after_cut_adj_closed hab ha (fun h ↦ hbr (Subtype.ext h))
  apply subdivision_path_disjoint_region hc hPN hE hPaths hInter D r hD
    ⟨Sum.inl ⟨L - 1, by omega⟩, pathComb_spine_mem γ L _⟩ hq e
  intro v hv hLater
  have hEarlier := hEnds v hv
  change q.val < (pathCombSpineIndex v.val).val at hLater
  omega

end GraphMinor.GM01
