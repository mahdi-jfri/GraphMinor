module

public import GraphMinor.GM06.Defs
import GraphMinor.GM11.Walks
import GraphMinor.GM06.Section4
import GraphMinor.GM07.NetExists

/-!
# Edges added along the cuffs

For VI (5.1), page 129, adjoining the cuffs adds edges but no
vertices. Every new edge lies entirely on the added set. Indeed,
if it met the old drawing away from a vertex, it would meet an old
edge. Both would then be the same edge of the larger drawing.
-/

public section

namespace GraphMinor.GM06

open Set GraphMinor.Surface

universe u

/-- Enlarging a drawing without adding vertices can add an edge only
in the added point set. -/
theorem edge_mem_or_subset_adjoined_set
    {S : Type u} [TopologicalSpace S] {G F : Drawing S} {X : Set S}
    (hGF : G.IsSubdrawing F) (hFU : F.U = G.U ∪ X) (hFV : F.V = G.V)
    {e : Set S} (he : e ∈ F.E) : e ∈ G.E ∨ e ⊆ X := by
  by_cases heG : e ∈ G.E
  · exact Or.inl heG
  · apply Or.inr
    intro x hx
    have hxF := he.2.1 hx
    have hxU : x ∈ G.U ∪ X := hFU ▸ hxF.1
    rcases hxU with hxG | hxX
    · have hxV : x ∉ G.V := by
        rw [← hFV]
        exact hxF.2
      obtain ⟨f, hf, hxf⟩ := G.exists_edge_of_mem hxG hxV
      have hfe := GM07.arcComponentsIn_eq_of_mem (hGF.2 hf) he hxf hx
      exact False.elim (heG (hfe ▸ hf))
    · exact hxX

/-- A new edge in an enlargement with no new vertices is disjoint
from the entire old drawing. -/
theorem disjoint_old_U_of_new_edge
    {S : Type u} [TopologicalSpace S] {G F : Drawing S}
    (hGF : G.IsSubdrawing F) (hFV : F.V = G.V)
    {e : Set S} (he : e ∈ F.E) (heG : e ∉ G.E) : Disjoint e G.U := by
  apply disjoint_left.mpr
  intro x hx hxG
  have hxV : x ∉ G.V := by
    rw [← hFV]
    exact (he.2.1 hx).2
  obtain ⟨f, hf, hxf⟩ := G.exists_edge_of_mem hxG hxV
  have hfe := GM07.arcComponentsIn_eq_of_mem (hGF.2 hf) he hxf hx
  exact heG (hfe ▸ hf)

/-- In the augmented cylinder drawing, every edge is an old edge or
lies on the cuffs. -/
theorem edge_mem_or_subset_boundary_of_adjoining
    {G F : Drawing ClosedCylinder} (hGF : G.IsSubdrawing F)
    (hFU : F.U = G.U ∪ bd ClosedCylinder) (hFV : F.V = G.V)
    {e : Set ClosedCylinder} (he : e ∈ F.E) : e ∈ G.E ∨ e ⊆ bd ClosedCylinder :=
  edge_mem_or_subset_adjoined_set hGF hFU hFV he

/-- A cuff edge lies on one cuff, since it is connected and the two
cuffs are separated by the open radial intervals about 3/2. -/
theorem edge_subset_one_cuff_of_subset_boundary
    {F : Drawing ClosedCylinder} {e : Set ClosedCylinder} (he : e ∈ F.E)
    (heBd : e ⊆ bd ClosedCylinder) : e ⊆ cylinderCuff1 ∨ e ⊆ cylinderCuff2 := by
  have hrad : Continuous (fun x : ClosedCylinder => x.1.1) :=
    continuous_fst.comp continuous_subtype_val
  have hcover : e ⊆ {x : ClosedCylinder | x.1.1 < 3 / 2} ∪
      {x : ClosedCylinder | 3 / 2 < x.1.1} := by
    intro x hx
    have hh := heBd hx
    rw [bd_closedCylinder] at hh
    rcases hh with h1 | h2
    · exact Or.inl (by change x.1.1 < 3 / 2; change x.1.1 = 1 at h1; rw [h1]; norm_num)
    · exact Or.inr (by change 3 / 2 < x.1.1; change x.1.1 = 2 at h2; rw [h2]; norm_num)
  have hdis : Disjoint {x : ClosedCylinder | x.1.1 < 3 / 2}
      {x : ClosedCylinder | 3 / 2 < x.1.1} :=
    disjoint_left.mpr (fun _ (h1 : _ < (3 / 2 : ℝ)) (h2 : (3 / 2 : ℝ) < _) => lt_asymm h1 h2)
  rcases he.2.2.1.isConnected.isPreconnected.subset_or_subset
      (isOpen_lt hrad continuous_const) (isOpen_lt continuous_const hrad) hdis hcover with h1 | h2
  · apply Or.inl
    intro x hx
    have hh := heBd hx
    rw [bd_closedCylinder] at hh
    rcases hh with hh | hh
    · exact hh
    · have hlt := h1 hx
      change x.1.1 = 2 at hh
      change x.1.1 < 3 / 2 at hlt
      rw [hh] at hlt
      norm_num at hlt
  · apply Or.inr
    intro x hx
    have hh := heBd hx
    rw [bd_closedCylinder] at hh
    rcases hh with hh | hh
    · have hlt := h2 hx
      change x.1.1 = 1 at hh
      change 3 / 2 < x.1.1 at hlt
      rw [hh] at hlt
      norm_num at hlt
    · exact hh

end GraphMinor.GM06
