module

public import GraphMinor.Surface.TopologyStatements
import GraphMinor.Surface.CutLoop
import GraphMinor.Surface.CutComp
import GraphMinor.Surface.DiscMerge

/-!
# The two cuffs of a two-sided circle cut

For Graph Minors V, (8.10), the two boundary lifts of the cut circle are
exactly the cuffs. Each lift is a circle in a cuff and hence is the
whole cuff. Their union is the boundary, so there are no other cuffs.
-/

public section

namespace GraphMinor.GM05

open Set Topology Surface

universe u

/-- A circle contained in the boundary of a surface is one of its cuffs. -/
theorem isOArc_mem_cuffs {Y : Type u} [TopologicalSpace Y] (hY : IsSurface Y)
    {X : Set Y} (hX : IsOArc X) (hx : X ⊆ bd Y) : X ∈ cuffs Y := by
  let : T2Space Y := hY.2.1
  have hp : IsPreconnected X := hX.isPreconnected
  obtain ⟨e⟩ := hX
  obtain ⟨x,hxX⟩ : X.Nonempty := ⟨(e 1).1,(e 1).2⟩
  have hc : connectedComponentIn (bd Y) x ∈ cuffs Y := ⟨x,hx hxX,rfl⟩
  obtain ⟨φ⟩ := (cuff_statement Y hY).2.2 _ hc
  have he : X=connectedComponentIn (bd Y) x :=
    oarc_eq φ ⟨e⟩ (hp.subset_connectedComponentIn hxX hx)
  exact he.symm ▸ hc

/-- A boundary that is the union of two circles has precisely those
circles as its cuffs. -/
theorem cuffs_eq_pair_of_boundary {Y : Type u} [TopologicalSpace Y]
    (hY : IsSurface Y) {X X' : Set Y} (hX : IsOArc X) (hX' : IsOArc X')
    (hbd : bd Y=X ∪ X') : cuffs Y={X,X'} := by
  have hx : X ⊆ bd Y := by rw [hbd]; exact subset_union_left
  have hx' : X' ⊆ bd Y := by rw [hbd]; exact subset_union_right
  have hcX := isOArc_mem_cuffs hY hX hx
  have hcX' := isOArc_mem_cuffs hY hX' hx'
  apply Subset.antisymm
  · rintro C ⟨y,hy,rfl⟩
    rcases (hbd ▸ hy : y ∈ X ∪ X') with hyX|hyX'
    · obtain ⟨z,hz,hzX⟩ := hcX
      have hyC : y ∈ connectedComponentIn (bd Y) z := hzX ▸ hyX
      exact Or.inl ((connectedComponentIn_eq hyC).symm.trans hzX)
    · obtain ⟨z,hz,hzX'⟩ := hcX'
      have hyC : y ∈ connectedComponentIn (bd Y) z := hzX' ▸ hyX'
      exact Or.inr ((connectedComponentIn_eq hyC).symm.trans hzX')
  · intro C hC
    rcases hC with rfl|rfl
    · exact hcX
    · exact hcX'

end GraphMinor.GM05
