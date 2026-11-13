module

public import GraphMinor.Surface.TopologyStatements
import GraphMinor.GM05.CuffPair
import GraphMinor.Surface.CutComp
import Mathlib.Topology.Homeomorph.Lemmas

/-!
# The cuff in a component of a separating cut

The boundary of a two-sided cut is the union of its two circle lifts.
Each of the two components contains one lift and misses the other.
Thus its entire boundary is the lift it contains, and that circle is
its only cuff. This identifies each cap in GM V, (8.10).
-/

public section

namespace GraphMinor.GM05

open Set Topology Surface

universe u

/-- A clopen part of a cut surface that contains one boundary lift and
misses the other has that lift as its sole cuff. -/
theorem cut_component_single_cuff {Y : Type u} [TopologicalSpace Y]
    (hY : IsSurface Y) {X X' W : Set Y} (hX : IsOArc X)
    (hbd : bd Y=X ∪ X') (hW : IsClopen W) (hs : X ⊆ W) (hd : Disjoint W X') :
    IsOArc (Subtype.val ⁻¹' X : Set W) ∧
      bd W=Subtype.val ⁻¹' X ∧ cuffs W={Subtype.val ⁻¹' X} := by
  have hr : X ⊆ range (Subtype.val : W → Y) := fun x hx ↦ ⟨⟨x,hs hx⟩,rfl⟩
  let e := IsEmbedding.subtypeVal.homeomorphOfSubsetRange hr
  have hC : IsOArc (Subtype.val ⁻¹' X : Set W) := by
    obtain ⟨φ⟩ := hX
    exact ⟨φ.trans e.symm⟩
  have hb : bd W=(Subtype.val ⁻¹' X : Set W) := by
    ext x
    rw [mem_bd_sub hW.2]
    constructor
    · intro hx
      rcases (hbd ▸ hx : x.1 ∈ X ∪ X') with hx|hx'
      · exact hx
      · exact (Set.disjoint_left.mp hd x.2 hx').elim
    · intro hx
      exact hbd.symm ▸ Or.inl hx
  have hpair : bd W=(Subtype.val ⁻¹' X : Set W) ∪ (Subtype.val ⁻¹' X) := by rw [union_self,hb]
  have hcuffs := cuffs_eq_pair_of_boundary (isSurface_sub hY hW) hC hC hpair
  exact ⟨hC,hb,by simpa only [Set.pair_eq_singleton] using hcuffs⟩

end GraphMinor.GM05
