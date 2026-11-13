module

public import GraphMinor.GM19.CutMap
import Mathlib.Data.Set.Card

/-!
# Counting vertices on and off the cut

A cutting map is bijective away from the cutting set. Partition a
finite vertex set into the vertices on the cut and those off it.
Only the first part changes its count. This separates the two vertex
terms in the Euler calculation of VIII (18.2).
-/

public section

namespace GraphMinor.GM08

open Set

universe u

/-- The lift of a finite vertex set has its full cut-vertex fibre count,
plus one point for each old vertex off the cut. This is the vertex
partition in the proof of VIII (18.2), page 286. -/
theorem cutMap_ncard_preimage_eq {S Y : Type u} [TopologicalSpace S]
    [TopologicalSpace Y] {ψ : Y → S} {F V : Set S}
    (hcm : GM19.IsCutMap ψ F) (hV : V.Finite) :
    (ψ ⁻¹' V).ncard = (ψ ⁻¹' (V ∩ F)).ncard + (V \ F).ncard := by
  classical
  have hcutfin : (ψ ⁻¹' (V ∩ F)).Finite := by
    have heq : ψ ⁻¹' (V ∩ F) = ⋃ v ∈ V ∩ F, ψ ⁻¹' {v} := by ext y; simp
    rw [heq]
    exact (hV.subset inter_subset_left).biUnion (fun v _ => hcm.2.2.2.1 v)
  have hoffinj : InjOn ψ (ψ ⁻¹' (V \ F)) :=
    hcm.2.2.1.mono (fun y hy => hy.2)
  have hofffin : (ψ ⁻¹' (V \ F)).Finite := (hV.subset sdiff_subset).preimage hoffinj
  have hoffcard : (ψ ⁻¹' (V \ F)).ncard = (V \ F).ncard := by
    have hh := hoffinj.ncard_image
    rw [hcm.2.1.image_preimage] at hh
    exact hh.symm
  have hpre : ψ ⁻¹' V = ψ ⁻¹' (V ∩ F) ∪ ψ ⁻¹' (V \ F) := by
    ext y
    by_cases hy : ψ y ∈ F <;> simp only [mem_preimage, mem_union, mem_inter_iff, mem_sdiff] <;> simp [hy]
  have hdis : Disjoint (ψ ⁻¹' (V ∩ F)) (ψ ⁻¹' (V \ F)) :=
    disjoint_left.mpr (fun y hy hz => hz.2 hy.2)
  rw [hpre, ncard_union_eq hdis hcutfin hofffin, hoffcard]

end GraphMinor.GM08
