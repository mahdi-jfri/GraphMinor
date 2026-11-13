module

public import Mathlib.Topology.MetricSpace.Thickening
public import Mathlib.Analysis.Complex.Basic
import Mathlib.Topology.Separation.Hausdorff

/-!
# Separate metric neighborhoods of the middle arcs

Part IV, Section 7a of the planarity note chooses pairwise disjoint open
metric neighborhoods of the compact middle arcs, avoiding the other radial
segments and original vertices. Finite compact separation first gives open
neighborhoods. Compactness then gives a positive metric thickness for each
arc inside its open neighborhood minus its forbidden closed set.
-/

public section
namespace GraphMinor.LRPlanarity

open Set Metric Topology

/-- The neighborhood-selection step of Part IV, Section 7a. Pairwise disjoint
compact sets have pairwise disjoint positive metric neighborhoods, each
avoiding a prescribed closed set disjoint from the original compact set. -/
theorem exists_disjoint_middle_neighborhoods {ι : Type*} [Finite ι]
    (K F : ι → Set ℂ) (hK : ∀ i, IsCompact (K i))
    (hdisj : Pairwise (fun i j => Disjoint (K i) (K j)))
    (hF : ∀ i, IsClosed (F i)) (hmiss : ∀ i, Disjoint (K i) (F i)) :
    ∃ r : ι → ℝ, (∀ i, 0 < r i ∧ Disjoint (thickening (r i) (K i)) (F i)) ∧
      Pairwise (fun i j => Disjoint (thickening (r i) (K i)) (thickening (r j) (K j))) := by
  have hn : Pairwise (fun i j => Disjoint (𝓝ˢ (K i)) (𝓝ˢ (K j))) := by
    intro i j hij
    exact (SeparatedNhds.of_isCompact_isCompact_isClosed (hK i) (hK j)
      (hK j).isClosed (hdisj hij)).disjoint_nhdsSet
  obtain ⟨U, hU, hUd⟩ := hn.exists_mem_filter_basis_of_disjoint (fun i => hasBasis_nhdsSet (K i))
  have hsub : ∀ i, K i ⊆ U i ∩ (F i)ᶜ := by
    intro i x hx
    exact ⟨(hU i).2 hx, fun hxf => disjoint_left.mp (hmiss i) hx hxf⟩
  have hmetric : ∀ i, ∃ r : ℝ, 0 < r ∧ thickening r (K i) ⊆ U i ∩ (F i)ᶜ :=
    fun i => (hK i).exists_thickening_subset_open
      ((hU i).1.inter (hF i).isOpen_compl) (hsub i)
  choose r hr hsmall using hmetric
  refine ⟨r, fun i => ⟨hr i, ?_⟩, ?_⟩
  · exact disjoint_left.mpr fun x hx hxf => (hsmall i hx).2 hxf
  · intro i j hij
    exact (hUd hij).mono (fun _ hx => (hsmall i hx).1) (fun _ hx => (hsmall j hx).1)

end GraphMinor.LRPlanarity
