module

public import GraphMinor.GM08.Section18Theorem182
public import GraphMinor.GM08.Section18SurroundSides
import GraphMinor.GM08.Section18X1Cut
import GraphMinor.GM08.Section18LineCut
import GraphMinor.GM08.Section18LineLift
import GraphMinor.GM08.Section18SurroundFarSide
import GraphMinor.GM08.Section18CutCompose
import GraphMinor.GM08.Section18CutBoundary
import GraphMinor.GM11.Section6

/-!
# The cut along an `X₄`-arc

A schism of type (vi) (VIII (18.2), page 286) is a circle `A` that surrounds
a cuff `C₂`, and a line `P` from a point `u` of `A` to a point `w` of another
cuff `C₁`. The point `w` is the only point of the schism on `bd(Σ)`. We cut
in two steps.

1. Cut along `A` (`exists_surround_sides`). One side `W` is a cylinder
   around `C₂`, and the far side `Wᶜ` has measure at most `g(Σ)`.
2. The lift of `P` is a line in `Wᶜ` from the new cuff over `A` to the cuff
   over `C₁`. These cuffs are different, so cutting `Wᶜ` along this line
   lowers its measure by one (`exists_line_cut_of_distinct`).

The cylinder has measure `2`, and `g(Σ) ≥ 3`, so every piece of the result
has measure less than `g(Σ)`.
-/

@[expose] public section

namespace GraphMinor.GM08

open Set Topology GraphMinor.Surface GraphMinor.GM11

universe w

/-- An open and closed connected set is the component of each of its points. -/
theorem connectedComponent_eq_of_isClopen {T : Type w} [TopologicalSpace T] {W : Set T}
    (hW : IsClopen W) [ConnectedSpace W] {z : T} (hz : z ∈ W) : connectedComponent z = W :=
  (hW.connectedComponent_subset hz).antisymm
    ((isConnected_iff_connectedSpace.mpr inferInstance).isPreconnected.subset_connectedComponent hz)

/-- **(18.2) for an `X₄`-arc** (type (vi)). -/
theorem theorem_18_2_X4 {S : Type w} [TopologicalSpace S] [ConnectedSpace S] (hS : IsSurface S)
    (hncyl : ¬ Nonempty (S ≃ₜ SurfaceModel 0 0 2)) (h3 : 3 ≤ surfaceComplexity S)
    {A P C₁ C₂ : Set S} {u v : S} (hA : IsOArc A) (hP : IsLineWithEnds P u v)
    (huv : u ≠ v) (hPA : P ∩ A = {u}) (hC₁ : C₁ ∈ cuffs S) (hC : C₁ ≠ C₂) (hv : v ∈ C₁)
    (hsur : GM07.SurroundsCuff A C₂) (hbd : (A ∪ P) ∩ bd S = {v}) :
    ∃ (T : Type w) (_ : TopologicalSpace T) (ψ : T → S),
      GM07.IsCutAlongSet (A ∪ P) ψ ∧ GM19.IsCutMap ψ (A ∪ P) ∧
      surfaceComplexity T < surfaceComplexity S := by
  have : T2Space S := hS.2.1
  have hC₁bd : C₁ ⊆ bd S := by
    obtain ⟨x, -, rfl⟩ := hC₁
    exact connectedComponentIn_subset _ _
  have hbd' : ∀ z ∈ A ∪ P, z ∈ bd S → z = v := fun z hz hzb =>
    (hbd ▸ ⟨hz, hzb⟩ : z ∈ ({v} : Set S))
  have huA : u ∈ A := (hPA.symm ▸ rfl : u ∈ P ∩ A).2
  have hvA : v ∉ A := fun h => huv ((hPA ▸ ⟨hP.right_mem, h⟩ : v ∈ ({u} : Set S)).symm)
  have hoffA : Disjoint A (bd S) := disjoint_left.mpr fun z hz hzb =>
    hvA (hbd' z (Or.inl hz) hzb ▸ hz)
  have hAc : IsClosed A := hA.isCompact.isClosed
  obtain ⟨T₁, t₁, ψ₁, W, hT₁, hcut₁, hs, hgR⟩ := exists_surround_sides hS hncyl h3 hA hoffA hsur
  have : CompactSpace T₁ := hT₁.1
  have : T2Space T₁ := hT₁.2.1
  have hPo : Disjoint (P \ {u, v}) A := disjoint_left.mpr fun z hz hzA =>
    hz.2 (Or.inl (hPA ▸ ⟨hz.1, hzA⟩ : z ∈ ({u} : Set S)))
  have hPb : Disjoint (P \ {u, v}) (bd S) := disjoint_left.mpr fun z hz hzb =>
    hz.2 (Or.inr (hbd' z (Or.inr hz.1) hzb))
  obtain ⟨x, y, hx, hy, hL, hbij, hdiff⟩ :=
    exists_line_closure_lift_of_cutMap (GM19.IsCutting.isCutMap hcut₁) hAc hP hPo
  set L := closure (ψ₁ ⁻¹' (P \ {u, v}))
  -- the lift of `P` lies on the far side, since `C₁` has no lift in `W`
  have hC₁W : ψ₁ ⁻¹' C₁ ⊆ Wᶜ := fun z hz hzW =>
    disjoint_left.mp (disjoint_of_mem_cuffs hC₁ hsur.1 hC) hz (hs.bd_sub z hzW (hC₁bd hz))
  have hfar : ψ₁ ⁻¹' (P \ {u, v}) ⊆ Wᶜ :=
    preimage_subset_compl_of_closure hS hT₁ hcut₁ hs hC₁W
      (GM11.IsLineWithEnds.isPreconnected_sdiff_pair hP) hPo
      ⟨v, hP.subset_closure_diff hP.right_mem, hv⟩
  have hLR : L ⊆ Wᶜ := closure_minimal hfar hs.isClopen.compl.isClosed
  have : ConnectedSpace (Wᶜ : Set T₁) := hs.connected_compl
  have : ConnectedSpace W := hs.connected
  have hxy : x ≠ y := fun h => huv (hx ▸ hy ▸ congrArg ψ₁ h)
  have hbdT : ψ₁ ⁻¹' (bd S ∪ A) = bd T₁ :=
    (isCutAlongSet_of_isCutting hS hT₁ hAc hcut₁).preimage_bd
  have hxb : x ∈ bd T₁ := hcut₁.2.2.2.2 (show ψ₁ x ∈ A by rw [hx]; exact huA)
  have hyb : y ∈ bd T₁ := by
    have h : y ∈ ψ₁ ⁻¹' (bd S ∪ A) := by
      rw [mem_preimage, hy]
      exact Or.inl (hC₁bd hv)
    rwa [hbdT] at h
  have hLbd : L ∩ bd T₁ = {x, y} := by
    ext z
    constructor
    · rintro ⟨hzL, hzb⟩
      by_contra hz
      have hz' : z ∈ ψ₁ ⁻¹' (P \ {u, v}) := hdiff ▸ ⟨hzL, hz⟩
      rcases (hbdT ▸ hzb : z ∈ ψ₁ ⁻¹' (bd S ∪ A)) with h | h
      · exact disjoint_left.mp hPb hz' h
      · exact disjoint_left.mp hPo hz' h
    · rintro (rfl | rfl)
      · exact ⟨hL.left_mem, hxb⟩
      · exact ⟨hL.right_mem, hyb⟩
  have hcuffs : connectedComponentIn (bd T₁) x ≠ connectedComponentIn (bd T₁) y :=
    connectedComponentIn_bd_ne_of_map hcut₁.1 hAc (cuff_statement S hS).1 hoffA
      (fun z hz => (hbdT ▸ hz : z ∈ ψ₁ ⁻¹' (bd S ∪ A)).symm)
      hxb hyb (show ψ₁ x ∈ A by rw [hx]; exact huA)
      (show ψ₁ y ∈ bd S by rw [hy]; exact hC₁bd hv)
  have hQn : surfaceComplexity (Wᶜ : Set T₁) ≤ surfaceComplexity S - 1 + 1 := by omega
  have hc : ∀ z ∉ (Wᶜ : Set T₁),
      connectedSurfaceComplexity (connectedComponent z) ≤ surfaceComplexity S - 1 := by
    intro z hz
    rw [notMem_compl_iff] at hz
    rw [connectedSurfaceComplexity_congr
      (Homeomorph.setCongr (connectedComponent_eq_of_isClopen hs.isClopen hz)),
      connectedSurfaceComplexity_eq hs.cylinder]
    omega
  obtain ⟨T₂, t₂, ψ₂, hT₂, hcut₂, hg₂⟩ :=
    exists_line_cut_of_distinct hT₁ hs.isClopen.compl hLR hL hxy hLbd hcuffs hQn hc
  have hG₂H : L ⊆ ψ₁ ⁻¹' P := fun z hz => hbij.mapsTo hz
  have hH : ψ₁ ⁻¹' P ⊆ L ∪ bd T₁ := by
    intro z hz
    by_cases huvz : ψ₁ z ∈ ({u, v} : Set S)
    · refine Or.inr ?_
      rcases huvz with h | h
      · exact hcut₁.2.2.2.2 (show ψ₁ z ∈ A by rw [h]; exact huA)
      · have h' : z ∈ ψ₁ ⁻¹' (bd S ∪ A) := by
          rw [mem_preimage, mem_singleton_iff.mp h]
          exact Or.inl (hC₁bd hv)
        rwa [hbdT] at h'
    · exact Or.inl (subset_closure ⟨hz, huvz⟩)
  exact ⟨T₂, t₂, ψ₁ ∘ ψ₂, isCutAlongSet_comp hS hT₁ hT₂ hcut₁ hAc hcut₂ isClosed_closure hG₂H hH,
    isCutMap_comp hT₁ hT₂ hcut₁ hcut₂ isClosed_closure hG₂H hH, by omega⟩

end GraphMinor.GM08
