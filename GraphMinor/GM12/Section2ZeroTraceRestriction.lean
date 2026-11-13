module

public import GraphMinor.GM12.Section2TraceImage
import GraphMinor.GM11.Walks
import GraphMinor.GM11.Regions

/-!
# Restricting a trace to a zero-length subcurve

In the restriction step of XII (2.1), pages 243--244, a normal subcurve
of length zero lies in a single region. The original traced curve
meets that region, so its trace contains the region's hub. The nil walk
at this hub is a trace of the subcurve, and its one-vertex drawing is
a subdrawing of the original trace.
-/

public section

namespace GraphMinor.GM12

open Set Surface GM11

/-- The zero-length subcurve case of the trace restriction step in
XII (2.1), pages 243--244. Injectivity of the subcurve is not needed. -/
theorem trace_restriction_of_length_zero
    {S : Type*} [TopologicalSpace S] [T1Space S] {Γ K : Drawing S}
    {φ ψ : C(Circle, S)} {u : S} (W : GraphWalk K.toGraph u u)
    (hW : IsTrace Γ K φ W) (hψ : IsNormalCurve Γ ψ)
    (hsub : range ψ ⊆ range φ) (hzero : curveLength Γ ψ = 0) :
    ∃ (v : S) (W' : GraphWalk K.toGraph v v), IsTrace Γ K ψ W' ∧
      (walkDrawing K W').IsSubdrawing (walkDrawing K W) := by
  have hemp : {z | ψ z ∈ Γ.U} = ∅ := (Set.ncard_eq_zero hψ.1).mp hzero
  have hoff : ∀ z, ψ z ∉ Γ.U := by
    intro z hz
    exact Set.notMem_empty z (hemp ▸ hz)
  obtain ⟨r, hr, hψr⟩ := exists_region_of_notMem (hoff 1)
  have hψsub : range ψ ⊆ r := subset_region hr (isPreconnected_range ψ.continuous)
    (disjoint_left.mpr (by rintro _ ⟨z, rfl⟩; exact hoff z)) ⟨1, rfl⟩ hψr
  obtain ⟨v, hvW, hvr⟩ := trace_region_in_image W hW hr ⟨ψ 1, hsub (mem_range_self 1), hψr⟩
  have hvdraw : v ∈ (walkDrawing K W).V := by rw [walkDrawing_V]; exact hvW
  have hvK : v ∈ K.V := (walkDrawing_isSubdrawing K W).1 hvdraw
  let W' : GraphWalk K.toGraph v v := .nil hvK
  refine ⟨v, W', ⟨hψ, Or.inl ⟨hzero, rfl, hvK, r, hr, hψsub, hvr⟩⟩, ?_, ?_⟩
  · intro x hx
    rw [walkDrawing_V] at hx
    have hxv : x = v := by simpa only [W', GraphWalk.support, List.mem_singleton, mem_ofPred_eq] using hx
    exact hxv.symm ▸ hvdraw
  · intro e he
    rw [walkDrawing_E] at he
    simp only [W', GraphWalk.edges, List.not_mem_nil, mem_ofPred_eq] at he

end GraphMinor.GM12
