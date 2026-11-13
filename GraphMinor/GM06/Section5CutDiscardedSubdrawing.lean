module

public import GraphMinor.GM06.Defs
import GraphMinor.GM06.Section5SeparationGeometry
import GraphMinor.GM11.Walks

/-!
# The discarded cut subdrawing with one isolated copy removed

For the one-path Reduction 2 argument of VI (5.5), page 130,
retain the lifted discarded edges and all lifted discarded vertices
except the clockwise initial copy. No retained edge is incident
with that copy. Spanning these data gives an actual subdrawing
whose point set is precisely the discarded preimage with that
isolated copy removed. This also proves that this punctured
preimage is closed.
-/

public section
namespace GraphMinor.GM06
open Set Topology GraphMinor.Surface

/-- A pullback subdrawing whose edges miss one isolated vertex
copy remains a drawing after that copy is removed. -/
theorem exists_discarded_cut_subdrawing_without_isolated_copy
    {X Y : Type*} [TopologicalSpace X] [T2Space X] [TopologicalSpace Y] [T2Space Y]
    (f : X → Y) (hf : Continuous f) {F : Drawing X} {G H : Drawing Y}
    (hHG : H.IsSubdrawing G) (hFV : F.V = f ⁻¹' G.V)
    (hcover : f ⁻¹' H.U ⊆ F.U) (B : Set X)
    (hB : (f ⁻¹' H.U) ∩ B ⊆ f ⁻¹' H.V)
    (hEdges : ∀ ec ∈ F.E, ec ⊆ B ∨ ∃ e ∈ G.E, ec = f ⁻¹' e)
    (v : X)
    (hno : ∀ ec ∈ F.E, (∃ e ∈ H.E, ec = f ⁻¹' e) → v ∉ closure ec) :
    ∃ K : Drawing X, K.IsSubdrawing F ∧ K.U = (f ⁻¹' H.U) \ {v} := by
  classical
  let V := (f ⁻¹' H.V) \ {v}
  let E := {ec ∈ F.E | ∃ e ∈ H.E, ec = f ⁻¹' e}
  let K := F.span V E
  have hKF : K.IsSubdrawing F := Drawing.span_isSubdrawing F V E
  have hKE : K.E = E := by
    rw [Drawing.span_E]
    exact inter_eq_left.mpr (fun _ he => he.1)
  have hcl (ec) (hec : ec ∈ E) : closure ec ⊆ (f ⁻¹' H.U) \ {v} := by
    obtain ⟨heF, e, heH, heq⟩ := hec
    have hsub : ec ⊆ f ⁻¹' H.U := by
      rw [heq]
      exact preimage_mono (fun y hy => (heH.2.1 hy).1)
    have hc : closure ec ⊆ f ⁻¹' H.U := closure_minimal hsub (H.isClosed_U.preimage hf)
    intro x hx
    refine ⟨hc hx, ?_⟩
    intro he
    exact hno ec heF ⟨e, heH, heq⟩ (mem_singleton_iff.mp he ▸ hx)
  have hupper : K.U ⊆ (f ⁻¹' H.U) \ {v} := by
    intro x hx
    change x ∈ F.spanV V E ∪ ⋃ ec ∈ E ∩ F.E, closure ec at hx
    rcases hx with hxV | hxE
    · rw [Drawing.spanV] at hxV
      rcases hxV with ⟨hxV, _⟩ | hxends
      · exact ⟨H.V_subset_U hxV.1, hxV.2⟩
      · obtain ⟨ec, hec, hxcl, _⟩ := mem_iUnion₂.mp hxends
        exact hcl ec hec.1 hxcl
    · obtain ⟨ec, hec, hxcl⟩ := mem_iUnion₂.mp hxE
      exact hcl ec hec.1 hxcl
  refine ⟨K, hKF, subset_antisymm hupper ?_⟩
  rintro x ⟨hxH, hxv⟩
  by_cases hxHV : f x ∈ H.V
  · apply K.V_subset_U
    rw [Drawing.span_V, Drawing.spanV]
    exact Or.inl ⟨⟨hxHV, hxv⟩, hFV.symm ▸ hHG.1 hxHV⟩
  · have hxFV : x ∉ F.V := by
      intro hxF
      rw [hFV] at hxF
      exact hxHV (vertex_mem_of_mem_subdrawing_point_set hHG hxH hxF)
    obtain ⟨ec, hec, hxec⟩ := F.exists_edge_of_mem (hcover hxH) hxFV
    have heE : ec ∈ E := by
      refine ⟨hec, ?_⟩
      rcases hEdges ec hec with heB | ⟨e, heG, heq⟩
      · exact False.elim (hxHV (hB ⟨hxH, heB hxec⟩))
      · obtain ⟨eH, heH, hxeH⟩ := H.exists_edge_of_mem hxH hxHV
        have hxe : f x ∈ e := by rw [heq] at hxec; exact hxec
        have he : e = eH := G.edge_eq_of_mem heG (hHG.2 heH) hxe hxeH
        exact ⟨eH, heH, he ▸ heq⟩
    have heK : ec ∈ K.E := hKE.symm ▸ heE
    exact (heK.2.1 hxec).1

end GraphMinor.GM06
