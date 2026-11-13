module

public import GraphMinor.Surface.SurfaceGraph
import Mathlib.Topology.Separation.Basic
import Mathlib.Tactic.NormNum

/-!
# A face boundary lies in the edge union

Removing finitely many points from a circle leaves a dense subset.
Thus a circle contained in a finite graph cannot use isolated vertices
without lying on edges. This places lifted face boundaries in the
lifted edge union when assembling the dissection for VIII (18.2).
-/

public section

namespace GraphMinor.GM08

open Set Topology GraphMinor.Surface

/-- Removing finitely many points from a circle does not change its
closure. This supplies the boundary coverage step in VIII (18.2). -/
theorem oArc_subset_closure_sdiff_finite {S : Type*} [TopologicalSpace S]
    {F P : Set S} (hF : IsOArc F) (hP : P.Finite) : F ⊆ closure (F \ P) := by
  have : Nontrivial Circle := ⟨⟨1, -1, by
    intro h
    have hh := congrArg (fun z : Circle => (z : ℂ)) h
    norm_num at hh⟩⟩
  obtain ⟨φ⟩ := hF
  let f : Circle → S := fun z => (φ z).1
  have hf : Continuous f := continuous_subtype_val.comp φ.continuous
  have hinj : Function.Injective f := fun x y hxy => φ.injective (Subtype.ext hxy)
  have hbad : (f ⁻¹' P).Finite := hP.preimage hinj.injOn
  have hdense : Dense ((univ : Set Circle) \ f ⁻¹' P) := dense_univ.sdiff_finite hbad
  have hsub : f '' ((univ : Set Circle) \ f ⁻¹' P) ⊆ F \ P := by
    rintro x ⟨z, hz, rfl⟩
    exact ⟨(φ z).2, hz.2⟩
  intro x hx
  have hfx : f (φ.symm ⟨x, hx⟩) = x := congrArg Subtype.val (φ.apply_symm_apply ⟨x, hx⟩)
  have hximage : x ∈ f '' closure ((univ : Set Circle) \ f ⁻¹' P) :=
    ⟨φ.symm ⟨x, hx⟩, hdense _, hfx⟩
  exact closure_mono hsub ((image_closure_subset_closure_image hf) hximage)

/-- A circle contained in a finite graph lies in its edge union.
This places the whole boundary of each lifted face on lifted edges in
VIII (18.2), page 286, including its lifted vertex points. -/
theorem oArc_subset_edges_of_subset_graph {S : Type*} [TopologicalSpace S] [T2Space S]
    {V F : Set S} {E : Set (Set S)} (hg : IsGraph V E) (hF : IsOArc F)
    (hsub : F ⊆ gr V E) : F ⊆ ⋃₀ E := by
  have hclosed : IsClosed (⋃₀ E) := hg.fine.isClosed_sUnion (fun e he => by
    obtain ⟨u, v, _, hline, _⟩ := hg.edge e he
    exact hline.isCompact.isClosed)
  have hoff : F \ V ⊆ ⋃₀ E := by
    rintro x ⟨hxF, hxV⟩
    exact (hsub hxF).resolve_left hxV
  exact (oArc_subset_closure_sdiff_finite hF hg.fin).trans (closure_minimal hoff hclosed)

end GraphMinor.GM08
