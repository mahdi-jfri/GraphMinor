module

public import GraphMinor.GM01.SubdivisionSides
public import GraphMinor.GM01.SubdivisionEmbeddingEdges

/-!
# A boundary path meets the selected subdivision only at its end

The boundary path into the skipped block of Graph Minors I, (4.1), page 55,
represents an edge with one end outside the selected two-cell source and
one end at its first spine vertex. It meets a selected replacing path
only at source centres. Its outside end is not a selected centre, and
cannot be an end of a selected edge. Thus its only vertex in the support
of the selected subdivision is the chosen attachment centre.
-/

public section

namespace GraphMinor.GM01

open Set Graph SimpleGraph Function

/-- The source boundary edge attaches to the selected subdivision at
exactly its selected end. The equality records the whole selected support,
not just its centres, for the contraction in GM01 (4.1). -/
theorem selected_subdivision_boundary_intersection {α β ν μ : Type*}
    {S : SimpleGraph ν} {T : SimpleGraph μ} (f : ν ↪ μ)
    (hf : ∀ {a b}, S.Adj a b → T.Adj (f a) (f b))
    {c : μ → α} (hc : Injective c) (P : T.edgeSet → Graph α β)
    (hRanges : ∀ e : T.edgeSet, ∃ a b, e.val = s(a,b) ∧
      V(P e) ∩ range c = {c a,c b})
    (hInter : ∀ e e' : T.edgeSet, e ≠ e' → V(P e) ∩ V(P e') ⊆ range c)
    (root : ν) (a : μ) (ha : a ∉ range f) (boundary : T.edgeSet)
    (hBoundary : boundary.val = s(a,f root)) :
    V(P boundary) ∩ (range (fun v ↦ c (f v)) ∪
      ⋃ e : S.edgeSet, V(P (subdivisionEmbeddingEdges f hf e))) = {c (f root)} := by
  have hselected : ∀ (e : S.edgeSet) (v : μ),
      v ∈ (subdivisionEmbeddingEdges f hf e).val → v ∈ range f := by
    intro e v hv
    obtain ⟨w, _, hw⟩ := Sym2.mem_map.mp hv
    exact ⟨w, hw⟩
  have hdistinct : ∀ e : S.edgeSet, boundary ≠ subdivisionEmbeddingEdges f hf e := by
    intro e heq
    have hamem : a ∈ boundary.val := hBoundary.symm ▸ Sym2.mem_mk_left a (f root)
    exact ha (hselected e a (heq ▸ hamem))
  apply Subset.antisymm
  · intro x hx
    rcases hx.2 with ⟨v, hv⟩ | hxSelected
    · change c (f v) = x at hv
      have hxP : c (f v) ∈ V(P boundary) := hv.symm ▸ hx.1
      have hmem := (subdivision_centre_mem_path_iff hc hRanges boundary (f v)).mp hxP
      rw [hBoundary, Sym2.mem_iff] at hmem
      rcases hmem with h | h
      · exact False.elim (ha ⟨v, h⟩)
      · exact mem_singleton_iff.mpr (hv.symm.trans (congrArg c h))
    · obtain ⟨e, hxe⟩ := mem_iUnion.mp hxSelected
      obtain ⟨v, hv⟩ := hInter boundary (subdivisionEmbeddingEdges f hf e) (hdistinct e) ⟨hx.1, hxe⟩
      have hxP : c v ∈ V(P boundary) := hv.symm ▸ hx.1
      have hmem := (subdivision_centre_mem_path_iff hc hRanges boundary v).mp hxP
      rw [hBoundary, Sym2.mem_iff] at hmem
      rcases hmem with h | h
      · have hselectedCentre : c a ∈ V(P (subdivisionEmbeddingEdges f hf e)) :=
          (congrArg c h) ▸ (hv.symm ▸ hxe)
        have hamem := (subdivision_centre_mem_path_iff hc hRanges
          (subdivisionEmbeddingEdges f hf e) a).mp hselectedCentre
        exact False.elim (ha (hselected e a hamem))
      · exact mem_singleton_iff.mpr (hv.symm.trans (congrArg c h))
  · intro x hx
    have heq : x = c (f root) := hx
    subst x
    refine ⟨?_, Or.inl (mem_range_self root)⟩
    apply (subdivision_centre_mem_path_iff hc hRanges boundary (f root)).mpr
    rw [hBoundary]
    exact Sym2.mem_mk_right a (f root)

end GraphMinor.GM01
