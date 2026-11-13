module

public import GraphMinor.GM01.SubdivisionMinor
public import GraphMinor.GM01.SubdivisionEmbeddingEdges

/-!
# Restricting a subdivision to an embedded source

For the last-block assertion in Graph Minors I, (4.1), page 55, retain the
replacing paths of an embedded consecutive subcomb. Distinct selected
edges remain distinct. The only original centres on a selected path are
its two ends, both of which are selected centres. Thus the selected paths
still give a subdivision of the smaller source. If all selected paths
and centres lie in a vertex set, the resulting minor lies in its induced
graph.
-/

public section

namespace GraphMinor.GM01

open Set Graph SimpleGraph Function GraphMinor.GM09

/-- Selected replacing paths retain the subdivision intersection properties
and lie in the specified induced target graph. -/
theorem subdivision_restriction_paths {α β ν μ : Type*}
    {S : SimpleGraph ν} {T : SimpleGraph μ}
    {G : Graph α β} (f : ν ↪ μ)
    (hf : ∀ {a b}, S.Adj a b → T.Adj (f a) (f b))
    (c : μ → α) (D : Set α)
    (P : T.edgeSet → Graph α β)
    (hPaths : ∀ e : T.edgeSet, ∃ a b, e.val = s(a,b) ∧
      IsGraphPathWithEnds G (P e) (c a) (c b) ∧
      V(P e) ∩ range c = {c a,c b})
    (hInter : ∀ e e' : T.edgeSet, e ≠ e' →
      V(P e) ∩ V(P e') ⊆ range c ∧ Disjoint E(P e) E(P e'))
    (hD : ∀ e : S.edgeSet, V(P (subdivisionEmbeddingEdges f hf e)) ⊆ D) :
    (∀ e : S.edgeSet, ∃ a b, e.val = s(a,b) ∧
      IsGraphPathWithEnds (G.induce D) (P (subdivisionEmbeddingEdges f hf e)) (c (f a)) (c (f b)) ∧
      V(P (subdivisionEmbeddingEdges f hf e)) ∩ range (fun v ↦ c (f v)) = {c (f a),c (f b)}) ∧
    (∀ e e' : S.edgeSet, e ≠ e' →
      V(P (subdivisionEmbeddingEdges f hf e)) ∩ V(P (subdivisionEmbeddingEdges f hf e')) ⊆
        range (fun v ↦ c (f v)) ∧
      Disjoint E(P (subdivisionEmbeddingEdges f hf e)) E(P (subdivisionEmbeddingEdges f hf e'))) := by
  let mapEdge := subdivisionEmbeddingEdges f hf
  let centres : ν → α := fun v ↦ c (f v)
  let paths (e : S.edgeSet) := P (mapEdge e)
  have hEnds : ∀ e : S.edgeSet, ∃ a b, e.val = s(a,b) := by
    rintro ⟨edge, he⟩
    induction edge using Sym2.inductionOn with
    | hf a b => exact ⟨a, b, rfl⟩
  have bigPath : ∀ (e : S.edgeSet) (a b : ν), e.val = s(a,b) →
      IsGraphPathWithEnds G (paths e) (centres a) (centres b) ∧
      V(paths e) ∩ range c = {centres a,centres b} := by
    intro e a b he
    obtain ⟨a', b', he', hP, hRange⟩ := hPaths (mapEdge e)
    have hpair : s(f a,f b) = s(a',b') :=
      (subdivisionEmbeddingEdges_ends f hf he).symm.trans he'
    rcases Sym2.eq_iff.mp hpair with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact ⟨hP, hRange⟩
    · exact ⟨hP.symm, by simpa only [pair_comm] using hRange⟩
  have smallPath : ∀ e : S.edgeSet, ∃ a b, e.val = s(a,b) ∧
      IsGraphPathWithEnds (G.induce D) (paths e) (centres a) (centres b) ∧
      V(paths e) ∩ range centres = {centres a,centres b} := by
    intro e
    obtain ⟨a, b, he⟩ := hEnds e
    obtain ⟨hP, hRange⟩ := bigPath e a b he
    have hPD : paths e ≤ G.induce D := by
      refine ⟨hD e, ?_⟩
      intro edge x y hxy
      exact ⟨hxy.mono hP.le, hD e hxy.left_mem, hD e hxy.right_mem⟩
    refine ⟨a, b, he, hP.of_le hPD, Subset.antisymm ?_ ?_⟩
    · intro x hx
      obtain ⟨v, hv⟩ := hx.2
      exact hRange ▸ ⟨hx.1, ⟨f v, hv⟩⟩
    · intro x hx
      rcases hx with rfl | hx
      · exact ⟨hP.left_mem, mem_range_self a⟩
      · have hxb : x = centres b := hx
        subst x
        exact ⟨hP.right_mem, mem_range_self b⟩
  have smallInter : ∀ e e' : S.edgeSet, e ≠ e' →
      V(paths e) ∩ V(paths e') ⊆ range centres ∧ Disjoint E(paths e) E(paths e') := by
    intro e e' hne
    have hne' : mapEdge e ≠ mapEdge e' := mapEdge.injective.ne hne
    obtain ⟨hVert, hEdge⟩ := hInter (mapEdge e) (mapEdge e') hne'
    refine ⟨?_, hEdge⟩
    intro x hx
    obtain ⟨a, b, he⟩ := hEnds e
    have hRange := (bigPath e a b he).2
    have hm : x ∈ ({centres a,centres b} : Set α) := hRange ▸ ⟨hx.1, hVert hx⟩
    rcases hm with rfl | hm
    · exact mem_range_self a
    · have hxb : x = centres b := hm
      exact hxb ▸ mem_range_self b
  exact ⟨smallPath, smallInter⟩

/-- Restrict the replacing paths to an embedded finite source and to an
induced target set containing them. This constructs the tail minor used
in GM01 (4.1) from the actual selected paths. -/
theorem exists_minorModel_of_subdivision_restriction {α β ν μ : Type*}
    [Finite ν] [Nonempty β] {S : SimpleGraph ν} {T : SimpleGraph μ}
    {G : Graph α β} (f : ν ↪ μ)
    (hf : ∀ {a b}, S.Adj a b → T.Adj (f a) (f b))
    (c : μ → α) (hc : Injective c) (D : Set α)
    (hcentres : ∀ v, c (f v) ∈ V(G) ∩ D) (P : T.edgeSet → Graph α β)
    (hPaths : ∀ e : T.edgeSet, ∃ a b, e.val = s(a,b) ∧
      IsGraphPathWithEnds G (P e) (c a) (c b) ∧
      V(P e) ∩ range c = {c a,c b})
    (hInter : ∀ e e' : T.edgeSet, e ≠ e' →
      V(P e) ∩ V(P e') ⊆ range c ∧ Disjoint E(P e) E(P e'))
    (hD : ∀ e : S.edgeSet, V(P (subdivisionEmbeddingEdges f hf e)) ⊆ D) :
    ∃ (ηv : ν → Set α) (ηe : Sym2 ν → β),
      IsMinorModel (Graph.ofSimpleGraph S) (G.induce D) ηv ηe := by
  obtain ⟨hP, hI⟩ := subdivision_restriction_paths f hf c D P hPaths hInter hD
  obtain ⟨ηv, ηe, hmodel, _⟩ := exists_minorModel_of_finite_subdivision
    (fun v ↦ c (f v)) (hc.comp f.injective) (fun v ↦ (hcentres v).2)
    (fun e ↦ P (subdivisionEmbeddingEdges f hf e)) hP hI
  exact ⟨ηv, ηe, hmodel⟩

end GraphMinor.GM01
