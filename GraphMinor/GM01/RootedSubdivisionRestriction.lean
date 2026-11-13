module

public import GraphMinor.GM01.SubdivisionRestriction
public import GraphMinor.GM01.RootedSubdivisionMinor
import GraphMinor.GM16.GraphPathSystemUnion

/-!
# Retaining a chosen root in the selected subdivision

The skipped-block minor in Graph Minors I, (4.1), page 55, must attach
at its first spine centre. The selected-path lemma supplies a subdivision
inside the induced block. Its root-preserving contraction then gives the
rooted model at that specified centre. No arbitrary rooting or choice
of source root is needed.
-/

public section

namespace GraphMinor.GM01

open Set Graph SimpleGraph Function GraphMinor.GM09

/-- The rooted version of selecting an embedded finite subdivision.
The chosen source centre is retained as the target root in the induced
graph, as required for the skipped block in GM01 (4.1). -/
theorem rooted_minor_of_subdivision_restriction {α β ν μ : Type*} [Finite ν]
    {S : SimpleGraph ν} {T : SimpleGraph μ} {G : Graph α β} (f : ν ↪ μ)
    (hf : ∀ {a b}, S.Adj a b → T.Adj (f a) (f b))
    (c : μ → α) (hc : Injective c) (D : Set α)
    (hcentres : ∀ v, c (f v) ∈ V(G) ∩ D) (P : T.edgeSet → Graph α β)
    (hPaths : ∀ e : T.edgeSet, ∃ a b, e.val = s(a,b) ∧
      IsGraphPathWithEnds G (P e) (c a) (c b) ∧
      V(P e) ∩ range c = {c a,c b})
    (hInter : ∀ e e' : T.edgeSet, e ≠ e' →
      V(P e) ∩ V(P e') ⊆ range c ∧ Disjoint E(P e) E(P e'))
    (hD : ∀ e : S.edgeSet, V(P (subdivisionEmbeddingEdges f hf e)) ⊆ D) (root : ν) :
    HasRootedMinor
      (⟨Graph.ofSimpleGraph S, ⟨root, mem_univ _⟩⟩ : RootedGraph ν (Sym2 ν))
      (⟨G.induce D, ⟨c (f root), (hcentres root).2⟩⟩ : RootedGraph α β) := by
  obtain ⟨hP, hI⟩ := subdivision_restriction_paths f hf c D P hPaths hInter hD
  exact ⟨rootedModelOfFiniteSubdivision (fun v ↦ c (f v)) (hc.comp f.injective)
    (fun v ↦ (hcentres v).2) (fun e ↦ P (subdivisionEmbeddingEdges f hf e)) hP
    (fun e e' hne ↦ (hI e e' hne).1) root⟩

/-- The selected rooted minor can be kept in the union of its centres
and replacing paths. Recording this actual support lets the later
attachment paths avoid every nonroot branch. -/
theorem exists_supported_rooted_subdivision_restriction {α β ν μ : Type*} [Finite ν]
    {S : SimpleGraph ν} {T : SimpleGraph μ} {G : Graph α β} (f : ν ↪ μ)
    (hf : ∀ {a b}, S.Adj a b → T.Adj (f a) (f b))
    (c : μ → α) (hc : Injective c) (D : Set α)
    (hcentres : ∀ v, c (f v) ∈ V(G) ∩ D) (P : T.edgeSet → Graph α β)
    (hPaths : ∀ e : T.edgeSet, ∃ a b, e.val = s(a,b) ∧
      IsGraphPathWithEnds G (P e) (c a) (c b) ∧
      V(P e) ∩ range c = {c a,c b})
    (hInter : ∀ e e' : T.edgeSet, e ≠ e' →
      V(P e) ∩ V(P e') ⊆ range c ∧ Disjoint E(P e) E(P e'))
    (hD : ∀ e : S.edgeSet, V(P (subdivisionEmbeddingEdges f hf e)) ⊆ D) (root : ν) :
    ∃ K : Graph α β, K ≤ G.induce D ∧
      V(K) = range (fun v ↦ c (f v)) ∪ ⋃ e : S.edgeSet, V(P (subdivisionEmbeddingEdges f hf e)) ∧
      ∃ hroot : c (f root) ∈ V(K), HasRootedMinor
        (⟨Graph.ofSimpleGraph S, ⟨root, mem_univ _⟩⟩ : RootedGraph ν (Sym2 ν))
        (⟨K, ⟨c (f root), hroot⟩⟩ : RootedGraph α β) := by
  obtain ⟨hP, hI⟩ := subdivision_restriction_paths f hf c D P hPaths hInter hD
  let centres := fun v ↦ c (f v)
  let paths := fun e : S.edgeSet ↦ P (subdivisionEmbeddingEdges f hf e)
  have hPathsLe : ∀ e, paths e ≤ G.induce D := by
    intro e
    obtain ⟨_, _, _, hPath, _⟩ := hP e
    exact hPath.le
  let K := GraphMinor.GM16.pathSystemGraph (G.induce D) (range centres) paths
  have hC : range centres ⊆ V(G.induce D) := by
    rintro x ⟨v, rfl⟩
    exact (hcentres v).2
  have hK := GraphMinor.GM16.pathSystemGraph_le hC hPathsLe
  have hCK : ∀ v, centres v ∈ V(K) := fun v ↦ Or.inl (mem_range_self v)
  have hPK : ∀ e : S.edgeSet, ∃ a b, e.val = s(a,b) ∧
      IsGraphPathWithEnds K (paths e) (centres a) (centres b) ∧
      V(paths e) ∩ range centres = {centres a,centres b} := by
    intro e
    obtain ⟨a, b, he, hPath, hRange⟩ := hP e
    exact ⟨a, b, he, hPath.of_le (GraphMinor.GM16.le_pathSystemGraph hPathsLe e), hRange⟩
  refine ⟨K, hK, GraphMinor.GM16.pathSystemGraph_vertexSet _ _ _, hCK root, ?_⟩
  exact ⟨rootedModelOfFiniteSubdivision centres (hc.comp f.injective) hCK paths hPK
    (fun e e' hne ↦ (hI e e' hne).1) root⟩

end GraphMinor.GM01
