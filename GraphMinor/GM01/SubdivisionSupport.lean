module

public import GraphMinor.GM01.SubdivisionSides
public import GraphMinor.GM01.SubdivisionEmbeddingEdges

/-!
# Supports of selected parts of a subdivision

Graph Minors I, page 58, defines the two ends of the layer subdivision
by selecting its first or last two spine cells and the paths inside
those cells. The support consists of the selected centres and selected
replacing paths. Disjoint source selections have disjoint supports:
any intersection of distinct replacing paths is a source centre, and
that centre would have to be selected on both sides.
-/

@[expose] public section

namespace GraphMinor.GM01

open Set Graph SimpleGraph Function

/-- Centres and replacing paths selected by a source embedding, as in
the first and second ends defined on page 58 of Graph Minors I. -/
def subdivisionEmbeddingSupport {α β ν μ : Type*} {S : SimpleGraph ν} {T : SimpleGraph μ}
    (f : ν ↪ μ) (hf : ∀ {a b}, S.Adj a b → T.Adj (f a) (f b))
    (c : μ → α) (P : T.edgeSet → Graph α β) : Set α :=
  range (fun v ↦ c (f v)) ∪ ⋃ e : S.edgeSet, V(P (subdivisionEmbeddingEdges f hf e))

/-- Every end of a selected edge is a selected source vertex. -/
theorem subdivisionEmbeddingEdges_mem_range {ν μ : Type*} {S : SimpleGraph ν} {T : SimpleGraph μ}
    (f : ν ↪ μ) (hf : ∀ {a b}, S.Adj a b → T.Adj (f a) (f b))
    (e : S.edgeSet) {v : μ} (hv : v ∈ (subdivisionEmbeddingEdges f hf e).val) : v ∈ range f := by
  obtain ⟨w, _, hw⟩ := Sym2.mem_map.mp hv
  exact ⟨w, hw⟩

/-- A source centre belongs to the selected support exactly when its
source vertex is selected. -/
theorem subdivisionEmbeddingSupport_centre_iff {α β ν μ : Type*}
    {S : SimpleGraph ν} {T : SimpleGraph μ}
    (f : ν ↪ μ) (hf : ∀ {a b}, S.Adj a b → T.Adj (f a) (f b))
    {c : μ → α} (hc : Injective c) (P : T.edgeSet → Graph α β)
    (hRanges : ∀ e : T.edgeSet, ∃ a b, e.val = s(a,b) ∧ V(P e) ∩ range c = {c a,c b})
    (v : μ) : c v ∈ subdivisionEmbeddingSupport f hf c P ↔ v ∈ range f := by
  constructor
  · intro hx
    rcases hx with ⟨w, hw⟩ | hxPath
    · exact ⟨w, hc hw⟩
    · obtain ⟨e, hxe⟩ := Set.mem_iUnion.mp hxPath
      have hv := (subdivision_centre_mem_path_iff hc hRanges _ v).mp hxe
      exact subdivisionEmbeddingEdges_mem_range f hf e hv
  · rintro ⟨w, rfl⟩
    exact Or.inl (mem_range_self w)

/-- Disjoint source selections have disjoint subdivision supports.
This gives disjointness of the two ends used in GM01 (4.13), page 59,
and the arm disjointness in the contraction for (4.9), page 58. -/
theorem disjoint_subdivisionEmbeddingSupports {α β ν κ μ : Type*}
    {S : SimpleGraph ν} {U : SimpleGraph κ} {T : SimpleGraph μ}
    (f : ν ↪ μ) (hf : ∀ {a b}, S.Adj a b → T.Adj (f a) (f b))
    (g : κ ↪ μ) (hg : ∀ {a b}, U.Adj a b → T.Adj (g a) (g b))
    (hfg : Disjoint (range f) (range g))
    {c : μ → α} (hc : Injective c) (P : T.edgeSet → Graph α β)
    (hRanges : ∀ e : T.edgeSet, ∃ a b, e.val = s(a,b) ∧ V(P e) ∩ range c = {c a,c b})
    (hInter : ∀ e e' : T.edgeSet, e ≠ e' → V(P e) ∩ V(P e') ⊆ range c) :
    Disjoint (subdivisionEmbeddingSupport f hf c P) (subdivisionEmbeddingSupport g hg c P) := by
  classical
  apply Set.disjoint_left.mpr
  intro x hxf hxg
  have hxNot : x ∉ range c := by
    rintro ⟨v, rfl⟩
    exact Set.disjoint_left.mp hfg
      ((subdivisionEmbeddingSupport_centre_iff f hf hc P hRanges v).mp hxf)
      ((subdivisionEmbeddingSupport_centre_iff g hg hc P hRanges v).mp hxg)
  have hxfPath : ∃ e : S.edgeSet, x ∈ V(P (subdivisionEmbeddingEdges f hf e)) := by
    rcases hxf with ⟨v, hv⟩ | h
    · exact False.elim (hxNot ⟨f v, hv⟩)
    · exact Set.mem_iUnion.mp h
  have hxgPath : ∃ e : U.edgeSet, x ∈ V(P (subdivisionEmbeddingEdges g hg e)) := by
    rcases hxg with ⟨v, hv⟩ | h
    · exact False.elim (hxNot ⟨g v, hv⟩)
    · exact Set.mem_iUnion.mp h
  obtain ⟨e, hxe⟩ := hxfPath
  obtain ⟨e', hxe'⟩ := hxgPath
  have hne : subdivisionEmbeddingEdges f hf e ≠ subdivisionEmbeddingEdges g hg e' := by
    intro heq
    have hex : ∃ v, v ∈ (subdivisionEmbeddingEdges f hf e).val :=
      Sym2.inductionOn (subdivisionEmbeddingEdges f hf e).val (fun a b ↦ ⟨a, Sym2.mem_mk_left a b⟩)
    obtain ⟨v, hv⟩ := hex
    exact Set.disjoint_left.mp hfg (subdivisionEmbeddingEdges_mem_range f hf e hv)
      (subdivisionEmbeddingEdges_mem_range g hg e' (heq ▸ hv))
  exact hxNot (hInter _ _ hne ⟨hxe, hxe'⟩)

end GraphMinor.GM01
