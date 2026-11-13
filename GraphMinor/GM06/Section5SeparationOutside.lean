module

public import GraphMinor.GM06.Defs
public import Mathlib.Combinatorics.Graph.Subgraph

/-!
# The discarded side of a one-vertex separation

For the completeness of the Reduction 2 scan in VI (5.7), page 133,
a proper retained side either omits a vertex or omits a loop at
the shared initial vertex. An edge from an omitted vertex cannot
return to the retained side except at that shared vertex. These
facts reduce the search to punctured components and initial loops.
-/

public section
namespace GraphMinor.GM06
open Set

/-- An edge cannot enter the retained side from outside it except
at the single vertex shared by the two sides. -/
theorem separation_link_notMem_left {α β : Type*} {G G₁ G₂ : Graph α β} {cut a b : α} {e : β}
    (hsep : IsGraphSeparation G G₁ G₂) (hover : G₁.vertexSet ∩ G₂.vertexSet ⊆ {cut})
    (hl : G.IsLink e a b) (ha : a ∉ G₁.vertexSet) (hb : b ≠ cut) : b ∉ G₁.vertexSet := by
  have he : e ∈ G₁.edgeSet ∪ G₂.edgeSet := by rw [hsep.2.2.2.1]; exact hl.edge_mem
  rcases he with he | he
  · exact False.elim (ha ((hsep.1.isLink_iff he).mpr hl).left_mem)
  · intro hb₁
    have hb₂ := ((hsep.2.1.isLink_iff he).mpr hl).right_mem
    exact hb (hover ⟨hb₁, hb₂⟩)

/-- A proper retained side misses a vertex, or misses a loop at the
single shared vertex. This covers the two cases scanned for Reduction 2. -/
theorem proper_separation_has_outside_vertex_or_cut_loop
    {α β : Type*} {G G₁ G₂ : Graph α β} {cut : α}
    (hsep : IsGraphSeparation G G₁ G₂) (hover : G₁.vertexSet ∩ G₂.vertexSet ⊆ {cut})
    (hne : G₁ ≠ G) :
    (∃ a ∈ G.vertexSet, a ∉ G₁.vertexSet) ∨
      ∃ e, G.IsLink e cut cut ∧ e ∉ G₁.edgeSet := by
  classical
  by_cases hV : G₁.vertexSet = G.vertexSet
  · right
    have hedge : ∃ e ∈ G.edgeSet, e ∉ G₁.edgeSet := by
      by_contra! hn
      have hE : G₁.edgeSet = G.edgeSet := subset_antisymm hsep.1.edgeSet_mono hn
      exact hne (hsep.1.compatible.ext hV hE)
    obtain ⟨e, heG, heNot⟩ := hedge
    have he₂ : e ∈ G₂.edgeSet := by
      have he : e ∈ G₁.edgeSet ∪ G₂.edgeSet := by rw [hsep.2.2.2.1]; exact heG
      exact he.resolve_left heNot
    obtain ⟨a, b, hl₂⟩ := G₂.exists_isLink_of_mem_edgeSet he₂
    have hl := hl₂.mono hsep.2.1
    have ha : a = cut := hover ⟨hV.symm ▸ hl.left_mem, hl₂.left_mem⟩
    have hb : b = cut := hover ⟨hV.symm ▸ hl.right_mem, hl₂.right_mem⟩
    exact ⟨e, by simpa only [ha, hb] using hl, heNot⟩
  · left
    by_contra! hn
    exact hV (subset_antisymm hsep.1.vertexSet_mono hn)

end GraphMinor.GM06
