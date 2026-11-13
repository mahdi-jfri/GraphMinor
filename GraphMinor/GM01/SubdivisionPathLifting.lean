module

public import GraphMinor.GM01.SubdivisionSides
public import Mathlib.Combinatorics.SimpleGraph.Walk.Operations
import Mathlib.Combinatorics.SimpleGraph.Paths

/-!
# Lifting a source path through its subdivision

The leaf-chain cover in Graph Minors I, page 60, must cover whole
replacing paths, including their interior vertices. Concatenate the
replacing paths along a source path. Different replacing paths meet
only at centres, and the source path has no repeated vertex, so each
concatenation meets only at its joining end.
-/

public section

namespace GraphMinor.GM01

open Set Graph SimpleGraph Function GraphMinor.GM09 GraphMinor.Surface

/-- A source path lifts to a path containing every replacing path
along it. This is the path-lifting step in the page-60 leaf cover. -/
theorem exists_subdivision_path_lift {α β ν : Type*} {S : SimpleGraph ν}
    {N : Graph α β} {c : ν → α} (hc : Injective c)
    (hcentres : ∀ v, c v ∈ V(N)) {P : S.edgeSet → Graph α β}
    (hPaths : ∀ e : S.edgeSet, ∃ a b, e.val = s(a,b) ∧
      IsGraphPathWithEnds N (P e) (c a) (c b) ∧ V(P e) ∩ range c = {c a,c b})
    (hInter : ∀ e f : S.edgeSet, e ≠ f → V(P e) ∩ V(P f) ⊆ range c)
    {a b : ν} (p : S.Walk a b) (hp : p.support.Nodup) :
    ∃ Q : Graph α β, IsGraphPathWithEnds N Q (c a) (c b) ∧
      (∀ v, c v ∈ V(Q) ↔ v ∈ p.support) ∧
      (∀ e : S.edgeSet, e.val ∈ p.edges → V(P e) ⊆ V(Q)) ∧
      V(Q) ⊆ range c ∪ ⋃ e : S.edgeSet, ⋃ (_ : e.val ∈ p.edges), V(P e) := by
  have hRanges : ∀ e : S.edgeSet, ∃ x y, e.val = s(x,y) ∧
      V(P e) ∩ range c = {c x,c y} := by
    intro e
    obtain ⟨x, y, he, _, hR⟩ := hPaths e
    exact ⟨x, y, he, hR⟩
  induction p with
  | @nil a =>
    obtain ⟨Q, hQ, hV, _⟩ := exists_isGraphPathWithEnds_of_walk (GraphWalk.nil (hcentres a))
    have hVQ : V(Q) = {c a} := by
      apply Subset.antisymm
      · intro x hx
        exact (List.mem_singleton.mp (hV hx))
      · exact singleton_subset_iff.mpr hQ.left_mem
    refine ⟨Q, hQ, ?_, ?_, ?_⟩
    · intro v
      simp only [hVQ, mem_singleton_iff, hc.eq_iff, SimpleGraph.Walk.support_nil,
        List.mem_singleton]
    · intro e he
      exact False.elim (List.not_mem_nil he)
    · intro x hx
      rw [hVQ] at hx
      have heq : x = c a := hx
      exact Or.inl ⟨a, heq.symm⟩
  | @cons a d b had p ih =>
    have hNodup := List.nodup_cons.mp hp
    obtain ⟨Q, hQ, hCQ, hPQ, hCover⟩ := ih hNodup.2
    let e : S.edgeSet := ⟨s(a,d), had⟩
    have hPe : IsGraphPathWithEnds N (P e) (c a) (c d) := by
      obtain ⟨x, y, he, hPath, _⟩ := hPaths e
      have heq : s(a,d) = s(x,y) := he
      rcases Sym2.eq_iff.mp heq with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
      · exact hPath
      · exact hPath.symm
    have heNot : e.val ∉ p.edges := by
      intro he
      exact hNodup.1 (p.fst_mem_support_of_mem_edges he)
    have haNot : c a ∉ V(Q) := fun h ↦ hNodup.1 ((hCQ a).mp h)
    have hMeet : V(P e) ∩ V(Q) = {c d} := by
      apply Subset.antisymm
      · rintro x ⟨hxP, hxQ⟩
        have hxRange : x ∈ range c := by
          rcases hCover hxQ with hx | hx
          · exact hx
          · obtain ⟨f, hf⟩ := mem_iUnion.mp hx
            obtain ⟨hfEdge, hxf⟩ := mem_iUnion.mp hf
            have hne : e ≠ f := fun heq ↦ heNot (heq ▸ hfEdge)
            exact hInter e f hne ⟨hxP, hxf⟩
        obtain ⟨v, rfl⟩ := hxRange
        have hv := (subdivision_centre_mem_path_iff hc hRanges e v).mp hxP
        rcases Sym2.mem_iff.mp hv with rfl | rfl
        · exact False.elim (haNot hxQ)
        · exact mem_singleton _
      · refine singleton_subset_iff.mpr ⟨hPe.right_mem, ?_⟩
        exact (hCQ d).mpr p.start_mem_support
    let Q' := subgraphUnion N (P e) Q
    have hQ' := hPe.subgraphUnion hQ hMeet
    refine ⟨Q', hQ', ?_, ?_, ?_⟩
    · intro v
      change (c v ∈ V(P e) ∨ c v ∈ V(Q)) ↔ v ∈ a :: p.support
      rw [subdivision_centre_mem_path_iff hc hRanges, hCQ]
      change (v ∈ s(a,d) ∨ v ∈ p.support) ↔ v ∈ a :: p.support
      simp only [Sym2.mem_iff, List.mem_cons]
      constructor
      · rintro ((h | h) | h)
        · exact Or.inl h
        · exact Or.inr (h ▸ p.start_mem_support)
        · exact Or.inr h
      · rintro (h | h)
        · exact Or.inl (Or.inl h)
        · exact Or.inr h
    · intro f hf x hx
      change x ∈ V(P e) ∨ x ∈ V(Q)
      rcases List.mem_cons.mp hf with heq | hf
      · have hfe : f = e := Subtype.ext heq
        exact Or.inl (hfe ▸ hx)
      · exact Or.inr (hPQ f hf hx)
    · intro x hx
      change x ∈ V(P e) ∨ x ∈ V(Q) at hx
      rcases hx with hx | hx
      · exact Or.inr (mem_iUnion.mpr ⟨e, mem_iUnion.mpr ⟨List.mem_cons_self, hx⟩⟩)
      · rcases hCover hx with hx | hx
        · exact Or.inl hx
        · obtain ⟨f, hf⟩ := mem_iUnion.mp hx
          obtain ⟨hfEdge, hxf⟩ := mem_iUnion.mp hf
          exact Or.inr (mem_iUnion.mpr ⟨f, mem_iUnion.mpr ⟨List.mem_cons_of_mem _ hfEdge, hxf⟩⟩)

end GraphMinor.GM01
