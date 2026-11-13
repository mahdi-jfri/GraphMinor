module

public import GraphMinor.Compute.GM02InjectedPattern
public import GraphMinor.Compute.GM02TopologicalInputFacts

/-!
# The isomorphism of an injected pattern

Replacing every edge end by its image under an injection preserves the
whole pattern. The vertex map is that injection and the edge map keeps
each edge's original list position, so repeated edges stay distinct.
-/

public section
namespace GraphMinor.Compute
open Graph Set Classical

/-- The vertex injection gives a bijection onto the supplied pattern vertices. -/
@[expose] noncomputable def gm02InjectedVertexEquiv (G H : GM02EdgeListInput)
    (f : Fin H.n ↪ Fin G.n) : V(H.graph) ≃ V((gm02InjectedPattern G H f).H) :=
  Equiv.ofBijective
    (fun v => ⟨(f ⟨v.val, v.property⟩).val,
      Finset.mem_image.2 ⟨_, Finset.mem_image.2 ⟨_, Finset.mem_univ _, rfl⟩, rfl⟩⟩)
    (by
      constructor
      · intro a b hab
        apply Subtype.ext
        exact congrArg Fin.val (f.injective (Fin.ext (congrArg Subtype.val hab)))
      · intro v
        obtain ⟨a, ha, hv⟩ := Finset.mem_image.1 v.property
        obtain ⟨b, _, hb⟩ := Finset.mem_image.1 ha
        refine ⟨⟨b.val, b.isLt⟩, ?_⟩
        apply Subtype.ext
        exact (congrArg Fin.val hb).trans hv)

/-- The injected pattern is isomorphic to its fixed original, by the injection on vertices and identity on edge positions. -/
@[expose] noncomputable def gm02InjectedPatternIso (G H : GM02EdgeListInput)
    (f : Fin H.n ↪ Fin G.n) : Iso H.graph (gm02InjectedPattern G H f).H where
  vertexEquiv := gm02InjectedVertexEquiv G H f
  edgeEquiv := {
    toFun := fun e => ⟨e.val, by
      apply (gm02InjectedPattern G H f).pattern_edges.ge
      simpa only [GM02EdgeListInput.graph_edges, gm02InjectedPattern_edges_length] using e.property⟩
    invFun := fun e => ⟨e.val, by
      have h := (gm02InjectedPattern G H f).pattern_edges.le e.property
      simpa only [GM02EdgeListInput.graph_edges, gm02InjectedPattern_edges_length] using h⟩
    left_inv := fun _ => rfl
    right_inv := fun _ => rfl }
  isLink_iff := by
    intro e a b
    have he : e.val < H.edges.length := e.property
    have hej : e.val < (gm02InjectedPattern G H f).edges.length := by
      simpa only [gm02InjectedPattern_edges_length] using he
    have hmap : (gm02InjectedPattern G H f).edges[e.val]'hej =
        (f (H.edges[e.val]'he).1, f (H.edges[e.val]'he).2) := by
      simp only [gm02InjectedPattern, List.getElem_map]
    have ha : (gm02InjectedVertexEquiv G H f a).val = (f ⟨a.val, a.property⟩).val := rfl
    have hb : (gm02InjectedVertexEquiv G H f b).val = (f ⟨b.val, b.property⟩).val := rfl
    change H.graph.IsLink e.val a.val b.val ↔
      (gm02InjectedPattern G H f).H.IsLink e.val
        (gm02InjectedVertexEquiv G H f a).val (gm02InjectedVertexEquiv G H f b).val
    constructor
    · rintro ⟨_, h⟩
      refine ⟨⟨?_, ?_⟩, (gm02InjectedVertexEquiv G H f a).property,
        (gm02InjectedVertexEquiv G H f b).property⟩
      · simpa only [GM02TopologicalInput.patternSource, gm02InjectedPattern_edges_length] using he
      · change s((gm02InjectedVertexEquiv G H f a).val, (gm02InjectedVertexEquiv G H f b).val) =
          s(((gm02InjectedPattern G H f).edges[e.val]'hej).1.val, ((gm02InjectedPattern G H f).edges[e.val]'hej).2.val)
        simp only [hmap, ha, hb]
        rcases Sym2.eq_iff.1 h with ⟨h1, h2⟩ | ⟨h1, h2⟩
        · exact Sym2.eq_iff.2 (Or.inl ⟨congrArg (fun v : Fin H.n => (f v).val) (Fin.ext h1),
            congrArg (fun v : Fin H.n => (f v).val) (Fin.ext h2)⟩)
        · exact Sym2.eq_iff.2 (Or.inr ⟨congrArg (fun v : Fin H.n => (f v).val) (Fin.ext h1),
            congrArg (fun v : Fin H.n => (f v).val) (Fin.ext h2)⟩)
    · rintro ⟨⟨_, h⟩, _, _⟩
      refine ⟨he, ?_⟩
      change s((gm02InjectedVertexEquiv G H f a).val, (gm02InjectedVertexEquiv G H f b).val) =
        s(((gm02InjectedPattern G H f).edges[e.val]'hej).1.val, ((gm02InjectedPattern G H f).edges[e.val]'hej).2.val) at h
      simp only [hmap, ha, hb] at h
      rcases Sym2.eq_iff.1 h with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · exact Sym2.eq_iff.2 (Or.inl ⟨congrArg Fin.val (f.injective (Fin.ext h1)),
          congrArg Fin.val (f.injective (Fin.ext h2))⟩)
      · exact Sym2.eq_iff.2 (Or.inr ⟨congrArg Fin.val (f.injective (Fin.ext h1)),
          congrArg Fin.val (f.injective (Fin.ext h2))⟩)

end GraphMinor.Compute
