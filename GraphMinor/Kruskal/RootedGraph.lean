module

public import GraphMinor.GM04.TreeLemma.Basic
public import GraphMinor.Statement

/-!
# The undirected graph of a rooted tree

Graph Minors IV, Section 2, page 230 identifies each directed edge with its
head. Forgetting the directions gives an undirected edge between each
non-root vertex and its parent. This file constructs that multigraph and
records isomorphisms of rooted trees by their vertex bijections and parent
maps.
-/

@[expose] public section

namespace GraphMinor.Kruskal

open Graph Set GraphMinor.GM04

/-- The underlying undirected multigraph of a rooted tree. Each edge is
named by its head, as in the rooted-tree representation of IV, Section 2. -/
@[reducible] def rootedGraph {ι : Type*} (T : RootedTree ι) : Graph ι ι where
  vertexSet := T.verts
  edgeSet := T.edges
  IsLink e x y := e ∈ T.edges ∧
    ((x = T.parent e ∧ y = e) ∨ (x = e ∧ y = T.parent e))
  isLink_symm _ _ := ⟨by
    rintro x y ⟨he, h⟩
    exact ⟨he, h.elim (fun h ↦ Or.inr h.symm) (fun h ↦ Or.inl h.symm)⟩⟩
  eq_or_eq_of_isLink_of_isLink := by
    rintro e x y z w ⟨he, h₁⟩ ⟨_, h₂⟩
    rcases h₁ with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
      rcases h₂ with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> simp
  edge_mem_iff_exists_isLink := by
    intro e
    exact ⟨fun he ↦ ⟨T.parent e, e, he, Or.inl ⟨rfl, rfl⟩⟩,
      fun ⟨_, _, he, _⟩ ↦ he⟩
  left_mem_of_isLink := by
    rintro e x y ⟨he, h⟩
    rcases h with ⟨rfl, _⟩ | ⟨rfl, _⟩
    · exact T.parent_mem e (T.mem_verts_of_mem_edges he)
    · exact T.mem_verts_of_mem_edges he

/-- Both sets of the undirected graph are finite. -/
theorem rootedGraph_finite {ι : Type*} (T : RootedTree ι) :
    V(rootedGraph T).Finite ∧ E(rootedGraph T).Finite :=
  ⟨T.verts.finite_toSet, T.edges.finite_toSet⟩

/-- A rooted-tree isomorphism is a bijection on the actual vertices that
preserves the root and the parent of every vertex. -/
structure RootedTreeIso {ι κ : Type*} (T : RootedTree ι) (S : RootedTree κ) where
  vertices : {v // v ∈ T.verts} ≃ {v // v ∈ S.verts}
  root_eq : (vertices ⟨T.root, T.root_mem⟩).val = S.root
  parent_eq : ∀ v : {v // v ∈ T.verts},
    (vertices ⟨T.parent v.val, T.parent_mem v.val v.property⟩).val =
      S.parent (vertices v).val

namespace RootedTreeIso

/-- A root-preserving bijection sends exactly the non-root vertices to
non-root vertices. These are the edge names of the rooted graphs. -/
theorem ne_root_iff {ι κ : Type*} {T : RootedTree ι} {S : RootedTree κ}
    (φ : RootedTreeIso T S) (v : {v // v ∈ T.verts}) :
    (φ.vertices v).val ≠ S.root ↔ v.val ≠ T.root := by
  have hroot : φ.vertices ⟨T.root, T.root_mem⟩ = ⟨S.root, S.root_mem⟩ :=
    Subtype.ext φ.root_eq
  constructor
  · intro h hv
    have hvroot : v = ⟨T.root, T.root_mem⟩ := Subtype.ext hv
    exact h (hvroot ▸ φ.root_eq)
  · intro h hv
    have heq : φ.vertices v = φ.vertices ⟨T.root, T.root_mem⟩ := by
      exact Subtype.ext (hv.trans φ.root_eq.symm)
    exact h (congrArg Subtype.val (φ.vertices.injective heq))

/-- A rooted-tree isomorphism gives an isomorphism of the underlying
undirected multigraphs. Its edge bijection is the vertex bijection restricted
to the non-root vertices. -/
noncomputable def toGraphIso {ι κ : Type*} {T : RootedTree ι} {S : RootedTree κ}
    (φ : RootedTreeIso T S) : Iso (rootedGraph T) (rootedGraph S) := by
  let edgeMap : E(rootedGraph T) → E(rootedGraph S) := fun e ↦
    ⟨(φ.vertices ⟨e.val, T.mem_verts_of_mem_edges e.property⟩).val,
      S.mem_edges.2 ⟨(φ.ne_root_iff _).2 (T.ne_root_of_mem_edges e.property),
        (φ.vertices ⟨e.val, T.mem_verts_of_mem_edges e.property⟩).property⟩⟩
  have hinj : Function.Injective edgeMap := by
    intro e f hef
    have hval : (φ.vertices ⟨e.val, T.mem_verts_of_mem_edges e.property⟩).val =
        (φ.vertices ⟨f.val, T.mem_verts_of_mem_edges f.property⟩).val :=
      congrArg (fun d : E(rootedGraph S) ↦ d.val) hef
    exact Subtype.ext (congrArg (fun v : {v // v ∈ T.verts} ↦ v.val)
      (φ.vertices.injective (Subtype.ext hval)))
  have hsurj : Function.Surjective edgeMap := by
    intro f
    let v := φ.vertices.symm ⟨f.val, S.mem_verts_of_mem_edges f.property⟩
    have hv : v.val ≠ T.root := by
      apply (φ.ne_root_iff v).1
      simpa only [v, Equiv.apply_symm_apply] using S.ne_root_of_mem_edges f.property
    refine ⟨⟨v.val, T.mem_edges.2 ⟨hv, v.property⟩⟩, ?_⟩
    exact Subtype.ext (congrArg (fun x : {v // v ∈ S.verts} ↦ x.val)
      (φ.vertices.apply_symm_apply ⟨f.val, S.mem_verts_of_mem_edges f.property⟩))
  refine { vertexEquiv := φ.vertices
           edgeEquiv := Equiv.ofBijective edgeMap ⟨hinj, hsurj⟩
           isLink_iff := ?_ }
  intro e x y
  let ev : {v // v ∈ T.verts} := ⟨e.val, T.mem_verts_of_mem_edges e.property⟩
  have heq (a b : {v // v ∈ T.verts}) :
      (φ.vertices a).val = (φ.vertices b).val ↔ a.val = b.val := by
    constructor
    · intro h
      exact congrArg Subtype.val (φ.vertices.injective (Subtype.ext h))
    · intro h
      exact congrArg (fun v ↦ (φ.vertices v).val) (Subtype.ext h)
  have hparent (a : {v // v ∈ T.verts}) :
      (φ.vertices a).val = S.parent (φ.vertices ev).val ↔ a.val = T.parent e.val := by
    rw [← φ.parent_eq ev]
    exact heq _ _
  change (e.val ∈ T.edges ∧
      ((x.val = T.parent e.val ∧ y.val = e.val) ∨
        (x.val = e.val ∧ y.val = T.parent e.val))) ↔
    ((edgeMap e).val ∈ S.edges ∧
      (((φ.vertices x).val = S.parent (φ.vertices ev).val ∧
          (φ.vertices y).val = (φ.vertices ev).val) ∨
        ((φ.vertices x).val = (φ.vertices ev).val ∧
          (φ.vertices y).val = S.parent (φ.vertices ev).val)))
  simp only [hparent, heq]
  constructor
  · rintro ⟨_, h⟩
    exact ⟨(edgeMap e).property, h⟩
  · rintro ⟨_, h⟩
    exact ⟨e.property, h⟩

end RootedTreeIso
end GraphMinor.Kruskal
