module

public import GraphMinor.GM01.Defs
import GraphMinor.GM01.Basic

/-!
# Components after deleting the root

In the base case of the rooted induction used for Graph Minors I, (1.1),
the root is deleted and each remaining component is rooted at a neighbour
of that root. We construct these components in the original ambient type
and prove the neighbour exists from connectedness.
-/

@[expose] public section

namespace GraphMinor.GM01

open SimpleGraph

variable {α : Type*}

/-- A connected component of a simple subgraph, viewed in the original
ambient vertex type. -/
abbrev ambientComponent (G : (⊤ : SimpleGraph α).Subgraph)
    (C : G.coe.ConnectedComponent) : (⊤ : SimpleGraph α).Subgraph :=
  Subgraph.coeSubgraph C.toSubgraph

/-- The ambient component stays inside its graph. -/
theorem ambientComponent_le (G : (⊤ : SimpleGraph α).Subgraph)
    (C : G.coe.ConnectedComponent) : ambientComponent G C ≤ G :=
  Subgraph.coeSubgraph_le _

/-- The ambient component is connected. -/
theorem ambientComponent_connected (G : (⊤ : SimpleGraph α).Subgraph)
    (C : G.coe.ConnectedComponent) : (ambientComponent G C).Connected :=
  C.connected_toSubgraph.coeSubgraph _

/-- A neighbour in the ambient graph stays in the same component. -/
theorem ambientComponent_closed (G : (⊤ : SimpleGraph α).Subgraph)
    (C : G.coe.ConnectedComponent) {x y : α}
    (hx : x ∈ (ambientComponent G C).verts) (hxy : G.Adj x y) :
    y ∈ (ambientComponent G C).verts := by
  obtain ⟨a, ha, hax⟩ := hx
  let b : G.verts := ⟨y, hxy.snd_mem⟩
  refine ⟨b, ?_, rfl⟩
  apply C.mem_supp_of_adj_mem_supp ha
  change a.val = x at hax
  change G.Adj a.val y
  rwa [hax]

/-- A component after root deletion avoids that root. -/
theorem root_not_mem_ambientComponent
    (G : (⊤ : SimpleGraph α).Subgraph) (root : G.verts)
    (C : (G.deleteVerts {root.val}).coe.ConnectedComponent) :
    root.val ∉ (ambientComponent (G.deleteVerts {root.val}) C).verts := by
  intro h
  have hmem := (ambientComponent_le _ C).1 h
  exact hmem.2 rfl

/-- In a connected graph each component remaining after root deletion has
some vertex adjacent to the deleted root, as used on page 54 of the proof. -/
theorem exists_root_neighbor_in_component
    (G : (⊤ : SimpleGraph α).Subgraph) (hG : G.Connected) (root : G.verts)
    (C : (G.deleteVerts {root.val}).coe.ConnectedComponent) :
    ∃ x ∈ (ambientComponent (G.deleteVerts {root.val}) C).verts, G.Adj root.val x := by
  classical
  let D := G.deleteVerts {root.val}
  let K := ambientComponent D C
  have hKle : K ≤ D := ambientComponent_le D C
  have hKconn : K.Connected := ambientComponent_connected D C
  have havoid : root.val ∉ K.verts := root_not_mem_ambientComponent G root C
  by_contra hno
  have closed {a b : α} (ha : a ∈ K.verts) (hab : G.Adj a b) : b ∈ K.verts := by
    by_cases hb : b = root.val
    · subst b
      exact False.elim (hno ⟨a, ha, hab.symm⟩)
    · have haD : a ∈ D.verts := hKle.1 ha
      have habD : D.Adj a b :=
        Subgraph.deleteVerts_adj.mpr ⟨haD.1, haD.2, hab.snd_mem, hb, hab⟩
      exact ambientComponent_closed D C ha habD
  obtain ⟨a, ha⟩ := hKconn.nonempty
  let aG : G.verts := ⟨a, G.deleteVerts_le.1 (hKle.1 ha)⟩
  have hr : Relation.ReflTransGen G.coe.Adj aG root :=
    (reachable_iff_reflTransGen aG root).mp (hG aG root)
  have preserves : ∀ {b : G.verts}, Relation.ReflTransGen G.coe.Adj aG b → b.val ∈ K.verts := by
    intro b hb
    induction hb with
    | refl => exact ha
    | @tail c d hpath hcd ih => exact closed ih hcd
  exact havoid (preserves hr)

/-- An ambient component is the induced subgraph on its vertex set. -/
theorem ambientComponent_eq_induce (G : (⊤ : SimpleGraph α).Subgraph)
    (C : G.coe.ConnectedComponent) :
    ambientComponent G C = G.induce (ambientComponent G C).verts := by
  apply Subgraph.ext
  · rfl
  · funext x y
    apply propext
    constructor
    · intro hxy
      obtain ⟨hx, hy, hC⟩ := (Subgraph.coeSubgraph_adj C.toSubgraph x y).mp hxy
      exact ⟨⟨⟨x, hx⟩, hC.1, rfl⟩, ⟨⟨y, hy⟩, hC.2.1, rfl⟩, hC.2.2⟩
    · rintro ⟨⟨a, ha, rfl⟩, ⟨b, hb, rfl⟩, hxy⟩
      exact (Subgraph.coeSubgraph_adj C.toSubgraph a.val b.val).mpr
        ⟨a.property, b.property, ha, hb, hxy⟩

end GraphMinor.GM01
