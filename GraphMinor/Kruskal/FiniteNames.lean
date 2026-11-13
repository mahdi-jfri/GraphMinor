module

public import GraphMinor.GM04.TopologicalContainment
import GraphMinor.Minor.Basic
import Mathlib.Data.Fintype.EquivFin

/-!
# Finite names for subdivision witnesses

Topological containment in Graph Minors IV, Section 1, page 229 allows
isomorphisms at either end of a subdivision. The Lean definition uses natural
numbers for the intermediate vertices and edges. We give every finite graph
such names by mapping its actual vertex and edge sets injectively into the
natural numbers. No map on unused names is required.
-/

@[expose] public section

namespace GraphMinor.Kruskal

open Graph Set

/-- Rename the actual vertices and edges by embeddings into new ambient types.
Links in the renamed graph are exactly the images of the original links. -/
def renameGraph {α β α' β' : Type*} (G : Graph α β)
    (vertices : V(G) ↪ α') (edges : E(G) ↪ β') : Graph α' β' where
  vertexSet := range vertices
  edgeSet := range edges
  IsLink e x y := ∃ (d : E(G)) (a b : V(G)),
    G.IsLink d a b ∧ edges d = e ∧ vertices a = x ∧ vertices b = y
  isLink_symm _ _ := ⟨by
    rintro x y ⟨d, a, b, h, rfl, rfl, rfl⟩
    exact ⟨d, b, a, h.symm, rfl, rfl, rfl⟩⟩
  eq_or_eq_of_isLink_of_isLink := by
    rintro e x y u v ⟨d, a, b, hab, hd, rfl, rfl⟩
      ⟨d', a', b', hab', hd', rfl, rfl⟩
    have hdd : d = d' := edges.injective (hd.trans hd'.symm)
    subst d'
    rcases hab.left_eq_or_eq hab' with ha | hb
    · exact Or.inl (congrArg vertices (Subtype.ext ha))
    · exact Or.inr (congrArg vertices (Subtype.ext hb))
  edge_mem_iff_exists_isLink := by
    intro e
    constructor
    · rintro ⟨d, rfl⟩
      obtain ⟨a, b, hab⟩ := G.exists_isLink_of_mem_edgeSet d.property
      exact ⟨vertices ⟨a, hab.left_mem⟩, vertices ⟨b, hab.right_mem⟩,
        d, ⟨a, hab.left_mem⟩, ⟨b, hab.right_mem⟩, hab, rfl, rfl, rfl⟩
    · rintro ⟨x, y, d, a, b, hab, hd, _⟩
      exact ⟨d, hd⟩
  left_mem_of_isLink := by
    rintro e x y ⟨d, a, b, hab, hd, rfl, hb⟩
    exact ⟨a, rfl⟩

/-- The renaming is an isomorphism, with the given maps on actual vertices
and edges. -/
noncomputable def renameGraphIso {α β α' β' : Type*} (G : Graph α β)
    (vertices : V(G) ↪ α') (edges : E(G) ↪ β') :
    Iso G (renameGraph G vertices edges) where
  vertexEquiv := Equiv.ofInjective vertices vertices.injective
  edgeEquiv := Equiv.ofInjective edges edges.injective
  isLink_iff d a b := by
    constructor
    · intro hab
      exact ⟨d, a, b, hab, rfl, rfl, rfl⟩
    · rintro ⟨d', a', b', hab, hd, ha, hb⟩
      have hdd : d' = d := edges.injective hd
      have haa : a' = a := vertices.injective ha
      have hbb : b' = b := vertices.injective hb
      simpa only [hdd, haa, hbb] using hab

/-- Every graph with finite vertex and edge sets has an isomorphic copy
whose vertex and edge names are natural numbers. This includes graphs with
no edges and graphs with empty ambient types. -/
theorem exists_nat_iso {α β : Type*} (G : Graph α β)
    (hV : V(G).Finite) (hE : E(G).Finite) :
    ∃ H : Graph ℕ ℕ, Nonempty (Iso G H) := by
  classical
  let := hV.fintype
  let := hE.fintype
  let vertices : V(G) ↪ ℕ :=
    (Fintype.equivFin V(G)).toEmbedding.trans ⟨Fin.val, Fin.val_injective⟩
  let edges : E(G) ↪ ℕ :=
    (Fintype.equivFin E(G)).toEmbedding.trans ⟨Fin.val, Fin.val_injective⟩
  exact ⟨renameGraph G vertices edges, ⟨renameGraphIso G vertices edges⟩⟩

/-- A finite graph is topologically contained in itself, using a subdivision
sequence of length zero after choosing natural-number names. -/
theorem isTopologicalMinor_refl {α β : Type*} (G : Graph α β)
    (hV : V(G).Finite) (hE : E(G).Finite) : GM04.IsTopologicalMinor G G := by
  obtain ⟨H, ⟨φ⟩⟩ := exists_nat_iso G hV hE
  exact ⟨H, H, ⟨φ⟩, .refl, G, le_rfl, ⟨φ.symm⟩⟩

end GraphMinor.Kruskal
