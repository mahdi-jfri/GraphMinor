module

public import GraphMinor.GM05.Defs

/-!
# The vertex conditions used by the auxiliary graph of a web

The auxiliary graph in V (4.4) depends only on path vertices. Its walk and
separator arguments use disjointness within each family and intersections
between them, without using edge-disjointness between the two families.
Keeping these conditions separate allows the same argument for multigraphs.
-/

public section
namespace GraphMinor.GM05
open SimpleGraph GM01
variable {V : Type*}

/-- The vertex conditions of a web, V page 97, without the separate
condition that the paths in opposite families use disjoint edges. -/
structure VertexWeb (G : (⊤ : SimpleGraph V).Subgraph) {m n : ℕ}
    (A : Fin m → Path V) (B : Fin n → Path V) : Prop where
  isIn_left : ∀ i, (A i).IsIn G
  isIn_right : ∀ j, (B j).IsIn G
  disjoint_left : Pairwise fun i j => Disjoint (A i).verts (A j).verts
  disjoint_right : Pairwise fun i j => Disjoint (B i).verts (B j).verts
  meets : ∀ i j, ((A i).verts ∩ (B j).verts).Nonempty

/-- A web has the vertex conditions used in its auxiliary graph. -/
theorem IsWeb.vertexWeb {G : (⊤ : SimpleGraph V).Subgraph} {m n : ℕ}
    {A : Fin m → Path V} {B : Fin n → Path V} (h : IsWeb G A B) : VertexWeb G A B :=
  ⟨h.isIn_left, h.isIn_right, h.disjoint_left, h.disjoint_right, h.meets⟩

end GraphMinor.GM05
